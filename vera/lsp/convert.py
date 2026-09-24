"""Coordinate conversion between Vera and LSP positions (#222 Phase C).

Three coordinate systems meet at the LSP boundary, and every feature
must convert through this module — nobody hand-rolls the arithmetic:

1. **``ast.Span``** — raw Lark positions: 1-based line, 1-based
   *code-point* column, exclusive 1-based end column
   (``transform._span_from_meta`` copies Lark's meta verbatim).
2. **``errors.SourceLocation``** — diagnostics: 1-based line but
   **0-based** code-point column (the historical convention of
   ``ContractVerifier._error`` / the checker; note the base differs
   from ``Span``, which is why every converter here takes its source
   type explicitly rather than guessing).
3. **LSP ``Position``** — 0-based line, 0-based **UTF-16 code unit**
   column (the protocol's mandatory default encoding).

The UTF-16 wrinkle: Python string indices count code points, LSP
columns count UTF-16 code units, so any astral-plane character (emoji,
mathematical alphanumerics — anything above U+FFFF) occupies *two* LSP
columns.  :class:`LineIndex` does the transcoding per line against the
document text.
"""

from __future__ import annotations

import urllib.parse
import urllib.request
from urllib.error import URLError

from lsprotocol import types as lsp

from vera.ast import Span
from vera.errors import SourceLocation


def uri_to_path(uri: str) -> str:
    """The filesystem path an LSP document URI names, or the URI itself.

    A fourth conversion at the same boundary, and the same rule: nobody
    hand-rolls it.  LSP identifies documents by URI (``file:///a/b.vera``);
    the compiler pipeline identifies them by path, and uses it — the
    module resolver reads imports from ``Path(file).parent``.  Handing it
    the raw URI made that parent the literal directory ``file:``, so a
    document with imports resolved none of them: the entry stopped at the
    resolver and the editor showed neither obligations nor tier hints, and
    ``verify_source``'s early return meant the resolver's own errors were
    not surfaced either — silently unverified (#1246 adversarial round,
    contradicting LSP_SERVER.md's "module imports resolve from disk").

    **Total by construction.**  Every caller is on the didOpen/didChange
    path.  ``analyze_and_publish`` reports an exception from the analysis
    as an ``E699``, but builds that report with ``analysis_failure``,
    which calls this too -- so a raise here would escape the handler all
    the same.  It returns a string for every input and never raises.  When a URI names
    no path this process can open, the URI is returned unchanged — an
    opaque document label the pipeline carries but never opens, which is
    the pre-existing behaviour and exactly what an unsaved buffer needs.
    Four kinds of input take that route:

    * a non-``file:`` scheme — ``untitled:``, a virtual filesystem, or
      the bare labels the tests use.  Matched case-insensitively, per
      RFC 3986 §3.1 (``FILE:///x`` is the same scheme as ``file:///x``);
    * an authority naming another host (``file://server/share/x``).  This
      process can only open a LOCAL file, so a remote authority names no
      path here.  Deciding it *here* also makes the answer the same on
      every Python: 3.14's ``url2pathname`` validates the authority and
      raises :exc:`~urllib.error.URLError` for anything but localhost,
      while 3.13 returned a ``//server/...`` string that on POSIX is a
      stray local path rather than a UNC mount — so the old fold was
      wrong on every version, and on 3.14 it took the request with it;
    * a degenerate URI that decodes to the empty string (``file://``,
      ``file:``), so the label the pipeline carries stays recognisably a
      URI rather than becoming ``""``.  This does NOT by itself stop the
      resolver rooting at the process CWD — ``Path("file:")`` is exactly
      as directory-less as ``Path("")``, both giving ``.`` — and an
      earlier version of this note wrongly claimed it did.  That property
      is enforced where the resolver is built
      (:meth:`vera.obligations.session.VerificationSession.verify_source`),
      which is the one place every caller passes through;
    * anything else ``url2pathname`` rejects, caught as a backstop so a
      future validation cannot reopen the same escape.

    An empty authority and ``localhost`` both mean *this* host and take
    the normal path.  ``url2pathname`` does the percent-decoding and, on
    Windows, the drive-letter transform (``/C:/x`` → ``C:\\x``), so no
    separate ``unquote`` here — a second one would corrupt a path
    containing a literal ``%``.
    """
    try:
        parsed = urllib.parse.urlsplit(uri)
    except ValueError:
        # A malformed authority — `file://[` is "Invalid IPv6 URL" — raises
        # out of the SPLIT, before any guard below could run.  Same escape
        # route the `URLError` took, and the same answer: a URI this
        # malformed names no path, so it stays an opaque label.
        return uri
    if parsed.scheme.lower() != "file":
        return uri
    if parsed.netloc and parsed.netloc.lower() != "localhost":
        return uri
    try:
        path = urllib.request.url2pathname(parsed.path)
    except URLError:
        return uri
    return path or uri


class LineIndex:
    """Code-point ↔ UTF-16 column transcoding for one document text.

    Built once per document version (the store caches it; see
    ``documents.py``) and queried per conversion.  Lines are split with
    ``splitlines()`` so all Unicode line boundaries Lark could have
    counted are covered; out-of-range lines degrade to identity
    transcoding rather than raising, because diagnostics can point at
    a virtual line just past EOF (e.g. unexpected-end-of-input).
    """

    def __init__(self, text: str) -> None:
        self._lines = text.splitlines()

    def _line_text(self, line0: int) -> str:
        if 0 <= line0 < len(self._lines):
            return self._lines[line0]
        return ""

    def cp_to_utf16(self, line0: int, cp_col: int) -> int:
        """Code-point column → UTF-16 column on 0-based line *line0*."""
        text = self._line_text(line0)
        clamped = max(0, min(cp_col, len(text)))
        return sum(
            2 if ord(ch) > 0xFFFF else 1 for ch in text[:clamped]
        )

    def utf16_to_cp(self, line0: int, utf16_col: int) -> int:
        """UTF-16 column → code-point column on 0-based line *line0*.

        A UTF-16 offset landing *inside* a surrogate pair snaps back to
        the character's start, per the LSP spec's guidance for invalid
        positions.
        """
        text = self._line_text(line0)
        units = 0
        for i, ch in enumerate(text):
            width = 2 if ord(ch) > 0xFFFF else 1
            if units + width > utf16_col:
                return i
            units += width
        return len(text)


def span_to_range(span: Span, index: LineIndex) -> lsp.Range:
    """``ast.Span`` (1-based line, 1-based cp col, exclusive end) →
    LSP ``Range`` (0-based line, UTF-16 col, exclusive end)."""
    return lsp.Range(
        start=lsp.Position(
            line=span.line - 1,
            character=index.cp_to_utf16(span.line - 1, span.column - 1),
        ),
        end=lsp.Position(
            line=span.end_line - 1,
            character=index.cp_to_utf16(
                span.end_line - 1, span.end_column - 1,
            ),
        ),
    )


def location_to_position(
    loc: SourceLocation, index: LineIndex,
) -> lsp.Position:
    """``SourceLocation`` (1-based line, 0-based cp col) → LSP
    ``Position``.  Note the column base differs from ``Span``."""
    return lsp.Position(
        line=max(0, loc.line - 1),
        character=index.cp_to_utf16(max(0, loc.line - 1), loc.column),
    )


def location_to_range(
    loc: SourceLocation, index: LineIndex,
) -> lsp.Range:
    """Point diagnostic location → a usable squiggle range.

    Diagnostics carry a point, not a span (the verifier copies only
    ``span.line``/``span.column``).  Widen point → end-of-token using
    a conservative token heuristic: extend across identifier-ish
    characters (``@`` slot sigils, alphanumerics, ``_``, ``.``); if
    the position is not on such a token, fall back to a single
    character so the squiggle is at least visible.
    """
    line0 = max(0, loc.line - 1)
    text = index._line_text(line0)
    start_cp = min(loc.column, len(text))
    end_cp = start_cp
    while end_cp < len(text) and (
        text[end_cp].isalnum() or text[end_cp] in "@_."
    ):
        end_cp += 1
    if end_cp == start_cp and start_cp < len(text):
        end_cp = start_cp + 1
    return lsp.Range(
        start=lsp.Position(
            line=line0, character=index.cp_to_utf16(line0, start_cp),
        ),
        end=lsp.Position(
            line=line0, character=index.cp_to_utf16(line0, end_cp),
        ),
    )


def position_to_cp(
    pos: lsp.Position, index: LineIndex,
) -> tuple[int, int]:
    """LSP ``Position`` → (1-based line, 0-based code-point column),
    the shape lookups against ``Span``-carrying AST nodes want."""
    return (
        pos.line + 1,
        index.utf16_to_cp(pos.line, pos.character),
    )
