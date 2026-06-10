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

from lsprotocol import types as lsp

from vera.ast import Span
from vera.errors import SourceLocation


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
