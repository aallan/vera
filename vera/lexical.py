"""Shared lexical scanning for Vera source text.

The single comment scanner that both the parser's pre-lex pass and the
formatter's comment extraction are derived from.

Vera's block comments **nest** (spec 1.3): a ``{-`` inside a block
comment opens a nested comment that must be closed by its own ``-}``.
A regular expression cannot express balanced delimiters at all, so
nesting is resolved here, once, by counting depth.

#1112 arose precisely because two scanners disagreed: the formatter
counted depth correctly (and ``tests/test_formatter.py`` asserted it),
while the grammar's ``%ignore /\\{-[\\s\\S]*?-\\}/`` closed at the
*first* ``-}``.  The same text was therefore a single nested comment to
``vera fmt`` and a syntax error to ``vera check``.  Deriving every
consumer from one scan makes that drift impossible **for block
comments**.  Line and annotation comments are still recognised
independently by ``grammar.lark``; the two agree today, but a change to
either form has to be made on both sides.

This module deliberately imports nothing from ``vera.parser`` or
``vera.formatter`` — the formatter already imports the parser, so a
shared helper has to sit below both.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

#: A comment's syntactic form.  A `Literal` rather than `str` because
#: mypy runs with ``--strict-equality``: a mistyped comparison against a
#: `str` field is silently always-false, and the symptom is comments
#: quietly ceasing to be handled.
CommentKind = Literal["line", "block", "annotation"]

#: A malformed-comment case.  Also a `Literal`, and more load-bearing than
#: :data:`CommentKind`: ``vera/errors.py`` indexes ``_COMMENT_PROBLEMS``
#: with it unguarded, so a value added here and not there is a bare
#: ``KeyError`` escaping the CLI's ``except VeraError`` — the #966
#: raw-traceback mode.
CommentProblemKind = Literal[
    "unterminated_block", "unterminated_annotation", "nested_annotation",
]

#: Attribute under which :func:`vera.parser.parse` stashes the source's
#: annotation labels on the Lark tree, and :func:`vera.transform.transform`
#: reads them back.  Named here so the two sides cannot drift apart.
ANNOTATIONS_ATTR = "vera_annotations"

#: Attribute under which :func:`vera.parser.parse` stashes the file name and
#: the source text on the Lark tree, so :func:`vera.transform.transform`
#: can place a transform-stage diagnostic in its file with its source line
#: (#1636) without taking either as an argument at its call sites.
ORIGIN_ATTR = "vera_origin"

__all__ = [
    "ANNOTATIONS_ATTR",
    "ORIGIN_ATTR",
    "AnnotationLabel",
    "CommentKind",
    "CommentProblemKind",
    "CommentProblem",
    "CommentSpan",
    "annotation_labels",
    "blank_block_comments",
    "blank_comments",
    "find_comment_problems",
    "scan_comments",
]


@dataclass(frozen=True)
class CommentSpan:
    """A comment's extent in the source text.

    ``start``/``end`` are character offsets (``end`` exclusive), so a
    consumer can slice or blank the exact region without rescanning.
    ``terminated`` is False for a block comment whose nesting never
    returns to depth zero, or an annotation comment with no ``*/`` —
    both run to end of input.
    """

    kind: CommentKind
    start: int
    end: int
    terminated: bool
    #: Parenthesis nesting depth at the opening delimiter.  A binding
    #: label always sits inside a signature's parens, so depth 0 marks a
    #: comment that cannot be one however close to a slot it looks.
    paren_depth: int = 0


def scan_comments(source: str) -> list[CommentSpan]:
    """Every comment span in ``source``, in source order.

    String literals are skipped (with backslash escapes honoured) so a
    ``{-`` or ``--`` inside a string is not mistaken for a comment
    opener.  Because the scan is strictly left-to-right, a delimiter
    inside an earlier comment is likewise consumed by that comment
    rather than opening a new one.
    """
    spans: list[CommentSpan] = []
    src = source
    n = len(src)
    pos = 0
    depth = 0

    while pos < n:
        # Line comment — runs to end of line.
        if src[pos:pos + 2] == "--":
            end = src.find("\n", pos)
            if end == -1:
                end = n
            spans.append(CommentSpan("line", pos, end, True, depth))
            pos = end
            continue

        # Block comment — nestable, so count depth rather than
        # scanning for the first closer.
        if src[pos:pos + 2] == "{-":
            block_depth = 1
            j = pos + 2
            while j < n and block_depth > 0:
                if src[j:j + 2] == "{-":
                    block_depth += 1
                    j += 2
                elif src[j:j + 2] == "-}":
                    block_depth -= 1
                    j += 2
                else:
                    j += 1
            spans.append(CommentSpan("block", pos, j, block_depth == 0, depth))
            pos = j
            continue

        # Annotation comment — does not nest (spec 1.3).
        if src[pos:pos + 2] == "/*":
            close = src.find("*/", pos + 2)
            terminated = close != -1
            end = n if close == -1 else close + 2
            spans.append(CommentSpan("annotation", pos, end, terminated, depth))
            pos = end
            continue

        # String literal — skip so delimiters inside it never match.
        if src[pos] == '"':
            j = pos + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            pos = j + 1
            continue

        if src[pos] == "(":
            depth += 1
        elif src[pos] == ")":
            depth = max(0, depth - 1)
        pos += 1

    return spans


def blank_block_comments(source: str) -> tuple[str, int | None]:
    """``source`` with block comments replaced by spaces.

    Every non-newline character of a block comment becomes a space and
    newlines are kept, so the result is **byte-for-byte the same length
    and line structure** as the input.  That is load-bearing: the
    grammar is parsed with ``propagate_positions=True``, every
    diagnostic quotes a line and column, and the formatter attaches
    comments by source span — all of which would shift if comments were
    deleted rather than blanked.

    Returns ``(blanked_source, unterminated_line)`` where
    ``unterminated_line`` is the 1-based line of the first block comment
    that never closes, or ``None`` when every block comment is balanced.
    No caller consumes it today: :func:`find_comment_problems` runs first
    and raises E020 from its own scan.  Kept because the blanking pass
    already knows the answer, and a caller that blanks without diagnosing
    would otherwise have no way to notice.
    """
    spans = scan_comments(source)
    chars = list(source)
    unterminated: int | None = None

    for span in spans:
        if span.kind != "block":
            continue
        if not span.terminated and unterminated is None:
            unterminated = source.count("\n", 0, span.start) + 1
        for i in range(span.start, span.end):
            if chars[i] != "\n":
                chars[i] = " "

    return "".join(chars), unterminated


def blank_comments(source: str) -> str:
    """``source`` with EVERY comment replaced by spaces.

    :func:`blank_block_comments`'s wider sibling — same length- and
    line-preserving blanking, over line and annotation comments too.  For a
    consumer that reads source text back out by span and must not pick a
    comment up with it: the verifier quotes a multi-line contract clause into
    a one-line message, and a ``--`` comment on the first physical line would
    otherwise swallow the rest of the clause (PR #1239 review).

    It shares :func:`scan_comments` with the parser rather than looking for
    delimiters itself, so a ``--`` inside a string literal survives — which
    is exactly the case a hand-rolled split would get wrong.

    The early return is an optimisation, so its opener set has to be the
    scanner's WHOLE set: all three of ``--``, ``{-`` and the annotation
    comment's ``/*`` (spec §1.3).  Missing one made the fast path a silent
    behaviour change rather than a shortcut — a clause whose only comment was
    an annotation came back unblanked and was quoted with the comment in it
    (PR #1239 review).
    """
    if not any(opener in source for opener in ("--", "{-", "/*")):
        return source
    chars = list(source)
    for span in scan_comments(source):
        for i in range(span.start, min(span.end, len(chars))):
            if chars[i] != "\n":
                chars[i] = " "
    return "".join(chars)


@dataclass(frozen=True)
class CommentProblem:
    """A malformed comment, located for a diagnostic.

    Reported as facts rather than messages: this module stays free of
    diagnostic policy, and ``vera/parser.py`` maps each ``kind`` onto
    its error code and wording.
    """

    kind: CommentProblemKind
    line: int          # 1-based
    column: int        # 1-based


def _locate(source: str, offset: int) -> tuple[int, int]:
    """1-based (line, column) of a character offset."""
    line = source.count("\n", 0, offset) + 1
    line_start = source.rfind("\n", 0, offset) + 1
    return line, offset - line_start + 1


@dataclass(frozen=True)
class AnnotationLabel:
    """An annotation comment, positioned the way Lark spans are.

    Line and column are 1-based and ``end_column`` is exclusive, so a
    label can be compared directly against an AST node's
    :class:`~vera.ast.Span` without converting between coordinate
    systems.  ``text`` is the inner text with ``/*``, ``*/`` and
    surrounding whitespace removed — the label itself, which is what
    spec 1.3 means by a human-readable label for a binding.
    """

    text: str
    line: int
    column: int
    end_line: int
    end_column: int
    #: See :attr:`CommentSpan.paren_depth`.
    depth: int = 0

    @property
    def start(self) -> tuple[int, int]:
        """Sort/compare key for the opening ``/*``."""
        return (self.line, self.column)


def annotation_labels(source: str) -> tuple[AnnotationLabel, ...]:
    """Every terminated annotation comment in ``source``, in source order.

    Unterminated ones are skipped: they are already an E021 parse error,
    and their extent runs to end of input, so treating one as a label
    would attach the rest of the file to a binding.
    """
    labels: list[AnnotationLabel] = []

    for span in scan_comments(source):
        if span.kind != "annotation" or not span.terminated:
            continue
        line, column = _locate(source, span.start)
        end_line, end_column = _locate(source, span.end)
        labels.append(AnnotationLabel(
            text=source[span.start + 2:span.end - 2].strip(),
            line=line,
            column=column,
            end_line=end_line,
            end_column=end_column,
            depth=span.paren_depth,
        ))

    return tuple(labels)


def find_comment_problems(source: str) -> list[CommentProblem]:
    """Malformed comments in ``source``, in source order.

    Each of these otherwise surfaces as a token-level complaint naming
    the wrong culprit — an unterminated ``/*`` is reported as an
    unexpected ``/`` — because the grammar only ever sees the wreckage
    a malformed comment leaves behind.  Detecting them during the scan
    that already knows where every comment starts and ends lets the
    parser name the real problem and point at the delimiter.
    """
    problems: list[CommentProblem] = []

    for span in scan_comments(source):
        if span.kind == "block" and not span.terminated:
            line, column = _locate(source, span.start)
            problems.append(CommentProblem("unterminated_block", line, column))

        elif span.kind == "annotation":
            if not span.terminated:
                line, column = _locate(source, span.start)
                problems.append(
                    CommentProblem("unterminated_annotation", line, column),
                )
                continue
            # Annotation comments do not nest (spec 1.3), so the span
            # closed at the first `*/` and a second `/*` inside it is
            # the author expecting nesting they do not have.
            interior = source.find("/*", span.start + 2, max(span.end - 2, 0))
            if interior != -1:
                line, column = _locate(source, interior)
                problems.append(
                    CommentProblem("nested_annotation", line, column),
                )

    return problems
