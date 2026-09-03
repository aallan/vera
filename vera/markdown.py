"""Pure-Python Markdown parser and renderer for the §9.7.3 subset.

Provides Python dataclasses mirroring the Vera MdInline/MdBlock ADTs,
plus five functions: parse_markdown, render_markdown, has_heading,
has_code_block, extract_code_blocks.

This is the **reference implementation** for the host-imported Markdown
functions.  The same .wasm binary works with any host runtime (Python,
JavaScript, Rust) that provides matching implementations of the WASM
import signatures defined in assembly.py.

Design constraints:
  - No external dependencies (hand-written parser for the §9.7.3 subset).
  - CommonMark-inspired but intentionally simplified per §9.7.3 design
    notes: no raw HTML, no link references, no setext headings, no
    indented code blocks, no hard/soft line breaks.
  - GFM tables are supported (ubiquitous in agent communication).
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from vera.markdown_grammar import (
    CONTINUATION_INDENT,
    PATTERNS,
    fence_close,
    is_blank,
    trim,
)


# =====================================================================
# ADT dataclasses — mirrors Vera MdInline / MdBlock
# =====================================================================


@dataclass(frozen=True, eq=True)
class MdText:
    """Plain text run."""
    text: str


@dataclass(frozen=True, eq=True)
class MdCode:
    """Inline code span."""
    code: str


@dataclass(frozen=True, eq=True)
class MdEmph:
    """Emphasis (italic)."""
    children: tuple[MdInline, ...]


@dataclass(frozen=True, eq=True)
class MdStrong:
    """Strong emphasis (bold)."""
    children: tuple[MdInline, ...]


@dataclass(frozen=True, eq=True)
class MdLink:
    """Hyperlink: display text + URL."""
    children: tuple[MdInline, ...]
    url: str


@dataclass(frozen=True, eq=True)
class MdImage:
    """Image: alt text + source URL."""
    alt: str
    src: str


MdInline = MdText | MdCode | MdEmph | MdStrong | MdLink | MdImage


@dataclass(frozen=True, eq=True)
class MdParagraph:
    """Paragraph: sequence of inline content."""
    children: tuple[MdInline, ...]


@dataclass(frozen=True, eq=True)
class MdHeading:
    """Heading: level (1-6) + inline content."""
    level: int
    children: tuple[MdInline, ...]


@dataclass(frozen=True, eq=True)
class MdCodeBlock:
    """Fenced code block: language + code body."""
    language: str
    code: str


@dataclass(frozen=True, eq=True)
class MdBlockQuote:
    """Block quote: recursive block content."""
    children: tuple[MdBlock, ...]


@dataclass(frozen=True, eq=True)
class MdList:
    """List: ordered (True) or unordered (False), with items."""
    ordered: bool
    items: tuple[tuple[MdBlock, ...], ...]


@dataclass(frozen=True, eq=True)
class MdThematicBreak:
    """Horizontal rule."""
    pass


@dataclass(frozen=True, eq=True)
class MdTable:
    """Table: rows × cells × inline content."""
    rows: tuple[tuple[tuple[MdInline, ...], ...], ...]


@dataclass(frozen=True, eq=True)
class MdDocument:
    """Top-level document: sequence of blocks."""
    children: tuple[MdBlock, ...]


MdBlock = (
    MdParagraph | MdHeading | MdCodeBlock | MdBlockQuote
    | MdList | MdThematicBreak | MdTable | MdDocument
)


# =====================================================================
# Block-level parser
# =====================================================================

# Block-level patterns.  Every one of them comes from
# ``vera/markdown_grammar.py``, which the browser runtime carries a
# generated copy of: the same pattern spelled twice is what made a ``+``
# bullet, an ``n)`` ordered marker and a separator-less table three
# different grammars across the two hosts (#1301).
_ATX_HEADING = re.compile(PATTERNS["atx_heading"])
_FENCE_OPEN = re.compile(PATTERNS["fence_open"])
_THEMATIC_BREAK = re.compile(PATTERNS["thematic_break"])
_BLOCKQUOTE_LINE = re.compile(PATTERNS["blockquote_line"])
_UNORDERED_ITEM = re.compile(PATTERNS["unordered_item"])
_ORDERED_ITEM = re.compile(PATTERNS["ordered_item"])
_TABLE_ROW = re.compile(PATTERNS["table_row"])
_TABLE_SEP = re.compile(PATTERNS["table_sep"])


def parse_markdown(text: str) -> MdDocument:
    """Parse a Markdown string into an MdDocument.

    This is the reference implementation for Vera's md_parse built-in.
    Supports the §9.7.3 subset: ATX headings, fenced code blocks, block
    quotes, ordered/unordered lists, thematic breaks, GFM tables, and
    paragraphs.  Inline parsing handles emphasis, strong, code spans,
    links, and images.
    """
    lines = text.split("\n")
    blocks = _parse_blocks(lines, 0, len(lines))
    return MdDocument(tuple(blocks))


def _parse_blocks(lines: list[str], start: int, end: int) -> list[MdBlock]:
    """Parse a range of lines into block-level elements."""
    blocks: list[MdBlock] = []
    i = start

    while i < end:
        line = lines[i]

        # Blank line — skip
        if is_blank(line):
            i += 1
            continue

        # ATX heading
        m = _ATX_HEADING.match(line)
        if m:
            level = len(m.group(1))
            content = trim(m.group(2))
            blocks.append(MdHeading(level, tuple(_parse_inlines(content))))
            i += 1
            continue

        # Fenced code block
        m = _FENCE_OPEN.match(line)
        if m:
            fence_char = m.group(1)[0]
            fence_len = len(m.group(1))
            lang = trim(m.group(2))
            code_lines: list[str] = []
            i += 1
            while i < end:
                close_match = re.match(
                    fence_close(fence_char, fence_len), lines[i],
                )
                if close_match:
                    i += 1
                    break
                code_lines.append(lines[i])
                i += 1
            blocks.append(MdCodeBlock(lang, "\n".join(code_lines)))
            continue

        # Thematic break
        if _THEMATIC_BREAK.match(line):
            blocks.append(MdThematicBreak())
            i += 1
            continue

        # Block quote
        bq_match = _BLOCKQUOTE_LINE.match(line)
        if bq_match:
            bq_lines: list[str] = []
            while i < end:
                bq_m = _BLOCKQUOTE_LINE.match(lines[i])
                if bq_m:
                    bq_lines.append(bq_m.group(1))
                elif not is_blank(lines[i]) and not _is_block_start(
                    lines[i],
                ):
                    # Lazy continuation
                    bq_lines.append(lines[i])
                else:
                    break
                i += 1
            inner = _parse_blocks(bq_lines, 0, len(bq_lines))
            blocks.append(MdBlockQuote(tuple(inner)))
            continue

        # GFM table (must have header + separator row)
        if _TABLE_ROW.match(line) and i + 1 < end and _TABLE_SEP.match(
            lines[i + 1]
        ):
            table_rows: list[tuple[tuple[MdInline, ...], ...]] = []
            # Header row
            table_rows.append(_parse_table_row(line))
            i += 2  # skip separator
            while i < end and _TABLE_ROW.match(lines[i]):
                table_rows.append(_parse_table_row(lines[i]))
                i += 1
            blocks.append(MdTable(tuple(table_rows)))
            continue

        # Unordered list
        ul_match = _UNORDERED_ITEM.match(line)
        if ul_match:
            items: list[tuple[MdBlock, ...]] = []
            while i < end:
                ul_m = _UNORDERED_ITEM.match(lines[i])
                if not ul_m:
                    break
                item_lines = [ul_m.group(1)]
                i += 1
                # Continuation lines lose a FIXED width — the marker plus
                # its space — not all their leading whitespace, which is
                # what keeps a third nesting level distinguishable from a
                # second (§9.7.3, #1301 class 6).
                width = CONTINUATION_INDENT["unordered"]
                indent = " " * width
                while (i < end and lines[i].startswith(indent)
                       and not is_blank(lines[i])):
                    item_lines.append(lines[i][width:])
                    i += 1
                # Skip blank lines between items
                while i < end and is_blank(lines[i]):
                    i += 1
                    # But only if next line is still a list item
                    if i < end and not _UNORDERED_ITEM.match(lines[i]):
                        break
                item_blocks = _parse_blocks(item_lines, 0, len(item_lines))
                items.append(tuple(item_blocks))
            blocks.append(MdList(False, tuple(items)))
            continue

        # Ordered list
        ol_match = _ORDERED_ITEM.match(line)
        if ol_match:
            items_ol: list[tuple[MdBlock, ...]] = []
            while i < end:
                ol_m = _ORDERED_ITEM.match(lines[i])
                if not ol_m:
                    break
                item_lines_ol = [ol_m.group(2)]
                i += 1
                # Continuation lines (fixed width, as above)
                width_ol = CONTINUATION_INDENT["ordered"]
                indent_ol = " " * width_ol
                while (i < end and lines[i].startswith(indent_ol)
                       and not is_blank(lines[i])):
                    item_lines_ol.append(lines[i][width_ol:])
                    i += 1
                # Skip blank lines between items
                while i < end and is_blank(lines[i]):
                    i += 1
                    if i < end and not _ORDERED_ITEM.match(lines[i]):
                        break
                item_blocks_ol = _parse_blocks(
                    item_lines_ol, 0, len(item_lines_ol),
                )
                items_ol.append(tuple(item_blocks_ol))
            blocks.append(MdList(True, tuple(items_ol)))
            continue

        # Paragraph (default fallback — collect until blank or block start)
        para_lines: list[str] = []
        while (i < end and not is_blank(lines[i])
               and not _is_block_start(lines[i])):
            para_lines.append(lines[i])
            i += 1
        if para_lines:
            text_content = " ".join(para_lines)
            blocks.append(
                MdParagraph(tuple(_parse_inlines(text_content))),
            )

    return blocks


def _is_block_start(line: str) -> bool:
    """Check if a line starts a new block-level construct."""
    if _ATX_HEADING.match(line):
        return True
    if _FENCE_OPEN.match(line):
        return True
    if _THEMATIC_BREAK.match(line):
        return True
    if _BLOCKQUOTE_LINE.match(line):
        return True
    if _UNORDERED_ITEM.match(line):
        return True
    if _ORDERED_ITEM.match(line):
        return True
    return False


def _parse_table_row(line: str) -> tuple[tuple[MdInline, ...], ...]:
    """Parse a GFM table row into cells of inline content."""
    # Strip leading/trailing pipes and split
    content = trim(line)
    if content.startswith("|"):
        content = content[1:]
    if content.endswith("|"):
        content = content[:-1]
    cells = content.split("|")
    return tuple(tuple(_parse_inlines(trim(cell))) for cell in cells)


# =====================================================================
# Inline-level parser
# =====================================================================

def _parse_inlines(text: str) -> list[MdInline]:
    """Parse inline Markdown content into MdInline nodes.

    Handles: code spans, images, links, strong (**), emphasis (*), and
    plain text.  Processes left-to-right with greedy matching.
    """
    result: list[MdInline] = []
    i = 0
    buf: list[str] = []  # accumulator for plain text

    def flush_text() -> None:
        if buf:
            result.append(MdText("".join(buf)))
            buf.clear()

    while i < len(text):
        ch = text[i]

        # Inline code span
        if ch == "`":
            # Count backtick run length
            run_start = i
            while i < len(text) and text[i] == "`":
                i += 1
            run_len = i - run_start
            # Find matching closing run
            close_pat = "`" * run_len
            close_idx = text.find(close_pat, i)
            if close_idx != -1:
                flush_text()
                code_content = text[i:close_idx]
                # Strip one leading/trailing space if both present
                if (len(code_content) >= 2
                        and code_content[0] == " "
                        and code_content[-1] == " "):
                    code_content = code_content[1:-1]
                result.append(MdCode(code_content))
                i = close_idx + run_len
            else:
                buf.append(close_pat[:run_len])
            continue

        # Image: ![alt](src)
        if ch == "!" and i + 1 < len(text) and text[i + 1] == "[":
            close_bracket = _find_matching_bracket(text, i + 1)
            if close_bracket is not None and close_bracket + 1 < len(text) and text[close_bracket + 1] == "(":
                close_paren = text.find(")", close_bracket + 2)
                if close_paren != -1:
                    flush_text()
                    alt = text[i + 2:close_bracket]
                    src = text[close_bracket + 2:close_paren]
                    result.append(MdImage(alt, src))
                    i = close_paren + 1
                    continue
            buf.append(ch)
            i += 1
            continue

        # Link: [text](url)
        if ch == "[":
            close_bracket = _find_matching_bracket(text, i)
            if close_bracket is not None and close_bracket + 1 < len(text) and text[close_bracket + 1] == "(":
                close_paren = text.find(")", close_bracket + 2)
                if close_paren != -1:
                    flush_text()
                    link_text = text[i + 1:close_bracket]
                    url = text[close_bracket + 2:close_paren]
                    children = _parse_inlines(link_text)
                    result.append(MdLink(tuple(children), url))
                    i = close_paren + 1
                    continue
            buf.append(ch)
            i += 1
            continue

        # Strong (**) or emphasis (*)
        if ch == "*" or ch == "_":
            # Count delimiter run
            delim = ch
            run_start = i
            while i < len(text) and text[i] == delim:
                i += 1
            run_len = i - run_start

            if run_len >= 2:
                # Try strong first (**)
                close_idx = text.find(delim * 2, i)
                if close_idx != -1:
                    flush_text()
                    inner = _parse_inlines(text[i:close_idx])
                    result.append(MdStrong(tuple(inner)))
                    i = close_idx + 2
                    # Handle remaining delimiters from the opening run
                    remaining = run_len - 2
                    if remaining > 0:
                        # Leftover * becomes emphasis or text
                        close_single = text.find(delim, i)
                        if remaining == 1 and close_single != -1:
                            inner2 = _parse_inlines(text[i:close_single])
                            result.append(MdEmph(tuple(inner2)))
                            i = close_single + 1
                        else:
                            buf.append(delim * remaining)
                    continue
                # Fall through to try single emphasis
                i = run_start + 1
                run_len = 1

            if run_len == 1:
                # Emphasis (*)
                close_idx = text.find(delim, i)
                if close_idx != -1:
                    flush_text()
                    inner = _parse_inlines(text[i:close_idx])
                    result.append(MdEmph(tuple(inner)))
                    i = close_idx + 1
                    continue
                else:
                    buf.append(delim)
                    continue

        # Plain character
        buf.append(ch)
        i += 1

    flush_text()
    return result


def _find_matching_bracket(text: str, start: int) -> int | None:
    """Find the matching ] for a [ at position start."""
    if start >= len(text) or text[start] != "[":
        return None
    depth = 0
    i = start
    while i < len(text):
        if text[i] == "[":
            depth += 1
        elif text[i] == "]":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


# =====================================================================
# Renderer — MdBlock/MdInline → canonical Markdown string
# =====================================================================

def render_markdown(block: MdBlock) -> str:
    """Render an MdBlock to a canonical Markdown string.

    The round-trip property md_parse(md_render(b)) ≈ b should hold
    for well-formed documents.
    """
    lines = _render_block(block)
    return "\n".join(lines)


def _render_block(block: MdBlock) -> list[str]:
    """Render a single block to lines of Markdown."""
    if isinstance(block, MdDocument):
        result: list[str] = []
        for child in block.children:
            child_lines = _render_block(child)
            # #1303 review: a child that renders to NOTHING — an
            # `MdList` with no items, an `MdTable` with no rows — must
            # not drag a separator in with it.  Counting it made the
            # separator a stray blank line the next parse cannot
            # attribute to anything, so `MdDocument([MdList([]), p])`
            # rendered "\nafter" and re-rendered "after": not a fixed
            # point, which is the property §9.7.3 asks of the render.
            if not child_lines:
                continue
            if result:
                result.append("")
            result.extend(child_lines)
        return result

    if isinstance(block, MdParagraph):
        return [_render_inlines(block.children)]

    if isinstance(block, MdHeading):
        prefix = "#" * block.level
        return [f"{prefix} {_render_inlines(block.children)}"]

    if isinstance(block, MdCodeBlock):
        lines = [f"```{block.language}"]
        lines.extend(block.code.split("\n"))
        lines.append("```")
        return lines

    if isinstance(block, MdBlockQuote):
        if not block.children:
            # A quote with nothing in it still occupies a line.  Render
            # it as no lines at all and the block vanishes on re-parse,
            # leaving the document's separator as a stray blank line —
            # `---\n>` renders `---\n` and comes back as just `---`.
            return [">"]
        result = []
        for i, child in enumerate(block.children):
            # #1294 review: a bare ``>`` between children, exactly as
            # MdDocument puts a blank line between its own.  Without it
            # a quote holding two paragraphs renders as two adjacent
            # quoted lines, which re-parses as ONE paragraph — the
            # structure is gone and no later pass can tell.  The
            # separator is unconditional rather than emitted only where
            # the next block would otherwise merge: one construct, one
            # textual representation (§0.2.3).
            child_lines = _render_block(child)
            # Same zero-line guard as MdDocument: a child that renders
            # nothing must not leave a bare `>` standing for it.
            if not child_lines:
                continue
            if i > 0 and result:
                result.append(">")
            for line in child_lines:
                result.append(f"> {line}" if line else ">")
        return result

    if isinstance(block, MdList):
        result = []
        for idx, item in enumerate(block.items):
            marker = f"{idx + 1}." if block.ordered else "-"
            item_lines: list[str] = []
            for child in item:
                item_lines.extend(_render_block(child))
            if not item_lines:
                # #1303 review: an item with no blocks is a value the
                # PARSER produces — `- ` reads back as `MdList([()])` —
                # so the renderer owed it a form.  Dropping it deleted
                # the item outright, and in a multi-item list silently
                # renumbered everything after it.  The marker plus its
                # space is what the parser reads back: a bare `-` is a
                # paragraph, because both item patterns require the
                # whitespace.
                result.append(f"{marker} ")
                continue
            for j, line in enumerate(item_lines):
                if j == 0:
                    result.append(f"{marker} {line}")
                else:
                    indent = " " * (len(marker) + 1)
                    result.append(f"{indent}{line}")
        return result

    if isinstance(block, MdThematicBreak):
        return ["---"]

    if isinstance(block, MdTable):
        if not block.rows:
            return []
        result = []
        # Header row
        header = block.rows[0]
        header_cells = [_render_inlines(cell) for cell in header]
        result.append("| " + " | ".join(header_cells) + " |")
        # Separator
        sep_cells = ["---"] * len(header)
        result.append("| " + " | ".join(sep_cells) + " |")
        # Data rows
        for row in block.rows[1:]:
            cells = [_render_inlines(cell) for cell in row]
            result.append("| " + " | ".join(cells) + " |")
        return result

    return []


def _render_code_span(code: str) -> str:
    """Fence a code span so it reads back as itself.

    The fence is one backtick longer than the longest run *inside* the
    content, because `_parse_inlines` closes a span on the first run of
    equal length — a fixed two-backtick fence therefore terminates on
    the content's own ``` `` ``` and loses the rest.

    Padding spaces are added in exactly the two cases where the parser
    would otherwise not read the content back.  `_parse_inlines` strips
    one leading and one trailing space iff the fenced text is at least
    two characters long and both ends are spaces, so the renderer pads
    when:

    * the content starts or ends with a backtick — the pad is what keeps
      the fence and the content from merging into one longer run; and
    * the content itself starts and ends with a space (#1303 review) —
      without a pad the parser's unconditional strip eats the content's
      own spaces, so ``MdCode(" x ")`` came back as ``MdCode("x")``.
      With it the strip removes the pad instead and the content
      survives, which also separates ``MdCode(" `x` ")`` from
      ``MdCode("`x`")``: both used to render to the same bytes.
    """
    longest = 0
    run = 0
    for ch in code:
        run = run + 1 if ch == "`" else 0
        longest = max(longest, run)
    fence = "`" * (longest + 1)
    strips_own_spaces = (
        len(code) >= 2 and code[0] == " " and code[-1] == " "
    )
    pad = (
        " "
        if code.startswith("`") or code.endswith("`") or strips_own_spaces
        else ""
    )
    return f"{fence}{pad}{code}{pad}{fence}"


def _render_inlines(inlines: tuple[MdInline, ...]) -> str:
    """Render inline content to a string."""
    parts: list[str] = []
    for inline in inlines:
        if isinstance(inline, MdText):
            parts.append(inline.text)
        elif isinstance(inline, MdCode):
            parts.append(_render_code_span(inline.code))
        elif isinstance(inline, MdEmph):
            parts.append(f"*{_render_inlines(inline.children)}*")
        elif isinstance(inline, MdStrong):
            parts.append(f"**{_render_inlines(inline.children)}**")
        elif isinstance(inline, MdLink):
            text = _render_inlines(inline.children)
            parts.append(f"[{text}]({inline.url})")
        elif isinstance(inline, MdImage):
            parts.append(f"![{inline.alt}]({inline.src})")
    return "".join(parts)


# =====================================================================
# Query functions
# =====================================================================

def has_heading(block: MdBlock, level: int) -> bool:
    """Return True if the block tree contains a heading of the given level."""
    if isinstance(block, MdHeading):
        return block.level == level
    if isinstance(block, MdDocument):
        return any(has_heading(child, level) for child in block.children)
    if isinstance(block, MdBlockQuote):
        return any(has_heading(child, level) for child in block.children)
    if isinstance(block, MdList):
        return any(
            has_heading(child, level)
            for item in block.items
            for child in item
        )
    return False


def has_code_block(block: MdBlock, language: str) -> bool:
    """Return True if the block tree contains a code block with the given language."""
    if isinstance(block, MdCodeBlock):
        return block.language == language
    if isinstance(block, MdDocument):
        return any(has_code_block(child, language) for child in block.children)
    if isinstance(block, MdBlockQuote):
        return any(has_code_block(child, language) for child in block.children)
    if isinstance(block, MdList):
        return any(
            has_code_block(child, language)
            for item in block.items
            for child in item
        )
    return False


def extract_code_blocks(block: MdBlock, language: str) -> list[str]:
    """Extract code from all code blocks with the given language tag."""
    results: list[str] = []
    _collect_code_blocks(block, language, results)
    return results


def _collect_code_blocks(
    block: MdBlock, language: str, acc: list[str],
) -> None:
    """Recursively collect code block contents matching a language."""
    if isinstance(block, MdCodeBlock):
        if block.language == language:
            acc.append(block.code)
    elif isinstance(block, MdDocument):
        for child in block.children:
            _collect_code_blocks(child, language, acc)
    elif isinstance(block, MdBlockQuote):
        for child in block.children:
            _collect_code_blocks(child, language, acc)
    elif isinstance(block, MdList):
        for item in block.items:
            for child in item:
                _collect_code_blocks(child, language, acc)
