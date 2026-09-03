"""Shared corpus and canonical ADT encoding for the `md_parse` parity gate.

Both legs of the #1301 differential read this module: the reference leg
imports :func:`md_corpus` and :func:`encode_block` directly, and the
browser leg gets the *same* corpus handed to it as JSON so the two
parsers are asked the identical bytes.  A corpus written twice would let
the gate pass on two hosts that were never sent the same input.

The encoding is deliberately positional and ASCII-only, so the two sides
can be compared as *bytes* rather than as re-parsed structures:
``json.dumps(..., ensure_ascii=True, separators=(",", ":"))`` and the
bridge's ``JSON.stringify`` + non-ASCII escaper produce the same text for
the same tree.  Comparing bytes is what makes the gate see a divergence
in how a paragraph's plain-text *runs are grouped* — a difference that
survives every render-level comparison, because the runs concatenate to
the same string.
"""

from __future__ import annotations

import json
import random
from typing import Any

from vera.markdown import (
    MdBlock,
    MdBlockQuote,
    MdCode,
    MdCodeBlock,
    MdDocument,
    MdEmph,
    MdHeading,
    MdImage,
    MdInline,
    MdLink,
    MdList,
    MdParagraph,
    MdStrong,
    MdTable,
    MdText,
    MdThematicBreak,
)

# ---------------------------------------------------------------------------
# Canonical encoding
# ---------------------------------------------------------------------------


def encode_inline(node: MdInline) -> Any:
    """Encode one `MdInline` as a positional JSON value."""
    if isinstance(node, MdText):
        return ["text", node.text]
    if isinstance(node, MdCode):
        return ["code", node.code]
    if isinstance(node, MdEmph):
        return ["emph", [encode_inline(c) for c in node.children]]
    if isinstance(node, MdStrong):
        return ["strong", [encode_inline(c) for c in node.children]]
    if isinstance(node, MdLink):
        return ["link", [encode_inline(c) for c in node.children], node.url]
    if isinstance(node, MdImage):
        return ["image", node.alt, node.src]
    raise TypeError(f"unknown MdInline node: {node!r}")


def encode_block(node: MdBlock) -> Any:
    """Encode one `MdBlock` as a positional JSON value."""
    if isinstance(node, MdParagraph):
        return ["para", [encode_inline(c) for c in node.children]]
    if isinstance(node, MdHeading):
        return [
            "heading", node.level, [encode_inline(c) for c in node.children],
        ]
    if isinstance(node, MdCodeBlock):
        return ["code_block", node.language, node.code]
    if isinstance(node, MdBlockQuote):
        return ["quote", [encode_block(c) for c in node.children]]
    if isinstance(node, MdList):
        return [
            "list",
            node.ordered,
            [[encode_block(b) for b in item] for item in node.items],
        ]
    if isinstance(node, MdThematicBreak):
        return ["break"]
    if isinstance(node, MdTable):
        return [
            "table",
            [
                [[encode_inline(i) for i in cell] for cell in row]
                for row in node.rows
            ],
        ]
    if isinstance(node, MdDocument):
        return ["doc", [encode_block(c) for c in node.children]]
    raise TypeError(f"unknown MdBlock node: {node!r}")


def encode_json(node: MdBlock) -> str:
    """Encode a block as the exact text the browser bridge emits."""
    return json.dumps(
        encode_block(node), ensure_ascii=True, separators=(",", ":"),
    )


# ---------------------------------------------------------------------------
# Corpus
# ---------------------------------------------------------------------------

# The divergence classes #1301 measured, each with the one-line repro the
# issue records.  Keeping the ids equal to the class names means a failure
# report names the class directly.
#
# Class 4 (*tight bullet marker*, 7 inputs, "table-adjacent") is absent:
# the issue records no repro for it — its repro, native and browser
# columns are all "—" — and no bullet-beside-a-table shape tried here
# reproduces it.  Rather than invent one, it is left to the generated
# sweep below, which takes every bullet marker against every table line.
CLASS_REPROS: list[tuple[str, str]] = [
    ("class1_plain_text_runs", "**unclosed"),
    ("class2_continuation_indent", "- a\n   b"),
    ("class3_emphasis_scanning", "***both***"),
    ("class5_table_without_separator", "| a | b |\n- li"),
    ("class6_list_nesting_three", "- a\n  - b\n    - c"),
    ("class7_loose_list", "- a\n\n- b"),
    ("class8_break_internal_spaces", "*   *   *"),
    ("class9_plus_bullet", "+ item"),
    ("class9_paren_ordered", "1) one"),
]

# Structural block shapes: every line template the §9.7.3 subset can open
# a block with, plus the near-misses that decide which branch takes the
# line.  The generator below takes them 1, 2 and 3 at a time, so a
# dispatch-order difference between the two parsers shows up as soon as
# two branches compete for the same line.
_BLOCK_LINES: list[str] = [
    "# h1",
    "###### h6",
    "####### seven",
    "#nospace",
    "## trailing ##",
    "```py",
    "~~~",
    "```",
    "code body",
    "---",
    "***",
    "___",
    "*   *   *",
    "- - -",
    "----",
    "> quoted",
    ">nospace",
    ">",
    "- a",
    "* a",
    "+ a",
    "-nospace",
    "1. one",
    "2) two",
    "10. ten",
    "1.nospace",
    "| a | b |",
    "| --- | --- |",
    "| :-: | ---: |",
    "|single",
    "a | b",
    "plain text",
    "  indented two",
    "   indented three",
    "\tindented tab",
    "",
    "   ",
]

# Inline shapes, each parsed inside a one-line paragraph.  Delimiter runs
# of every length up to four, matched and unmatched, because the
# reference's run-length scan and a naive two-character scan agree on the
# matched cases and part company on the rest.
_INLINE_TEXTS: list[str] = [
    "plain",
    "*em*",
    "**strong**",
    "***both***",
    "****quad****",
    "*unclosed",
    "**unclosed",
    "***unclosed",
    "a*b*c",
    "a**b**c",
    "a***b***c",
    "_em_",
    "__strong__",
    "___both___",
    "_unclosed",
    "__unclosed",
    "*a_b*",
    "_a*b_",
    "**a*b**",
    "*a**b*",
    "`code`",
    "``a`b``",
    "```triple```",
    "`unclosed",
    "``unclosed`",
    "` x `",
    "`  `",
    "``",
    "a`b`c",
    "[text](url)",
    "[](url)",
    "[text]()",
    "[unclosed(url)",
    "[text]no-paren",
    "[a[b]c](url)",
    "![alt](src)",
    "![](src)",
    "!not-an-image",
    "![alt]no-paren",
    "[*em*](url)",
    "![*em*](src)",
    "*[link](url)*",
    "`*not em*`",
    "*`code`*",
    "text *em* `code` [l](u) ![i](s) **s** end",
    "*",
    "**",
    "***",
    "_",
    "__",
    "`",
    "[",
    "]",
    "!",
    "![",
    "*a",
    "a*",
    "**a",
    "a**",
    "a * b * c",
    "a ** b ** c",
]

# Delimiter-run boundaries — the shapes that pin §9.7.3's two scan rules
# and separate them from the readings they are easily mistaken for
# (#1386 review).  A code span closes at the next OCCURRENCE of its run
# length, which may be the leading part of a longer run, so `x`` is a
# span plus a literal backtick rather than literal text throughout; and
# an emphasis run of two or more with no closing pair is retried from
# its own second character, so it yields an EMPTY emphasis rather than
# literal text.  Both hosts already agree here — these keep it that way,
# and keep the spec sentence honest about which reading is canonical.
_SPAN_LINES: list[str] = [
    "`x``",
    "``x`",
    "`x```",
    "```x`",
    "``x```",
    "`a`b`",
    "``a``b``",
    "` `",
    "`  `",
    "`   `",
    "*unclosed",
    "**unclosed",
    "***unclosed",
    "****unclosed",
    "**a*b",
    "***a**b",
]

# Carriage returns: a CRLF document split on "\n" leaves a trailing "\r"
# on every line, and a lone "\r" can appear mid-line.  ECMAScript's "."
# excludes "\r" where Python's does not, so these are the shapes that
# tell a grammar naming its own character classes from one leaning on
# the shorthands (see vera/markdown_grammar.py).
_CR_LINES: list[str] = [
    "# heading\r",
    "###### six\r",
    "para\r",
    "- item\r",
    "1. item\r",
    "> quote\r",
    "---\r",
    "```py\r",
    "| a | b |\r\n| --- | --- |\r",
    "# a\rb",
    "para\rmore",
    "- a\r- b",
    "\r",
    "a\r\nb\r\n",
]

# Whitespace the two hosts' *shorthands* disagree about.  `String.trim`
# strips U+00A0, U+3000 and U+FEFF where `str.strip` does not, and
# `str.strip` strips U+001C..U+001F and U+0085 where `String.trim` does
# not; a regex `\s` covers a third set again.  The grammar names its own
# class precisely so none of that leaks in, and these are the inputs that
# hold it to it — without them a parser reverting to `trim()` passes the
# whole corpus unnoticed (measured: it did).
_WS_CLASS_LINES: list[str] = [
    "# heading\u00a0",
    "#\u00a0heading",
    "para\u00a0",
    "para\u3000",
    "\ufeffpara",
    "- item\u00a0",
    "-\u00a0item",
    "1.\u00a0item",
    "> quote\u00a0",
    "---\u00a0",
    "\u00a0",
    "\u001c",
    "para\u0085more",
    "```py\u00a0\ncode\n```",
    "|\u00a0a\u00a0|\u00a0b\u00a0|\n| --- | --- |",
    "- a\n\u00a0 b",
]

# Alphabet for the seeded fuzz leg: markdown-significant tokens beside
# ordinary words, so a random draw produces plausible-but-adversarial
# documents rather than noise no parser branch reaches.  Deliberately no
# exotic whitespace — the shared grammar names its whitespace class
# explicitly (spec §9.7.3), and a corpus of U+00A0 would test that
# decision rather than the parsers.
_FUZZ_TOKENS: list[str] = [
    "#", "##", "###", "- ", "* ", "+ ", "1. ", "2) ", "> ", ">", "|",
    "```", "~~~", "---", "***", "___", "`", "``", "*", "**", "_", "__",
    "[", "]", "(", ")", "!", "word", "a", " ", "  ", "   ", "\t", ":",
    "-", "text", "x",
]


def _fuzz_documents(count: int, seed: int) -> list[tuple[str, str]]:
    """Deterministic pseudo-random documents built from `_FUZZ_TOKENS`."""
    rng = random.Random(seed)
    out: list[tuple[str, str]] = []
    for n in range(count):
        lines = []
        for _ in range(rng.randint(1, 5)):
            lines.append(
                "".join(
                    rng.choice(_FUZZ_TOKENS)
                    for _ in range(rng.randint(1, 7))
                )
            )
        out.append((f"fuzz{n:04d}", "\n".join(lines)))
    return out


def md_corpus() -> list[tuple[str, str]]:
    """The full `(case_id, markdown)` corpus, in a stable order.

    Deterministic: the same list on every run and on every platform, so a
    divergence reported by the gate is reproducible from its id alone.
    """
    cases: list[tuple[str, str]] = list(CLASS_REPROS)

    for idx, line in enumerate(_BLOCK_LINES):
        cases.append((f"block1_{idx:02d}", line))
    for i, first in enumerate(_BLOCK_LINES):
        for j, second in enumerate(_BLOCK_LINES):
            cases.append((f"block2_{i:02d}_{j:02d}", f"{first}\n{second}"))
    # Three-line shapes are the ones that reach a continuation *inside* an
    # already-open block (a list item's second line, a quote's lazy third).
    # Taking the full product would be 47k documents; a rotation over the
    # openers keeps every opener paired with every follower twice.
    for i, first in enumerate(_BLOCK_LINES):
        for j, second in enumerate(_BLOCK_LINES):
            third = _BLOCK_LINES[(i + j) % len(_BLOCK_LINES)]
            cases.append(
                (f"block3_{i:02d}_{j:02d}", f"{first}\n{second}\n{third}"),
            )

    for idx, text in enumerate(_INLINE_TEXTS):
        cases.append((f"inline_{idx:02d}", text))
        # The same inline content in the three other positions that reach
        # the inline parser: a heading, a quote, and a table cell.
        cases.append((f"inline_h_{idx:02d}", f"## {text}"))
        cases.append((f"inline_q_{idx:02d}", f"> {text}"))
        cases.append(
            (f"inline_t_{idx:02d}", f"| {text} | b |\n| --- | --- |"),
        )

    for idx, line in enumerate(_CR_LINES):
        cases.append((f"cr_{idx:02d}", line))
    for idx, line in enumerate(_WS_CLASS_LINES):
        cases.append((f"ws_{idx:02d}", line))
    for idx, line in enumerate(_SPAN_LINES):
        cases.append((f"span_{idx:02d}", line))

    cases.extend(_fuzz_documents(600, seed=1301))
    return cases
