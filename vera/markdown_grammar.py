"""The §9.7.3 Markdown grammar — one table, read by both runtimes.

`md_parse` has two implementations: `vera/markdown.py` (the reference,
used by the CLI host) and the port in `vera/browser/runtime.mjs`.  Spec
§12.9.3 requires them to agree, and for a long time they did not: nine
measured divergence classes (#1301), of which three — a ``+`` bullet, an
``n)`` ordered marker, and a table with no separator row — were nothing
more than the two files spelling the same pattern differently.

So the patterns live here, once, and the browser runtime carries a
*generated* copy emitted by :func:`js_grammar_block`, which
``tests/test_browser.py`` asserts is byte-identical.  Editing a pattern
on one side and not the other is no longer possible without the gate
going red.

Two portability rules make a shared pattern mean the same thing to
Python's ``re`` and to ECMAScript's ``RegExp``, and both are the reason
the table names its character classes rather than using the shorthands:

* ``\\s`` matches Unicode whitespace in Python and a *different* Unicode
  set in ECMAScript, and ``\\d`` matches Unicode digits in Python but
  only ``[0-9]`` in ECMAScript.  :data:`WS` and :data:`DIGIT` name the
  ASCII sets both engines agree on.
* ``.`` excludes ``\\n`` in Python and ``\\n \\r \\u2028 \\u2029`` in
  ECMAScript, so a line carrying a lone ``\\r`` — a CRLF document split
  on ``\\n`` — matches in one engine and not the other.  :data:`ANY`
  names the Python set explicitly.

The same reasoning applies to ``str.strip()`` and ``String.trim()``,
which strip different sets: :func:`trim` and :func:`is_blank` are what
both parsers use instead, over :data:`WS_CHARS`.
"""

from __future__ import annotations

import json

# ---------------------------------------------------------------------------
# Character classes
# ---------------------------------------------------------------------------

#: The whitespace a line can carry, as literal characters.  Excludes
#: ``\n``, which never survives the line split.
WS_CHARS = " \t\r\x0b\x0c"

#: The same set, as a regex character class.
WS = "[ \\t\\r\\x0b\\x0c]"

#: The characters usable *inside* another class (no brackets).
_WS_INNER = " \\t\\r\\x0b\\x0c"

#: Any character a line can hold — Python's ``.``, spelled out.
ANY = "[^\\n]"

#: ASCII digits.  Python's ``\\d`` would also admit e.g. Devanagari.
DIGIT = "[0-9]"


# ---------------------------------------------------------------------------
# Block-level patterns
# ---------------------------------------------------------------------------

#: Every block-opening pattern, keyed by construct.  Order of dispatch is
#: NOT expressed here — it lives in the two parsers, which walk the
#: constructs in the order §9.7.3 states.
PATTERNS: dict[str, str] = {
    "atx_heading": f"^(#{{1,6}}){WS}+({ANY}*?)(?:{WS}+#+{WS}*)?$",
    "fence_open": f"^(`{{3,}}|~{{3,}}){WS}*({ANY}*?)$",
    "thematic_break": f"^(?:---+|\\*\\*\\*+|___+){WS}*$",
    "blockquote_line": f"^>{WS}?({ANY}*)",
    "unordered_item": f"^[-*+]{WS}+({ANY}*)",
    "ordered_item": f"^({DIGIT}+)[.)]{WS}+({ANY}*)",
    "table_row": f"^\\|({ANY}+)\\|?{WS}*$",
    "table_sep": f"^\\|[{_WS_INNER}:]*-[-{_WS_INNER}:|]*\\|?{WS}*$",
}

#: How many characters a continuation line loses, per list kind.  The
#: reference strips a fixed width — the marker plus its space — rather
#: than all leading whitespace, which is what keeps a third nesting level
#: distinguishable from a second (`- a / ``  - b`` / ``    - c``).
CONTINUATION_INDENT: dict[str, int] = {"unordered": 2, "ordered": 3}


def fence_close(fence_char: str, fence_len: int) -> str:
    """Pattern closing a fence opened with `fence_len` of `fence_char`."""
    escaped = "\\`" if fence_char == "`" else "~"
    return f"^{escaped}{{{fence_len},}}{WS}*$"


# ---------------------------------------------------------------------------
# Whitespace helpers (the shared spelling of ``strip`` / ``trim``)
# ---------------------------------------------------------------------------


def trim(text: str) -> str:
    """Strip :data:`WS_CHARS` from both ends."""
    return text.strip(WS_CHARS)


def is_blank(line: str) -> bool:
    """Is this line nothing but :data:`WS_CHARS`?"""
    return not line.strip(WS_CHARS)


# ---------------------------------------------------------------------------
# JavaScript emission
# ---------------------------------------------------------------------------

_JS_HEADER = """\
// --- BEGIN GENERATED: §9.7.3 Markdown grammar ---
// Source of truth: vera/markdown_grammar.py.  Do not hand-edit — the
// #1301 gate in tests/test_browser.py asserts this block is byte-for-byte
// what the generator emits.  Regenerate with:
//   python -c "from vera.markdown_grammar import js_grammar_block as g; print(g())"
"""

_JS_FOOTER = """\
const MD_RE = {};
for (const [key, pattern] of Object.entries(MD_PATTERNS)) {
  MD_RE[key] = new RegExp(pattern);
}
function mdFenceClose(fenceChar, fenceLen) {
  const escaped = fenceChar === '`' ? '\\\\`' : '~';
  return new RegExp('^' + escaped + '{' + fenceLen + ',}' + MD_WS + '*$');
}
// --- END GENERATED: §9.7.3 Markdown grammar ---"""


def js_grammar_block() -> str:
    """The generated JavaScript the browser runtime must carry verbatim."""
    lines = [_JS_HEADER]
    lines.append(f"const MD_WS_CHARS = {json.dumps(WS_CHARS)};")
    lines.append(f"const MD_WS = {json.dumps(WS)};")
    lines.append("const MD_PATTERNS = {")
    for key, pattern in PATTERNS.items():
        lines.append(f"  {json.dumps(key)}: {json.dumps(pattern)},")
    lines.append("};")
    lines.append("const MD_CONTINUATION_INDENT = {")
    for key, width in CONTINUATION_INDENT.items():
        lines.append(f"  {json.dumps(key)}: {width},")
    lines.append("};")
    lines.append(_JS_FOOTER)
    return "\n".join(lines)


if __name__ == "__main__":  # pragma: no cover — regeneration entry point
    print(js_grammar_block())
