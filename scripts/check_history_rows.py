#!/usr/bin/env python3
"""Hold HISTORY.md's stage tables and stage introductions to the file's rule (#1880).

HISTORY.md states its own rule: a version row is "one sentence, at most one
issue link", and CHANGELOG.md is the per-release log of record.  This gate
holds the file to it, and to the length of its early stages:

- A row of a stage's "What shipped" table (``| vX.Y.Z | date | text |``, a
  ``vA–vB`` range, or ``| – | date | text |`` for a change no release
  carries), its header and rule line excepted, is one sentence after its
  leading bold label, holds at most one issue or pull-request link and no em
  dash, and is at most ``ROW_CAP`` words.  A sentence end is counted with
  each code span read as one token, so punctuation inside a span never ends
  a sentence and a span that opens one still counts.
- A stage's prose, every line from a ``## Stage N`` or ``## Stages N–M``
  heading to the next ``## `` heading that is not a table row or a ``---``
  rule, its italic tagline included, is at most ``STAGE_CAP`` words.

Words are whitespace tokens after a link is reduced to its text and ``**``,
``*``, backticks and ``\\|`` escapes are removed.  The caps are ceilings set
from the file's own early entries (rows of v0.0.1 to v0.2.1 reach 34 words,
Stages 1 to 20 reach 85), not targets: a row names its release's theme in
about twenty words.

Usage: ``python scripts/check_history_rows.py [PATH]`` (default HISTORY.md).
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

ROW_CAP = 35
STAGE_CAP = 85

_ROW = re.compile(r"^\|[^|]*\|[^|]*\|(?P<text>.*)\|\s*$")
_TABLE_RULE = re.compile(r"^\|[\s:|-]+\|\s*$")
_TABLE_HEADER = "What shipped"
_STAGE = re.compile(r"^## Stages? \d")
_CODE_SPAN = re.compile(r"`[^`]*`")
_CODE_TOKEN = "`code"
_LINK = re.compile(r"\[([^\]]*)\]\([^)]*\)")
_ISSUE_LINK = re.compile(r"\]\(https://github\.com/aallan/vera/(?:issues|pull)/\d+\)")
_LABEL = re.compile(r"^\*\*[^*]+\*\*:?\s*")
_SENTENCE_END = re.compile(r"[.!?]\s+(?=[A-Z`*(\[])")
_EM_DASH = "—"


@dataclass(frozen=True)
class Violation:
    line: int
    rule: str
    detail: str


def plain(text: str) -> str:
    """The text a reader reads: links as their text, no markup."""
    text = text.replace("\\|", "|")
    text = _LINK.sub(r"\1", text)
    return text.replace("**", "").replace("*", "").replace("`", "")


def word_count(text: str) -> int:
    return len(plain(text).split())


def sentence_text(text: str) -> str:
    """The text sentence ends are counted on.

    Each code span becomes one fixed token that begins with a backtick, so
    punctuation inside a span or a path never ends a sentence, and a span that
    opens a sentence still marks the sentence before it as ended.
    """
    text = text.replace("\\|", "|")
    text = _CODE_SPAN.sub(_CODE_TOKEN, text)
    text = _LINK.sub(r"\1", text)
    return text.replace("**", "").replace("*", "")


def sentence_count(text: str) -> int:
    """Sentences after the row's leading bold label, if it has one."""
    body = sentence_text(_LABEL.sub("", text.strip()))
    return 1 + len(_SENTENCE_END.findall(body))


def check_row(text: str, line: int) -> list[Violation]:
    out = []
    words = word_count(text)
    if words > ROW_CAP:
        out.append(Violation(line, "row over the word cap", f"{words} words (cap {ROW_CAP})"))
    sentences = sentence_count(text)
    if sentences > 1:
        out.append(Violation(line, "row is more than one sentence", f"{sentences} sentences"))
    links = len(_ISSUE_LINK.findall(text))
    if links > 1:
        out.append(Violation(line, "row has more than one issue link", f"{links} links"))
    if _EM_DASH in text:
        out.append(Violation(line, "row has an em dash", "use a colon, a semicolon or two clauses"))
    return out


def check_text(source: str) -> list[Violation]:
    lines = source.splitlines()
    out: list[Violation] = []
    i = 0
    while i < len(lines):
        if not _STAGE.match(lines[i]):
            i += 1
            continue
        heading = i + 1
        prose = []
        j = i + 1
        while j < len(lines) and not lines[j].startswith("## "):
            text = lines[j].strip()
            if text.startswith("|"):
                row = _ROW.match(text)
                if row and _TABLE_HEADER not in text and not _TABLE_RULE.match(text):
                    out.extend(check_row(row.group("text"), j + 1))
            elif text and text != "---":
                prose.append(text)
            j += 1
        words = word_count(" ".join(prose))
        if words > STAGE_CAP:
            out.append(Violation(
                heading, "stage prose over the word cap", f"{words} words (cap {STAGE_CAP})"))
        i = j
    return sorted(out, key=lambda v: v.line)


def main(argv: list[str]) -> int:
    path = Path(argv[0]) if argv else ROOT / "HISTORY.md"
    violations = check_text(path.read_text(encoding="utf-8"))
    if not violations:
        print(f"check_history_rows: OK: every stage-table row and stage in {path.name} is within its rule.")
        return 0
    for v in violations:
        print(f"{path.name}:{v.line}: {v.rule}: {v.detail}", file=sys.stderr)
    print(
        f"check_history_rows: {len(violations)} violation(s).  A row is one sentence naming "
        "its release's theme; CHANGELOG.md lists what shipped.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
