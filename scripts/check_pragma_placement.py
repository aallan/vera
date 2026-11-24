#!/usr/bin/env python3
"""Every ``# pragma: no mutate`` under ``vera/`` is filed by mutmut under the line it is written on (#1838).

mutmut 3.8 does not read a pragma by its physical line.  Its
``PragmaVisitor`` (``mutmut/mutation/pragma_handling.py``) files a comment by
its place in the syntax tree:

- inside brackets, a bare pragma ending a line is filed under that line
  (``visit_ParenthesizedWhitespace``); a ``block``, ``start`` or ``end``
  pragma there is read by no visitor at all;
- alone on its line, a pragma is filed under that line, where ``start``,
  ``end`` and ``block`` open and close their regions and a bare one protects
  no node, since none starts on a line that holds only a comment;
- after code, outside every bracket, a pragma ends a statement and is filed
  under the line the statement starts on: a simple statement's trailing
  comment (``visit_SimpleStatementLine``), a compound statement's header
  (``if``, ``for``, ``while``, ``with``, ``try``, ``except``, ``else``,
  ``finally``, ``def``, ``class``, ``case``; a decorated ``def`` or ``class``
  starts at its ``def`` or ``class``, not at a decorator), a one-line suite,
  a ``match`` header.

So a pragma written after the closing bracket of a statement that spans
lines protects the statement's first line, not its own: every mutant anchored
on the first line (each argument of a call, an assignment's value, a
condition's ``or``) is suppressed, and none on the pragma's line is.  The
gate reads each pragma as the engine does, with ``tokenize`` for the bracket
depth at the comment and the logical line it ends, and fails on one filed
under another line, a bare one that protects nothing, and one no visitor
reads.  The fix is to write the comment inside the brackets on the line of
the node it answers (after a comma, or before a closing bracket put on a line
of its own), or to make the statement one line.

It runs without the engine.  ``tests/test_check_pragma_placement.py`` holds it
to mutmut's own visitor where mutmut is installed (the Mutation (diff) lane's
self-test step).

Usage:
    python scripts/check_pragma_placement.py            # every .py file under vera/
    python scripts/check_pragma_placement.py FILE ...   # the files named
"""

from __future__ import annotations

import ast
import io
import sys
import tokenize
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

#: The tree mutmut mutates (``[tool.mutmut]``'s ``source_paths``).
SCOPE = ("vera",)


@dataclass(frozen=True)
class Pragma:
    """One ``# pragma: no mutate`` comment: where it is written, its token
    (``bare``, ``block``, ``start`` or ``end``), the line the engine files it
    under (None: no visitor reads it), and how."""

    line: int
    token: str
    filed: int | None
    how: str

    @property
    def misplaced(self) -> bool:
        """Whether the engine reads it otherwise than its line says."""
        if self.filed is None:
            return True
        if self.how == "alone" and self.token == "bare":
            return True
        return self.filed != self.line


def token_of(comment: str) -> str | None:
    """The pragma's token, as mutmut parses it (``_parse_pragma_token``), or
    None for a comment that is no pragma."""
    if "# pragma:" not in comment or "no mutate" not in comment:
        return None
    tail = comment.partition("no mutate")[-1].strip()
    words = tail.lstrip(": ").split(",", 1)[0].split()
    word = words[0] if words else None
    return word if word in ("block", "start", "end") else "bare"


def pragmas(source: str) -> list[Pragma]:
    """Every pragma in ``source`` with the line the engine files it under.
    The source must parse: ``tokenize`` alone accepts some text Python does
    not, where the engine's parser would refuse the file."""
    ast.parse(source)
    found: list[Pragma] = []
    depth = 0
    logical_start: int | None = None
    skip = (tokenize.NL, tokenize.NEWLINE, tokenize.COMMENT, tokenize.INDENT, tokenize.DEDENT,
            tokenize.ENCODING, tokenize.ENDMARKER)
    for tok in tokenize.generate_tokens(io.StringIO(source).readline):
        if tok.type not in skip and logical_start is None:
            logical_start = tok.start[0]
        if tok.type == tokenize.OP and tok.string in "([{":
            depth += 1
        elif tok.type == tokenize.OP and tok.string in ")]}":
            depth -= 1
        elif tok.type == tokenize.COMMENT:
            token = token_of(tok.string)
            if token is not None:
                line = tok.start[0]
                if not tok.line[:tok.start[1]].strip():
                    found.append(Pragma(line, token, line, "alone"))
                elif depth > 0:
                    found.append(Pragma(line, token, line if token == "bare" else None, "brackets"))
                else:
                    start = logical_start if logical_start is not None else line
                    found.append(Pragma(line, token, start, "statement"))
        elif tok.type == tokenize.NEWLINE:
            logical_start = None
    return found


def explain(p: Pragma) -> str:
    """What is wrong with a misplaced pragma, and the fix."""
    if p.filed is None:
        return (f"a `{p.token}` pragma inside brackets is read by no visitor: "
                "write it on a line of its own")
    if p.how == "alone":
        return ("a bare pragma on a line of its own protects no node: "
                "write it after the code of the line it answers")
    return (f"filed under line {p.filed}, where the statement starts, not under line {p.line}: "
            "write it inside the brackets on the line of the node it answers, or make the "
            "statement one line")


def check_source(source: str) -> list[Pragma]:
    return [p for p in pragmas(source) if p.misplaced]


def iter_scope_files(root: Path = ROOT) -> list[Path]:
    return sorted(p for d in SCOPE for p in (root / d).rglob("*.py"))


def main(argv: list[str]) -> int:
    paths = [Path(a) for a in argv] if argv else iter_scope_files()
    bad: list[tuple[Path, Pragma]] = []
    total = 0
    for path in paths:
        found = pragmas(path.read_text(encoding="utf-8"))
        total += len(found)
        bad += [(path, p) for p in found if p.misplaced]
    if not bad:
        print(f"check_pragma_placement: OK: each of {total} `# pragma: no mutate` comment(s) "
              "is filed under the line it is written on.")
        return 0
    print(f"check_pragma_placement: {len(bad)} `# pragma: no mutate` comment(s) the engine "
          "reads otherwise than their line says (#1838):", file=sys.stderr)
    for path, p in bad:
        try:
            shown = path.resolve().relative_to(ROOT).as_posix()
        except ValueError:
            shown = path.as_posix()
        print(f"  {shown}:{p.line}: {explain(p)}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
