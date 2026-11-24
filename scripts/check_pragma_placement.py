#!/usr/bin/env python3
"""Every ``# pragma: no mutate`` under ``vera/`` is filed by mutmut under the line it is written on (#1838).

mutmut 3.8 does not read a pragma by its physical line.  Its
``PragmaVisitor`` (``mutmut/mutation/pragma_handling.py``) files a comment by
its place in the syntax tree:

- inside brackets, a bare pragma ending a line of code is filed under that
  line (``visit_ParenthesizedWhitespace``); a ``block``, ``start`` or
  ``end`` pragma there, and any pragma alone on a line inside brackets, is
  read by no visitor at all;
- alone on its line, a pragma is filed under that line where it is a
  module's header or footer, a statement's leading line in a body, or a
  block's footer: there ``start``, ``end`` and ``block`` open and close
  their regions, and a bare one protects no node, since none starts on a
  line that holds only a comment.  Alone after a decorator, or in the own
  leading lines of an ``else``, ``elif``, ``except`` or ``finally`` (above
  the clause and shallower than the indented block it closes, or at any
  indent after a one-line suite, which has no footer), it is read by no
  visitor;
- on a decorator's line, after the decorator, it is read by no visitor;
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

It runs without the engine.  ``tests/test_check_pragma_placement.py`` (its
named shapes) and ``tests/test_pragma_placement_matrix.py`` (a generated
matrix of every place a comment can go) hold it to mutmut's own visitor where
mutmut is installed (the Mutation (diff) lane's self-test step).

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


#: The clauses whose own leading lines (libcst's ``leading_lines`` of
#: ``else``, ``elif``, ``except`` and ``finally``) no visitor of the engine
#: scans.
CLAUSES = frozenset({"else", "elif", "except", "finally"})


def footer_owns(column: int, clause: int, levels: list[int]) -> bool:
    """Whether a comment line at ``column`` above a clause at column
    ``clause`` is the footer of the indented block the clause closes, where
    the engine reads it, rather than the clause's own leading lines, where it
    does not.  ``levels`` are the indents of the blocks open at the comment.
    The block the clause closes is the shallowest one deeper than the clause;
    a clause after a one-line suite closes none, so nothing above it is a
    footer, at any column."""
    closed = [level for level in levels if level > clause]
    return bool(closed) and column >= min(closed)


def pragmas(source: str) -> list[Pragma]:
    """Every pragma in ``source`` with the line the engine files it under.
    The source must parse: ``tokenize`` alone accepts some text Python does
    not, where the engine's parser would refuse the file.

    A comment alone on its line is read where it is a module's header or
    footer, a statement's leading line in a body, or a block's footer; it is
    read nowhere inside brackets, after a decorator (between decorators, or
    between the last one and its ``def`` or ``class``), or in a clause's own
    leading lines (``footer_owns``).  A comment after code is read on a statement, a
    compound header, a one-line suite or a ``match`` header, and nowhere on a
    decorator's line."""
    ast.parse(source)
    found: list[Pragma] = []
    depth = 0
    logical_start: int | None = None
    logical_first: str | None = None
    after_decorator = False
    levels: list[int] = []
    skip = (tokenize.NL, tokenize.NEWLINE, tokenize.COMMENT, tokenize.INDENT, tokenize.DEDENT,
            tokenize.ENCODING, tokenize.ENDMARKER)
    tokens = list(tokenize.generate_tokens(io.StringIO(source).readline))
    for at, tok in enumerate(tokens):
        if tok.type not in skip and logical_start is None:
            logical_start, logical_first = tok.start[0], tok.string
            after_decorator = after_decorator and tok.string == "@"
        if tok.type == tokenize.OP and tok.string in "([{":
            depth += 1
        elif tok.type == tokenize.OP and tok.string in ")]}":
            depth -= 1
        elif tok.type == tokenize.COMMENT:
            token = token_of(tok.string)
            if token is not None:
                line = tok.start[0]
                if not tok.line[:tok.start[1]].strip():
                    following = next((t for t in tokens[at + 1:] if t.type not in skip), None)
                    if depth > 0:
                        found.append(Pragma(line, token, None, "alone in brackets"))
                    elif after_decorator:
                        found.append(Pragma(line, token, None, "after a decorator"))
                    elif (following is not None and following.string in CLAUSES
                          and not footer_owns(tok.start[1], following.start[1], levels)):
                        found.append(Pragma(line, token, None, "above a clause"))
                    else:
                        found.append(Pragma(line, token, line, "alone"))
                elif depth > 0:
                    found.append(Pragma(line, token, line if token == "bare" else None, "brackets"))
                elif logical_first == "@":
                    found.append(Pragma(line, token, None, "on a decorator"))
                else:
                    start = logical_start if logical_start is not None else line
                    found.append(Pragma(line, token, start, "statement"))
        elif tok.type == tokenize.NEWLINE:
            after_decorator = logical_first == "@"
            logical_start = logical_first = None
        elif tok.type == tokenize.INDENT:
            levels.append(tok.end[1])
        elif tok.type == tokenize.DEDENT:
            levels.pop()
    return found


def explain(p: Pragma) -> str:
    """What is wrong with a misplaced pragma, and the fix."""
    if p.filed is None:
        where = {"brackets": "inside brackets after code", "alone in brackets": "alone inside brackets",
                 "after a decorator": "alone after a decorator",
                 "above a clause": ("alone above an else, elif, except or finally, outside the "
                                    "footer of the block it closes"),
                 "on a decorator": "on a decorator's line"}[p.how]
        fix = ("write it after the code of the line it answers" if p.token == "bare"
               else "write it on a line of its own in a body, outside every bracket")
        return f"a `{p.token}` pragma {where} is read by no visitor: {fix}"
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
