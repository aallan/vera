#!/usr/bin/env python3
"""Every ``# pragma: no mutate`` under ``vera/`` is filed by mutmut under the line it is written on (#1838).

mutmut 3.8 does not read a pragma by its physical line.  Its
``PragmaVisitor`` (``mutmut/mutation/pragma_handling.py``) files a comment by
its place in libcst's syntax tree, and where libcst puts a comment line
depends on rules no local reading reproduces in full (a block's footer, a
module's footer, a clause's own leading lines).  So the gate does not try to
read every placement.  Its contract:

- it ACCEPTS a pragma only in a shape it places by a local rule, and for
  each shape it accepts, the line it files the pragma under is the line
  mutmut's visitor marks;
- it REFUSES every other shape, with a message that says where to write the
  pragma instead.  A refused pragma may still be one mutmut reads.

The shapes it accepts, each filed under its own line:

- after the code of a line that starts a statement, outside every bracket: a
  simple statement's trailing comment (``visit_SimpleStatementLine``), a
  compound statement's header (``if``, ``for``, ``while``, ``with``, ``try``,
  ``except``, ``else``, ``finally``, ``def``, ``class``, ``match``, ``case``),
  a one-line suite.  On a header, ``block`` covers the whole statement;
- a bare pragma after code inside brackets, on the line of the node it
  answers: after a comma, or before a closing bracket put on a line of its
  own (``visit_ParenthesizedWhitespace``);
- a ``block``, ``start`` or ``end`` pragma alone on its line, directly above
  a statement, a compound statement, a ``case`` or a decorator at that
  statement's column: the next line that is neither blank nor a comment
  starts it, no backslash continuation is open, and every comment line
  between is at the same column.  The comment is that statement's leading
  line, which the visitor scans;
- an ``end`` pragma alone on its line, directly below a statement at the same
  column, where a region that ends with its block has to close: the latest
  statement starting at that column or shallower starts at it (so the line
  above is that statement's last), no backslash continuation is open, every
  comment line between that statement and the next is at the same column,
  and the next statement is shallower, at the same column and no clause, or
  there is none.  Comment lines below the pragma that are shallower than it
  are ignored when the next statement is shallower too (the block has
  closed); a deeper comment line, or a shallower one followed by a statement
  at the pragma's own column or by the end of the module, is still refused.  The comment is then the footer of the block, or of the
  module, which the visitor scans (at the end of a module too: mutmut 3.8.1
  marks the line there).  ``block`` and ``start`` are not accepted there:
  nothing follows them for a region to cover.

A ``case`` is a statement here and ``else``, ``elif``, ``except`` and
``finally`` are not: the visitor scans the leading lines of each ``case`` and
of no other clause.

Refused, with the reason: a pragma after code on a line that does not start
its statement (after the closing bracket of a statement that spans lines, it
is filed under the statement's first line and protects that line's mutants,
not its own); a bare pragma alone on its line (no node starts there); a
``block``, ``start`` or ``end`` inside brackets; a pragma on a decorator's
line or alone after a decorator; and a pragma alone on its line in any other
shape: a ``block`` or ``start`` at the end of a block or of a module, at an
indent no statement next to it has, above an ``else``, ``elif``, ``except``
or ``finally`` at its column, after a backslash, or with a comment line at
another column between it and the statement.  The fix is to write the
comment on the node's own line (inside the brackets on a statement that
spans lines), or alone directly above the statement it covers, at that
statement's column.

It runs without the engine.  ``tests/test_check_pragma_placement.py`` (its
named shapes) and ``tests/test_pragma_placement_matrix.py`` (a generated
matrix of every place a comment can go) hold every pragma it accepts to
mutmut's own visitor where mutmut is installed (the Mutation (diff) lane's
self-test step), and hold the documented shapes accepted.

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
    (``bare``, ``block``, ``start`` or ``end``), the line the gate files it
    under (None: a shape the gate does not place), and its shape."""

    line: int
    token: str
    filed: int | None
    how: str

    @property
    def misplaced(self) -> bool:
        """Whether the gate refuses it."""
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


def pragmas(source: str) -> list[Pragma]:
    """Every pragma in ``source`` with the line the gate files it under, by
    the module's contract.  The source must parse: ``tokenize`` alone accepts
    some text Python does not, where the engine's parser would refuse the
    file."""
    ast.parse(source)
    found: list[Pragma] = []
    depth = 0
    logical_start: int | None = None
    logical_first: str | None = None
    after_decorator = False
    starts: list[int] = []  # the column each logical line so far starts at
    skip = (tokenize.NL, tokenize.NEWLINE, tokenize.COMMENT, tokenize.INDENT, tokenize.DEDENT,
            tokenize.ENCODING, tokenize.ENDMARKER)
    tokens = list(tokenize.generate_tokens(io.StringIO(source).readline))
    for at, tok in enumerate(tokens):
        if tok.type not in skip and logical_start is None:
            logical_start, logical_first = tok.start[0], tok.string
            starts.append(tok.start[1])
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
                    if depth > 0:
                        found.append(Pragma(line, token, None, "alone in brackets"))
                    elif logical_start is not None:
                        found.append(Pragma(line, token, None, "after a backslash"))
                    elif after_decorator:
                        found.append(Pragma(line, token, None, "after a decorator"))
                    else:
                        rest = tokens[at + 1:]
                        ahead = next((n for n, t in enumerate(rest) if t.type not in skip), len(rest))
                        column = tok.start[1]
                        following = rest[ahead] if ahead < len(rest) else None
                        aligned = all(t.start[1] == column for t in rest[:ahead] if t.type == tokenize.COMMENT)
                        # Above a statement at its column: its leading line.
                        placed = (aligned and following is not None and following.start[1] == column
                                  and following.string not in CLAUSES)
                        if token == "end" and not placed:
                            # Below a statement at its column, ending its block
                            # or the module: the block's or the module's footer.
                            back = at
                            while back > 0 and tokens[back - 1].type in skip:
                                back -= 1
                            owner = next((c for c in reversed(starts) if c <= column), None)
                            # A shallower comment line below is ignored when the
                            # next statement is shallower too: the block has closed.
                            closed = following is not None and following.start[1] < column
                            below = all(t.start[1] == column or (closed and t.start[1] < column)
                                        for t in rest[:ahead] if t.type == tokenize.COMMENT)
                            placed = (below and owner == column
                                      and all(t.start[1] == column for t in tokens[back:at]
                                              if t.type == tokenize.COMMENT)
                                      and (following is None or following.start[1] < column
                                           or (following.start[1] == column
                                               and following.string not in CLAUSES)))
                        found.append(Pragma(line, token, line, "alone") if placed
                                     else Pragma(line, token, None, "alone elsewhere"))
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
    return found


#: Where to write a pragma the gate refuses, by its token.
FIX = {
    "bare": ("write it after the code on the node's own line; on a statement that spans lines, "
             "inside the brackets (after a comma, or before a closing bracket on a line of its own)"),
    "block": ("write it after the code on the compound statement's own header line, or alone "
              "directly above the statement at that statement's column"),
}


def explain(p: Pragma) -> str:
    """What is wrong with a refused pragma, and where to write it."""
    fix = FIX.get(p.token, "write it alone directly above a statement, at that statement's column")
    if p.token == "bare" and p.how in ("alone", "alone elsewhere"):
        return f"a bare pragma on a line of its own protects no node: {fix}"
    if p.filed is not None:
        return (f"filed under line {p.filed}, where the statement starts, not under line {p.line}: "
                f"{fix}, or make the statement one line")
    where = {"brackets": "{a} `{t}` pragma inside brackets is read by no visitor",
             "alone in brackets": "{a} `{t}` pragma alone inside brackets is read by no visitor",
             "after a decorator": "{a} `{t}` pragma alone after a decorator is read by no visitor",
             "on a decorator": "{a} `{t}` pragma on a decorator's line is read by no visitor",
             "after a backslash": "{a} `{t}` pragma on a line of its own after a backslash is not placed",
             "alone elsewhere": ("{a} `{t}` pragma on a line of its own is placed only directly above "
                                 "a statement at its column (an `end` also directly below one, "
                                 "ending its block), with no comment line at another column "
                                 "between, and never above an else, elif, except or finally "
                                 "at its column")}[p.how]
    return f"{where.format(a='an' if p.token == 'end' else 'a', t=p.token)}: {fix}"


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
