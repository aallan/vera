"""The class instrument of `scripts/check_pragma_placement.py` (#1838): a
generated matrix whose every source the gate accepts is judged by mutmut's
own `PragmaVisitor`.

No expected line is written by hand.  Each cell is one construct (a simple
statement, or a compound statement with its clauses) in one form (its headers
on one line, spanning lines inside brackets, or continued by a backslash; its
suites on the header's line or indented), in one context (first at module
level, or in a function body between two statements), with one pragma token
(bare, ``block``, ``start``, ``end``), and with or without an ordinary comment
line just above or just below each pragma alone on its line, at every indent
a block opens at.  Sources Python refuses (all of them hold a backslash) are
left out.  The
cell writes one pragma in every place a comment can go in the construct:
after the code of each of its lines, and alone on a line in each gap between
its lines (before the first, after the last) at every indent its lines use,
halfway between two of them, and one level deeper than the deepest.  So it
covers, without naming them, a comment after code outside every bracket,
inside brackets after a comma or before the closing bracket, alone inside
brackets, alone before the statement, in a block's footer, above a clause at
the clause's indent and deeper (in the block's footer, or in the clause's own
leading lines after a one-line suite), between decorators and after the last.

The gate accepts a pragma only in a shape it places by a local rule and
refuses every other shape (the script's docstring).  So for each source the
cell holds:

- soundness: a pragma the gate accepts is one the engine files under its own
  line, the line the gate files it under.  The engine's line is the line a
  `start` or `end` it reads raises its unmatched-region error at; otherwise
  the first line the visitor marks (`no_mutate_lines` with
  `ignore_node_lines`), a `block` region growing only downwards from it.  An
  accepted bare pragma marks exactly that one line;
- usefulness: a pragma written in one of the documented shapes (`documented`,
  read from the generator's own record of where it put the comment, not from
  the gate) is accepted: after the code of a line that starts its statement
  outside every bracket; bare, after code inside brackets; a `block`,
  `start` or `end` alone directly above a statement at its column; an `end`
  alone directly below a statement at its column, ending its block or the
  module;
- a refused pragma's message says where to write it.

The gate is not held to accept everything the visitor reads: a refused
pragma may be one mutmut reads, and the axes (backslash continuations,
comment runs beside the pragma, a module's tail, an `end` at a block's end)
show that what is refused there is refused with a fix.

Where mutmut is not installed (the test shards install `[dev]` alone) a cell
checks usefulness and the messages, then skips the soundness half; the cells
run whole in the Mutation (diff) lane's self-test step, which installs the
engine.
"""

from __future__ import annotations

import ast
import importlib.util
import itertools
import re
import sys
from pathlib import Path

import pytest

pytestmark = pytest.mark.matrix(decides=["scripts/check_pragma_placement.py"])

ROOT = Path(__file__).resolve().parent.parent
SCRIPT_PATH = ROOT / "scripts" / "check_pragma_placement.py"


def _load() -> object:
    spec = importlib.util.spec_from_file_location("check_pragma_placement", SCRIPT_PATH)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["check_pragma_placement"] = module
    spec.loader.exec_module(module)
    return module


gate = _load()

Line = tuple[int, str]

# ---------------------------------------------------------------------------
# The constructs: each a function of (span, form) giving its lines
# ---------------------------------------------------------------------------

#: Each header with an expression, on one line, spanning lines inside
#: brackets, and continued by a backslash (the continuation lines' indents
#: are relative to the header's).
HEADERS: dict[str, tuple[list[Line], list[Line], list[Line]]] = {
    "if": ([(0, "if a:")], [(0, "if (a"), (8, "or b):")], [(0, "if a or \\"), (8, "b:")]),
    "elif": ([(0, "elif c:")], [(0, "elif (c"), (8, "or d):")], [(0, "elif c or \\"), (8, "d:")]),
    "while": ([(0, "while a:")], [(0, "while (a"), (8, "or b):")], [(0, "while a or \\"), (8, "b:")]),
    "for": ([(0, "for i in xs:")], [(0, "for i in ("), (4, "xs"), (0, "):")], [(0, "for i in \\"), (4, "xs:")]),
    "with": ([(0, "with m:")], [(0, "with ("), (4, "m"), (0, "):")], [(0, "with m, \\"), (4, "n:")]),
    "except": ([(0, "except E:")], [(0, "except (E,"), (8, "F):")], [(0, "except \\"), (4, "E:")]),
    "def": ([(0, "def f(a):")], [(0, "def f("), (4, "a,"), (0, "):")], [(0, "def f(a) \\"), (4, "-> T:")]),
    "class": ([(0, "class C(B):")], [(0, "class C("), (4, "B,"), (0, "):")], [(0, "class C \\"), (4, "(B):")]),
    "match": ([(0, "match a:")], [(0, "match ("), (4, "a"), (0, "):")], [(0, "match a \\"), (4, ":")]),
    "case": ([(0, "case 1:")], [(0, "case ("), (4, "1"), (0, "):")], [(0, "case 1 \\"), (4, ":")]),
    "else": ([(0, "else:")], [(0, "else:")], [(0, "else \\"), (4, ":")]),
    "try": ([(0, "try:")], [(0, "try:")], [(0, "try \\"), (4, ":")]),
    "finally": ([(0, "finally:")], [(0, "finally:")], [(0, "finally \\"), (4, ":")]),
}

#: Decorators, the same three ways.
DECORATORS: tuple[list[Line], list[Line], list[Line]] = (
    [(0, "@d"), (0, "@e(1)")],
    [(0, "@d"), (0, "@e("), (4, "1,"), (0, ")")],
    [(0, "@d"), (0, "@e \\"), (4, ".f")],
)

#: Simple statements, the same three ways.
SIMPLE: dict[str, tuple[list[Line], list[Line], list[Line]]] = {
    "assign": ([(0, "x = f(1, 2)")], [(0, "x = f("), (4, "1,"), (4, "2,"), (0, ")")], [(0, "x = f(1) + \\"), (4, "2")]),
    "assign_tight": ([(0, "x = g(1, 2)")], [(0, "x = g("), (4, "1,"), (4, "2)")], [(0, "x = g(1) \\"), (4, "+ 2")]),
    # Complete before its backslash: only a comment line below it ends it.
    "dangling": ([(0, "x = 1")], [(0, "x = 1")], [(0, "x = 1 \\")]),
    "call": ([(0, "f(1)")], [(0, "f("), (4, "1,"), (0, ")")], [(0, "f \\"), (4, "(1)")]),
    "return": ([(0, "return a or b")], [(0, "return ("), (4, "a"), (4, "or b"), (0, ")")], [(0, "return a \\"), (4, "or b")]),
}

SPANS = ("one", "span", "backslash")
FORMS = ("line", "block")
CONTEXTS = ("module", "body")
TOKENS = ("bare", "block", "start", "end")


def _shift(lines: list[Line], by: int) -> list[Line]:
    return [(indent + by, text) for indent, text in lines]


def _clause(name: str, span: str, form: str, body: str, at: int = 0) -> list[Line]:
    """A header and its suite: on the header's line, or indented below it."""
    header = _shift(HEADERS[name][SPANS.index(span)], at)
    if form == "line":
        indent, text = header[-1]
        return [*header[:-1], (indent, f"{text} {body}")]
    return [*header, (at + 4, body)]


def _clauses(names: list[str], span: str, form: str) -> list[Line]:
    return [line for n, name in enumerate(names) for line in _clause(name, span, form, f"x = {n}")]


def construct(name: str, span: str, form: str) -> list[Line]:
    """The lines of one construct at indent 0."""
    if name in SIMPLE:
        return SIMPLE[name][SPANS.index(span)]
    chains = {
        "if": ["if"], "if_else": ["if", "else"], "if_elif_else": ["if", "elif", "else"],
        "for_else": ["for", "else"], "while_else": ["while", "else"], "with": ["with"],
        "try_except": ["try", "except"], "try_except_else_finally": ["try", "except", "else", "finally"],
        "try_finally": ["try", "finally"], "def": ["def"], "class": ["class"],
    }
    if name in chains:
        return _clauses(chains[name], span, form)
    if name in ("decorated_def", "decorated_class"):
        return [*DECORATORS[SPANS.index(span)], *_clause(name.split("_")[1], span, form, "x = 0")]
    if name == "match":
        # A `match` has no suite of its own: its cases take the form.
        header = HEADERS["match"][SPANS.index(span)]
        return [*header, *_clause("case", span, form, "x = 0", 4),
                (4, "case _:" + (" x = 1" if form == "line" else "")),
                *([] if form == "line" else [(8, "x = 1")])]
    if name == "if_dangling":
        # A header complete before its backslash, its suite indented below.
        return [(0, "if a: \\"), (4, "x = 0")]
    if name == "if_nested_else":
        # The `else` closes the outer block; the inner `if` takes the form.
        return [*HEADERS["if"][SPANS.index(span)], *_clause("if", span, form, "x = 0", 4),
                (0, "else:"), (4, "x = 1")]
    raise AssertionError(name)


CONSTRUCTS = (*SIMPLE, "if", "if_dangling","if_else", "if_elif_else", "if_nested_else", "for_else", "while_else",
              "with", "try_except", "try_except_else_finally", "try_finally", "def", "class",
              "decorated_def", "decorated_class", "match")


def _text(token: str) -> str:
    return "# pragma: no mutate" + ("" if token == "bare" else f" {token}")


#: An ordinary comment line beside each pragma alone on its line: none, one
#: just above it, or one just below it, at every indent a block opens at.
COMPANIONS = ("none", "above", "below")

Cell = tuple[str, str, str, str, str, str]

#: One written source: where the cell put the pragma, the source, the
#: pragma's line, whether it is alone on its line, and the documented shape
#: it is written in (None: no documented shape).
Source = tuple[str, str, int, bool, str | None]

#: The clauses a pragma alone on its line is never placed above.
CLAUSES = ("else", "elif", "except", "finally")


def sources(*cell: str) -> list[Source]:
    """Every source of a cell that Python parses."""
    out = []
    for written_source in written(*cell):
        try:
            ast.parse(written_source[1])
        except SyntaxError:
            continue
        out.append(written_source)
    return out


def _structure(full: list[Line]) -> tuple[list[bool], list[bool], list[int]]:
    """For each line of the pragma-free lines: whether it starts a statement,
    whether a bracket or a backslash is open at its end, and the bracket
    depth at its end (the constructs' texts hold no bracket in a string)."""
    starts: list[bool] = []
    open_after: list[bool] = []
    depths: list[int] = []
    depth = 0
    for n, (_, text) in enumerate(full):
        starts.append(n == 0 or not open_after[n - 1])
        depth += sum(map(text.count, "([{")) - sum(map(text.count, ")]}"))
        depths.append(depth)
        open_after.append(depth > 0 or text.endswith("\\"))
    return starts, open_after, depths


def _is_clause(text: str) -> bool:
    return text.split()[0].rstrip(":") in CLAUSES


def documented_after(full: list[Line], k: int, token: str) -> str | None:
    """The documented shape of a pragma written after the code of line `k`."""
    starts, _, depths = _structure(full)
    text = full[k][1]
    if depths[k] > 0:
        return "brackets" if token == "bare" else None
    if starts[k] and not text.endswith("\\") and not text.startswith("@"):
        return "statement"
    return None


def documented_alone(
    full: list[Line], gap: int, column: int, token: str, companion: str, note: int | None
) -> str | None:
    """The documented shape of a pragma alone on its line at `column`,
    between `full[gap - 1]` and `full[gap]`, with an ordinary comment line at
    column `note` just above it or just below it (`companion`)."""
    if token == "bare":
        return None
    starts, open_after, _ = _structure(full)
    above = gap - 1
    if above >= 0:
        if open_after[above]:
            return None  # a bracket or a backslash is open
        first = max(n for n in range(above + 1) if starts[n])
        if full[first][1].startswith("@"):
            return None  # after a decorator
    following = full[gap] if gap < len(full) else None
    if (following is not None and following[0] == column and not _is_clause(following[1])
            and (companion != "below" or note == column)):
        return "above"
    if token != "end" or above < 0:
        return None
    # The latest statement starting at the pragma's column or shallower.
    owner = next((full[n][0] for n in range(above, -1, -1) if starts[n] and full[n][0] <= column), None)
    closed = following is not None and following[0] < column
    if (owner == column
            and (companion != "above" or note == column)
            and (companion != "below" or note == column or (closed and note is not None and note < column))
            and (following is None or following[0] < column
                 or (following[0] == column and not _is_clause(following[1])))):
        return "below"
    return None


#: The documented shapes, and the tokens each is written with.
SHAPES = {"statement": TOKENS, "brackets": ("bare",), "above": ("block", "start", "end"), "below": ("end",)}


def written(name: str, span: str, form: str, context: str, token: str, companion: str) -> list[Source]:
    """Every source a cell writes.  A cell with a companion writes only the
    pragmas alone on their line, each beside one ordinary comment line."""
    lines = construct(name, span, form)
    before: list[Line] = []
    after: list[Line] = []
    if context == "body":
        lines = _shift(lines, 4)
        before, after = [(0, "def g():"), (4, "w = 0")], [(4, "y = 0")]
    full = [*before, *lines, *after]
    levels = sorted({indent for indent, _ in full})
    columns = sorted({*levels, *(a + (b - a) // 2 for a, b in itertools.pairwise(levels)), levels[-1] + 4})
    comment = _text(token)
    out = []

    def emit(where: str, body: list[Line], line: int, alone: bool, shape: str | None) -> None:
        source = "".join(" " * indent + text + "\n" for indent, text in [*before, *body, *after])
        out.append((where, source, len(before) + line, alone, shape))

    if companion == "none":
        for i, (indent, text) in enumerate(lines):
            emit(f"after_line_{i + 1}", [*lines[:i], (indent, f"{text}  {comment}"), *lines[i + 1:]], i + 1, False,
                 documented_after(full, len(before) + i, token))
    for gap in range(len(lines) + 1):
        for column in columns:
            if companion == "none":
                emit(f"gap_{gap}_col_{column}", [*lines[:gap], (column, comment), *lines[gap:]], gap + 1, True,
                     documented_alone(full, len(before) + gap, column, token, companion, None))
                continue
            for other in levels:
                pair = [(other, "# a note"), (column, comment)]
                if companion == "below":
                    pair.reverse()
                emit(f"gap_{gap}_col_{column}_note_{companion}_col_{other}", [*lines[:gap], *pair, *lines[gap:]],
                     gap + 1 + (companion == "above"), True,
                     documented_alone(full, len(before) + gap, column, token, companion, other))
    return out


def _cells() -> list[Cell]:
    cells, seen = [], set()
    for cell in itertools.product(CONSTRUCTS, SPANS, FORMS, CONTEXTS, TOKENS, COMPANIONS):
        key = tuple(source for _, source, _, _, _ in sources(*cell))
        if key in seen:  # A simple statement has no suite: its two forms are one.
            continue
        seen.add(key)
        cells.append(cell)
    return cells


CELLS = _cells()

# ---------------------------------------------------------------------------
# The oracle: mutmut's own visitor
# ---------------------------------------------------------------------------

_UNMATCHED = re.compile(r"(?:Missing no mutate end for start block at|# pragma: no mutate end at) <cell>:(\d+)")


def engine_reading(source: str) -> tuple[int | None, set[int]]:
    """The line mutmut 3.8's `PragmaVisitor` files the one pragma of
    `source` under, and the lines it marks."""
    cst = pytest.importorskip("libcst")
    handling = pytest.importorskip("mutmut.mutation.pragma_handling")
    visitor = handling.PragmaVisitor("<cell>")
    try:
        cst.MetadataWrapper(cst.parse_module(source)).visit(visitor)
    except handling.PragmaParseError as error:
        match = _UNMATCHED.search(str(error))
        assert match is not None, str(error)
        return int(match.group(1)), set(visitor.no_mutate_lines) | set(visitor.ignore_node_lines)
    marked = set(visitor.no_mutate_lines) | set(visitor.ignore_node_lines)
    return (min(marked) if marked else None), marked


def the_gates_faults(cell: Cell) -> tuple[int, list[str]]:
    """How many sources the cell has, and each one where the gate refuses a
    documented shape or refuses with no fix, described."""
    token = cell[4]
    found = sources(*cell)
    wrong = []
    for where, source, line, _, shape in found:
        (p,) = gate.pragmas(source)
        assert (p.line, p.token) == (line, token), (where, source)
        if shape is not None and p.misplaced:
            wrong.append(f"{where}: the gate refuses a pragma written {shape!r}: {gate.explain(p)}\n{source}")
        elif p.misplaced and "write it" not in gate.explain(p):
            wrong.append(f"{where}: the refusal says nowhere to write it: {gate.explain(p)}\n{source}")
    return len(found), wrong


def the_unsound_accepts(cell: Cell) -> list[str]:
    """Each source whose pragma the gate accepts and the engine files under
    another line, or (bare) marks more than its line, described."""
    wrong = []
    for where, source, line, _, _ in sources(*cell):
        (p,) = gate.pragmas(source)
        if p.misplaced:
            continue
        filed, marked = engine_reading(source)
        if (p.filed, filed) != (line, line):
            wrong.append(f"{where}: accepted and filed under {p.filed}, the engine under {filed}\n{source}")
        elif p.token == "bare" and marked != {line}:
            wrong.append(f"{where}: an accepted bare pragma marks {sorted(marked)}\n{source}")
    return wrong


@pytest.mark.parametrize(("construct", "span", "form", "context", "token", "companion"), CELLS)
def test_the_gate_accepts_each_documented_shape_and_what_it_accepts_the_engine_reads_there(
    construct: str, span: str, form: str, context: str, token: str, companion: str
) -> None:
    cell = (construct, span, form, context, token, companion)
    count, wrong = the_gates_faults(cell)
    assert count > 0
    assert not wrong, "\n".join(wrong)
    pytest.importorskip("libcst")
    pytest.importorskip("mutmut.mutation.pragma_handling")
    unsound = the_unsound_accepts(cell)
    assert not unsound, "\n".join(unsound)


def test_each_documented_shape_is_written_in_every_context_with_every_token_it_takes() -> None:
    """The usefulness half reaches each shape: every documented shape is
    written somewhere in each context, with each token it takes, both at
    module level and in a function body, and the gate accepts some source
    and refuses some in every cell's axis value."""
    met: set[tuple[str, str, str]] = set()
    verdicts: dict[tuple[int, str], set[bool]] = {}
    for cell in CELLS:
        for _, source, _, _, shape in sources(*cell):
            if shape is not None:
                met.add((shape, cell[3], cell[4]))
            (p,) = gate.pragmas(source)
            for n, value in enumerate(cell):
                verdicts.setdefault((n, value), set()).add(p.misplaced)
    assert met == {(shape, context, token) for shape, tokens in SHAPES.items()
                   for context in CONTEXTS for token in tokens}
    assert {key for key, seen in verdicts.items() if seen != {True, False}} == set()


def test_the_matrix_spans_every_dimension_and_drops_only_what_python_refuses() -> None:
    """Every value of every dimension is in some cell, and the only sources
    Python refuses hold a backslash: a comment after one on its line, or a
    comment line ending the statement it continues too early, or no comment
    line ending a statement complete before it."""
    for n, dimension in enumerate((CONSTRUCTS, SPANS, FORMS, CONTEXTS, TOKENS, COMPANIONS)):
        assert {cell[n] for cell in CELLS} == set(dimension)
    for cell in CELLS:
        kept = {source for _, source, _, _, _ in sources(*cell)}
        assert kept, cell
        for where, source, _, _, _ in written(*cell):
            assert source in kept or "\\\n" in source or "\\  #" in source, (cell, where, source)
