"""The class instrument of `scripts/check_pragma_placement.py` (#1838): a
generated matrix whose every source is judged by mutmut's own `PragmaVisitor`.

No expected value is written by hand.  Each cell is one construct (a simple
statement, or a compound statement with its clauses) in one form (its headers
on one line or spanning lines; its suites on the header's line or indented),
in one context (first at module level, or in a function body between two
statements), with one pragma token (bare, ``block``, ``start``, ``end``).  The
cell writes one pragma in every place a comment can go in the construct:
after the code of each of its lines, and alone on a line in each gap between
its lines (before the first, after the last) at every indent its lines use,
halfway between two of them, and one level deeper than the deepest.  So it
covers, without naming them, a comment after code outside every bracket,
inside brackets after a comma or before the closing bracket, alone inside
brackets, alone before the statement, in a block's footer, above a clause at
the clause's indent and deeper (in the block's footer, or in the clause's own
leading lines after a one-line suite), between decorators and after the last.

For each source the gate's reading of its one pragma (`pragmas`) is held to
the visitor's:

- the line the engine files it under is the gate's ``filed``: the line a
  `start` or `end` the engine reads raises its unmatched-region error at;
  otherwise the first line the visitor marks (`no_mutate_lines` with
  `ignore_node_lines`), a `block` region growing only downwards from it; and
  None when it marks nothing;
- a bare pragma marks exactly that one line, or none;
- the gate refuses the pragma (`misplaced`) exactly when the engine files it
  under no line or another line than its own, or it is bare and alone on its
  line.

Where mutmut is not installed (the test shards install `[dev]` alone) the
cells check only that the gate finds the one pragma on its line, and skip
the differential; they run whole in the Mutation (diff) lane's self-test
step, which installs the engine.
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

#: Each header with an expression, on one line and spanning lines (the
#: continuation lines' indents are relative to the header's).
HEADERS: dict[str, tuple[list[Line], list[Line]]] = {
    "if": ([(0, "if a:")], [(0, "if (a"), (8, "or b):")]),
    "elif": ([(0, "elif c:")], [(0, "elif (c"), (8, "or d):")]),
    "while": ([(0, "while a:")], [(0, "while (a"), (8, "or b):")]),
    "for": ([(0, "for i in xs:")], [(0, "for i in ("), (4, "xs"), (0, "):")]),
    "with": ([(0, "with m:")], [(0, "with ("), (4, "m"), (0, "):")]),
    "except": ([(0, "except E:")], [(0, "except (E,"), (8, "F):")]),
    "def": ([(0, "def f(a):")], [(0, "def f("), (4, "a,"), (0, "):")]),
    "class": ([(0, "class C(B):")], [(0, "class C("), (4, "B,"), (0, "):")]),
    "match": ([(0, "match a:")], [(0, "match ("), (4, "a"), (0, "):")]),
    "case": ([(0, "case 1:")], [(0, "case ("), (4, "1"), (0, "):")]),
    "else": ([(0, "else:")], [(0, "else:")]),
    "try": ([(0, "try:")], [(0, "try:")]),
    "finally": ([(0, "finally:")], [(0, "finally:")]),
}

#: Decorators, on one line and spanning lines.
DECORATORS: tuple[list[Line], list[Line]] = (
    [(0, "@d"), (0, "@e(1)")],
    [(0, "@d"), (0, "@e("), (4, "1,"), (0, ")")]
)

#: Simple statements, on one line and spanning lines.
SIMPLE: dict[str, tuple[list[Line], list[Line]]] = {
    "assign": ([(0, "x = f(1, 2)")], [(0, "x = f("), (4, "1,"), (4, "2,"), (0, ")")]),
    "assign_tight": ([(0, "x = g(1, 2)")], [(0, "x = g("), (4, "1,"), (4, "2)")]),
    "call": ([(0, "f(1)")], [(0, "f("), (4, "1,"), (0, ")")]),
    "return": ([(0, "return a or b")], [(0, "return ("), (4, "a"), (4, "or b"), (0, ")")]),
}

SPANS = ("one", "span")
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
    if name == "if_nested_else":
        # The `else` closes the outer block; the inner `if` takes the form.
        return [*HEADERS["if"][SPANS.index(span)], *_clause("if", span, form, "x = 0", 4),
                (0, "else:"), (4, "x = 1")]
    raise AssertionError(name)


CONSTRUCTS = (*SIMPLE, "if", "if_else", "if_elif_else", "if_nested_else", "for_else", "while_else",
              "with", "try_except", "try_except_else_finally", "try_finally", "def", "class",
              "decorated_def", "decorated_class", "match")


def _text(token: str) -> str:
    return "# pragma: no mutate" + ("" if token == "bare" else f" {token}")


def sources(name: str, span: str, form: str, context: str, token: str) -> list[tuple[str, str, int, bool]]:
    """Every source of a cell that Python parses."""
    out = []
    for where, source, line, alone in written(name, span, form, context, token):
        try:
            ast.parse(source)
        except SyntaxError:
            continue
        out.append((where, source, line, alone))
    return out


def written(name: str, span: str, form: str, context: str, token: str) -> list[tuple[str, str, int, bool]]:
    """Every source a cell writes: (where, source, the pragma's line,
    whether it is alone on its line)."""
    lines = construct(name, span, form)
    before: list[Line] = []
    after: list[Line] = []
    if context == "body":
        lines = _shift(lines, 4)
        before, after = [(0, "def g():"), (4, "w = 0")], [(4, "y = 0")]
    levels = sorted({indent for indent, _ in [*before, *lines, *after]})
    columns = sorted({*levels, *(a + (b - a) // 2 for a, b in itertools.pairwise(levels)), levels[-1] + 4})
    comment = _text(token)
    out = []

    def emit(where: str, body: list[Line], line: int, alone: bool) -> None:
        source = "".join(" " * indent + text + "\n" for indent, text in [*before, *body, *after])
        out.append((where, source, len(before) + line, alone))

    for i, (indent, text) in enumerate(lines):
        emit(f"after_line_{i + 1}", [*lines[:i], (indent, f"{text}  {comment}"), *lines[i + 1:]], i + 1, False)
    for gap in range(len(lines) + 1):
        for column in columns:
            emit(f"gap_{gap}_col_{column}", [*lines[:gap], (column, comment), *lines[gap:]], gap + 1, True)
    return out


def _cells() -> list[tuple[str, str, str, str, str]]:
    cells, seen = [], set()
    for name, span, form, context, token in itertools.product(CONSTRUCTS, SPANS, FORMS, CONTEXTS, TOKENS):
        key = tuple(source for _, source, _, _ in sources(name, span, form, context, token))
        if key in seen:  # A simple statement has no suite: its two forms are one.
            continue
        seen.add(key)
        cells.append((name, span, form, context, token))
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


def disagreements(cell: tuple[str, str, str, str, str]) -> tuple[int, list[str]]:
    """How many sources the cell has, and each one where the gate and the
    engine differ, described."""
    token = cell[-1]
    found = sources(*cell)
    wrong = []
    for where, source, line, alone in found:
        (p,) = gate.pragmas(source)
        assert (p.line, p.token) == (line, token), (where, source)
        filed, marked = engine_reading(source)
        refused = filed != line or (token == "bare" and alone)
        if p.filed != filed:
            wrong.append(f"{where}: the gate files it under {p.filed}, the engine under {filed}\n{source}")
        elif token == "bare" and marked != ({filed} if filed is not None else set()):
            wrong.append(f"{where}: a bare pragma marks {sorted(marked)}\n{source}")
        elif p.misplaced != refused:
            wrong.append(f"{where}: the gate {'refuses' if p.misplaced else 'accepts'} it\n{source}")
    return len(found), wrong


@pytest.mark.parametrize(("construct", "span", "form", "context", "token"), CELLS)
def test_the_gate_reads_every_place_of_a_pragma_as_the_engine_does(
    construct: str, span: str, form: str, context: str, token: str
) -> None:
    count, wrong = disagreements((construct, span, form, context, token))
    assert count > 0
    assert not wrong, "\n".join(wrong)


def test_the_matrix_spans_every_construct_and_drops_none() -> None:
    """Every construct, span, form, context and token is in some cell, and
    every source a cell writes parses: none is left out."""
    for n, dimension in enumerate((CONSTRUCTS, SPANS, FORMS, CONTEXTS, TOKENS)):
        assert {cell[n] for cell in CELLS} == set(dimension)
    for cell in CELLS:
        assert len(sources(*cell)) == len(written(*cell)) > 2 * len(construct(*cell[:3])), cell
