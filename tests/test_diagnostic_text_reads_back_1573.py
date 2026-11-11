"""What a diagnostic prints is the program's own text (#1573, #1853, #1851).

Three readers each printed a different text from the one the program holds.

* An expression (#1573).  ``ast.format_expr``'s ``BinaryExpr`` arm printed
  ``left op right`` with no precedence rule, so every message built from it
  dropped a parenthesised operand of lower precedence: the ``@Nat``
  subtraction trap, a refinement guard, the ``requires`` / ``call_pre`` /
  ``int_overflow`` descriptions of ``vera verify --json``, E501's "At this
  call site" line and ``vera run``'s ``requires(...) failed``.  It is now the
  canonical formatter's expression rule, the one renderer, and a message
  that composes an expression of its own builds the node and renders it.
  The universal form is the round trip: every expression of the corpus and
  of the generator's programs parses back from its text to itself, and its
  text is what ``vera fmt`` writes.  Then the operator matrix (each binary
  operator inside each other on either side, unary operators, a pipe, an
  index and a call as operands) and, over the shapes each message can hold,
  the message that prints it, asserting the printed text parses back to the
  written expression.
* A source line (#1853).  The quoted line was cut by ``str.splitlines``,
  which also cuts at eight characters the lexer reads inside a line, so
  after one of them the line quoted was not the one the location names.
  One splitter, ``vera.errors.source_lines``, cuts at ``\\n`` alone.
* The ``stack_exhausted`` fix text (#1851), which said a proved
  postcondition keeps a function's tail calls.

The ``repro`` cells are the issues' programs, unparametrised so every pull
request runs them.
"""

from __future__ import annotations

import itertools
import re
from dataclasses import fields, is_dataclass
from pathlib import Path

import pytest

from tests import pipeline
from vera import ast as vast
from vera.errors import source_lines
from vera.formatter import format_expr_canonical, format_source
from vera.parser import read_source

pytestmark = pytest.mark.matrix(decides=[
    "vera/ast.py",
    "vera/formatter.py",
    "vera/errors.py",
    "vera/verifier.py",
    "vera/wasm/operators.py",
    "vera/wasm/data.py",
    "vera/wasm/calls_strings.py",
    "vera/trap_registry.py",
])

ROOT = Path(__file__).resolve().parent.parent
CORPUS = sorted((ROOT / "examples").glob("*.vera")) + sorted(
    (ROOT / "tests" / "conformance").glob("*.vera"))


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _children(node: object) -> list[vast.Node]:
    out: list[vast.Node] = []
    if isinstance(node, vast.Node) and is_dataclass(node):
        for fld in fields(node):
            val = getattr(node, fld.name)
            if isinstance(val, vast.Node):
                out.append(val)
            elif isinstance(val, (list, tuple)):
                out.extend(v for v in val if isinstance(v, vast.Node))
    return out


def _expressions(root: vast.Node) -> list[vast.Expr]:
    found: list[vast.Expr] = []
    stack: list[vast.Node] = [root]
    while stack:
        node = stack.pop()
        if isinstance(node, vast.Expr):
            found.append(node)
        stack.extend(_children(node))
    return found


def _parse_expr(text: str) -> vast.Expr:
    """*text* parsed as an expression: the value of a function body."""
    prog = pipeline.parse(
        "private fn probe(-> @Unit)\n  requires(true)\n  ensures(true)\n"
        f"  effects(pure)\n{{\n  {text}\n}}\n").program
    body = prog.declarations[0].decl.body
    assert not body.statements, text
    return body.expr


def _trap(ran: pipeline.Ran) -> str:
    """The message of the trap that ended *ran*."""
    assert ran.trap is not None, "the call returned without a trap"
    return str(ran.trap)


def _reads_back(expr: vast.Expr) -> None:
    """``parse(format_expr(e)) == e``, and the text is a fixed point."""
    text = vast.format_expr(expr)
    back = _parse_expr(text)
    assert back == expr, (text, expr, back)
    assert vast.format_expr(back) == text


# ---------------------------------------------------------------------------
# The repros: the issues' programs
# ---------------------------------------------------------------------------

_NAT_SUB = """\
public fn f(@Nat, @Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.2 - (@Nat.1 - @Nat.0)
}
"""


def test_repro_1573_nat_subtraction_trap_keeps_the_parentheses() -> None:
    ran = pipeline.run(_NAT_SUB, fn="f", args=[1, 5, 0])
    assert not ran.ok
    text = _trap(ran)
    assert "`@Nat.2 - (@Nat.1 - @Nat.0)` would be negative" in text, text
    assert "requires(@Nat.2 >= @Nat.1 - @Nat.0)" in text, text


_REFINED_GUARD = """\
type Small = { @Nat | (@Nat.0 > 5 || @Nat.0 == 3) };

public fn g(@Nat -> @Small)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}
"""


def test_repro_1573_refinement_guard_keeps_the_parentheses() -> None:
    ran = pipeline.run(_REFINED_GUARD, fn="g", args=[4])
    assert not ran.ok
    text = _trap(ran)
    assert "return value: @Nat.0 >= 0 && (@Nat.0 > 5 || @Nat.0 == 3) failed" \
        in text, text


_PRECEDENCE = """\
private fn h(@Int -> @Int)
  requires((@Int.0 + 1) * 2 > 4)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  h(0)
}

public fn entry(@Int -> @Int)
  requires((@Int.0 + 1) * 2 > 4)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


def test_repro_1573_contract_texts_keep_the_parentheses() -> None:
    verified = pipeline.verify(_PRECEDENCE)
    by_kind: dict[str, set[str]] = {}
    for ob in verified.envelope()["obligations"]:
        by_kind.setdefault(ob["kind"], set()).add(ob["description"])
    assert "(@Int.0 + 1) * 2 > 4" in by_kind["requires"]
    assert by_kind["call_pre"] == {"(@Int.0 + 1) * 2 > 4"}
    assert "(@Int.0 + 1) * 2" in by_kind["int_overflow"]
    e501 = [d for d in verified.errors if d.error_code == "E501"]
    assert len(e501) == 1
    assert "At this call site: (0 + 1) * 2 > 4" in e501[0].description
    assert "requires((0 + 1) * 2 > 4)" in e501[0].fix
    ran = pipeline.run(_PRECEDENCE, fn="entry", args=[0])
    assert not ran.ok
    assert "requires((@Int.0 + 1) * 2 > 4) failed" in str(
        _trap(ran))


_PIPE = """\
private fn twice(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 * 2)
  effects(pure)
{
  @Int.0 * 2
}

public fn f(@String -> @Int)
  requires(true)
  ensures(@Int.result == (string_length(@String.0) |> nat_to_int() |> twice()))
  effects(pure)
{
  0
}
"""


def test_repro_1573_a_parenthesised_pipe_keeps_its_parentheses() -> None:
    want = ("@Int.result == "
            "(string_length(@String.0) |> nat_to_int() |> twice())")
    descriptions = {ob["description"] for ob in
                    pipeline.verify(_PIPE).envelope()["obligations"]
                    if ob["kind"] == "ensures"}
    assert want in descriptions, descriptions
    ran = pipeline.run(_PIPE, fn="f", raw_args=["abc"])
    assert not ran.ok
    assert f"ensures({want}) failed" in _trap(ran)


# ---------------------------------------------------------------------------
# The round trip: every expression of the corpus and the generator
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "path", CORPUS, ids=[p.relative_to(ROOT).as_posix() for p in CORPUS])
def test_every_corpus_expression_reads_back(path: Path) -> None:
    source = read_source(path)
    parsed = pipeline.parse(source, file=str(path))
    if not parsed.ok:  # a negative fixture
        pytest.skip("the program does not parse")
    prog = parsed.program
    for expr in _expressions(prog):
        _reads_back(expr)
    # And the text is what `vera fmt` writes: a corpus program is canonical,
    # so every one-line contract clause appears in it as rendered.
    if format_source(source, str(path)) != source:
        return
    stack: list[vast.Node] = [prog]
    while stack:
        node = stack.pop()
        if isinstance(node, (vast.Requires, vast.Ensures)) and (
                node.span is not None and node.span.line == node.span.end_line):
            word = "requires" if isinstance(node, vast.Requires) else "ensures"
            line = source_lines(source)[node.span.line - 1]
            assert f"{word}({vast.format_expr(node.expr)})" in line, (
                path.name, line)
        stack.extend(_children(node))


@pytest.mark.parametrize("seed", range(40))
def test_every_generated_expression_reads_back(seed: int) -> None:
    from tests import program_generator as gen
    for _, text in gen.generate(seed).files().items():
        for expr in _expressions(pipeline.parse(text).program):
            _reads_back(expr)


# ---------------------------------------------------------------------------
# The operator matrix: the renderer
# ---------------------------------------------------------------------------

_A, _B, _C = (vast.SlotRef(type_name="Int", type_args=None, index=i)
              for i in (2, 1, 0))
_BINOPS = list(vast.BinOp)


def _bin(op: vast.BinOp, left: vast.Expr, right: vast.Expr) -> vast.Expr:
    return vast.BinaryExpr(op=op, left=left, right=right)


def _pipe(arg: vast.Expr) -> vast.Expr:
    return vast.FnCall(name="f", args=(arg,), piped=True)


@pytest.mark.parametrize(
    ("outer", "inner", "side"),
    list(itertools.product(_BINOPS, _BINOPS, ("left", "right"))),
    ids=lambda v: getattr(v, "name", v))
def test_a_binary_operand_reads_back(
        outer: vast.BinOp, inner: vast.BinOp, side: str) -> None:
    child = _bin(inner, _A, _B)
    expr = (_bin(outer, child, _C) if side == "left"
            else _bin(outer, _C, child))
    _reads_back(expr)


_OPERAND_FORMS = {
    "neg": lambda e: vast.UnaryExpr(op=vast.UnaryOp.NEG, operand=e),
    "not": lambda e: vast.UnaryExpr(op=vast.UnaryOp.NOT, operand=e),
    "index": lambda e: vast.IndexExpr(collection=e, index=_C),
    "index_at": lambda e: vast.IndexExpr(
        collection=vast.SlotRef(type_name="Array", type_args=None, index=0),
        index=e),
    "call": lambda e: vast.FnCall(name="g", args=(e, _C)),
    "pipe_from": _pipe,
}


@pytest.mark.parametrize(
    ("form", "inner"), list(itertools.product(_OPERAND_FORMS, _BINOPS)),
    ids=lambda v: getattr(v, "name", v))
def test_a_binary_expression_under_a_unary_postfix_or_call_reads_back(
        form: str, inner: vast.BinOp) -> None:
    _reads_back(_OPERAND_FORMS[form](_bin(inner, _A, _B)))


@pytest.mark.parametrize(
    ("outer", "side"), list(itertools.product(_BINOPS, ("left", "right"))),
    ids=lambda v: getattr(v, "name", v))
def test_a_pipe_as_a_binary_operand_reads_back(
        outer: vast.BinOp, side: str) -> None:
    child = _pipe(_A)
    _reads_back(_bin(outer, child, _C) if side == "left"
                else _bin(outer, _C, child))


@pytest.mark.parametrize("form", ["neg", "not", "index", "call"])
def test_a_pipe_under_a_unary_postfix_or_call_reads_back(form: str) -> None:
    _reads_back(_OPERAND_FORMS[form](_pipe(_A)))


def test_a_pipe_chain_and_an_implication_chain_read_back() -> None:
    _reads_back(_pipe(_pipe(_A)))
    _reads_back(vast.FnCall(name="f", args=(_pipe(_A), _B), piped=True))
    implies = vast.BinOp.IMPLIES
    _reads_back(_bin(implies, _bin(implies, _A, _B), _C))
    _reads_back(_bin(implies, _A, _bin(implies, _B, _C)))


def test_the_renderer_is_the_formatters() -> None:
    """One renderer: ``format_expr`` is ``vera fmt``'s expression rule."""
    expr = _bin(vast.BinOp.SUB, _A, _bin(vast.BinOp.SUB, _B, _C))
    assert vast.format_expr(expr) == format_expr_canonical(expr) \
        == "@Int.2 - (@Int.1 - @Int.0)"


# ---------------------------------------------------------------------------
# The operator matrix: the messages that print an expression
# ---------------------------------------------------------------------------

_ARITH = ["+", "-", "*"]
_CMP = ["==", "!=", "<", ">", "<=", ">="]
_LOGIC = ["&&", "||", "==>"]


def _int_shapes() -> list[str]:
    """Int expressions over `@Int.1` and `@Int.0` mixing two arithmetic
    operators each way round, a unary minus over a sum, and a call."""
    shapes = []
    for p, q in itertools.product(_ARITH, _ARITH):
        shapes.append(f"(@Int.1 {p} @Int.0) {q} 2")
        shapes.append(f"@Int.1 {p} (@Int.0 {q} 2)")
    shapes.append("-(@Int.1 + @Int.0)")
    shapes.append("abs(@Int.1 - @Int.0) * 2")
    return shapes


def _bool_shapes() -> list[str]:
    """Bool expressions: a comparison over each Int shape, and two logical
    operators each way round over comparisons."""
    shapes = [f"{e} {c} 4" for e, c in zip(
        _int_shapes(), itertools.cycle(_CMP))]
    for p, q in itertools.product(_LOGIC, _LOGIC):
        shapes.append(f"(@Int.1 > 0 {p} @Int.0 > 0) {q} @Int.1 == 7")
        shapes.append(f"@Int.1 > 0 {p} (@Int.0 > 0 {q} @Int.1 == 7)")
    shapes.append("!(@Int.1 > 0 && @Int.0 > 0) || @Int.1 == 7")
    shapes.append("(@Int.1 > 0) == (@Int.0 > 0)")
    return shapes


def _prog_requires(pred: str) -> str:
    return (
        "public fn entry(@Int, @Int -> @Int)\n"
        f"  requires({pred})\n  ensures(true)\n  effects(pure)\n"
        "{\n  0\n}\n")


def _read_back_equal(printed: str, written: str) -> None:
    assert _parse_expr(printed) == _parse_expr(written), (printed, written)


def _canonical(text: str) -> str:
    return format_expr_canonical(_parse_expr(text))


@pytest.mark.parametrize("pred", _bool_shapes())
def test_requires_texts_read_back(pred: str) -> None:
    """The `requires` obligation's description and `vera run`'s
    `requires(...) failed`, for a precondition no input meets."""
    source = _prog_requires(f"({pred}) && false")
    want = f"({pred}) && false"
    verified = pipeline.verify(source)
    described = [ob["description"] for ob in verified.envelope()["obligations"]
                 if ob["kind"] == "requires"]
    assert described == [_canonical(want)]
    _read_back_equal(described[0], want)
    ran = pipeline.run(source, fn="entry", args=[3, 2])
    assert not ran.ok
    match = re.search(r"requires\((.*)\) failed",
                      _trap(ran))
    assert match is not None, _trap(ran)
    _read_back_equal(match.group(1), want)


@pytest.mark.parametrize("pred", _bool_shapes())
def test_call_site_texts_read_back(pred: str) -> None:
    """`call_pre`'s description and E501's "At this call site" line, whose
    instance substitutes the arguments into the callee's precondition."""
    source = (
        "private fn callee(@Int, @Int -> @Int)\n"
        f"  requires(({pred}) && false)\n  ensures(true)\n  effects(pure)\n"
        "{\n  0\n}\n\n"
        "public fn caller(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  callee(@Int.0 + 1, 2 * @Int.0)\n}\n")
    verified = pipeline.verify(source)
    pre = [ob["description"] for ob in verified.envelope()["obligations"]
           if ob["kind"] == "call_pre"]
    assert len(pre) == 1
    _read_back_equal(pre[0], f"({pred}) && false")
    e501 = [d for d in verified.errors if d.error_code == "E501"]
    assert len(e501) == 1
    match = re.search(r"At this call site: (.*)", e501[0].description)
    assert match is not None, e501[0].description
    # The callee's `@Int.1` is the first argument and `@Int.0` the second.
    instance = re.sub(
        r"@Int\.([01])",
        lambda m: "(@Int.0 + 1)" if m.group(1) == "1" else "(2 * @Int.0)",
        f"({pred}) && false")
    _read_back_equal(match.group(1), instance)


@pytest.mark.parametrize("expr", _int_shapes())
def test_int_overflow_texts_read_back(expr: str) -> None:
    """The `int_overflow` obligation's description of the whole sum."""
    source = (
        "public fn entry(@Int, @Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  {expr}\n}}\n")
    verified = pipeline.verify(source)
    overflow = {ob["description"] for ob in verified.envelope()["obligations"]
                if ob["kind"] == "int_overflow"}
    want = _parse_expr(expr)
    outer = want.operand if isinstance(want, vast.UnaryExpr) else want
    assert format_expr_canonical(outer) in overflow, (overflow, expr)
    for text in overflow:
        _parse_expr(text)  # every description parses


@pytest.mark.parametrize("pred", _bool_shapes())
def test_refinement_guard_texts_read_back(pred: str) -> None:
    """A refinement guard's message: the `@Nat` base invariant joined to the
    predicate, which keeps the parentheses the predicate needs."""
    nat_pred = pred.replace("@Int.1", "@Nat.0").replace("@Int.0", "@Nat.0")
    source = (
        f"type R = {{ @Nat | ({nat_pred}) && false }};\n\n"
        "public fn entry(@Nat -> @R)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Nat.0\n}\n")
    ran = pipeline.run(source, fn="entry", args=[3])
    assert not ran.ok
    match = re.search(r"return value: (.*) failed",
                      _trap(ran))
    assert match is not None, _trap(ran)
    _read_back_equal(match.group(1), f"@Nat.0 >= 0 && (({nat_pred}) && false)")


@pytest.mark.parametrize(("p", "q"), list(itertools.product(
    ["+", "-", "*"], ["+", "-", "*"])))
def test_nat_subtraction_trap_reads_back(p: str, q: str) -> None:
    """The `@Nat` subtraction trap's site and its suggested `requires`."""
    right = f"(@Nat.1 {p} @Nat.0) {q} @Nat.0"
    source = (
        "public fn entry(@Nat, @Nat, @Nat -> @Nat)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  @Nat.2 - ({right})\n}}\n")
    ran = pipeline.run(source, fn="entry", args=[0, 3, 1])
    assert not ran.ok
    text = _trap(ran)
    match = re.search(r"subtraction `(.*)` would be negative.*"
                      r"`requires\((.*)\)`", text)
    assert match is not None, text
    _read_back_equal(match.group(1), f"@Nat.2 - ({right})")
    _read_back_equal(match.group(2), f"@Nat.2 >= {right}")


@pytest.mark.parametrize("index", [
    "@Int.0 + 1", "(@Int.0 + 1) * 2", "@Int.0 |> abs()",
    "-(@Int.0 - 9)"])
def test_index_trap_reads_back(index: str) -> None:
    """The index trap's access and both its bounds."""
    source = (
        "public fn entry(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  let @Array<Int> = [1, 2, 3];\n  @Array<Int>.0[{index}]\n}}\n")
    ran = pipeline.run(source, fn="entry", args=[50])
    assert not ran.ok
    text = _trap(ran)
    match = re.search(r"`(.*)` needs `(.*)` and `(.*)`", text)
    assert match is not None, text
    _read_back_equal(match.group(1), f"@Array<Int>.0[{index}]")
    _read_back_equal(match.group(2), f"0 <= {index}"
                     if "|>" not in index else f"0 <= ({index})")
    _read_back_equal(match.group(3), f"({index}) < array_length(@Array<Int>.0)")


@pytest.mark.parametrize("index", ["@Int.0 + 1", "@Int.0 |> abs()"])
def test_string_index_trap_reads_back(index: str) -> None:
    source = (
        "public fn entry(@Int -> @Nat)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f'{{\n  string_char_code("abc", {index})\n}}\n')
    ran = pipeline.run(source, fn="entry", args=[50])
    assert not ran.ok
    text = _trap(ran)
    match = re.search(r"`(.*)` needs `(.*)` and `(.*)`, the string", text)
    assert match is not None, text
    _read_back_equal(match.group(1), f'string_char_code("abc", {index})')
    _read_back_equal(match.group(2), f"0 <= ({index})")
    _read_back_equal(match.group(3), f'({index}) < string_length("abc")')


def test_the_refined_narrowing_fix_parenthesises_a_disjunction() -> None:
    """E5xx's narrowing message joins the base invariant to the predicate as
    a node: a disjunction keeps its parentheses under the `&&`."""
    source = (
        "type R = { @Nat | @Nat.0 > 5 || @Nat.0 == 3 };\n\n"
        "public fn entry(@Nat -> @R)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  4\n}\n")
    verified = pipeline.verify(source)
    texts = [d.description + d.fix for d in verified.errors]
    assert any("`@Nat.0 >= 0 && (@Nat.0 > 5 || @Nat.0 == 3)`" in t
               for t in texts), texts


def test_the_divisor_fix_parenthesises_a_pipe() -> None:
    """E526's suggested clauses are nodes: a piped divisor keeps its
    parentheses under `!=` and `==`."""
    source = (
        "public fn entry(@Int, @Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Int.1 / (@Int.0 |> abs())\n}\n")
    verified = pipeline.verify(source)
    e526 = [d for d in verified.errors if d.error_code == "E526"]
    assert len(e526) == 1
    assert "`requires((@Int.0 |> abs()) != 0)`" in e526[0].fix
    assert "`if (@Int.0 |> abs()) == 0 then" in e526[0].fix


# ---------------------------------------------------------------------------
# The quoted source line (#1853)
# ---------------------------------------------------------------------------

#: The characters `str.splitlines` cuts at and the lexer reads inside a line.
_LINE_BREAKERS = ["\x0b", "\x0c", "\x1c", "\x1d", "\x1e", "\x85",
                  " ", " "]


def _ids(chars: list[str]) -> list[str]:
    return [f"U+{ord(c):04X}" for c in chars]


@pytest.mark.parametrize("char", _LINE_BREAKERS, ids=_ids(_LINE_BREAKERS))
def test_source_lines_cut_at_newline_alone(char: str) -> None:
    text = f"a{char}b\nc\r\nd"
    assert source_lines(text) == [f"a{char}b", "c", "d"]
    assert "".join(source_lines(text, keepends=True)) == text


def test_source_lines_agree_with_splitlines_on_newlines() -> None:
    for text in ["", "a", "a\n", "a\nb", "a\n\nb\n", "\n", "a\r\nb\r\n"]:
        assert source_lines(text) == text.splitlines(), text
        assert source_lines(text, keepends=True) == text.splitlines(
            keepends=True), text


_CHECK_ERROR = (
    "public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
    "  effects(pure)\n{{{char}\n  @Bool.0\n}}\n")


@pytest.mark.parametrize("char", _LINE_BREAKERS, ids=_ids(_LINE_BREAKERS))
def test_the_checker_quotes_the_line_its_location_names(char: str) -> None:
    checked = pipeline.check(_CHECK_ERROR.format(char=char))
    diag = checked.errors[0]
    assert diag.location.line == 6
    assert diag.source_line == "  @Bool.0"


@pytest.mark.parametrize("char", _LINE_BREAKERS, ids=_ids(_LINE_BREAKERS))
def test_the_parser_quotes_the_line_its_location_names(char: str) -> None:

    source = ("public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
              f"  effects(pure)\n{{{char}\n  0 @\n}}\n")
    parsed = pipeline.parse(source)
    assert not parsed.ok
    diag = parsed.diagnostics[0]
    assert diag.location.line == 6
    assert diag.source_line == "  0 @"


@pytest.mark.parametrize("char", _LINE_BREAKERS, ids=_ids(_LINE_BREAKERS))
def test_the_verifier_quotes_the_line_its_location_names(char: str) -> None:
    source = ("public fn f(@Int -> @Int)\n  requires(true)\n"
              f"  ensures(true)\n  effects(pure)\n{{{char}\n"
              "  @Int.0 / 0\n}\n")
    verified = pipeline.verify(source)
    e526 = [d for d in verified.errors if d.error_code == "E526"]
    assert len(e526) == 1
    assert e526[0].location.line == 6
    assert e526[0].source_line == "  @Int.0 / 0"


@pytest.mark.parametrize("char", _LINE_BREAKERS, ids=_ids(_LINE_BREAKERS))
def test_the_language_server_reads_the_line_its_location_names(
        char: str) -> None:
    """The column transcoding reads the line Lark's location counts: an
    astral character on line 2 after the breaker widens the UTF-16 column."""
    from vera.lsp.convert import LineIndex
    index = LineIndex(f"x{char}y\n\U0001F600z")
    assert index.cp_to_utf16(1, 1) == 2


@pytest.mark.parametrize("char", _LINE_BREAKERS, ids=_ids(_LINE_BREAKERS))
def test_the_resolver_quotes_the_line_its_location_names(
        char: str, tmp_path: Path) -> None:
    (tmp_path / "main.vera").write_text(
        f"-- a{char}comment\nimport nowhere;\n\n"
        "public fn main(-> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  0\n}\n", encoding="utf-8")
    checked = pipeline.check(tmp_path / "main.vera")
    diag = checked.errors[0]
    assert diag.location.line == 2
    assert diag.source_line == "import nowhere;"


# ---------------------------------------------------------------------------
# A refinement predicate's KEY is its rendered text (#1573, silent)
# ---------------------------------------------------------------------------

#: `Loose` admits `x > 1`, `Tight` only `x > 2`: two predicates the base
#: renderer wrote alike, `@Int.0 + 1 * 2 > 4`.  The handler-clause binder's
#: narrowing compares predicate-text sets, so at base `Tight` "did not
#: narrow" `Loose`: no obligation, no guard, and 2 was bound into `@Tight`.
_KEYS = """\
type Loose = { @Int | (@Int.0 + 1) * 2 > 4 };

type Tight = { @Int | @Int.0 + 1 * 2 > 4 };

public fn f(@Int -> @Int)
  requires((@Int.0 + 1) * 2 > 4)
  ensures(true)
  effects(pure)
{
  handle[Exn<Loose>] {
    throw(@Tight) -> { @Tight.0 }
  } in {
    throw(@Int.0)
  }
}
"""


def test_repro_1573_predicates_apart_by_parentheses_are_two_keys() -> None:
    verified = pipeline.verify(_KEYS)
    rows = [(ob["kind"], ob["status"], ob["description"])
            for ob in verified.envelope()["obligations"]
            if ob["kind"] == "refine_bind"]
    assert ("refine_bind", "tier3", "@Tight") in rows, rows
    ran = pipeline.run(_KEYS, fn="f", args=[2])
    assert not ran.ok
    assert "@Tight binding: @Int.0 + 1 * 2 > 4 failed" in str(
        _trap(ran))
    assert pipeline.run(_KEYS, fn="f", args=[3]).value == 3


# ---------------------------------------------------------------------------
# The stack_exhausted fix text (#1851)
# ---------------------------------------------------------------------------

def _stack_fix() -> str:
    from vera.trap_registry import TRAP_KINDS
    return TRAP_KINDS["stack_exhausted"].fix


def test_the_stack_fix_says_a_proved_postcondition_costs_the_tail_call() -> None:
    fix = " ".join(_stack_fix().split())
    assert "anything other than `ensures(true)`" in fix
    assert "whether `vera verify` proves the postcondition or not" in fix
    assert "`array_fold` / `array_map`" in fix
    assert "Tier 1" not in fix and "Tier-3" not in fix


_COUNT = """\
public fn count_plain(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    count_plain(@Nat.1 + 1, @Nat.0 - 1)
  }
}

public fn count_proved(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    count_proved(@Nat.1 + 1, @Nat.0 - 1)
  }
}
"""


def test_repro_1851_a_proved_postcondition_exhausts_the_stack() -> None:
    """What the text now states: `count_proved`'s `ensures` is proved, and
    its recursion still exhausts the stack where `ensures(true)` does not."""
    verified = pipeline.verify(_COUNT)
    assert verified.ok
    assert {ob["status"] for ob in verified.envelope()["obligations"]
            if ob["kind"] == "ensures"} == {"verified"}
    assert pipeline.run(_COUNT, fn="count_plain",
                        args=[0, 1000000]).value == 1000000
    ran = pipeline.run(_COUNT, fn="count_proved", args=[0, 1000000])
    assert not ran.ok
    assert ran.trap is not None and ran.trap.kind == "stack_exhausted"
