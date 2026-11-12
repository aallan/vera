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


def test_nat_subtraction_trap_parenthesises_a_piped_operand() -> None:
    """A pipe binds more loosely than `>=`: the suggested `requires` built
    as a node keeps the right operand's parentheses, where joining the two
    rendered operands with `>=` named `(@Nat.1 >= @Nat.0) |> dbl()`."""
    source = (
        "private fn dbl(@Nat -> @Nat)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Nat.0 + @Nat.0\n}\n\n"
        "public fn entry(@Nat, @Nat -> @Nat)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Nat.1 - (@Nat.0 |> dbl())\n}\n")
    ran = pipeline.run(source, fn="entry", args=[1, 5])
    assert not ran.ok
    text = _trap(ran)
    assert "`@Nat.1 - (@Nat.0 |> dbl())` would be negative" in text, text
    assert "`requires(@Nat.1 >= (@Nat.0 |> dbl()))`" in text, text


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


def test_the_stack_fix_names_the_check_at_the_exit() -> None:
    """The condition is a check when the function returns, from either of
    its two sources, whatever the verdict; the cells below pin each."""
    fix = " ".join(_stack_fix().split())
    assert "a function that checks something when it returns" in fix
    assert "a postcondition the compiled code checks at run time" in fix
    assert "the guard of a refined return type" in fix
    assert "does not by itself remove it" in fix
    assert "`array_fold` / `array_map`" in fix
    assert "Tier 1" not in fix and "Tier-3" not in fix
    assert "ensures(true)" not in fix


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


_EXIT_CHECKS = """\
type Pos = { @Nat | @Nat.0 > 0 };

public fn cp(@Pos, @Nat -> @Pos)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Pos.0
  } else {
    cp(@Pos.0, @Nat.0 - 1)
  }
}

public fn cs(@String, @Nat -> @String)
  requires(true)
  ensures(string_length(@String.result) >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @String.0
  } else {
    cs(@String.0, @Nat.0 - 1)
  }
}
"""


def test_repro_1851_a_refined_return_s_guard_costs_the_tail_call() -> None:
    """`cp` says `ensures(true)`, and its refined return's guard, a check
    at the exit, still costs its tail calls: the text's second source."""
    verified = pipeline.verify(_EXIT_CHECKS)
    assert verified.ok
    ran = pipeline.run(_EXIT_CHECKS, fn="cp", args=[1, 1000000])
    assert ran.trap is not None and ran.trap.kind == "stack_exhausted"


def test_a_postcondition_with_no_check_at_the_exit_keeps_the_tail_call() -> None:
    """`cs`'s postcondition is not `true`, and no check is emitted for it,
    so its tail calls are kept: the condition is the check, not the
    clause's spelling."""
    ran = pipeline.run(_EXIT_CHECKS, fn="cs", raw_args=["abc", "1000000"])
    assert ran.ok
    assert ran.value == "abc"


# ---------------------------------------------------------------------------
# Exact values: every reader moved to the one splitter, at line 1, at the
# last line, past the end and with no span; the exact text a span covers;
# the exact texts the verifier's reports and the traps compose
# ---------------------------------------------------------------------------

#: Three lines as the location counts them; the second holds a vertical tab
#: (`splitlines` would make it two) and ends in the `\r` of a `\r\n`.
_TEXT = "first line\nsecond\x0bstill second\r\nthird"
_LINES = {0: "", 1: "first line", 2: "second\x0bstill second", 3: "third",
          4: ""}


def _span(line: int, column: int = 1, end_line: int | None = None,
          end_column: int = 2) -> vast.Span:
    return vast.Span(line=line, column=column,
                     end_line=line if end_line is None else end_line,
                     end_column=end_column)


@pytest.mark.parametrize("line", sorted(_LINES))
def test_errors_quotes_the_counted_line(line: int) -> None:
    from vera.errors import _get_source_line
    assert _get_source_line(_TEXT, line) == _LINES[line]


@pytest.mark.parametrize("line", sorted(_LINES))
def test_the_checker_quotes_the_counted_line(line: int) -> None:
    from vera.checker.core import TypeChecker
    assert TypeChecker(source=_TEXT)._source_line(_span(line)) == _LINES[line]


def test_the_checker_quotes_nothing_without_a_span_or_a_source() -> None:
    from vera.checker.core import TypeChecker
    assert TypeChecker(source=_TEXT)._source_line(None) == ""
    assert TypeChecker(source="")._source_line(_span(1)) == ""


@pytest.mark.parametrize("line", sorted(_LINES))
def test_the_resolver_quotes_the_counted_line(line: int, tmp_path: Path) -> None:
    from vera.resolver import ModuleResolver
    path = tmp_path / "m.vera"
    path.write_bytes(_TEXT.encode("utf-8"))
    node = vast.IntLit(value=0, span=_span(line))
    assert ModuleResolver._source_line(path, node) == _LINES[line]
    assert ModuleResolver._source_line(path, vast.IntLit(value=0)) == ""


@pytest.mark.parametrize("line", sorted(_LINES))
def test_the_tester_quotes_the_counted_line(line: int) -> None:
    from types import SimpleNamespace

    from vera.tester import _get_source_line
    decl = SimpleNamespace(span=_span(line, column=3))
    assert _get_source_line(_TEXT, decl) == _LINES[line]  # type: ignore[arg-type]
    assert _get_source_line(_TEXT, SimpleNamespace(span=None)) == ""  # type: ignore[arg-type]


@pytest.mark.parametrize("line", sorted(_LINES))
@pytest.mark.parametrize("same_file", [True, False])
def test_an_e703_quotes_the_counted_line(line: int, same_file: bool) -> None:
    """The refuted clause's line when it lies in the file under test and
    the line exists; the declaration's (line 3) otherwise."""
    from types import SimpleNamespace

    from vera.tester import _TestEngine
    engine = SimpleNamespace(source=_TEXT, file="f.vera")
    trial = SimpleNamespace(refutes=[SimpleNamespace(
        file="f.vera" if same_file else "g.vera", line=line, column=4)])
    decl = SimpleNamespace(span=_span(3, column=2))
    loc, quoted = _TestEngine._refuted_location(
        engine, trial, decl)  # type: ignore[arg-type]
    if same_file and 1 <= line <= 3:
        assert (loc.line, loc.column, quoted) == (line, 4, _LINES[line])
    else:
        assert (loc.line, loc.column, quoted) == (3, 2, "third")


@pytest.mark.parametrize("line", sorted(_LINES))
def test_the_typed_program_quotes_the_counted_line(line: int) -> None:
    from vera.typed import _diagnostic
    diag = _diagnostic("E613", "f.vera", _TEXT,
                       vast.IntLit(value=0, span=_span(line, column=5)),
                       "description", "fix")
    assert (diag.location.file, diag.location.line, diag.location.column,
            diag.source_line) == ("f.vera", line, 5, _LINES[line])
    unspanned = _diagnostic("E613", "f.vera", _TEXT, vast.IntLit(value=0),
                            "description", "fix")
    assert (unspanned.location.line, unspanned.source_line) == (0, "")


@pytest.mark.parametrize("line", sorted(_LINES))
def test_reconciliation_quotes_the_counted_line(line: int) -> None:
    from vera.reconcile import Mismatch, mismatch_diagnostics
    m = Mismatch(kind="guarded_unrecorded", obligation="nat_sub",
                 file="f.vera", line=line, column=1, function="f",
                 emitter="wasm/operators.py:_emit_nat_sub_guard")
    (diag,) = mismatch_diagnostics([m], {"f.vera": _TEXT})
    assert diag.source_line == _LINES[line]


#: Spans and the exact text each covers, by the location's own count: a
#: span on line 1, one across the vertical tab's line into the last, one
#: on the last line, and spans the text does not hold.
_COVERS = [
    (_span(1, 1, 1, 6), "first"),
    (_span(2, 8, 3, 3), "still second\r\nth"),
    (_span(3, 1, 3, 6), "third"),
    (_span(4, 1, 4, 2), None),
    (_span(0, 1, 1, 2), None),
    (_span(1, 1, 4, 2), None),
    (_span(4, 1, 3, 2), None),  # starts past the last line, ends before it
    (None, None),
]


@pytest.mark.parametrize(("span", "covered"), _COVERS)
def test_the_span_bounds_cover_the_counted_text(
        span: vast.Span | None, covered: str | None) -> None:
    from vera.checker.resolution import _span_bounds
    from vera.typed import _source_text
    bounds = _span_bounds(_TEXT, span)
    assert (None if bounds is None else _TEXT[bounds[0]:bounds[1]]) == covered
    assert _source_text(_TEXT, span) == covered
    assert _span_bounds("", span) is None and _source_text("", span) is None


@pytest.mark.parametrize(("span", "start", "end"), [
    (_span(2, 8, 2, 13), 6, 11),     # within the base's first line
    (_span(3, 1, 3, 4), 20, 23),     # on the base's second, last line
    (_span(5, 1, 5, 2), None, None),  # past the text's last line
    (_span(1, 1, 1, 2), None, None),  # before the base
])
def test_an_offset_counts_lines_by_the_newline(
        span: vast.Span, start: int | None, end: int | None) -> None:
    """`_offset` within the text a base span covers (it starts at line 2,
    column 2): the vertical tab is inside the base's first line."""
    from vera.typed import _offset
    text = "second\x0bstill second\r\nthird"[1:]
    base = _span(2, 2, 3, 6)
    assert _offset(text, base, span, start=True) == start
    assert _offset(text, base, span, start=False) == end
    assert _offset(text, base, None, start=True) is None


# The verifier's reports, whole.

_H = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _only_error(source: str, code: str) -> tuple[str, str]:
    errors = [d for d in pipeline.verify(source).errors if d.error_code == code]
    assert len(errors) == 1, errors
    return errors[0].description, errors[0].fix


def test_e502_in_a_measure_says_the_bounding_requires_whole() -> None:
    description, fix = _only_error(
        "public fn count_to(@Nat -> @Nat)\n" + _H
        + "{\n  loop(@Nat.0, 1)\n}\nwhere {\n  fn loop(@Nat, @Nat -> @Nat)\n"
        "    requires(true)\n    ensures(true)\n"
        "    decreases(@Nat.1 - @Nat.0 + 1)\n    effects(pure)\n  {\n"
        "    if @Nat.0 > @Nat.1 then { @Nat.0 } else "
        "{ loop(@Nat.1, @Nat.0 + 1) }\n  }\n}\n", "E502")
    assert description == (
        "@Nat subtraction in 'loop' may underflow.\n  Counterexample:\n"
        "      @Nat.0 = 1\n      @Nat.1 = 0\n  In the `decreases` measure, "
        "which the compiled function evaluates on entry, after its "
        "`requires` are checked.")
    assert fix == (
        "Either state the precondition that bounds the subtraction — "
        "`requires(@Nat.0 <= @Nat.1)`; for the count-up loop "
        "`decreases(@Nat.1 + 1 - @Nat.0)` that is "
        "`requires(@Nat.0 <= @Nat.1 + 1)` — which the measure can rely "
        "on because the compiled function checks every `requires` before it "
        "evaluates it, and which each recursive call must then establish for "
        "its own arguments; or write the measure without a `@Nat` "
        "subtraction, for example a parameter that counts down to zero.")


def test_e502_in_a_body_says_the_generic_remedy() -> None:
    _, fix = _only_error(
        "public fn f(@Nat, @Nat -> @Nat)\n" + _H + "{\n  @Nat.1 - @Nat.0\n}\n",
        "E502")
    assert fix == (
        "Add a precondition that rules out the bad inputs, e.g. "
        "`requires(@Nat.0 >= @Nat.1)`.  Alternatively, guard the "
        "subtraction: `if @Nat.0 >= @Nat.1 then @Nat.0 - @Nat.1 else 0` "
        "— the path condition discharges the obligation in the "
        "then-branch.")


@pytest.mark.parametrize(("op", "word"), [("/", "division"), ("%", "modulo")])
def test_e526_says_the_operation_and_the_divisor_whole(op: str, word: str) -> None:
    description, fix = _only_error(
        "public fn f(@Int, @Int -> @Int)\n" + _H
        + f"{{\n  @Int.1 {op} (@Int.0 - 1)\n}}\n", "E526")
    assert description == (
        f"Integer {word} in 'f' may divide by zero.\n  Counterexample:\n"
        "      @Int.0 = 1\n      @Int.1 = 0")
    assert fix == (
        "Add a precondition ruling out a zero divisor, e.g. "
        "`requires(@Int.0 - 1 != 0)`.  Alternatively guard the operation "
        "with `if @Int.0 - 1 == 0 then <default> else ...` (the path "
        "condition discharges the obligation in the else-branch), or give "
        "the divisor a refinement type that excludes zero.")


def test_e527_says_the_bounds_and_the_access_whole() -> None:
    description, fix = _only_error(
        "public fn f(@Int -> @Int)\n  requires(@Int.0 < 0 - 1)\n"
        "  ensures(true)\n  effects(pure)\n"
        "{\n  let @Array<Int> = [1, 2, 3];\n  @Array<Int>.0[@Int.0 + 1]\n}\n",
        "E527")
    assert description.startswith(
        "Array index in 'f' is out of bounds.\n  Counterexample:\n"
        "      @Int.0 = "), description
    bounds = "0 <= @Int.0 + 1 && @Int.0 + 1 < array_length(@Array<Int>.0)"
    assert fix == (
        "Index within bounds, or constrain the index with a precondition "
        f"covering both bounds, e.g. `requires({bounds})`.  Alternatively "
        f"guard the access with `if {bounds} then @Array<Int>.0[@Int.0 + 1] "
        "else <default>` — the path condition discharges the obligation "
        "in the then-branch.")


@pytest.mark.parametrize("body", ["4", "@Nat.0"])
def test_e505_says_the_whole_chain_with_its_parentheses(body: str) -> None:
    description, fix = _only_error(
        "type Small = { @Nat | @Nat.0 > 5 || @Nat.0 == 3 };\n\n"
        "public fn f(@Nat -> @Small)\n" + _H + f"{{\n  {body}\n}}\n", "E505")
    pred = "@Nat.0 >= 0 && (@Nat.0 > 5 || @Nat.0 == 3)"
    head, value = description.rsplit(" = ", 1)
    assert head == (
        "Value narrowing into a refined return type in 'f' may violate the "
        f"refinement predicate `{pred}`.\n  Counterexample:\n"
        "      @Nat.0")
    assert value.isdigit(), value
    assert fix == (
        f"Add a precondition implying the predicate, e.g. `requires({pred})`."
        "  Alternatively, guard the binding with an `if` whose condition is "
        "the predicate — the path condition discharges the obligation in "
        "the then-branch.")


def test_e501_quotes_a_clause_across_lines_whole() -> None:
    description, _ = _only_error(
        "private fn h(@Int -> @Int)\n  requires(\n    (@Int.0 + 1) * 2 > 4 -- c\n"
        "  )\n  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n\n"
        "public fn caller(@Int -> @Int)\n" + _H + "{\n  h(0)\n}\n", "E501")
    assert description.splitlines()[1:3] == [
        "  Precondition: requires( (@Int.0 + 1) * 2 > 4 )",
        "  At this call site: (0 + 1) * 2 > 4"]


def test_e501_quotes_a_clause_on_the_first_line() -> None:
    """The clause's lines are counted from line 1: a callee written on the
    file's first line still has its precondition quoted."""
    description, _ = _only_error(
        "private fn h(@Int -> @Int) requires(@Int.0 > 0) ensures(true) "
        "effects(pure) { @Int.0 }\n\n"
        "public fn caller(@Int -> @Int)\n" + _H + "{\n  h(0)\n}\n", "E501")
    precondition = description.splitlines()[1]
    assert precondition.startswith("  Precondition: "), description
    assert "requires(@Int.0 > 0)" in precondition


def test_e527_without_a_counterexample_says_the_access_alone() -> None:
    """The report with no model to show: the description is its first
    sentence and nothing after it."""
    from types import SimpleNamespace

    from vera.verifier import ContractVerifier
    reported: list[tuple[str, str]] = []
    verifier = SimpleNamespace(
        _as_written=lambda node: node,
        _written=vast.format_expr,
        _error=lambda node, description, **kw: reported.append(
            (description, kw["fix"])))
    access = vast.IndexExpr(
        collection=vast.SlotRef(type_name="Array", type_args=None, index=0),
        index=_A)
    ContractVerifier._report_index_oob(
        verifier, SimpleNamespace(name="f"), access, None)  # type: ignore[arg-type]
    assert reported[0][0] == "Array index in 'f' is out of bounds."


# The traps' messages, whole.

def test_the_nat_subtraction_trap_message_whole() -> None:
    ran = pipeline.run(_NAT_SUB, fn="f", args=[1, 5, 0])
    assert _trap(ran) == (
        "@Nat subtraction `@Nat.2 - (@Nat.1 - @Nat.0)` would be negative "
        "(line 6): its right operand is larger than its left.  Add "
        "`requires(@Nat.2 >= @Nat.1 - @Nat.0)` to the enclosing function, "
        "or compute in @Int.")


def test_the_index_trap_message_whole() -> None:
    ran = pipeline.run(
        "public fn entry(@Int -> @Int)\n" + _H
        + "{\n  let @Array<Int> = [1, 2, 3];\n  @Array<Int>.0[@Int.0 + 1]\n}\n",
        fn="entry", args=[50])
    assert _trap(ran) == (
        "Array index out of bounds (line 7): `@Array<Int>.0[@Int.0 + 1]` "
        "needs `0 <= @Int.0 + 1` and "
        "`@Int.0 + 1 < array_length(@Array<Int>.0)`.")


def test_the_string_index_trap_message_whole() -> None:
    ran = pipeline.run(
        "public fn entry(@Int -> @Nat)\n" + _H
        + '{\n  string_char_code("abc", @Int.0 + 1)\n}\n',
        fn="entry", args=[50])
    assert _trap(ran) == (
        'String index out of bounds (line 6): `string_char_code("abc", '
        '@Int.0 + 1)` needs `0 <= @Int.0 + 1` and '
        '`@Int.0 + 1 < string_length("abc")`, the string\'s length in bytes.')


def test_the_resolver_quotes_nothing_from_a_file_it_cannot_read(
        tmp_path: Path) -> None:
    from vera.resolver import ModuleResolver
    node = vast.IntLit(value=0, span=_span(1))
    assert ModuleResolver._source_line(tmp_path / "absent.vera", node) == ""


@pytest.mark.parametrize("line", sorted(_LINES))
def test_the_verifier_quotes_the_counted_line(line: int) -> None:
    from types import SimpleNamespace

    from vera.verifier import ContractVerifier
    verifier = SimpleNamespace(_current_source=_TEXT)
    assert ContractVerifier._get_source_line(
        verifier, line) == _LINES[line]  # type: ignore[arg-type]


def _reporting_verifier(reported: list[tuple[str, str]], **reads: object):
    from types import SimpleNamespace
    return SimpleNamespace(
        _as_written=lambda node: node, _written=vast.format_expr,
        _error=lambda node, description, **kw: reported.append(
            (description, kw["fix"])), **reads)


def test_e527_leaves_the_result_out_of_its_counterexample() -> None:
    from vera.verifier import ContractVerifier
    reported: list[tuple[str, str]] = []
    access = vast.IndexExpr(
        collection=vast.SlotRef(type_name="Array", type_args=None, index=0),
        index=_A)
    ContractVerifier._report_index_oob(
        _reporting_verifier(reported), _named("f"), access,
        {"@result": "1", "@Int.2": "-1"})  # type: ignore[arg-type]
    assert reported[0][0] == (
        "Array index in 'f' is out of bounds.\n  Counterexample:\n"
        "      @Int.2 = -1")


def _named(name: str) -> object:
    from types import SimpleNamespace
    return SimpleNamespace(name=name)


def test_e505_names_the_predicate_it_cannot_render() -> None:
    """A refined type whose chain the verifier cannot read: the report says
    "the predicate" in both places, and leaves the result out."""
    from vera.verifier import ContractVerifier
    reported: list[tuple[str, str]] = []
    ContractVerifier._report_refined_binding(
        _reporting_verifier(reported, _refined_chain=lambda ty: None),
        _named("f"), _A, None, "return type",
        {"@result": "1", "@Int.2": "0"})  # type: ignore[arg-type]
    description, fix = reported[0]
    assert description == (
        "Value narrowing into a refined return type in 'f' may violate the "
        "refinement predicate `the predicate`.\n  Counterexample:\n"
        "      @Int.2 = 0")
    assert "`requires(the predicate)`" in fix


def test_e501_quotes_an_imported_clause_from_its_own_file(
        tmp_path: Path) -> None:
    """The clause is quoted out of the module that declares it: the line
    numbers its span counts are that file's."""
    (tmp_path / "lib.vera").write_text(
        "-- a library\n\npublic fn h(@Int -> @Int)\n"
        "  requires(@Int.0 > 7)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Int.0\n}\n", encoding="utf-8")
    (tmp_path / "main.vera").write_text(
        "import lib(h);\n\npublic fn caller(@Int -> @Int)\n" + _H
        + "{\n  h(0)\n}\n", encoding="utf-8")
    verified = pipeline.verify(tmp_path / "main.vera")
    e501 = [d for d in verified.errors if d.error_code == "E501"]
    assert len(e501) == 1, verified.errors
    assert e501[0].description.splitlines()[1] == (
        "  Precondition: requires(@Int.0 > 7)")
