"""A pipe is the call it stands for.

`a |> f(b, c)` means `f(a, b, c)` (spec §4.11.2).  The pipe used to reach
every phase as a `BinaryExpr` whose operator was `|>`, so each walker over
the AST had to know that one of the binary operators is a call.  The ones
that rebuilt the call (`pipe_desugared_call`, at seven sites, and seven
more `op == PIPE` tests) agreed with the direct spelling; the ones that did
not read the pipe as an operator, and the two spellings of one call parted
company:

* #1615 — a pipe as an `if` or `match` arm's tail gave the `if` no result
  type, so `vera compile` wrote an invalid module and exited 0;
* #1614 — a piped `map_insert` in a typed `let` was guarded at the store
  and never obligated;
* #1604 — indexing a pipe's result dropped the function (E602);
* #1599 — a pipe as a tuple or constructor component dropped the function;
* #1580 — a `@Nat` result piped into an `@Int` position was never a
  widening: no obligation, no guard, `u64.MAX` came back as -1;
* #1578 — a pipe as a `match` scrutinee dropped the function;
* #1626 — a piped call in tail position was no tail call (`call`, not
  `return_call`, so a piped tail recursion exhausted the stack, and its
  `decreases` went unproved); a piped `decreases` measure was obligated at
  Tier 3 and never checked; a piped `eq` or `compare` dropped the function;
  a piped `put` in a handled body compiled to an invalid module; and a
  piped float conversion carried no obligation for the check it traps on.

The transform now writes the pipe as the call once, flagged `piped` so
`vera fmt` prints it back, and no later phase can tell the spellings apart.
A pipe into a constructor or a qualified effect operation, which `main`
refused at check, is the call it stands for too; a right operand that is
not a call, which `main` typed as the right operand alone, is E040.

The class: a program whose behaviour differs between a pipe and the call it
stands for, in any phase.  It spans every position a call can take, every
call form a pipe can name, and every phase.  The instrument:

* `TestTheReportedPrograms` — each issue's program, checked, verified,
  compiled and run (#1615's run in a subprocess: on `main` its module is
  invalid).
* `TestEveryPosition` — a call in every expression position the grammar and
  the AST have (enumerated, with a coverage cell), written directly and as
  a pipe.  The direct spelling is the premise: it checks, verifies, compiles
  and runs to its value.  The pipe must then agree with it in every phase:
  the same diagnostics, the same obligations, the same WAT, the same value.
* `TestEveryCallForm` — every call form the pipe can name (`fn_call`'s
  alternatives with an argument list) and every kind of callee, the same
  agreement in a tail position, a `let` and an `if` arm.  A cell with a
  module compares the verifier's errors, not its obligations: the shared
  multi-module builder reports errors only.
* `TestTheCorpusPipesEveryCall` — a generator: every call with an argument
  in the corpus, written as a pipe, transforms to the same AST and formats
  back to the pipe.
* `TestARightOperandThatIsNoCall` — every other right operand is E040.
"""

from __future__ import annotations

import dataclasses
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import NamedTuple

import pytest
import wasmtime

from tests.checker_helpers import _check
from tests.codegen_helpers import exceptions_engine
from tests.module_fixture_helpers import build_multi_module
from tests.test_check_implies_compile import (
    ast_expression_fields,
    grammar_expression_positions,
)
from tests.verifier_helpers import _verify
from vera import ast
from vera.codegen import CompileResult, execute
from vera.errors import TransformError
from vera.formatter import (
    Formatter,
    _attach_comments,
    blank_source_lines,
    extract_comments,
    format_source,
)
from vera.parser import parse_to_ast
from vera.runtime.traps import WasmTrapError

ROOT = Path(__file__).resolve().parent.parent

# =====================================================================
# Drivers: the shared helpers, and a run that never executes a module
# that does not validate
# =====================================================================


class Built(NamedTuple):
    """One program through every phase, as `vera run` drives it."""

    check: list[tuple[str, str]]  # (code, severity) of every diagnostic
    obligations: list[tuple[str, str, str, int, str]]
    verify: list[tuple[str, str]]  # (code, severity) of verify diagnostics
    result: CompileResult
    valid: bool  # the module validates

    @property
    def wat(self) -> str:
        return self.result.wat

    @property
    def codegen(self) -> list[str]:
        return [d.error_code for d in self.result.diagnostics]

    def describe(self) -> str:
        return (f"check {self.check}\nverify {self.verify}\n"
                f"codegen {[(d.error_code, d.description[:120]) for d in self.result.diagnostics]}\n"
                f"exports {self.result.exports}\nvalid {self.valid}")


def _build(tmp_path: Path, files: dict[str, str]) -> Built:
    """Check, verify (obligations included) and compile ``main.vera`` as
    `vera run` does."""
    source = files["main.vera"]
    _verify_errors, result, _cg = build_multi_module(tmp_path, files)
    if len(files) == 1:
        check = [(d.error_code, d.severity) for d in _check(source)]
        verified = _verify(source)
        obligations = [(o.fn_name, o.kind, o.status, o.line, o.error_code)
                       for o in verified.obligations]
        verify = [(d.error_code, d.severity) for d in verified.diagnostics]
    else:
        # The multi-module builder raises on a check error, so a module
        # cell's premise is the builder returning at all.
        check, obligations = [], []
        verify = [(code, "error") for code, _d in _verify_errors]
    try:
        wasmtime.Module.validate(exceptions_engine(), result.wasm_bytes)
        valid = True
    except wasmtime.WasmtimeError:
        valid = False
    return Built(check, obligations, verify, result, valid)


def _value(built: Built, fn: str,
           args: list[int | float]) -> tuple[str, object]:
    """``("ok", value)`` or ``("trap", message)``.  A module that does not
    validate, or that dropped *fn*, is reported as such and never
    instantiated in-process."""
    if not built.valid:
        return "invalid module", None
    if fn not in built.result.exports:
        return "dropped", [d.error_code for d in built.result.diagnostics]
    try:
        return "ok", execute(built.result, fn_name=fn, args=args).value
    except WasmTrapError as exc:
        return "trap", str(exc)


def _single(tmp_path: Path, source: str) -> Built:
    return _build(tmp_path, {"main.vera": source})


def _fn(sig: str, body: str, *, vis: str = "private", req: str = "true",
        ens: str = "true", dec: str | None = None,
        eff: str = "pure") -> str:
    decreases = f"  decreases({dec})\n" if dec else ""
    return (f"{vis} fn {sig}\n  requires({req})\n  ensures({ens})\n"
            f"{decreases}  effects({eff})\n{{\n  {body}\n}}\n")


def _with(*decls: str, main: str) -> str:
    return "\n".join((*decls, main))


# =====================================================================
# The reported programs
# =====================================================================

_INC = _fn("inc(@Int, @Int -> @Int)", "@Int.0 + @Int.1")
_ID = ("private forall<T> fn id(@T -> @T)\n  requires(true)\n"
       "  ensures(true)\n  effects(pure)\n{\n  @T.0\n}\n")
_BIG = _fn("big(@Nat -> @Nat)", "@Nat.0")
_TWICE = _fn("twice(@Int -> @Int)", "@Int.0 * 2")
_U64_MAX = 18446744073709551615


class TestTheReportedPrograms:
    """Each issue's own program, run to the value its direct spelling gives."""

    def test_1615_a_pipe_as_an_if_arm_tail(self, tmp_path: Path) -> None:
        """The `if` takes the arms' type, and the module loads and runs.
        The run is a subprocess: on `main` the module is invalid."""
        source = _with(_INC, main=_fn(
            "g(@Float64 -> @Int)",
            "if @Float64.0 > 0.0 then { 1 |> inc(2) } else { 3 |> inc(4) }",
            vis="public"))
        built = _single(tmp_path, source)
        assert built.valid, built.describe()
        assert "(result i64)" in built.wat
        path = tmp_path / "issue1615.vera"
        path.write_text(source, encoding="utf-8")
        for arg, value in (("5.0", "3"), ("-5.0", "7")):
            ran = subprocess.run(
                [sys.executable, "-m", "vera.cli", "run", str(path),
                 "--fn", "g", "--", arg],
                capture_output=True, text=True, encoding="utf-8",
                timeout=120, check=False, cwd=ROOT)
            assert ran.returncode == 0, ran.stderr
            assert ran.stdout.strip() == value

    @pytest.mark.parametrize("arm", ("if", "match"))
    def test_1615_the_map_and_match_variants(self, arm: str,
                                             tmp_path: Path) -> None:
        """The issue's other two spellings: a `map_insert` pipe in an `if`
        arm, and a pipe as a `match` arm's tail."""
        if arm == "if":
            body = ('let @Map<String, Int> = if @Int.0 > 0 then '
                    '{ map_new() |> map_insert("k", 1) } else '
                    '{ map_new() |> map_insert("k", 2) };\n'
                    '  option_unwrap_or(map_get(@Map<String, Int>.0, "k"), 0)')
            expect = 1
        else:
            body = ("match @Int.0 {\n    0 -> 0 |> inc(1),\n"
                    "    @Int -> @Int.0 |> inc(1)\n  }")
            expect = 6
        built = _single(tmp_path, _with(_INC, main=_fn(
            "f(@Int -> @Int)", body, vis="public")))
        assert built.valid, built.describe()
        assert _value(built, "f", [5]) == ("ok", expect)

    @pytest.mark.parametrize("shape", (
        "let", "return", "block tail", "nested", "refined"))
    def test_1614_a_piped_map_insert_is_obligated(self, shape: str,
                                                  tmp_path: Path) -> None:
        """The map value is obligated where it is guarded, as the direct
        spelling's is (a `nat_bind`, or for a refined value a guarded
        `refine_bind`), and a negative value traps at the store."""
        value = "float_to_int(@Float64.0)"
        piped = f'map_new() |> map_insert("k", {value})'
        decls: tuple[str, ...] = ()
        ret = "@Int"
        if shape == "let":
            body = f"let @Map<String, Nat> = {piped};\n  7"
        elif shape == "return":
            body, ret = piped, "@Map<String, Nat>"
        elif shape == "block tail":
            body = f"let @Map<String, Nat> = {{\n    {piped}\n  }};\n  7"
        elif shape == "nested":
            body = ("let @Map<String, Tuple<Nat, Int>> = map_new() |> "
                    f'map_insert("k", Tuple({value}, 3));\n  7')
        else:
            decls = ("type PosInt = { @Int | @Int.0 > 0 };\n",)
            body = f"let @Map<String, PosInt> = {piped};\n  7"
        source = _with(*decls, main=_fn(f"g(@Float64 -> {ret})", body,
                                        vis="public"))
        built = _single(tmp_path, source)
        kind = "refine_bind" if shape == "refined" else "nat_bind"
        line = next(i for i, text in enumerate(source.splitlines(), 1)
                    if "map_insert" in text)
        statuses = [o[2] for o in built.obligations
                    if o[1] == kind and o[3] == line]
        assert "tier3" in statuses, built.obligations
        assert built.valid, built.describe()
        ran = _value(built, "g", [-5.0])
        assert ran[0] == "trap", ran

    def test_1604_indexing_a_pipes_result(self, tmp_path: Path) -> None:
        built = _single(tmp_path, _fn(
            "f(@Int -> @Int)",
            "let @Array<Int> = [1, 5];\n"
            "  (@Array<Int>.0 |> array_reverse())[0]", vis="public"))
        assert "E602" not in built.codegen, built.describe()
        assert _value(built, "f", [0]) == ("ok", 5)

    @pytest.mark.parametrize("component", (
        "Tuple(1, 3 |> id())", "Tuple(1, { 3 |> id() })", "a box"))
    def test_1599_a_pipe_as_a_component(self, component: str,
                                        tmp_path: Path) -> None:
        decls: tuple[str, ...] = (_ID,)
        if component == "a box":
            decls += ("private data Box {\n  MkBox(Int)\n}\n",)
            body = "match MkBox(3 |> id()) {\n    MkBox(@Int) -> @Int.0\n  }"
        else:
            body = f"let Tuple<@Int, @Int> = {component};\n  @Int.0"
        built = _single(tmp_path, _with(*decls, main=_fn(
            "f(@Int -> @Int)", body, vis="public")))
        assert "E602" not in built.codegen, built.describe()
        assert _value(built, "f", [0]) == ("ok", 3)

    @pytest.mark.parametrize("fn,body", (
        ("f", "let @Int = @Nat.0 |> big();\n  @Int.0"),
        ("h", "@Nat.0 |> big()"),
    ))
    def test_1580_a_piped_nat_widening(self, fn: str, body: str,
                                       tmp_path: Path) -> None:
        """Obligated as `nat_to_int_coerce`, and guarded: `u64.MAX` traps
        instead of coming back as -1."""
        built = _single(tmp_path, _with(_BIG, main=_fn(
            f"{fn}(@Nat -> @Int)", body, vis="public")))
        assert (fn, "nat_to_int_coerce", "tier3") in {
            o[:3] for o in built.obligations}, built.obligations
        ran = _value(built, fn, [_U64_MAX])
        assert ran[0] == "trap", ran
        assert _value(built, fn, [42]) == ("ok", 42)

    def test_1578_a_pipe_as_a_match_scrutinee(self, tmp_path: Path) -> None:
        """The pipe half of #1578.  Its `array_fold` scrutinee is no pipe:
        code generation re-derives that call's type, and it stays open."""
        built = _single(tmp_path, _with(_TWICE, main=_fn(
            "main(@Unit -> @Int)",
            "match 3 |> twice() {\n    @Int -> @Int.0\n  }", vis="public")))
        assert "E602" not in built.codegen, built.describe()
        assert _value(built, "main", []) == ("ok", 6)

    def test_a_piped_tail_recursion(self, tmp_path: Path) -> None:
        """#1626: a tail call however it is spelled — `return_call`, a
        `decreases` obligation the verifier proves, and a million-deep
        recursion that returns rather than exhausting the stack."""
        built = _single(tmp_path, _fn(
            "count(@Nat -> @Nat)",
            "if @Nat.0 == 0 then { 0 } else { @Nat.0 - 1 |> count() }",
            vis="public", dec="@Nat.0"))
        assert "return_call $count" in built.wat
        assert ("count", "decreases", "verified") in {
            o[:3] for o in built.obligations}, built.obligations
        assert "E525" not in {code for code, _s in built.verify}
        assert _value(built, "count", [1_000_000]) == ("ok", 0)


# =====================================================================
# Every position: a call written directly and as a pipe
# =====================================================================

#: The callees the cells call.  `sub2` reads its arguments in order, so a
#: pipe that put the piped value anywhere but first would change the value
#: (10 - 3, not 3 - 10).
_CALLEES = "\n".join((
    _fn("sub2(@Int, @Int -> @Int)", "@Int.1 - @Int.0",
        ens="@Int.result == @Int.1 - @Int.0"),
    _fn("gt(@Int, @Int -> @Bool)", "@Int.1 > @Int.0",
        ens="@Bool.result == (@Int.1 > @Int.0)"),
    "private data Box {\n  MkBox(Int)\n}\n",
))

#: The call, by the type of its value, in its two spellings.
_SPELLINGS: dict[str, tuple[str, str]] = {
    "X": ("sub2(@Int.0, 3)", "@Int.0 |> sub2(3)"),
    "B": ("gt(@Int.0, 3)", "@Int.0 |> gt(3)"),
    "A": ("array_reverse([@Int.0, 3])", "[@Int.0, 3] |> array_reverse()"),
    "N": ("abs(@Int.0)", "@Int.0 |> abs()"),
    # No slot is in scope in a data invariant.
    "C": ("gt(4, 3)", "4 |> gt(3)"),
}

_STATE_INT = ("get(@Unit) -> { resume(@Int.0) },\n"
              "    put(@Int) -> { resume(()) }")


class Position(NamedTuple):
    label: str
    grammar: frozenset[str]
    fields: frozenset[tuple[str, str]]
    #: `f`'s body; `{X}`, `{B}`, `{A}`, `{N}` and `{C}` stand for the call.
    body: str
    #: What `f(10)` returns.
    value: int
    contracts: tuple[str, str] = ("true", "true")
    decreases: str | None = None
    extra: str = ""
    module: str | None = None


def _g(*names: str) -> frozenset[str]:
    return frozenset(names)


def _af(*fields: tuple[str, str]) -> frozenset[tuple[str, str]]:
    return frozenset(fields)


_MA = ("module ma;\n\n"
       + _fn("sub2(@Int, @Int -> @Int)", "@Int.1 - @Int.0", vis="public")
       + "\n" + _fn("echo(@Int -> @Int)", "@Int.0", vis="public"))

POSITIONS: tuple[Position, ...] = (
    Position("function return", _g("block_contents"),
             _af(("Block", "expr"), ("FnDecl", "body")), "{X}", 7),
    Position("let binding", _g("let_stmt"), _af(("LetStmt", "value")),
             "let @Int = {X};\n  @Int.0", 7),
    Position("expression statement", _g("expr_stmt"),
             _af(("ExprStmt", "expr")), "{X};\n  {X}", 7),
    Position("tuple component", _g("let_destruct", "constructor_call"),
             _af(("LetDestruct", "value"), ("ConstructorCall", "args")),
             "let Tuple<@Int, @Int> = Tuple(1, {X});\n  @Int.0", 7),
    Position("if branch", _g("if_expr"),
             _af(("IfExpr", "then_branch"), ("IfExpr", "else_branch")),
             "if @Int.0 > 0 then { {X} } else { {X} }", 7),
    Position("if condition", _g("if_expr"), _af(("IfExpr", "condition")),
             "if {B} then { 1 } else { 2 }", 1),
    Position("match scrutinee", _g("match_expr"),
             _af(("MatchExpr", "scrutinee")),
             "match {X} {\n    @Int -> @Int.0\n  }", 7),
    Position("match arm", _g("match_arm"), _af(("MatchArm", "body")),
             "match @Int.0 {\n    0 -> 0,\n    @Int -> {X}\n  }", 7),
    Position("call argument", _g("func_call"), _af(("FnCall", "args")),
             "sub2({X}, 1)", 6),
    Position("constructor argument", _g("constructor_call"),
             _af(("ConstructorCall", "args")),
             "match Some({X}) {\n    Some(@Int) -> @Int.0,\n"
             "    None -> 0\n  }", 7),
    Position("user constructor field", _g("constructor_call"),
             _af(("ConstructorCall", "args")),
             "match MkBox({X}) {\n    MkBox(@Int) -> @Int.0\n  }", 7),
    Position("module-qualified call argument", _g("module_call"),
             _af(("ModuleCall", "args")), "ma::echo({X})", 7, module=_MA),
    Position("qualified call argument", _g("qualified_call", "handle_expr"),
             _af(("QualifiedCall", "args"), ("HandleExpr", "body")),
             "handle[State<Int>](@Int = 0) {\n    " + _STATE_INT
             + "\n  } in {\n    State.put({X});\n    State.get(())\n  }", 7),
    Position("handler state", _g("handler_state"),
             _af(("HandlerState", "init_expr")),
             "handle[State<Int>](@Int = {X}) {\n    " + _STATE_INT
             + "\n  } in {\n    get(())\n  }", 7),
    Position("handler with-clause", _g("with_clause"),
             _af(("HandlerClause", "state_update")),
             "handle[State<Int>](@Int = 0) {\n"
             "    get(@Unit) -> { resume(@Int.0) },\n"
             "    put(@Int) -> { resume(()) } with @Int = {X}\n"
             "  } in {\n    put(@Int.0);\n    get(())\n  }", -3),
    Position("handler clause body", _g("handler_clause"),
             _af(("HandlerClause", "body")),
             "handle[Exn<Int>] {\n    throw(@Int) -> {X}\n  } in {\n"
             "    throw(@Int.0)\n  }", 7),
    Position("array element", _g("array_literal"),
             _af(("ArrayLit", "elements")),
             "let @Array<Int> = [{X}, 1];\n  @Array<Int>.0[0]", 7),
    Position("block tail", _g("block_contents"), _af(("Block", "expr")),
             "sub2({\n    {X}\n  }, 0)", 7),
    Position("parenthesised", _g("paren_expr"), frozenset(), "({X})", 7),
    Position("pipe operand", _g("pipe"), frozenset(), "{X} |> sub2(1)", 6),
    # An operator's operand: `|>` binds loosest, so the pipe is written in
    # parentheses there, as the formatter prints it (`TestFormatting`), and
    # the direct spelling carries the same parentheses, which the parser
    # drops.
    Position("equality", _g("eq_op"),
             _af(("BinaryExpr", "left"), ("BinaryExpr", "right")),
             "if ({X}) == 7 then { 1 } else { 2 }", 1),
    Position("inequality", _g("neq_op"), frozenset(),
             "if 7 != ({X}) then { 1 } else { 2 }", 2),
    *(Position(f"ordering {op}", _g(label), frozenset(),
               f"if ({{X}}) {op} 7 then {{ 1 }} else {{ 2 }}", value)
      for label, op, value in (("lt_op", "<", 2), ("gt_op", ">", 2),
                               ("le_op", "<=", 1), ("ge_op", ">=", 1))),
    *(Position(f"arithmetic {op}", _g(label), frozenset(),
               f"({{X}}) {op} 2", value)
      for label, op, value in (("add_op", "+", 9), ("sub_op", "-", 5),
                               ("mul_op", "*", 14), ("div_op", "/", 3),
                               ("mod_op", "%", 1))),
    Position("conjunction", _g("and_op"), frozenset(),
             "if ({B}) && true then { 1 } else { 2 }", 1),
    Position("disjunction", _g("or_op"), frozenset(),
             "if false || ({B}) then { 1 } else { 2 }", 1),
    Position("implication", _g("implies"), frozenset(),
             "if ({B}) ==> false then { 1 } else { 2 }", 2),
    Position("logical not", _g("not_op"), _af(("UnaryExpr", "operand")),
             "if !({B}) then { 1 } else { 2 }", 2),
    Position("negation", _g("neg_op"), _af(("UnaryExpr", "operand")),
             "-({X})", -7),
    Position("index collection", _g("index_op"),
             _af(("IndexExpr", "collection")), "({A})[0]", 3),
    # The array is bound first: indexing an array literal directly is
    # dropped at compile whatever the index is (#1564).
    Position("index position", _g("index_op"), _af(("IndexExpr", "index")),
             "let @Array<Int> = [0, 1, 2, 3, 4, 5, 6, 7];\n"
             "  @Array<Int>.0[{X}]", 7),
    Position("interpolation segment", frozenset(),
             _af(("InterpolatedString", "parts")),
             'string_length("\\({X})")', 1),
    Position("anonymous function body", frozenset(), _af(("AnonFn", "body")),
             "array_map([@Int.0], fn(@Int -> @Int) effects(pure) "
             "{ {X} })[0]", 7),
    Position("assert", _g("assert_expr"), _af(("AssertExpr", "expr")),
             "assert({B});\n  1", 1),
    Position("assume", _g("assume_expr"), _af(("AssumeExpr", "expr")),
             "assume({B});\n  1", 1),
    Position("requires clause", _g("requires_clause"),
             _af(("Requires", "expr")), "1", 1, contracts=("{B}", "true")),
    Position("ensures clause", _g("ensures_clause"),
             _af(("Ensures", "expr")), "sub2(@Int.0, 3)", 7,
             contracts=("true", "@Int.result == ({X})")),
    Position("decreases clause", _g("decreases_clause"),
             _af(("Decreases", "exprs")), "1", 1, decreases="{N}"),
    Position("forall domain", _g("forall_expr"),
             _af(("ForallExpr", "domain"), ("ForallExpr", "predicate")),
             "1", 1, contracts=(
                 "forall(@Nat, {N}, fn(@Nat -> @Bool) effects(pure) "
                 "{ @Nat.0 >= 0 })", "true")),
    Position("exists domain", _g("exists_expr"),
             _af(("ExistsExpr", "domain"), ("ExistsExpr", "predicate")),
             "1", 1, contracts=(
                 "exists(@Nat, {N}, fn(@Nat -> @Bool) effects(pure) "
                 "{ @Nat.0 == 0 })", "true")),
    Position("data invariant", _g("invariant_clause"),
             _af(("DataDecl", "invariant"), ("Invariant", "expr")),
             "match MkHeld(@Int.0) {\n    MkHeld(@Int) -> @Int.0\n  }", 10,
             contracts=("@Int.0 > 3", "true"),
             extra="private data Held invariant({C}) {\n  MkHeld(Int)\n}\n"),
    Position("refinement predicate", _g("refinement_type"),
             _af(("RefinementType", "predicate")),
             "let @Big = @Int.0;\n  @Big.0", 10,
             contracts=("@Int.0 > 3", "true"),
             extra="type Big = { @Int | {B} };\n"),
)


def _fill(text: str, spelling: int) -> str:
    for key, pair in _SPELLINGS.items():
        text = text.replace("{" + key + "}", pair[spelling])
    return text


def _position_files(cell: Position, spelling: int) -> dict[str, str]:
    req, ens = (_fill(c, spelling) for c in cell.contracts)
    dec = _fill(cell.decreases, spelling) if cell.decreases else None
    main = _fn("f(@Int -> @Int)", _fill(cell.body, spelling), vis="public",
               req=req, ens=ens, dec=dec)
    head = "import ma(echo);\n\n" if cell.module else ""
    files = {"main.vera": head + "\n".join(
        (_CALLEES, _fill(cell.extra, spelling), main))}
    if cell.module:
        files["ma.vera"] = cell.module
    return files


_DATA = re.compile(r'^\s*\(data \(i32\.const (\d+)\) "((?:[^"\\]|\\.)*)"\)$',
                   re.M)
_LAYOUT = re.compile(r"(\(global \$(?:heap_ptr|gc_sp|gc_stack_base|"
                     r"gc_stack_limit|gc_heap_start|gc_worklist_end|"
                     r"gc_wrap_base|gc_wrap_ptr|gc_wrap_end)\b[^\n]*"
                     r"\(i32\.const )\d+\)")
_ESCAPES = {"n": 10, "t": 9, "r": 13, '"': 34, "'": 39, "\\": 92}


def _wat_string_length(text: str) -> int:
    """The byte length of a WAT string literal's contents."""
    length, i = 0, 0
    while i < len(text):
        if text[i] != "\\":
            length += len(text[i].encode("utf-8"))
            i += 1
        else:
            length += 1
            i += 2 if text[i + 1] in _ESCAPES else 3
    return length


def _messages(wat: str) -> tuple[str, list[str]]:
    """*wat* with its data segments' layout taken out, and the segments.

    A contract, an assertion or a refinement guard quotes the expression it
    checks, so two spellings of one call give modules that differ in those
    strings, and in where everything after them is laid out.  The code is
    compared with each string's offset and length named rather than
    numbered, and the strings separately (:func:`_unquoted`)."""
    segments = [(int(off), text) for off, text in _DATA.findall(wat)]
    normal = _LAYOUT.sub(lambda m: m.group(1) + "layout)",
                         _DATA.sub("(data)", wat))
    for k, (off, text) in enumerate(segments):
        pair = re.compile(rf"i32\.const {off}\n(\s*)i32\.const "
                          rf"{_wat_string_length(text)}\n")
        normal = pair.sub(lambda m, k=k: (f"i32.const <data {k}>\n"
                                          f"{m.group(1)}i32.const "
                                          f"<length {k}>\n"), normal)
    return normal, [text for _off, text in segments]


def _unquoted(messages: list[str], spellings: list[tuple[str, str]],
              ) -> list[str]:
    """*messages* with each spelling of the call named rather than written,
    and the parentheses around it dropped: a quoted pipe is parenthesised
    where its context needs it, and its direct spelling is not."""
    out = []
    for text in messages:
        for direct, piped in spellings:
            text = text.replace(piped, "<call>").replace(direct, "<call>")
        while "(<call>)" in text:
            text = text.replace("(<call>)", "<call>")
        out.append(text)
    return out


def _agree(tmp_path: Path, direct_files: dict[str, str],
           piped_files: dict[str, str], fn: str, args: list[int | float],
           value: object,
           spellings: list[tuple[str, str]] | None = None) -> None:
    """The premise on the direct spelling, then agreement in every phase.

    The two modules are one module, but for a message that quotes the call
    as it is written."""
    direct = _build(tmp_path / "direct", direct_files)
    assert not [c for c, s in direct.check + direct.verify if s == "error"], (
        direct.describe())
    assert fn in direct.result.exports and direct.valid, direct.describe()
    expected = _value(direct, fn, args)
    assert expected == ("ok", value), expected
    piped = _build(tmp_path / "piped", piped_files)
    assert Counter(piped.check) == Counter(direct.check)
    assert Counter(piped.verify) == Counter(direct.verify)
    assert Counter(piped.obligations) == Counter(direct.obligations)
    assert piped.codegen == direct.codegen, piped.describe()
    direct_code, direct_text = _messages(direct.wat)
    piped_code, piped_text = _messages(piped.wat)
    assert piped_code == direct_code
    named = list(_SPELLINGS.values()) if spellings is None else spellings
    assert _unquoted(piped_text, named) == _unquoted(direct_text, named)
    assert _value(piped, fn, args) == expected


class TestEveryPosition:
    """A call in every expression position, written directly and piped."""

    def test_every_expression_position_has_a_cell(self) -> None:
        """Both enumerations, the grammar's alternatives and the AST's
        expression-bearing fields, are claimed by a cell."""
        grammar = grammar_expression_positions()
        claimed = frozenset().union(*(c.grammar for c in POSITIONS))
        assert not grammar - claimed, sorted(grammar - claimed)
        assert not claimed - grammar, sorted(claimed - grammar)
        fields = {f for f in ast_expression_fields()
                  if not f[0].startswith("_")}
        claimed_fields = frozenset().union(*(c.fields for c in POSITIONS))
        assert not fields - claimed_fields, sorted(fields - claimed_fields)
        assert not claimed_fields - fields, sorted(claimed_fields - fields)

    @pytest.mark.parametrize("cell", POSITIONS, ids=lambda c: c.label)
    def test_the_pipe_agrees_with_the_call(self, cell: Position,
                                           tmp_path: Path) -> None:
        _agree(tmp_path, _position_files(cell, 0), _position_files(cell, 1),
               "f", [10], cell.value)


# =====================================================================
# Every call form, every kind of callee
# =====================================================================


class Form(NamedTuple):
    label: str
    #: The direct and the piped spelling of an `@Int`-valued call.
    direct: str
    piped: str
    #: Its value for `@Int.0` = 10.
    value: int
    extra: str = ""
    module: str | None = None


_HANDLED = ("handle[State<Int>](@Int = 0) {\n    " + _STATE_INT
            + "\n  } in {\n    {S};\n    get(())\n  }")

_HELPER = ("where {\n  fn helper(@Int -> @Int)\n    requires(true)\n"
           "    ensures(true)\n    effects(pure)\n  {\n    @Int.0 + 1\n  }\n}\n")

FORMS: tuple[Form, ...] = (
    Form("user function", "sub2(@Int.0, 3)", "@Int.0 |> sub2(3)", 7),
    Form("one-argument function", "neg(@Int.0)", "@Int.0 |> neg()", -10,
         extra=_fn("neg(@Int -> @Int)", "0 - @Int.0")),
    Form("generic function", "id(@Int.0)", "@Int.0 |> id()", 10, extra=_ID),
    Form("where helper", "helper(@Int.0)", "@Int.0 |> helper()", 11),
    Form("built-in", "array_length([@Int.0, 1, 2])",
         "[@Int.0, 1, 2] |> array_length()", 3),
    Form("built-in with a declared domain", 'string_char_code("abc", 1)',
         '"abc" |> string_char_code(1)', 98),
    Form("float conversion", "float_to_int(int_to_float(@Int.0))",
         "@Int.0 |> int_to_float() |> float_to_int()", 10),
    Form("float rendering", "string_length(show(int_to_float(@Int.0)))",
         "@Int.0 |> int_to_float() |> show() |> string_length()", 4),
    Form("generic built-in", "option_unwrap_or(Some(@Int.0), 0)",
         "Some(@Int.0) |> option_unwrap_or(0)", 10),
    Form("a nat-valued callee widened", "nat_to_int(abs(@Int.0))",
         "@Int.0 |> abs() |> nat_to_int()", 10),
    Form("prelude constructor", "option_unwrap_or(Some(@Int.0), 0)",
         "option_unwrap_or(@Int.0 |> Some(), 0)", 10),
    Form("user constructor", "unbox(MkBox(@Int.0))",
         "@Int.0 |> MkBox() |> unbox()", 10,
         extra=_fn("unbox(@Box -> @Int)",
                   "match @Box.0 {\n    MkBox(@Int) -> @Int.0\n  }")),
    Form("tuple constructor", "first(Tuple(@Int.0, 3))",
         "@Int.0 |> Tuple(3) |> first()", 10,
         extra=_fn("first(@Tuple<Int, Int> -> @Int)",
                   "match @Tuple<Int, Int>.0 {\n"
                   "    Tuple(@Int, @Int) -> @Int.1\n  }")),
    Form("apply_fn",
         "apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }, @Int.0)",
         "fn(@Int -> @Int) effects(pure) { @Int.0 + 1 } |> apply_fn(@Int.0)",
         11),
    Form("ability operation", "string_length(show(@Int.0))",
         "@Int.0 |> show() |> string_length()", 2),
    Form("comparison ability",
         "match compare(@Int.0, 3) {\n    Less -> 1,\n    Equal -> 2,\n"
         "    Greater -> 3\n  }",
         "match @Int.0 |> compare(3) {\n    Less -> 1,\n    Equal -> 2,\n"
         "    Greater -> 3\n  }", 3),
    Form("bare effect operation", _HANDLED.replace("{S}", "put(@Int.0)"),
         _HANDLED.replace("{S}", "@Int.0 |> put()"), 10),
    Form("qualified effect operation",
         _HANDLED.replace("{S}", "State.put(@Int.0)"),
         _HANDLED.replace("{S}", "@Int.0 |> State.put()"), 10),
    Form("module call", "ma::sub2(@Int.0, 3)", "@Int.0 |> ma::sub2(3)", 7,
         module=_MA),
)


def _form_files(form: Form, position: str, spelling: int) -> dict[str, str]:
    call = form.piped if spelling else form.direct
    body = {"tail": call,
            "let": f"let @Int = {call};\n  @Int.0",
            "if arm": f"if @Int.0 > 0 then {{ {call} }} else {{ 0 }}",
            }[position]
    main = _fn("f(@Int -> @Int)", body, vis="public")
    if form.label == "where helper":
        main += _HELPER
    head = "import ma(sub2);\n\n" if form.module else ""
    files = {"main.vera": head + "\n".join((_CALLEES, form.extra, main))}
    if form.module:
        files["ma.vera"] = form.module
    return files


class TestEveryCallForm:
    """Every call form a pipe can name, and every kind of callee."""

    def test_every_call_form_has_a_cell(self) -> None:
        """The grammar's `fn_call` alternatives with an argument list are
        the call forms; `nullary_constructor_expr` has none, and a pipe
        into it is E040 (`TestARightOperandThatIsNoCall`)."""
        forms = {type(c).__name__ for f in FORMS
                 for c in _calls(parse_to_ast(_form_files(f, "tail", 1)[
                     "main.vera"])) if c.piped}
        assert forms == {"FnCall", "ConstructorCall", "QualifiedCall",
                         "ModuleCall"}

    @pytest.mark.parametrize("position", ("tail", "let", "if arm"))
    @pytest.mark.parametrize("form", FORMS, ids=lambda f: f.label)
    def test_the_pipe_agrees_with_the_call(self, form: Form, position: str,
                                           tmp_path: Path) -> None:
        _agree(tmp_path, _form_files(form, position, 0),
               _form_files(form, position, 1), "f", [10], form.value,
               [(form.direct, form.piped)])

    def test_a_pipe_into_the_modules_own_path(self, tmp_path: Path) -> None:
        """Inside `module ma`, a pipe into `ma::sub2` is the call by the
        module's own path (#1558), which is the bare call."""
        def files(call: str) -> dict[str, str]:
            ma = _MA.replace(
                _fn("echo(@Int -> @Int)", "@Int.0", vis="public"),
                _fn("echo(@Int -> @Int)", call, vis="public"))
            return {"ma.vera": ma, "main.vera": (
                "import ma(echo);\n\n"
                + _fn("f(@Int -> @Int)", "ma::echo(@Int.0)", vis="public"))}
        _agree(tmp_path, files("ma::sub2(@Int.0, 3)"),
               files("@Int.0 |> ma::sub2(3)"), "f", [10], 7)

    def test_a_piped_print(self, tmp_path: Path) -> None:
        """A qualified `IO` operation prints what its direct spelling does."""
        def files(call: str) -> dict[str, str]:
            return {"main.vera": _fn("main(@Unit -> @Unit)", call,
                                     vis="public", eff="<IO>")}
        direct = _build(tmp_path / "d", files('IO.print("piped")'))
        piped = _build(tmp_path / "p", files('"piped" |> IO.print()'))
        assert piped.check == direct.check == []
        assert piped.wat == direct.wat
        assert execute(piped.result, fn_name="main").stdout == "piped"


# =====================================================================
# The transform: the call, its span, its flag
# =====================================================================

_CALLS = (ast.FnCall, ast.ConstructorCall, ast.QualifiedCall, ast.ModuleCall)


def _calls(node: object) -> list[ast.Expr]:
    """Every call under *node*, in walk order."""
    out: list[ast.Expr] = []

    def walk(value: object) -> None:
        if isinstance(value, tuple):
            for v in value:
                walk(v)
            return
        if not isinstance(value, ast.Node):
            return
        if isinstance(value, _CALLS):
            out.append(value)
        for f in dataclasses.fields(value):
            if f.name != "span":
                walk(getattr(value, f.name))

    walk(node)
    return out


def _body(source: str) -> ast.Expr:
    program = parse_to_ast(source)
    decl = program.declarations[-1].decl
    assert isinstance(decl, ast.FnDecl)
    return decl.body.expr


def _piped_call(expr_text: str) -> ast.Expr:
    """The body expression of a function whose body is *expr_text*."""
    return _body(_fn("f(@Int -> @Int)", expr_text, vis="public"))


class TestTheTransform:
    """`a |> f(b)` is parsed as the call `f(a, b)`, flagged `piped`."""

    @pytest.mark.parametrize("text,cls,first", (
        ("@Int.0 |> sub2(3)", ast.FnCall, ast.SlotRef),
        ("@Int.0 |> Some()", ast.ConstructorCall, ast.SlotRef),
        ("@Int.0 |> State.put()", ast.QualifiedCall, ast.SlotRef),
        ("@Int.0 |> ma::sub2(3)", ast.ModuleCall, ast.SlotRef),
        ("1 |> sub2(2) |> sub2(3)", ast.FnCall, ast.FnCall),
    ))
    def test_the_pipe_is_the_call(self, text: str, cls: type,
                                  first: type) -> None:
        call = _piped_call(text)
        assert type(call) is cls
        assert isinstance(call, _CALLS) and call.piped
        assert isinstance(call.args[0], first)

    def test_the_piped_value_is_the_first_argument(self) -> None:
        """The flag and the span are presentation: the two spellings are
        one call, equal as nodes."""
        piped, direct = _piped_call("1 |> sub2(2)"), _piped_call("sub2(1, 2)")
        assert piped == direct
        assert isinstance(piped, ast.FnCall) and piped.piped
        assert isinstance(direct, ast.FnCall) and not direct.piped

    def test_the_call_carries_the_pipes_span(self) -> None:
        """Diagnostics point at the pipe: the call's span is the whole
        `a |> f(b)`, from the piped value to the closing parenthesis."""
        source = _fn("f(@Int -> @Int)", "@Int.0 |> sub2(3)", vis="public")
        call = _body(source)
        line = source.splitlines().index("  @Int.0 |> sub2(3)") + 1
        assert call.span is not None
        assert (call.span.line, call.span.column) == (line, 3)
        assert (call.span.end_line, call.span.end_column) == (line, 20)

    def test_no_binary_operator_is_a_pipe(self) -> None:
        """The operator enum has no pipe, so no `BinaryExpr` is a call."""
        assert "|>" not in {op.value for op in ast.BinOp}

    def test_the_spelling_is_shown_only_where_it_is_set(self) -> None:
        """`vera ast` and `vera ast --json` show `piped` on a piped call and
        nowhere else, so every other node serialises as it always did."""
        piped, direct = _piped_call("1 |> sub2(2)"), _piped_call("sub2(1, 2)")
        assert piped.to_dict()["piped"] is True
        assert "piped" not in direct.to_dict()
        assert "piped: True" in piped.pretty()
        assert "piped" not in direct.pretty()

    def test_a_message_quotes_the_pipe_as_written(self) -> None:
        """`ast.format_expr`, which runtime messages and obligation texts
        quote, prints a piped call as the pipe."""
        for text in ("@Int.0 |> sub2(3)", "@Int.0 |> Some()",
                     "@Int.0 |> State.put()", "@Int.0 |> ma::sub2(3)",
                     "1 |> sub2(2) |> sub2(3)"):
            assert ast.format_expr(_piped_call(text)) == text

    def test_a_diagnostic_on_a_piped_call_points_at_the_pipe(self) -> None:
        source = _with(_CALLEES, main=_fn(
            "f(@Int -> @Int)", "@Int.0 |> sub2()", vis="public"))
        errors = [d for d in _check(source) if d.severity == "error"]
        assert [d.error_code for d in errors] == ["E201"]
        line = source.splitlines().index("  @Int.0 |> sub2()") + 1
        assert (errors[0].location.line, errors[0].location.column) == (
            line, 3)


class TestOneTypeForBothSpellings:
    """The spelling flag takes no part in equality, so a predicate written
    with a pipe and the same predicate written as the call are one type, and
    one `State` cell: a cell is named after its type's structural rendering,
    which prints the call (`TestFormatting`)."""

    def test_one_state_cell(self, tmp_path: Path) -> None:
        """`bump` writes `State<Large>`, the handler holds `State<Big>`, and
        the two aliases name one refinement: the write reaches the cell
        `get` reads (on `main` the checker refused the call, E125; with the
        cell named after the spelling, the run returned the initial 5)."""
        source = _with(
            _CALLEES,
            "type Big = { @Int | @Int.0 |> gt(3) };\n",
            "type Large = { @Int | gt(@Int.0, 3) };\n",
            _fn("bump(@Large -> @Unit)", "put(@Large.0)",
                eff="<State<Large>>"),
            main=_fn("f(@Int -> @Int)",
                     "handle[State<Big>](@Big = 5) {\n"
                     "    get(@Unit) -> { resume(@Big.0) },\n"
                     "    put(@Big) -> { resume(()) } with @Big = @Big.0\n"
                     "  } in {\n    bump(@Int.0);\n    get(())\n  }",
                     vis="public", req="@Int.0 > 3"))
        built = _single(tmp_path, source)
        assert built.valid, built.describe()
        assert _value(built, "f", [10]) == ("ok", 10)


# =====================================================================
# A right operand that is no call
# =====================================================================


class TestARightOperandThatIsNoCall:
    """`a |> b` where `b` is not a call has no argument list for `a` to
    join: E040 at the transform, at the right operand.  On `main` the
    checker typed such a pipe as its right operand and discarded the left
    one, and code generation failed with an internal error (E699)."""

    @pytest.mark.parametrize("rhs", (
        "4", "@Int.1", "{ sub2(1, 2) }", "sub2(1, 2) + 1", "-sub2(1, 2)",
        "None", "(1 |> sub2(2))", "[sub2(1, 2)][0]",
        "if true then { 1 } else { 2 }",
    ))
    def test_e040(self, rhs: str) -> None:
        source = _with(_CALLEES, main=_fn(
            "f(@Int, @Int -> @Int)", f"@Int.0 |> {rhs}", vis="public"))
        with pytest.raises(TransformError) as info:
            parse_to_ast(source)
        diagnostic = info.value.diagnostic
        assert diagnostic.error_code == "E040"
        assert diagnostic.rationale and diagnostic.fix and diagnostic.spec_ref
        line = next(i for i, text in enumerate(source.splitlines(), 1)
                    if "|>" in text)
        # At the right operand: where its node begins, which for a block or
        # a parenthesised operand is inside the delimiters the parser drops.
        start = source.splitlines()[line - 1].index("|>") + 4
        assert diagnostic.location.line == line
        assert start <= diagnostic.location.column < start + len(rhs)

    def test_e040_in_a_string_interpolation(self) -> None:
        """Inside `\\(...)` the segment is parsed on its own, and the
        diagnostic is moved back to where the right operand is written."""
        source = _fn("f(@Int -> @String)", '"x\\(@Int.0 |> 2)"',
                     vis="public")
        with pytest.raises(TransformError) as info:
            parse_to_ast(source)
        location = info.value.diagnostic.location
        line = next(i for i, text in enumerate(source.splitlines(), 1)
                    if "|>" in text)
        column = source.splitlines()[line - 1].index("|> 2") + 4
        assert (location.line, location.column) == (line, column)

    def test_a_parenthesised_call_is_a_call(self) -> None:
        """Parentheses are grouping: `a |> (f(b))` is `a |> f(b)`."""
        assert _piped_call("1 |> (sub2(2))") == _piped_call("sub2(1, 2)")


# =====================================================================
# Formatting
# =====================================================================


class TestFormatting:
    """`vera fmt` prints a piped call as the pipe, parenthesised exactly
    where the pipe binds looser than its context."""

    @pytest.mark.parametrize("text", (
        "@Int.0 |> sub2(3)",
        "1 |> sub2(2) |> sub2(3)",
        "sub2(1 |> sub2(2), 3)",
        "(@Int.0 |> sub2(3)) + 1",
        "1 + (@Int.0 |> sub2(3))",
        "-(@Int.0 |> sub2(3))",
        "([@Int.0] |> array_reverse())[0]",
        "@Int.0 + 1 |> sub2(3)",
        "let @Bool = !(@Int.0 |> gt(3));\n  1",
        "let @Bool = (@Int.0 |> gt(3)) == true;\n  1",
        "let @Bool = @Int.0 > 3 ==> true |> both(true);\n  1",
        "option_unwrap_or(@Int.0 |> Some(), 0)",
        "@Int.0 |> Tuple(3) |> first()",
        "@Int.0 |> ma::sub2(3)",
        '"x" |> IO.print()',
        'string_length("\\(@Int.0 |> sub2(3))")',
    ))
    def test_a_piped_call_is_a_fixed_point(self, text: str) -> None:
        source = _fn("f(@Int -> @Int)", text, vis="public")
        assert format_source(source) == source

    def test_the_structural_rendering_does_not_see_the_spelling(
            self) -> None:
        """A `State` cell is named after its type's structural rendering
        (`structural_type_key`), and a predicate's two spellings are one
        type, the flag taking no part in equality, so they render alike
        there; `vera fmt` still prints the pipe."""
        from vera.formatter import format_expr_canonical
        from vera.types import INT, RefinedType, structural_type_key

        piped = _piped_call("(@Int.0 |> gt(3)) == true")
        direct = _piped_call("gt(@Int.0, 3) == true")
        assert RefinedType(INT, piped) == RefinedType(INT, direct)
        assert (structural_type_key(RefinedType(INT, piped))
                == structural_type_key(RefinedType(INT, direct)))
        assert format_expr_canonical(piped) == "(@Int.0 |> gt(3)) == true"

    @pytest.mark.parametrize("written,canonical", (
        ("(@Int.0 |> sub2(3))", "@Int.0 |> sub2(3)"),
        ("@Int.0 |> (sub2(3))", "@Int.0 |> sub2(3)"),
        ("(1 |> sub2(2)) |> sub2(3)", "1 |> sub2(2) |> sub2(3)"),
    ))
    def test_parentheses_the_parser_drops_are_not_kept(
            self, written: str, canonical: str) -> None:
        source = _fn("f(@Int -> @Int)", written, vis="public")
        assert format_source(source) == _fn("f(@Int -> @Int)", canonical,
                                             vis="public")


# =====================================================================
# The generator: every call in the corpus, piped
# =====================================================================


def _pipe_every_call(node: object) -> tuple[object, int]:
    """*node* with every call that has an argument flagged `piped`, and how
    many were flagged."""
    count = 0

    def walk(value: object) -> object:
        nonlocal count
        if isinstance(value, tuple):
            return tuple(walk(v) for v in value)
        if not isinstance(value, ast.Node):
            return value
        changes = {f.name: walk(getattr(value, f.name))
                   for f in dataclasses.fields(value)
                   if f.init and f.name not in ("span", "piped")}
        if isinstance(value, _CALLS) and value.args and not value.piped:
            changes["piped"] = True
            count += 1
        return dataclasses.replace(value, **changes)

    return walk(node), count


def _corpus() -> list[Path]:
    return sorted(p for root in ("examples", "tests/conformance")
                  for p in (ROOT / root).rglob("*.vera"))


class TestTheCorpusPipesEveryCall:
    """Every call with an argument in the corpus, written as a pipe, is the
    same program: it formats as a pipe, parses back to the same AST with
    the same calls flagged, and is canonical."""

    @pytest.mark.parametrize(
        "path", _corpus(), ids=lambda p: p.relative_to(ROOT).as_posix())
    def test_the_piped_spelling_is_the_same_program(self, path: Path) -> None:
        source = path.read_text(encoding="utf-8")
        try:
            program = parse_to_ast(source)
        except Exception:  # noqa: BLE001 - a negative fixture's refusal
            pytest.skip("the program does not parse")
        piped, count = _pipe_every_call(program)
        if not count:
            pytest.skip("no call with an argument")
        formatter = Formatter(_attach_comments(extract_comments(source),
                                               piped),  # type: ignore[arg-type]
                              blank_source_lines(source))
        text = formatter.format_program(piped)  # type: ignore[arg-type]
        assert text.count("|>") >= count
        reparsed = parse_to_ast(text)
        assert reparsed == program
        assert [c.piped for c in _calls(reparsed)] == [
            c.piped for c in _calls(piped)]
        assert format_source(text) == text
