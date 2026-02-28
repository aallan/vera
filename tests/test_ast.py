"""Tests for the Vera AST layer (vera.ast + vera.transform).

Tests are organised in four groups:
  1. Round-trip tests — every example file parses and transforms to AST
  2. Node-specific tests — each AST node type constructed correctly
  3. Span / serialisation tests — source locations and JSON/pretty output
  4. Error tests — unhandled rules raise TransformError
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from vera.ast import (
    AnonFn,
    ArrayLit,
    AssertExpr,
    AssumeExpr,
    BinaryExpr,
    BinOp,
    BindingPattern,
    Block,
    BoolLit,
    BoolPattern,
    Constructor,
    ConstructorCall,
    ConstructorPattern,
    DataDecl,
    Decreases,
    EffectDecl,
    EffectRef,
    EffectSet,
    Ensures,
    ExistsExpr,
    ExprStmt,
    FloatLit,
    FnCall,
    FnDecl,
    FnType,
    ForallExpr,
    HandleExpr,
    HandlerClause,
    HandlerState,
    IfExpr,
    ImportDecl,
    IndexExpr,
    IntLit,
    IntPattern,
    Invariant,
    LetDestruct,
    LetStmt,
    MatchArm,
    MatchExpr,
    ModuleCall,
    ModuleDecl,
    NamedType,
    NullaryConstructor,
    NullaryPattern,
    OldExpr,
    NewExpr,
    OpDecl,
    Program,
    PureEffect,
    QualifiedCall,
    QualifiedEffectRef,
    RefinementType,
    Requires,
    ResultRef,
    SlotRef,
    Span,
    StringLit,
    StringPattern,
    TopLevelDecl,
    TypeAliasDecl,
    UnaryExpr,
    UnaryOp,
    UnitLit,
    WildcardPattern,
)
from vera.ast import format_expr
from vera.errors import TransformError, VeraError
from vera.parser import parse, parse_to_ast
from vera.transform import transform

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"


# =====================================================================
# Helper
# =====================================================================

def _ast(source: str) -> Program:
    """Parse source and return AST."""
    return parse_to_ast(source)


def _first_fn(source: str) -> FnDecl:
    """Parse source, return the first FnDecl."""
    prog = _ast(source)
    return prog.declarations[0].decl


def _body_expr(source: str):
    """Parse source, return the body expression of the first function."""
    fn = _first_fn(source)
    return fn.body.expr


# =====================================================================
# 1. Round-trip tests — all example files
# =====================================================================

EXAMPLE_FILES = sorted(f.name for f in EXAMPLES_DIR.glob("*.vera"))


@pytest.mark.parametrize("filename", EXAMPLE_FILES)
def test_example_roundtrip(filename):
    """Every example file should parse and transform to a valid AST."""
    tree = parse((EXAMPLES_DIR / filename).read_text(), file=filename)
    ast = transform(tree)
    assert isinstance(ast, Program)
    # Serialisable
    d = ast.to_dict()
    assert d["_type"] == "Program"
    json.dumps(d)  # valid JSON
    # Pretty-printable
    text = ast.pretty()
    assert "Program" in text


# =====================================================================
# 2. Node-specific tests
# =====================================================================

# -- Program structure --

class TestProgramStructure:
    def test_empty_program(self):
        prog = _ast("")
        assert isinstance(prog, Program)
        assert prog.module is None
        assert prog.imports == ()
        assert prog.declarations == ()

    def test_module_decl(self):
        prog = _ast("module my.app.core;")
        assert isinstance(prog.module, ModuleDecl)
        assert prog.module.path == ("my", "app", "core")

    def test_import_with_names(self):
        prog = _ast("import collections.list(List, map);")
        imp = prog.imports[0]
        assert isinstance(imp, ImportDecl)
        assert imp.path == ("collections", "list")
        assert imp.names == ("List", "map")

    def test_import_all(self):
        prog = _ast("import utils.math;")
        imp = prog.imports[0]
        assert imp.names is None

    def test_visibility_public(self):
        src = """
        public fn foo(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        { @Int.0 }
        """
        prog = _ast(src)
        decl = prog.declarations[0]
        assert isinstance(decl, TopLevelDecl)
        assert decl.visibility == "public"

    def test_visibility_private(self):
        src = """
        private fn bar(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        { @Int.0 }
        """
        prog = _ast(src)
        assert prog.declarations[0].visibility == "private"


# -- Function declarations --

class TestFunctions:
    def test_simple_fn(self):
        fn = _first_fn("""
        private fn inc(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        { @Int.0 + 1 }
        """)
        assert fn.name == "inc"
        assert len(fn.params) == 1
        assert isinstance(fn.params[0], NamedType)
        assert fn.params[0].name == "Int"
        assert isinstance(fn.return_type, NamedType)
        assert fn.return_type.name == "Int"
        assert fn.forall_vars is None
        assert fn.where_fns is None

    def test_fn_with_forall(self):
        fn = _first_fn("""
        private forall<T> fn identity(@T -> @T)
          requires(true)
          ensures(true)
          effects(pure)
        { @T.0 }
        """)
        assert fn.forall_vars == ("T",)

    def test_fn_multiple_forall_vars(self):
        fn = _first_fn("""
        private forall<A, B> fn swap(@A, @B -> @B)
          requires(true)
          ensures(true)
          effects(pure)
        { @B.0 }
        """)
        assert fn.forall_vars == ("A", "B")

    def test_fn_with_where(self):
        fn = _first_fn("""
        private fn main(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        { helper(@Int.0) }
        where {
          fn helper(@Int -> @Int)
            requires(true)
            ensures(true)
            effects(pure)
          { @Int.0 + 1 }
        }
        """)
        assert fn.where_fns is not None
        assert len(fn.where_fns) == 1
        assert fn.where_fns[0].name == "helper"

    def test_multiple_contracts(self):
        fn = _first_fn("""
        private fn clamp(@Int -> @Int)
          requires(@Int.0 >= 0)
          requires(@Int.0 <= 100)
          ensures(@Int.result >= 0)
          ensures(@Int.result <= 100)
          effects(pure)
        { @Int.0 }
        """)
        assert len(fn.contracts) == 4
        assert isinstance(fn.contracts[0], Requires)
        assert isinstance(fn.contracts[2], Ensures)

    def test_decreases_clause(self):
        fn = _first_fn("""
        private fn f(@Nat -> @Nat)
          requires(true)
          ensures(true)
          decreases(@Nat.0)
          effects(pure)
        { @Nat.0 }
        """)
        dec = [c for c in fn.contracts if isinstance(c, Decreases)]
        assert len(dec) == 1
        assert len(dec[0].exprs) == 1


# -- Data declarations --

class TestDataDecls:
    def test_simple_adt(self):
        prog = _ast("""
        private data Color { Red, Green, Blue }
        """)
        decl = prog.declarations[0].decl
        assert isinstance(decl, DataDecl)
        assert decl.name == "Color"
        assert len(decl.constructors) == 3
        assert decl.constructors[0].name == "Red"
        assert decl.constructors[0].fields is None

    def test_parameterized_adt(self):
        prog = _ast("""
        private data Option<T> { None, Some(T) }
        """)
        decl = prog.declarations[0].decl
        assert decl.type_params == ("T",)
        assert decl.constructors[0].name == "None"
        assert decl.constructors[0].fields is None
        assert decl.constructors[1].name == "Some"
        assert len(decl.constructors[1].fields) == 1

    def test_adt_with_invariant(self):
        prog = _ast("""
        private data PosInt
          invariant(@Int.0 > 0)
        { MkPosInt(Int) }
        """)
        decl = prog.declarations[0].decl
        assert decl.invariant is not None
        assert isinstance(decl.invariant, BinaryExpr)

    def test_type_alias(self):
        prog = _ast("""
        type Age = Int;
        """)
        decl = prog.declarations[0].decl
        assert isinstance(decl, TypeAliasDecl)
        assert decl.name == "Age"
        assert isinstance(decl.type_expr, NamedType)
        assert decl.type_expr.name == "Int"


# -- Effect declarations --

class TestEffectDecls:
    def test_effect_with_ops(self):
        prog = _ast("""
        effect Counter {
          op get(Unit -> Int);
          op increment(Unit -> Unit);
        }
        """)
        decl = prog.declarations[0].decl
        assert isinstance(decl, EffectDecl)
        assert decl.name == "Counter"
        assert len(decl.operations) == 2
        assert decl.operations[0].name == "get"
        assert decl.operations[1].name == "increment"

    def test_parameterized_effect(self):
        prog = _ast("""
        effect State<T> {
          op get(Unit -> T);
          op put(T -> Unit);
        }
        """)
        decl = prog.declarations[0].decl
        assert decl.type_params == ("T",)


# -- Type expressions --

class TestTypeExprs:
    def test_named_type_simple(self):
        fn = _first_fn("""
        private fn f(@Int -> @Int)
          requires(true) ensures(true) effects(pure)
        { @Int.0 }
        """)
        assert isinstance(fn.params[0], NamedType)
        assert fn.params[0].name == "Int"
        assert fn.params[0].type_args is None

    def test_named_type_with_args(self):
        fn = _first_fn("""
        private fn f(@Option<Int> -> @Bool)
          requires(true) ensures(true) effects(pure)
        { true }
        """)
        assert fn.params[0].name == "Option"
        assert fn.params[0].type_args is not None
        assert fn.params[0].type_args[0].name == "Int"

    def test_fn_type_alias(self):
        prog = _ast("""
        type Mapper = fn(Int -> Int) effects(pure);
        """)
        decl = prog.declarations[0].decl
        assert isinstance(decl.type_expr, FnType)
        assert len(decl.type_expr.params) == 1
        assert isinstance(decl.type_expr.effect, PureEffect)

    def test_refinement_type(self):
        prog = _ast("""
        type PosInt = { @Int | @Int.0 > 0 };
        """)
        decl = prog.declarations[0].decl
        assert isinstance(decl.type_expr, RefinementType)
        assert isinstance(decl.type_expr.base_type, NamedType)
        assert isinstance(decl.type_expr.predicate, BinaryExpr)


# -- Expressions --

class TestExpressions:
    def test_int_lit(self):
        expr = _body_expr("""
        private fn f(@Unit -> @Int) requires(true) ensures(true) effects(pure) { 42 }
        """)
        assert isinstance(expr, IntLit)
        assert expr.value == 42

    def test_float_lit(self):
        expr = _body_expr("""
        private fn f(@Unit -> @Float64)
          requires(true) ensures(true) effects(pure)
        { 3.14 }
        """)
        assert isinstance(expr, FloatLit)
        assert expr.value == 3.14

    def test_string_lit(self):
        expr = _body_expr("""
        private fn f(@Unit -> @String)
          requires(true) ensures(true) effects(pure)
        { "hello" }
        """)
        assert isinstance(expr, StringLit)
        assert expr.value == "hello"

    def test_bool_lit(self):
        expr = _body_expr("""
        private fn f(@Unit -> @Bool) requires(true) ensures(true) effects(pure) { true }
        """)
        assert isinstance(expr, BoolLit)
        assert expr.value is True

    def test_unit_lit(self):
        expr = _body_expr("""
        private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(pure) { () }
        """)
        assert isinstance(expr, UnitLit)

    def test_binary_add(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { @Int.0 + 1 }
        """)
        assert isinstance(expr, BinaryExpr)
        assert expr.op == BinOp.ADD
        assert isinstance(expr.left, SlotRef)
        assert isinstance(expr.right, IntLit)

    def test_binary_implies(self):
        fn = _first_fn("""
        private fn f(@Bool -> @Bool)
          requires(@Bool.0 ==> true)
          ensures(true)
          effects(pure)
        { @Bool.0 }
        """)
        req = fn.contracts[0]
        assert isinstance(req.expr, BinaryExpr)
        assert req.expr.op == BinOp.IMPLIES

    def test_unary_not(self):
        expr = _body_expr("""
        private fn f(@Bool -> @Bool) requires(true) ensures(true) effects(pure)
        { !@Bool.0 }
        """)
        assert isinstance(expr, UnaryExpr)
        assert expr.op == UnaryOp.NOT

    def test_unary_neg(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { -@Int.0 }
        """)
        assert isinstance(expr, UnaryExpr)
        assert expr.op == UnaryOp.NEG

    def test_slot_ref(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { @Int.0 }
        """)
        assert isinstance(expr, SlotRef)
        assert expr.type_name == "Int"
        assert expr.index == 0
        assert expr.type_args is None

    def test_result_ref(self):
        fn = _first_fn("""
        private fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        { @Int.0 }
        """)
        ens = fn.contracts[1]
        assert isinstance(ens.expr.left, ResultRef)
        assert ens.expr.left.type_name == "Int"

    def test_fn_call(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { add(@Int.0, 1) }
        """)
        assert isinstance(expr, FnCall)
        assert expr.name == "add"
        assert len(expr.args) == 2

    def test_constructor_call(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { Some(@Int.0) }
        """)
        assert isinstance(expr, ConstructorCall)
        assert expr.name == "Some"

    def test_nullary_constructor(self):
        expr = _body_expr("""
        private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(pure)
        { None }
        """)
        assert isinstance(expr, NullaryConstructor)
        assert expr.name == "None"

    def test_qualified_call(self):
        expr = _body_expr("""
        private fn f(@Unit -> @Int) requires(true) ensures(true) effects(<Counter>)
        { Counter.get(()) }
        """)
        assert isinstance(expr, QualifiedCall)
        assert expr.qualifier == "Counter"
        assert expr.name == "get"

    def test_if_expr(self):
        expr = _body_expr("""
        private fn f(@Bool -> @Int) requires(true) ensures(true) effects(pure)
        { if @Bool.0 then { 1 } else { 0 } }
        """)
        assert isinstance(expr, IfExpr)
        assert isinstance(expr.then_branch, Block)
        assert isinstance(expr.else_branch, Block)

    def test_match_expr(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { match @Int.0 { 0 -> 1, _ -> 0 } }
        """)
        assert isinstance(expr, MatchExpr)
        assert len(expr.arms) == 2
        assert isinstance(expr.arms[0], MatchArm)
        assert isinstance(expr.arms[0].pattern, IntPattern)
        assert isinstance(expr.arms[1].pattern, WildcardPattern)

    def test_block_with_let(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        {
          let @Int = @Int.0 + 1;
          @Int.1
        }
        """)
        assert isinstance(expr, SlotRef)
        fn = _first_fn("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        {
          let @Int = @Int.0 + 1;
          @Int.1
        }
        """)
        assert len(fn.body.statements) == 1
        assert isinstance(fn.body.statements[0], LetStmt)

    def test_array_literal(self):
        expr = _body_expr("""
        private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(pure)
        { [1, 2, 3] }
        """)
        assert isinstance(expr, ArrayLit)
        assert len(expr.elements) == 3

    def test_index_expr(self):
        expr = _body_expr("""
        private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(pure)
        { [1, 2, 3][0] }
        """)
        assert isinstance(expr, IndexExpr)

    def test_pipe_expr(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { @Int.0 |> inc() }
        """)
        assert isinstance(expr, BinaryExpr)
        assert expr.op == BinOp.PIPE

    def test_anonymous_fn(self):
        prog = _ast("""
        type IntToInt = fn(Int -> Int) effects(pure);
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { apply(fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }) }
        """)
        fn = prog.declarations[1].decl
        call = fn.body.expr
        assert isinstance(call, FnCall)
        assert isinstance(call.args[0], AnonFn)
        anon = call.args[0]
        assert len(anon.params) == 1
        assert isinstance(anon.effect, PureEffect)

    def test_module_call_ast_structure(self):
        """Module-qualified call parses to ModuleCall AST (#95)."""
        prog = _ast("""
        import vera.math;
        private fn f(@Int -> @Int)
          requires(true) ensures(true) effects(pure)
        { vera.math::abs(@Int.0) }
        """)
        fn = prog.declarations[0].decl
        body = fn.body.expr
        assert isinstance(body, ModuleCall)
        assert body.path == ("vera", "math")
        assert body.name == "abs"
        assert len(body.args) == 1

    def test_module_call_single_segment(self):
        """Single-segment module call: math::abs(@Int.0)."""
        prog = _ast("""
        import math;
        private fn f(@Int -> @Int)
          requires(true) ensures(true) effects(pure)
        { math::abs(@Int.0) }
        """)
        fn = prog.declarations[0].decl
        body = fn.body.expr
        assert isinstance(body, ModuleCall)
        assert body.path == ("math",)
        assert body.name == "abs"

    def test_format_expr_module_call(self):
        """format_expr produces :: syntax for ModuleCall."""
        mc = ModuleCall(
            path=("vera", "math"), name="abs",
            args=(IntLit(value=42),),
        )
        assert format_expr(mc) == "vera.math::abs(42)"


# -- Contract expressions --

class TestContractExprs:
    def test_old_new_expr(self):
        fn = _first_fn("""
        private fn f(@Unit -> @Int)
          requires(true)
          ensures(@Int.result == old(State<Int>) && new(State<Int>) == old(State<Int>) + 1)
          effects(<State<Int>>)
        { 0 }
        """)
        ens = fn.contracts[1]
        # old and new are deep in the expression tree
        assert isinstance(ens.expr, BinaryExpr)

    def test_assert_assume(self):
        fn = _first_fn("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        {
          assert(@Int.0 > 0);
          assume(@Int.0 < 100);
          @Int.0
        }
        """)
        stmts = fn.body.statements
        assert isinstance(stmts[0], ExprStmt)
        assert isinstance(stmts[0].expr, AssertExpr)
        assert isinstance(stmts[1], ExprStmt)
        assert isinstance(stmts[1].expr, AssumeExpr)


# -- Quantifiers --

class TestQuantifiers:
    def test_forall_expr(self):
        fn = _first_fn("""
        private fn f(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
        { forall(@Int, 10, fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }) }
        """)
        expr = fn.body.expr
        assert isinstance(expr, ForallExpr)
        assert isinstance(expr.predicate, AnonFn)

    def test_exists_expr(self):
        fn = _first_fn("""
        private fn f(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
        { exists(@Int, 10, fn(@Int -> @Bool) effects(pure) { @Int.0 == 5 }) }
        """)
        expr = fn.body.expr
        assert isinstance(expr, ExistsExpr)


# -- Effect handlers --

class TestHandlers:
    def test_handler_with_state(self):
        src = """
        private fn f(@Unit -> @Int) requires(true) ensures(true) effects(pure)
        {
          handle[Counter] (@Int = 0) {
            get(@Unit) -> { resume(0) },
            increment(@Unit) -> { resume(()) }
          } in {
            Counter.get(())
          }
        }

        effect Counter {
          op get(Unit -> Int);
          op increment(Unit -> Unit);
        }
        """
        fn = _first_fn(src)
        expr = fn.body.expr
        assert isinstance(expr, HandleExpr)
        assert isinstance(expr.state, HandlerState)
        assert len(expr.clauses) == 2
        assert expr.clauses[0].op_name == "get"

    def test_handler_without_state(self):
        src = """
        private fn f(@Unit -> @Int) requires(true) ensures(true) effects(pure)
        {
          handle[Abort] {
            abort(@Unit) -> { 0 }
          } in {
            42
          }
        }

        effect Abort {
          op abort(Unit -> Int);
        }
        """
        fn = _first_fn(src)
        expr = fn.body.expr
        assert isinstance(expr, HandleExpr)
        assert expr.state is None


# -- Patterns --

class TestPatterns:
    def test_constructor_pattern(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { match Some(@Int.0) { Some(@Int) -> @Int.0, None -> 0 } }
        """)
        assert isinstance(expr, MatchExpr)
        arm0 = expr.arms[0]
        assert isinstance(arm0.pattern, ConstructorPattern)
        assert arm0.pattern.name == "Some"
        assert isinstance(arm0.pattern.sub_patterns[0], BindingPattern)

    def test_nullary_pattern(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { match None { None -> 0 } }
        """)
        assert isinstance(expr.arms[0].pattern, NullaryPattern)
        assert expr.arms[0].pattern.name == "None"

    def test_wildcard_pattern(self):
        expr = _body_expr("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { match @Int.0 { _ -> 0 } }
        """)
        assert isinstance(expr.arms[0].pattern, WildcardPattern)

    def test_literal_patterns(self):
        expr = _body_expr("""
        private fn f(@Int -> @Bool) requires(true) ensures(true) effects(pure)
        { match @Int.0 { 0 -> true, 1 -> false, _ -> false } }
        """)
        assert isinstance(expr.arms[0].pattern, IntPattern)
        assert expr.arms[0].pattern.value == 0

    def test_bool_pattern(self):
        expr = _body_expr("""
        private fn f(@Bool -> @Int) requires(true) ensures(true) effects(pure)
        { match @Bool.0 { true -> 1, false -> 0 } }
        """)
        assert isinstance(expr.arms[0].pattern, BoolPattern)
        assert expr.arms[0].pattern.value is True
        assert isinstance(expr.arms[1].pattern, BoolPattern)
        assert expr.arms[1].pattern.value is False


# -- Statements --

class TestStatements:
    def test_let_stmt(self):
        fn = _first_fn("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { let @Int = @Int.0 + 1; @Int.1 }
        """)
        stmt = fn.body.statements[0]
        assert isinstance(stmt, LetStmt)
        assert isinstance(stmt.type_expr, NamedType)
        assert stmt.type_expr.name == "Int"

    def test_let_destruct(self):
        fn = _first_fn("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { let Tuple<@Int, @String> = make_pair(); @Int.1 }
        """)
        stmt = fn.body.statements[0]
        assert isinstance(stmt, LetDestruct)
        assert stmt.constructor == "Tuple"
        assert len(stmt.type_bindings) == 2

    def test_expr_stmt(self):
        fn = _first_fn("""
        private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>)
        { print("hello"); () }
        """)
        stmt = fn.body.statements[0]
        assert isinstance(stmt, ExprStmt)
        assert isinstance(stmt.expr, FnCall)


# -- Effects --

class TestEffects:
    def test_pure_effect(self):
        fn = _first_fn("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { @Int.0 }
        """)
        assert isinstance(fn.effect, PureEffect)

    def test_single_effect(self):
        fn = _first_fn("""
        private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>)
        { () }
        """)
        assert isinstance(fn.effect, EffectSet)
        assert len(fn.effect.effects) == 1
        assert fn.effect.effects[0].name == "IO"

    def test_multiple_effects(self):
        fn = _first_fn("""
        private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO, State<Int>>)
        { () }
        """)
        assert isinstance(fn.effect, EffectSet)
        assert len(fn.effect.effects) == 2

    def test_parameterized_effect(self):
        fn = _first_fn("""
        private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<State<Int>>)
        { () }
        """)
        eff = fn.effect.effects[0]
        assert isinstance(eff, EffectRef)
        assert eff.name == "State"
        assert eff.type_args is not None
        assert eff.type_args[0].name == "Int"


# =====================================================================
# 3. Span and serialisation tests
# =====================================================================

class TestSpans:
    def test_span_populated(self):
        prog = _ast("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 }
        """)
        assert prog.span is not None
        assert isinstance(prog.span, Span)

    def test_span_correct_line(self):
        src = "private fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n  effects(pure)\n{ @Int.0 }"
        prog = _ast(src)
        fn = prog.declarations[0].decl
        assert fn.span is not None
        assert fn.span.line == 1

    def test_nested_spans(self):
        fn = _first_fn("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)
        { @Int.0 + 1 }
        """)
        body_expr = fn.body.expr
        assert body_expr.span is not None
        assert body_expr.left.span is not None


class TestSerialisation:
    def test_to_dict_structure(self):
        prog = _ast("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 }
        """)
        d = prog.to_dict()
        assert d["_type"] == "Program"
        assert "declarations" in d
        assert isinstance(d["declarations"], list)
        assert d["declarations"][0]["_type"] == "TopLevelDecl"

    def test_json_roundtrip(self):
        prog = _ast("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 }
        """)
        d = prog.to_dict()
        j = json.dumps(d)
        d2 = json.loads(j)
        assert d2["_type"] == "Program"
        assert d == d2

    def test_pretty_format(self):
        prog = _ast("""
        private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 }
        """)
        text = prog.pretty()
        assert text.startswith("Program")
        assert "FnDecl" in text
        assert "SlotRef" in text


# =====================================================================
# 4. Error tests
# =====================================================================

class TestErrors:
    def test_transform_error_is_vera_error(self):
        assert issubclass(TransformError, VeraError)

    def test_unhandled_rule_raises(self):
        """Injecting a Tree with an unknown rule name should raise."""
        from lark import Tree
        fake_tree = Tree("start", [Tree("totally_fake_rule", [])])
        with pytest.raises(TransformError, match="Unhandled grammar rule"):
            transform(fake_tree)
