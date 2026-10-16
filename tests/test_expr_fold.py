"""The class instrument for `vera/fold.py`: one traversal, one scope walk.

Every hand-written walker over `Expr` used to choose, class by class, which
fields to descend into, and a walker that forgot one was silent: the missing
case fell through to its default and the enclosing pass produced wrong output
(#588, #604, #559, #648, and the `#597` gate that only checked the comments).
`vera/fold.py` derives the children of a node from its dataclass fields, so a
new node class is traversed by construction, and its scope walk derives the
binders in scope from `vera/binders.py`'s `BINDER_FIELDS`.  This file holds
both to the AST:

(a) **Completeness.**  For every node class `vera/ast.py` declares (read by
    reflection, never listed here), a node built with every field populated
    yields every expression-bearing child exactly once, in the documented
    order, and nothing from a type, a pattern or an effect.
(b) **Scope.**  For every binder position `BINDER_FIELDS` declares, a
    reference inside the position's extent resolves to that binder through
    the walk, a reference outside it does not, and where two binders of one
    type are in scope `.0` is the most recent.
(c) **Dispatch.**  A `fold.dispatch` table names every `Expr` class or
    refuses to be built, so a new subclass fails at the import of every
    module that builds a `fold.dispatch` table.
(d) **Context.**  `fold.contexts` visits as `walk` does, hands each child
    the context its step gives, asks for a child's context only once the
    previous child's subtree has been visited, and refuses a step that
    leaves a child out, adds one or reorders them.

The two run-level cells at the end are the shapes the free-variable port
changed: a destructuring `let` in a closure (refused at 313c04db, the
function dropped with "unsupported expressions" and `main` with E620), and a
closure whose `handle` captures different new types in its body and in its
state (its capture layout order moved; the run output is the same).
"""

from __future__ import annotations

import ast as pyast
import dataclasses
import inspect
import re
import subprocess
import sys
import types
import typing
from collections.abc import Callable
from pathlib import Path

import pytest
import z3

from tests import pipeline
from vera import ast, binders, fold
from vera.checker import sql
from vera.codegen import compilability
from vera.codegen.core import CodeGenerator
from vera.environment import TypeEnv
from vera.smt import SlotEnv, SmtContext
from vera.wasm.context import WasmContext
from vera.wasm.helpers import CellNames, StringPool

pytestmark = pytest.mark.matrix(decides=["vera/fold.py", "vera/binders.py"])

ROOT = Path(__file__).resolve().parent.parent


# =====================================================================
# Building a node with every field populated
# =====================================================================

class _Builder:
    """Builds nodes field by field and records what the fold must yield.

    Each expression-bearing value placed in a field is recorded as an
    expected child of the node being built; each type, pattern and effect
    carries a POISON expression the fold must never reach.  The record is
    made as the value is built, so the expectation does not restate the
    fold's own rule for which fields it enters."""

    def __init__(self) -> None:
        self._next = 0
        self._in_decl = False
        self.poison: list[ast.Expr] = []

    def marker(self) -> ast.IntLit:
        self._next += 1
        return ast.IntLit(value=self._next)

    def poisoned_expr(self) -> ast.Expr:
        bad = ast.IntLit(value=-1 - len(self.poison))
        self.poison.append(bad)
        return bad

    def poisoned_type(self) -> ast.TypeExpr:
        return ast.RefinementType(
            base_type=ast.NamedType(name="Int", type_args=None),
            predicate=self.poisoned_expr())

    def poisoned_effect(self) -> ast.EffectRefNode:
        return ast.EffectRef(name="State", type_args=(self.poisoned_type(),))

    def value(self, annotation: object, expected: list[ast.Node]) -> object:
        """A value for a field annotated *annotation*, appending to
        *expected* the children the fold must yield from it."""
        origin = typing.get_origin(annotation)
        args = typing.get_args(annotation)
        if origin in _UNIONS:
            # `X | None` and `str | Expr`: build the non-None alternative,
            # preferring a node so the field is exercised.
            options = [a for a in args if a is not type(None)]
            nodes = [a for a in options
                     if inspect.isclass(a) and issubclass(a, ast.Node)]
            return self.value((nodes or options)[0], expected)
        if origin is tuple:
            if len(args) == 2 and args[1] is Ellipsis:
                item = args[0]
                if (typing.get_origin(item) in _UNIONS
                        and ast.Expr in typing.get_args(item)):
                    # `tuple[str | Expr, ...]`: interpolation parts.
                    first, second = self.marker(), self.marker()
                    expected.extend((first, second))
                    return ("a", first, "b", second, "c")
                return tuple(self.value(item, expected) for _ in range(2))
            # `tuple[TypeExpr, Expr]`: a state update.
            return tuple(self.value(a, expected) for a in args)
        if annotation is str:
            return "x"
        if annotation is int:
            return 1
        if annotation is float:
            return 1.5
        if annotation is bool:
            return True
        if annotation is ast.BinOp:
            return ast.BinOp.SUB
        if annotation is ast.UnaryOp:
            return ast.UnaryOp.NEG
        if annotation is ast.Span:
            return ast.Span(1, 1, 1, 2)
        if inspect.isclass(annotation) and issubclass(annotation, ast.Node):
            node = self.node(annotation)
            if not isinstance(node, _NOT_ENTERED):
                expected.append(node)
            return node
        raise AssertionError(
            f"no value for a field annotated {annotation!r}: teach the "
            "builder this annotation, or the class it belongs to goes untested")

    def node(self, cls: type[ast.Node]) -> ast.Node:
        """An instance of *cls*, or of a concrete class standing for it."""
        concrete = _STAND_INS.get(cls, cls)
        if concrete is ast.TypeExpr or issubclass(concrete, ast.TypeExpr):
            return self.poisoned_type()
        if concrete is ast.EffectRefNode or issubclass(concrete, ast.EffectRefNode):
            return self.poisoned_effect()
        if concrete is ast.EffectRow:
            return ast.EffectSet(effects=(self.poisoned_effect(),))
        if concrete is ast.Pattern:
            return ast.BindingPattern(type_expr=self.poisoned_type())
        if concrete is ast.Expr:
            return self.marker()
        if concrete is ast.Decl or concrete is ast.FnDecl:
            if self._in_decl:
                # A declaration nested in one being built: one level is
                # enough to show the fold does not enter it.
                return ast.FnDecl(
                    name="g", forall_vars=None, forall_constraints=None,
                    params=(), return_type=self.poisoned_type(), contracts=(),
                    effect=ast.PureEffect(),
                    body=ast.Block(statements=(), expr=self.poisoned_expr()),
                    where_fns=None)
            self._in_decl = True
            try:
                return self.built(ast.FnDecl)[0]
            finally:
                self._in_decl = False
        if concrete is ast.Stmt:
            return self.built(ast.ExprStmt)[0]
        if concrete is ast.Contract:
            return self.built(ast.Requires)[0]
        return self.built(concrete)[0]

    def built(self, cls: type[ast.Node]) -> tuple[ast.Node, dict[str, list[ast.Node]]]:
        """*cls* with every field populated, and the children each field
        must yield, by field name."""
        hints = typing.get_type_hints(cls, vars(ast))
        values: dict[str, object] = {}
        per_field: dict[str, list[ast.Node]] = {}
        for fld in dataclasses.fields(cls):
            if fld.name == "span":
                continue
            expected: list[ast.Node] = []
            values[fld.name] = self.value(hints[fld.name], expected)
            per_field[fld.name] = expected
        return cls(**values), per_field


#: The abstract field types a builder stands a concrete class in for.
_STAND_INS: dict[type, type] = {}

#: The kinds the fold promises never to enter as children, stated here and
#: not read from `fold.OPAQUE`, so a fold that enters one cannot also move
#: the expectation.
_NOT_ENTERED: tuple[type[ast.Node], ...] = (
    ast.TypeExpr, ast.Pattern, ast.EffectRow, ast.EffectRefNode, ast.Decl,
)

_UNIONS = (typing.Union, types.UnionType)


def _node_classes() -> list[type[ast.Node]]:
    """Every concrete node class `vera/ast.py` declares, by reflection."""
    abstract = {ast.Node, ast.Expr, ast.TypeExpr, ast.Pattern, ast.Stmt,
                ast.Decl, ast.Contract, ast.EffectRow, ast.EffectRefNode}
    return sorted(
        (obj for obj in vars(ast).values()
         if inspect.isclass(obj) and issubclass(obj, ast.Node)
         and obj.__module__ == ast.__name__ and obj not in abstract),
        key=lambda c: c.__name__)


def _documented_order(cls: type[ast.Node]) -> list[str]:
    """Declaration order, unless the order table names the class."""
    if cls in fold.ORDER:
        return list(fold.ORDER[cls].fields)
    return [f.name for f in dataclasses.fields(cls) if f.name != "span"]


def _reached(root: ast.Node) -> list[int]:
    """The ids of every node `fold.walk` yields under *root*."""
    return [id(n) for n in fold.walk(root)]


# =====================================================================
# (a) Completeness by construction
# =====================================================================

def test_expr_classes_are_every_expr_subclass_vera_ast_declares() -> None:
    reflected = {c for c in _node_classes() if issubclass(c, ast.Expr)}
    assert fold.EXPR_CLASSES == reflected
    assert len(fold.EXPR_CLASSES) == 29


def test_the_order_table_is_the_documented_one() -> None:
    """One exception to declaration order, and it is evaluation order."""
    assert set(fold.ORDER) == {ast.HandleExpr}
    assert fold.ORDER[ast.HandleExpr].fields == (
        "effect", "state", "body", "clauses")
    for cls, order in fold.ORDER.items():
        assert order.why, cls
        declared = [f.name for f in dataclasses.fields(cls) if f.name != "span"]
        assert sorted(order.fields) == sorted(declared), cls


@pytest.mark.parametrize("cls", _node_classes(), ids=lambda c: c.__name__)
def test_every_child_is_yielded_once_in_order(cls: type[ast.Node]) -> None:
    builder = _Builder()
    node, per_field = builder.built(cls)
    expected = [kid for name in _documented_order(cls)
                for kid in per_field.get(name, [])]
    got = fold.children(node)
    assert [id(c) for c in got] == [id(c) for c in expected], (
        f"{cls.__name__}: children {[type(c).__name__ for c in got]} "
        f"!= {[type(c).__name__ for c in expected]}")
    reached = _reached(node)
    assert reached[0] == id(node)
    assert len(reached) == len(set(reached)), "a node was yielded twice"
    for kid in expected:
        assert id(kid) in reached, f"{type(kid).__name__} unreached"
    for bad in builder.poison:
        assert id(bad) not in reached, (
            f"{cls.__name__}: the fold entered a type, pattern or effect")
    entered = [type(n).__name__ for n in fold.walk(node)
               if n is not node and isinstance(n, _NOT_ENTERED)]
    assert not entered, f"{cls.__name__}: the fold entered {entered}"


def test_the_kinds_the_fold_does_not_enter_are_the_documented_ones() -> None:
    assert set(fold.OPAQUE) == set(_NOT_ENTERED)


def test_walk_is_pre_order_and_survives_depth() -> None:
    """An explicit stack: a chain far deeper than Python's recursion limit
    is walked, node before child (the #1208 depth rule)."""
    depth = sys.getrecursionlimit() * 3
    expr: ast.Expr = ast.IntLit(value=0)
    for _ in range(depth):
        expr = ast.UnaryExpr(op=ast.UnaryOp.NEG, operand=expr)
    seen = list(fold.walk(expr))
    assert len(seen) == depth + 1
    assert seen[0] is expr and isinstance(seen[-1], ast.IntLit)
    assert fold.fold(expr, lambda n, kids: 1 + sum(kids)) == depth + 1


def test_fold_hands_each_node_its_childrens_results_in_order() -> None:
    tree = ast.BinaryExpr(
        op=ast.BinOp.SUB,
        left=ast.IntLit(value=7),
        right=ast.Block(statements=(
            ast.LetStmt(type_expr=ast.NamedType(name="Int", type_args=None),
                        value=ast.IntLit(value=2)),),
            expr=ast.IntLit(value=3)))

    def spell(node: ast.Node, kids: tuple[str, ...]) -> str:
        own = str(node.value) if isinstance(node, ast.IntLit) else type(node).__name__
        return f"{own}({','.join(kids)})" if kids else own

    assert fold.fold(tree, spell) == "BinaryExpr(7,Block(LetStmt(2),3))"


def test_walk_does_not_enter_a_nested_declaration() -> None:
    """A `where` helper is its own root: the parent's walk stops at it."""
    builder = _Builder()
    fn, per_field = builder.built(ast.FnDecl)
    assert not per_field["where_fns"]
    assert all(not isinstance(n, ast.FnDecl) or n is fn for n in fold.walk(fn))


# =====================================================================
# (b) Scope: every binder position BINDER_FIELDS declares
# =====================================================================

def _ty(name: str) -> ast.NamedType:
    return ast.NamedType(name=name, type_args=None)


def _ref(name: str, index: int) -> ast.SlotRef:
    return ast.SlotRef(type_name=name, type_args=None, index=index)


def _namer(te: ast.TypeExpr) -> str | None:
    return te.name if isinstance(te, ast.NamedType) else None


def _block(*exprs: ast.Expr) -> ast.Block:
    """A block that evaluates every expression, the last as its value."""
    return ast.Block(statements=tuple(ast.ExprStmt(expr=e) for e in exprs[:-1]),
                     expr=exprs[-1])


def _fn(params: tuple[ast.TypeExpr, ...], body: ast.Block, *,
        contracts: tuple[ast.Contract, ...] = (),
        ret: ast.TypeExpr | None = None,
        where: tuple[ast.FnDecl, ...] | None = None) -> ast.FnDecl:
    return ast.FnDecl(
        name="f", forall_vars=None, forall_constraints=None, params=params,
        return_type=ret or _ty("Unit"), contracts=contracts,
        effect=ast.PureEffect(), body=body, where_fns=where)


def _anon(params: tuple[ast.TypeExpr, ...], body: ast.Block,
          ret: ast.TypeExpr | None = None) -> ast.AnonFn:
    return ast.AnonFn(params=params, return_type=ret or _ty("Unit"),
                      effect=ast.PureEffect(), body=body)


def _resolutions(root: ast.Node,
                 scope: fold.Scope | None = None) -> dict[int, fold.Binder | None]:
    """Every slot reference the scope walk reaches, by id, with its binder."""
    out: dict[int, fold.Binder | None] = {}
    for node, sc in fold.scoped(root, _namer, scope or fold.EMPTY_SCOPE):
        if isinstance(node, ast.SlotRef):
            out[id(node)] = sc.resolve(node.type_name, node.index)
    return out


class _Cell(typing.NamedTuple):
    """One position's program: what resolves where.

    *bound* pairs a reference with the (owner, field, index) it must reach;
    *unbound* are references inside the program that must reach no binder."""

    root: ast.Node
    bound: tuple[tuple[ast.SlotRef, ast.Node, str, int], ...]
    unbound: tuple[ast.SlotRef, ...]


def _cell_fn_params() -> _Cell:
    in_contract, in_body, in_helper = _ref("T", 0), _ref("T", 0), _ref("T", 0)
    sibling = _ref("T", 1)
    helper = _fn((), _block(in_helper))
    fn = _fn((_ty("T"), _ty("T")), _block(sibling, in_body),
             contracts=(ast.Requires(expr=in_contract),), where=(helper,))
    return _Cell(fn, ((in_contract, fn, "params", 1), (in_body, fn, "params", 1),
                      (sibling, fn, "params", 0)), ())


def _cell_fn_return() -> _Cell:
    ref = _ref("T", 0)
    return _Cell(_fn((), _block(ref), ret=_ty("T")), (), (ref,))


def _cell_anon_params() -> _Cell:
    inner, sibling, outside = _ref("T", 0), _ref("T", 1), _ref("T", 0)
    anon = _anon((_ty("T"), _ty("T")), _block(sibling, inner))
    return _Cell(_block(anon, outside),
                 ((inner, anon, "params", 1), (sibling, anon, "params", 0)),
                 (outside,))


def _cell_anon_return() -> _Cell:
    ref = _ref("T", 0)
    return _Cell(_anon((), _block(ref), ret=_ty("T")), (), (ref,))


def _cell_let() -> _Cell:
    own, after, older, outside = _ref("T", 0), _ref("T", 0), _ref("T", 1), _ref("T", 0)
    first = ast.LetStmt(type_expr=_ty("T"), value=ast.IntLit(value=1))
    second = ast.LetStmt(type_expr=_ty("T"), value=own)
    inner = ast.Block(statements=(first, second), expr=_block(older, after))
    root = ast.IfExpr(condition=ast.BoolLit(value=True), then_branch=inner,
                      else_branch=_block(outside))
    # `own` is the second let's value: it sees the first let, not itself.
    return _Cell(root, ((own, first, "type_expr", 0), (after, second, "type_expr", 0),
                        (older, first, "type_expr", 0)), (outside,))


def _cell_destructure() -> _Cell:
    own = _ref("T", 0)
    t0, t1, u0 = _ref("T", 0), _ref("T", 1), _ref("U", 0)
    let = ast.LetDestruct(constructor="Tuple",
                          type_bindings=(_ty("T"), _ty("U"), _ty("T")), value=own)
    root = ast.Block(statements=(let,), expr=_block(t1, u0, t0))
    # What the checker binds (`_check_let_destruct`): each component in
    # order, so the LAST `T` component is `@T.0`.
    return _Cell(root, ((t0, let, "type_bindings", 2), (t1, let, "type_bindings", 0),
                        (u0, let, "type_bindings", 1)), (own,))


def _match(*arms: ast.MatchArm, scrutinee: ast.Expr | None = None) -> ast.MatchExpr:
    return ast.MatchExpr(scrutinee=scrutinee or ast.IntLit(value=0), arms=arms)


def _cell_arm() -> _Cell:
    body, scrut, other = _ref("T", 0), _ref("T", 0), _ref("T", 0)
    binder = ast.BindingPattern(type_expr=_ty("T"))
    root = _match(ast.MatchArm(pattern=binder, body=body),
                  ast.MatchArm(pattern=ast.WildcardPattern(), body=other),
                  scrutinee=scrut)
    return _Cell(root, ((body, binder, "type_expr", 0),), (scrut, other))


def _cell_sub_patterns() -> _Cell:
    first = ast.BindingPattern(type_expr=_ty("T"))
    middle = ast.BindingPattern(type_expr=_ty("U"))
    nested = ast.BindingPattern(type_expr=_ty("T"))
    pattern = ast.ConstructorPattern(name="C", sub_patterns=(
        first, middle, ast.ConstructorPattern(name="D", sub_patterns=(nested,))))
    t0, t1, u0 = _ref("T", 0), _ref("T", 1), _ref("U", 0)
    root = _match(ast.MatchArm(pattern=pattern, body=_block(t1, u0, t0)))
    # Depth first, left to right: the nested `T` is the most recent.
    return _Cell(root, ((t0, nested, "type_expr", 0), (t1, first, "type_expr", 0),
                        (u0, middle, "type_expr", 0)), ())


def _cell_binding_pattern() -> _Cell:
    ref = _ref("T", 0)
    binder = ast.BindingPattern(type_expr=_ty("T"))
    return _Cell(_match(ast.MatchArm(pattern=binder, body=ref)),
                 ((ref, binder, "type_expr", 0),), ())


def _handle(state: ast.HandlerState | None, *clauses: ast.HandlerClause,
            body: ast.Block) -> ast.HandleExpr:
    return ast.HandleExpr(effect=ast.EffectRef(name="State", type_args=None),
                          state=state, clauses=clauses, body=body)


def _cell_clause_params() -> _Cell:
    in_clause, sibling, in_body = _ref("T", 0), _ref("T", 1), _ref("T", 0)
    clause = ast.HandlerClause(op_name="op", params=(_ty("T"), _ty("T")),
                               body=_block(sibling, in_clause))
    root = _handle(None, clause, body=_block(in_body))
    return _Cell(root, ((in_clause, clause, "params", 1),
                        (sibling, clause, "params", 0)), (in_body,))


def _cell_state_update() -> _Cell:
    update = _ref("T", 0)
    clause = ast.HandlerClause(op_name="put", params=(), body=ast.UnitLit(),
                               state_update=(_ty("T"), update))
    state = ast.HandlerState(type_expr=_ty("U"), init_expr=ast.IntLit(value=0))
    return _Cell(_handle(state, clause, body=_block(ast.UnitLit())), (), (update,))


def _cell_handler_state() -> _Cell:
    in_clause, param, in_update = _ref("T", 0), _ref("T", 1), _ref("T", 0)
    in_init, in_body = _ref("T", 0), _ref("T", 0)
    clause = ast.HandlerClause(op_name="op", params=(_ty("T"),),
                               body=_block(param, in_clause),
                               state_update=(_ty("T"), in_update))
    state = ast.HandlerState(type_expr=_ty("T"), init_expr=in_init)
    root = _handle(state, clause, body=_block(in_body))
    # The state is bound after the clause's parameters (`_check_handle`), so
    # it is the clause's `.0`; neither its initialiser nor the handled body
    # sees it (spec §7.5.1).
    return _Cell(root, ((in_clause, state, "type_expr", 0), (param, clause, "params", 0),
                        (in_update, state, "type_expr", 0)), (in_init, in_body))


def _cell_constructor_fields() -> _Cell:
    invariant = _ref("T", 0)
    data = ast.DataDecl(name="D", type_params=None, invariant=invariant,
                        constructors=(ast.Constructor(name="C", fields=(_ty("T"),)),))
    return _Cell(data, (), (invariant,))


def _cell_op_decl() -> _Cell:
    return _Cell(ast.OpDecl(name="op", param_types=(_ty("T"),), return_type=_ty("T")),
                 (), ())


def _quantifier(cls: type[ast.ForallExpr] | type[ast.ExistsExpr]) -> _Cell:
    in_pred, in_domain = _ref("T", 0), _ref("T", 0)
    pred = _anon((_ty("T"),), _block(in_pred), ret=_ty("Bool"))
    root = cls(binding_type=_ty("T"), domain=in_domain, predicate=pred)
    # The predicate closure's own parameter binds the slot; the declared
    # binding type opens no scope of its own.
    return _Cell(root, ((in_pred, pred, "params", 0),), (in_domain,))


_CELLS: dict[tuple[type[ast.Node], str], Callable[[], _Cell]] = {
    (ast.FnDecl, "params"): _cell_fn_params,
    (ast.FnDecl, "return_type"): _cell_fn_return,
    (ast.AnonFn, "params"): _cell_anon_params,
    (ast.AnonFn, "return_type"): _cell_anon_return,
    (ast.LetStmt, "type_expr"): _cell_let,
    (ast.LetDestruct, "type_bindings"): _cell_destructure,
    (ast.MatchArm, "pattern"): _cell_arm,
    (ast.ConstructorPattern, "sub_patterns"): _cell_sub_patterns,
    (ast.BindingPattern, "type_expr"): _cell_binding_pattern,
    (ast.HandlerClause, "params"): _cell_clause_params,
    (ast.HandlerClause, "state_update"): _cell_state_update,
    (ast.HandlerState, "type_expr"): _cell_handler_state,
    (ast.Constructor, "fields"): _cell_constructor_fields,
    (ast.OpDecl, "param_types"): _cell_op_decl,
    (ast.OpDecl, "return_type"): _cell_op_decl,
    (ast.ForallExpr, "binding_type"): lambda: _quantifier(ast.ForallExpr),
    (ast.ExistsExpr, "binding_type"): lambda: _quantifier(ast.ExistsExpr),
}


def _positions() -> list[tuple[type[ast.Node], str]]:
    return [(cls, b.field) for cls, bs in binders.BINDER_FIELDS.items() for b in bs]


def test_every_binder_position_has_an_extent_and_a_cell() -> None:
    """The extent table and the cells are keyed by `BINDER_FIELDS` exactly:
    a position added to `vera/binders.py` without an extent fails here."""
    assert set(fold.EXTENTS) == set(_positions())
    assert set(_CELLS) == set(_positions())
    for key, extent in fold.EXTENTS.items():
        assert extent.why, key


@pytest.mark.parametrize("position", _positions(),
                         ids=lambda p: f"{p[0].__name__}.{p[1]}")
def test_a_reference_resolves_to_its_binder_inside_the_extent_only(
        position: tuple[type[ast.Node], str]) -> None:
    cell = _CELLS[position]()
    resolved = _resolutions(cell.root)
    for ref, owner, field, index in cell.bound:
        got = resolved.get(id(ref), "unreached")
        assert isinstance(got, fold.Binder), (position, ref, got)
        assert got.owner is owner and (got.field, got.index) == (field, index), (
            position, ref, (type(got.owner).__name__, got.field, got.index))
    for ref in cell.unbound:
        assert resolved.get(id(ref), "unreached") is None, (position, ref)


def test_a_none_extent_binds_nothing_where_it_would_be_read() -> None:
    """The positions that open no slot scope say why, and the cells above
    place a reference where the binding would be read."""
    none = {key for key, extent in fold.EXTENTS.items() if extent.kind == "none"}
    assert none == {
        (ast.FnDecl, "return_type"), (ast.AnonFn, "return_type"),
        (ast.HandlerClause, "state_update"), (ast.Constructor, "fields"),
        (ast.OpDecl, "param_types"), (ast.OpDecl, "return_type"),
        (ast.ForallExpr, "binding_type"), (ast.ExistsExpr, "binding_type"),
    }


def test_a_where_helper_is_its_own_root() -> None:
    """A helper cannot reach its parent's parameters (DE_BRUIJN.md): walked
    from the parent it is not entered, walked alone its reference is free."""
    cell = _cell_fn_params()
    assert isinstance(cell.root, ast.FnDecl) and cell.root.where_fns
    helper = cell.root.where_fns[0]
    in_helper = helper.body.expr
    assert id(in_helper) not in _resolutions(cell.root)
    assert _resolutions(helper)[id(in_helper)] is None


def test_scope_counts_and_resolves_de_bruijn() -> None:
    a, b, c = (fold.Binder(owner=ast.UnitLit(), field="params", index=i,
                           type_expr=_ty(n), name=n)
               for i, n in enumerate(("T", "U", "T")))
    scope = fold.EMPTY_SCOPE.push(a, b, c)
    assert scope.resolve("T", 0) is c and scope.resolve("T", 1) is a
    assert scope.resolve("U", 0) is b and scope.resolve("T", 2) is None
    assert scope.count("T") == 2 and scope.count("V") == 0
    assert scope.binders() == (a, b, c)
    assert fold.EMPTY_SCOPE.binders() == ()


# =====================================================================
# (c) Dispatch: a table names every Expr class or is not built
# =====================================================================

def test_dispatch_refuses_a_table_that_misses_a_class() -> None:
    arms = {cls: cls.__name__ for cls in fold.EXPR_CLASSES}
    assert fold.dispatch("ok", arms)[ast.IntLit] == "IntLit"
    del arms[ast.HoleExpr]
    with pytest.raises(TypeError, match="HoleExpr"):
        fold.dispatch("short", arms)
    arms[ast.HoleExpr] = "HoleExpr"
    arms[ast.MatchArm] = "MatchArm"  # type: ignore[index]
    with pytest.raises(TypeError, match="MatchArm"):
        fold.dispatch("long", arms)


#: Every `fold.dispatch` table the compiler builds, by the name it gives.
_TABLES = frozenset({
    "_is_void_expr", "_infer_expr_wasm_type", "_walk_vera_type",
    "_translate_expr_unscoped", "resolve_literal_string", "resolve_array_len",
    "_synth_expr_impl", "translate_expr",
})


def test_a_new_expr_subclass_fails_every_dispatching_module_at_import() -> None:
    """Declare a 30th `Expr` subclass before `vera.fold` is imported: the
    first dispatching module refuses to import, naming it, and every table
    the compiler builds is refused, each by its own name, which is the
    coverage the walker gate checked in comments."""
    script = (
        "import dataclasses, importlib, sys\n"
        "from vera import ast\n"
        "@dataclasses.dataclass(frozen=True)\n"
        "class ZzNewExpr(ast.Expr):\n"
        "    pass\n"
        "ZzNewExpr.__module__ = ast.__name__\n"
        "ast.ZzNewExpr = ZzNewExpr\n"
        "from vera import fold\n"
        "assert ast.ZzNewExpr in fold.EXPR_CLASSES\n"
        "try:\n"
        "    importlib.import_module('vera.checker.sql')\n"
        "except TypeError as exc:\n"
        "    assert 'ZzNewExpr' in str(exc), exc\n"
        "    print('import refused')\n"
        "real = fold.dispatch\n"
        "refused = []\n"
        "def recording(name, arms):\n"
        "    try:\n"
        "        return real(name, arms)\n"
        "    except TypeError as exc:\n"
        "        assert 'ZzNewExpr' in str(exc), exc\n"
        "        refused.append(name)\n"
        "        return arms\n"
        "fold.dispatch = recording\n"
        "for name in sys.argv[1:]:\n"
        "    importlib.import_module(name)\n"
        "print(' '.join(sorted(refused)))\n"
    )
    modules = ["vera.checker.sql", "vera.checker.expressions",
               "vera.wasm.context", "vera.wasm.inference", "vera.smt"]
    out = subprocess.run(
        [sys.executable, "-c", script, *modules], cwd=ROOT, capture_output=True,
        text=True, encoding="utf-8", timeout=120, check=False)
    assert out.returncode == 0, out.stderr
    lines = out.stdout.splitlines()
    assert lines[0] == "import refused", out.stdout
    assert set(lines[1].split()) == _TABLES, out.stdout


# =====================================================================
# (d) The context walk
# =====================================================================

def test_contexts_with_no_step_visits_as_walk_does() -> None:
    """With every step `None`, every node of every class, pre-order, each
    in the root's context."""
    for cls in _node_classes():
        root, _ = _Builder().built(cls)
        pairs = list(fold.contexts(root, lambda node, ctx: None, "root"))
        assert [id(node) for node, _ in pairs] == _reached(root), cls.__name__
        assert {ctx for _, ctx in pairs} == {"root"}, cls.__name__


def _depths(root: ast.Node) -> dict[int, int]:
    out: dict[int, int] = {}

    def visit(node: ast.Node, depth: int) -> None:
        out[id(node)] = depth
        for kid in fold.children(node):
            visit(kid, depth + 1)

    visit(root, 0)
    return out


def test_contexts_hands_each_child_the_context_its_step_gives() -> None:
    for cls in _node_classes():
        root, _ = _Builder().built(cls)
        pairs = list(fold.contexts(
            root, lambda node, depth: ((kid, depth + 1) for kid in fold.children(node)), 0))
        assert {id(node): depth for node, depth in pairs} == _depths(root), cls.__name__


def test_contexts_refuses_a_step_that_leaves_out_adds_or_reorders_a_child() -> None:
    left, right = ast.IntLit(value=1), ast.IntLit(value=2)
    root = ast.BinaryExpr(op=ast.BinOp.ADD, left=left, right=right)
    copy = ast.IntLit(value=1)
    assert copy == left and copy is not left
    for given in ([(left, 0)], [(right, 0), (left, 0)],
                  [(left, 0), (right, 0), (left, 0)], [(copy, 0), (right, 0)]):
        def step(node: ast.Node, ctx: int,
                 given: list[tuple[ast.Node, int]] = given) -> list[tuple[ast.Node, int]] | None:
            return given if node is root else None
        with pytest.raises(TypeError, match="BinaryExpr"):
            list(fold.contexts(root, step, 0))


def test_contexts_asks_for_a_childs_context_after_the_previous_subtree() -> None:
    """A step runs between its children: what it does to give the `else`
    branch its context happens after the whole `then` branch is visited."""
    log: list[str] = []
    cond = ast.BinaryExpr(op=ast.BinOp.LT, left=_ONE, right=ast.IntLit(value=2))
    root = ast.IfExpr(condition=cond, then_branch=_tail(ast.IntLit(value=3)),
                      else_branch=_tail(ast.IntLit(value=4)))

    def step(node: ast.Node, ctx: str):  # type: ignore[no-untyped-def]
        if node is not root:
            return None
        return if_step()

    def if_step():  # type: ignore[no-untyped-def]
        yield root.condition, "cond"
        log.append("then's context")
        yield root.then_branch, "then"
        log.append("else's context")
        yield root.else_branch, "else"

    for node, ctx in fold.contexts(root, step, "root"):
        log.append(f"{type(node).__name__}@{ctx}")
    assert log == [
        "IfExpr@root", "BinaryExpr@cond", "IntLit@cond", "IntLit@cond",
        "then's context", "Block@then", "IntLit@then",
        "else's context", "Block@else", "IntLit@else",
    ]


# =====================================================================
# Per-node pins for the tables the ports built
# =====================================================================

def _wasm() -> WasmContext:
    return WasmContext(string_pool=StringPool())


def _arm(body: ast.Expr) -> ast.MatchArm:
    return ast.MatchArm(pattern=ast.WildcardPattern(), body=body)


def _tail(expr: ast.Expr) -> ast.Block:
    return ast.Block(statements=(), expr=expr)


_TRUE, _ONE, _HALF = ast.BoolLit(value=True), ast.IntLit(value=1), ast.FloatLit(value=0.5)
_CLOSURE = _anon((), _tail(ast.IntLit(value=1)), ret=_ty("Int"))


def _if(then: ast.Expr, other: ast.Expr) -> ast.IfExpr:
    return ast.IfExpr(condition=_TRUE, then_branch=_tail(then), else_branch=_tail(other))


def _exn_handle(body: ast.Expr) -> ast.HandleExpr:
    return ast.HandleExpr(effect=ast.EffectRef(name="Exn", type_args=(_ty("Int"),)),
                          state=None, clauses=(), body=_tail(body))


def test_the_void_table_answers_each_shape() -> None:
    """`_is_void_expr`: a compound is void when every value position is."""
    ctx = _wasm()
    pins = [
        (ast.UnitLit(), True), (_ONE, False), (ast.AssertExpr(expr=_TRUE), True),
        (ast.QualifiedCall(qualifier="IO", name="print", args=(ast.StringLit(value="x"),)), True),
        (ast.QualifiedCall(qualifier="Http", name="get", args=()), False),
        (_if(ast.UnitLit(), ast.UnitLit()), True), (_if(ast.UnitLit(), _ONE), False),
        (_match(_arm(ast.UnitLit()), _arm(ast.UnitLit())), True),
        (_match(_arm(ast.UnitLit()), _arm(_ONE)), False),
        (_tail(ast.UnitLit()), True), (_exn_handle(ast.UnitLit()), True),
        (_exn_handle(_ONE), False),
    ]
    assert [ctx._is_void_expr(node) for node, _ in pins] == [want for _, want in pins]


def test_the_wat_type_table_answers_each_shape() -> None:
    """`_infer_expr_wasm_type`: the first typed arm or branch of a join."""
    ctx = _wasm()
    pins = [
        (_match(_arm(ast.AssertExpr(expr=_TRUE)), _arm(_HALF)), "f64"),
        (_if(ast.AssertExpr(expr=_TRUE), _HALF), "f64"),
        (ast.BinaryExpr(op=ast.BinOp.ADD, left=_HALF, right=_HALF), "f64"),
        (ast.BinaryExpr(op=ast.BinOp.ADD, left=_ONE, right=_ONE), "i64"),
        (ast.BinaryExpr(op=ast.BinOp.LT, left=_ONE, right=_ONE), "i32"),
        (ast.UnaryExpr(op=ast.UnaryOp.NEG, operand=_HALF), "f64"),
        (ast.UnaryExpr(op=ast.UnaryOp.NOT, operand=_TRUE), "i32"),
        (ast.StringLit(value="x"), "i32_pair"), (ast.UnitLit(), None),
        (_exn_handle(_HALF), "f64"), (_tail(_TRUE), "i32"),
    ]
    assert [ctx._infer_expr_wasm_type(node) for node, _ in pins] == [
        want for _, want in pins]


def test_the_vera_type_table_answers_each_shape() -> None:
    """`_walk_vera_type`: a closure names nothing, so the join reads on."""
    ctx = _wasm()
    pins = [
        (_match(_arm(_CLOSURE), _arm(_ONE)), "Int"),
        (_if(_CLOSURE, _TRUE), "Bool"),
        (ast.BinaryExpr(op=ast.BinOp.EQ, left=_ONE, right=_ONE), "Bool"),
        (ast.BinaryExpr(op=ast.BinOp.ADD, left=_HALF, right=_HALF), "Float64"),
        (ast.UnaryExpr(op=ast.UnaryOp.NEG, operand=_ONE), "Int"),
        (ast.UnaryExpr(op=ast.UnaryOp.NOT, operand=_TRUE), "Bool"),
        (ast.StringLit(value="x"), "String"), (ast.ArrayLit(elements=()), "Array"),
        (_tail(ast.UnitLit()), "Unit"), (_exn_handle(_TRUE), "Bool"),
        (ast.AssertExpr(expr=_TRUE), "Unit"), (_CLOSURE, None),
    ]
    assert [ctx._walk_vera_type(node) for node, _ in pins] == [want for _, want in pins]


def test_the_sql_tables_answer_each_shape() -> None:
    """The literal-provenance and array-length resolvers, slot-free."""
    env = TypeEnv()

    def key(ref: ast.SlotRef) -> str:
        return ref.type_name

    def lit(value: str) -> ast.StringLit:
        return ast.StringLit(value=value)

    strings = [
        (lit("a"), "a"),
        (ast.InterpolatedString(parts=("a", lit("b"), "c")), "abc"),
        (ast.InterpolatedString(parts=("a", _ONE, "c")), None),
        (ast.FnCall(name="string_concat", args=(lit("a"), lit("b"))), "ab"),
        (ast.FnCall(name="string_upper", args=(lit("a"),)), None),
        (_if(lit("a"), lit("a")), None),
    ]
    assert [sql.resolve_literal_string(e, env, key) for e, _ in strings] == [
        want for _, want in strings]
    lengths = [(ast.ArrayLit(elements=(_ONE, _ONE)), 2), (lit("ab"), None)]
    assert [sql.resolve_array_len(e, env, key) for e, _ in lengths] == [
        want for _, want in lengths]


def _smt_term(term: z3.ExprRef | None) -> str | None:
    """A term as text, its fresh constants' counters elided."""
    return None if term is None else re.sub(r"_\d+", "_N", str(term))


def test_the_smt_table_answers_each_shape() -> None:
    """`translate_expr`: each class's term in a bare context, one shape per
    class, and none for the classes a contract never translates."""
    smt = SmtContext()
    smt.set_result_var(z3.Int("r"))
    env = SlotEnv().push("Int", z3.Int("x"))
    two, x0 = ast.IntLit(value=2), ast.SlotRef(type_name="Int", type_args=None, index=0)
    pair = ast.ArrayLit(elements=(_ONE, two))
    state = ast.EffectRef(name="State", type_args=(_ty("Int"),))
    pred = _anon((_ty("Int"),), _tail(_TRUE), ret=_ty("Bool"))
    pins = [
        (_ONE, "1"), (_TRUE, "True"), (ast.StringLit(value="a"), '"a"'),
        (_HALF, "1*(2**-1)"), (x0, "x"), (ast.ResultRef(type_name="Int", type_args=None), "r"),
        (ast.BinaryExpr(op=ast.BinOp.ADD, left=_ONE, right=two), "1 + 2"),
        (ast.UnaryExpr(op=ast.UnaryOp.NEG, operand=_ONE), "-1"),
        (_if(_ONE, two), "If(True, 1, 2)"), (_tail(two), "2"),
        (_match(_arm(two), scrutinee=_ONE), "2"),
        (ast.FnCall(name="abs", args=(x0,)), "If(x >= 0, x, -x)"),
        (pair, "_call_array_lit_N"),
        (ast.IndexExpr(collection=pair, index=_ONE), "index_Array_Int(_call_array_lit_N, 1)"),
        # A bare context registers no module function and no data type.
        (ast.ModuleCall(path=("m",), name="f", args=(_ONE,)), None),
        (ast.ConstructorCall(name="Some", args=(_ONE,)), None),
        (ast.NullaryConstructor(name="None", owner=None), None),
        # An effect operation is no term; its arguments are translated for
        # their preconditions.
        (ast.QualifiedCall(qualifier="IO", name="print", args=(ast.StringLit(value="a"),)), None),
        (ast.UnitLit(), None), (ast.InterpolatedString(parts=("a", _ONE)), None),
        (ast.HoleExpr(), None), (_CLOSURE, None), (_exn_handle(_ONE), None),
        (ast.AssertExpr(expr=_TRUE), None), (ast.AssumeExpr(expr=_TRUE), None),
        (ast.ForallExpr(binding_type=_ty("Int"), domain=_ONE, predicate=pred), None),
        (ast.ExistsExpr(binding_type=_ty("Int"), domain=_ONE, predicate=pred), None),
        (ast.OldExpr(effect_ref=state), None), (ast.NewExpr(effect_ref=state), None),
    ]
    assert {type(node) for node, _ in pins} == fold.EXPR_CLASSES
    assert [_smt_term(smt.translate_expr(node, env)) for node, _ in pins] == [
        want for _, want in pins]


# =====================================================================
# Run-level cells: the shapes the free-variable port changed
# =====================================================================

_DESTRUCTURE_IN_CLOSURE = """\
type IntToInt = fn(Int -> Int) effects(pure);

private fn make(@Int -> @IntToInt)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Int) effects(pure) {
    let Tuple<@Int, @Int> = Tuple(@Int.0, 7);
    @Int.0 + @Int.1 + @Int.3
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = make(100);
  apply_fn(@IntToInt.0, 5)
}
"""


def test_repro_a_destructuring_let_in_a_closure_compiles_and_runs() -> None:
    """At 313c04db the free-variable walk skipped a `LetDestruct`: it never
    read the source and never counted the two bindings, so `@Int.1` and
    `@Int.3` were taken for captures the enclosing scope does not hold, and
    `make` was dropped ("unsupported expressions") and `main` with it
    (E620).  The scope walk reads the destructure as `vera/binders.py` lists
    it: `@Int.0` is 7, `@Int.1` is the argument 5, `@Int.2` the parameter
    and `@Int.3` the captured 100, so the closure returns 112."""
    ran = pipeline.run(_DESTRUCTURE_IN_CLOSURE, "main")
    assert ran.execution.value == 112


_HANDLE_IN_CLOSURE = """\
private fn probe(@Int, @Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = array_map([1, 2], fn(@Int -> @Int) effects(pure) {
    handle[State<Int>](@Int = @Int.1) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      if @Bool.0 then { get(()) + @Int.0 } else { @Int.0 }
    }
  });
  @Array<Int>.0[0] + @Array<Int>.0[1]
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(10, true)
}
"""


def test_a_handle_in_a_closure_captures_in_evaluation_order() -> None:
    """The closure's `handle` captures `@Int` in its state initialiser and
    `@Bool` in its body.  The free-variable walk now meets the initialiser
    first (fold.ORDER), so the closure's environment holds the `Int` before
    the `Bool` where it held them the other way round; the value is the
    same, 11 + 12."""
    ran = pipeline.run(_HANDLE_IN_CLOSURE, "main")
    assert ran.execution.value == 23


def test_an_effect_operation_translates_its_arguments() -> None:
    """`translate_expr`'s effect-operation arm: no term, and every argument
    translated for what its translation records (`#776`): an array
    literal's length and elements reach the solver."""
    smt = SmtContext()
    pair = ast.ArrayLit(elements=(_ONE, ast.IntLit(value=2)))
    op = ast.QualifiedCall(qualifier="IO", name="print", args=(pair,))
    assert smt.translate_expr(op, SlotEnv()) is None
    assert len(smt.solver.assertions()) == 4


# =====================================================================
# Context-walk consumers: where a step's work runs
# =====================================================================

_CONDITION_IN_A_LET = """\
public fn count(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  let @Nat = if @Nat.0 > 0 then { count(@Nat.0 - 1) } else { 0 };
  @Nat.0
}
"""


def test_the_decreases_walk_translates_a_condition_before_its_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The `decreases` walk's steps run where the recursive walk ran them:
    the `if`'s condition is translated when the walk reaches it, inside the
    `let` it is the value of, and only after that subtree does the block's
    step bind the `let`, translating the whole `if`.  A step whose pairs
    were computed before its first child bound the `let` first.  The walk
    records calls and nothing else, so no verdict and no obligation tells
    the two orders apart; the order the solver's facts are built in does,
    and this cell reads it."""
    from vera.verifier import ContractVerifier

    order: list[str] = []
    walking: list[bool] = []
    walk_for_calls = ContractVerifier._walk_for_calls
    translate = SmtContext.translate_expr

    def walk(self, *args, **kwargs):  # type: ignore[no-untyped-def]
        walking.append(True)
        try:
            return walk_for_calls(self, *args, **kwargs)
        finally:
            walking.pop()

    def spy(self, expr, env):  # type: ignore[no-untyped-def]
        if walking:
            order.append(type(expr).__name__)
        return translate(self, expr, env)

    monkeypatch.setattr(ContractVerifier, "_walk_for_calls", walk)
    monkeypatch.setattr(SmtContext, "translate_expr", spy)
    envelope = pipeline.verify(_CONDITION_IN_A_LET).envelope()
    assert envelope["ok"], envelope
    assert "IfExpr" in order, order
    assert order[0] == "BinaryExpr", (
        f"the walk translated {order[0]} first: the `let` was bound before "
        f"the condition inside it was reached ({order})")


def _line_of(source: str, text: str) -> int:
    """The 1-based line of the one occurrence of *text* in *source*."""
    assert source.count(text) == 1, text
    return source[:source.index(text)].count("\n") + 1


_HANDLER_WRITES = """\
private fn g(@Nat -> @Int)
  requires(true)
  ensures(@Int.result == nat_to_int(@Nat.0))
  effects(pure)
{
  nat_to_int(@Nat.0)
}

public fn f(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = g(@Int.0)) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) } with @Nat = g(nat_to_int(@Nat.0) - 1)
  } in {
    put(get(()));
    nat_to_int(get(()))
  }
}
"""


def test_a_handler_s_state_writes_obligate_before_what_they_hold() -> None:
    """The `@Nat`-binding walk's handler step obligates the state's
    initialiser into its cell before the walk reaches the initialiser's own
    sites, and a clause's step obligates its `with` update after the
    clause's body and before the update's own sites, where the recursive
    walk did: a write's record comes before the records of the value it
    writes."""
    envelope = pipeline.verify(_HANDLER_WRITES).envelope()
    assert envelope["ok"], envelope
    binds = [o["description"] for o in envelope["obligations"]
             if o["kind"] == "nat_bind"]
    assert binds == [
        "g(@Int.0)", "@Int.0",
        "g(nat_to_int(@Nat.0) - 1)", "nat_to_int(@Nat.0) - 1"], binds


_DIVERGENT_CELL = """\
private forall<T> fn h(@T, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<T>](@Int = 1) {
    get(@Unit) -> { resume(@T.0) },
    put(@T) -> { resume(()) } with @Int = 0 - 5
  } in {
    @Int.0
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = 3;
  h(@Nat.0, 7)
}
"""


def test_a_with_update_is_obligated_against_its_handler_s_cell() -> None:
    """A clause's `with` update writes its handler's cell, the effect's
    `State<T>` argument, whatever the `with` annotation says (#1203).  A
    generic handler may declare its state at another type than its cell,
    which the checker leaves to the instantiation (#1206): at `Nat` the
    declaration is E533, and the update `0 - 5` is refused into the `Nat`
    cell (E503).  The clause's step cannot see its handler, so the
    handler's step hands it the cell; a clause handed none reads the `Int`
    annotation and obligates nothing."""
    envelope = pipeline.verify(_DIVERGENT_CELL).envelope()
    records = [(o["kind"], o["status"], o.get("error_code"), o["location"]["line"])
               for o in envelope["obligations"]
               if o["kind"] in ("state_decl", "nat_bind")]
    assert ("state_decl", "violated", "E533",
            _line_of(_DIVERGENT_CELL, "(@Int = 1)")) in records, records
    assert ("nat_bind", "violated", "E503",
            _line_of(_DIVERGENT_CELL, "with @Int = 0 - 5")) in records, records


# =====================================================================
# The pre-scans meet a handler's body before its clauses
# =====================================================================
#
# Code generation's two pre-scans, `_scan_io_ops` and
# `_scan_expr_for_handlers`, are `fold.walk`, which meets a handler's state,
# then its body, then its clauses (`fold.ORDER`).  The hand walks met the
# clauses before the body.  What follows the order: the State and Exn
# families a module declares, in the order they are first registered; the
# cell or payload E607 and E612 name, the first unregistrable one the walk
# meets; and the order E618 is reported in, by the derivation the pre-scans
# walk each closure's signature with.  E617 is reported where a closure is
# lowered, which already met the body first.

_EXN_STATE_IN_CLAUSE_AND_BODY = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> {
      handle[State<Bool>](@Bool = true) {
        get(@Unit) -> { resume(@Bool.0) },
        put(@Bool) -> { resume(()) }
      } in {
        if get(()) then { @Int.0 } else { 0 }
      }
    }
  } in {
    handle[State<Nat>](@Nat = 3) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      nat_to_int(get(()))
    }
  }
}
"""

_STATE_IN_CLAUSE_AND_BODY = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 10) {
    get(@Unit) -> {
      let @Bool = handle[State<Bool>](@Bool = true) {
        get(@Unit) -> { resume(@Bool.0) },
        put(@Bool) -> { resume(()) }
      } in {
        get(())
      };
      resume(if @Bool.0 then { @Int.0 } else { 0 })
    },
    put(@Int) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 3) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    };
    get(()) + nat_to_int(@Nat.0)
  }
}
"""


def test_a_handler_declares_its_body_families_before_its_clauses() -> None:
    """A handler whose clause and body each hold a handler of a family
    nothing registered before: the body's family is declared first.  The
    same imports are declared either way; the hand walk declared the
    clause's first.  The first program is check-green and does not load
    (issue #1724), which this cell does not ask; the second runs."""
    for source, families in (
            (_EXN_STATE_IN_CLAUSE_AND_BODY, ["Nat", "Bool"]),
            (_STATE_IN_CLAUSE_AND_BODY, ["Int", "Nat", "Bool"])):
        compiled = pipeline.compile(source)
        assert compiled.ok, [d.description for d in compiled.diagnostics]
        declared = re.findall(r'\(import "vera" "state_get_(\w+)"', compiled.wat)
        assert declared == families, declared
    assert pipeline.run(_STATE_IN_CLAUSE_AND_BODY, "main").execution.value == 13


_UNSUPPORTED_CELLS = """\
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> {
      handle[State<String>](@String = "a") {
        get(@Unit) -> { resume(@String.0) },
        put(@String) -> { resume(()) }
      } in {
        @Int.0
      }
    }
  } in {
    handle[State<Array<Int>>](@Array<Int> = [1]) {
      get(@Unit) -> { resume(@Array<Int>.0) },
      put(@Array<Int>) -> { resume(()) }
    } in {
      3
    }
  }
}
"""

_UNSUPPORTED_PAYLOADS = """\
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> {
      handle[Exn<Unit>] {
        throw(@Unit) -> { 0 }
      } in {
        @Int.0
      }
    }
  } in {
    handle[Exn<Unit>] {
      throw(@Unit) -> { 1 }
    } in {
      3
    }
  }
}
"""


def test_the_unsupported_cell_named_is_the_body_s() -> None:
    """A handler whose clause and body each hold a `State` cell (E607) or
    an `Exn` payload (E612) the backend cannot compile: the diagnostic names
    the body's, the first the walk meets.  Compiled unchecked, as the
    checker refuses both types where they are written (E340); a generic
    clone instantiated at one is how a checked program reaches here."""
    for source, code, body in (
            (_UNSUPPORTED_CELLS, "E607", "handle[State<Array<Int>>]"),
            (_UNSUPPORTED_PAYLOADS, "E612", "handle[Exn<Unit>] {\n      throw(@Unit) -> { 1 }")):
        result = pipeline.compile(source, checked=False).result
        named = [d.location.line for d in result.diagnostics if d.error_code == code]
        assert named == [_line_of(source, body)], (code, named)


_NESTED_BASES = """\
type Pos = { @Int | @Int.0 > 0 };
type Tiny = { @Pos | @Pos.0 < 10 };
type Small = { @Pos | @Pos.0 < 20 };
type TinyFn = fn(Tiny -> Int) effects(pure);
type SmallFn = fn(Small -> Int) effects(pure);

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> {
      let @TinyFn = fn(@Tiny -> @Int) effects(pure) { 1 };
      @Int.0
    }
  } in {
    let @SmallFn = fn(@Small -> @Int) effects(pure) { 2 };
    3
  }
}
"""

_GENERIC_PREDICATES = """\
private forall<T> fn always_true(@T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  true
}

type Checked = { @Int | always_true(@Int.0) };
type Checked2 = { @Int | always_true(@Int.0 + 1) };
type CheckedFn = fn(Checked -> Int) effects(pure);
type Checked2Fn = fn(Checked2 -> Int) effects(pure);

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> {
      let @CheckedFn = fn(@Checked -> @Int) effects(pure) { 1 };
      @Int.0
    }
  } in {
    let @Checked2Fn = fn(@Checked2 -> @Int) effects(pure) { 2 };
    3
  }
}
"""


def test_a_handler_s_body_closures_report_before_its_clauses() -> None:
    """A handler whose clause and body each hold a closure whose signature
    cannot be guarded: the body's closure reports first.  E618 (a
    refinement whose base is another refinement) is reported by the
    signature derivation the pre-scans walk, which met the clause's closure
    first while they were hand walks; E617 (a predicate calling a generic
    function) is reported where the closure is lowered, which met the
    body's first all along.  Compiled unchecked, as the module tests of
    both codes are."""
    for source, code, clause_line, body_line in (
            (_NESTED_BASES, "E618",
             _line_of(_NESTED_BASES, "let @TinyFn"),
             _line_of(_NESTED_BASES, "let @SmallFn")),
            (_GENERIC_PREDICATES, "E617",
             _line_of(_GENERIC_PREDICATES, "type Checked = "),
             _line_of(_GENERIC_PREDICATES, "type Checked2 = "))):
        result = pipeline.compile(source, checked=False).result
        reported = [d.location.line for d in result.diagnostics if d.error_code == code]
        assert reported == [body_line, clause_line], (code, reported)

# =====================================================================
# The pins the walker-coverage gate's test file held (#597, #1210)
# =====================================================================
#
# Moved from `tests/test_walker_defensive_branches_597.py` when the last
# hand walkers ported and the gate retired: the positions each pre-scan
# reaches, the arms of the WASM-type and Vera-type tables, the one
# boundary-guard derivation both pre-scans read, and `contract_exprs`.
# The file's field-coverage gate read the walkers' `# WALKER_COVERAGE:`
# checklists; the fold reaches every field by construction, which cell
# (a) above holds.


def _make_cg() -> CodeGenerator:
    """Build a fresh CodeGenerator for compilability scans."""
    return CodeGenerator()


def _make_ctx() -> WasmContext:
    """Build a fresh WasmContext for inference helpers."""
    return WasmContext(string_pool=StringPool())


def _declared_imports(body: str, formals: str, ret: str, effect: str,
                      decls: str = "") -> set[str]:
    """The host imports a module declares whose `main` has *body*."""
    from tests import pipeline

    source = (f"{decls}public fn main({formals} -> @{ret})\n"
              f"  requires(true)\n  ensures(true)\n  {effect}\n{{\n  {body}\n}}\n")
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    assert "main" in compiled.exports
    return set(re.findall(r'^\s*\(import "vera" "([^"]+)" ', compiled.wat, re.MULTILINE))


class TestScanIoOpsPositions:
    """A host call in each of these positions declares its import.  The
    pre-scan walks them and registers nothing: the emitter that
    lowers the call registers the import it calls (#735), so what pins each
    position is the compiled module's declaration."""

    def test_indexexpr_collection_recursion(self) -> None:
        # An IO call's array indexed directly is dropped (E602), so the
        # collection is a host built-in's.
        assert "map_keys$ks" in _declared_imports(
            "map_keys(@Map<String, Int>.0)[0]", "@Map<String, Int>", "String",
            "effects(pure)")

    def test_indexexpr_index_recursion(self) -> None:
        assert "time" in _declared_imports(
            "@Array<Int>.0[nat_to_int(IO.time(()))]", "@Array<Int>", "Int",
            "effects(<IO>)")

    def test_arraylit_elements_recursion(self) -> None:
        assert "read_line" in _declared_imports(
            "[IO.read_line(())]", "", "Array<String>", "effects(<IO>)")

    def test_interpolated_string_parts_recursion(self) -> None:
        # The literal fragments are bare `str`, the interpolated part an
        # expression.
        assert "read_line" in _declared_imports(
            'IO.print("prefix: \\(IO.read_line(())) suffix")', "", "Unit",
            "effects(<IO>)")

    def test_anonfn_body_recursion(self) -> None:
        # A lifted closure's body: its own context registers the import,
        # merged into the module's when the closure is lifted.
        decls = (
            "type Reader = fn(Unit -> String) effects(<IO>);\n\n"
            "private fn run(@Reader -> @String)\n  requires(true)\n"
            "  ensures(true)\n  effects(<IO>)\n{\n  apply_fn(@Reader.0, ())\n}\n\n")
        assert "read_line" in _declared_imports(
            "run(fn(@Unit -> @String) effects(<IO>) { IO.read_line(()) })", "", "String",
            "effects(<IO>)", decls)


def _handle_expr() -> ast.HandleExpr:
    """Build a minimal HandleExpr for State<Int>."""
    return ast.HandleExpr(
        effect=ast.EffectRef(
            name="State",
            type_args=(ast.NamedType(name="Int", type_args=None),)),
        state=None,
        clauses=(),
        body=ast.Block(statements=(), expr=ast.UnitLit()),
    )


class TestScanExprForHandlersPositions:
    """Each sub-expression position is walked, so
    HandleExprs buried inside are still discovered for type
    registration."""

    def test_qualifiedcall_args_recursion(self) -> None:
        cg = _make_cg()
        node = ast.QualifiedCall(
            qualifier="IO", name="print", args=(_handle_expr(),))
        cg._scan_expr_for_handlers(node)
        # State<Int> registered
        assert (CellNames(family="Int", base="Int"), "i64") in cg._state_types

    def test_indexexpr_recursion(self) -> None:
        cg = _make_cg()
        node = ast.IndexExpr(
            collection=_handle_expr(), index=ast.IntLit(value=0))
        cg._scan_expr_for_handlers(node)
        assert (CellNames(family="Int", base="Int"), "i64") in cg._state_types

    def test_arraylit_recursion(self) -> None:
        cg = _make_cg()
        node = ast.ArrayLit(elements=(_handle_expr(),))
        cg._scan_expr_for_handlers(node)
        assert (CellNames(family="Int", base="Int"), "i64") in cg._state_types

    def test_interpolated_string_recursion(self) -> None:
        cg = _make_cg()
        node = ast.InterpolatedString(parts=("x: ", _handle_expr()))
        cg._scan_expr_for_handlers(node)
        assert (CellNames(family="Int", base="Int"), "i64") in cg._state_types

    def test_anonfn_body_recursion(self) -> None:
        cg = _make_cg()
        body = ast.Block(statements=(), expr=_handle_expr())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        cg._scan_expr_for_handlers(node)
        assert (CellNames(family="Int", base="Int"), "i64") in cg._state_types


class TestInferExprWasmTypeArms:
    """AnonFn → "i32" (closure handle), ModuleCall → None (path
    field can't be threaded through bare-name FnCall dispatch)."""

    def test_anonfn_returns_i32(self) -> None:
        ctx = _make_ctx()
        body = ast.Block(statements=(), expr=ast.UnitLit())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        assert ctx._infer_expr_wasm_type(node) == "i32"

    def test_modulecall_returns_none(self) -> None:
        """ModuleCall carries `expr.path` that the bare-name FnCall
        dispatcher can't consume.  Returning None surfaces the
        unknown-type cleanly rather than masking with a wrong same-
        name lookup."""
        ctx = _make_ctx()
        node = ast.ModuleCall(
            path=("some_module",), name="some_fn", args=())
        assert ctx._infer_expr_wasm_type(node) is None


class TestInferVeraTypeArms:
    """Block / MatchExpr / HandleExpr → trailing-expr type;
    AssertExpr / AssumeExpr → "Unit"; AnonFn / QualifiedCall /
    ModuleCall → None (path/qualifier fields can't be threaded
    through the bare-name FnCall dispatcher).

    Since #1286 the `MatchExpr` arm joins over the arms rather than
    reading `arms[0]` — it answers from the first arm that YIELDS a
    name, an arm that only throws naming none.  The single-arm cases
    below are unaffected by that distinction; the join itself is pinned
    in `test_infer_vera_type_join_1286.py`.
    """

    def test_block_returns_trailing_expr_type(self) -> None:
        ctx = _make_ctx()
        node = ast.Block(statements=(), expr=ast.IntLit(value=42))
        assert ctx._infer_vera_type(node) == "Int"

    def test_matchexpr_returns_first_arm_body_type(self) -> None:
        ctx = _make_ctx()
        arm = ast.MatchArm(
            pattern=ast.WildcardPattern(),
            body=ast.BoolLit(value=True),
        )
        node = ast.MatchExpr(
            scrutinee=ast.IntLit(value=0), arms=(arm,))
        assert ctx._infer_vera_type(node) == "Bool"

    def test_matchexpr_no_arms_returns_none(self) -> None:
        ctx = _make_ctx()
        node = ast.MatchExpr(
            scrutinee=ast.IntLit(value=0), arms=())
        assert ctx._infer_vera_type(node) is None

    def test_handleexpr_returns_body_expr_type(self) -> None:
        ctx = _make_ctx()
        node = ast.HandleExpr(
            effect=ast.EffectRef(name="State", type_args=()),
            state=None,
            clauses=(),
            body=ast.Block(statements=(), expr=ast.FloatLit(value=1.5)),
        )
        assert ctx._infer_vera_type(node) == "Float64"

    def test_assertexpr_returns_unit(self) -> None:
        ctx = _make_ctx()
        node = ast.AssertExpr(expr=ast.BoolLit(value=True))
        assert ctx._infer_vera_type(node) == "Unit"

    def test_assumeexpr_returns_unit(self) -> None:
        ctx = _make_ctx()
        node = ast.AssumeExpr(expr=ast.BoolLit(value=True))
        assert ctx._infer_vera_type(node) == "Unit"

    def test_anonfn_returns_none(self) -> None:
        """Closure handle has no simple Vera-type name suitable
        for call rewriting; None lets callers handle the unknown
        case explicitly (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        body = ast.Block(statements=(), expr=ast.UnitLit())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        assert ctx._infer_vera_type(node) is None

    def test_qualifiedcall_returns_none(self) -> None:
        """`qualifier` can't be threaded through bare-name FnCall
        dispatch (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        node = ast.QualifiedCall(
            qualifier="IO", name="read_line", args=(ast.UnitLit(),))
        assert ctx._infer_vera_type(node) is None

    def test_modulecall_returns_none(self) -> None:
        """`path` can't be threaded through bare-name FnCall
        dispatch (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        node = ast.ModuleCall(
            path=("some_module",), name="some_fn", args=())
        assert ctx._infer_vera_type(node) is None


# The two pre-scans.  Both are in `vera/codegen/compilability.py`.
_PRE_SCANS = ("_scan_io_ops", "_scan_expr_for_handlers")


def _self_calls(path: Path, fn: str) -> set[str]:
    """Method names *fn* calls on `self`, anywhere in its body."""
    tree = pyast.parse(path.read_text(encoding="utf-8"))
    for node in pyast.walk(tree):
        if isinstance(node, pyast.FunctionDef) and node.name == fn:
            return {
                c.func.attr
                for c in pyast.walk(node)
                if isinstance(c, pyast.Call)
                and isinstance(c.func, pyast.Attribute)
                and isinstance(c.func.value, pyast.Name)
                and c.func.value.id == "self"
            }
    raise AssertionError(f"{fn} not found in {path.name} — has it moved?")


_CONTRACTS = Path(inspect.getfile(compilability)).parent / "contracts.py"
_COMPILABILITY = Path(inspect.getfile(compilability))


class TestBoundaryGuardDerivationIsShared:
    """The pre-scan reads the emitters' own decomposition, not a copy of it.

    Round 5 registered a named function's params and return by RE-DERIVING
    the emitter's two bails ("mirror `_refinement_guard_parts` exactly" was
    the comment).  It was a faithful copy of one route and unaware of three
    others — tuple components on the way in, tuple components on the way out,
    and closure signatures — each of which lowered predicates nothing
    registered, and each of which was a check-green program that died at
    whole-module WAT with `unknown func $vera.state_push_Nat`.

    A behavioural test can only pin the shapes someone thought to write; the
    reason round 5's fix was incomplete is that three shapes went unwritten.
    So this asserts the STRUCTURE that makes the classes converge: exactly
    one function classifies, and every consumer calls it.  Divergence now
    requires editing that function — or deleting an edge here.
    """

    def test_every_consumer_reads_the_one_decomposition(self) -> None:
        for consumer in (
            "_emit_component_refinement_guards",   # the emitter
            "_has_guardable_tuple_components",     # the epilogue gate
            "_component_guard_predicates",         # the pre-scan's enumeration
        ):
            calls = _self_calls(_CONTRACTS, consumer)
            assert "_tuple_component_guard_sites" in calls, (
                f"`{consumer}` no longer reads the shared tuple "
                "decomposition — it is classifying components itself again, "
                f"which is the round-5 shape.  Calls: {sorted(calls)}"
            )

    def test_no_consumer_reclassifies_behind_the_decomposition(self) -> None:
        """The negative half: a consumer that re-derives has diverged.

        `_refinement_guard_parts` / `_resolve_tuple_type` / `_resolve_type_
        alias` are how a component is classified.  Called from a consumer
        rather than from `_tuple_component_guard_sites`, they are a second
        opinion — and a second opinion is what the pre-scan and the emitter
        having was.
        """
        for consumer in (
            "_emit_component_refinement_guards",
            "_has_guardable_tuple_components",
            "_component_guard_predicates",
        ):
            calls = _self_calls(_CONTRACTS, consumer)
            reclassified = calls & {
                "_refinement_guard_parts",
                "_resolve_tuple_type",
                "_resolve_type_alias",
            }
            assert not reclassified, (
                f"`{consumer}` classifies components with "
                f"{sorted(reclassified)} instead of reading "
                "`_tuple_component_guard_sites` — put the decision in the "
                "decomposition, where all three consumers see it"
            )

    def test_the_pre_scan_walks_closure_signatures(self) -> None:
        """Both walkers reach the closure leg, and it reads the derivation."""
        assert "_signature_refinement_predicates" in _self_calls(
            _COMPILABILITY, "_scan_anon_fn_signature")
        for walker in _PRE_SCANS:
            assert "_scan_anon_fn_signature" in _self_calls(
                _COMPILABILITY, walker), (
                f"`{walker}` no longer walks an AnonFn's SIGNATURE — a "
                "refined closure formal / return is guarded in the lifted "
                "body, and nothing else registers what its predicate needs"
            )

    def test_the_named_entry_point_reads_the_same_derivation(self) -> None:
        """The handler walk's entry point enumerates a `FnDecl`'s signature."""
        assert "_signature_refinement_predicates" in _self_calls(
            _COMPILABILITY, "_scan_body_for_state_handlers")

    def test_the_callgraph_probe_can_go_red(self) -> None:
        """The extraction finds real edges, and misses ones that are absent."""
        calls = _self_calls(_CONTRACTS, "_signature_refinement_predicates")
        assert {"_refinement_guard_parts", "_component_guard_predicates"} <= (
            calls), sorted(calls)
        assert "_emit_refinement_check" not in calls, (
            "the derivation must not EMIT anything — it is read by the "
            "import pre-scan, which runs before any instruction is built"
        )
        with pytest.raises(AssertionError):
            _self_calls(_CONTRACTS, "_no_such_method_anywhere")


class TestContractExprsDispatch:
    """Every contract kind is enumerated, a new one by construction.

    The helper started as `getattr(c, "expr", None)`, which treats an
    unrecognised contract kind as "carries no predicates" — the silent skip it
    was written to fix, since `Decreases` carries `exprs` and was dropped
    exactly that way.  It reads each clause's fields through `vera.fold`, so
    the next new `ast.Contract` subclass has its expressions enumerated
    whatever its fields are called.
    """

    @staticmethod
    def _lit(n: int) -> ast.IntLit:
        return ast.IntLit(value=n)

    def test_single_predicate_kinds_are_yielded(self) -> None:
        contracts = (
            ast.Requires(expr=self._lit(1)),
            ast.Ensures(expr=self._lit(2)),
            ast.Invariant(expr=self._lit(3)),
        )
        assert [e.value for e in compilability.contract_exprs(contracts)] == [
            1, 2, 3]

    def test_decreases_yields_every_measure_component(self) -> None:
        """A lexicographic measure is SEVERAL expressions, in `exprs`."""
        contracts = (ast.Decreases(exprs=(self._lit(7), self._lit(8))),)
        assert [e.value for e in compilability.contract_exprs(contracts)] == [
            7, 8]

    def test_a_new_contract_kind_is_enumerated_by_construction(self) -> None:
        """A new `ast.Contract` subclass yields its expressions, in field
        order, under field names no enumeration was told about.

        Constructed synthetically because every kind that exists today is
        handled — which is the point: this pins what happens to the NEXT one.
        """

        @dataclasses.dataclass(frozen=True)
        class _FutureContract(ast.Contract):
            measure: ast.Expr
            bounds: tuple[ast.Expr, ...]

        future = _FutureContract(
            measure=self._lit(4), bounds=(self._lit(5), self._lit(6)))
        assert [e.value for e in compilability.contract_exprs((future,))] == [
            4, 5, 6]
