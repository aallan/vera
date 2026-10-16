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
    module that dispatches on `Expr`.

The two run-level cells at the end are the shapes the free-variable port
changed: a destructuring `let` in a closure (refused at 313c04db, the
function dropped with "unsupported expressions" and `main` with E620), and a
closure whose `handle` captures different new types in its body and in its
state (its capture layout order moved; the run output is the same).
"""

from __future__ import annotations

import dataclasses
import inspect
import subprocess
import sys
import types
import typing
from collections.abc import Callable
from pathlib import Path

import pytest

from tests import pipeline
from vera import ast, binders, fold

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
            if not isinstance(node, fold.OPAQUE):
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
        assert (got.owner, got.field, got.index) == (owner, field, index), (
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
    "_synth_expr_impl",
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
               "vera.wasm.context", "vera.wasm.inference"]
    out = subprocess.run(
        [sys.executable, "-c", script, *modules], cwd=ROOT, capture_output=True,
        text=True, encoding="utf-8", timeout=120, check=False)
    assert out.returncode == 0, out.stderr
    lines = out.stdout.splitlines()
    assert lines[0] == "import refused", out.stdout
    assert set(lines[1].split()) == _TABLES, out.stdout


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


@pytest.mark.xfail(strict=True, reason="the free-variable walk skips a LetDestruct")
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
