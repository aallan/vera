"""One traversal of the AST, one table dispatch over `Expr`, and one
binder-aware scope walk.

Every pass that walks an expression used to choose, class by class, which
fields to descend into, and a walker that forgot one was silent: the missing
case fell through to its default and the enclosing pass produced wrong
output (#588, #604, #559, #648).  The `#597` gate made each walker LIST every
`Expr` class in a comment, which checked the comment and not the walk.  This
module takes the choice away:

- **The traversal.**  :func:`children` reads a node's dataclass fields, so a
  node class added to ``vera/ast.py`` is traversed by construction.  The
  children of a node are the `ast.Node` values of its fields, a tuple's
  items in turn, in the order :func:`field_order` gives: declaration order,
  except for the classes :data:`ORDER` names, each with its reason.  Five
  kinds are never entered, because nothing in them is evaluated as part of
  the expression that holds them (:data:`OPAQUE`): a type, whose refinement
  predicate has a scope of its own; a pattern; an effect row or reference;
  and a nested declaration, which is its own root.  :func:`walk` and
  :func:`fold` are built on :func:`children`, with explicit stacks, since an
  expression is as deep as the program makes it (the #1208 depth rule).

- **The dispatch.**  A pass whose work differs per expression class builds
  a :func:`dispatch` table, which refuses to be built unless it names every
  class in :data:`EXPR_CLASSES`.  A new subclass in ``vera/ast.py`` therefore
  fails the import of every module that builds a `fold.dispatch` table, at
  the commit that adds it, where the `#597` gate read a checklist comment.
  The arms keep their own per-class logic, recursion included: the table
  decides only which arm runs.

- **The scope walk.**  :func:`scoped` yields every node with the slots in
  scope where it is evaluated.  The binder positions are
  ``vera.binders.BINDER_FIELDS``; this module adds only where each
  position's slots are visible (:data:`EXTENTS`, one entry per position,
  held equal to ``BINDER_FIELDS`` at import), read off the checker's
  ``push_scope`` / ``bind`` sites.  A :class:`Scope` resolves ``@T.n`` as
  ``TypeEnv.resolve_slot_binding`` does: the ``n``-th most recent binder
  whose name is ``T``.

- **The context walk.**  :func:`contexts` yields every node with the
  context a consumer's step gives it, a parameterised walk for the passes
  whose context is not a scope (a verifier walk's path facts and slot
  environment).  The step chooses each child's context, lazily, after the
  previous child's subtree, and never the children: the walk refuses a step
  that leaves one out.

What a consumer may do: read nodes, keep them, compare them by identity, and
build its own results from them.  What it may not: mutate the AST (nodes are
frozen and the fold builds none), or ask the fold about types.  The fold is
structural and knows no types; the scope walk names a binder by the namer
the consumer passes, because a slot's name depends on the alias environment
of the module that declared it (`vera.naming`), which no structural walk
holds.  A consumer whose output ORDER matters (a closure's capture layout, an
obligation list) inherits :data:`ORDER`.

Imports ``vera.ast`` and ``vera.binders`` only.
"""

from __future__ import annotations

import inspect
from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import Field, dataclass, fields
from types import MappingProxyType
from typing import Any, Generic, TypeVar

from vera import ast
from vera.binders import BINDER_FIELDS

R = TypeVar("R")
H = TypeVar("H")


# =====================================================================
# The classes
# =====================================================================

def _reflect_expr_classes() -> frozenset[type[ast.Expr]]:
    """Every `Expr` subclass ``vera/ast.py`` declares, at any depth."""
    return frozenset(
        obj for obj in vars(ast).values()
        if inspect.isclass(obj) and issubclass(obj, ast.Expr)
        and obj is not ast.Expr and obj.__module__ == ast.__name__
    )


#: Every concrete expression class, read from ``vera/ast.py`` when this
#: module is imported.  :func:`dispatch` holds every table to it.
EXPR_CLASSES: frozenset[type[ast.Expr]] = _reflect_expr_classes()

#: The node kinds the fold does not enter as children: nothing inside one is
#: evaluated as part of the expression that holds it.  A type's refinement
#: predicate is checked with its own binder as the only slot in scope (spec
#: §2.6), a pattern binds rather than evaluates, an effect is a name, and a
#: nested declaration (a `where` helper) is a root of its own.  Any of them
#: can still be the ROOT of a walk.
OPAQUE: tuple[type[ast.Node], ...] = (
    ast.TypeExpr, ast.Pattern, ast.EffectRow, ast.EffectRefNode, ast.Decl,
)


# =====================================================================
# The order
# =====================================================================

@dataclass(frozen=True)
class FieldOrder:
    """The order one node class's fields are visited in, and why."""

    #: Every field of the class but ``span``, in visiting order.
    fields: tuple[str, ...]
    #: Why the order is not declaration order.
    why: str


#: The classes whose fields are not visited in declaration order.  Each entry
#: names every field of its class, so a field added to the class later is a
#: failure at import rather than a field the fold skips.
ORDER: dict[type[ast.Node], FieldOrder] = {
    ast.HandleExpr: FieldOrder(
        ("effect", "state", "body", "clauses"),
        "evaluation order: the state's initialiser runs before the handled "
        "body, and a clause runs only when the body performs its operation, "
        "so the clauses come after the body; the declaration writes them "
        "before it.  The verifier's walks visit a handler in this order",
    ),
}


_FIELD_ORDERS: dict[type, tuple[str, ...]] = {}


def _visited(f: Field[Any]) -> bool:
    """Whether the fold names field *f*: every field but a node's span and
    its identity (``node_id``), which say where a node is, not what it
    holds."""
    return f.name != "span" and not f.metadata.get("identity")


def field_order(cls: type[ast.Node]) -> tuple[str, ...]:
    """The fields of *cls* the fold visits, in order: declaration order, or
    the order :data:`ORDER` gives the class."""
    order = _FIELD_ORDERS.get(cls)
    if order is None:
        entry = ORDER.get(cls)
        order = entry.fields if entry is not None else tuple(
            f.name for f in fields(cls) if _visited(f))
        _FIELD_ORDERS[cls] = order
    return order


def _check_order() -> None:
    for cls, entry in ORDER.items():
        declared = {f.name for f in fields(cls) if _visited(f)}
        if set(entry.fields) != declared or len(entry.fields) != len(declared):
            raise TypeError(
                f"vera.fold.ORDER names {entry.fields} for {cls.__name__}, "
                f"whose fields are {sorted(declared)}: name every field, in "
                f"the order the fold visits them")


# =====================================================================
# The traversal
# =====================================================================

def _gather(value: object, out: list[ast.Node]) -> None:
    """Append the nodes the fold enters from one field's *value*."""
    if isinstance(value, ast.Node):
        if not isinstance(value, OPAQUE):
            out.append(value)
    elif isinstance(value, tuple):
        for item in value:
            _gather(item, out)


def children(node: ast.Node) -> tuple[ast.Node, ...]:
    """The child nodes the fold enters from *node*, in :func:`field_order`.

    A field holding a node yields it, a tuple its nodes in turn (so an
    interpolation's string fragments and a `with` update's type are passed
    over), and a node of an :data:`OPAQUE` kind is not yielded."""
    out: list[ast.Node] = []
    for name in field_order(type(node)):
        _gather(getattr(node, name), out)
    return tuple(out)


def _roots(root: object) -> list[ast.Node]:
    """*root* itself, or the nodes of a tuple of roots, in order."""
    if isinstance(root, ast.Node):
        return [root]
    if isinstance(root, tuple):
        return [item for item in root if isinstance(item, ast.Node)]
    return []


def walk(root: object) -> Iterator[ast.Node]:
    """Every node under *root*, pre-order: a node, then its children's
    subtrees in order.  *root* is a node of any kind, or a tuple of them."""
    stack = _roots(root)
    stack.reverse()
    while stack:
        node = stack.pop()
        yield node
        stack.extend(reversed(children(node)))


def fold(root: ast.Node, f: Callable[[ast.Node, tuple[R, ...]], R]) -> R:
    """``f(node, results)`` applied bottom-up, *results* being the folded
    values of ``children(node)`` in order."""
    out: list[R] = []
    stack: list[tuple[ast.Node, int]] = [(root, -1)]
    while stack:
        node, count = stack.pop()
        if count < 0:
            kids = children(node)
            stack.append((node, len(kids)))
            stack.extend((kid, -1) for kid in reversed(kids))
            continue
        start = len(out) - count
        results = tuple(out[start:])
        del out[start:]
        out.append(f(node, results))
    return out[0]


# =====================================================================
# The dispatch
# =====================================================================

def dispatch(
    name: str, arms: Mapping[type[ast.Expr], H],
) -> Mapping[type[ast.Expr], H]:
    """*arms* as a read-only table keyed by expression class, once it is
    shown to name every class in :data:`EXPR_CLASSES` and nothing else.

    *name* is the pass the table belongs to, for the refusal.  A consumer
    looks its arm up with ``table.get(type(expr))``: an expression of a class
    the table cannot name (a synthetic one a test builds) gets the
    consumer's own fallback."""
    missing = EXPR_CLASSES - arms.keys()
    extra = arms.keys() - EXPR_CLASSES
    if missing or extra:
        parts = []
        if missing:
            parts.append(
                "no arm for " + ", ".join(sorted(c.__name__ for c in missing)))
        if extra:
            parts.append(
                "arms for classes that are no expression: "
                + ", ".join(sorted(c.__name__ for c in extra)))
        raise TypeError(
            f"{name}: {'; '.join(parts)}.  A dispatch over `Expr` names every "
            f"class vera/ast.py declares: give each new class its arm")
    return MappingProxyType(dict(arms))


def each(classes: Iterable[type[ast.Expr]], arm: H) -> dict[type[ast.Expr], H]:
    """One *arm* for each of *classes*: the classes a table answers alike,
    still each named."""
    return {cls: arm for cls in classes}


# =====================================================================
# The scope walk
# =====================================================================

@dataclass(frozen=True)
class Binder:
    """One slot a binder position declares."""

    #: The node that declares it: the function, closure, `let`, destructure,
    #: binding pattern, handler clause or handler state.
    owner: ast.Node
    #: The ``BINDER_FIELDS`` field it is declared in.
    field: str
    #: Its index within that field (0 for a single type).
    index: int
    #: Its declared type.
    type_expr: ast.TypeExpr
    #: The slot name a reference reaches it by, as the consumer's namer
    #: renders it; ``None`` when the namer cannot name it.
    name: str | None


class Scope:
    """The binders in scope at a point, persistent: :meth:`push` returns a
    new scope and leaves this one as it was, so a scope the walk yielded
    stays what it was where it was yielded."""

    __slots__ = ("_parent", "_binder")

    def __init__(self, parent: Scope | None = None,
                 binder: Binder | None = None) -> None:
        self._parent = parent
        self._binder = binder

    def push(self, *binders: Binder) -> Scope:
        """This scope with *binders* added, the last the most recent."""
        scope = self
        for binder in binders:
            scope = Scope(scope, binder)
        return scope

    def _newest_first(self) -> Iterator[Binder]:
        scope: Scope | None = self
        while scope is not None and scope._binder is not None:
            yield scope._binder
            scope = scope._parent

    def resolve(self, name: str, index: int) -> Binder | None:
        """The binder ``@name.index`` names: the *index*-th most recent one
        named *name*, or ``None`` when fewer are in scope."""
        count = 0
        for binder in self._newest_first():
            if binder.name == name:
                if count == index:
                    return binder
                count += 1
        return None

    def count(self, name: str) -> int:
        """How many binders named *name* are in scope."""
        return sum(1 for binder in self._newest_first() if binder.name == name)

    def binders(self) -> tuple[Binder, ...]:
        """Every binder in scope, oldest first."""
        return tuple(reversed(list(self._newest_first())))


#: The scope with nothing in it.
EMPTY_SCOPE = Scope()


@dataclass(frozen=True)
class Extent:
    """Where the slots one binder position declares are in scope.

    ``kind`` is one of:

    - ``"fields"``: the owner's own fields named in ``over``;
    - ``"block"``: the statements after the owner in its block, and the
      block's value;
    - ``"clauses"``: each clause of the owner's handler, after the clause's
      own parameters;
    - ``"pattern"``: a position inside a pattern, whose slots are the
      enclosing arm's (``MatchArm.pattern``), depth first, left to right;
    - ``"none"``: no slot a reference can reach.
    """

    kind: str
    over: tuple[str, ...] = ()
    why: str = ""


#: One extent per ``BINDER_FIELDS`` position, keyed the same way.  Read off
#: the checker: ``_check_fn`` and ``_check_anon_fn`` bind the parameters in a
#: scope pushed over the contracts and the body, ``_check_block`` binds a
#: statement's slots after checking its value, ``_check_match`` an arm's
#: pattern over its body, and ``_check_handle`` a clause's parameters and then
#: the handler's state over the clause body and its `with` update.
EXTENTS: dict[tuple[type[ast.Node], str], Extent] = {
    (ast.FnDecl, "params"): Extent(
        "fields", ("contracts", "body"),
        "a function's parameters are its contracts' and its body's slots; "
        "a `where` helper is a closed scope of its own and cannot reach "
        "them"),
    (ast.FnDecl, "return_type"): Extent(
        "none", why="the return value is reached as `@T.result`, a "
        "`ResultRef`, never as a slot"),
    (ast.AnonFn, "params"): Extent(
        "fields", ("body",), "a closure's parameters are its body's most "
        "recent slots, over whatever it captures"),
    (ast.AnonFn, "return_type"): Extent(
        "none", why="as a function's: the lifted body's value binds no "
        "slot"),
    (ast.LetStmt, "type_expr"): Extent(
        "block", why="`let @T = e;` binds after `e` is evaluated, so `e` "
        "does not see it and everything after it in the block does"),
    (ast.LetDestruct, "type_bindings"): Extent(
        "block", why="each component in order, after the source is "
        "evaluated, so the last component of a type is that type's `.0`"),
    (ast.MatchArm, "pattern"): Extent(
        "fields", ("body",), "an arm's pattern binds over that arm's body "
        "only: not the scrutinee, not another arm"),
    (ast.ConstructorPattern, "sub_patterns"): Extent(
        "pattern", why="a sub-pattern's binders are its arm's, in source "
        "order"),
    (ast.BindingPattern, "type_expr"): Extent(
        "pattern", why="the one slot a binding pattern declares, in its "
        "arm's scope"),
    (ast.HandlerClause, "params"): Extent(
        "fields", ("body", "state_update"), "the operation's arguments, "
        "bound over the clause body and its `with` update"),
    (ast.HandlerClause, "state_update"): Extent(
        "none", why="`with @T = e` writes the handler's cell; the slot it "
        "names is the handler state's"),
    (ast.HandlerState, "type_expr"): Extent(
        "clauses", why="the handler's state is a slot in each clause, bound "
        "after the clause's parameters; neither its own initialiser nor the "
        "handled body sees it (spec §7.5.1)"),
    (ast.Constructor, "fields"): Extent(
        "none", why="a constructor's fields are a declaration; no "
        "expression is evaluated in their scope"),
    (ast.OpDecl, "param_types"): Extent(
        "none", why="an operation's formals are a declaration; a clause's "
        "`params` bind its arguments"),
    (ast.OpDecl, "return_type"): Extent(
        "none", why="a declaration; a clause's `resume` delivers the value"),
    (ast.ForallExpr, "binding_type"): Extent(
        "none", why="the quantified slot is the predicate closure's own "
        "parameter; the declared type opens no scope of its own"),
    (ast.ExistsExpr, "binding_type"): Extent(
        "none", why="as `forall`'s"),
}


def _check_extents() -> None:
    positions = {(cls, b.field) for cls, bs in BINDER_FIELDS.items()
                 for b in bs}
    if set(EXTENTS) != positions:
        unlisted = sorted(f"{c.__name__}.{f}" for c, f in positions - set(EXTENTS))
        stale = sorted(f"{c.__name__}.{f}" for c, f in set(EXTENTS) - positions)
        raise TypeError(
            f"vera.fold.EXTENTS and vera.binders.BINDER_FIELDS disagree: "
            f"no extent for {unlisted}, an extent for no position {stale}")


Namer = Callable[[ast.TypeExpr], "str | None"]


def _declared(owner: ast.Node, name: str, namer: Namer) -> list[Binder]:
    """The binders *owner*'s field *name* declares, in order."""
    value = getattr(owner, name)
    items = value if isinstance(value, tuple) else (value,)
    out: list[Binder] = []
    for index, item in enumerate(items):
        if isinstance(item, ast.TypeExpr):
            out.append(Binder(owner, name, index, item, namer(item)))
        elif isinstance(item, ast.Pattern):
            out.extend(_pattern_binders(item, namer))
    return out


def _pattern_binders(pattern: ast.Pattern, namer: Namer) -> list[Binder]:
    """A pattern's binders, depth first, left to right, from the positions
    ``BINDER_FIELDS`` registers on pattern classes."""
    out: list[Binder] = []
    for binder in BINDER_FIELDS.get(type(pattern), ()):
        if EXTENTS[(type(pattern), binder.field)].kind == "pattern":
            out.extend(_declared(pattern, binder.field, namer))
    return out


def _binders_of(node: ast.Node, kind: str, namer: Namer) -> list[Binder]:
    """The binders *node* declares at its positions of extent *kind*."""
    out: list[Binder] = []
    for binder in BINDER_FIELDS.get(type(node), ()):
        if EXTENTS[(type(node), binder.field)].kind == kind:
            out.extend(_declared(node, binder.field, namer))
    return out


_Item = tuple[ast.Node, Scope, tuple[Binder, ...]]


def _scoped_children(node: ast.Node, scope: Scope,
                     pending: tuple[Binder, ...], namer: Namer) -> list[_Item]:
    """*node*'s children, each with the scope it is evaluated in.

    *pending* are the binders an enclosing node hands down to be bound after
    *node*'s own: a handler's state, for each of its clauses."""
    kids = children(node)
    if type(node) is ast.Block:
        # A block threads one scope through its statements in order.
        out: list[_Item] = []
        for kid in kids:
            out.append((kid, scope, ()))
            scope = scope.push(*_binders_of(kid, "block", namer))
        return out
    over: dict[str, list[Binder]] = {}
    for binder in BINDER_FIELDS.get(type(node), ()):
        extent = EXTENTS[(type(node), binder.field)]
        if extent.kind == "fields":
            declared = _declared(node, binder.field, namer)
            for name in extent.over:
                over.setdefault(name, []).extend(declared)
    for name in over:
        over[name].extend(pending)
    handed: tuple[Binder, ...] = tuple(
        b for kid in kids for b in _binders_of(kid, "clauses", namer))
    out = []
    for name in field_order(type(node)):
        bound = over.get(name)
        field_scope = scope.push(*bound) if bound else scope
        found: list[ast.Node] = []
        _gather(getattr(node, name), found)
        for kid in found:
            down = handed if isinstance(kid, ast.HandlerClause) else ()
            out.append((kid, field_scope, down))
    return out


def scoped(root: object, namer: Namer,
           scope: Scope = EMPTY_SCOPE) -> Iterator[tuple[ast.Node, Scope]]:
    """Every node under *root*, pre-order as :func:`walk` visits them, with
    the scope it is evaluated in.

    *namer* renders a binder's declared type to the slot name references
    reach it by.  *scope* is what is in scope at *root*: a consumer reading
    a closure body starts with the closure's own scope and treats a
    reference that resolves to nothing as a capture."""
    stack: list[_Item] = [(node, scope, ()) for node in _roots(root)]
    stack.reverse()
    while stack:
        node, here, pending = stack.pop()
        yield node, here
        stack.extend(reversed(_scoped_children(node, here, pending, namer)))


# =====================================================================
# The context walk
# =====================================================================

C = TypeVar("C")

#: A context walk's step: *node*'s children, each with the context it is
#: evaluated in, or ``None`` when each is evaluated in *node*'s own.
Step = Callable[[ast.Node, C], "Iterable[tuple[ast.Node, C]] | None"]


class _Frame(Generic[C]):
    """A node on the context walk's stack: the pairs its step gives, and
    the children those must be, in order."""

    __slots__ = ("node", "kids", "pairs", "given")

    def __init__(self, node: ast.Node, ctx: C, step: Step[C]) -> None:
        self.node = node
        self.kids = children(node)
        pairs = step(node, ctx)
        self.pairs: Iterator[tuple[ast.Node, C]] = iter(
            ((kid, ctx) for kid in self.kids) if pairs is None else pairs)
        self.given = 0

    def refusal(self, why: str) -> TypeError:
        return TypeError(
            f"vera.fold.contexts: the step for {type(self.node).__name__} "
            f"{why}; a step gives the children `children()` yields, each "
            f"once, in that order")


def contexts(root: ast.Node, step: Step[C],
             ctx: C) -> Iterator[tuple[ast.Node, C]]:
    """Every node under *root*, pre-order as :func:`walk` visits them, with
    the context it is evaluated in.

    *ctx* is the context at *root*.  ``step(node, ctx)`` gives *node*'s
    children with the context each is evaluated in, or ``None`` when each is
    evaluated in *ctx*.  The walk iterates a step lazily: it asks for the
    next child only once the previous child's subtree has been yielded, so a
    step that derives a child's context from what is evaluated before it (a
    condition, a binding, an assumption) runs in the order a recursive walk
    runs it, interleaved with whatever the consumer does at each node it is
    handed.

    A step chooses contexts, never children: it gives exactly the children
    :func:`children` yields, each once, in that order, or the walk raises
    `TypeError` at the first one out of place, so no walk built on this one
    can leave a child out."""
    yield root, ctx
    stack = [_Frame(root, ctx, step)]
    while stack:
        frame = stack[-1]
        try:
            child, child_ctx = next(frame.pairs)
        except StopIteration:
            if frame.given != len(frame.kids):
                raise frame.refusal(
                    f"gave {frame.given} of its {len(frame.kids)} "
                    f"children") from None
            stack.pop()
            continue
        if frame.given >= len(frame.kids) or child is not frame.kids[frame.given]:
            raise frame.refusal(
                f"gave {type(child).__name__} where child {frame.given} is due")
        frame.given += 1
        yield child, child_ctx
        stack.append(_Frame(child, child_ctx, step))


_check_order()
_check_extents()
