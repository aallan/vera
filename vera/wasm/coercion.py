"""Composite coercions into a `Nat` component (#1542's shape, #1695's line).

The checker admits a value whose type holds an `Int` where the position it
stands in holds a `Nat` (`Option<Int>` at an `Option<Nat>` formal, an array
literal of `Wrap<Int>` under an `Array<Wrap<Nat>>` binding), and records the
target on the coerced node alone.  Nothing obligates the component, so code
generation guards it, by ONE rule decided off the typed program.

For an expression node N the REQUIREMENT is the type an enclosing descent
handed N, else the type the checker checked N against; its differing tree
against N's own type (:func:`vera.narrowing.differing_tree`) names every
component where the requirement holds a `Nat` and N's type an `Int`.  When
the tree has a position below the root (a difference at the root alone is a
scalar narrowing, the existing guards' business):

* a CONSTRUCTION (a constructor call, a tuple, an array literal,
  ``map_insert``, ``set_add``) hands each child its component of the
  requirement, and a scalar child the requirement makes a `Nat` is guarded
  where it is STORED (:meth:`CoercionMixin._coercion_leaf_guard`), beside the
  store's existing in-place decision and only where that decision placed no
  guard; a nullary constructor, ``[]``, ``map_new()`` and ``set_new()`` hold
  nothing;
* a JOIN (a block's tail, an ``if``, a ``match``, a ``handle``) hands the
  requirement to each value leaf and is never guarded itself;
* any other node is OPAQUE (a slot, a call's result, an index, a field read):
  its value is walked at run time along the tree's positions, by a helper
  generated per tree on the ``$eq_*`` model, and a negative component traps
  exactly as a scalar narrowing does (``nat_guard``).

A pattern binder declared narrower than the component it binds walks the
bound value (:func:`vera.narrowing.component_coercion`), and so does a
destructure and a handler clause binder, bar the one exclusion
(:data:`vera.narrowing.CLAUSE_BINDER_UNGUARDED_HEADS`).

Three existing guards of the same coercion are deferred to, never doubled:
the in-place decision at a store, #1606's construction hand-down (which that
decision reads), and a function boundary's tuple-component guard (#746),
whose positions leave the tree before it is acted on (:meth:`_deferring`).

A handed requirement nothing consumes is a lost guard, so it is loud: the
node that handed it raises :class:`CodegenInvariantError` when its own
translation ends.  A `Map` or `Set` walk reads the collection through the
same projections a program's own ``map_keys`` / ``map_values`` /
``set_to_array`` call does, so its guard is O(n) and allocates; the walked
value and every projected array are rooted on the GC shadow stack across it.
"""

from __future__ import annotations

import hashlib
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from vera import ast, narrowing
from vera.narrowing import Coercion
from vera.skip import CodegenInvariantError
from vera.types import NAT, AdtType, Type, pretty_type, value_type_name
from vera.wasm.helpers import element_sequence_loop, gc_shadow_push

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

    from vera.codegen.memory import ConstructorLayout
    from vera.typed import TypedProgram

#: The projection that reads each collection position as an array: the
#: generated function a program's own call would reach, and the slot of
#: `_collection_fn` its element's tag fills.
_PROJECTIONS: dict[tuple[str, str], tuple[str, str]] = {
    ("set", ""): ("set_to_array", "e"),
    ("map", "key"): ("map_keys", "k"),
    ("map", "value"): ("map_values", "v"),
}


@dataclass
class _Handed:
    """A requirement a descent handed one node, until that node consumes it."""

    expr: ast.Expr
    target: Type
    covered: frozenset[tuple[int, ...]]
    consumed: bool = False


@dataclass
class _HelperLocals:
    """The locals of one generated walk helper, numbered after its params."""

    first: int
    types: list[str] = field(default_factory=list)

    def new(self, wt: str) -> int:
        self.types.append(wt)
        return self.first + len(self.types) - 1


def _unwrap_future(node: Coercion) -> Coercion:
    """A `Future` is its payload at run time, so its walk is the payload's."""
    while node.kind == "future":
        node = node.parts[0][2]
    return node


def _tree_key(node: Coercion) -> str:
    """A canonical spelling of *node*, which names its helper."""
    head = f"{node.kind}({pretty_type(node.source)}=>{pretty_type(node.target)})"
    if not node.parts:
        return head
    inner = ",".join(f"{c}.{i}:{_tree_key(child)}" for c, i, child in node.parts)
    return f"{head}[{inner}]"


class CoercionMixin:
    """The composite-coercion rule over a :class:`WasmContext`."""

    if TYPE_CHECKING:
        _typed_program: TypedProgram | None
        _expr_semantic_types: Mapping[int, object]
        _expr_target_types: Mapping[int, object]
        needs_alloc: bool

        def alloc_local(self, wasm_type: str) -> int: ...
        def _emit_trap(self, emitter: str, *, at: ast.Node | None,
                       message: str | None = None,
                       path: tuple[str, ...] = ()) -> list[str]: ...
        def _emit_negative_i64_guard(self, value: list[str], *,
                                     trap: list[str]) -> list[str]: ...
        def _narrows_into_nat(self, expr: ast.Expr) -> bool: ...
        def _type_of(self, node: ast.Node) -> Type | None: ...
        def _map_wasm_tag(self, vera_type: str | None) -> str | None: ...
        def _collection_fn(self, op: str, **tags: str) -> str: ...
        def _element_mem_size(self, elem_type: str) -> int | None: ...
        def _element_load_op(self, elem_type: str) -> str | None: ...
        def _is_pair_element_type(self, elem_type: str) -> bool: ...
        def _concrete_field_layout(
            self, field_type_names: list[str]) -> list[tuple[int, str]]: ...

        _adt_ctor_layouts: dict[str, dict[str, ConstructorLayout]]
        _boundary_coercion_paths: Callable[
            [ast.TypeExpr, int | None], frozenset[tuple[int, ...]]] | None
        _fn_boundary_coercion_paths: dict[
            str, tuple[frozenset[tuple[int, ...]], ...]]

    def _init_component_coercion(self) -> None:
        #: The requirement each node was handed, by node identity.
        self._coercion_handed: dict[int, _Handed] = {}
        #: The keys each handing node registered, checked when it ends.
        self._coercion_owned: dict[int, list[int]] = {}
        #: The positions a boundary guard checks, by the node they leave.
        self._coercion_deferred: dict[int, frozenset[tuple[int, ...]]] = {}
        #: The generated walk helpers, by name, merged into the module.
        self._coercion_helpers: dict[str, str] = {}
        self._coercion_pending: set[str] = set()
        #: The per-pair differing trees, computed once each.
        self._coercion_trees: dict[tuple[Type, Type], Coercion | None] = {}

    # -----------------------------------------------------------------
    # The rule
    # -----------------------------------------------------------------

    def _differing(self, source: Type, target: Type) -> Coercion | None:
        typed = self._typed_program
        if typed is None:
            return None
        key = (source, target)
        if key not in self._coercion_trees:
            self._coercion_trees[key] = narrowing.differing_tree(
                source, target, typed.field_types_at, typed.constructors_of)
        return self._coercion_trees[key]

    def _effective_type(self, expr: ast.Expr) -> Type | None:
        """The type *expr* was checked against, else its own."""
        if expr.node_id is None:
            return None
        target = self._expr_target_types.get(expr.node_id)
        if isinstance(target, Type):
            return target
        own = self._expr_semantic_types.get(expr.node_id)
        return own if isinstance(own, Type) else None

    def _coercion_enter(self, expr: ast.Expr) -> Coercion | None:
        """Act on *expr*'s requirement before it is translated: hand a
        construction's or a join's components down, and return the tree an
        opaque value is walked along after it is translated."""
        if expr.node_id is None or self._typed_program is None:
            return None
        handed = self._coercion_handed.get(id(expr))
        if handed is not None and handed.expr is not expr:
            handed = None
        if handed is not None:
            target: object = handed.target
            covered = handed.covered
        else:
            target = self._expr_target_types.get(expr.node_id)
            covered = self._coercion_deferred.get(id(expr), frozenset())
        source = self._expr_semantic_types.get(expr.node_id)
        if not (isinstance(target, Type) and isinstance(source, Type)):
            if handed is not None:
                handed.consumed = True
            return None
        tree = narrowing.without_paths(self._differing(source, target), covered)
        if tree is not None and tree.kind == "nat":
            # A scalar requirement: the store that receives the value guards
            # it (`_coercion_leaf_guard`), and consumes it there.
            return None
        if handed is not None:
            handed.consumed = True
        if tree is None:
            return None
        if narrowing.flow_arms(expr) is not None:
            for leaf in narrowing.value_leaves(expr):
                self._hand(expr, leaf, target, covered)
            return None
        if self._hand_construction(expr, tree, target, covered):
            return None
        return tree

    def _coercion_leave(self, expr: ast.Expr, *, translated: bool) -> None:
        """End *expr*'s scope: every requirement it handed is consumed, or
        a guard was lost and the compile says so."""
        keys = self._coercion_owned.pop(id(expr), None)
        if not keys:
            return
        lost = []
        for key in keys:
            handed = self._coercion_handed.pop(key, None)
            if handed is not None and not handed.consumed:
                lost.append(handed)
        if lost and translated:
            raise CodegenInvariantError(
                f"a composite coercion handed {len(lost)} component "
                f"requirement(s) no translation consumed (the first at "
                f"{type(lost[0].expr).__name__}): a guard would be lost",
                lost[0].expr,
            )

    def _hand(self, owner: ast.Expr, node: ast.Expr, target: Type,
              covered: frozenset[tuple[int, ...]]) -> None:
        """Hand *target* to *node*; the outermost hand-down wins."""
        key = id(node)
        if key in self._coercion_handed:
            return
        self._coercion_handed[key] = _Handed(node, target, covered)
        self._coercion_owned.setdefault(id(owner), []).append(key)

    def _hand_construction(
        self, expr: ast.Expr, tree: Coercion, target: Type,
        covered: frozenset[tuple[int, ...]],
    ) -> bool:
        """Hand a construction's children their components of *target*;
        False for a node that is no construction."""
        if narrowing.holds_no_component(expr):
            return True
        if isinstance(expr, ast.ConstructorCall):
            name = _short(expr.name)
            for ctor, index, child in tree.parts:
                if _short(ctor) != name or index >= len(expr.args):
                    continue
                below = (frozenset(p[1:] for p in covered
                                   if len(p) > 1 and p[0] == index)
                         if tree.kind == "tuple" else frozenset())
                self._hand(expr, expr.args[index], child.target, below)
            return True
        if isinstance(expr, ast.ArrayLit):
            for _ctor, _index, child in tree.parts:
                for element in expr.elements:
                    self._hand(expr, element, child.target, frozenset())
            return True
        if not isinstance(expr, ast.FnCall):
            return False
        if expr.name == "map_insert" and len(expr.args) == 3:
            self._hand(expr, expr.args[0], target, frozenset())
            for label, index, child in tree.parts:
                arg = expr.args[1] if label == "key" else expr.args[2]
                self._hand(expr, arg, child.target, frozenset())
            return True
        if expr.name == "set_add" and len(expr.args) == 2:
            self._hand(expr, expr.args[0], target, frozenset())
            for _ctor, _index, child in tree.parts:
                self._hand(expr, expr.args[1], child.target, frozenset())
            return True
        return False

    def _coercion_leaf_guard(
        self, arg: ast.Expr, value: list[str], *, in_place: bool,
    ) -> list[str]:
        """The store-site guard of a scalar component a descent made a
        `Nat`: *value* (the component's translation) checked where the
        store's own in-place decision placed no guard (*in_place* False),
        on the same narrowing rule every sign guard reads."""
        handed = self._coercion_handed.get(id(arg))
        if handed is None or handed.expr is not arg:
            return value
        handed.consumed = True
        if in_place or handed.target != NAT:
            return value
        if not self._narrows_into_nat(arg):
            return value
        return self._emit_negative_i64_guard(
            value, trap=self._emit_component_coercion(at=arg))

    # -----------------------------------------------------------------
    # The deference to a function boundary's tuple-component guard (#746)
    # -----------------------------------------------------------------

    @contextmanager
    def _deferring(self, expr: ast.Expr,
                   covered: frozenset[tuple[int, ...]]) -> Iterator[None]:
        """While *expr* is translated, the tuple positions *covered* (the
        ones the receiving boundary's guard checks) are no position of its
        requirement, nor of any node its value flows through."""
        keys: list[int] = []
        if covered:
            for node in _flow_nodes(expr):
                if id(node) not in self._coercion_deferred:
                    self._coercion_deferred[id(node)] = covered
                    keys.append(id(node))
        try:
            yield
        finally:
            for key in keys:
                self._coercion_deferred.pop(key, None)

    def _callee_boundary_paths(
        self, call_target: str, index: int,
    ) -> frozenset[tuple[int, ...]]:
        paths = self._fn_boundary_coercion_paths.get(call_target, ())
        return paths[index] if index < len(paths) else frozenset()

    def _closure_boundary_paths(
        self, closure: ast.Expr, index: int,
    ) -> frozenset[tuple[int, ...]]:
        """The positions every closure that can be *closure*'s value checks
        at its parameter *index*: each guards its own formal's tuple
        components (#746), and a closure whose formal holds an `Int` where
        the closure type holds a `Nat` binds no `Nat` there to guard."""
        oracle = self._boundary_coercion_paths
        if oracle is None:
            return frozenset()
        if isinstance(closure, ast.AnonFn):
            if index < len(closure.params):
                return oracle(closure.params[index], None)
            return frozenset()
        if isinstance(closure, ast.SlotRef):
            return oracle(ast.NamedType(name=closure.type_name,
                                        type_args=closure.type_args), index)
        return frozenset()

    def _return_boundary_paths(
        self, return_te: ast.TypeExpr,
    ) -> frozenset[tuple[int, ...]]:
        oracle = self._boundary_coercion_paths
        return oracle(return_te, None) if oracle is not None else frozenset()

    # -----------------------------------------------------------------
    # Binders
    # -----------------------------------------------------------------

    def _binder_coercions(
        self, sources: tuple[narrowing.ComponentSource, ...], index: int,
        ctor_name: str, declared: Type | None,
    ) -> tuple[Coercion, ...]:
        typed = self._typed_program
        if typed is None or declared is None:
            return ()
        return narrowing.component_coercion(
            sources, index, ctor_name, declared, self._effective_type,
            self._type_of, typed.field_types_at, typed.constructors_of,
            self._narrows_into_nat)

    def _scrutinee_coercions(
        self, scrutinee: ast.Expr | None, declared: Type | None,
    ) -> tuple[Coercion, ...]:
        typed = self._typed_program
        if typed is None or declared is None or scrutinee is None:
            return ()
        return narrowing.value_coercion(
            scrutinee, declared, self._effective_type, typed.field_types_at,
            typed.constructors_of, self._narrows_into_nat)

    def _clause_coercions(
        self, payload_te: ast.TypeExpr | None, binder_te: object,
    ) -> tuple[Coercion, ...]:
        """A handler clause binder's walk: from the payload the operation
        declares to the type the binder declares, bar a container payload
        (:data:`vera.narrowing.CLAUSE_BINDER_UNGUARDED_HEADS`)."""
        if payload_te is None or not isinstance(binder_te, ast.TypeExpr):
            return ()
        payload = self._type_of(payload_te)
        declared = self._type_of(binder_te)
        if payload is None or declared is None:
            return ()
        head = getattr(declared, "name", None)
        if head in narrowing.CLAUSE_BINDER_UNGUARDED_HEADS:
            return ()
        tree = self._differing(payload, declared)
        if tree is None or tree.kind == "nat":
            return ()
        return (tree,)

    def _emit_binder_coercions(
        self, trees: tuple[Coercion, ...], local: int, *, at: ast.Node,
    ) -> list[str]:
        """The walk of a bound value, in *local* (and, for an array, the
        length in ``local + 1``), along each of *trees*."""
        out: list[str] = []
        for tree in trees:
            out.extend(self._emit_walk(tree, local, at=at))
        return out

    # -----------------------------------------------------------------
    # The walk
    # -----------------------------------------------------------------

    def _emit_component_coercion(self, *, at: ast.Node) -> list[str]:
        """The trap of one composite-coercion check, the one emitter of every
        check this module plants (``TRAP_EMITTERS``): a scalar narrowing's
        ``nat_guard``, recorded as the runtime half of
        ``component_coercion``."""
        return self._emit_trap(
            "wasm/coercion.py:_emit_component_coercion", at=at)

    def _walk_coerced_value(
        self, expr: ast.Expr, value: list[str], tree: Coercion,
    ) -> list[str]:
        """*value* (an opaque node's translation) walked along *tree*'s
        positions, left on the stack when every component conforms."""
        node = _unwrap_future(tree)
        if node.kind == "nat":
            return self._emit_negative_i64_guard(
                value, trap=self._emit_component_coercion(at=expr))
        pair = node.kind == "array"
        local = self.alloc_local("i32")
        if pair:
            length = self.alloc_local("i32")
            if length != local + 1:  # pragma: no cover — the allocator's order
                raise CodegenInvariantError(
                    "an array walk needs its two locals adjacent", expr)
            spill = [f"local.set {length}", f"local.set {local}"]
            reload = [f"local.get {local}", f"local.get {length}"]
        else:
            spill = [f"local.set {local}"]
            reload = [f"local.get {local}"]
        return [*value, *spill, *self._emit_walk(node, local, at=expr), *reload]

    def _emit_walk(self, tree: Coercion, local: int, *,
                   at: ast.Node) -> list[str]:
        """Check the value in *local* along *tree*; trap on a negative."""
        trap = self._emit_component_coercion(at=at)
        node = _unwrap_future(tree)
        if node.kind == "nat":
            return [f"local.get {local}", "i64.const 0", "i64.lt_s",
                    "if", *(f"  {line}" for line in trap), "end"]
        helper, allocates = self._request_coercion_helper(node)
        args = ([f"local.get {local}", f"local.get {local + 1}"]
                if node.kind == "array" else [f"local.get {local}"])
        check = [*args, f"call {helper}", "i32.eqz",
                 "if", *(f"  {line}" for line in trap), "end"]
        if not allocates:
            return check
        # The helper projects a `Map` or a `Set` into arrays, which
        # allocates: the walked value is reachable from this local alone, and
        # a local is no GC root, so it is rooted across the call and the
        # shadow stack put back after it.
        self.needs_alloc = True
        saved = self.alloc_local("i32")
        return ["global.get $gc_sp", f"local.set {saved}",
                *gc_shadow_push(local), *check,
                f"local.get {saved}", "global.set $gc_sp"]

    # -----------------------------------------------------------------
    # The walk helpers, generated per tree on the `$eq_*` model
    # -----------------------------------------------------------------

    def _request_coercion_helper(self, tree: Coercion) -> tuple[str, bool]:
        """``(name, allocates)`` of the helper walking *tree*, generated on
        the first request.  Signature by the walked value's representation:
        ``(i32) -> i32`` for a pointer or a handle, ``(i32, i32) -> i32``
        for an array's ``(ptr, len)``; the result is 1 when every component
        conforms."""
        node = self._fresh(_unwrap_future(tree))
        digest = hashlib.sha256(_tree_key(node).encode("utf-8")).hexdigest()
        name = f"$coerce_{digest[:16]}"
        allocates = self._walk_allocates(node, set())
        if name in self._coercion_helpers or name in self._coercion_pending:
            return name, allocates
        self._coercion_pending.add(name)
        try:
            self._coercion_helpers[name] = self._generate_coercion_helper(
                name, node, allocates)
        finally:
            self._coercion_pending.discard(name)
        if allocates:
            self.needs_alloc = True
        return name, allocates

    def _fresh(self, node: Coercion) -> Coercion:
        """An `again` node is the walk of its pair's own tree."""
        if node.kind != "again":
            return node
        fresh = self._differing(node.source, node.target)
        if fresh is None:  # pragma: no cover — a live pair has a tree
            raise CodegenInvariantError(
                "a recursive coercion's pair has no tree", None)
        return fresh

    def _walk_allocates(self, node: Coercion,
                        seen: set[tuple[Type, Type]]) -> bool:
        node = _unwrap_future(node)
        if node.kind in ("map", "set"):
            return True
        if node.kind == "again":
            if node.pair in seen:
                return False
            seen.add(node.pair)
            return self._walk_allocates(self._fresh(node), seen)
        return any(self._walk_allocates(child, seen)
                   for _c, _i, child in node.parts)

    def _generate_coercion_helper(
        self, name: str, node: Coercion, allocates: bool,
    ) -> str:
        pair = node.kind == "array"
        params = "(param i32) (param i32)" if pair else "(param i32)"
        locals_ = _HelperLocals(first=2 if pair else 1)
        if allocates:
            # The projections allocate, and the helper roots what they
            # return on the shadow stack, whose `$gc_sp` this declares.
            self.needs_alloc = True
        saved = locals_.new("i32") if allocates else None
        fail = (["local.get " + str(saved), "global.set $gc_sp"]
                if saved is not None else [])
        fail += ["i32.const 0", "return"]
        body: list[str] = []
        if saved is not None:
            body += ["global.get $gc_sp", f"local.set {saved}"]
        if node.kind == "array":
            body += self._walk_sequence(node.parts[0][2], 0, 1,
                                        _elem_name(node.source, 0), locals_,
                                        fail)
        elif node.kind in ("set", "map"):
            for label, _index, child in node.parts:
                op, slot = _PROJECTIONS[(node.kind, label)]
                elem = _elem_name(node.source, 0 if label in ("", "key") else 1)
                tag = self._map_wasm_tag(elem)
                if tag is None:  # pragma: no cover — refused at the map op
                    raise CodegenInvariantError(
                        f"no projection of a {elem} collection to walk", None)
                fn = self._collection_fn(op, **{slot: tag})
                seq_ptr = locals_.new("i32")
                seq_len = locals_.new("i32")
                if seq_len != seq_ptr + 1:  # pragma: no cover
                    raise CodegenInvariantError(
                        "a projected sequence needs adjacent locals", None)
                body += ["local.get 0", f"call {fn}", f"local.set {seq_len}",
                         f"local.set {seq_ptr}", *gc_shadow_push(seq_ptr)]
                body += self._walk_sequence(child, seq_ptr, seq_len, elem,
                                            locals_, fail)
        else:
            body += self._walk_fields(node, locals_, fail)
        if saved is not None:
            body += [f"local.get {saved}", "global.set $gc_sp"]
        body.append("i32.const 1")
        decls = "".join(f" (local {wt})" for wt in locals_.types)
        lines = [f"  (func {name} {params} (result i32){decls}"]
        lines += [f"    {line}" for line in body]
        lines.append("  )")
        return "\n".join(lines)

    def _walk_fields(self, node: Coercion, locals_: _HelperLocals,
                     fail: list[str]) -> list[str]:
        """The checks of a tuple's or a data type's differing fields, the
        value's pointer in local 0."""
        source = node.source
        out: list[str] = []
        groups: dict[str, tuple[int | None, list[Type]]] = {}
        if node.kind == "tuple":
            assert isinstance(source, AdtType)  # noqa: S101
            groups["Tuple"] = (None, list(source.type_args))
        else:
            typed = self._typed_program
            assert typed is not None  # noqa: S101
            layouts = self._ctor_layouts_of(source)
            for ctor, _index, _child in node.parts:
                if ctor in groups:
                    continue
                fields = typed.field_types_at(ctor, source)
                short = _short(ctor)
                layout = layouts.get(ctor) or layouts.get(short)
                if layout is None:
                    layout = next((lay for key, lay in layouts.items()
                                   if _short(key) == short), None)
                if fields is None or layout is None:
                    raise CodegenInvariantError(
                        f"no layout for constructor {short!r} of "
                        f"{pretty_type(source)} to walk", None)
                groups[ctor] = (layout.tag, list(fields))
        tag_local = None
        if node.kind == "data":
            tag_local = locals_.new("i32")
            out += ["local.get 0", "i32.load", f"local.set {tag_local}"]
        for ctor, (tag, field_types) in groups.items():
            names = [value_type_name(f) or "<opaque>" for f in field_types]
            offsets = self._concrete_field_layout(names)
            checks: list[str] = []
            for c, index, child in node.parts:
                if c != ctor:
                    continue
                offset, wt = offsets[index]
                checks += self._check_component(
                    child, wt, 0, offset, locals_, fail)
            if not checks:
                continue
            if tag_local is None:
                out += checks
            else:
                out += [f"local.get {tag_local}", f"i32.const {tag}",
                        "i32.eq", "if", *(f"  {line}" for line in checks),
                        "end"]
        return out

    def _ctor_layouts_of(
        self, source: Type,
    ) -> dict[str, ConstructorLayout]:
        name = getattr(source, "name", "")
        layouts = self._adt_ctor_layouts.get(name)
        if layouts is None:
            layouts = self._adt_ctor_layouts.get(name.rsplit(".", 1)[-1])
        if layouts is None:
            raise CodegenInvariantError(
                f"no constructor layouts for {name!r} to walk", None)
        return layouts

    def _check_component(
        self, child: Coercion, wt: str, ptr: int, offset: int,
        locals_: _HelperLocals, fail: list[str],
    ) -> list[str]:
        """Load the component at *offset* of the object *ptr* points to, laid
        out as *wt*, and check it along *child*: a `Nat` position by its
        sign, any other by its own helper."""
        node = _unwrap_future(child)
        if wt == "i32_pair":
            first = locals_.new("i32")
            length = locals_.new("i32")
            return [f"local.get {ptr}", f"i32.load offset={offset}",
                    f"local.set {first}",
                    f"local.get {ptr}", f"i32.load offset={offset + 4}",
                    f"local.set {length}",
                    *self._call_check(node, [f"local.get {first}",
                                             f"local.get {length}"], fail)]
        value = locals_.new(wt)
        load = [f"local.get {ptr}", f"{wt}.load offset={offset}",
                f"local.set {value}"]
        if node.kind == "nat":
            return [*load, f"local.get {value}", "i64.const 0", "i64.lt_s",
                    "if", *(f"  {line}" for line in fail), "end"]
        return [*load, *self._call_check(node, [f"local.get {value}"], fail)]

    def _call_check(self, node: Coercion, args: list[str],
                    fail: list[str]) -> list[str]:
        helper, _allocates = self._request_coercion_helper(node)
        return [*args, f"call {helper}", "i32.eqz",
                "if", *(f"  {line}" for line in fail), "end"]

    def _walk_sequence(
        self, child: Coercion, ptr_local: int, len_local: int,
        elem: str, locals_: _HelperLocals, fail: list[str],
    ) -> list[str]:
        """Every element of the sequence at ``(ptr_local, len_local)``
        checked along *child*, laid out as an array of *elem* is."""
        node = _unwrap_future(child)
        stride = self._element_mem_size(elem)
        if stride is None:  # pragma: no cover — an array of it exists
            raise CodegenInvariantError(
                f"no element layout for {elem} to walk", None)
        idx = locals_.new("i32")
        if self._is_pair_element_type(elem):
            first = locals_.new("i32")
            length = locals_.new("i32")
            check = [f"local.get {ptr_local}", f"local.get {idx}",
                     f"i32.const {stride}", "i32.mul", "i32.add",
                     "i32.load offset=4", f"local.set {length}",
                     *self._call_check(node, [f"local.get {first}",
                                              f"local.get {length}"], fail)]
            return element_sequence_loop(
                idx_local=idx, ptr_local=ptr_local, len_local=len_local,
                elem_local=first, load_wt="i32", load_op="i32.load",
                stride=stride, check=check)
        load_op = self._element_load_op(elem)
        if load_op is None:  # pragma: no cover — a pair is handled above
            raise CodegenInvariantError(
                f"no element load for {elem} to walk", None)
        wt = "i64" if load_op.startswith("i64") else "i32"
        element = locals_.new(wt)
        if node.kind == "nat":
            check = [f"local.get {element}", "i64.const 0", "i64.lt_s",
                     "if", *(f"  {line}" for line in fail), "end"]
        else:
            check = self._call_check(node, [f"local.get {element}"], fail)
        return element_sequence_loop(
            idx_local=idx, ptr_local=ptr_local, len_local=len_local,
            elem_local=element, load_wt=wt, load_op=load_op, stride=stride,
            check=check)


_short = narrowing._short_ctor


def _elem_name(collection: Type, index: int) -> str:
    """The value-type name of a collection's type argument *index*."""
    args = getattr(collection, "type_args", ())
    name = value_type_name(args[index]) if index < len(args) else None
    if name is None:  # pragma: no cover — a collection has its arguments
        raise CodegenInvariantError(
            f"no element type in {pretty_type(collection)} to walk", None)
    return name


def _flow_nodes(expr: ast.Expr) -> Iterator[ast.Expr]:
    """*expr* and every node its value flows through: the joins'
    arms (:func:`vera.narrowing.flow_arms`) down to their leaves."""
    yield expr
    arms = narrowing.flow_arms(expr)
    if arms:
        for arm in arms:
            yield from _flow_nodes(arm)
