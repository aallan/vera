"""Composite coercions into a `Nat` component (#1542's shape, #1695's line).

The checker admits a value whose type holds an `Int` where the position it
stands in holds a `Nat` (`Option<Int>` at an `Option<Nat>` formal, an array
literal of `Wrap<Int>` under an `Array<Wrap<Nat>>` binding), and records the
target on the coerced node alone.  The obligation table (#1695,
:mod:`vera.obligations.table`) lists every such component as a `nat_bind`
row with the component's path, by one rule over the typed program: the
requirement a node is held to is the component an enclosing construction
handed it, else the target the checker recorded, and the differing tree
against the node's own type (:func:`vera.narrowing.differing_tree`) names
the positions.  This module is the LOWERING of those rows:

* a scalar child of a construction the requirement makes a `Nat` has a
  head row at the child, guarded where it is stored by the sign guard
  (``_guard_nat_narrowing``), under this module's emitter where the
  requirement reached it from the construction alone (``Row.handed``);
* an OPAQUE value (a slot, a call's result, an index, a field read) with
  rows below its head has its first such row carry the tree
  (``Row.tree``), and its value is walked at run time along the tree's
  positions after it is translated (``_walk_coerced_value``), by a helper
  generated per tree on the ``$eq_*`` model, and a negative component
  traps exactly as a scalar narrowing does (``nat_guard``);
* a pattern binder, a destructure component and a handler clause binder
  declared narrower than what they bind walk the bound value the same way
  (``_emit_binder_walks``), each walk one row.

A tuple position a function boundary's component guard checks (#746) is a
row the boundary's entry row answers, and is no position of the walk: the
table prunes it from the tree (:func:`vera.narrowing.without_paths`), so
the two guards never double.  A `Map` or `Set` walk reads the collection
through the same projections a program's own ``map_keys`` / ``map_values``
/ ``set_to_array`` call does, so its guard is O(n) and allocates; the
walked value and every projected array are rooted on the GC shadow stack
across it.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from vera import ast, narrowing
from vera.narrowing import Coercion
from vera.obligations.table import Evaluation, Row
from vera.skip import CodegenInvariantError
from vera.types import AdtType, Type, pretty_type, value_type_name
from vera.wasm.helpers import element_sequence_loop, gc_shadow_push

if TYPE_CHECKING:
    from collections.abc import Mapping

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
        def _emit_trap(self, emitter: str, *, row: Row | None,
                       at: ast.Node | None = None,
                       message: str | None = None,
                       path: tuple[str, ...] = ()) -> list[str]: ...
        def _emit_negative_i64_guard(self, value: list[str], *,
                                     trap: list[str]) -> list[str]: ...
        def _rows(self, node: ast.Node, kind: str,
                  path: tuple[str, ...] | None = None, *,
                  evaluation: Evaluation | None = None) -> list[Row]: ...
        def _checked(self, row: Row | None) -> bool: ...
        def _type_of(self, node: ast.Node) -> Type | None: ...
        def _map_wasm_tag(self, vera_type: str | None) -> str | None: ...
        def _collection_fn(self, op: str, **tags: str) -> str: ...
        def _element_mem_size(self, elem_type: str) -> int | None: ...
        def _element_load_op(self, elem_type: str) -> str | None: ...
        def _is_pair_element_type(self, elem_type: str) -> bool: ...
        def _concrete_field_layout(
            self, field_type_names: list[str]) -> list[tuple[int, str]]: ...

        _adt_ctor_layouts: dict[str, dict[str, ConstructorLayout]]

    def _init_component_coercion(self) -> None:
        #: The generated walk helpers, by name, merged into the module.
        self._coercion_helpers: dict[str, str] = {}
        self._coercion_pending: set[str] = set()
        #: The per-pair differing trees, computed once each.
        self._coercion_trees: dict[tuple[Type, Type], Coercion | None] = {}

    # -----------------------------------------------------------------
    # The rows a walk lowers
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

    def _walk_rows(self, node: ast.Node) -> list[Row]:
        """The rows at *node* a walk lowers (#1695): each `nat_bind` row
        below the head that carries a tree and a check of its own."""
        return [row for row in self._rows(node, "nat_bind")
                if row.path and row.tree is not None and self._checked(row)]

    def _emit_binder_walks(
        self, rows: list[Row], local: int, *, at: ast.Node,
    ) -> list[str]:
        """The walk of a bound value, in *local* (and, for an array, the
        length in ``local + 1``), along each of *rows*' trees."""
        out: list[str] = []
        for row in rows:
            assert row.tree is not None  # noqa: S101 — `_walk_rows`
            out.extend(self._emit_walk(row.tree, local, row=row, at=at))
        return out

    # -----------------------------------------------------------------
    # The walk
    # -----------------------------------------------------------------

    def _emit_component_coercion(
        self, *, row: Row, at: ast.Node | None = None,
    ) -> list[str]:
        """The trap of one composite-coercion check, the one emitter of every
        check this module plants (``TRAP_EMITTERS``): a scalar narrowing's
        ``nat_guard``, recorded as the runtime half of
        ``component_coercion``, by its row (#1695)."""
        return self._emit_trap(
            "wasm/coercion.py:_emit_component_coercion", row=row, at=at)

    def _walk_coerced_value(
        self, expr: ast.Expr, value: list[str], row: Row,
    ) -> list[str]:
        """*value* (an opaque node's translation) walked along *row*'s
        tree, left on the stack when every component conforms."""
        tree = row.tree
        assert tree is not None  # noqa: S101 — `_walk_rows`
        node = _unwrap_future(tree)
        if node.kind == "nat":
            return self._emit_negative_i64_guard(
                value, trap=self._emit_component_coercion(row=row, at=expr))
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
        return [*value, *spill,
                *self._emit_walk(node, local, row=row, at=expr), *reload]

    def _emit_walk(self, tree: Coercion, local: int, *, row: Row,
                   at: ast.Node | None = None) -> list[str]:
        """Check the value in *local* along *tree*; trap on a negative."""
        trap = self._emit_component_coercion(row=row, at=at)
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
