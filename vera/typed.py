"""The typed program: every type derived once (#1679, ROADMAP Stage 26).

The checker types every node of the entry file, of each module the program
reaches and of the prelude, and records each generic call's instantiation,
the type arguments it inferred there.  Those records are keyed by a node's
identity (:attr:`vera.ast.Node.node_id`), not its span: a span cannot tell a
clone's node from its template's or from another clone's.

From them this pass derives, once, the set of instances the program needs:
each generic call in a body that is not generic fixes an instance, and each
generic call inside an instance's template fixes another, its recorded type
arguments read under the instance's substitution, transitively.  The
verifier and code generation read this one set.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass, field, fields
from typing import Any

from vera import ast
from vera.types import (
    AdtType,
    FunctionType,
    PrimitiveType,
    RefinedType,
    Type,
    strip_builtin_typevar_marker,
    substitute,
)


@dataclass(frozen=True)
class Instantiation:
    """A generic call's instantiation, as the checker inferred it.

    *callee* is the link name of the generic declaration the call binds to
    (:attr:`vera.binding.DeclId.link_name`), *forall_vars* the callee's type
    variables in its declared order, and *mapping* the type each variable
    the call fixed is instantiated at.  A type in *mapping* can name a type
    variable of the function the call is written in, which an instantiation
    of that function binds."""

    callee: str
    forall_vars: tuple[str, ...]
    mapping: Mapping[str, Type]


#: The type a variable no argument fixes is instantiated at: a type with a
#: runtime representation, whose clone's code is the same whatever it is
#: named, since nothing in the generic reads a value of it.
PHANTOM_TYPE: Type = PrimitiveType("Bool")


def type_arg_name(ty: Type) -> str:
    """The canonical name of the type argument *ty*, as a clone's name and
    its substitution spell it: a refinement by its base, an alias already
    resolved (the checker's types hold none), a variable left unbound by
    the phantom type (:data:`PHANTOM_TYPE`)."""
    if isinstance(ty, RefinedType):
        return type_arg_name(ty.base)
    if isinstance(ty, PrimitiveType):
        return ty.name
    if isinstance(ty, AdtType):
        if not ty.type_args:
            return ty.name
        return f"{ty.name}<{', '.join(type_arg_name(a) for a in ty.type_args)}>"
    if isinstance(ty, FunctionType):
        params = ", ".join(type_arg_name(p) for p in ty.params)
        return f"fn({params} -> {type_arg_name(ty.return_type)})"
    return type_arg_name(PHANTOM_TYPE)


# =====================================================================
# The templates: every generic declaration, and the calls in its scope
# =====================================================================


@dataclass
class Template:
    """A generic declaration of the linked program, under its link name.

    *ancestor* is the link name of the nearest generic declaration it is a
    ``where`` helper of: an instance of it exists only under an instance of
    that one, whose substitution its body reads too.  ``None`` for a
    top-level generic and for a generic helper of functions that are not
    generic, each of which is instantiated on its own.  *calls* are the
    recorded generic calls in its scope: its body, its contracts and its
    signature, and those of the ``where`` helpers in it that are not
    generic; a generic helper's calls are the helper's own."""

    decl: ast.FnDecl
    origin: tuple[str, ...] | None
    ancestor: str | None
    calls: list[ast.Node] = field(default_factory=list)


def _calls_in(node: object, into: list[ast.Node],
              recorded: Mapping[int, Instantiation]) -> None:
    """Append each recorded generic call under *node*, a declaration's
    ``where`` helpers left out (each is a scope of its own or a part of its
    parent's, which :func:`_index` walks)."""
    stack: list[object] = [node]
    while stack:
        item = stack.pop()
        if isinstance(item, ast.Node):
            if (isinstance(item, (ast.FnCall, ast.ModuleCall))
                    and item.node_id in recorded):
                into.append(item)
            for f in fields(item):
                if f.name in ("span", "where_fns") or f.metadata.get("identity"):
                    continue
                stack.append(getattr(item, f.name))
        elif isinstance(item, tuple):
            stack.extend(reversed(item))


def _index(decl: ast.FnDecl, origin: tuple[str, ...] | None,
           ancestor: str | None, scope: list[ast.Node],
           templates: dict[str, Template],
           recorded: Mapping[int, Instantiation]) -> None:
    """Index *decl* and its ``where`` helpers: a generic one as a template
    whose scope its calls join, any other into the enclosing *scope*."""
    own: list[ast.Node] = scope
    inner: str | None = ancestor
    if decl.forall_vars:
        template = Template(decl, origin, ancestor)
        templates[decl.name] = template
        own, inner = template.calls, decl.name
    _calls_in(replace_where(decl), own, recorded)
    for helper in decl.where_fns or ():
        _index(helper, origin, inner, own, templates, recorded)


def replace_where(decl: ast.FnDecl) -> ast.FnDecl:
    """*decl* without its ``where`` helpers, for a walk of its own scope."""
    from dataclasses import replace
    return replace(decl, where_fns=None) if decl.where_fns else decl


def _programs(
    linked_program: ast.Program,
    modules: Sequence[tuple[tuple[str, ...], ast.Program]],
    prelude: Sequence[ast.TopLevelDecl],
) -> Iterator[tuple[tuple[str, ...] | None, ast.FnDecl]]:
    """Every top-level function of the linked program, its modules and its
    prelude, with the path of the module that declares it (``None`` for the
    entry file and the prelude)."""
    for tld in (*prelude, *linked_program.declarations):
        if isinstance(tld.decl, ast.FnDecl):
            yield None, tld.decl
    for path, program in modules:
        for tld in program.declarations:
            if isinstance(tld.decl, ast.FnDecl):
                yield path, tld.decl


# =====================================================================
# The instances
# =====================================================================


@dataclass(eq=False)
class Instance:
    """One instantiation of a generic declaration the program needs.

    *key* is the declaration's link name and *args* the canonical names of
    its type arguments in its declared order.  A ``where`` helper of a
    generic declaration is instantiated under an instance of that one, its
    *parent*.  *sigma* is the substitution its body is read under: its own
    variables and its ancestors', by the names the checker's types give
    them."""

    key: str
    args: tuple[str, ...]
    parent: Instance | None
    origin: tuple[str, ...] | None
    sigma: dict[str, Type]
    #: The instance each recorded call in the instance's scope calls, by
    #: the call's identity in the template.
    calls: dict[int, Instance] = field(default_factory=dict)
    #: The clone: the template under *sigma*, named :attr:`name`, every node
    #: its own (:func:`build`).
    clone: ast.FnDecl | None = None

    @property
    def ident(self) -> tuple[object, ...]:
        """The instance's identity: its key, its arguments, its parent's."""
        return (self.key, self.args,
                self.parent.ident if self.parent is not None else None)

    def compiled_nodes(self) -> Iterator[ast.Node]:
        """Every node of the clone this instance compiles: the clone's own
        and its ``where`` helpers', a generic helper's left out, since the
        helper's instances compile it."""
        assert self.clone is not None  # noqa: S101
        stack: list[object] = [self.clone]
        while stack:
            item = stack.pop()
            if isinstance(item, ast.Node):
                yield item
                for f in fields(item):
                    if f.name == "span" or f.metadata.get("identity"):
                        continue
                    value = getattr(item, f.name)
                    if f.name == "where_fns" and value:
                        value = tuple(h for h in value if not h.forall_vars)
                    stack.append(value)
            elif isinstance(item, tuple):
                stack.extend(item)

    @property
    def name(self) -> str:
        """The clone's name: the declaration's link name and its arguments,
        for a helper of a generic under its parent clone's name, as code
        generation names the helper it hoists out of that clone."""
        from vera.monomorphize import Monomorphizer, where_helper_name
        base = self.key
        if self.parent is not None:
            base = f"{self.parent.name}$where${where_helper_name(self.key)}"
        return Monomorphizer._mangle_fn_name(base, self.args)


def ground(ty: Type) -> Type:
    """*ty* as an instance is built at it: a refinement by its base, and a
    type variable left unbound, or an unknown, by :data:`PHANTOM_TYPE`."""
    if isinstance(ty, RefinedType):
        return ground(ty.base)
    if isinstance(ty, AdtType):
        return AdtType(ty.name, tuple(ground(a) for a in ty.type_args))
    if isinstance(ty, FunctionType):
        return FunctionType(tuple(ground(p) for p in ty.params),
                            ground(ty.return_type), ty.effect)
    if isinstance(ty, PrimitiveType):
        return ty
    return PHANTOM_TYPE


def _own_args(template: Template, record: Instantiation,
              sigma: Mapping[str, Type]) -> list[Type]:
    """The type arguments *record* fixes for *template*'s variables, read
    under *sigma*, in the declaration's order.

    A record names the variables as the callee's signature does, which for
    a prelude function is the built-in registry's (``T#b``): unmarked, they
    are the declaration's names, and where they are not they are taken by
    position, the order both declare them in.  A variable no argument fixes
    is instantiated at :data:`PHANTOM_TYPE`."""
    decl_vars = template.decl.forall_vars or ()
    unmarked = [strip_builtin_typevar_marker(v) for v in record.forall_vars]
    if set(unmarked) == set(decl_vars):
        recorded_as = dict(zip(unmarked, record.forall_vars))
    else:
        recorded_as = dict(zip(decl_vars, record.forall_vars))
    types: list[Type] = []
    for var in decl_vars:
        ty = record.mapping.get(recorded_as.get(var, ""))
        types.append(PHANTOM_TYPE if ty is None
                     else ground(substitute(ty, dict(sigma))))
    return types


def derive_instances(
    linked_program: ast.Program,
    modules: Sequence[tuple[tuple[str, ...], ast.Program]],
    prelude: Sequence[ast.TopLevelDecl],
    recorded: Mapping[int, Instantiation],
) -> tuple[dict[str, Template], list[Instance], dict[int, Instance]]:
    """The templates of the linked program, the instances it needs, in the
    order they are reached, and the instance each recorded call in a body
    that is not generic calls.

    Each recorded call in a body that is not generic fixes an instance at
    its recorded arguments; each recorded call in an instance's scope fixes
    one at its recorded arguments read under the instance's substitution,
    under the instance of the callee's generic ancestor the chain holds."""
    templates: dict[str, Template] = {}
    seeds: list[ast.Node] = []
    for origin, decl in _programs(linked_program, modules, prelude):
        _index(decl, origin, None, seeds, templates, recorded)

    instances: list[Instance] = []
    by_ident: dict[tuple[object, ...], Instance] = {}
    seed_targets: dict[int, Instance] = {}

    def reach(call: ast.Node, within: Instance | None) -> Instance | None:
        record = recorded[call.node_id]  # type: ignore[index]
        template = templates.get(record.callee)
        if template is None:
            return None
        sigma: dict[str, Type] = dict(within.sigma) if within else {}
        types = _own_args(template, record, sigma)
        own = dict(zip(template.decl.forall_vars or (), types))
        parent: Instance | None = None
        if template.ancestor is not None:
            parent = within
            while parent is not None and parent.key != template.ancestor:
                parent = parent.parent
            if parent is None:
                return None
        args = tuple(type_arg_name(t) for t in types)
        ident = (record.callee, args,
                 parent.ident if parent is not None else None)
        found = by_ident.get(ident)
        if found is None:
            base = dict(parent.sigma) if parent is not None else {}
            found = Instance(record.callee, args, parent, template.origin,
                             {**base, **own})
            by_ident[ident] = found
            instances.append(found)
        return found

    for call in seeds:
        target = reach(call, None)
        if target is not None:
            seed_targets[call.node_id] = target  # type: ignore[index]
    done = 0
    while done < len(instances):
        inst = instances[done]
        done += 1
        for call in templates[inst.key].calls:
            target = reach(call, inst)
            if target is not None:
                inst.calls[call.node_id] = target  # type: ignore[index]
    return templates, instances, seed_targets


# =====================================================================
# The one link
# =====================================================================


def link_checked(program: ast.Program, modules: Sequence[object],
                 binding: object, prelude: Sequence[ast.TopLevelDecl],
                 prelude_source: str) -> object:
    """The linked program (:class:`vera.binding.Linked`) of a checked
    *program*, from the binding its check bound and the prelude
    declarations that binding covers, so the nodes the checker typed are the
    nodes the verifier and code generation read."""
    from dataclasses import replace

    from vera.binding import PRELUDE, Binding, DeclId, Linked, _link_fn, link
    from vera.resolver import ResolvedModule

    assert isinstance(binding, Binding)  # noqa: S101
    mods = [m for m in modules if isinstance(m, ResolvedModule)]
    linked_program, linked_modules = link(program, mods, binding)
    return Linked(
        program=linked_program,
        modules=linked_modules,
        prelude=tuple(
            replace(tld, decl=_link_fn(tld.decl, DeclId(PRELUDE, tld.decl.name),
                                       binding.calls))
            if isinstance(tld.decl, ast.FnDecl) else tld
            for tld in prelude
        ),
        prelude_source=prelude_source,
        binding=binding,
    )


# =====================================================================
# The typed program
# =====================================================================


@dataclass
class TypedProgram:
    """A checked program, linked once, with every instance it needs built
    once and every node of every clone typed (#1679).

    *semantic* and *target* hold the checker's type and target of every
    expression by node identity: a template's from the check, a clone's
    node the template's under the instance's substitution.  *call_targets*
    maps every generic call of a body the program compiles, a clone's
    included, to the instance it calls; *origin* each clone node to the
    template node it was built from.  The verifier and code generation read
    this, and derive no type and no instantiation of their own."""

    program: ast.Program
    modules: list[object]
    linked: object
    templates: dict[str, Template]
    instances: list[Instance]
    semantic: dict[int, Type]
    target: dict[int, Type]
    call_targets: dict[int, Instance]
    origin: dict[int, int]

    def semantic_type(self, node: ast.Node) -> Type | None:
        """The checker's type of *node*, or ``None`` for a node it did not
        type (a pattern, a type expression, a node built after the check)."""
        return None if node.node_id is None else self.semantic.get(node.node_id)

    def target_type(self, node: ast.Node) -> Type | None:
        """The type *node* was checked against, or ``None``."""
        return None if node.node_id is None else self.target.get(node.node_id)

    def call_target(self, call: ast.Node) -> Instance | None:
        """The instance the generic call *call* calls, or ``None`` for a call
        that is not generic."""
        return None if call.node_id is None else self.call_targets.get(call.node_id)


def _renumber(node: ast.FnDecl, origin: dict[int, int]) -> ast.FnDecl:
    """*node* rebuilt with a fresh identity for every node in it, each
    recorded in *origin* against the template node it stands for."""
    from dataclasses import replace

    memo: dict[int, object] = {}

    def copy(item: object) -> object:
        if isinstance(item, ast.Node):
            done = memo.get(id(item))
            if done is not None:
                return done
            changes: dict[str, Any] = {
                f.name: copy(getattr(item, f.name)) for f in fields(item)
                if f.name != "span" and not f.metadata.get("identity")
            }
            fresh = ast.fresh_node_id()
            if item.node_id is not None:
                origin[fresh] = origin.get(item.node_id, item.node_id)
            changes["node_id"] = fresh
            new = replace(item, **changes)
            memo[id(item)] = new
            return new
        if isinstance(item, tuple):
            return tuple(copy(x) for x in item)
        return item

    out = copy(node)
    assert isinstance(out, ast.FnDecl)  # noqa: S101
    return out


def _helper_in(fn: ast.FnDecl, name: str) -> ast.FnDecl | None:
    """The ``where`` helper named *name* at any depth of *fn*."""
    for helper in fn.where_fns or ():
        if helper.name == name:
            return helper
        found = _helper_in(helper, name)
        if found is not None:
            return found
    return None


def _walk(node: object) -> Iterator[ast.Node]:
    stack: list[object] = [node]
    while stack:
        item = stack.pop()
        if isinstance(item, ast.Node):
            yield item
            stack.extend(getattr(item, f.name) for f in fields(item)
                         if f.name != "span" and not f.metadata.get("identity"))
        elif isinstance(item, tuple):
            stack.extend(item)


def build(program: ast.Program, modules: Sequence[object],
          artifacts: object) -> TypedProgram:
    """The typed program of the checked *program*, from its check's
    *artifacts* (:class:`vera.checker.core.CheckArtifacts`).

    Each instance is built once, in the order it was reached, from its
    template (a helper of a generic from the copy in its parent's clone),
    renumbered, and typed by its substitution; the recursion each clone's
    binder names are counted in is the declaring module's naming
    environment (#1208)."""
    from dataclasses import replace

    from vera.binding import Linked
    from vera.monomorphize import MonoContext, Monomorphizer
    from vera.naming import AliasEnv, alias_env_from_program

    arts = artifacts
    linked = link_checked(
        program, modules, arts.binding,  # type: ignore[attr-defined]
        arts.prelude, arts.prelude_source)  # type: ignore[attr-defined]
    assert isinstance(linked, Linked)  # noqa: S101
    recorded = arts.instantiations  # type: ignore[attr-defined]
    templates, instances, seed_targets = derive_instances(
        linked.program, [(m.path, m.program) for m in linked.modules],
        linked.prelude, recorded)
    checked_semantic: dict[int, Type] = arts.node_semantic_types  # type: ignore[attr-defined]
    checked_target: dict[int, Type] = arts.node_target_types  # type: ignore[attr-defined]
    semantic = dict(checked_semantic)
    target = dict(checked_target)
    call_targets: dict[int, Instance] = dict(seed_targets)
    origin: dict[int, int] = {}
    envs: dict[tuple[str, ...] | None, AliasEnv] = {
        None: alias_env_from_program(replace(
            linked.program,
            declarations=(*linked.prelude, *linked.program.declarations))),
        **{m.path: alias_env_from_program(m.program) for m in linked.modules},
    }
    mono = Monomorphizer(MonoContext({}, {}, {}, {}, {}, {}, {}))
    for inst in instances:
        if inst.parent is None:
            template: ast.FnDecl | None = templates[inst.key].decl
        else:
            assert inst.parent.clone is not None  # noqa: S101
            template = _helper_in(inst.parent.clone, inst.key)
        assert template is not None, inst.key  # noqa: S101
        clone = mono.monomorphize_fn(template, inst.args, envs[inst.origin])
        clone = _renumber(replace(clone, name=inst.name), origin)
        inst.clone = clone
        for node in _walk(clone):
            if node.node_id is None:
                continue
            source = origin.get(node.node_id)
            if source is None:
                continue
            ty = checked_semantic.get(source)
            if ty is not None:
                semantic[node.node_id] = substitute(ty, inst.sigma)
            at = checked_target.get(source)
            if at is not None:
                target[node.node_id] = substitute(at, inst.sigma)
            callee = inst.calls.get(source)
            if callee is not None:
                call_targets[node.node_id] = callee
    return TypedProgram(
        program=program, modules=list(modules), linked=linked,
        templates=templates, instances=instances, semantic=semantic,
        target=target, call_targets=call_targets, origin=origin)
