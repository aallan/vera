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
from typing import TYPE_CHECKING, Any

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

if TYPE_CHECKING:
    from vera.binding import Binding, Linked
    from vera.checker.core import CheckArtifacts
    from vera.environment import TypeEnv
    from vera.errors import Diagnostic
    from vera.resolver import ResolvedModule


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
        from vera.monomorphize import Monomorphizer
        base = self.key
        if self.parent is not None:
            # The helper's link name is its generic ancestor's key and the
            # chain of helpers down to it (`f$where$g$where$h`), and code
            # generation hoists it under the parent clone along that chain.
            assert self.key.startswith(self.parent.key + "$where$")  # noqa: S101
            base = self.parent.name + self.key[len(self.parent.key):]
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


def link_checked(program: ast.Program, modules: Sequence[ResolvedModule],
                 binding: Binding | None,
                 prelude: Sequence[ast.TopLevelDecl],
                 prelude_source: str) -> Linked:
    """The linked program (:class:`vera.binding.Linked`) of a checked
    *program*, from the binding its check bound and the prelude
    declarations that binding covers, so the nodes the checker typed are the
    nodes the verifier and code generation read."""
    from dataclasses import replace

    from vera.binding import PRELUDE, DeclId, Linked, _link_fn, link

    assert binding is not None  # every check binds  # noqa: S101
    linked_program, linked_modules = link(program, modules, binding)
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


@dataclass
class Derivation:
    """A checked program linked once, with the generic declarations it
    holds and the instances it needs (:func:`derive_instances`): derived by
    its check (:func:`derive_checked`), which judges each instance there,
    and read by :func:`build`, which builds their clones."""

    linked: Linked
    templates: dict[str, Template]
    instances: list[Instance]
    #: The instance each recorded call in a body that is not generic calls.
    seed_targets: dict[int, Instance]
    #: The typed program :func:`build` built from this derivation.
    typed: TypedProgram | None = None


def derive_checked(program: ast.Program, modules: Sequence[ResolvedModule],
                   binding: Binding | None,
                   prelude: Sequence[ast.TopLevelDecl], prelude_source: str,
                   recorded: Mapping[int, Instantiation]) -> Derivation:
    """The :class:`Derivation` of a checked *program*: its one link, and
    the instances its *recorded* instantiations reach."""
    linked = link_checked(program, modules, binding, prelude, prelude_source)
    templates, instances, seed_targets = derive_instances(
        linked.program, [(m.path, m.program) for m in linked.modules],
        linked.prelude, recorded)
    return Derivation(linked, templates, instances, seed_targets)


# =====================================================================
# The judgments an instantiation decides (#1679)
# =====================================================================
#
# A rule whose answer depends on what a generic is instantiated at is
# judged here, once the check has inferred every call's type arguments and
# the instances they reach are derived: an ability constraint (E613), a
# `State<T>` cell no cell lowers at (E607), an `Exn<E>` payload no tag
# lowers at (E612), a handler state declaration its cell diverges from
# (E533), and a Map or Set operation over an Array or zero-size key, value
# or element (E135).  Code generation and the verifier made each of these
# per clone, after `vera check` had accepted the program.  Each is reported
# at the ROOT call, the call in a body that is not generic whose type
# arguments reach the failing instance, with the chain from it named,
# since that call is where the type argument is chosen.


@dataclass(frozen=True)
class HandlerCell:
    """A ``handle[State<T>]`` or ``handle[Exn<E>]`` expression's cell as the
    check resolved it: the effect, its type argument, and for ``State`` the
    type the handler's state is declared at (``None`` where it declares
    none).  A cell typed by a type parameter is judged at each instance of
    the generic it is written in (:func:`judge`)."""

    effect: str
    cell: Type
    state: Type | None = None


def _scope(decl: ast.FnDecl) -> Iterator[ast.Node]:
    """Every node of *decl*'s own scope: its signature, contracts and body,
    and those of each ``where`` helper that is not generic, recursively.  A
    generic helper is a scope of its own."""
    yield from _walk(replace_where(decl))
    for helper in decl.where_fns or ():
        if not helper.forall_vars:
            yield from _scope(helper)


@dataclass(frozen=True)
class _Refusal:
    """One judgment an instance fails: its code, what fails (the clause a
    message ends with), and the property the root call's type argument
    needs.  A *fix* of ``None`` is the root call's own: instantiate it where
    the judgment holds."""

    code: str
    what: str
    needs: str = ""
    fix: str | None = None


_ABILITY_RATIONALE = (
    "A generic's ability constraint holds for every type argument it is "
    "instantiated at.  The check infers each call's type arguments and "
    "holds each constraint against the type it is instantiated at, at the "
    "call whose arguments choose it.")
_CELL_RATIONALE = (
    "A State<T> cell's value crosses host imports that carry one word, so a "
    "cell whose value is a (ptr, len) pair (String, Array<T>) or has no "
    "representation (Unit, Never) is not lowered.  A cell typed by a type "
    "parameter is judged at each type it is instantiated at, at the call "
    "whose arguments choose it.")
_PAYLOAD_RATIONALE = (
    "An Exn<E> payload is thrown as a WebAssembly tag's parameters, so a "
    "payload with no representation (Unit, Never) has nothing to throw.  A "
    "payload typed by a type parameter is judged at each type it is "
    "instantiated at, at the call whose arguments choose it.")
_STATE_RATIONALE = (
    "For the builtin State effect the handler state declaration IS the "
    "State<T> cell, and a generic handler's cell is its type parameter's "
    "instantiation, so a declaration that names another type diverges from "
    "the cell where the instantiation makes them differ: the obligations "
    "and the runtime guards key off the cell.")
_COLLECTION_RATIONALE = (
    "A Map or Set operation is lowered through an operation generated for "
    "the representation of its key, value or element, and none is generated "
    "for an Array (a (ptr, len) pair) or for a type with no value (Unit, or "
    "a Future of one).  A component typed by a type parameter is judged at "
    "each type it is instantiated at, at the call whose arguments choose "
    "it.")


def _bare(link_name: str) -> str:
    from vera.binding import bare_name
    return bare_name(link_name)


def _type_text(ty: Type) -> str:
    from vera.types import pretty_type
    return pretty_type(ty)


def _ability_refusals(template: Template, inst: Instance,
                      env: TypeEnv) -> list[_Refusal]:
    """The ability constraints of *template* its instance *inst* does not
    satisfy: ``Eq`` derived structurally over *env*'s data types, the
    others by :data:`vera.lowering.ABILITY_TYPES`."""
    from vera.checker.eq_ability import is_eq_derivable
    from vera.lowering import ABILITY_TYPES, EQ_TYPES_PHRASE, ability_lowerable

    found: list[_Refusal] = []
    for constraint in template.decl.forall_constraints or ():
        ability = constraint.ability_name
        ty = inst.sigma.get(constraint.type_var)
        if ty is None or not ability_lowerable(ability):
            continue  # an ability no code lowers is E340 at the constraint
        if ability == "Eq":
            if is_eq_derivable(ty, env):
                continue
            phrase = EQ_TYPES_PHRASE
        else:
            types, phrase = ABILITY_TYPES[ability]
            if type_arg_name(ty) in types:
                continue
        found.append(_Refusal(
            "E613",
            f"type '{_type_text(ty)}' does not satisfy ability '{ability}', "
            f"which '{_bare(inst.key)}' requires of {constraint.type_var}: "
            f"only {phrase} support {ability}", f"supports '{ability}'"))
    return found


def _cell_refusals(node: ast.HandleExpr, record: HandlerCell,
                   inst: Instance, template: Template,
                   source: str) -> list[_Refusal]:
    """What the handler *node*, written in *template*, fails at its
    instance *inst*: a cell or payload no instantiation lowers at this
    type, or a state declared at a type its cell is not.  A handler that
    holds no type parameter was judged where it is written (E340, E336)."""
    from vera.lowering import exn_payload_type_lowerable, state_cell_type_lowerable
    from vera.types import (
        contains_typevar,
        is_pair_represented,
        state_cell_decl_equal,
    )

    generic_cell = contains_typevar(record.cell)
    if not generic_cell and (record.state is None
                             or not contains_typevar(record.state)):
        return []
    cell = substitute(record.cell, inst.sigma)
    written, shown = _type_text(record.cell), _type_text(cell)
    if record.effect == "Exn":
        if generic_cell and not exn_payload_type_lowerable(cell):
            return [_Refusal(
                "E612",
                f"its Exn<{written}> payload is an Exn<{shown}>, which code "
                f"generation cannot lower: {shown} has no runtime "
                f"representation to throw", "an Exn payload carries")]
        return []
    if generic_cell and not state_cell_type_lowerable(cell):
        why = ("its value is a (ptr, len) pair, and a cell's host imports "
               "carry one word" if is_pair_represented(cell)
               else f"{shown} has no runtime representation to store")
        return [_Refusal(
            "E607",
            f"its State<{written}> cell is a State<{shown}>, which code "
            f"generation cannot lower: {why}", "a State cell holds")]
    if record.state is None:
        return []
    declared = substitute(record.state, inst.sigma)
    if state_cell_decl_equal(cell, declared):
        return []
    return [_Refusal(
        "E533",
        f"its handler's state is declared @{_type_text(declared)} but its "
        f"cell is State<{shown}>",
        fix=_state_fix(node, record, template, source))]


def _state_fix(node: ast.HandleExpr, record: HandlerCell,
               template: Template, source: str) -> str:
    """E533's fix: declare the handler's state at its cell's type, so every
    instance's state is its cell.  Written as a replacement where the cell
    is a type parameter the generic holds a parameter of, whose slot then
    initialises the state."""
    from vera.types import TypeVar

    cell = record.cell
    declared = (_source_text(source, node.state.span)
                if node.state is not None else None)
    if (isinstance(cell, TypeVar) and declared is not None
            and any(isinstance(p, ast.NamedType) and p.name == cell.name
                    and not p.type_args for p in template.decl.params)):
        state = f"@{cell.name} = @{cell.name}.0"
        if declared.startswith("(") and declared.endswith(")"):
            state = f"({state})"
        return (f"Declare the handler's state at its cell's type, the type "
                f"parameter {cell.name}, so every instantiation's state is "
                f"its cell: replace '{declared}' with '{state}'.")
    return (f"Declare the handler's state at its cell's type, "
            f"@{_type_text(cell)}, so every instantiation's state is its "
            f"cell.")


def _component_refusals(
    node: ast.FnCall, types: Mapping[int, Type],
    sigma: Mapping[str, Type] | None,
) -> list[tuple[str, Type, str]]:
    """The components of the Map or Set operation *node* code generation
    lowers no operation over, as (role, type, reason), read from the check's
    *types*: under *sigma*, an instance's, the components that hold a type
    parameter, and where *sigma* is ``None`` the ones that hold none."""
    from vera.lowering import COLLECTION_COMPONENTS, collection_component_refusal
    from vera.types import base_type, contains_typevar

    found: list[tuple[str, Type, str]] = []
    for role, index, arg in COLLECTION_COMPONENTS.get(node.name, ()):
        if index >= len(node.args):
            continue
        ident = node.args[index].node_id
        ty = types.get(ident) if ident is not None else None
        if ty is None:
            continue
        if arg is not None:
            container = base_type(ty)
            if (not isinstance(container, AdtType)
                    or len(container.type_args) <= arg):
                continue
            ty = container.type_args[arg]
        if contains_typevar(ty) != (sigma is not None):
            continue
        if sigma is not None:
            ty = substitute(ty, dict(sigma))
        reason = collection_component_refusal(ty)
        if reason is not None:
            found.append((role, ty, reason))
    return found


def _component_what(node: ast.FnCall, role: str, ty: Type,
                    reason: str) -> str:
    return (f"the {role} of its '{node.name}' call is '{_type_text(ty)}', "
            f"{reason}, and code generation lowers no Map or Set operation "
            f"over {reason}")


def _source_text(source: str, span: ast.Span | None) -> str | None:
    """The text of *source* that *span* covers (1-based, end exclusive)."""
    if span is None or not source:
        return None
    starts = [0]
    for line in source.splitlines(keepends=True):
        starts.append(starts[-1] + len(line))
    if not (1 <= span.line < len(starts) and 1 <= span.end_line < len(starts)):
        return None
    return source[starts[span.line - 1] + span.column - 1:
                  starts[span.end_line - 1] + span.end_column - 1]


def _example(te: ast.TypeExpr, variables: frozenset[str]) -> str | None:
    """A value of the formal type *te* with each of *variables* at Int,
    where one is a literal: ``0``, ``Some(0)``, ``[0]``; else ``None``."""
    if isinstance(te, ast.NamedType):
        if te.name in variables and not te.type_args:
            return "0"
        if te.name in ("Option", "Array") and te.type_args and len(
                te.type_args) == 1:
            inner = _example(te.type_args[0], variables)
            if inner is None:
                return None
            return f"Some({inner})" if te.name == "Option" else f"[{inner}]"
    return None


def _mentions(te: object, variables: frozenset[str]) -> bool:
    return any(isinstance(n, ast.NamedType) and n.name in variables
               for n in _walk(te))


def _call_fix(call: ast.Node, source: str, root: Template, needs: str) -> str:
    """The root call's fix: instantiate its generic at Int, which every
    judgment here holds for, written as the call with each argument whose
    formal holds one of the generic's type parameters replaced by a value
    at Int, where each such formal has one."""
    advice = (f"Instantiate '{_bare(root.decl.name)}' at a type that "
              f"{needs}, Int for example")
    text = _source_text(source, call.span)
    args: tuple[ast.Expr, ...] = getattr(call, "args", ())
    variables = frozenset(root.decl.forall_vars or ())
    if text is None or call.span is None or len(args) != len(root.decl.params):
        return advice + "."
    edits: list[tuple[int, int, str]] = []
    for arg, formal in zip(args, root.decl.params, strict=True):
        if not _mentions(formal, variables):
            continue
        example = _example(formal, variables)
        lo = _offset(text, call.span, arg.span, start=True)
        hi = _offset(text, call.span, arg.span, start=False)
        if example is None or lo is None or hi is None:
            return advice + ", by annotating the value it is fixed from."
        edits.append((lo, hi, example))
    if not edits:
        return advice + ", by annotating the value it is fixed from."
    fixed = text
    for lo, hi, example in sorted(edits, reverse=True):
        fixed = fixed[:lo] + example + fixed[hi:]
    return f"{advice}: replace '{text}' with '{fixed}'."


def _offset(text: str, base: ast.Span, span: ast.Span | None, *,
            start: bool) -> int | None:
    """Where *span* starts (or ends) in *text*, the source *base* covers."""
    if span is None:
        return None
    line, column = ((span.line, span.column) if start
                    else (span.end_line, span.end_column))
    starts = [0]
    for piece in text.splitlines(keepends=True):
        starts.append(starts[-1] + len(piece))
    row = line - base.line
    if not 0 <= row < len(starts):
        return None
    return starts[row] + column - (base.column if row == 0 else 1)


def judge(derivation: Derivation, types: Mapping[int, Type],
          cells: Mapping[int, HandlerCell], env: TypeEnv,
          entry_file: str | None, entry_source: str) -> list[Diagnostic]:
    """Every judgment the program's instantiations decide (#1679), as the
    diagnostics the check reports: each failing instance at each root call
    that reaches it, and each Map or Set operation over an Array or
    zero-size component that holds no type parameter where it is written.

    *types* are the check's semantic types by node identity, *cells* the
    handlers' cells, *env* the check's environment, whose data types are
    every type a value of the program can carry (Eq derives over them)."""
    templates = derivation.templates
    files: dict[tuple[str, ...], tuple[str | None, str]] = {
        m.path: (str(m.file_path), m.source)
        for m in derivation.linked.modules}
    found: list[Diagnostic] = []
    refusals: dict[int, list[_Refusal]] = {}

    def of(inst: Instance) -> list[_Refusal]:
        done = refusals.get(id(inst))
        if done is None:
            template = templates[inst.key]
            source = (entry_source if inst.origin is None
                      else files.get(inst.origin, (None, ""))[1])
            done = _ability_refusals(template, inst, env)
            for node in _scope(template.decl):
                if isinstance(node, ast.HandleExpr):
                    record = cells.get(node.node_id) if node.node_id else None
                    if record is not None:
                        done.extend(_cell_refusals(node, record, inst,
                                                   template, source))
                elif isinstance(node, ast.FnCall):
                    done.extend(
                        _Refusal("E135", _component_what(node, *component),
                                 f"a Map or Set stores as a {component[0]}")
                        for component in _component_refusals(
                            node, types, inst.sigma))
            refusals[id(inst)] = done
        return done

    bodies: list[tuple[str | None, str, ast.FnDecl]] = [
        (entry_file, entry_source, tld.decl)
        for tld in derivation.linked.program.declarations
        if isinstance(tld.decl, ast.FnDecl)]
    for mod in derivation.linked.modules:
        file, source = files[mod.path]
        bodies.extend((file, source, tld.decl)
                      for tld in mod.program.declarations
                      if isinstance(tld.decl, ast.FnDecl))

    for file, source, decl in bodies:
        # A Map or Set operation whose component holds no type parameter,
        # in any body: the same at every instantiation, so judged as written.
        for node in _walk(decl):
            if isinstance(node, ast.FnCall):
                for role, ty, reason in _component_refusals(node, types, None):
                    found.append(_diagnostic(
                        "E135", file, source, node,
                        f"The '{node.name}' call's {role} is "
                        f"'{_type_text(ty)}', {reason}, and code generation "
                        f"lowers no Map or Set operation over {reason}.",
                        _component_fix(node, role, source)))
        if decl.forall_vars:
            continue
        # Each root call, and every instance it reaches.
        for node in _scope(decl):
            if not isinstance(node, (ast.FnCall, ast.ModuleCall)):
                continue
            root = (derivation.seed_targets.get(node.node_id)
                    if node.node_id is not None else None)
            if root is None:
                continue
            call_text = _source_text(source, node.span) or _bare(root.key)
            paths: dict[int, list[Instance]] = {id(root): [root]}
            queue = [root]
            while queue:
                inst = queue.pop(0)
                for refusal in of(inst):
                    fix = (refusal.fix if refusal.fix is not None
                           else _call_fix(node, source, templates[root.key],
                                          refusal.needs))
                    found.append(_diagnostic(
                        refusal.code, file, source, node,
                        f"The call '{call_text}' instantiates "
                        f"{_chain(paths[id(inst)], templates)}, where "
                        f"{refusal.what}.", fix))
                for callee in inst.calls.values():
                    if id(callee) not in paths:
                        paths[id(callee)] = [*paths[id(inst)], callee]
                        queue.append(callee)
    return found


def _component_fix(node: ast.FnCall, role: str, source: str) -> str:
    """The fix for a Map or Set operation over a component no operation is
    generated for: for an argument the call passes, a value of a type the
    collection stores, an `Option` of it for a value (stored by reference)
    and its `show` text for a key or an element (compared by content),
    written as the call with the argument replaced."""
    from vera.lowering import COLLECTION_COMPONENTS

    index = next((i for r, i, arg in COLLECTION_COMPONENTS[node.name]
                  if r == role and arg is None), None)
    text = _source_text(source, node.span)
    if index is None or index >= len(node.args) or text is None:
        return (f"Give the collection's {role} a type it stores where the "
                f"collection is built: a String or a number for a key or an "
                f"element, an Option of the value for a value.")
    arg = node.args[index]
    lo = _offset(text, node.span, arg.span, start=True)  # type: ignore[arg-type]
    hi = _offset(text, node.span, arg.span, start=False)  # type: ignore[arg-type]
    if lo is None or hi is None:
        return f"Give the {role} a type the collection stores."
    value = text[lo:hi]
    if role == "value":
        how, wrapped = "Store the value by reference in an Option", f"Some({value})"
    else:
        how = (f"{'Key the map' if node.name.startswith('map') else 'Hold the set'}"
               f" by the value's show text, which it compares by content")
        wrapped = f"show({value})"
    return (f"{how}: replace '{text}' with "
            f"'{text[:lo] + wrapped + text[hi:]}'.")


def _chain(path: Sequence[Instance], templates: Mapping[str, Template]) -> str:
    """The instances from a root call's to the failing one, as a message
    names them: each generic and the types its variables are at."""
    parts = []
    for inst in path:
        decl = templates[inst.key].decl
        at = ", ".join(f"{v} = {_type_text(inst.sigma[v])}"
                       for v in decl.forall_vars or () if v in inst.sigma)
        parts.append(f"'{_bare(inst.key)}' at {at}")
    return ", which calls ".join(parts)


def _diagnostic(code: str, file: str | None, source: str, node: ast.Node,
                description: str, fix: str) -> Diagnostic:
    """The *code* diagnostic a judgment reports at *node* in *file*."""
    from vera.binding import display_type_names
    from vera.errors import Diagnostic, SourceLocation

    loc = SourceLocation(file=file)
    line = ""
    if node.span is not None:
        loc.line, loc.column = node.span.line, node.span.column
        lines = source.splitlines()
        if 0 <= node.span.line - 1 < len(lines):
            line = lines[node.span.line - 1]
    description, fix = display_type_names(description, fix)
    if code == "E613":
        return Diagnostic(
            description=description, location=loc, source_line=line,
            rationale=_ABILITY_RATIONALE, fix=fix,
            spec_ref='Chapter 9, Section 9.8 "Abilities"',
            severity="error", error_code="E613")
    if code == "E607":
        return Diagnostic(
            description=description, location=loc, source_line=line,
            rationale=_CELL_RATIONALE, fix=fix,
            spec_ref='Chapter 7, Section 7.5.1 "Handler Syntax"',
            severity="error", error_code="E607")
    if code == "E612":
        return Diagnostic(
            description=description, location=loc, source_line=line,
            rationale=_PAYLOAD_RATIONALE, fix=fix,
            spec_ref='Chapter 7, Section 7.5.1 "Handler Syntax"',
            severity="error", error_code="E612")
    if code == "E533":
        return Diagnostic(
            description=description, location=loc, source_line=line,
            rationale=_STATE_RATIONALE, fix=fix,
            spec_ref='Chapter 7, Section 7.5.1 "Handler Syntax"',
            severity="error", error_code="E533")
    assert code == "E135", code  # noqa: S101
    return Diagnostic(
        description=description, location=loc, source_line=line,
        rationale=_COLLECTION_RATIONALE, fix=fix,
        spec_ref='Chapter 9, Section 9.4 "Built-in Collections"',
        severity="error", error_code="E135")


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
    modules: list[ResolvedModule]
    linked: Linked
    templates: dict[str, Template]
    instances: list[Instance]
    semantic: dict[int, Type]
    target: dict[int, Type]
    call_targets: dict[int, Instance]
    origin: dict[int, int]
    #: The instances a body that is not generic calls, each once, in the
    #: order the bodies are read.
    seeds: list[Instance] = field(default_factory=list)
    _by_ident: dict[tuple[object, ...], Instance] | None = field(
        default=None, repr=False)
    _by_name: dict[str, Instance] | None = field(default=None, repr=False)

    def instance(self, key: str, args: tuple[str, ...],
                 parent: Instance | None = None) -> Instance | None:
        """The instance of *key* at *args* (under *parent*), if the program
        needs it."""
        if self._by_ident is None:
            self._by_ident = {inst.ident: inst for inst in self.instances}
        return self._by_ident.get(
            (key, args, parent.ident if parent is not None else None))

    def instance_named(self, name: str) -> Instance | None:
        """The instance whose clone is named *name*."""
        if self._by_name is None:
            self._by_name = {inst.name: inst for inst in self.instances}
        return self._by_name.get(name)

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


def build(program: ast.Program, modules: Sequence[ResolvedModule],
          artifacts: CheckArtifacts) -> TypedProgram:
    """The typed program of the checked *program*, from its check's
    *artifacts* (:class:`vera.checker.core.CheckArtifacts`), whose
    derivation holds the program's one link and the instances it needs.

    Each instance is built once, in the order it was reached, from its
    template (a helper of a generic from the copy in its parent's clone),
    renumbered, and typed by its substitution; the recursion each clone's
    binder names are counted in is the declaring module's naming
    environment (#1208).  The typed program is built once per check: a
    second call returns the first's."""
    from dataclasses import replace

    from vera.monomorphize import Monomorphizer
    from vera.naming import AliasEnv, alias_env_from_program

    arts = artifacts
    derivation = arts.derivation
    assert derivation is not None, "a refused program has no typed program"  # noqa: S101
    if derivation.typed is not None:
        return derivation.typed
    linked = derivation.linked
    templates = derivation.templates
    instances = derivation.instances
    seed_targets = derivation.seed_targets
    checked_semantic: dict[int, Type] = arts.node_semantic_types
    checked_target: dict[int, Type] = arts.node_target_types
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
    mono = Monomorphizer()
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
    seeds: list[Instance] = []
    for inst in seed_targets.values():
        if all(inst is not seen for seen in seeds):
            seeds.append(inst)
    derivation.typed = TypedProgram(
        program=program, modules=list(modules), linked=linked,
        templates=templates, instances=instances, semantic=semantic,
        target=target, call_targets=call_targets, origin=origin,
        seeds=seeds)
    return derivation.typed
