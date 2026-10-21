"""The resolver pass: every declaration's identity, every call's binding (#1694).

Spec §8.5 says what a bare or qualified function name denotes in a
namespace.  This module says it ONCE, for the entry file, every module the
program reaches and the prelude, before any later stage asks: each function
declaration gets a :class:`DeclId`, and each call occurrence (``FnCall``,
``ModuleCall``) maps to the ``DeclId`` of the declaration it calls.  The
checker, the verifier and code generation read :class:`Binding` instead of
resolving a name themselves, so two of them cannot read one call two ways.

A ``DeclId`` is the declaration's owner (the entry file, the prelude, a
module path, or the built-in registry), its name, and for a ``where`` helper
the chain of functions it is nested in.  Its link name is unique across the
whole program by construction:

* an entry-file or prelude declaration keeps its bare name, and the two
  spaces are disjoint because no declaration may take a prelude function's
  name (#1469, :func:`vera.prelude.reserved_function_names`);
* a module declaration is always ``mod$<path>$<name>``, which no bare
  identifier can spell, whether or not some namespace sees it under its
  bare name, so no ownership question is asked;
* a ``where`` helper is ``<parent>$where$<name>``, its parent's link name
  being unique.

Its WASM symbol is :data:`SYMBOL_PREFIX` + the link name.  No symbol code
generation generates for itself (``alloc``, ``gc_collect``, ``anon_0``,
``eq_String``, …) contains the prefix's character, and no Vera identifier
can, so a declaration and a generated function never share a symbol
(#1494).

The rule order for a bare call is the checker's (``_lookup_function_scoped``
and the import injection in ``checker/modules.py``): the ``where`` helpers of
the innermost enclosing function first and then each ancestor's, the
namespace's own top-level functions, the built-ins and the prelude's
functions, and last the functions the namespace's direct imports admit,
where exactly one supplier binds and two leave the call unbound (E155 is the
checker's report of that).  An occurrence the rules do not bind is absent
from :attr:`Binding.calls`; reporting it is the checker's job.
"""

from __future__ import annotations

from collections.abc import (
    Collection, Iterable, Iterator, Mapping, Sequence,
)
from dataclasses import dataclass, field, fields, replace
from typing import Any, cast

from vera import ast
from vera.prelude import PRELUDE_NAMESPACE
from vera.resolver import ResolvedModule, merged_import_filters, own_module_path

#: The owner of the entry file's declarations.  ``<`` cannot begin a module
#: path segment (§8.1), so no module's path is this one.
ENTRY: tuple[str, ...] = ("<entry>",)

#: The owner of the prelude's declarations, shaped as a module path like
#: :data:`vera.prelude.PRELUDE_NAMESPACE`, which it is.
PRELUDE: tuple[str, ...] = PRELUDE_NAMESPACE

#: The owner of a built-in function: it has no Vera declaration, and code
#: generation lowers each call through the built-in's registry record.
BUILTIN: tuple[str, ...] = ("<builtin>",)

#: What every declaration's WASM symbol starts with.  ``:`` is a WebAssembly
#: identifier character and no Vera identifier's.
SYMBOL_PREFIX = ":"

#: The handler-clause operator: ``check_handle_expr`` binds it for each
#: clause body, so no declaration is ever its target.
_HANDLER_OPERATORS = frozenset({"resume"})


@dataclass(frozen=True)
class DeclId:
    """One function declaration's identity."""

    owner: tuple[str, ...]
    name: str
    #: The functions a ``where`` helper is nested in, outermost first; empty
    #: for a top-level declaration.
    scope: tuple[str, ...] = ()

    @property
    def link_name(self) -> str:
        """The name the declaration has in the linked program: unique."""
        if self.scope:
            parent = DeclId(self.owner, self.scope[-1], self.scope[:-1])
            return f"{parent.link_name}$where${self.name}"
        if self.owner in (ENTRY, PRELUDE, BUILTIN):
            return self.name
        return "mod$" + "$".join(self.owner) + "$" + self.name

    @property
    def symbol(self) -> str:
        """The WASM symbol (without its ``$``), in the declarations' own
        namespace."""
        return SYMBOL_PREFIX + self.link_name


def symbol(link_name: str) -> str:
    """The WASM symbol of the declaration (or a clone of it) whose linked
    name is *link_name*, without its ``$``."""
    return SYMBOL_PREFIX + link_name


def source_name(wasm_name: str) -> str:
    """*wasm_name* with the declarations' prefix removed: the name a trap
    frame or a diagnostic shows for a declaration's symbol, and *wasm_name*
    itself for a generated function."""
    return wasm_name.removeprefix(SYMBOL_PREFIX)


@dataclass
class _Namespace:
    """What one file's bare and qualified calls can reach."""

    owner: tuple[str, ...]
    program: ast.Program
    #: The path a ``p::f`` call names this file by, if any (#1558).
    own_path: tuple[str, ...] | None
    #: The modules this file imports directly, with each one's filter.
    imports: dict[tuple[str, ...], set[str] | None]


@dataclass
class Binding:
    """The resolver pass's output: declarations and the calls bound to them."""

    #: Every function declaration of every namespace, by identity.
    decls: dict[DeclId, ast.FnDecl] = field(default_factory=dict)
    #: ``id(occurrence)`` of each bound ``FnCall`` / ``ModuleCall`` to the
    #: declaration it calls.
    calls: dict[int, DeclId] = field(default_factory=dict)
    #: The occurrences themselves, so an ``id`` is never reused while the
    #: binding is alive.
    _nodes: list[ast.Node] = field(default_factory=list, repr=False)

    def of(self, call: ast.Node) -> DeclId | None:
        """The declaration *call* calls, or ``None`` if it binds none."""
        return self.calls.get(id(call))

    def _bind(self, call: ast.Node, target: DeclId) -> None:
        self.calls[id(call)] = target
        self._nodes.append(call)


def _public_fns(program: ast.Program) -> dict[str, ast.FnDecl]:
    return {
        tld.decl.name: tld.decl for tld in program.declarations
        if isinstance(tld.decl, ast.FnDecl) and tld.visibility == "public"
    }


def _top_level_fns(program: ast.Program) -> dict[str, ast.FnDecl]:
    """The first declaration of each name: a surplus one is refused (E184)
    and the first stays canonical, as the checker has it (#1433)."""
    out: dict[str, ast.FnDecl] = {}
    for tld in program.declarations:
        if isinstance(tld.decl, ast.FnDecl):
            out.setdefault(tld.decl.name, tld.decl)
    return out


def _calls_under(root: object) -> Iterator[ast.FnCall | ast.ModuleCall]:
    """Every call written under *root*: in an expression, in a refinement
    predicate a type expression carries (a parameter's, a ``let``'s, an
    alias body's, a constructor field's), in a contract or an invariant.  A
    function's ``where`` helpers are left out; each is its own frame."""
    stack: list[object] = [root]
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FnCall, ast.ModuleCall)):
            yield node
        if isinstance(node, ast.Node):
            for f in fields(node):
                if f.name == "where_fns" and isinstance(node, ast.FnDecl):
                    continue
                stack.append(getattr(node, f.name))
        elif isinstance(node, tuple):
            stack.extend(node)


class _Binder:
    """One run of the pass."""

    def __init__(
        self,
        builtins: frozenset[str],
        prelude_fns: Mapping[str, ast.FnDecl],
        modules: Mapping[tuple[str, ...], ResolvedModule],
    ) -> None:
        self.builtins = builtins
        self.prelude_fns = prelude_fns
        self.modules = modules
        self.out = Binding()

    def namespace(
        self, owner: tuple[str, ...], program: ast.Program,
        resolved_as: tuple[str, ...] | None,
    ) -> _Namespace:
        return _Namespace(
            owner=owner,
            program=program,
            own_path=own_module_path(
                program, resolved_as, self.modules.values()),
            imports=merged_import_filters(program.imports),
        )

    def declare(self, ns: _Namespace) -> None:
        for name, decl in _top_level_fns(ns.program).items():
            self._declare(DeclId(ns.owner, name), decl)

    def _declare(self, ident: DeclId, decl: ast.FnDecl) -> None:
        self.out.decls[ident] = decl
        for wfn in decl.where_fns or ():
            self._declare(
                DeclId(ident.owner, wfn.name, (*ident.scope, ident.name)),
                wfn)

    def bind(self, ns: _Namespace) -> None:
        own = _top_level_fns(ns.program)
        for name, decl in own.items():
            self._bind_fn(ns, own, decl, [(name, decl)])
        # A call can be written outside every function too: in a refinement
        # an alias or a constructor field carries, or a data invariant.
        for tld in ns.program.declarations:
            if not isinstance(tld.decl, ast.FnDecl):
                self._bind_calls(ns, own, tld.decl, [])

    def _bind_fn(
        self, ns: _Namespace, own: Mapping[str, ast.FnDecl],
        decl: ast.FnDecl, frames: list[tuple[str, ast.FnDecl]],
    ) -> None:
        self._bind_calls(ns, own, decl, frames)
        for wfn in decl.where_fns or ():
            self._bind_fn(ns, own, wfn, [*frames, (wfn.name, wfn)])

    def _bind_calls(
        self, ns: _Namespace, own: Mapping[str, ast.FnDecl],
        root: ast.Node, frames: list[tuple[str, ast.FnDecl]],
    ) -> None:
        for node in _calls_under(root):
            if isinstance(node, ast.FnCall):
                target = self._bare(ns, own, node.name, frames)
            else:
                target = self._qualified(ns, node.path, node.name)
            if target is not None:
                self.out._bind(node, target)

    def _bare(
        self, ns: _Namespace, own: Mapping[str, ast.FnDecl], name: str,
        frames: list[tuple[str, ast.FnDecl]],
    ) -> DeclId | None:
        if name in _HANDLER_OPERATORS:
            return None
        # The innermost frame's helpers first, then each ancestor's.
        for depth in range(len(frames) - 1, -1, -1):
            for wfn in frames[depth][1].where_fns or ():
                if wfn.name == name:
                    chain = tuple(n for n, _ in frames[:depth + 1])
                    return DeclId(ns.owner, name, chain)
        if name in own:
            return DeclId(ns.owner, name)
        if name in self.builtins:
            return DeclId(BUILTIN, name)
        if name in self.prelude_fns:
            return DeclId(PRELUDE, name)
        suppliers = [
            path for path, admitted in ns.imports.items()
            if path in self.modules
            and (admitted is None or name in admitted)
            and name in _public_fns(self.modules[path].program)
        ]
        if len(suppliers) == 1:
            return DeclId(suppliers[0], name)
        return None

    def _qualified(
        self, ns: _Namespace, path: tuple[str, ...], name: str,
    ) -> DeclId | None:
        if ns.own_path is not None and path == ns.own_path:
            own = _top_level_fns(ns.program)
            return DeclId(ns.owner, name) if name in own else None
        if path not in ns.imports or path not in self.modules:
            return None
        admitted = ns.imports[path]
        if admitted is not None and name not in admitted:
            return None
        if name in _public_fns(self.modules[path].program):
            return DeclId(path, name)
        return None


def bind_program(
    program: ast.Program,
    resolved_modules: Iterable[ResolvedModule] = (),
    prelude_decls: Iterable[ast.TopLevelDecl] = (),
) -> Binding:
    """Run the pass over *program*, every module it reaches and the prelude
    declarations *prelude_decls* (those the program is compiled with)."""
    from vera.environment import TypeEnv
    from vera.prelude import overridable_builtin_names

    modules = {mod.path: mod for mod in resolved_modules}
    prelude_fns = {
        tld.decl.name: tld.decl for tld in prelude_decls
        if isinstance(tld.decl, ast.FnDecl)
    }
    builtins = (frozenset(TypeEnv().functions)
                - overridable_builtin_names()) | {"apply_fn"}
    binder = _Binder(builtins, prelude_fns, modules)
    namespaces = [binder.namespace(ENTRY, program, None)]
    namespaces.extend(
        binder.namespace(path, mod.program, path)
        for path, mod in modules.items())
    prelude_program = ast.Program(
        module=None, imports=(), declarations=tuple(prelude_decls),
        span=None)
    namespaces.append(binder.namespace(PRELUDE, prelude_program, None))
    for ns in namespaces:
        binder.declare(ns)
    for ns in namespaces:
        binder.bind(ns)
    return binder.out


# =====================================================================
# The link step: each program with every declaration under its link name
# =====================================================================

def _relinked_call(
    node: ast.FnCall | ast.ModuleCall, target: DeclId | None,
    args: tuple[ast.Expr, ...],
) -> ast.Expr:
    """*node*, naming *target* by its link name.

    A built-in or a prelude function keeps its bare name, which is its link
    name; every other declaration, a ``where`` helper included, is named by
    the one name it has in the linked program, so no later pass asks which
    declaration a call's name means.  A qualified call becomes a plain one.
    """
    if target is not None and target.owner not in (BUILTIN, PRELUDE):
        return ast.FnCall(
            name=target.link_name, args=args, piped=node.piped,
            stage_span=node.stage_span, span=node.span)
    if args is node.args:
        return node
    return replace(node, args=args)


def _relink(node: object, calls: Mapping[int, DeclId]) -> object:
    """*node* with every call the binding binds naming its target's link
    name.  Nodes are rebuilt only where something under them changed, and
    every rebuilt node keeps its span, so the checker's span-keyed tables
    still answer for it."""
    if isinstance(node, (ast.FnCall, ast.ModuleCall)):
        args = cast(tuple[ast.Expr, ...], _relink(node.args, calls))
        return _relinked_call(node, calls.get(id(node)), args)
    if isinstance(node, ast.Node):
        changed: dict[str, Any] = {}
        for f in fields(node):
            old = getattr(node, f.name)
            new = _relink(old, calls)
            if new is not old:
                changed[f.name] = new
        return replace(node, **changed) if changed else node
    if isinstance(node, tuple):
        walked = tuple(_relink(x, calls) for x in node)
        if any(a is not b for a, b in zip(walked, node)):
            return walked
        return node
    return node


def _link_fn(
    decl: ast.FnDecl, ident: DeclId, calls: Mapping[int, DeclId],
) -> ast.FnDecl:
    """*decl* under *ident*'s link name, its calls relinked, and each of its
    ``where`` helpers linked the same way under its own identity.  *decl*
    itself when none of that changes anything, as for a prelude function."""
    if not decl.where_fns:
        own = cast(ast.FnDecl, _relink(decl, calls))
        if own is decl and ident.link_name == decl.name:
            return decl
        return replace(own, name=ident.link_name)
    own = cast(ast.FnDecl, _relink(replace(decl, where_fns=None), calls))
    helpers = tuple(
        _link_fn(wfn, DeclId(ident.owner, wfn.name,
                             (*ident.scope, ident.name)), calls)
        for wfn in decl.where_fns
    )
    return replace(own, name=ident.link_name, where_fns=helpers)


def _link_program(
    program: ast.Program, owner: tuple[str, ...], binding: Binding,
) -> ast.Program:
    decls: list[ast.TopLevelDecl] = []
    for tld in program.declarations:
        if isinstance(tld.decl, ast.FnDecl):
            decl: ast.Decl = _link_fn(
                tld.decl, DeclId(owner, tld.decl.name), binding.calls)
        else:
            decl = cast(ast.Decl, _relink(tld.decl, binding.calls))
        decls.append(tld if decl is tld.decl else replace(tld, decl=decl))
    return replace(program, declarations=tuple(decls))


def relink_calls_to(
    decl: ast.FnDecl, targets: Collection[DeclId], binding: Binding,
) -> ast.FnDecl:
    """*decl* with each call *binding* binds to one of *targets* naming it
    by its link name, and every other call as written.  *decl* must be a
    declaration *binding* was computed over."""
    calls = {
        key: ident for key, ident in binding.calls.items()
        if ident in targets
    }
    return cast(ast.FnDecl, _relink(decl, calls))


def bare_name(link_name: str) -> str:
    """The source name a declaration's link name was made from: the last
    ``$where$`` segment of a helper's, the name after a module path's."""
    name = link_name.rpartition("$where$")[2]
    if name.startswith("mod$"):
        name = name.rpartition("$")[2]
    return name


def display_names(binding: Binding) -> dict[str, str]:
    """Each module declaration's link name to the spelling a message shows
    for it: the name it is declared under (a helper's chained under its
    parent's, ``f$where$h``).  The file a message or a trap frame names
    says which module the declaration is in."""
    return {
        ident.link_name: DeclId(ENTRY, ident.name, ident.scope).link_name
        for ident in binding.decls
        if ident.owner not in (ENTRY, PRELUDE, BUILTIN)
    }


def display_name(name: str, names: Mapping[str, str]) -> str:
    """*name* as a message shows it: its :func:`display_names` spelling, or,
    for a clone of a declaration or a helper hoisted from one, that
    declaration's spelling with the clone's suffix kept."""
    shown = names.get(name)
    if shown is not None:
        return shown
    best = ""
    for link_name in names:
        if (len(link_name) > len(best)
                and name.startswith(link_name + "$")):
            best = link_name
    return names[best] + name[len(best):] if best else name


def display_text(text: str, names: Mapping[str, str]) -> str:
    """*text* with every link name in it spelled as :func:`display_name`
    spells it, the longest first so no name is rewritten inside another."""
    if "mod$" not in text:
        return text
    for link_name in sorted(names, key=len, reverse=True):
        if link_name in text:
            text = text.replace(link_name, names[link_name])
    return text


@dataclass(frozen=True)
class Linked:
    """The program, its modules and its prelude, every declaration under
    its link name (:func:`link_program`)."""

    program: ast.Program
    modules: list[ResolvedModule]
    #: The prelude declarations the binding bound, which are the ones to
    #: compile (their link names are their own).
    prelude: tuple[ast.TopLevelDecl, ...]
    #: The buffer the prelude declarations' spans index into.
    prelude_source: str
    binding: Binding


def link(
    program: ast.Program,
    resolved_modules: Sequence[ResolvedModule],
    binding: Binding,
) -> tuple[ast.Program, list[ResolvedModule]]:
    """The entry *program* and its *resolved_modules*, linked.

    Every module's top-level function takes its link name
    (``mod$<path>$<name>``), every ``where`` helper its own
    (``<parent>$where$<name>``), and every call *binding* binds names the
    declaration it calls by that link name: a qualified call becomes a plain
    call of the name.  So no two declarations share a name, and a consumer
    looking a call's name up finds the one declaration the call means
    without asking which namespace or which ``where`` block it sits in.
    Types, constructors and aliases keep their names here, and every node
    keeps its span.
    """
    linked = [
        replace(mod, program=_link_program(mod.program, mod.path, binding))
        for mod in resolved_modules
    ]
    return _link_program(program, ENTRY, binding), linked


def link_program(
    program: ast.Program,
    resolved_modules: Sequence[ResolvedModule],
) -> Linked:
    """:func:`link` over a fresh binding of *program*, its modules and the
    prelude they are compiled with."""
    from vera.prelude import prelude_declarations

    prelude, prelude_source = prelude_declarations(
        program, {mod.path: mod.program for mod in resolved_modules})
    binding = bind_program(program, resolved_modules, prelude)
    linked_program, linked_modules = link(program, resolved_modules, binding)
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
