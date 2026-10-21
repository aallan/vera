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

from collections.abc import Iterable, Iterator, Mapping
from dataclasses import dataclass, field

from vera import ast
from vera.fold import walk
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


def _type_predicates(te: ast.TypeExpr | None) -> Iterator[ast.Expr]:
    """The refinement predicates written inside a type expression."""
    stack: list[object] = [te]
    while stack:
        t = stack.pop()
        if isinstance(t, ast.RefinementType):
            yield t.predicate
            stack.append(t.base_type)
        elif isinstance(t, ast.NamedType):
            stack.extend(t.type_args or ())
        elif isinstance(t, ast.FnType):
            stack.extend(t.params)
            stack.append(t.return_type)


def _fn_roots(decl: ast.FnDecl) -> list[ast.Node]:
    """Everything in *decl* a call can be written in, nested declarations
    (its ``where`` helpers) excepted."""
    roots: list[ast.Node] = [decl.body]
    for contract in decl.contracts:
        if isinstance(contract, ast.Decreases):
            roots.extend(contract.exprs)
        else:
            roots.append(contract.expr)  # type: ignore[attr-defined]
    for te in (*decl.params, decl.return_type):
        roots.extend(_type_predicates(te))
    return roots


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

    def _bind_fn(
        self, ns: _Namespace, own: Mapping[str, ast.FnDecl],
        decl: ast.FnDecl, frames: list[tuple[str, ast.FnDecl]],
    ) -> None:
        for node in walk(tuple(_fn_roots(decl))):
            if isinstance(node, ast.FnCall):
                target = self._bare(ns, own, node.name, frames)
            elif isinstance(node, ast.ModuleCall):
                target = self._qualified(ns, node.path, node.name)
            else:
                continue
            if target is not None:
                self.out._bind(node, target)
        for wfn in decl.where_fns or ():
            self._bind_fn(ns, own, wfn, [*frames, (wfn.name, wfn)])

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
