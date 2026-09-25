"""The call graph of one program, and the cycles recursion lives on (#1492).

Spec §5.6 makes a ``decreases`` clause mandatory on every function that is
recursive "directly or mutually", and §7.7.3 states the same rule by effect
row: a function without ``Diverge`` must be proved to terminate.  Both need
one answer to "which functions are recursive?", and there were two partial
ones: the checker had none at all, and the verifier's was a function plus its
``where`` group, which missed a cycle through any other declaration (#1520).

The answer lives here once, and both components read it.  The checker refuses
a recursive function that declares neither a measure nor ``Diverge`` (E137),
and a contract whose calls lead back into its own function (E138).  The
verifier checks a measure across every call edge inside the cycle.

**Nodes** are the program's own function declarations, ``where`` helpers at
every depth included.

**Edges** are bare calls, resolved lexically the way the checker resolves
them (#991): the innermost enclosing declaration's helpers first, then each
ancestor's, then the program's top-level functions.  A call is an edge
wherever it is written in the declaration: in the body, in a closure the body
builds, in a handler clause, and in a contract.  A call written in a contract
or in a refinement predicate is a SPECIFICATION edge.  A type named in the
declaration contributes the calls in its refinement predicates, because the
compiled program evaluates them as guards: an alias through its definition,
and a constructor call through its field types.

A module-qualified call by the program's OWN path (``ma::f(...)`` inside
``module ma;``, spec §8.5.3, #1558) is an edge too, to the top-level
function it names — never to a ``where`` helper, which a qualified call does
not reach.  It is the bare call's twin, so leaving it out let a function
recurse through it with no measure.  The graph is told that path
(*own_path*); :func:`vera.resolver.own_module_path` derives it.

**Not edges**: a call through a function value (``apply_fn``), whose callee
is a value no declaration names; a module-qualified call into ANOTHER module,
because the module graph is acyclic (E011); built-ins, and effect and ability
operations.  Spec §5.6 states the first as the recursion this analysis cannot
see.

**Not read**: what the checker refused or does not check (#1433, #815).  A
refused declaration is no node and no call target, and adds no call: the
first declaration of a name, or the built-in, stays the one a call reaches.
A function whose body the check phase skips holds its name but adds no call.
See :class:`CallGraph`.

The calls themselves are enumerated once, by :func:`iter_calls`.  The graph
draws its edges from it, and the verifier holds its measure proof to it
(:func:`computation_calls`), so the two cannot disagree about where a call
can be written.
"""

from __future__ import annotations

from collections.abc import Callable, Container, Iterable, Iterator, Sequence
from dataclasses import dataclass, fields, is_dataclass

from vera import ast

#: A bare call name no declaration can own: the checker binds it only inside
#: a handler clause (`vera.checker.registration._HANDLER_OPERATOR_FN_NAMES`,
#: reserved by E153).  Read lazily, so this module does not import the
#: checker package it is imported by.
def _operator_names() -> frozenset[str]:
    from vera.checker.registration import _HANDLER_OPERATOR_FN_NAMES
    return _HANDLER_OPERATOR_FN_NAMES


@dataclass(frozen=True)
class CallSite:
    """One call edge: *caller* calls *callee* at *call*.

    ``spec`` is True when the call is written in a contract or a refinement
    predicate — a specification the compiled program evaluates as a check,
    not as part of the computation.
    """

    caller: ast.FnDecl
    callee: ast.FnDecl
    call: ast.FnCall | ast.ModuleCall
    spec: bool


def iter_calls(
    root: object,
    spec: bool = False,
    expand: Callable[[ast.Node], object] | None = None,
    skip: Container[int] = frozenset(),
    own_path: tuple[str, ...] | None = None,
) -> Iterator[tuple[ast.FnCall | ast.ModuleCall, bool]]:
    """Every bare call under *root*, with whether it is a specification call
    — and every module-qualified call by *own_path*, the program's own path,
    which names one of its top-level functions as a bare call does (#1558).

    THE enumeration of where a call can be written.  It is a generic walk
    over every dataclass field, not a dispatch on expression kinds, so a node
    kind that no list names is still walked.  A nested declaration is not
    entered: it is its own node of the graph, with its own frame.  Nor is a
    node whose id is in *skip*: a declaration the checker refused, such as a
    handler's surplus clause for an operation (#1433).

    A call inside a contract or a refinement predicate is a specification
    call, and so is every call under what *expand* returns for a node: the
    type text the node contributes (an alias's definition, a constructor's
    field types), whose predicates the compiled program evaluates as guards.

    An explicit stack, not recursion: an alias chain or a nested expression
    is as deep as the program makes it, and a walk with a Python frame per
    level would raise `RecursionError` on a program the checker accepts (the
    #1208 depth lesson).  Children are pushed in reverse, so calls are met
    in source order.
    """
    stack: list[tuple[object, bool]] = [(root, spec)]
    while stack:
        node, in_spec = stack.pop()
        if isinstance(node, ast.FnDecl):
            continue
        if isinstance(node, tuple):
            stack.extend((item, in_spec) for item in reversed(node))
            continue
        if not (is_dataclass(node) and isinstance(node, ast.Node)):
            continue
        if id(node) in skip:
            continue
        if isinstance(node, ast.FnCall):
            yield node, in_spec
        elif (own_path is not None and isinstance(node, ast.ModuleCall)
                and tuple(node.path) == own_path):
            yield node, in_spec
        elif isinstance(node, (ast.Contract, ast.RefinementType)):
            in_spec = True
        expansion = expand(node) if expand is not None else None
        stack.extend(reversed([
            (getattr(node, f.name), in_spec)
            for f in fields(node) if f.name != "span"
        ]))
        if expansion is not None:
            stack.append((expansion, True))


def computation_calls(
    root: object, own_path: tuple[str, ...] | None = None,
) -> list[ast.FnCall | ast.ModuleCall]:
    """The calls under *root* that run as computation, in source order.

    Those the graph's body edges are drawn from: every call outside a
    contract and a refinement predicate, the calls by *own_path* among them.
    The verifier checks its measure walk against this list (#1524 review),
    because a call that walk does not reach would otherwise be left out of a
    termination proof while the runtime guard still meets it.
    """
    return [call for call, spec in iter_calls(root, own_path=own_path)
            if not spec]


def declares_diverge(decl: ast.FnDecl) -> bool:
    """Whether *decl*'s effect row names ``Diverge`` (spec §7.7.3)."""
    effect = decl.effect
    if not isinstance(effect, ast.EffectSet):
        return False
    return any(
        isinstance(eff, ast.EffectRef) and eff.name == "Diverge"
        for eff in effect.effects
    )


def declares_decreases(decl: ast.FnDecl) -> bool:
    """Whether *decl* carries a ``decreases`` clause with a measure."""
    return any(
        isinstance(c, ast.Decreases) and c.exprs for c in decl.contracts
    )


class CallGraph:
    """The call graph of one program's declarations, with its cycles.

    *refused* and *unchecked* are the checker's ``_refused_decl_ids`` and
    ``_unchecked_body_ids``, so the graph reads what its check phase reads.
    A refused declaration, at any depth, is no node, no call target and no
    source of calls: a built-in's redefinition (E151), a type named after a
    primitive (E158), the surplus of a name declared twice in one namespace
    (E184), and a refused member (a constructor, a handler clause).  Every
    use of the name reaches the built-in or the first declaration (spec
    §8.5.5), and a call does here too.  An unchecked function, one with a refused ``where`` helper (#815),
    holds its name, so it is a node and a call target, but nothing written
    in it is read.  The verifier passes neither: it reads only a program
    that type-checked, where both are empty.

    *own_path* is the path that names the program's own file in a
    module-qualified call, or ``None`` where it has none (#1558): a call by
    it is an edge to the top-level function it names.
    """

    def __init__(
        self,
        declarations: Iterable[ast.Decl],
        refused: Container[int] = frozenset(),
        unchecked: Container[int] = frozenset(),
        own_path: tuple[str, ...] | None = None,
    ) -> None:
        self._refused = refused
        self._unchecked = unchecked
        self._own_path = own_path
        decls = [d for d in declarations if id(d) not in refused]
        self._top: dict[str, ast.FnDecl] = {}
        self._aliases: dict[str, ast.TypeExpr] = {}
        self._ctor_fields: dict[str, tuple[ast.TypeExpr, ...]] = {}
        for d in decls:
            if isinstance(d, ast.FnDecl):
                # One declaration per name: the checker refuses the surplus
                # (E184), which *refused* has left out.
                self._top[d.name] = d
            elif isinstance(d, ast.TypeAliasDecl):
                self._aliases[d.name] = d.type_expr
            elif isinstance(d, ast.DataDecl):
                for ctor in d.constructors:
                    if id(ctor) not in refused:
                        self._ctor_fields[ctor.name] = tuple(
                            ctor.fields or ())
        #: Every declaration, `where` helpers included, in source preorder.
        self.fns: list[ast.FnDecl] = []
        #: Every call edge, in the order the walk met them.
        self.sites: list[CallSite] = []
        for d in decls:
            if isinstance(d, ast.FnDecl):
                self._add_fn(d, [])
        self._index = {id(fn): i for i, fn in enumerate(self.fns)}
        body_succ: list[set[int]] = [set() for _ in self.fns]
        full_succ: list[set[int]] = [set() for _ in self.fns]
        for site in self.sites:
            a = self._index[id(site.caller)]
            b = self._index[id(site.callee)]
            full_succ[a].add(b)
            if not site.spec:
                body_succ[a].add(b)
        self._body_comp = _components(body_succ)
        self._full_comp = _components(full_succ)
        self._body_loop = {i for i, s in enumerate(body_succ) if i in s}
        self._full_loop = {i for i, s in enumerate(full_succ) if i in s}

    # -- construction ------------------------------------------------------

    def _add_fn(self, decl: ast.FnDecl, outer: list[ast.FnDecl]) -> None:
        frames = [*outer, decl]
        self.fns.append(decl)
        if id(decl) in self._unchecked:
            return
        seen: set[str] = set()
        for te in (*decl.params, decl.return_type):
            self._walk(te, decl, frames, True, seen)
        for contract in decl.contracts:
            self._walk(contract, decl, frames, True, seen)
        self._walk(decl.body, decl, frames, False, seen)
        for wfn in decl.where_fns or ():
            if id(wfn) not in self._refused:
                self._add_fn(wfn, frames)

    def _resolve(
        self, name: str, frames: Sequence[ast.FnDecl],
    ) -> ast.FnDecl | None:
        """The declaration a bare call to *name* denotes here, if any."""
        if name in _operator_names():
            return None
        for frame in reversed(frames):
            for wfn in frame.where_fns or ():
                if wfn.name == name and id(wfn) not in self._refused:
                    return wfn
        return self._top.get(name)

    def _walk(
        self,
        root: object,
        caller: ast.FnDecl,
        frames: Sequence[ast.FnDecl],
        spec: bool,
        seen: set[str],
    ) -> None:
        """Record every call reachable from *root* as an edge of *caller*.

        The calls are :func:`iter_calls`'s.  What this adds is the type
        expansion: a type contributes the calls in its refinement
        predicates, which the compiled program evaluates as guards, an alias
        through its definition and a constructor through its fields.  Each
        is expanded once per declaration (*seen*), so a recursive type ends.
        """
        def expand(node: ast.Node) -> object:
            if isinstance(node, ast.NamedType):
                key = f"type:{node.name}"
                if node.name in self._aliases and key not in seen:
                    seen.add(key)
                    return self._aliases[node.name]
            elif isinstance(node, (ast.ConstructorCall,
                                   ast.NullaryConstructor)):
                key = f"ctor:{node.name}"
                if node.name in self._ctor_fields and key not in seen:
                    seen.add(key)
                    return self._ctor_fields[node.name]
            return None

        for call, in_spec in iter_calls(root, spec, expand, self._refused,
                                        self._own_path):
            # A call by the own path names a TOP-LEVEL function: no helper
            # shadows a module-qualified call (§8.5.3).
            callee = (self._top.get(call.name)
                      if isinstance(call, ast.ModuleCall)
                      else self._resolve(call.name, frames))
            if callee is not None:
                self.sites.append(CallSite(caller, callee, call, in_spec))

    # -- queries -----------------------------------------------------------

    def is_recursive(self, decl: ast.FnDecl) -> bool:
        """Whether *decl* lies on a cycle of computation (body) edges."""
        i = self._index.get(id(decl))
        if i is None:
            return False
        return i in self._body_loop or len(self._body_comp[i]) > 1

    def cycle(self, decl: ast.FnDecl) -> list[ast.FnDecl]:
        """The declarations on *decl*'s cycles, *decl* included, in source
        order; empty when *decl* is not recursive."""
        if not self.is_recursive(decl):
            return []
        comp = self._body_comp[self._index[id(decl)]]
        return [self.fns[j] for j in sorted(comp)]

    def cycle_sites(self, decl: ast.FnDecl) -> list[CallSite]:
        """The computation calls from *decl* that stay on its cycle."""
        members = {id(fn) for fn in self.cycle(decl)}
        return [
            s for s in self.sites
            if s.caller is decl and not s.spec and id(s.callee) in members
        ]

    def spec_cycle_sites(self) -> list[CallSite]:
        """Specification calls that lead back to their own declaration."""
        out: list[CallSite] = []
        for s in self.sites:
            if not s.spec:
                continue
            a = self._index[id(s.caller)]
            b = self._index[id(s.callee)]
            if (a == b and a in self._full_loop) or (
                    a != b and b in self._full_comp[a]):
                out.append(s)
        return out

    def unmeasured(self) -> Iterator[ast.FnDecl]:
        """Recursive declarations with neither a measure nor ``Diverge``."""
        for fn in self.fns:
            if (self.is_recursive(fn) and not declares_decreases(fn)
                    and not declares_diverge(fn)):
                yield fn


def _components(succ: list[set[int]]) -> list[frozenset[int]]:
    """Each node's strongly connected component (Tarjan, iterative)."""
    n = len(succ)
    index = [-1] * n
    low = [0] * n
    on_stack = [False] * n
    stack: list[int] = []
    comp: list[frozenset[int]] = [frozenset()] * n
    counter = 0
    for root in range(n):
        if index[root] != -1:
            continue
        work: list[tuple[int, Iterator[int]]] = [(root, iter(sorted(succ[root])))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on_stack[root] = True
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if index[w] == -1:
                    index[w] = low[w] = counter
                    counter += 1
                    stack.append(w)
                    on_stack[w] = True
                    work.append((w, iter(sorted(succ[w]))))
                    advanced = True
                    break
                if on_stack[w]:
                    low[v] = min(low[v], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
            if low[v] == index[v]:
                members: list[int] = []
                while True:
                    w = stack.pop()
                    on_stack[w] = False
                    members.append(w)
                    if w == v:
                        break
                frozen = frozenset(members)
                for w in members:
                    comp[w] = frozen
    return comp
