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

**Not edges**: a call through a function value (``apply_fn``), whose callee
is a value no declaration names; a module-qualified call, because the module
graph is acyclic (E011); built-ins, and effect and ability operations.  Spec
§5.6 states the first as the recursion this analysis cannot see.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator, Sequence
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
    call: ast.FnCall
    spec: bool


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
    """The call graph of one program's declarations, with its cycles."""

    def __init__(self, declarations: Iterable[ast.Decl]) -> None:
        decls = list(declarations)
        self._top: dict[str, ast.FnDecl] = {}
        self._aliases: dict[str, ast.TypeExpr] = {}
        self._ctor_fields: dict[str, tuple[ast.TypeExpr, ...]] = {}
        for d in decls:
            if isinstance(d, ast.FnDecl):
                # Last wins, as the checker's top-level table does.
                self._top[d.name] = d
            elif isinstance(d, ast.TypeAliasDecl):
                self._aliases[d.name] = d.type_expr
            elif isinstance(d, ast.DataDecl):
                for ctor in d.constructors:
                    self._ctor_fields[ctor.name] = tuple(ctor.fields or ())
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
        seen: set[str] = set()
        for te in (*decl.params, decl.return_type):
            self._walk(te, decl, frames, True, seen)
        for contract in decl.contracts:
            self._walk(contract, decl, frames, True, seen)
        self._walk(decl.body, decl, frames, False, seen)
        for wfn in decl.where_fns or ():
            self._add_fn(wfn, frames)

    def _resolve(
        self, name: str, frames: Sequence[ast.FnDecl],
    ) -> ast.FnDecl | None:
        """The declaration a bare call to *name* denotes here, if any."""
        if name in _operator_names():
            return None
        for frame in reversed(frames):
            for wfn in frame.where_fns or ():
                if wfn.name == name:
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

        An explicit stack, not recursion: an alias chain or a nested
        expression is as deep as the program makes it, and a walk with a
        Python frame per level would raise `RecursionError` on a program the
        checker accepts (the #1208 depth lesson).  Children are pushed in
        reverse, so edges are met in source order.
        """
        stack: list[tuple[object, bool]] = [(root, spec)]
        while stack:
            node, in_spec = stack.pop()
            if isinstance(node, ast.FnDecl):
                # A nested declaration is its own node, with its own frame.
                continue
            if isinstance(node, tuple):
                stack.extend((item, in_spec) for item in reversed(node))
                continue
            if not (is_dataclass(node) and isinstance(node, ast.Node)):
                continue
            if isinstance(node, ast.FnCall):
                callee = self._resolve(node.name, frames)
                if callee is not None:
                    self.sites.append(CallSite(caller, callee, node, in_spec))
            elif isinstance(node, (ast.Contract, ast.RefinementType)):
                in_spec = True
            # A type contributes the calls in its refinement predicates,
            # which the compiled program evaluates as guards: an alias
            # through its definition, a constructor through its fields.
            # Every call reached that way is inside a predicate.
            expansion: object = None
            if isinstance(node, ast.NamedType):
                key = f"type:{node.name}"
                if node.name in self._aliases and key not in seen:
                    seen.add(key)
                    expansion = self._aliases[node.name]
            elif isinstance(node, (ast.ConstructorCall,
                                   ast.NullaryConstructor)):
                key = f"ctor:{node.name}"
                if node.name in self._ctor_fields and key not in seen:
                    seen.add(key)
                    expansion = self._ctor_fields[node.name]
            children = [
                (getattr(node, f.name), in_spec)
                for f in fields(node) if f.name != "span"
            ]
            stack.extend(reversed(children))
            if expansion is not None:
                stack.append((expansion, True))

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
