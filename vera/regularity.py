"""Regular recursion in `data` declarations — ONE derivation (#1429).

The rule is read PER TYPE ARGUMENT of a recursive occurrence — of the
declaration itself, or of any type mutually recursive with it.  Inside a
declaration `N<P...>`, each argument of such an occurrence must be either

* a BARE PARAMETER of `N`, passed along unchanged, or
* CLOSED with respect to `N`'s parameters — mentioning none of them anywhere
  inside it, as in `Expr<Int>`, `Body<Int>`, or a zero-argument `Decl`;

and an argument that wraps a parameter inside another type constructor
(`Option<T>`, `Tuple<T, T>`) is the growth case, which is refused.  An
occurrence of the declaration's OWN name must additionally keep its parameters
in their original positions.

`data List<T> { Cons(T, List<T>), Nil }` passes one along and `data Expr<T> {
Lit(T), Add(Expr<Int>, Expr<Int>) }` closes one; `data Nest<T> {
N(Nest<Option<T>>), Z }` does neither — `Option<T>` wraps the parameter, so
each level's argument is larger than the last and the chain `Nest<Int>` ->
`Nest<Option<Int>>` -> `Nest<Option<Option<Int>>>` never repeats.

Comparing the occurrence's whole argument LIST against the declaration's
parameter list is the rule this replaces, and it over-refused: the comparison
cannot even be stated for a mutually recursive pair whose members differ in
arity, and it rejected `data Decl { D(Body<Int>) }` with `data Body<T> { B(T,
Decl) }` and `data Expr<T> { Lit(T), Add(Expr<Int>, Expr<Int>) }`, whose
closures are two members each (PR #1432 re-verification).

Two consumers ask, and they must not answer differently:

* the CHECKER refuses the declaration (`E129`), which is where the program
  says what it means and where a reader can act on it; and
* the SMT layer DECLINES TO MODEL it, because `verify()` is a public entry
  point whose "must already have passed type checking" precondition a library
  caller can violate — and when it is violated the datatype-group closure has
  no fixed point, so the walk does not return.  Measured: `verify()` called
  directly on a check-refused program did not come back within 60 s.

A second copy of the rule in the second consumer would be free to drift from
the first, and the drift would be invisible — one refusing what the other
models.  Both import this.
"""

from __future__ import annotations

from vera.environment import AdtInfo
from vera.types import AdtType, RefinedType, Type, TypeVar


def adt_names_in(ty: Type, into: set[str]) -> None:
    """Every ADT name occurring in *ty*, head and type arguments alike."""
    if isinstance(ty, RefinedType):
        adt_names_in(ty.base, into)
        return
    if isinstance(ty, AdtType):
        into.add(ty.name)
        for arg in ty.type_args:
            adt_names_in(arg, into)


def recursive_group(
    root: str, registry: dict[str, AdtInfo],
) -> frozenset[str]:
    """The ADT names mutually reachable with *root* through field types.

    Reachability descends type ARGUMENTS as well as a field's own head, so a
    member reached only through a carrier (`Array<A>`, `Tuple<A, Int>`) is in
    the group.  The group is the intersection of what *root* reaches with what
    reaches *root* — exactly the recursive cycle it participates in.  A
    one-way reference is not recursion and has nothing to be regular about.
    """
    def out_edges(name: str) -> set[str]:
        info = registry.get(name)
        if info is None:
            return set()
        seen: set[str] = set()
        for ctor in info.constructors.values():
            for field in ctor.field_types or ():
                adt_names_in(field, seen)
        return seen

    def reachable(start: str) -> set[str]:
        out: set[str] = set()
        stack = [start]
        while stack:
            for nxt in out_edges(stack.pop()):
                if nxt not in out:
                    out.add(nxt)
                    stack.append(nxt)
        return out

    forward = reachable(root)
    return frozenset(n for n in forward if n == root or root in reachable(n))


def _mentions_parameter(ty: Type, params: frozenset[str]) -> bool:
    """Whether any of *params* occurs anywhere inside *ty*."""
    if isinstance(ty, TypeVar):
        return ty.name in params
    if isinstance(ty, RefinedType):
        return _mentions_parameter(ty.base, params)
    if isinstance(ty, AdtType):
        return any(_mentions_parameter(a, params) for a in ty.type_args)
    return False


def first_irregular_occurrence(
    ty: Type,
    group: frozenset[str],
    expected: tuple[str, ...],
    owner: str,
) -> AdtType | None:
    """The first occurrence in *ty* of a *group* member instantiated in a way
    that can grow without bound, or None.

    Read per ARGUMENT of the occurrence, against the enclosing declaration
    ``owner``'s parameters *expected*:

    * a **bare parameter** of the enclosing declaration is fine — that is the
      argument being passed along unchanged, which is what makes the chain
      repeat;
    * an argument **closed** with respect to those parameters is fine too —
      `Expr<Int>`, `Body<Int>`, a zero-argument `Decl` — because a constant
      argument cannot vary from level to level, so the instantiations it
      reaches are finite;
    * an argument that mentions a parameter INSIDE another type constructor —
      `Option<T>`, `Tuple<T, T>` — is the growth case, and is refused: each
      level wraps the last, so no instantiation ever repeats.

    Comparing the whole argument LIST against the enclosing declaration's
    parameter list is what the first implementation did, and it over-rejected
    (PR #1432 re-verification): every mixed-arity mutual pair
    (`Decl { D(Body<Int>) }` with `Body<T> { B(T, Decl) }`) and every
    closed-argument occurrence (`data Expr<T> { Lit(T), Add(Expr<Int>,
    Expr<Int>) }`) was refused although its instantiation closure is finite —
    two members — and it verified at Tier 1 before the rule existed.  The list
    comparison also cannot be stated for a mutual pair whose members differ in
    arity, which is why the rule is per argument.

    One list-level condition survives, and only for an occurrence of the
    declaration ITSELF: a bare parameter must be the parameter of that
    position.  `data R<A, B> { CR(R<B, A>), ZR }` passes every per-argument
    test — both arguments are bare parameters — while permuting them at each
    level, so it is refused positionally, which is the rule spec §2.4 states.
    Across a mutual pair there is no such ordering to keep (the members'
    parameters are their own), and permuting between two types cycles rather
    than growing.

    Typed `AdtType` because the caller names the offending type in its
    diagnostic, and for a mutual pair that name is the OTHER member.
    """
    if isinstance(ty, RefinedType):
        return first_irregular_occurrence(ty.base, group, expected, owner)
    if not isinstance(ty, AdtType):
        return None
    if ty.name in group:
        params = frozenset(expected)
        for index, arg in enumerate(ty.type_args):
            if isinstance(arg, TypeVar) and arg.name in params:
                # Passed along unchanged.  For the declaration's own name the
                # position has to match, or the chain permutes for ever.
                if ty.name == owner and (
                    index >= len(expected) or arg.name != expected[index]
                ):
                    return ty
                continue
            if _mentions_parameter(arg, params):
                return ty
    for arg in ty.type_args:
        found = first_irregular_occurrence(arg, group, expected, owner)
        if found is not None:
            return found
    return None


def _first_parameter_mentioned(
    ty: Type, params: tuple[str, ...],
) -> str | None:
    """The first of *params* occurring anywhere in *ty*, in declaration order."""
    for name in params:
        if _mentions_parameter(ty, frozenset({name})):
            return name
    return None


def suggested_occurrence(
    bad: AdtType, expected: tuple[str, ...], owner: str | None = None,
) -> str:
    """The offending occurrence, repaired (#1429).

    Built from the OCCURRENCE's head, so the arity is preserved by
    construction.  Taking the enclosing declaration's parameters instead
    produced remedies that are not types — a mixed-arity pair was told to
    write `Body` — and would misstate the arity whenever the two members'
    parameter counts differ (PR #1432 re-verification).

    Two repairs, because the rule has two clauses.  For an occurrence of
    another group member there is no positional constraint, so each argument
    that wraps a parameter is unwrapped to the parameter it wraps:
    `B<Option<T>, Int>` -> `B<T, Int>`.  For an occurrence of the declaration
    *itself* the parameters must additionally be in their original positions,
    so every argument that mentions one is replaced by the parameter belonging
    to that position: `R<B, C, D, E, A>` -> `R<A, B, C, D, E>`.  Without that
    second clause a permutation was handed back its own spelling — every
    argument is already a bare parameter, so nothing was unwrapped and the
    "fix" repeated the line it was meant to repair.

    Arguments that mention no parameter are left exactly as written: they are
    the closed case, which the rule allows.
    """
    from vera.types import pretty_type

    if not bad.type_args:
        return bad.name
    params = frozenset(expected)
    repaired: list[str] = []
    for index, arg in enumerate(bad.type_args):
        if not _mentions_parameter(arg, params):
            repaired.append(pretty_type(arg))
            continue
        if bad.name == owner and index < len(expected):
            repaired.append(expected[index])
            continue
        if isinstance(arg, TypeVar):
            repaired.append(pretty_type(arg))
            continue
        param = _first_parameter_mentioned(arg, expected)
        repaired.append(param if param is not None else pretty_type(arg))
    return f"{bad.name}<{', '.join(repaired)}>"


def _strongly_connected_components(
    nodes: list[str], adjacency: dict[str, list[str]],
) -> list[list[str]]:
    """Tarjan's SCCs, iteratively.

    Iterative rather than recursive because the input is a user's module: a
    thousand-declaration chain is one thousand frames deep, which is a
    ``RecursionError`` on the default limit — the same failure mode #1429 is
    about, reintroduced by the fix for it.
    """
    index_of: dict[str, int] = {}
    low: dict[str, int] = {}
    on_stack: set[str] = set()
    stack: list[str] = []
    components: list[list[str]] = []
    counter = 0

    for root in nodes:
        if root in index_of:
            continue
        work: list[tuple[str, int]] = [(root, 0)]
        while work:
            node, edge_i = work[-1]
            if edge_i == 0:
                index_of[node] = counter
                low[node] = counter
                counter += 1
                stack.append(node)
                on_stack.add(node)
            succs = adjacency[node]
            descended = False
            while edge_i < len(succs):
                nxt = succs[edge_i]
                edge_i += 1
                if nxt not in index_of:
                    work[-1] = (node, edge_i)
                    work.append((nxt, 0))
                    descended = True
                    break
                if nxt in on_stack:
                    low[node] = min(low[node], index_of[nxt])
            if descended:
                continue
            work.pop()
            if low[node] == index_of[node]:
                component: list[str] = []
                while True:
                    popped = stack.pop()
                    on_stack.discard(popped)
                    component.append(popped)
                    if popped == node:
                        break
                components.append(component)
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[node])
    return components


class RegularityIndex:
    """One module's recursive groups and regularity verdicts, computed once.

    Built per registry by each consumer, at a point where registration is
    complete.  Asking :func:`recursive_group` per declaration re-walked
    reachability from every member of every group, which is cubic in the
    number of declarations: measured on chains of 300 / 600 / 1000 `data`
    declarations, `vera check` took 1.8 s / 12.5 s / 73 s against 0.5 s
    before the rule existed (PR #1432 re-verification).  The groups are the
    strongly connected components of the one field-reference graph, so one
    SCC pass answers for every declaration at once, and each verdict is then
    derived once and kept.

    A SNAPSHOT of the registry it was built from: this class holds no
    invalidation hook, because it is handed a plain `dict` and cannot observe
    a write to it.  Invalidation is therefore the CALLER's, and each consumer
    keys its cached index on something it does control —
    :meth:`vera.environment.TypeEnv.regularity_index` on the declaration
    counter every `data` registration bumps (and the registry's size, so a
    write that somehow skipped the counter still invalidates), and the SMT
    context on a version it increments at its one `register_adt` site.  Either
    way a stale index is replaced rather than mutated.
    """

    def __init__(self, registry: dict[str, AdtInfo]) -> None:
        self._registry = registry
        self._verdicts: dict[str, tuple[str, int, AdtType] | None] = {}
        nodes = list(registry)
        known = set(nodes)
        adjacency: dict[str, list[str]] = {}
        for name in nodes:
            reached: set[str] = set()
            info = registry[name]
            for ctor in info.constructors.values():
                for field in ctor.field_types or ():
                    adt_names_in(field, reached)
            # Names outside the registry are sinks — they have no fields to
            # follow, so they can never lie on a cycle and never belong to a
            # group.  Dropping them keeps the graph over declarations only.
            adjacency[name] = sorted(reached & known)
        self._adjacency = adjacency
        self._groups: dict[str, frozenset[str]] = {}
        for component in _strongly_connected_components(nodes, adjacency):
            if len(component) > 1:
                shared = frozenset(component)
                for member in component:
                    self._groups[member] = shared
                continue
            # A singleton is a recursive group only if it refers to itself.
            only = component[0]
            self._groups[only] = (
                frozenset(component) if only in adjacency[only]
                else frozenset()
            )

    def group(self, name: str) -> frozenset[str]:
        """The recursive group *name* participates in (empty = no recursion)."""
        return self._groups.get(name, frozenset())

    def irregular(self, name: str) -> tuple[str, int, AdtType] | None:
        """`(constructor, field index, offending occurrence)`, or None."""
        if name in self._verdicts:
            return self._verdicts[name]
        verdict = self._derive(name)
        self._verdicts[name] = verdict
        return verdict

    def _derive(self, name: str) -> tuple[str, int, AdtType] | None:
        info = self._registry.get(name)
        if info is None:
            return None
        group = self.group(name)
        if not group:
            return None
        expected = tuple(info.type_params or ())
        for ctor_name, ctor in info.constructors.items():
            for index, field in enumerate(ctor.field_types or ()):
                bad = first_irregular_occurrence(field, group, expected, name)
                if bad is not None:
                    return ctor_name, index, bad
        return None

    def is_regular(self, name: str) -> bool:
        """Whether *name*'s recursion (if any) is regular."""
        return self.irregular(name) is None


def occurrence_grows(bad: AdtType, expected: tuple[str, ...]) -> bool:
    """Whether *bad* fails by GROWTH rather than by position (#1429).

    True when some argument wraps a parameter inside another type constructor
    — `Nest<Option<T>>`, `Ne<Tuple<T, T>>` — which is the case where the
    varying part is a real sub-expression the author can lift out.  False for
    a pure PERMUTATION (`R<B, A>` inside `R<A, B>`), where every argument is
    already a bare parameter and nothing varies: there is no part to move, and
    advice to move one misdescribes the program (PR #1432 re-verification).

    An occurrence that does both — `R<B, Option<A>>` — answers True, because
    the wrapped argument is present and the advice applies to it.
    """
    params = frozenset(expected)
    return any(
        not isinstance(arg, TypeVar) and _mentions_parameter(arg, params)
        for arg in bad.type_args
    )


def irregular_occurrence(
    name: str, registry: dict[str, AdtInfo],
) -> tuple[str, int, AdtType] | None:
    """`(constructor, field index, offending occurrence)` for the declaration
    *name*, or None when its recursion is regular (or it has none).

    Builds a throwaway :class:`RegularityIndex`.  A consumer asking about more
    than one declaration should hold an index instead — that is the whole
    difference between one SCC pass per module and one per declaration.
    """
    return RegularityIndex(registry).irregular(name)


def is_regular(name: str, registry: dict[str, AdtInfo]) -> bool:
    """Whether *name*'s recursion (if any) is regular."""
    return irregular_occurrence(name, registry) is None
