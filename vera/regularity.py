"""Regular recursion in `data` declarations — ONE derivation (#1429).

A recursive occurrence of a type inside its own declaration must instantiate
that type at the declaration's own type parameters, in order.
`data List<T> { Cons(T, List<T>), Nil }` does; `data Nest<T> {
N(Nest<Option<T>>), Z }` does not — its argument grows at every level, so the
instantiation chain `Nest<Int>` -> `Nest<Option<Int>>` ->
`Nest<Option<Option<Int>>>` never repeats and the type has no finite set of
instantiations.

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


def first_irregular_occurrence(
    ty: Type, group: frozenset[str], expected: tuple[str, ...],
) -> AdtType | None:
    """The first occurrence in *ty* of a *group* member instantiated at
    anything but *expected*, or None.

    Typed `AdtType` rather than `Type` because the caller names the offending
    type in its diagnostic, and for a mutual pair that name is the OTHER
    member: `data A<T> { CA(B<Option<T>>) }` must say `B<T>`, not `A<T>`
    (PR #1432 review).
    """
    if isinstance(ty, RefinedType):
        return first_irregular_occurrence(ty.base, group, expected)
    if not isinstance(ty, AdtType):
        return None
    if ty.name in group:
        actual = tuple(
            arg.name if isinstance(arg, TypeVar) else None
            for arg in ty.type_args
        )
        if actual != expected:
            return ty
    for arg in ty.type_args:
        found = first_irregular_occurrence(arg, group, expected)
        if found is not None:
            return found
    return None


def irregular_occurrence(
    name: str, registry: dict[str, AdtInfo],
) -> tuple[str, int, AdtType] | None:
    """`(constructor, field index, offending occurrence)` for the declaration
    *name*, or None when its recursion is regular (or it has none)."""
    info = registry.get(name)
    if info is None:
        return None
    group = recursive_group(name, registry)
    if not group:
        return None
    expected = tuple(info.type_params or ())
    for ctor_name, ctor in info.constructors.items():
        for index, field in enumerate(ctor.field_types or ()):
            bad = first_irregular_occurrence(field, group, expected)
            if bad is not None:
                return ctor_name, index, bad
    return None


def is_regular(name: str, registry: dict[str, AdtInfo]) -> bool:
    """Whether *name*'s recursion (if any) is regular."""
    return irregular_occurrence(name, registry) is None
