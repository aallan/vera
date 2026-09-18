"""The one enumeration of the containers whose ELEMENTS can carry refinements.

A refinement can be written one level inside a type — `Array<Pos>`,
`Map<String, Pos>`, `Set<Pos>` — and then the predicate belongs to the
container's elements rather than to the slot.  Three components have to agree
about that: the verifier states the goal ("every element satisfies P"), code
generation plants the boundary guard that checks it, and the narrowing walk
decides whether there is anything to obligate at all.

Before this module each container answered separately.  `Array` had an SMT
carrier sort with `index_`/`length_` observers and an element-wise guard loop;
`Map` and `Set` reached no sort branch at all and fell through to an
unconstrained integer, so their element refinements could only be disclosed.
"Add Map, then add Set" would have meant a third and a fourth lowering, which
is the shape #1430 is an instance of rather than a fix for.

What makes one lowering possible is that every container already projects to a
SEQUENCE: `map_values`, `map_keys` and `set_to_array` are built-ins, and on the
code-generation side each is a host import returning an array's `(ptr, len)`
pair.  So a carrier is not "a sort with a membership relation" — it is a thing
that projects to elements, and once the projection is named the element fact
(a bounded quantifier over the sequence's indices) and the element guard (one
loop over `ptr`/`len`) are each written once.  An `Array` is the carrier whose
projection is the identity.

The module holds no analysis.  It says WHICH element positions a type has, what
each is called in a diagnostic, and which built-in projects it; whether a
particular element's refinement can be stated, and whether its base can be
lowered into a guard, stay with the components that can answer them.
"""

from __future__ import annotations

from dataclasses import dataclass

from vera.types import AdtType, RefinedType, Type


@dataclass(frozen=True)
class ElementCarrier:
    """One element position of one container type.

    *projection* is the built-in that turns the container into an array of
    these elements, or None when the container IS that array.  It is the only
    thing the three lowerings differ by, which is why it is data here rather
    than a branch in each of them.
    """

    #: The diagnostic site name — the same string the guard table and the
    #: obligation stream use, so a reader sees which position was meant.
    kind: str
    #: The Vera type of one element, refinements intact.
    element_type: Type
    #: The built-in projecting the container to an `Array` of these elements,
    #: or None for `Array` itself.
    projection: str | None


#: Container name -> its element positions, as (kind, type-argument index,
#: projection).  A `Map` has TWO: a refinement can be written on either the
#: key or the value, and they are separate goals with separate projections.
#:
#: Public, because the two consumers hold different things: the verifier has
#: the checker's semantic types and reads it through
#: :func:`element_carriers`, while code generation has type EXPRESSIONS and an
#: alias table and reads the table directly after resolving its own aliases —
#: the same split :func:`vera.narrowing.narrows_into_refinement` makes by
#: taking caller-produced chains.  What must not differ between them is the
#: LIST, and that is what lives here.
CARRIER_POSITIONS: dict[str, tuple[tuple[str, int, str | None], ...]] = {
    "Array": (("array element", 0, None),),
    "Map": (("map key", 0, "map_keys"), ("map value", 1, "map_values")),
    "Set": (("set element", 0, "set_to_array"),),
}


def element_carriers(ty: Type | None) -> tuple[ElementCarrier, ...]:
    """The element positions *ty* has, in declaration order.

    Empty for anything that is not one of the three containers — an ADT with
    constructor decomposition is not a carrier, because its fields are reached
    by accessors and the structural walk already states them, and a recursive
    ADT is not one either: there is nothing to enumerate and no boundary can
    check it.
    """
    if isinstance(ty, RefinedType):
        ty = ty.base
    if not isinstance(ty, AdtType):
        return ()
    spec = CARRIER_POSITIONS.get(ty.name)
    if spec is None:
        return ()
    out: list[ElementCarrier] = []
    for kind, arg_index, projection in spec:
        if arg_index >= len(ty.type_args):
            continue
        out.append(ElementCarrier(
            kind=kind,
            element_type=ty.type_args[arg_index],
            projection=projection,
        ))
    return tuple(out)


def is_carrier(ty: Type | None) -> bool:
    """Whether *ty* is one of the container types with element positions."""
    return bool(element_carriers(ty))


def projected_carrier_name(ty: Type | None) -> str | None:
    """The container's name when *ty* is a carrier reached through a
    PROJECTION — a `Map` or a `Set` — and None otherwise.

    An `Array` is excluded because it is its own element sequence: it already
    has a Z3 sort and observers, and the arm that asks this question is the
    one deciding whether to mint a carrier sort for a container that has
    none.
    """
    if isinstance(ty, RefinedType):
        ty = ty.base
    if not isinstance(ty, AdtType):
        return None
    spec = CARRIER_POSITIONS.get(ty.name)
    if spec is None or all(p is None for _k, _i, p in spec):
        return None
    return ty.name


#: The binder positions where code generation plants an ELEMENT guard, and
#: the emitter that plants it (#1430).
#:
#: A SEPARATE roster from `narrowing.REFINED_BIND_GUARDED_SITES`, which
#: answers the question for the slot's own §2.6.5 predicate.  The element
#: guard is a different lowering with a different reach — it walks a sequence
#: — so a site in that roster is not automatically in this one, and reading
#: the scalar roster for this question is what let a `tier3` be recorded at a
#: closure boundary whose module carried no element loop at all.
#:
#: Each value names the FUNCTION that emits for that position, and
#: `test_the_element_guard_roster_matches_where_it_is_wired` holds the two
#: together: it scans the code-generation layer for the emitter's call sites,
#: resolves each to its enclosing function, and asserts the two sets match.
#: Each value is the emitting function and the ROLE it emits under, because
#: neither alone separates the four: file granularity let the `return type`
#: entry point at `functions.py` — which wires the PARAMETER loop — while the
#: return boundary is emitted in `contracts.py`, and function granularity
#: collapses the two closure positions onto `_compile_lifted_closure`, so
#: deleting one left the comparison unchanged (PR #1447 review, F3).  The
#: role is the emitter's own argument, the word its trap message prints, so
#: the key is data the call site already carries.  Deleting ANY single entry
#: reds the test, and a cell drives that once per entry rather than once.
#:
#: Membership is necessary and not sufficient.  The TYPE half is
#: `ContractVerifier._element_guard_emitted`, and at a `call argument` there
#: is a third question — whether the CALLEE has a prologue at all, which a
#: built-in does not (`_element_callee_guards`).
ELEMENT_GUARD_SITES: dict[str, str] = {
    "call argument": "_compile_fn/parameter",
    "return type": "_compile_postconditions/return value",
    "closure argument": "_compile_lifted_closure/parameter",
    "closure return": "_compile_lifted_closure/return value",
}
