"""Check-time ``Eq``-derivability predicate (#928).

`==` / `!=` (and the ``eq`` ability operation) are the surface spelling of
the ``Eq`` ability (spec §9.8.1).  ``Eq`` derives **structurally** (§9.8.2,
#773): an ``Eq`` primitive, a *simple* enum, or an ADT every constructor
field of which is itself ``Eq`` — recursing through nested ADTs, including
recursive and mutually-recursive types.  A field with no ``Eq`` semantics
— ``Array`` / ``Map`` / ``Set`` / a host handle / a **function** / a
``Tuple`` — makes the whole type non-derivable.

Before #928 the checker's ``==`` / ``!=`` gate only required the two
operands to share a type; it never asked whether that type was actually
``Eq``.  A non-``Eq`` ``==`` (two function values, or a ``State<Rec>`` /
composite whose field is a ``Map``) then reached codegen, where — unlike the
direct-ADT path that routes through ``_translate_adt_eq`` and raises a clean
E613 — it fell to a raw ``i32`` / pointer comparison that never consults the
structural-``Eq`` derivability dispatch.  The result was a **silent
pointer-identity comparison** accepted with zero diagnostics: a "passing"
program returning a possibly-wrong answer (the equality sibling of #921's
ordering hole).

This module is the earliest, loudest gate: it rejects a non-``Eq`` ``==`` /
``!=`` / ``eq`` at **check** time (E243), mirroring how #921 gates ordering
(E242).  Its verdict MUST agree exactly with codegen's structural-``Eq``
derivability dispatch (``_adt_satisfies_eq`` / ``_type_eq_derivable`` in
``vera/codegen/monomorphize.py``) — accept exactly what codegen can derive
and reject exactly the complement — or the checker↔codegen lockstep (#732)
breaks.  The invariant is proven by the cross-component differential
``tests/test_adt_eq_reject_928.py::test_eq_gate_matches_codegen``.
"""

from __future__ import annotations

from vera.environment import TypeEnv
from vera.types import (
    AdtType,
    FunctionType,
    PrimitiveType,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    base_type,
)

# The ``Eq`` primitives — the checker mirror of codegen's ``_EQ_TYPES``
# (``vera/codegen/monomorphize.py``).  String is included (compared by
# content), as is Unit (a zero-field value that is trivially equal).
EQ_PRIMITIVES: frozenset[str] = frozenset({
    "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit",
})

# Built-in parametric container / handle types with NO auto-derived ``Eq``.
# Codegen's ``_type_eq_derivable`` rejects these (they are not in ``_EQ_TYPES``
# and not user ADTs with recursable field metadata): a field of one of these
# makes the enclosing ADT non-derivable, and a direct ``==`` on one is itself
# non-``Eq``.  ``Tuple`` is here too — codegen's ``_adt_satisfies_eq`` returns
# ``False`` for ``Tuple`` (its registered layout is a variadic zero-field
# placeholder with no per-instantiation component metadata; spec §9.8.2 lists
# tuple fields among the non-derivable ones) until tuple structural ``Eq``
# lands.
NON_EQ_ADTS: frozenset[str] = frozenset({
    "Array", "Map", "Set", "Tuple",
})


def is_eq_derivable(
    ty: Type,
    env: TypeEnv,
    _seen: frozenset[str] = frozenset(),
) -> bool:
    """Whether *ty* satisfies ``Eq`` via structural auto-derivation (§9.8.2).

    Mirrors codegen's ``_adt_satisfies_eq`` / ``_type_eq_derivable`` exactly so
    the checker rejects precisely the set codegen cannot derive (#928, #732):

    - An ``Eq`` primitive (Int/Nat/Bool/Float64/String/Byte/Unit) → derivable.
    - A ``FunctionType`` → **not** derivable (functions have no value equality;
      a raw pointer compare is identity, not equality).
    - A built-in non-``Eq`` container/handle (``Array`` / ``Map`` / ``Set``) or
      ``Tuple`` → not derivable.
    - A user / prelude ADT → derivable iff every constructor field type is
      (recursively) derivable, with the ADT's type parameters substituted by
      the concrete type arguments.  A recursive occurrence is cycle-broken via
      ``_seen`` (so ``List<Int>`` derives rather than looping).
    - ``UnknownType`` → derivable (error recovery: never pile a spurious E243
      on top of an already-reported type error).
    - A bare ``TypeVar`` is **not** decided here — callers defer it (inside a
      ``forall<T where Eq<T>>`` body the constraint promises derivability, and
      the monomorphizer's E613 gate re-checks each concrete instantiation).
    """
    ty = base_type(ty)  # a refinement is Eq iff its base is (predicate aside)

    if isinstance(ty, UnknownType):
        return True
    if isinstance(ty, PrimitiveType):
        return ty.name in EQ_PRIMITIVES
    if isinstance(ty, FunctionType):
        return False
    if isinstance(ty, TypeVar):
        # Deferred: the caller decides (a constrained-generic body defers to
        # the ability constraint + the codegen E613 instantiation gate).  A
        # conservative ``False`` here would false-reject the legitimate
        # constrained form; a ``True`` would false-accept.  Neither is right,
        # so a TypeVar must never reach this predicate as a decision point —
        # callers skip it.  Treat as derivable to avoid a spurious reject if
        # one leaks through nested substitution (matches codegen, which defers
        # unresolved params to monomorphization).
        return True
    if isinstance(ty, RefinedType):  # pragma: no cover — base_type stripped it
        return is_eq_derivable(ty.base, env, _seen)
    if isinstance(ty, AdtType):
        return _adt_is_eq_derivable(ty, env, _seen)
    return False


def _adt_is_eq_derivable(
    ty: AdtType,
    env: TypeEnv,
    seen: frozenset[str],
) -> bool:
    """Structural ``Eq`` for a (possibly parametric) ADT — see ``is_eq_derivable``."""
    if ty.name in NON_EQ_ADTS:
        # Array / Map / Set / Tuple — no auto-derived structural Eq.
        return False

    info = env.data_types.get(ty.name)
    if info is None:
        # Not a registered ADT (nor a known non-Eq container): a host handle
        # or otherwise opaque parametric type.  Codegen has no layout to
        # recurse, so it is non-derivable.
        return False

    # #1429: stop at a declaration whose recursion is NON-REGULAR.  The
    # cycle-break below keys on the fully-applied name, which terminates a
    # regular recursion because its instantiation closure is finite — and
    # never fires for a growing one, where every level's key is new:
    # `Nest<Int>` -> `Nest<Option<Int>>` -> `Nest<Option<Option<Int>>>`.
    # Measured, `==`, `!=` and `eq(...)` over such a value each recursed this
    # walk into a `RecursionError`, surfacing as an internal-compiler `E699`
    # that also discarded the E129 the checker had already recorded
    # (PR #1432 re-verification).
    #
    # Asked of EVERY member the walk reaches, not just the root: regularity is
    # per declaration, so a regular `A<T> { CA(B<T>) }` can reach an irregular
    # `B`, and checking only the entry type would still not terminate.  With
    # this, the walk descends only through members whose closure is finite, so
    # the key guard below always terminates — a guarantee from the rule rather
    # than a bound on depth.  Through the ENV's shared index, so asking it per
    # field of every `==` costs a dict lookup rather than a walk of the whole
    # declaration graph.
    if ty.name in env.refused_non_regular:
        # Already refused as non-regular, with E129 recorded against the
        # declaration itself.  Answer as the cycle-break below does so the
        # user is shown that one root cause and not a second diagnostic
        # about equality on a type they may not declare at all.  Safe to
        # claim: a module carrying E129 never reaches codegen.
        return True
    if not env.regularity_index().is_regular(ty.name):
        return False

    # Cycle-break on the fully-applied name so a recursive ADT (List<Int>)
    # terminates instead of unfolding forever — the same guard codegen uses.
    key = _canonical(ty)
    if key in seen:
        return True
    seen = seen | {key}

    # Map the ADT's declared type parameters to this instantiation's concrete
    # arguments, so a type-parameter field (``T`` in ``Cons(T, List<T>)``) is
    # judged by its concrete argument, and a nested declared field
    # (``List<T>`` → ``List<Int>``) recurses with the substitution applied.
    params = info.type_params or ()
    mapping: dict[str, Type] = dict(zip(params, ty.type_args))

    for ctor in info.constructors.values():
        if ctor.field_types is None:  # nullary constructor — trivially Eq
            continue
        for field_ty in ctor.field_types:
            resolved = _substitute(field_ty, mapping)
            if not is_eq_derivable(resolved, env, seen):
                return False
    return True


def _substitute(ty: Type, mapping: dict[str, Type]) -> Type:
    """Substitute type parameters by concrete arguments (checker-local).

    A thin structural walk — mirrors ``vera.types.substitute`` but is inlined
    here to avoid importing checker orchestration into this leaf module, and to
    substitute inside ``AdtType`` / ``FunctionType`` / ``RefinedType`` exactly
    as codegen's field-type substitution does.
    """
    if isinstance(ty, TypeVar):
        return mapping.get(ty.name, ty)
    if isinstance(ty, AdtType):
        return AdtType(ty.name, tuple(_substitute(a, mapping)
                                      for a in ty.type_args))
    if isinstance(ty, FunctionType):
        return FunctionType(
            tuple(_substitute(p, mapping) for p in ty.params),
            _substitute(ty.return_type, mapping),
            ty.effect,
        )
    if isinstance(ty, RefinedType):
        return RefinedType(_substitute(ty.base, mapping), ty.predicate)
    return ty


def _canonical(ty: AdtType) -> str:
    """A stable string key for cycle-breaking (base name + type-arg shape)."""
    if not ty.type_args:
        return ty.name
    return f"{ty.name}<{', '.join(_canonical_of(a) for a in ty.type_args)}>"


def _canonical_of(ty: Type) -> str:
    ty = base_type(ty)
    if isinstance(ty, PrimitiveType):
        return ty.name
    if isinstance(ty, TypeVar):
        return ty.name
    if isinstance(ty, AdtType):
        return _canonical(ty)
    if isinstance(ty, FunctionType):
        return "fn"
    return "?"
