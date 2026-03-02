"""Internal type representation for the Vera type checker.

These semantic types are distinct from the syntactic AST TypeExpr nodes.
AST types mirror what the user wrote; these represent resolved, canonical
types suitable for comparison, subtyping, and substitution.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from vera import ast as _ast


# =====================================================================
# Type hierarchy
# =====================================================================

@dataclass(frozen=True)
class Type:
    """Abstract base for all resolved types."""


@dataclass(frozen=True)
class PrimitiveType(Type):
    """A built-in primitive type (Int, Nat, Bool, Float64, ...)."""
    name: str


@dataclass(frozen=True)
class AdtType(Type):
    """A parameterised algebraic data type (Array<T>, Option<Int>, user ADTs)."""
    name: str
    type_args: tuple[Type, ...]  # () for non-parameterised


@dataclass(frozen=True)
class FunctionType(Type):
    """A function type: params -> return with effect row."""
    params: tuple[Type, ...]
    return_type: Type
    effect: EffectRowType


@dataclass(frozen=True)
class RefinedType(Type):
    """A refinement type.  Tracks the base type and preserves the predicate
    AST node for later verification (C4).  In C3, treated as its base type
    for subtyping purposes."""
    base: Type
    predicate: _ast.Expr  # kept opaque — not verified in C3


@dataclass(frozen=True)
class TypeVar(Type):
    """A universally-quantified type variable (from forall<T>)."""
    name: str


@dataclass(frozen=True)
class UnknownType(Type):
    """Placeholder for unresolved or error-recovery types.

    Any operation involving UnknownType silently propagates it,
    preventing cascading error messages."""


# =====================================================================
# Effect types
# =====================================================================

@dataclass(frozen=True)
class EffectRowType:
    """Abstract base for effect rows."""


@dataclass(frozen=True)
class PureEffectRow(EffectRowType):
    """The empty effect row (effects(pure))."""


@dataclass(frozen=True)
class EffectInstance:
    """A single effect instantiation, e.g. State<Int>."""
    name: str
    type_args: tuple[Type, ...]

    def __hash__(self) -> int:
        return hash((self.name, self.type_args))


@dataclass(frozen=True)
class ConcreteEffectRow(EffectRowType):
    """A set of concrete effects, possibly with an open row variable tail."""
    effects: frozenset[EffectInstance]
    row_var: str | None = None  # None = closed row; "E" = open variable


# =====================================================================
# Primitive constants
# =====================================================================

INT = PrimitiveType("Int")
NAT = PrimitiveType("Nat")
BOOL = PrimitiveType("Bool")
FLOAT64 = PrimitiveType("Float64")
STRING = PrimitiveType("String")
BYTE = PrimitiveType("Byte")
UNIT = PrimitiveType("Unit")
NEVER = PrimitiveType("Never")

PRIMITIVES: dict[str, Type] = {
    "Int": INT,
    "Nat": NAT,
    "Bool": BOOL,
    "Float64": FLOAT64,
    "String": STRING,
    "Byte": BYTE,
    "Unit": UNIT,
    "Never": NEVER,
}

# Removed aliases — used by the checker to produce helpful error messages
# when a user writes an old alias name instead of the canonical type.
REMOVED_ALIASES: dict[str, str] = {
    "Float": "Float64",
}

# Numeric types (for operator checking)
NUMERIC_TYPES: frozenset[Type] = frozenset({INT, NAT, FLOAT64})
ORDERABLE_TYPES: frozenset[Type] = frozenset({INT, NAT, FLOAT64, BYTE, STRING})


# =====================================================================
# Utility functions
# =====================================================================

def canonical_type_name(type_name: str,
                        type_args: tuple[Type, ...] | None = None) -> str:
    """Form the canonical string used for slot reference matching.

    Type aliases are OPAQUE: @PosInt.0 and @Int.0 are separate namespaces.
    Parameterised types include args: "Option<Int>", "List<T>".
    """
    if not type_args:
        return type_name
    arg_strs = ", ".join(pretty_type(a) for a in type_args)
    return f"{type_name}<{arg_strs}>"


def pretty_type(ty: Type) -> str:
    """Human-readable type string for error messages."""
    if isinstance(ty, PrimitiveType):
        return ty.name
    if isinstance(ty, AdtType):
        if ty.type_args:
            args = ", ".join(pretty_type(a) for a in ty.type_args)
            return f"{ty.name}<{args}>"
        return ty.name
    if isinstance(ty, FunctionType):
        params = ", ".join(pretty_type(p) for p in ty.params)
        ret = pretty_type(ty.return_type)
        eff = pretty_effect(ty.effect)
        return f"fn({params} -> {ret}) {eff}"
    if isinstance(ty, RefinedType):
        return f"{{@{pretty_type(ty.base)} | ...}}"
    if isinstance(ty, TypeVar):
        return ty.name
    if isinstance(ty, UnknownType):
        return "?"
    return str(ty)


def pretty_effect(eff: EffectRowType) -> str:
    """Human-readable effect row string."""
    if isinstance(eff, PureEffectRow):
        return "effects(pure)"
    if isinstance(eff, ConcreteEffectRow):
        parts = sorted(
            canonical_type_name(e.name, e.type_args if e.type_args else None)
            for e in eff.effects
        )
        if eff.row_var:
            parts.append(eff.row_var)
        return f"effects(<{', '.join(parts)}>)"
    return "effects(?)"


def base_type(ty: Type) -> Type:
    """Strip refinement wrappers to get the underlying base type."""
    while isinstance(ty, RefinedType):
        ty = ty.base
    return ty


def is_subtype(sub: Type, sup: Type) -> bool:
    """Check if sub <: sup under the subtyping rules.

    Rules:
    1. Reflexivity: T <: T (including TypeVar("X") <: TypeVar("X"))
    2. Never <: T for all T
    3a. Nat <: Int (widening — always safe)
    3b. Int <: Nat (checker permits; verifier enforces non-negativity via Z3)
    4. ADT structural: same name + covariant subtyping on type args
    5. RefinedType(base, _) <: base
    6. RefinedType(base, _) <: T if base <: T
    7. T <: RefinedType(base, _) if T <: base (predicate enforced by verifier)
    8. UnknownType is compatible with everything (error recovery)

    TypeVar is NOT compatible with concrete types.  TypeVar equality is
    handled by reflexivity (rule 1).  At call sites, type inference
    substitutes TypeVars before subtype checks; unresolved TypeVars are
    skipped by the caller.
    """
    # Unknown propagates silently
    if isinstance(sub, UnknownType) or isinstance(sup, UnknownType):
        return True

    # Reflexivity (structural equality)
    if types_equal(sub, sup):
        return True

    # Never is bottom
    if isinstance(sub, PrimitiveType) and sub.name == "Never":
        return True

    # Nat <: Int (widening — always safe)
    # Int <: Nat (checker permits; verifier enforces >= 0 via Z3)
    if isinstance(sub, PrimitiveType) and isinstance(sup, PrimitiveType):
        if sub.name == "Nat" and sup.name == "Int":
            return True
        if sub.name == "Int" and sup.name == "Nat":
            return True

    # ADT with compatible type args (e.g. Option<T> <: Option<T>)
    if isinstance(sub, AdtType) and isinstance(sup, AdtType):
        if sub.name == sup.name and len(sub.type_args) == len(sup.type_args):
            return all(
                is_subtype(sa, pa) for sa, pa in
                zip(sub.type_args, sup.type_args)
            )

    # Refinement to base: { @T | P } <: T
    if isinstance(sub, RefinedType):
        return is_subtype(sub.base, sup)

    # Refinement on the sup side: T <: { @T | P } only if T <: base
    # (predicate enforced by the contract verifier, not the type checker)
    if isinstance(sup, RefinedType):
        return is_subtype(sub, sup.base)

    return False


def types_equal(a: Type, b: Type) -> bool:
    """Structural type equality."""
    if isinstance(a, UnknownType) or isinstance(b, UnknownType):
        return True
    if type(a) != type(b):
        return False
    if isinstance(a, PrimitiveType) and isinstance(b, PrimitiveType):
        return a.name == b.name
    if isinstance(a, AdtType) and isinstance(b, AdtType):
        return (a.name == b.name
                and len(a.type_args) == len(b.type_args)
                and all(types_equal(x, y)
                        for x, y in zip(a.type_args, b.type_args)))
    if isinstance(a, FunctionType) and isinstance(b, FunctionType):
        return (len(a.params) == len(b.params)
                and all(types_equal(x, y)
                        for x, y in zip(a.params, b.params))
                and types_equal(a.return_type, b.return_type))
    if isinstance(a, RefinedType) and isinstance(b, RefinedType):
        return types_equal(a.base, b.base)
    if isinstance(a, TypeVar) and isinstance(b, TypeVar):
        return a.name == b.name
    return a == b


def contains_typevar(ty: Type) -> bool:
    """True if *ty* contains any TypeVar anywhere in its structure."""
    if isinstance(ty, TypeVar):
        return True
    if isinstance(ty, AdtType):
        return any(contains_typevar(a) for a in ty.type_args)
    if isinstance(ty, FunctionType):
        return (any(contains_typevar(p) for p in ty.params)
                or contains_typevar(ty.return_type))
    if isinstance(ty, RefinedType):
        return contains_typevar(ty.base)
    return False


def substitute(ty: Type, mapping: dict[str, Type]) -> Type:
    """Apply a type-variable substitution."""
    if isinstance(ty, TypeVar):
        return mapping.get(ty.name, ty)
    if isinstance(ty, AdtType):
        new_args = tuple(substitute(a, mapping) for a in ty.type_args)
        return AdtType(ty.name, new_args)
    if isinstance(ty, FunctionType):
        new_params = tuple(substitute(p, mapping) for p in ty.params)
        new_ret = substitute(ty.return_type, mapping)
        return FunctionType(new_params, new_ret, ty.effect)
    if isinstance(ty, RefinedType):
        return RefinedType(substitute(ty.base, mapping), ty.predicate)
    # PrimitiveType, UnknownType — unchanged
    return ty


def substitute_effect(eff: EffectRowType,
                      mapping: dict[str, Type]) -> EffectRowType:
    """Apply a type-variable substitution to an effect row."""
    if isinstance(eff, ConcreteEffectRow):
        new_effects = frozenset(
            EffectInstance(e.name, tuple(substitute(a, mapping)
                                        for a in e.type_args))
            for e in eff.effects
        )
        return ConcreteEffectRow(new_effects, eff.row_var)
    return eff
