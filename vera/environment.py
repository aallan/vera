"""Type environment for the Vera type checker.

Manages scope stacks, binding registries, and the De Bruijn slot
reference resolution algorithm.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from vera.types import (
    BOOL,
    FLOAT64,
    INT,
    NAT,
    PRIMITIVES,
    STRING,
    UNIT,
    AdtType,
    ConcreteEffectRow,
    EffectInstance,
    EffectRowType,
    FunctionType,
    PureEffectRow,
    Type,
    TypeVar,
    canonical_type_name,
)


# =====================================================================
# Registry data structures
# =====================================================================

@dataclass
class FunctionInfo:
    """Registered function signature."""
    name: str
    forall_vars: tuple[str, ...] | None
    param_types: tuple[Type, ...]
    return_type: Type
    effect: EffectRowType
    span: object | None = None  # ast.Span
    contracts: tuple[object, ...] = ()  # ast.Contract nodes (for C4)
    param_type_exprs: tuple[object, ...] = ()  # ast.TypeExpr nodes (for C6b)
    visibility: str | None = None  # "public" | "private" | None (C7c)


@dataclass
class AdtInfo:
    """Registered algebraic data type."""
    name: str
    type_params: tuple[str, ...] | None
    constructors: dict[str, ConstructorInfo]
    visibility: str | None = None  # "public" | "private" | None (C7c)


@dataclass
class ConstructorInfo:
    """Registered ADT constructor."""
    name: str
    parent_type: str
    parent_type_params: tuple[str, ...] | None
    field_types: tuple[Type, ...] | None  # None = nullary


@dataclass
class TypeAliasInfo:
    """Registered type alias."""
    name: str
    type_params: tuple[str, ...] | None
    resolved_type: Type


@dataclass
class EffectInfo:
    """Registered effect declaration."""
    name: str
    type_params: tuple[str, ...] | None
    operations: dict[str, OpInfo]


@dataclass
class OpInfo:
    """Registered effect operation."""
    name: str
    param_types: tuple[Type, ...]
    return_type: Type
    parent_effect: str


# =====================================================================
# Binding
# =====================================================================

@dataclass
class Binding:
    """A single binding in the type environment.

    type_name is the *syntactic* name used for slot reference matching.
    Type aliases are OPAQUE: @PosInt.0 counts PosInt bindings, not Int.
    """
    type_name: str       # canonical name for slot matching
    resolved_type: Type  # fully resolved semantic type
    source: str          # "param", "let", "match", "handler", "destruct"


# =====================================================================
# Type environment
# =====================================================================

@dataclass
class TypeEnv:
    """Layered type environment with De Bruijn slot reference resolution."""

    # Scope stack: each scope is a list of bindings (innermost scope last)
    _scopes: list[list[Binding]] = field(default_factory=lambda: [[]])

    # Declaration registries (not scope-stacked)
    functions: dict[str, FunctionInfo] = field(default_factory=dict)
    data_types: dict[str, AdtInfo] = field(default_factory=dict)
    type_aliases: dict[str, TypeAliasInfo] = field(default_factory=dict)
    effects: dict[str, EffectInfo] = field(default_factory=dict)
    constructors: dict[str, ConstructorInfo] = field(default_factory=dict)

    # Type variables currently in scope (from forall<T>)
    type_params: dict[str, TypeVar] = field(default_factory=dict)

    # Context flags
    in_ensures: bool = False
    in_contract: bool = False
    current_return_type: Type | None = None
    current_effect_row: EffectRowType | None = None

    def __post_init__(self) -> None:
        """Register built-in types, effects, and functions."""
        self._register_builtins()

    # -----------------------------------------------------------------
    # Built-ins
    # -----------------------------------------------------------------

    def _register_builtins(self) -> None:
        """Register the built-in types, effects, and functions."""
        # Built-in parameterised ADTs (so constructors are found)
        # Option<T>
        self.data_types["Option"] = AdtInfo(
            name="Option",
            type_params=("T",),
            constructors={
                "None": ConstructorInfo("None", "Option", ("T",), None),
                "Some": ConstructorInfo("Some", "Option", ("T",),
                                        (TypeVar("T"),)),
            },
        )
        for c in self.data_types["Option"].constructors.values():
            self.constructors[c.name] = c

        # Result<T, E>
        self.data_types["Result"] = AdtInfo(
            name="Result",
            type_params=("T", "E"),
            constructors={
                "Ok": ConstructorInfo("Ok", "Result", ("T", "E"),
                                      (TypeVar("T"),)),
                "Err": ConstructorInfo("Err", "Result", ("T", "E"),
                                       (TypeVar("E"),)),
            },
        )
        for c in self.data_types["Result"].constructors.values():
            self.constructors[c.name] = c

        # State<T> effect with get/put
        self.effects["State"] = EffectInfo(
            name="State",
            type_params=("T",),
            operations={
                "get": OpInfo("get", (UNIT,), TypeVar("T"), "State"),
                "put": OpInfo("put", (TypeVar("T"),), UNIT, "State"),
            },
        )

        # IO effect (no operations exposed at type level in C3)
        self.effects["IO"] = EffectInfo(
            name="IO",
            type_params=None,
            operations={},
        )

        # Built-in function: length
        self.functions["length"] = FunctionInfo(
            name="length",
            forall_vars=("T",),
            param_types=(AdtType("Array", (TypeVar("T"),)),),
            return_type=INT,
            effect=PureEffectRow(),
        )

    # -----------------------------------------------------------------
    # Scope management
    # -----------------------------------------------------------------

    def push_scope(self) -> None:
        """Enter a new scope (block, match arm, handler body, fn body)."""
        self._scopes.append([])

    def pop_scope(self) -> None:
        """Exit the current scope."""
        if len(self._scopes) > 1:
            self._scopes.pop()

    def bind(self, type_name: str, resolved_type: Type, source: str) -> None:
        """Add a binding to the current (innermost) scope."""
        self._scopes[-1].append(Binding(type_name, resolved_type, source))

    # -----------------------------------------------------------------
    # Slot reference resolution (De Bruijn counting)
    # -----------------------------------------------------------------

    def resolve_slot(self, type_name: str, index: int) -> Type | None:
        """Resolve @T.n by counting bindings whose canonical type_name matches.

        Walks scopes innermost-to-outermost.  Returns the resolved type of
        the n-th match, or None if fewer than n+1 bindings exist.
        """
        count = 0
        # Walk scopes from innermost to outermost
        for scope in reversed(self._scopes):
            # Walk bindings from most recent to earliest within each scope
            for binding in reversed(scope):
                if binding.type_name == type_name:
                    if count == index:
                        return binding.resolved_type
                    count += 1
        return None

    def count_bindings(self, type_name: str) -> int:
        """Count how many bindings of the given type name are in scope."""
        count = 0
        for scope in self._scopes:
            for binding in scope:
                if binding.type_name == type_name:
                    count += 1
        return count

    def list_bindings(self, type_name: str) -> list[Binding]:
        """List all bindings of the given type name (for error messages)."""
        result = []
        for scope in self._scopes:
            for binding in scope:
                if binding.type_name == type_name:
                    result.append(binding)
        return result

    # -----------------------------------------------------------------
    # Lookups
    # -----------------------------------------------------------------

    def lookup_function(self, name: str) -> FunctionInfo | None:
        """Look up a function by name."""
        return self.functions.get(name)

    def lookup_constructor(self, name: str) -> ConstructorInfo | None:
        """Look up a constructor by name."""
        return self.constructors.get(name)

    def lookup_effect(self, name: str) -> EffectInfo | None:
        """Look up an effect by name."""
        return self.effects.get(name)

    def lookup_effect_op(self, op_name: str,
                         qualifier: str | None = None) -> OpInfo | None:
        """Look up an effect operation, optionally qualified.

        If qualifier is given, look only in that effect.
        Otherwise, search all effects in the current effect row.
        """
        if qualifier:
            eff = self.effects.get(qualifier)
            if eff and op_name in eff.operations:
                return eff.operations[op_name]
            return None

        # Search effects in the current effect row
        if isinstance(self.current_effect_row, ConcreteEffectRow):
            for ei in self.current_effect_row.effects:
                eff = self.effects.get(ei.name)
                if eff and op_name in eff.operations:
                    return eff.operations[op_name]

        # Also search all registered effects (for handler clauses)
        for eff in self.effects.values():
            if op_name in eff.operations:
                return eff.operations[op_name]

        return None

    def is_type_name(self, name: str) -> bool:
        """Check if a name refers to a known type (primitive, ADT, or alias)."""
        return (name in PRIMITIVES
                or name in self.data_types
                or name in self.type_aliases)
