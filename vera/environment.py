"""Type environment for the Vera type checker.

Manages scope stacks, binding registries, and the De Bruijn slot
reference resolution algorithm.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from vera.types import (
    BOOL,
    BYTE,
    FLOAT64,
    INT,
    NAT,
    NEVER,
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
    forall_constraints: tuple[object, ...] = ()  # ast.AbilityConstraint nodes


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
    """Registered effect or ability operation."""
    name: str
    param_types: tuple[Type, ...]
    return_type: Type
    parent_effect: str  # also used for parent ability name


@dataclass
class AbilityInfo:
    """Registered ability declaration."""
    name: str
    type_params: tuple[str, ...] | None
    operations: dict[str, OpInfo]


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
    abilities: dict[str, AbilityInfo] = field(default_factory=dict)
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

        # UrlParts — URL components (scheme, authority, path, query, fragment)
        self.data_types["UrlParts"] = AdtInfo(
            name="UrlParts",
            type_params=(),
            constructors={
                "UrlParts": ConstructorInfo(
                    "UrlParts", "UrlParts", (),
                    (STRING, STRING, STRING, STRING, STRING),
                ),
            },
        )
        for c in self.data_types["UrlParts"].constructors.values():
            self.constructors[c.name] = c

        # Json — structured data interchange (§9.7.1)
        _JSON_TYPE = AdtType("Json", ())
        _ARR_JSON = AdtType("Array", (_JSON_TYPE,))
        _MAP_STR_JSON = AdtType("Map", (STRING, _JSON_TYPE))
        self.data_types["Json"] = AdtInfo(
            name="Json",
            type_params=(),
            constructors={
                "JNull": ConstructorInfo(
                    "JNull", "Json", (), None,
                ),
                "JBool": ConstructorInfo(
                    "JBool", "Json", (), (BOOL,),
                ),
                "JNumber": ConstructorInfo(
                    "JNumber", "Json", (), (FLOAT64,),
                ),
                "JString": ConstructorInfo(
                    "JString", "Json", (), (STRING,),
                ),
                "JArray": ConstructorInfo(
                    "JArray", "Json", (), (_ARR_JSON,),
                ),
                "JObject": ConstructorInfo(
                    "JObject", "Json", (), (_MAP_STR_JSON,),
                ),
            },
        )
        for c in self.data_types["Json"].constructors.values():
            self.constructors[c.name] = c

        # Future<T> — async computation result (WASM-transparent wrapper)
        self.data_types["Future"] = AdtInfo(
            name="Future",
            type_params=("T",),
            constructors={
                "Future": ConstructorInfo(
                    "Future", "Future", ("T",), (TypeVar("T"),),
                ),
            },
        )
        for c in self.data_types["Future"].constructors.values():
            self.constructors[c.name] = c

        # MdInline — inline Markdown elements (§9.3.5 / §9.7.3)
        _MD_INLINE = AdtType("MdInline", ())
        _ARR_MD_INLINE = AdtType("Array", (_MD_INLINE,))
        self.data_types["MdInline"] = AdtInfo(
            name="MdInline",
            type_params=(),
            constructors={
                "MdText": ConstructorInfo(
                    "MdText", "MdInline", (), (STRING,),
                ),
                "MdCode": ConstructorInfo(
                    "MdCode", "MdInline", (), (STRING,),
                ),
                "MdEmph": ConstructorInfo(
                    "MdEmph", "MdInline", (), (_ARR_MD_INLINE,),
                ),
                "MdStrong": ConstructorInfo(
                    "MdStrong", "MdInline", (), (_ARR_MD_INLINE,),
                ),
                "MdLink": ConstructorInfo(
                    "MdLink", "MdInline", (),
                    (_ARR_MD_INLINE, STRING),
                ),
                "MdImage": ConstructorInfo(
                    "MdImage", "MdInline", (), (STRING, STRING),
                ),
            },
        )
        for c in self.data_types["MdInline"].constructors.values():
            self.constructors[c.name] = c

        # MdBlock — block-level Markdown elements (§9.3.6 / §9.7.3)
        _MD_BLOCK = AdtType("MdBlock", ())
        _ARR_MD_BLOCK = AdtType("Array", (_MD_BLOCK,))
        _ARR_ARR_MD_BLOCK = AdtType("Array", (_ARR_MD_BLOCK,))
        _ARR_ARR_ARR_MD_INLINE = AdtType(
            "Array", (AdtType("Array", (_ARR_MD_INLINE,)),),
        )
        self.data_types["MdBlock"] = AdtInfo(
            name="MdBlock",
            type_params=(),
            constructors={
                "MdParagraph": ConstructorInfo(
                    "MdParagraph", "MdBlock", (),
                    (_ARR_MD_INLINE,),
                ),
                "MdHeading": ConstructorInfo(
                    "MdHeading", "MdBlock", (),
                    (NAT, _ARR_MD_INLINE),
                ),
                "MdCodeBlock": ConstructorInfo(
                    "MdCodeBlock", "MdBlock", (),
                    (STRING, STRING),
                ),
                "MdBlockQuote": ConstructorInfo(
                    "MdBlockQuote", "MdBlock", (),
                    (_ARR_MD_BLOCK,),
                ),
                "MdList": ConstructorInfo(
                    "MdList", "MdBlock", (),
                    (BOOL, _ARR_ARR_MD_BLOCK),
                ),
                "MdThematicBreak": ConstructorInfo(
                    "MdThematicBreak", "MdBlock", (), (),
                ),
                "MdTable": ConstructorInfo(
                    "MdTable", "MdBlock", (),
                    (_ARR_ARR_ARR_MD_INLINE,),
                ),
                "MdDocument": ConstructorInfo(
                    "MdDocument", "MdBlock", (),
                    (_ARR_MD_BLOCK,),
                ),
            },
        )
        for c in self.data_types["MdBlock"].constructors.values():
            self.constructors[c.name] = c

        # HtmlNode — HTML document nodes (§9.7.4)
        _HTML_NODE = AdtType("HtmlNode", ())
        _MAP_STR_STR = AdtType("Map", (STRING, STRING))
        _ARR_HTML_NODE = AdtType("Array", (_HTML_NODE,))
        self.data_types["HtmlNode"] = AdtInfo(
            name="HtmlNode",
            type_params=(),
            constructors={
                "HtmlElement": ConstructorInfo(
                    "HtmlElement", "HtmlNode", (),
                    (STRING, _MAP_STR_STR, _ARR_HTML_NODE),
                ),
                "HtmlText": ConstructorInfo(
                    "HtmlText", "HtmlNode", (), (STRING,),
                ),
                "HtmlComment": ConstructorInfo(
                    "HtmlComment", "HtmlNode", (), (STRING,),
                ),
            },
        )
        for c in self.data_types["HtmlNode"].constructors.values():
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

        # IO effect — built-in operations for console, file, and process I/O.
        # User-declared `effect IO { ... }` overrides this (backward compat).
        self.effects["IO"] = EffectInfo(
            name="IO",
            type_params=None,
            operations={
                "print": OpInfo("print", (STRING,), UNIT, "IO"),
                "read_line": OpInfo("read_line", (UNIT,), STRING, "IO"),
                "read_file": OpInfo(
                    "read_file", (STRING,),
                    AdtType("Result", (STRING, STRING)), "IO",
                ),
                "write_file": OpInfo(
                    "write_file", (STRING, STRING),
                    AdtType("Result", (UNIT, STRING)), "IO",
                ),
                "args": OpInfo(
                    "args", (UNIT,),
                    AdtType("Array", (STRING,)), "IO",
                ),
                "exit": OpInfo("exit", (INT,), NEVER, "IO"),
                "get_env": OpInfo(
                    "get_env", (STRING,),
                    AdtType("Option", (STRING,)), "IO",
                ),
                # Time and flow-control ops — added for animation
                # loops, rate limiting, elapsed-time measurement
                # (#463).
                "sleep": OpInfo("sleep", (NAT,), UNIT, "IO"),
                "time": OpInfo("time", (UNIT,), NAT, "IO"),
                "stderr": OpInfo("stderr", (STRING,), UNIT, "IO"),
            },
        )

        # Http effect — network access via host imports.
        # Functions using Http.get or Http.post must declare effects(<Http>).
        self.effects["Http"] = EffectInfo(
            name="Http",
            type_params=None,
            operations={
                "get": OpInfo(
                    "get", (STRING,),
                    AdtType("Result", (STRING, STRING)), "Http",
                ),
                "post": OpInfo(
                    "post", (STRING, STRING),
                    AdtType("Result", (STRING, STRING)), "Http",
                ),
            },
        )

        # Diverge effect — marker for potentially non-terminating functions.
        # No operations; its presence in the effect row opts out of
        # termination checking (Chapter 7, Section 7.7.3).
        self.effects["Diverge"] = EffectInfo(
            name="Diverge",
            type_params=None,
            operations={},
        )

        # Async effect — marker for concurrent computation.
        # No operations; async/await are registered as built-in functions
        # with effects(<Async>).  The reference implementation evaluates
        # eagerly (sequential); WASI 0.3 will provide true concurrency.
        self.effects["Async"] = EffectInfo(
            name="Async",
            type_params=None,
            operations={},
        )

        # Random effect — non-determinism via host imports.
        # Functions using Random.* must declare effects(<Random>); the
        # type signature carries the non-determinism explicitly so
        # callers can audit it.  See #465.
        self.effects["Random"] = EffectInfo(
            name="Random",
            type_params=None,
            operations={
                # random_int(low, high) → Int in inclusive range
                # [low, high].  Caller must ensure low <= high.
                "random_int": OpInfo(
                    "random_int", (INT, INT), INT, "Random",
                ),
                # random_float() → Float64 in [0.0, 1.0).  Unit
                # argument erased at the WASM boundary.
                "random_float": OpInfo(
                    "random_float", (UNIT,), FLOAT64, "Random",
                ),
                # random_bool() → Bool.  Coin flip.
                "random_bool": OpInfo(
                    "random_bool", (UNIT,), BOOL, "Random",
                ),
            },
        )

        # Inference effect — LLM calls via host imports.
        # Functions using Inference.complete must declare effects(<Inference>).
        self.effects["Inference"] = EffectInfo(
            name="Inference",
            type_params=None,
            operations={
                "complete": OpInfo(
                    "complete", (STRING,),
                    AdtType("Result", (STRING, STRING)), "Inference",
                ),
            },
        )

        # Ordering ADT — result type for Ord's compare operation (§9.8).
        self.data_types["Ordering"] = AdtInfo(
            name="Ordering",
            type_params=(),
            constructors={
                "Less": ConstructorInfo("Less", "Ordering", (), None),
                "Equal": ConstructorInfo("Equal", "Ordering", (), None),
                "Greater": ConstructorInfo("Greater", "Ordering", (), None),
            },
        )
        for c in self.data_types["Ordering"].constructors.values():
            self.constructors[c.name] = c

        # Built-in abilities (spec §9.8).
        # All use type param "A" (not "T") to avoid confusion with
        # function-level forall<T where Eq<T>>.
        self.abilities["Eq"] = AbilityInfo(
            name="Eq",
            type_params=("A",),
            operations={
                "eq": OpInfo("eq", (TypeVar("A"), TypeVar("A")),
                             BOOL, "Eq"),
            },
        )
        self.abilities["Ord"] = AbilityInfo(
            name="Ord",
            type_params=("A",),
            operations={
                "compare": OpInfo(
                    "compare", (TypeVar("A"), TypeVar("A")),
                    AdtType("Ordering", ()), "Ord"),
            },
        )
        self.abilities["Hash"] = AbilityInfo(
            name="Hash",
            type_params=("A",),
            operations={
                "hash": OpInfo("hash", (TypeVar("A"),), INT, "Hash"),
            },
        )
        self.abilities["Show"] = AbilityInfo(
            name="Show",
            type_params=("A",),
            operations={
                "show": OpInfo("show", (TypeVar("A"),), STRING, "Show"),
            },
        )

        # Built-in array operations
        self.functions["array_length"] = FunctionInfo(
            name="array_length",
            forall_vars=("T",),
            param_types=(AdtType("Array", (TypeVar("T"),)),),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["array_append"] = FunctionInfo(
            name="array_append",
            forall_vars=("T",),
            param_types=(
                AdtType("Array", (TypeVar("T"),)),
                TypeVar("T"),
            ),
            return_type=AdtType("Array", (TypeVar("T"),)),
            effect=PureEffectRow(),
        )
        self.functions["array_range"] = FunctionInfo(
            name="array_range",
            forall_vars=None,
            param_types=(INT, INT),
            return_type=AdtType("Array", (INT,)),
            effect=PureEffectRow(),
        )
        self.functions["array_concat"] = FunctionInfo(
            name="array_concat",
            forall_vars=("T",),
            param_types=(
                AdtType("Array", (TypeVar("T"),)),
                AdtType("Array", (TypeVar("T"),)),
            ),
            return_type=AdtType("Array", (TypeVar("T"),)),
            effect=PureEffectRow(),
        )
        self.functions["array_slice"] = FunctionInfo(
            name="array_slice",
            forall_vars=("T",),
            param_types=(
                AdtType("Array", (TypeVar("T"),)),
                INT,
                INT,
            ),
            return_type=AdtType("Array", (TypeVar("T"),)),
            effect=PureEffectRow(),
        )
        self.functions["array_map"] = FunctionInfo(
            name="array_map",
            forall_vars=("A", "B"),
            param_types=(
                AdtType("Array", (TypeVar("A"),)),
                FunctionType(
                    params=(TypeVar("A"),),
                    return_type=TypeVar("B"),
                    effect=PureEffectRow(),
                ),
            ),
            return_type=AdtType("Array", (TypeVar("B"),)),
            effect=PureEffectRow(),
        )
        self.functions["array_filter"] = FunctionInfo(
            name="array_filter",
            forall_vars=("T",),
            param_types=(
                AdtType("Array", (TypeVar("T"),)),
                FunctionType(
                    params=(TypeVar("T"),),
                    return_type=BOOL,
                    effect=PureEffectRow(),
                ),
            ),
            return_type=AdtType("Array", (TypeVar("T"),)),
            effect=PureEffectRow(),
        )
        self.functions["array_fold"] = FunctionInfo(
            name="array_fold",
            forall_vars=("T", "U"),
            param_types=(
                AdtType("Array", (TypeVar("T"),)),
                TypeVar("U"),
                FunctionType(
                    params=(TypeVar("U"), TypeVar("T")),
                    return_type=TypeVar("U"),
                    effect=PureEffectRow(),
                ),
            ),
            return_type=TypeVar("U"),
            effect=PureEffectRow(),
        )

        # Array utility built-ins (#466 phase 1).  Mirrors the
        # array_map/filter/fold pattern: iterative WASM over a
        # call_indirect callback, no prelude recursion.  Phase 1
        # covers the operations that do not require ability
        # dispatch on a polymorphic element type; array_sort,
        # array_contains, and array_index_of (all of which need
        # compare$T / eq$T dispatch from inside a WASM loop) are
        # tracked separately.
        self.functions["array_mapi"] = FunctionInfo(
            name="array_mapi",
            forall_vars=("A", "B"),
            param_types=(
                AdtType("Array", (TypeVar("A"),)),
                FunctionType(
                    params=(TypeVar("A"), NAT),
                    return_type=TypeVar("B"),
                    effect=PureEffectRow(),
                ),
            ),
            return_type=AdtType("Array", (TypeVar("B"),)),
            effect=PureEffectRow(),
        )
        self.functions["array_reverse"] = FunctionInfo(
            name="array_reverse",
            forall_vars=("T",),
            param_types=(AdtType("Array", (TypeVar("T"),)),),
            return_type=AdtType("Array", (TypeVar("T"),)),
            effect=PureEffectRow(),
        )
        self.functions["array_find"] = FunctionInfo(
            name="array_find",
            forall_vars=("T",),
            param_types=(
                AdtType("Array", (TypeVar("T"),)),
                FunctionType(
                    params=(TypeVar("T"),),
                    return_type=BOOL,
                    effect=PureEffectRow(),
                ),
            ),
            return_type=AdtType("Option", (TypeVar("T"),)),
            effect=PureEffectRow(),
        )
        self.functions["array_any"] = FunctionInfo(
            name="array_any",
            forall_vars=("T",),
            param_types=(
                AdtType("Array", (TypeVar("T"),)),
                FunctionType(
                    params=(TypeVar("T"),),
                    return_type=BOOL,
                    effect=PureEffectRow(),
                ),
            ),
            return_type=BOOL,
            effect=PureEffectRow(),
        )
        self.functions["array_all"] = FunctionInfo(
            name="array_all",
            forall_vars=("T",),
            param_types=(
                AdtType("Array", (TypeVar("T"),)),
                FunctionType(
                    params=(TypeVar("T"),),
                    return_type=BOOL,
                    effect=PureEffectRow(),
                ),
            ),
            return_type=BOOL,
            effect=PureEffectRow(),
        )
        self.functions["array_flatten"] = FunctionInfo(
            name="array_flatten",
            forall_vars=("T",),
            param_types=(
                AdtType("Array", (AdtType("Array", (TypeVar("T"),)),)),
            ),
            return_type=AdtType("Array", (TypeVar("T"),)),
            effect=PureEffectRow(),
        )
        self.functions["array_sort_by"] = FunctionInfo(
            name="array_sort_by",
            forall_vars=("T",),
            param_types=(
                AdtType("Array", (TypeVar("T"),)),
                FunctionType(
                    params=(TypeVar("T"), TypeVar("T")),
                    return_type=AdtType("Ordering", ()),
                    effect=PureEffectRow(),
                ),
            ),
            return_type=AdtType("Array", (TypeVar("T"),)),
            effect=PureEffectRow(),
        )

        # Map<K, V> operations (host-import builtins)
        # Require Eq<K> + Hash<K> ability constraints.
        from vera.ast import AbilityConstraint
        _map_kv_constraints = (
            AbilityConstraint(ability_name="Eq", type_var="K"),
            AbilityConstraint(ability_name="Hash", type_var="K"),
        )
        self.functions["map_new"] = FunctionInfo(
            name="map_new",
            forall_vars=("K", "V"),
            param_types=(),
            return_type=AdtType("Map", (TypeVar("K"), TypeVar("V"))),
            effect=PureEffectRow(),
            forall_constraints=_map_kv_constraints,
        )
        self.functions["map_insert"] = FunctionInfo(
            name="map_insert",
            forall_vars=("K", "V"),
            param_types=(
                AdtType("Map", (TypeVar("K"), TypeVar("V"))),
                TypeVar("K"),
                TypeVar("V"),
            ),
            return_type=AdtType("Map", (TypeVar("K"), TypeVar("V"))),
            effect=PureEffectRow(),
            forall_constraints=_map_kv_constraints,
        )
        self.functions["map_get"] = FunctionInfo(
            name="map_get",
            forall_vars=("K", "V"),
            param_types=(
                AdtType("Map", (TypeVar("K"), TypeVar("V"))),
                TypeVar("K"),
            ),
            return_type=AdtType("Option", (TypeVar("V"),)),
            effect=PureEffectRow(),
            forall_constraints=_map_kv_constraints,
        )
        self.functions["map_contains"] = FunctionInfo(
            name="map_contains",
            forall_vars=("K", "V"),
            param_types=(
                AdtType("Map", (TypeVar("K"), TypeVar("V"))),
                TypeVar("K"),
            ),
            return_type=BOOL,
            effect=PureEffectRow(),
            forall_constraints=_map_kv_constraints,
        )
        self.functions["map_remove"] = FunctionInfo(
            name="map_remove",
            forall_vars=("K", "V"),
            param_types=(
                AdtType("Map", (TypeVar("K"), TypeVar("V"))),
                TypeVar("K"),
            ),
            return_type=AdtType("Map", (TypeVar("K"), TypeVar("V"))),
            effect=PureEffectRow(),
            forall_constraints=_map_kv_constraints,
        )
        self.functions["map_size"] = FunctionInfo(
            name="map_size",
            forall_vars=("K", "V"),
            param_types=(
                AdtType("Map", (TypeVar("K"), TypeVar("V"))),
            ),
            return_type=INT,
            effect=PureEffectRow(),
            forall_constraints=_map_kv_constraints,
        )
        self.functions["map_keys"] = FunctionInfo(
            name="map_keys",
            forall_vars=("K", "V"),
            param_types=(
                AdtType("Map", (TypeVar("K"), TypeVar("V"))),
            ),
            return_type=AdtType("Array", (TypeVar("K"),)),
            effect=PureEffectRow(),
            forall_constraints=_map_kv_constraints,
        )
        self.functions["map_values"] = FunctionInfo(
            name="map_values",
            forall_vars=("K", "V"),
            param_types=(
                AdtType("Map", (TypeVar("K"), TypeVar("V"))),
            ),
            return_type=AdtType("Array", (TypeVar("V"),)),
            effect=PureEffectRow(),
            forall_constraints=_map_kv_constraints,
        )

        # Set<T> operations (host-import builtins)
        # Require Eq<T> + Hash<T> ability constraints.
        _set_constraints = (
            AbilityConstraint(ability_name="Eq", type_var="T"),
            AbilityConstraint(ability_name="Hash", type_var="T"),
        )
        self.functions["set_new"] = FunctionInfo(
            name="set_new",
            forall_vars=("T",),
            param_types=(),
            return_type=AdtType("Set", (TypeVar("T"),)),
            effect=PureEffectRow(),
            forall_constraints=_set_constraints,
        )
        self.functions["set_add"] = FunctionInfo(
            name="set_add",
            forall_vars=("T",),
            param_types=(
                AdtType("Set", (TypeVar("T"),)),
                TypeVar("T"),
            ),
            return_type=AdtType("Set", (TypeVar("T"),)),
            effect=PureEffectRow(),
            forall_constraints=_set_constraints,
        )
        self.functions["set_contains"] = FunctionInfo(
            name="set_contains",
            forall_vars=("T",),
            param_types=(
                AdtType("Set", (TypeVar("T"),)),
                TypeVar("T"),
            ),
            return_type=BOOL,
            effect=PureEffectRow(),
            forall_constraints=_set_constraints,
        )
        self.functions["set_remove"] = FunctionInfo(
            name="set_remove",
            forall_vars=("T",),
            param_types=(
                AdtType("Set", (TypeVar("T"),)),
                TypeVar("T"),
            ),
            return_type=AdtType("Set", (TypeVar("T"),)),
            effect=PureEffectRow(),
            forall_constraints=_set_constraints,
        )
        self.functions["set_size"] = FunctionInfo(
            name="set_size",
            forall_vars=("T",),
            param_types=(
                AdtType("Set", (TypeVar("T"),)),
            ),
            return_type=INT,
            effect=PureEffectRow(),
            forall_constraints=_set_constraints,
        )
        self.functions["set_to_array"] = FunctionInfo(
            name="set_to_array",
            forall_vars=("T",),
            param_types=(
                AdtType("Set", (TypeVar("T"),)),
            ),
            return_type=AdtType("Array", (TypeVar("T"),)),
            effect=PureEffectRow(),
            forall_constraints=_set_constraints,
        )

        # ── Decimal built-in functions ──────────────────────────────
        DECIMAL = AdtType("Decimal", ())
        OPTION_DECIMAL = AdtType("Option", (DECIMAL,))
        ORDERING = AdtType("Ordering", ())

        # Construction / conversion
        self.functions["decimal_from_int"] = FunctionInfo(
            name="decimal_from_int",
            forall_vars=None,
            param_types=(INT,),
            return_type=DECIMAL,
            effect=PureEffectRow(),
        )
        self.functions["decimal_from_float"] = FunctionInfo(
            name="decimal_from_float",
            forall_vars=None,
            param_types=(FLOAT64,),
            return_type=DECIMAL,
            effect=PureEffectRow(),
        )
        self.functions["decimal_from_string"] = FunctionInfo(
            name="decimal_from_string",
            forall_vars=None,
            param_types=(STRING,),
            return_type=OPTION_DECIMAL,
            effect=PureEffectRow(),
        )
        self.functions["decimal_to_string"] = FunctionInfo(
            name="decimal_to_string",
            forall_vars=None,
            param_types=(DECIMAL,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["decimal_to_float"] = FunctionInfo(
            name="decimal_to_float",
            forall_vars=None,
            param_types=(DECIMAL,),
            return_type=FLOAT64,
            effect=PureEffectRow(),
        )

        # Arithmetic
        self.functions["decimal_add"] = FunctionInfo(
            name="decimal_add",
            forall_vars=None,
            param_types=(DECIMAL, DECIMAL),
            return_type=DECIMAL,
            effect=PureEffectRow(),
        )
        self.functions["decimal_sub"] = FunctionInfo(
            name="decimal_sub",
            forall_vars=None,
            param_types=(DECIMAL, DECIMAL),
            return_type=DECIMAL,
            effect=PureEffectRow(),
        )
        self.functions["decimal_mul"] = FunctionInfo(
            name="decimal_mul",
            forall_vars=None,
            param_types=(DECIMAL, DECIMAL),
            return_type=DECIMAL,
            effect=PureEffectRow(),
        )
        self.functions["decimal_div"] = FunctionInfo(
            name="decimal_div",
            forall_vars=None,
            param_types=(DECIMAL, DECIMAL),
            return_type=OPTION_DECIMAL,
            effect=PureEffectRow(),
        )
        self.functions["decimal_neg"] = FunctionInfo(
            name="decimal_neg",
            forall_vars=None,
            param_types=(DECIMAL,),
            return_type=DECIMAL,
            effect=PureEffectRow(),
        )

        # Comparison
        self.functions["decimal_compare"] = FunctionInfo(
            name="decimal_compare",
            forall_vars=None,
            param_types=(DECIMAL, DECIMAL),
            return_type=ORDERING,
            effect=PureEffectRow(),
        )
        self.functions["decimal_eq"] = FunctionInfo(
            name="decimal_eq",
            forall_vars=None,
            param_types=(DECIMAL, DECIMAL),
            return_type=BOOL,
            effect=PureEffectRow(),
        )

        # Rounding
        self.functions["decimal_round"] = FunctionInfo(
            name="decimal_round",
            forall_vars=None,
            param_types=(DECIMAL, INT),
            return_type=DECIMAL,
            effect=PureEffectRow(),
        )
        self.functions["decimal_abs"] = FunctionInfo(
            name="decimal_abs",
            forall_vars=None,
            param_types=(DECIMAL,),
            return_type=DECIMAL,
            effect=PureEffectRow(),
        )

        # Option / Result combinators
        # Implementations are injected as Vera source AST during codegen
        # (see vera.prelude); these signatures enable type checking.
        self.functions["option_unwrap_or"] = FunctionInfo(
            name="option_unwrap_or",
            forall_vars=("T",),
            param_types=(
                AdtType("Option", (TypeVar("T"),)),
                TypeVar("T"),
            ),
            return_type=TypeVar("T"),
            effect=PureEffectRow(),
        )
        self.functions["option_map"] = FunctionInfo(
            name="option_map",
            forall_vars=("A", "B"),
            param_types=(
                AdtType("Option", (TypeVar("A"),)),
                FunctionType(
                    params=(TypeVar("A"),),
                    return_type=TypeVar("B"),
                    effect=PureEffectRow(),
                ),
            ),
            return_type=AdtType("Option", (TypeVar("B"),)),
            effect=PureEffectRow(),
        )
        self.functions["option_and_then"] = FunctionInfo(
            name="option_and_then",
            forall_vars=("A", "B"),
            param_types=(
                AdtType("Option", (TypeVar("A"),)),
                FunctionType(
                    params=(TypeVar("A"),),
                    return_type=AdtType("Option", (TypeVar("B"),)),
                    effect=PureEffectRow(),
                ),
            ),
            return_type=AdtType("Option", (TypeVar("B"),)),
            effect=PureEffectRow(),
        )
        self.functions["result_unwrap_or"] = FunctionInfo(
            name="result_unwrap_or",
            forall_vars=("T", "E"),
            param_types=(
                AdtType("Result", (TypeVar("T"), TypeVar("E"))),
                TypeVar("T"),
            ),
            return_type=TypeVar("T"),
            effect=PureEffectRow(),
        )
        self.functions["result_map"] = FunctionInfo(
            name="result_map",
            forall_vars=("A", "B", "E"),
            param_types=(
                AdtType("Result", (TypeVar("A"), TypeVar("E"))),
                FunctionType(
                    params=(TypeVar("A"),),
                    return_type=TypeVar("B"),
                    effect=PureEffectRow(),
                ),
            ),
            return_type=AdtType("Result", (TypeVar("B"), TypeVar("E"))),
            effect=PureEffectRow(),
        )

        # Built-in string operations
        self.functions["string_length"] = FunctionInfo(
            name="string_length",
            forall_vars=None,
            param_types=(STRING,),
            return_type=NAT,
            effect=PureEffectRow(),
        )
        self.functions["string_concat"] = FunctionInfo(
            name="string_concat",
            forall_vars=None,
            param_types=(STRING, STRING),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["string_slice"] = FunctionInfo(
            name="string_slice",
            forall_vars=None,
            param_types=(STRING, NAT, NAT),
            return_type=STRING,
            effect=PureEffectRow(),
        )

        # String/number conversion and inspection
        self.functions["string_char_code"] = FunctionInfo(
            name="string_char_code",
            forall_vars=None,
            param_types=(STRING, INT),
            return_type=NAT,
            effect=PureEffectRow(),
        )
        self.functions["string_from_char_code"] = FunctionInfo(
            name="string_from_char_code",
            forall_vars=None,
            param_types=(NAT,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["string_repeat"] = FunctionInfo(
            name="string_repeat",
            forall_vars=None,
            param_types=(STRING, NAT),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["parse_nat"] = FunctionInfo(
            name="parse_nat",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Result", (NAT, STRING)),
            effect=PureEffectRow(),
        )
        self.functions["parse_int"] = FunctionInfo(
            name="parse_int",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Result", (INT, STRING)),
            effect=PureEffectRow(),
        )
        self.functions["parse_float64"] = FunctionInfo(
            name="parse_float64",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Result", (FLOAT64, STRING)),
            effect=PureEffectRow(),
        )
        self.functions["parse_bool"] = FunctionInfo(
            name="parse_bool",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Result", (BOOL, STRING)),
            effect=PureEffectRow(),
        )
        self.functions["base64_encode"] = FunctionInfo(
            name="base64_encode",
            forall_vars=None,
            param_types=(STRING,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["base64_decode"] = FunctionInfo(
            name="base64_decode",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Result", (STRING, STRING)),
            effect=PureEffectRow(),
        )
        self.functions["url_encode"] = FunctionInfo(
            name="url_encode",
            forall_vars=None,
            param_types=(STRING,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["url_decode"] = FunctionInfo(
            name="url_decode",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Result", (STRING, STRING)),
            effect=PureEffectRow(),
        )
        self.functions["url_parse"] = FunctionInfo(
            name="url_parse",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType(
                "Result", (AdtType("UrlParts", ()), STRING)
            ),
            effect=PureEffectRow(),
        )
        self.functions["url_join"] = FunctionInfo(
            name="url_join",
            forall_vars=None,
            param_types=(AdtType("UrlParts", ()),),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        # Markdown builtins — pure host-import functions (§9.7.3)
        _MD_BLOCK_TYPE = AdtType("MdBlock", ())
        self.functions["md_parse"] = FunctionInfo(
            name="md_parse",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType(
                "Result", (_MD_BLOCK_TYPE, STRING),
            ),
            effect=PureEffectRow(),
        )
        self.functions["md_render"] = FunctionInfo(
            name="md_render",
            forall_vars=None,
            param_types=(_MD_BLOCK_TYPE,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["md_has_heading"] = FunctionInfo(
            name="md_has_heading",
            forall_vars=None,
            param_types=(_MD_BLOCK_TYPE, NAT),
            return_type=BOOL,
            effect=PureEffectRow(),
        )
        self.functions["md_has_code_block"] = FunctionInfo(
            name="md_has_code_block",
            forall_vars=None,
            param_types=(_MD_BLOCK_TYPE, STRING),
            return_type=BOOL,
            effect=PureEffectRow(),
        )
        self.functions["md_extract_code_blocks"] = FunctionInfo(
            name="md_extract_code_blocks",
            forall_vars=None,
            param_types=(_MD_BLOCK_TYPE, STRING),
            return_type=AdtType("Array", (STRING,)),
            effect=PureEffectRow(),
        )
        # Json builtins (§9.7.1) — host-imported parse/stringify
        _JSON_T = AdtType("Json", ())
        self.functions["json_parse"] = FunctionInfo(
            name="json_parse",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Result", (_JSON_T, STRING)),
            effect=PureEffectRow(),
        )
        self.functions["json_stringify"] = FunctionInfo(
            name="json_stringify",
            forall_vars=None,
            param_types=(_JSON_T,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        # Json utility functions — pure Vera (prelude-injected bodies)
        self.functions["json_get"] = FunctionInfo(
            name="json_get",
            forall_vars=None,
            param_types=(_JSON_T, STRING),
            return_type=AdtType("Option", (_JSON_T,)),
            effect=PureEffectRow(),
        )
        self.functions["json_array_get"] = FunctionInfo(
            name="json_array_get",
            forall_vars=None,
            param_types=(_JSON_T, INT),
            return_type=AdtType("Option", (_JSON_T,)),
            effect=PureEffectRow(),
        )
        self.functions["json_array_length"] = FunctionInfo(
            name="json_array_length",
            forall_vars=None,
            param_types=(_JSON_T,),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["json_keys"] = FunctionInfo(
            name="json_keys",
            forall_vars=None,
            param_types=(_JSON_T,),
            return_type=AdtType("Array", (STRING,)),
            effect=PureEffectRow(),
        )
        self.functions["json_has_field"] = FunctionInfo(
            name="json_has_field",
            forall_vars=None,
            param_types=(_JSON_T, STRING),
            return_type=BOOL,
            effect=PureEffectRow(),
        )
        self.functions["json_type"] = FunctionInfo(
            name="json_type",
            forall_vars=None,
            param_types=(_JSON_T,),
            return_type=STRING,
            effect=PureEffectRow(),
        )

        # #366 — typed accessors (Json -> Option<T>) and compound field
        # accessors (Json, String -> Option<T>).  All pure-Vera prelude
        # functions; bodies live in vera/prelude.py _JSON_COMBINATORS.
        _ARR_JSON = AdtType("Array", (_JSON_T,))
        _MAP_STR_JSON_T = AdtType("Map", (STRING, _JSON_T))
        # Layer 1: type coercion accessors
        for _name, _ret in [
            ("json_as_string", STRING),
            ("json_as_number", FLOAT64),
            ("json_as_bool", BOOL),
            ("json_as_int", INT),
            ("json_as_array", _ARR_JSON),
            ("json_as_object", _MAP_STR_JSON_T),
        ]:
            self.functions[_name] = FunctionInfo(
                name=_name,
                forall_vars=None,
                param_types=(_JSON_T,),
                return_type=AdtType("Option", (_ret,)),
                effect=PureEffectRow(),
            )
        # Layer 2: compound field accessors (skip the array variant —
        # see json_get_array below; the FLOAT64 list mirrors json_as_*)
        for _name, _ret in [
            ("json_get_string", STRING),
            ("json_get_number", FLOAT64),
            ("json_get_bool", BOOL),
            ("json_get_int", INT),
            ("json_get_array", _ARR_JSON),
        ]:
            self.functions[_name] = FunctionInfo(
                name=_name,
                forall_vars=None,
                param_types=(_JSON_T, STRING),
                return_type=AdtType("Option", (_ret,)),
                effect=PureEffectRow(),
            )

        # Html builtins (§9.7.4) — host-imported parse/to_string/query/text
        _HTML_T = AdtType("HtmlNode", ())
        _ARR_HTML_T = AdtType("Array", (_HTML_T,))
        self.functions["html_parse"] = FunctionInfo(
            name="html_parse",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Result", (_HTML_T, STRING)),
            effect=PureEffectRow(),
        )
        self.functions["html_to_string"] = FunctionInfo(
            name="html_to_string",
            forall_vars=None,
            param_types=(_HTML_T,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["html_query"] = FunctionInfo(
            name="html_query",
            forall_vars=None,
            param_types=(_HTML_T, STRING),
            return_type=_ARR_HTML_T,
            effect=PureEffectRow(),
        )
        self.functions["html_text"] = FunctionInfo(
            name="html_text",
            forall_vars=None,
            param_types=(_HTML_T,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        # html_attr is a pure Vera function (prelude-injected body)
        self.functions["html_attr"] = FunctionInfo(
            name="html_attr",
            forall_vars=None,
            param_types=(_HTML_T, STRING),
            return_type=AdtType("Option", (STRING,)),
            effect=PureEffectRow(),
        )

        # Regex builtins (§9.6.15) — host-imported, pure
        self.functions["regex_match"] = FunctionInfo(
            name="regex_match",
            forall_vars=None,
            param_types=(STRING, STRING),
            return_type=AdtType("Result", (BOOL, STRING)),
            effect=PureEffectRow(),
        )
        self.functions["regex_find"] = FunctionInfo(
            name="regex_find",
            forall_vars=None,
            param_types=(STRING, STRING),
            return_type=AdtType(
                "Result", (AdtType("Option", (STRING,)), STRING),
            ),
            effect=PureEffectRow(),
        )
        self.functions["regex_find_all"] = FunctionInfo(
            name="regex_find_all",
            forall_vars=None,
            param_types=(STRING, STRING),
            return_type=AdtType(
                "Result", (AdtType("Array", (STRING,)), STRING),
            ),
            effect=PureEffectRow(),
        )
        self.functions["regex_replace"] = FunctionInfo(
            name="regex_replace",
            forall_vars=None,
            param_types=(STRING, STRING, STRING),
            return_type=AdtType("Result", (STRING, STRING)),
            effect=PureEffectRow(),
        )
        # Async builtins — require effects(<Async>)
        _ASYNC_EFFECT = ConcreteEffectRow(
            frozenset({EffectInstance("Async", ())}), row_var=None,
        )
        self.functions["async"] = FunctionInfo(
            name="async",
            forall_vars=("T",),
            param_types=(TypeVar("T"),),
            return_type=AdtType("Future", (TypeVar("T"),)),
            effect=_ASYNC_EFFECT,
        )
        self.functions["await"] = FunctionInfo(
            name="await",
            forall_vars=("T",),
            param_types=(AdtType("Future", (TypeVar("T"),)),),
            return_type=TypeVar("T"),
            effect=_ASYNC_EFFECT,
        )
        self.functions["to_string"] = FunctionInfo(
            name="to_string",
            forall_vars=None,
            param_types=(INT,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["int_to_string"] = FunctionInfo(
            name="int_to_string",
            forall_vars=None,
            param_types=(INT,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["bool_to_string"] = FunctionInfo(
            name="bool_to_string",
            forall_vars=None,
            param_types=(BOOL,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["nat_to_string"] = FunctionInfo(
            name="nat_to_string",
            forall_vars=None,
            param_types=(NAT,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["byte_to_string"] = FunctionInfo(
            name="byte_to_string",
            forall_vars=None,
            param_types=(BYTE,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["float_to_string"] = FunctionInfo(
            name="float_to_string",
            forall_vars=None,
            param_types=(FLOAT64,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["string_strip"] = FunctionInfo(
            name="string_strip",
            forall_vars=None,
            param_types=(STRING,),
            return_type=STRING,
            effect=PureEffectRow(),
        )

        # String search and transformation builtins
        self.functions["string_contains"] = FunctionInfo(
            name="string_contains",
            forall_vars=None,
            param_types=(STRING, STRING),
            return_type=BOOL,
            effect=PureEffectRow(),
        )
        self.functions["string_starts_with"] = FunctionInfo(
            name="string_starts_with",
            forall_vars=None,
            param_types=(STRING, STRING),
            return_type=BOOL,
            effect=PureEffectRow(),
        )
        self.functions["string_ends_with"] = FunctionInfo(
            name="string_ends_with",
            forall_vars=None,
            param_types=(STRING, STRING),
            return_type=BOOL,
            effect=PureEffectRow(),
        )
        self.functions["string_index_of"] = FunctionInfo(
            name="string_index_of",
            forall_vars=None,
            param_types=(STRING, STRING),
            return_type=AdtType("Option", (NAT,)),
            effect=PureEffectRow(),
        )
        self.functions["string_upper"] = FunctionInfo(
            name="string_upper",
            forall_vars=None,
            param_types=(STRING,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["string_lower"] = FunctionInfo(
            name="string_lower",
            forall_vars=None,
            param_types=(STRING,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["string_replace"] = FunctionInfo(
            name="string_replace",
            forall_vars=None,
            param_types=(STRING, STRING, STRING),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["string_split"] = FunctionInfo(
            name="string_split",
            forall_vars=None,
            param_types=(STRING, STRING),
            return_type=AdtType("Array", (STRING,)),
            effect=PureEffectRow(),
        )
        self.functions["string_join"] = FunctionInfo(
            name="string_join",
            forall_vars=None,
            param_types=(AdtType("Array", (STRING,)), STRING),
            return_type=STRING,
            effect=PureEffectRow(),
        )

        # String utility built-ins (#470).  Six string transformations
        # plus the bridge primitive ``string_chars`` and the two
        # structural splits ``string_lines`` / ``string_words`` that
        # ``string_split`` cannot express because it only takes a
        # single delimiter character.
        self.functions["string_chars"] = FunctionInfo(
            name="string_chars",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Array", (STRING,)),
            effect=PureEffectRow(),
        )
        self.functions["string_lines"] = FunctionInfo(
            name="string_lines",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Array", (STRING,)),
            effect=PureEffectRow(),
        )
        self.functions["string_words"] = FunctionInfo(
            name="string_words",
            forall_vars=None,
            param_types=(STRING,),
            return_type=AdtType("Array", (STRING,)),
            effect=PureEffectRow(),
        )
        self.functions["string_pad_start"] = FunctionInfo(
            name="string_pad_start",
            forall_vars=None,
            param_types=(STRING, NAT, STRING),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["string_pad_end"] = FunctionInfo(
            name="string_pad_end",
            forall_vars=None,
            param_types=(STRING, NAT, STRING),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["string_reverse"] = FunctionInfo(
            name="string_reverse",
            forall_vars=None,
            param_types=(STRING,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["string_trim_start"] = FunctionInfo(
            name="string_trim_start",
            forall_vars=None,
            param_types=(STRING,),
            return_type=STRING,
            effect=PureEffectRow(),
        )
        self.functions["string_trim_end"] = FunctionInfo(
            name="string_trim_end",
            forall_vars=None,
            param_types=(STRING,),
            return_type=STRING,
            effect=PureEffectRow(),
        )

        # Character classification + single-character case conversion
        # (#471).  All operate on the first character of the input
        # string (Vera has no Char type — characters are
        # single-character strings, same as Elm / PureScript).
        # Empty-string convention: classifiers return false; case
        # converters return the empty string.  Classifiers are
        # ASCII-only by design (matches the issue's spec).
        for _classifier in (
            "is_digit", "is_alpha", "is_alphanumeric",
            "is_whitespace", "is_upper", "is_lower",
        ):
            self.functions[_classifier] = FunctionInfo(
                name=_classifier,
                forall_vars=None,
                param_types=(STRING,),
                return_type=BOOL,
                effect=PureEffectRow(),
            )
        for _case_fn in ("char_to_upper", "char_to_lower"):
            self.functions[_case_fn] = FunctionInfo(
                name=_case_fn,
                forall_vars=None,
                param_types=(STRING,),
                return_type=STRING,
                effect=PureEffectRow(),
            )

        # Numeric math builtins
        self.functions["abs"] = FunctionInfo(
            name="abs",
            forall_vars=None,
            param_types=(INT,),
            return_type=NAT,
            effect=PureEffectRow(),
        )
        self.functions["min"] = FunctionInfo(
            name="min",
            forall_vars=None,
            param_types=(INT, INT),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["max"] = FunctionInfo(
            name="max",
            forall_vars=None,
            param_types=(INT, INT),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["floor"] = FunctionInfo(
            name="floor",
            forall_vars=None,
            param_types=(FLOAT64,),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["ceil"] = FunctionInfo(
            name="ceil",
            forall_vars=None,
            param_types=(FLOAT64,),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["round"] = FunctionInfo(
            name="round",
            forall_vars=None,
            param_types=(FLOAT64,),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["sqrt"] = FunctionInfo(
            name="sqrt",
            forall_vars=None,
            param_types=(FLOAT64,),
            return_type=FLOAT64,
            effect=PureEffectRow(),
        )
        self.functions["pow"] = FunctionInfo(
            name="pow",
            forall_vars=None,
            param_types=(FLOAT64, INT),
            return_type=FLOAT64,
            effect=PureEffectRow(),
        )

        # Logarithmic functions (#467).  All three go through host
        # imports (`vera.log` / `vera.log2` / `vera.log10`) because
        # WASM has no native logarithm instructions.  Return `NaN`
        # for inputs <= 0 — JavaScript's `Math.log` returns NaN
        # natively, and the Python host wrapper translates
        # `math.log`'s `ValueError` ("math domain error") to NaN
        # (see `vera/codegen/api.py::_math_unary_host`), so both
        # runtimes expose the same IEEE 754 behaviour to Vera code.
        for _log_name in ("log", "log2", "log10"):
            self.functions[_log_name] = FunctionInfo(
                name=_log_name,
                forall_vars=None,
                param_types=(FLOAT64,),
                return_type=FLOAT64,
                effect=PureEffectRow(),
            )

        # Trigonometric functions (#467).  Unary: sin/cos/tan plus
        # their inverses asin/acos/atan (all Float64 → Float64).
        # atan2 is binary (y, x) → Float64 for quadrant-correct
        # angle-from-coordinates.  All go through host imports.
        for _trig_name in ("sin", "cos", "tan", "asin", "acos", "atan"):
            self.functions[_trig_name] = FunctionInfo(
                name=_trig_name,
                forall_vars=None,
                param_types=(FLOAT64,),
                return_type=FLOAT64,
                effect=PureEffectRow(),
            )
        self.functions["atan2"] = FunctionInfo(
            name="atan2",
            forall_vars=None,
            param_types=(FLOAT64, FLOAT64),
            return_type=FLOAT64,
            effect=PureEffectRow(),
        )

        # Mathematical constants (#467).  Zero-arg FunctionInfos —
        # user-facing syntax is `pi()` / `e()`.  Inlined in WAT as
        # `f64.const 3.141592653589793` etc., no host call needed.
        self.functions["pi"] = FunctionInfo(
            name="pi",
            forall_vars=None,
            param_types=(),
            return_type=FLOAT64,
            effect=PureEffectRow(),
        )
        self.functions["e"] = FunctionInfo(
            name="e",
            forall_vars=None,
            param_types=(),
            return_type=FLOAT64,
            effect=PureEffectRow(),
        )

        # Numeric utilities (#467).  sign/clamp/float_clamp are
        # simple enough to inline in WAT rather than route through
        # the host.  sign(x) returns -1/0/1.  Both clamp variants
        # evaluate `min(max(v, lo), hi)` — so when `lo <= hi` the
        # result is pinned to `[lo, hi]`, but when `lo > hi` the
        # outer `min` dominates and the result equals `hi`.  This
        # fallthrough is intentional; tests/test_codegen.py asserts
        # it for both `clamp` (Int) and `float_clamp` (Float64).
        self.functions["sign"] = FunctionInfo(
            name="sign",
            forall_vars=None,
            param_types=(INT,),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["clamp"] = FunctionInfo(
            name="clamp",
            forall_vars=None,
            # (value, min, max) → value clamped to [min, max]
            param_types=(INT, INT, INT),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["float_clamp"] = FunctionInfo(
            name="float_clamp",
            forall_vars=None,
            param_types=(FLOAT64, FLOAT64, FLOAT64),
            return_type=FLOAT64,
            effect=PureEffectRow(),
        )

        # Numeric type conversions
        self.functions["int_to_float"] = FunctionInfo(
            name="int_to_float",
            forall_vars=None,
            param_types=(INT,),
            return_type=FLOAT64,
            effect=PureEffectRow(),
        )
        self.functions["float_to_int"] = FunctionInfo(
            name="float_to_int",
            forall_vars=None,
            param_types=(FLOAT64,),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["nat_to_int"] = FunctionInfo(
            name="nat_to_int",
            forall_vars=None,
            param_types=(NAT,),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["int_to_nat"] = FunctionInfo(
            name="int_to_nat",
            forall_vars=None,
            param_types=(INT,),
            return_type=AdtType("Option", (NAT,)),
            effect=PureEffectRow(),
        )
        self.functions["byte_to_int"] = FunctionInfo(
            name="byte_to_int",
            forall_vars=None,
            param_types=(BYTE,),
            return_type=INT,
            effect=PureEffectRow(),
        )
        self.functions["int_to_byte"] = FunctionInfo(
            name="int_to_byte",
            forall_vars=None,
            param_types=(INT,),
            return_type=AdtType("Option", (BYTE,)),
            effect=PureEffectRow(),
        )

        # Float64 special value operations
        self.functions["float_is_nan"] = FunctionInfo(
            name="float_is_nan",
            forall_vars=None,
            param_types=(FLOAT64,),
            return_type=BOOL,
            effect=PureEffectRow(),
        )
        self.functions["float_is_infinite"] = FunctionInfo(
            name="float_is_infinite",
            forall_vars=None,
            param_types=(FLOAT64,),
            return_type=BOOL,
            effect=PureEffectRow(),
        )
        self.functions["nan"] = FunctionInfo(
            name="nan",
            forall_vars=None,
            param_types=(),
            return_type=FLOAT64,
            effect=PureEffectRow(),
        )
        self.functions["infinity"] = FunctionInfo(
            name="infinity",
            forall_vars=None,
            param_types=(),
            return_type=FLOAT64,
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

    def lookup_ability_op(self, op_name: str) -> OpInfo | None:
        """Look up an ability operation by name.

        Searches all registered abilities.  Constraint scoping is
        enforced by the caller (checker/calls.py), not here.
        """
        for ab in self.abilities.values():
            if op_name in ab.operations:
                return ab.operations[op_name]
        return None

    def is_type_name(self, name: str) -> bool:
        """Check if a name refers to a known type (primitive, ADT, or alias)."""
        return (name in PRIMITIVES
                or name in self.data_types
                or name in self.type_aliases)
