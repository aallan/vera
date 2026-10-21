"""The built-in registry: one record per built-in, read by every phase (#735).

A built-in function is one :class:`BuiltinSpec` in :data:`BUILTINS`:

- its **signature**, the checker's view, which ``TypeEnv`` registers as the
  function's ``FunctionInfo`` (``vera/environment.py``) and ``vera builtins
  --json`` publishes (``vera/introspect.py``);
- its **since**, the version that first registered it;
- its **lowering**, how code generation lowers a call to it: ``Inline``, by an
  emitter of ``WasmContext`` that writes the computation in place; ``Host``,
  by an emitter that calls one of the host imports in :data:`HOST_IMPORTS`;
  or ``Prelude``, as the Vera body ``vera/prelude.py`` injects, compiled like
  any declaration;
- its **domain**, for a built-in whose translation traps outside a range the
  verifier can state (``vera/builtin_domains.py`` parses it).

An effect operation implemented by the host is one operation in its effect's
``EffectInfo`` (``vera/environment.py``, which ``vera effects --json``
publishes) and one :class:`HostImport` row here.  The row is what the module
declares and what a host binds.

:data:`HOST_IMPORTS` lists every ``(import "vera" ...)`` declaration code
generation can emit, in the order a module declares them: the families in
:data:`HOST_FAMILIES`' order, and the rows of a family in the order they are
listed here.  That order is load-bearing.  The io, md, regex and decimal
rows are listed by name, while the json, html, http, async, db, random and
math rows keep the order the modules have always declared them in, which is
not sorted.  A per-instance row (a ``State`` cell by its type) is one row,
declared once for each instance a module uses.

What a call's emitter is handed is its record's :class:`Binding`, the
argument convention that emitter takes.

A built-in's trap kind is not restated here: ``vera.trap_registry``'s
``TRAP_EMITTERS`` is keyed by emitter, so the rows for a built-in are the ones
naming its record's emitter.

``tests/test_builtin_registry.py`` holds each record to the phases that read
it: the checker's arity, the emitter and its convention, the imports a call
declares, the hosts that bind them.
"""

from __future__ import annotations

import enum
from collections.abc import Collection, Iterator, Mapping
from dataclasses import dataclass

from vera.trap_registry import (
    CONTRACT_SIGNAL,
    TRAP_EMITTERS,
    TRAP_IMPORT_WAT,
    TRAP_SIGNAL,
    TrapEmitter,
)
from vera.types import (
    BOOL,
    BYTE,
    FLOAT64,
    INT,
    NAT,
    STRING,
    AdtType,
    ConcreteEffectRow,
    EffectInstance,
    EffectRowType,
    FunctionType,
    PureEffectRow,
    Type,
    TypeVar,
)

# =====================================================================
# Records
# =====================================================================


class Binding(enum.Enum):
    """The arguments the dispatch hands a call's emitter, in its order."""

    ARGS = "args"
    """``emitter(*call.args, env)``."""
    ARGS_AT = "args_at"
    """``emitter(*call.args, env, at=call)``: the call is the check's site."""
    ARGS_SITE = "args_site"
    """``emitter(*call.args, env, at=<the call's rendering site>)``."""
    ARGS_CALL = "args_call"
    """``emitter(*call.args, env, call)``."""
    CALL = "call"
    """``emitter(call, env)``."""
    CALL_EXTRA = "call_extra"
    """``emitter(call, env, *extra)``."""
    NONE = "none"
    """``emitter()``."""
    NAMED = "named"
    """``emitter(name, *call.args, env)``: one emitter for several names."""


@dataclass(frozen=True)
class Signature:
    """A built-in's type, as the checker registers it."""

    params: tuple[Type, ...]
    ret: Type
    #: The type variables, unrenamed: ``TypeEnv`` namespaces them (#970).
    forall: tuple[str, ...] | None = None
    effect: EffectRowType = PureEffectRow()
    #: ``(ability, type variable)`` pairs, e.g. ``("Eq", "K")``.
    constraints: tuple[tuple[str, str], ...] = ()


@dataclass(frozen=True)
class Inline:
    """Lowered in place by an emitter of ``WasmContext``."""

    emitter: str
    binding: Binding = Binding.ARGS
    extra: tuple[str, ...] = ()


@dataclass(frozen=True)
class Host:
    """Lowered by an emitter to a call of a host import of *family*."""

    emitter: str
    family: str
    binding: Binding = Binding.ARGS
    extra: tuple[str, ...] = ()


@dataclass(frozen=True)
class Prelude:
    """Lowered as the Vera body ``vera/prelude.py`` injects.

    A program may declare a function of the same name, which replaces the
    prelude's (``prelude.overridable_builtin_names``); E151 refuses every
    other built-in's name.
    """


Lowering = Inline | Host | Prelude


@dataclass(frozen=True)
class Domain:
    """A trapping built-in's precondition, as a Vera ``requires`` (#1480)."""

    #: The body of the ``requires``, over the built-in's parameters.
    requires: str
    #: What the translation does outside the domain.
    trap: str


@dataclass(frozen=True)
class BuiltinSpec:
    """One built-in function."""

    name: str
    signature: Signature
    since: str
    lowering: Lowering
    domain: Domain | None = None

    @property
    def arity(self) -> int:
        return len(self.signature.params)


@dataclass(frozen=True)
class AbilityIntrinsic:
    """An ability operation code generation lowers by name, as a built-in.

    Its signature is the ability's (``TypeEnv.abilities``); it is not a
    function, so ``vera builtins`` does not list it and E151 does not refuse
    a declaration of its name.
    """

    name: str
    ability: str
    arity: int
    lowering: Inline


@dataclass(frozen=True)
class Intrinsic:
    """A name the dispatch lowers in place of a call: what it reads."""

    name: str
    arity: int
    lowering: Inline | Host


# =====================================================================
# Built-in functions
# =====================================================================

T, U, A, B, E, K, V = (TypeVar(n) for n in ("T", "U", "A", "B", "E", "K", "V"))

_JSON = AdtType("Json", ())
_HTML = AdtType("HtmlNode", ())
_MD = AdtType("MdBlock", ())
_DECIMAL = AdtType("Decimal", ())
_ORDERING = AdtType("Ordering", ())
_URL_PARTS = AdtType("UrlParts", ())
_ASYNC = ConcreteEffectRow(frozenset({EffectInstance("Async", ())}), row_var=None)


def _array(t: Type) -> AdtType:
    return AdtType("Array", (t,))


def _option(t: Type) -> AdtType:
    return AdtType("Option", (t,))


def _result(t: Type, e: Type) -> AdtType:
    return AdtType("Result", (t, e))


def _map(k: Type, v: Type) -> AdtType:
    return AdtType("Map", (k, v))


def _set(t: Type) -> AdtType:
    return AdtType("Set", (t,))


def _future(t: Type) -> AdtType:
    return AdtType("Future", (t,))


def _pure_fn(params: tuple[Type, ...], ret: Type) -> FunctionType:
    return FunctionType(params=params, return_type=ret, effect=PureEffectRow())


def _fn(
    name: str, params: tuple[Type, ...], ret: Type, *,
    since: str, lowering: Lowering,
    forall: tuple[str, ...] | None = None,
    effect: EffectRowType = PureEffectRow(),
    constraints: tuple[tuple[str, str], ...] = (),
    domain: Domain | None = None,
) -> BuiltinSpec:
    return BuiltinSpec(
        name, Signature(params, ret, forall, effect, constraints),
        since, lowering, domain,
    )


_MAP_K = (("Eq", "K"), ("Hash", "K"))
_SET_T = (("Eq", "T"), ("Hash", "T"))

_CHAR_CODE_DOMAIN = Domain(
    requires="@Int.0 >= 0 && @Int.0 < string_length(@String.0)",
    trap=(
        "the index is compared in i64 with the string's length in bytes, and "
        "the call traps when it is negative or not below that length"
    ),
)


def _table(*specs: BuiltinSpec) -> dict[str, BuiltinSpec]:
    out: dict[str, BuiltinSpec] = {}
    for spec in specs:
        if spec.name in out:  # pragma: no cover — table typo
            raise ValueError(f"built-in {spec.name!r} declared twice")
        out[spec.name] = spec
    return out


#: Every built-in function, in the order ``TypeEnv`` registers them.
BUILTINS: Mapping[str, BuiltinSpec] = _table(
    # --- Arrays: iterative WASM, the combinators over `call_indirect`
    # (#480, #466 phase 1) ---------------------------------------------
    _fn("array_length", (_array(T),), INT,
        forall=("T",), since="0.0.78", lowering=Inline("_translate_array_length")),
    _fn("array_append", (_array(T), T), _array(T),
        forall=("T",), since="0.0.78", lowering=Inline("_translate_array_append")),
    _fn("array_range", (INT, INT), _array(INT),
        since="0.0.78", lowering=Inline("_translate_array_range")),
    _fn("array_concat", (_array(T), _array(T)), _array(T),
        forall=("T",), since="0.0.78", lowering=Inline("_translate_array_concat")),
    _fn("array_slice", (_array(T), INT, INT), _array(T),
        forall=("T",), since="0.0.91", lowering=Inline("_translate_array_slice")),
    _fn("array_map", (_array(A), _pure_fn((A,), B)), _array(B),
        forall=("A", "B"), since="0.0.91", lowering=Inline("_translate_array_map")),
    _fn("array_filter", (_array(T), _pure_fn((T,), BOOL)), _array(T),
        forall=("T",), since="0.0.91", lowering=Inline("_translate_array_filter")),
    _fn("array_fold", (_array(T), U, _pure_fn((U, T), U)), U,
        forall=("T", "U"), since="0.0.91", lowering=Inline("_translate_array_fold")),
    _fn("array_mapi", (_array(A), _pure_fn((A, NAT), B)), _array(B),
        forall=("A", "B"), since="0.0.117", lowering=Inline("_translate_array_mapi")),
    _fn("array_reverse", (_array(T),), _array(T),
        forall=("T",), since="0.0.117", lowering=Inline("_translate_array_reverse")),
    _fn("array_find", (_array(T), _pure_fn((T,), BOOL)), _option(T),
        forall=("T",), since="0.0.117", lowering=Inline("_translate_array_find")),
    _fn("array_any", (_array(T), _pure_fn((T,), BOOL)), BOOL,
        forall=("T",), since="0.0.117", lowering=Inline("_translate_array_any")),
    _fn("array_all", (_array(T), _pure_fn((T,), BOOL)), BOOL,
        forall=("T",), since="0.0.117", lowering=Inline("_translate_array_all")),
    _fn("array_flatten", (_array(_array(T)),), _array(T),
        forall=("T",), since="0.0.117", lowering=Inline("_translate_array_flatten")),
    _fn("array_sort_by", (_array(T), _pure_fn((T, T), _ORDERING)), _array(T),
        forall=("T",), since="0.0.117", lowering=Inline("_translate_array_sort_by")),
    # --- Map<K, V>: functions of the module, one per key and value
    # representation (`vera.wasm.hamt`, #1676); `Eq<K>` and `Hash<K>` ------
    _fn("map_new", (), _map(K, V),
        forall=("K", "V"), constraints=_MAP_K, since="0.0.94",
        lowering=Inline("_translate_map_new", Binding.CALL)),
    _fn("map_insert", (_map(K, V), K, V), _map(K, V),
        forall=("K", "V"), constraints=_MAP_K, since="0.0.94",
        lowering=Inline("_translate_map_insert", Binding.CALL)),
    _fn("map_get", (_map(K, V), K), _option(V),
        forall=("K", "V"), constraints=_MAP_K, since="0.0.94",
        lowering=Inline("_translate_map_get", Binding.CALL)),
    _fn("map_contains", (_map(K, V), K), BOOL,
        forall=("K", "V"), constraints=_MAP_K, since="0.0.94",
        lowering=Inline("_translate_map_contains", Binding.CALL)),
    _fn("map_remove", (_map(K, V), K), _map(K, V),
        forall=("K", "V"), constraints=_MAP_K, since="0.0.94",
        lowering=Inline("_translate_map_remove", Binding.CALL)),
    _fn("map_size", (_map(K, V),), INT,
        forall=("K", "V"), constraints=_MAP_K, since="0.0.94",
        lowering=Inline("_translate_map_size")),
    _fn("map_keys", (_map(K, V),), _array(K),
        forall=("K", "V"), constraints=_MAP_K, since="0.0.94",
        lowering=Inline("_translate_map_keys", Binding.CALL)),
    _fn("map_values", (_map(K, V),), _array(V),
        forall=("K", "V"), constraints=_MAP_K, since="0.0.94",
        lowering=Inline("_translate_map_values", Binding.CALL)),
    # --- Set<T>: functions of the module, one per element
    # representation (`vera.wasm.hamt`, #1676); `Eq<T>` and `Hash<T>` --
    _fn("set_new", (), _set(T),
        forall=("T",), constraints=_SET_T, since="0.0.95",
        lowering=Inline("_translate_set_new", Binding.CALL)),
    _fn("set_add", (_set(T), T), _set(T),
        forall=("T",), constraints=_SET_T, since="0.0.95",
        lowering=Inline("_translate_set_add", Binding.CALL)),
    _fn("set_contains", (_set(T), T), BOOL,
        forall=("T",), constraints=_SET_T, since="0.0.95",
        lowering=Inline("_translate_set_contains", Binding.CALL)),
    _fn("set_remove", (_set(T), T), _set(T),
        forall=("T",), constraints=_SET_T, since="0.0.95",
        lowering=Inline("_translate_set_remove", Binding.CALL)),
    _fn("set_size", (_set(T),), INT,
        forall=("T",), constraints=_SET_T, since="0.0.95",
        lowering=Inline("_translate_set_size")),
    _fn("set_to_array", (_set(T),), _array(T),
        forall=("T",), constraints=_SET_T, since="0.0.95",
        lowering=Inline("_translate_set_to_array", Binding.CALL)),
    # --- Decimal: construction, conversion, arithmetic, comparison,
    # rounding.  A unary operation's literals are its import's parameter
    # and result types, which its emitter reads to wrap and unwrap -------
    _fn("decimal_from_int", (INT,), _DECIMAL, since="0.0.97",
        lowering=Host("_translate_decimal_unary", "decimal", Binding.CALL_EXTRA,
                      ("decimal_from_int", "i64", "i32"))),
    _fn("decimal_from_float", (FLOAT64,), _DECIMAL, since="0.0.97",
        lowering=Host("_translate_decimal_unary", "decimal", Binding.CALL_EXTRA,
                      ("decimal_from_float", "f64", "i32"))),
    _fn("decimal_from_string", (STRING,), _option(_DECIMAL), since="0.0.97",
        lowering=Host("_translate_decimal_from_string", "decimal", Binding.CALL)),
    _fn("decimal_to_string", (_DECIMAL,), STRING, since="0.0.97",
        lowering=Host("_translate_decimal_to_string", "decimal", Binding.CALL)),
    _fn("decimal_to_float", (_DECIMAL,), FLOAT64, since="0.0.97",
        lowering=Host("_translate_decimal_unary", "decimal", Binding.CALL_EXTRA,
                      ("decimal_to_float", "i32", "f64"))),
    _fn("decimal_add", (_DECIMAL, _DECIMAL), _DECIMAL, since="0.0.97",
        lowering=Host("_translate_decimal_binary", "decimal", Binding.CALL_EXTRA,
                      ("decimal_add",))),
    _fn("decimal_sub", (_DECIMAL, _DECIMAL), _DECIMAL, since="0.0.97",
        lowering=Host("_translate_decimal_binary", "decimal", Binding.CALL_EXTRA,
                      ("decimal_sub",))),
    _fn("decimal_mul", (_DECIMAL, _DECIMAL), _DECIMAL, since="0.0.97",
        lowering=Host("_translate_decimal_binary", "decimal", Binding.CALL_EXTRA,
                      ("decimal_mul",))),
    _fn("decimal_div", (_DECIMAL, _DECIMAL), _option(_DECIMAL), since="0.0.97",
        lowering=Host("_translate_decimal_div", "decimal", Binding.CALL)),
    _fn("decimal_neg", (_DECIMAL,), _DECIMAL, since="0.0.97",
        lowering=Host("_translate_decimal_unary", "decimal", Binding.CALL_EXTRA,
                      ("decimal_neg", "i32", "i32"))),
    _fn("decimal_compare", (_DECIMAL, _DECIMAL), _ORDERING, since="0.0.97",
        lowering=Host("_translate_decimal_compare", "decimal", Binding.CALL)),
    _fn("decimal_eq", (_DECIMAL, _DECIMAL), BOOL, since="0.0.97",
        lowering=Host("_translate_decimal_eq", "decimal", Binding.CALL)),
    _fn("decimal_round", (_DECIMAL, INT), _DECIMAL, since="0.0.97",
        lowering=Host("_translate_decimal_round", "decimal", Binding.CALL)),
    _fn("decimal_abs", (_DECIMAL,), _DECIMAL, since="0.0.97",
        lowering=Host("_translate_decimal_unary", "decimal", Binding.CALL_EXTRA,
                      ("decimal_abs", "i32", "i32"))),
    # --- Option / Result combinators: prelude bodies --------------------
    _fn("option_unwrap_or", (_option(T), T), T,
        forall=("T",), since="0.0.89", lowering=Prelude()),
    _fn("option_map", (_option(A), _pure_fn((A,), B)), _option(B),
        forall=("A", "B"), since="0.0.89", lowering=Prelude()),
    _fn("option_and_then", (_option(A), _pure_fn((A,), _option(B))), _option(B),
        forall=("A", "B"), since="0.0.89", lowering=Prelude()),
    _fn("result_unwrap_or", (_result(T, E), T), T,
        forall=("T", "E"), since="0.0.89", lowering=Prelude()),
    _fn("result_map", (_result(A, E), _pure_fn((A,), B)), _result(B, E),
        forall=("A", "B", "E"), since="0.0.89", lowering=Prelude()),
    # --- Strings ----------------------------------------------------------
    _fn("string_length", (STRING,), NAT,
        since="0.0.50", lowering=Inline("_translate_string_length")),
    _fn("string_concat", (STRING, STRING), STRING,
        since="0.0.50", lowering=Inline("_translate_string_concat")),
    _fn("string_slice", (STRING, NAT, NAT), STRING,
        since="0.0.50", lowering=Inline("_translate_string_slice")),
    _fn("string_char_code", (STRING, INT), NAT,
        since="0.0.50", lowering=Inline("_translate_char_code", Binding.ARGS_AT),
        domain=_CHAR_CODE_DOMAIN),
    _fn("string_from_char_code", (NAT,), STRING,
        since="0.0.74", lowering=Inline("_translate_from_char_code")),
    _fn("string_repeat", (STRING, NAT), STRING,
        since="0.0.75", lowering=Inline("_translate_string_repeat")),
    # --- Parsing and encoding ---------------------------------------------
    _fn("parse_nat", (STRING,), _result(NAT, STRING),
        since="0.0.50", lowering=Inline("_translate_parse_nat")),
    _fn("parse_int", (STRING,), _result(INT, STRING),
        since="0.0.77", lowering=Inline("_translate_parse_int")),
    _fn("parse_float64", (STRING,), _result(FLOAT64, STRING),
        since="0.0.50", lowering=Inline("_translate_parse_float64")),
    _fn("parse_bool", (STRING,), _result(BOOL, STRING),
        since="0.0.77", lowering=Inline("_translate_parse_bool")),
    _fn("base64_encode", (STRING,), STRING,
        since="0.0.79", lowering=Inline("_translate_base64_encode")),
    _fn("base64_decode", (STRING,), _result(STRING, STRING),
        since="0.0.79", lowering=Inline("_translate_base64_decode")),
    # A `String` and an `Array<Byte>` are both a (ptr, len) pair over
    # one-byte cells, so the string pair's emitters encode and decode bytes
    # (#1711).
    _fn("base64_encode_bytes", (_array(BYTE),), STRING,
        since="0.2.4", lowering=Inline("_translate_base64_encode")),
    _fn("base64_decode_bytes", (STRING,), _result(_array(BYTE), STRING),
        since="0.2.4", lowering=Inline("_translate_base64_decode")),
    # --- UTF-8 between `String` and `Array<Byte>` (#1711) ------------------
    _fn("string_to_bytes", (STRING,), _array(BYTE),
        since="0.2.4", lowering=Inline("_translate_string_to_bytes")),
    _fn("bytes_to_string", (_array(BYTE),), _result(STRING, STRING),
        since="0.2.4", lowering=Inline("_translate_bytes_to_string")),
    _fn("url_encode", (STRING,), STRING,
        since="0.0.80", lowering=Inline("_translate_url_encode")),
    _fn("url_decode", (STRING,), _result(STRING, STRING),
        since="0.0.80", lowering=Inline("_translate_url_decode")),
    _fn("url_parse", (STRING,), _result(_URL_PARTS, STRING),
        since="0.0.81", lowering=Inline("_translate_url_parse")),
    _fn("url_join", (_URL_PARTS,), STRING,
        since="0.0.81", lowering=Inline("_translate_url_join")),
    # --- Markdown (§9.7.3): host imports -----------------------------------
    _fn("md_parse", (STRING,), _result(_MD, STRING),
        since="0.0.84", lowering=Host("_translate_md_parse", "md")),
    _fn("md_render", (_MD,), STRING,
        since="0.0.84", lowering=Host("_translate_md_render", "md")),
    _fn("md_has_heading", (_MD, NAT), BOOL,
        since="0.0.84", lowering=Host("_translate_md_has_heading", "md")),
    _fn("md_has_code_block", (_MD, STRING), BOOL,
        since="0.0.84", lowering=Host("_translate_md_has_code_block", "md")),
    _fn("md_extract_code_blocks", (_MD, STRING), _array(STRING),
        since="0.0.84", lowering=Host("_translate_md_extract_code_blocks", "md")),
    # --- Json (§9.7.1): parse and stringify are host imports, the
    # utilities and the typed accessors (#366) prelude bodies -------------
    _fn("json_parse", (STRING,), _result(_JSON, STRING),
        since="0.0.98", lowering=Host("_translate_json_parse", "json")),
    _fn("json_stringify", (_JSON,), STRING,
        since="0.0.98", lowering=Host("_translate_json_stringify", "json")),
    _fn("json_get", (_JSON, STRING), _option(_JSON),
        since="0.0.98", lowering=Prelude()),
    _fn("json_array_get", (_JSON, INT), _option(_JSON),
        since="0.0.98", lowering=Prelude()),
    _fn("json_array_length", (_JSON,), INT,
        since="0.0.98", lowering=Prelude()),
    _fn("json_keys", (_JSON,), _array(STRING),
        since="0.0.98", lowering=Prelude()),
    _fn("json_has_field", (_JSON, STRING), BOOL,
        since="0.0.98", lowering=Prelude()),
    _fn("json_type", (_JSON,), STRING,
        since="0.0.98", lowering=Prelude()),
    _fn("json_as_string", (_JSON,), _option(STRING),
        since="0.0.119", lowering=Prelude()),
    _fn("json_as_number", (_JSON,), _option(FLOAT64),
        since="0.0.119", lowering=Prelude()),
    _fn("json_as_bool", (_JSON,), _option(BOOL),
        since="0.0.119", lowering=Prelude()),
    _fn("json_as_int", (_JSON,), _option(INT),
        since="0.0.119", lowering=Prelude()),
    _fn("json_as_array", (_JSON,), _option(_array(_JSON)),
        since="0.0.119", lowering=Prelude()),
    _fn("json_as_object", (_JSON,), _option(_map(STRING, _JSON)),
        since="0.0.119", lowering=Prelude()),
    _fn("json_get_string", (_JSON, STRING), _option(STRING),
        since="0.0.119", lowering=Prelude()),
    _fn("json_get_number", (_JSON, STRING), _option(FLOAT64),
        since="0.0.119", lowering=Prelude()),
    _fn("json_get_bool", (_JSON, STRING), _option(BOOL),
        since="0.0.119", lowering=Prelude()),
    _fn("json_get_int", (_JSON, STRING), _option(INT),
        since="0.0.119", lowering=Prelude()),
    _fn("json_get_array", (_JSON, STRING), _option(_array(_JSON)),
        since="0.0.119", lowering=Prelude()),
    # --- Html (§9.7.4): host imports; `html_attr` a prelude body --------
    _fn("html_parse", (STRING,), _result(_HTML, STRING),
        since="0.0.100", lowering=Host("_translate_html_parse", "html")),
    _fn("html_to_string", (_HTML,), STRING,
        since="0.0.100", lowering=Host("_translate_html_to_string", "html")),
    _fn("html_query", (_HTML, STRING), _array(_HTML),
        since="0.0.100", lowering=Host("_translate_html_query", "html")),
    _fn("html_text", (_HTML,), STRING,
        since="0.0.100", lowering=Host("_translate_html_text", "html")),
    _fn("html_attr", (_HTML, STRING), _option(STRING),
        since="0.0.100", lowering=Prelude()),
    # --- Regex (§9.6.15): host imports ------------------------------------
    _fn("regex_match", (STRING, STRING), _result(BOOL, STRING),
        since="0.0.86", lowering=Host("_translate_regex_match", "regex")),
    _fn("regex_find", (STRING, STRING), _result(_option(STRING), STRING),
        since="0.0.86", lowering=Host("_translate_regex_find", "regex")),
    _fn("regex_find_all", (STRING, STRING), _result(_array(STRING), STRING),
        since="0.0.86", lowering=Host("_translate_regex_find_all", "regex")),
    _fn("regex_replace", (STRING, STRING, STRING), _result(STRING, STRING),
        since="0.0.86", lowering=Host("_translate_regex_replace", "regex")),
    # --- Async: `effects(<Async>)`; a fused `async(Http.get/post)` and its
    # `await` call the async rows below (#841) ---------------------------
    _fn("async", (T,), _future(T),
        forall=("T",), effect=_ASYNC, since="0.0.82",
        lowering=Inline("_translate_async")),
    _fn("await", (_future(T),), T,
        forall=("T",), effect=_ASYNC, since="0.0.82",
        lowering=Inline("_translate_await")),
    # --- Conversions to String --------------------------------------------
    _fn("to_string", (INT,), STRING,
        since="0.0.50", lowering=Inline("_translate_to_string")),
    _fn("int_to_string", (INT,), STRING,
        since="0.0.64", lowering=Inline("_translate_to_string")),
    _fn("bool_to_string", (BOOL,), STRING,
        since="0.0.64", lowering=Inline("_translate_bool_to_string")),
    _fn("nat_to_string", (NAT,), STRING,
        since="0.0.64", lowering=Inline("_translate_nat_to_string")),
    _fn("byte_to_string", (BYTE,), STRING,
        since="0.0.64", lowering=Inline("_translate_byte_to_string")),
    _fn("float_to_string", (FLOAT64,), STRING,
        since="0.0.64", lowering=Inline("_translate_float_to_string", Binding.ARGS_SITE)),
    _fn("string_strip", (STRING,), STRING,
        since="0.0.50", lowering=Inline("_translate_strip")),
    # --- String search and transformation ----------------------------------
    _fn("string_contains", (STRING, STRING), BOOL,
        since="0.0.73", lowering=Inline("_translate_string_contains")),
    _fn("string_starts_with", (STRING, STRING), BOOL,
        since="0.0.73", lowering=Inline("_translate_starts_with")),
    _fn("string_ends_with", (STRING, STRING), BOOL,
        since="0.0.73", lowering=Inline("_translate_ends_with")),
    _fn("string_index_of", (STRING, STRING), _option(NAT),
        since="0.0.73", lowering=Inline("_translate_index_of")),
    _fn("string_upper", (STRING,), STRING,
        since="0.0.73", lowering=Inline("_translate_to_upper")),
    _fn("string_lower", (STRING,), STRING,
        since="0.0.73", lowering=Inline("_translate_to_lower")),
    _fn("string_replace", (STRING, STRING, STRING), STRING,
        since="0.0.73", lowering=Inline("_translate_replace")),
    _fn("string_split", (STRING, STRING), _array(STRING),
        since="0.0.73", lowering=Inline("_translate_split")),
    _fn("string_join", (_array(STRING), STRING), STRING,
        since="0.0.73", lowering=Inline("_translate_join")),
    # --- String utilities (#470): `string_chars`, and the structural
    # splits `string_split` cannot express with one delimiter ----------
    _fn("string_chars", (STRING,), _array(STRING),
        since="0.0.118", lowering=Inline("_translate_string_chars")),
    _fn("string_lines", (STRING,), _array(STRING),
        since="0.0.118", lowering=Inline("_translate_string_lines")),
    _fn("string_words", (STRING,), _array(STRING),
        since="0.0.118", lowering=Inline("_translate_string_words")),
    _fn("string_pad_start", (STRING, NAT, STRING), STRING,
        since="0.0.118", lowering=Inline("_translate_string_pad_start")),
    _fn("string_pad_end", (STRING, NAT, STRING), STRING,
        since="0.0.118", lowering=Inline("_translate_string_pad_end")),
    _fn("string_reverse", (STRING,), STRING,
        since="0.0.118", lowering=Inline("_translate_string_reverse")),
    _fn("string_trim_start", (STRING,), STRING,
        since="0.0.118", lowering=Inline("_translate_string_trim_start")),
    _fn("string_trim_end", (STRING,), STRING,
        since="0.0.118", lowering=Inline("_translate_string_trim_end")),
    # --- Character classification and case (#471): each reads the first
    # character; Vera has no Char type, so a character is a one-character
    # String.  An empty string classifies false and converts to "".  The
    # classifiers are ASCII-only -----------------------------------------
    _fn("is_digit", (STRING,), BOOL,
        since="0.0.118", lowering=Inline("_translate_is_digit")),
    _fn("is_alpha", (STRING,), BOOL,
        since="0.0.118", lowering=Inline("_translate_is_alpha")),
    _fn("is_alphanumeric", (STRING,), BOOL,
        since="0.0.118", lowering=Inline("_translate_is_alphanumeric")),
    _fn("is_whitespace", (STRING,), BOOL,
        since="0.0.118", lowering=Inline("_translate_is_whitespace")),
    _fn("is_upper", (STRING,), BOOL,
        since="0.0.118", lowering=Inline("_translate_is_upper")),
    _fn("is_lower", (STRING,), BOOL,
        since="0.0.118", lowering=Inline("_translate_is_lower")),
    _fn("char_to_upper", (STRING,), STRING,
        since="0.0.118", lowering=Inline("_translate_char_to_upper")),
    _fn("char_to_lower", (STRING,), STRING,
        since="0.0.118", lowering=Inline("_translate_char_to_lower")),
    # --- Numeric ------------------------------------------------------------
    _fn("abs", (INT,), NAT,
        since="0.0.70", lowering=Inline("_translate_abs", Binding.ARGS_AT)),
    _fn("min", (INT, INT), INT,
        since="0.0.70", lowering=Inline("_translate_min")),
    _fn("max", (INT, INT), INT,
        since="0.0.70", lowering=Inline("_translate_max")),
    _fn("floor", (FLOAT64,), INT,
        since="0.0.70", lowering=Inline("_translate_floor", Binding.ARGS_AT)),
    _fn("ceil", (FLOAT64,), INT,
        since="0.0.70", lowering=Inline("_translate_ceil", Binding.ARGS_AT)),
    _fn("round", (FLOAT64,), INT,
        since="0.0.70", lowering=Inline("_translate_round", Binding.ARGS_AT)),
    _fn("sqrt", (FLOAT64,), FLOAT64,
        since="0.0.70", lowering=Inline("_translate_sqrt")),
    _fn("pow", (FLOAT64, INT), FLOAT64,
        since="0.0.70", lowering=Inline("_translate_pow")),
    # --- Logarithms and trigonometry (#467): host imports, since WASM has
    # no instruction for them.  Both hosts return NaN outside the domain
    # and -Infinity at a logarithm's pole (#790) ---------------------------
    _fn("log", (FLOAT64,), FLOAT64,
        since="0.0.116", lowering=Host("_translate_math_unary_host", "math", Binding.NAMED)),
    _fn("log2", (FLOAT64,), FLOAT64,
        since="0.0.116", lowering=Host("_translate_math_unary_host", "math", Binding.NAMED)),
    _fn("log10", (FLOAT64,), FLOAT64,
        since="0.0.116", lowering=Host("_translate_math_unary_host", "math", Binding.NAMED)),
    _fn("sin", (FLOAT64,), FLOAT64,
        since="0.0.116", lowering=Host("_translate_math_unary_host", "math", Binding.NAMED)),
    _fn("cos", (FLOAT64,), FLOAT64,
        since="0.0.116", lowering=Host("_translate_math_unary_host", "math", Binding.NAMED)),
    _fn("tan", (FLOAT64,), FLOAT64,
        since="0.0.116", lowering=Host("_translate_math_unary_host", "math", Binding.NAMED)),
    _fn("asin", (FLOAT64,), FLOAT64,
        since="0.0.116", lowering=Host("_translate_math_unary_host", "math", Binding.NAMED)),
    _fn("acos", (FLOAT64,), FLOAT64,
        since="0.0.116", lowering=Host("_translate_math_unary_host", "math", Binding.NAMED)),
    _fn("atan", (FLOAT64,), FLOAT64,
        since="0.0.116", lowering=Host("_translate_math_unary_host", "math", Binding.NAMED)),
    _fn("atan2", (FLOAT64, FLOAT64), FLOAT64,
        since="0.0.116", lowering=Host("_translate_atan2", "math")),
    # --- Constants and numeric utilities (#467), written in WAT.  Both
    # clamps compute `min(max(v, lo), hi)`, so `lo > hi` gives `hi` ---------
    _fn("pi", (), FLOAT64,
        since="0.0.116", lowering=Inline("_translate_pi", Binding.NONE)),
    _fn("e", (), FLOAT64,
        since="0.0.116", lowering=Inline("_translate_e", Binding.NONE)),
    _fn("sign", (INT,), INT,
        since="0.0.116", lowering=Inline("_translate_sign")),
    _fn("clamp", (INT, INT, INT), INT,
        since="0.0.116", lowering=Inline("_translate_clamp")),
    _fn("float_clamp", (FLOAT64, FLOAT64, FLOAT64), FLOAT64,
        since="0.0.116", lowering=Inline("_translate_float_clamp")),
    # --- Numeric conversions ------------------------------------------------
    _fn("int_to_float", (INT,), FLOAT64,
        since="0.0.71", lowering=Inline("_translate_to_float")),
    _fn("float_to_int", (FLOAT64,), INT,
        since="0.0.71", lowering=Inline("_translate_float_to_int", Binding.ARGS_AT)),
    _fn("nat_to_int", (NAT,), INT,
        since="0.0.71", lowering=Inline("_translate_nat_to_int")),
    _fn("int_to_nat", (INT,), _option(NAT),
        since="0.0.71", lowering=Inline("_translate_int_to_nat")),
    _fn("byte_to_int", (BYTE,), INT,
        since="0.0.71", lowering=Inline("_translate_byte_to_int")),
    _fn("int_to_byte", (INT,), _option(BYTE),
        since="0.0.71", lowering=Inline("_translate_int_to_byte")),
    # --- Float64 predicates and special values --------------------------
    _fn("float_is_nan", (FLOAT64,), BOOL,
        since="0.0.72", lowering=Inline("_translate_is_nan")),
    _fn("float_is_infinite", (FLOAT64,), BOOL,
        since="0.0.72", lowering=Inline("_translate_is_infinite")),
    _fn("nan", (), FLOAT64,
        since="0.0.72", lowering=Inline("_translate_nan", Binding.NONE)),
    _fn("infinity", (), FLOAT64,
        since="0.0.72", lowering=Inline("_translate_infinity", Binding.NONE)),
)

#: The ability operations code generation lowers by name (§9.8).
ABILITY_INTRINSICS: Mapping[str, AbilityIntrinsic] = {
    i.name: i for i in (
        AbilityIntrinsic("show", "Show", 1,
                         Inline("_translate_show", Binding.ARGS_CALL)),
        AbilityIntrinsic("hash", "Hash", 1, Inline("_translate_hash")),
    )
}


def _intrinsics() -> dict[str, Intrinsic]:
    out: dict[str, Intrinsic] = {}
    for spec in BUILTINS.values():
        if not isinstance(spec.lowering, Prelude):
            out[spec.name] = Intrinsic(spec.name, spec.arity, spec.lowering)
    for name, ability_op in ABILITY_INTRINSICS.items():
        if name in out:  # pragma: no cover — table typo
            raise ValueError(f"ability intrinsic {name!r} is also a built-in")
        out[name] = Intrinsic(name, ability_op.arity, ability_op.lowering)
    return out


#: What ``_translate_call`` lowers in place of a call, by name: every
#: built-in with an emitter and every ability intrinsic, at its arity.
INTRINSICS: Mapping[str, Intrinsic] = _intrinsics()


def trap_rows(name: str) -> list[TrapEmitter]:
    """The ``TRAP_EMITTERS`` rows of intrinsic *name*'s emitter: the checks
    its translation can trap at, each with its kind."""
    intrinsic = INTRINSICS.get(name)
    if intrinsic is None:
        return []
    suffix = ":" + intrinsic.lowering.emitter
    return [row for key, row in TRAP_EMITTERS.items() if key.endswith(suffix)]


# =====================================================================
# Host imports
# =====================================================================


class Style(enum.Enum):
    """How an import's ``(func ...)`` writes its types."""

    GROUPED = "grouped"
    """``(param i32 i32) (result i32)``."""
    SEPARATE = "separate"
    """``(param i32) (param i32) (result i32)``."""


class Gate(enum.Enum):
    """What decides that a family's import is declared."""

    NAMES = "names"
    """The module used it: code generation recorded its name."""
    FLAG = "flag"
    """A flag of code generation holds: every row of the family."""
    CELL = "cell"
    """Once for each ``State`` cell the module uses."""


@dataclass(frozen=True)
class HostFamily:
    name: str
    style: Style
    gate: Gate


@dataclass(frozen=True)
class HostImport:
    """One ``(import "vera" ...)`` declaration code generation can emit."""

    name: str
    family: str
    #: WAT value types.  In a ``State`` row, ``"C"`` stands for the cell's
    #: type.
    params: tuple[str, ...] = ()
    results: tuple[str, ...] = ()
    #: ``"cell"`` for a ``State`` row, declared once per cell under the
    #: cell's family (``state_get_Int``), or ``""``.
    instance: str = ""
    #: The built-in or effect operation the import implements; empty for
    #: the runtime's own imports.
    serves: str = ""
    #: The declaration as its owner writes it, for an import whose WAT
    #: another module states (the trap signal's, ``vera.trap_registry``).
    line: str = ""
    needs_alloc: bool = False
    needs_memory: bool = False
    needs_wrap_table: bool = False
    #: The WASI worlds whose component implements the import
    #: (``vera/codegen/wasi.py``): ``WASI_CLI``, ``WASI_SERVER``, both, or
    #: neither, and a module that declares it for another world is refused.
    wasi: tuple[str, ...] = ()


#: The two worlds of ``--target wasi-p2``: the command and the HTTP server.
WASI_CLI = "cli"
WASI_SERVER = "server"
_BOTH = (WASI_CLI, WASI_SERVER)

#: The families, in the order a module declares their imports.
HOST_FAMILIES: tuple[HostFamily, ...] = (
    HostFamily("io", Style.GROUPED, Gate.NAMES),
    HostFamily("md", Style.GROUPED, Gate.NAMES),
    HostFamily("regex", Style.GROUPED, Gate.NAMES),
    HostFamily("decimal", Style.SEPARATE, Gate.NAMES),
    HostFamily("wrap", Style.SEPARATE, Gate.FLAG),
    HostFamily("json", Style.GROUPED, Gate.NAMES),
    HostFamily("html", Style.GROUPED, Gate.NAMES),
    HostFamily("http", Style.GROUPED, Gate.NAMES),
    HostFamily("async", Style.GROUPED, Gate.NAMES),
    HostFamily("inference", Style.GROUPED, Gate.NAMES),
    HostFamily("db", Style.GROUPED, Gate.NAMES),
    HostFamily("random", Style.GROUPED, Gate.NAMES),
    HostFamily("math", Style.GROUPED, Gate.NAMES),
    HostFamily("hash", Style.GROUPED, Gate.NAMES),
    HostFamily("contract", Style.GROUPED, Gate.FLAG),
    HostFamily("trap", Style.GROUPED, Gate.FLAG),
    HostFamily("state", Style.GROUPED, Gate.CELL),
)


def _io(name: str, params: tuple[str, ...], results: tuple[str, ...],
        *, alloc: bool = False, server: bool = False) -> HostImport:
    """An IO operation: the cli world's adapter implements every one, and
    the server world's the four a request handler can use."""
    return HostImport(name, "io", params, results, serves=f"IO.{name}",
                      needs_alloc=alloc,
                      wasi=_BOTH if server else (WASI_CLI,))


def _md(name: str, params: tuple[str, ...], results: tuple[str, ...]) -> HostImport:
    return HostImport(name, "md", params, results, serves=name, needs_alloc=True)


def _regex(name: str, params: tuple[str, ...]) -> HostImport:
    return HostImport(name, "regex", params, ("i32",), serves=name,
                      needs_alloc=True)


def _handle(family: str, name: str, params: tuple[str, ...],
            results: tuple[str, ...]) -> HostImport:
    """A Decimal import: its value lives on the GC heap behind a wrapper
    the wrap table reclaims (#573)."""
    return HostImport(name, family, params, results, serves=name,
                      needs_alloc=True, needs_memory=True, needs_wrap_table=True)


def _heap(family: str, name: str, params: tuple[str, ...],
          results: tuple[str, ...], serves: str = "", *,
          wrap: bool = False) -> HostImport:
    """An import whose result the host allocates in the module's memory."""
    return HostImport(name, family, params, results, serves=serves or name,
                      needs_alloc=True, needs_memory=True, needs_wrap_table=wrap)


def _scalar(family: str, name: str, params: tuple[str, ...],
            results: tuple[str, ...], serves: str = "",
            *, wasi: tuple[str, ...] = ()) -> HostImport:
    return HostImport(name, family, params, results, serves=serves or name,
                      wasi=wasi)


_I32_PAIR = ("i32", "i32")

#: Every host import, in the order a module declares them.
HOST_IMPORTS: tuple[HostImport, ...] = (
    # --- IO effect operations (#463, #618) ------------------------------
    _io("args", (), _I32_PAIR, alloc=True),
    _io("exit", ("i64",), ()),
    _io("get_env", _I32_PAIR, ("i32",), alloc=True),
    _io("print", _I32_PAIR, (), server=True),
    _io("read_bytes", _I32_PAIR, ("i32",), alloc=True),
    _io("read_char", (), ("i32",), alloc=True),
    _io("read_file", _I32_PAIR, ("i32",), alloc=True),
    _io("read_line", (), _I32_PAIR, alloc=True),
    _io("sleep", ("i64",), (), server=True),
    _io("stderr", _I32_PAIR, (), server=True),
    _io("time", (), ("i64",), server=True),
    _io("write_bytes", ("i32", "i32", "i32", "i32"), ("i32",), alloc=True),
    _io("write_file", ("i32", "i32", "i32", "i32"), ("i32",), alloc=True),
    # --- Markdown (§9.7.3) --------------------------------------------------
    _md("md_extract_code_blocks", ("i32", "i32", "i32"), _I32_PAIR),
    _md("md_has_code_block", ("i32", "i32", "i32"), ("i32",)),
    _md("md_has_heading", ("i32", "i64"), ("i32",)),
    _md("md_parse", _I32_PAIR, ("i32",)),
    _md("md_render", ("i32",), _I32_PAIR),
    # --- Regex (§9.6.15) ------------------------------------------------------
    _regex("regex_find", ("i32", "i32", "i32", "i32")),
    _regex("regex_find_all", ("i32", "i32", "i32", "i32")),
    _regex("regex_match", ("i32", "i32", "i32", "i32")),
    _regex("regex_replace", ("i32", "i32", "i32", "i32", "i32", "i32")),
    # --- Decimal: a handle into the host's store (#573 phase 3) -------------
    _handle("decimal", "decimal_abs", ("i32",), ("i32",)),
    _handle("decimal", "decimal_add", _I32_PAIR, ("i32",)),
    _handle("decimal", "decimal_compare", _I32_PAIR, ("i32",)),
    _handle("decimal", "decimal_div", _I32_PAIR, ("i32",)),
    _handle("decimal", "decimal_eq", _I32_PAIR, ("i32",)),
    _handle("decimal", "decimal_from_float", ("f64",), ("i32",)),
    _handle("decimal", "decimal_from_int", ("i64",), ("i32",)),
    _handle("decimal", "decimal_from_string", _I32_PAIR, ("i32",)),
    _handle("decimal", "decimal_mul", _I32_PAIR, ("i32",)),
    _handle("decimal", "decimal_neg", ("i32",), ("i32",)),
    _handle("decimal", "decimal_round", ("i32", "i64"), ("i32",)),
    _handle("decimal", "decimal_sub", _I32_PAIR, ("i32",)),
    _handle("decimal", "decimal_to_float", ("i32",), ("f64",)),
    _handle("decimal", "decimal_to_string", ("i32",), _I32_PAIR),
    # --- The wrap table's two helpers (#573, #695/#705): declared when
    # any wrapper is, and called by `$gc_collect`'s phase 2c and by the
    # wrap step ---------------------------------------------------------------
    HostImport("host_decref_handle", "wrap", ("i32", "i32")),
    HostImport("attach_bucket_to_wrapper", "wrap", ("i32", "i32", "i32")),
    # --- Json and Html: the parsers build a `JObject`'s and an
    # `HtmlElement`'s `Map` through the module's own functions (#1676) -----
    _heap("json", "json_parse", _I32_PAIR, ("i32",)),
    _heap("json", "json_stringify", ("i32",), _I32_PAIR),
    _heap("html", "html_parse", _I32_PAIR, ("i32",)),
    _heap("html", "html_to_string", ("i32",), _I32_PAIR),
    _heap("html", "html_query", ("i32", "i32", "i32"), _I32_PAIR),
    _heap("html", "html_text", ("i32",), _I32_PAIR),
    # --- Http effect operations --------------------------------------------
    _heap("http", "http_get", _I32_PAIR, ("i32",), "Http.get"),
    _heap("http", "http_post", ("i32", "i32", "i32", "i32"), ("i32",), "Http.post"),
    # --- Fused async (#841): `async(Http.get/post)` returns a future the
    # wrap table reclaims, and `await` of one blocks on `async_await` ------
    _heap("async", "async_http_get", _I32_PAIR, ("i32",), "Http.get", wrap=True),
    _heap("async", "async_http_post", ("i32", "i32", "i32", "i32"), ("i32",),
          "Http.post", wrap=True),
    _heap("async", "async_await", ("i32",), ("i32",), "await"),
    # --- Inference and DB effect operations (#229) --------------------------
    _heap("inference", "inference_complete", _I32_PAIR, ("i32",),
          "Inference.complete"),
    _heap("db", "db_query", ("i32", "i32", "i32", "i32"), ("i32",), "DB.query"),
    _heap("db", "db_execute", ("i32", "i32", "i32", "i32"), ("i32",), "DB.execute"),
    # --- Random effect operations (#465): scalars, nothing allocated --------
    _scalar("random", "random_int", ("i64", "i64"), ("i64",), "Random.random_int", wasi=_BOTH),
    _scalar("random", "random_float", (), ("f64",), "Random.random_float", wasi=_BOTH),
    _scalar("random", "random_bool", (), ("i32",), "Random.random_bool", wasi=_BOTH),
    # --- Math (#467) ---------------------------------------------------------
    _scalar("math", "log", ("f64",), ("f64",)),
    _scalar("math", "log2", ("f64",), ("f64",)),
    _scalar("math", "log10", ("f64",), ("f64",)),
    _scalar("math", "sin", ("f64",), ("f64",)),
    _scalar("math", "cos", ("f64",), ("f64",)),
    _scalar("math", "tan", ("f64",), ("f64",)),
    _scalar("math", "asin", ("f64",), ("f64",)),
    _scalar("math", "acos", ("f64",), ("f64",)),
    _scalar("math", "atan", ("f64",), ("f64",)),
    _scalar("math", "atan2", ("f64", "f64"), ("f64",)),
    # --- The key a `Map`'s or `Set`'s `String` hash draws, one 64-bit word
    # a call, twice per instantiation (#1736) ----------------------------------
    HostImport("hash_key", "hash", (), ("i64",), wasi=_BOTH),
    # --- The two signals a failing check calls before it traps (#1479) -----
    HostImport(CONTRACT_SIGNAL, "contract", ("i32", "i32"), wasi=_BOTH),
    HostImport(TRAP_SIGNAL, "trap", line=TRAP_IMPORT_WAT, wasi=_BOTH),
    # --- State<T>: four imports per cell, its family mangled (#914) ---------
    HostImport("state_get", "state", (), ("C",), "cell", serves="State.get"),
    HostImport("state_put", "state", ("C",), (), "cell", serves="State.put"),
    HostImport("state_push", "state", (), (), "cell"),
    HostImport("state_pop", "state", (), (), "cell"),
)

#: The rows by name.
HOST_IMPORT_BY_NAME: Mapping[str, HostImport] = {row.name: row for row in HOST_IMPORTS}

_STYLE: Mapping[str, Style] = {f.name: f.style for f in HOST_FAMILIES}

def family_rows(family: str) -> Iterator[HostImport]:
    """A family's rows, in the order a module declares them."""
    return (row for row in HOST_IMPORTS if row.family == family)


#: The ``instance`` of a ``State`` row: named by :func:`cell_lines`.
CELL = "cell"

_CELL_ROWS = tuple(row for row in HOST_IMPORTS if row.instance == CELL)


def host_import(name: str) -> HostImport | None:
    """The row a declared import *name* is an instance of, or None: the
    row's own name, or a ``State`` cell's, the row's name and the cell's
    family (``state_get_Int``)."""
    row = HOST_IMPORT_BY_NAME.get(name)
    if row is not None:
        return row
    return next((r for r in _CELL_ROWS if name.startswith(r.name + "_")), None)


def wasi_refused(world: str) -> tuple[str, ...]:
    """The families a module calls by name whose rows *world*'s component
    implements none of, in :data:`HOST_FAMILIES`' order: a module that
    declares one of their imports is refused for that world."""
    return tuple(
        f.name for f in HOST_FAMILIES
        if f.gate is Gate.NAMES
        and not any(world in row.wasi for row in family_rows(f.name)))


def _func(name: str, params: tuple[str, ...], results: tuple[str, ...],
          style: Style) -> str:
    if style is Style.GROUPED:
        pieces = ([f"(param {' '.join(params)})"] if params else []) + (
            [f"(result {' '.join(results)})"] if results else [])
    else:
        pieces = [f"(param {p})" for p in params] + [f"(result {r})" for r in results]
    return f"(func $vera.{name}" + "".join(" " + piece for piece in pieces) + ")"


def import_line(name: str) -> str:
    """The declaration of import *name*, a row's name."""
    row = HOST_IMPORT_BY_NAME.get(name)
    if row is None or row.instance == CELL:
        raise KeyError(f"no host import declares {name!r}")
    if row.line:
        return row.line
    sig = _func(name, row.params, row.results, _STYLE[row.family])
    return f'  (import "vera" "{name}" {sig})'


def declaration_lines(family: str, names: Collection[str]) -> list[str]:
    """The declarations of *family*'s imports among *names*, in the
    family's row order."""
    return [import_line(row.name) for row in family_rows(family) if row.name in names]


def cell_lines(family_symbol: str, wasm_type: str) -> list[str]:
    """The four declarations of a ``State`` cell, its family mangled."""
    lines: list[str] = []
    for row in family_rows("state"):
        name = f"{row.name}_{family_symbol}"
        params = tuple(wasm_type if p == "C" else p for p in row.params)
        results = tuple(wasm_type if r == "C" else r for r in row.results)
        lines.append(
            f'  (import "vera" "{name}" '
            f"{_func(name, params, results, _STYLE[row.family])})")
    return lines


def _validate() -> None:
    """The tables' own consistency, checked when the module loads."""
    families = [f.name for f in HOST_FAMILIES]
    seen: list[str] = []
    for row in HOST_IMPORTS:
        if row.family not in families:  # pragma: no cover — table typo
            raise ValueError(f"host import {row.name}: unknown family {row.family!r}")
        if seen and seen[-1] != row.family and row.family in seen:  # pragma: no cover
            raise ValueError(f"host import {row.name}: family {row.family!r} is split")
        if not seen or seen[-1] != row.family:
            seen.append(row.family)
    if [f for f in families if f in seen] != seen:  # pragma: no cover — table typo
        raise ValueError("host imports are not in HOST_FAMILIES' order")
    if len(HOST_IMPORT_BY_NAME) != len(HOST_IMPORTS):  # pragma: no cover
        raise ValueError("a host import is declared twice")
    for row in HOST_IMPORTS:
        if not set(row.wasi) <= set(_BOTH):  # pragma: no cover — table typo
            raise ValueError(f"host import {row.name}: unknown WASI world in {row.wasi}")
    for row in HOST_IMPORTS:
        slots = {t for t in (*row.params, *row.results) if t.isupper()}
        if slots - ({"C"} if row.instance == CELL else set()):  # pragma: no cover
            raise ValueError(
                f"host import {row.name}: placeholders {sorted(slots)} outside"
                f" a State cell's row")
    for spec in BUILTINS.values():
        low = spec.lowering
        if isinstance(low, Host):
            served = [r for r in HOST_IMPORTS if r.serves == spec.name]
            if low.family not in families or not served or any(
                    r.family != low.family for r in served):  # pragma: no cover
                raise ValueError(
                    f"built-in {spec.name}: no {low.family!r} host import serves it")


_validate()
