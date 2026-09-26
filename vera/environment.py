"""Type environment for the Vera type checker.

Manages scope stacks, binding registries, and the De Bruijn slot
reference resolution algorithm.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from vera import ast
from vera.types import (
    BOOL,
    BUILTIN_TYPEVAR_MARKER,
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
    effect_sort_key,
    substitute,
)


# =====================================================================
# Registry data structures
# =====================================================================

if TYPE_CHECKING:  # pragma: no cover — import cycle at runtime
    from vera.regularity import RegularityIndex

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
    # #900: forall type-var names the *body* reads via a `@T.n` slot (a WASM
    # local materialization).  A generic monomorphized at `T = Unit` only
    # crashes codegen (dangling `@T.n`) when its body READS `@T`; a `@T`
    # parameter that is never read erases cleanly from the ABI.  Empty for
    # non-generic and built-in functions.  Drives the narrowed E206.
    forall_vars_read: frozenset[str] = frozenset()


@dataclass
class AdtInfo:
    """Registered algebraic data type."""
    name: str
    type_params: tuple[str, ...] | None
    constructors: dict[str, ConstructorInfo]
    visibility: str | None = None  # "public" | "private" | None (C7c)
    # #1208: this ADT's position in the module's SHARED declaration-index
    # space — see :py:meth:`TypeEnv.next_decl_index`.  ``-1`` means "precedes
    # every user declaration", which is what the built-in ADTs are and what
    # any unstamped construction site conservatively gets.
    decl_index: int = -1


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
    # #1208: the SYNTACTIC alias body, exactly as written.  ``resolved_type``
    # is the semantic collapse computed at registration time and cannot be
    # walked back to the spelling, but the one naming renderer
    # (:mod:`vera.naming`) needs the source-level body to build its
    # ``AliasEnv`` from a live :class:`Environment` — the same map codegen
    # already keeps in its own ``_type_aliases`` side-table.  Defaulted so the
    # other construction sites stay valid; ``None`` means "body unavailable",
    # and the naming env simply omits that alias.
    body: ast.TypeExpr | None = None
    # #1208: this alias's position in the module's SHARED declaration-index
    # space — see :py:meth:`TypeEnv.next_decl_index`.  ``_register_alias``
    # resolves each body against the table as it stood, so the index is what
    # bounds which aliases AND which ADTs that body can see.  ``-1`` (the
    # unstamped default) reads as "precedes everything", matching the
    # always-visible behaviour the flat registries had.
    decl_index: int = -1


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

    ``type_name`` is the name slot references match against, rendered by
    :func:`vera.naming.slot_name` — and alias opacity applies to the HEAD
    of that name only.  ``@PosInt.0`` counts ``PosInt`` bindings and never
    ``Int`` ones; but a parameter written ``@Option<Cnt>`` under
    ``type Cnt = Int`` binds ``Option<Int>``, because a type ARGUMENT is a
    component of a structural type and one type must not become two
    namespaces.  Spec §3.8 and §3.8.1.
    """
    type_name: str       # canonical name for slot matching
    resolved_type: Type  # fully resolved semantic type
    source: str          # "param", "let", "match", "handler",
                         # "destruct", "refinement"
    # #309: the compile-time value of this binding IFF it is a String of
    # literal provenance (a literal, a string_concat of literals, or a let of
    # those), else None.  Computed eagerly when the binding is created — in its
    # own scope — so the SQL literal-provenance gate can follow a let chain
    # through slot references without re-walking a De Bruijn-shifted environment.
    # Only the ``let`` source tracks provenance; ``param`` / ``match`` /
    # ``handler`` / ``destruct`` bindings are always None (conservative — a
    # String parameter used as SQL is correctly rejected).  ``None`` means "no
    # literal available"; ``""`` is the literal empty string — consumers MUST
    # test ``is None``, never truthiness, or the empty literal misroutes.
    literal_str: str | None = None

    # #1160: the binding's compile-time array length when its value is an array
    # literal, else None.  The array-side analogue of ``literal_str``, computed
    # eagerly at the same moment and for the same reason — so the E208 arity
    # check can follow a ``let`` chain without re-walking a De Bruijn-shifted
    # environment.  Only ``let`` bindings carry it.  ``None`` means "length not
    # statically known", which defers the count to the driver; a length is never
    # invented, so resolution failure can only under-report, never false-reject.
    array_len: int | None = None

    def __post_init__(self) -> None:
        """Reject provenance on a binding that cannot legitimately carry it.

        For ``literal_str`` this is the E207 gate itself, not bookkeeping: a
        ``param`` binding that acquired one would make
        ``DB.execute(@String.0, [])`` type-check clean — the textbook
        injection, accepted.  Probed during the #1163 review.

        Enforced here rather than in :meth:`TypeEnv.bind` because
        ``vera/checker/control.py`` constructs a ``Binding`` directly for
        match patterns, bypassing ``bind`` entirely.  ``ValueError`` rather
        than ``assert``: a load-bearing guard must survive ``-O``, and the
        ``ruff --select S`` CI lint rejects asserts used this way.
        """
        if self.source == "let":
            return
        for field_name in ("literal_str", "array_len"):
            if getattr(self, field_name) is not None:
                raise ValueError(
                    f"Binding(source={self.source!r}) carries {field_name}; "
                    f"only 'let' bindings have compile-time provenance "
                    f"(#309 / #1160). A non-let binding is a runtime value, "
                    f"and treating one as literal would defeat the E207 "
                    f"SQL-injection gate."
                )


# =====================================================================
# Type environment
# =====================================================================

# #309: the names of the built-in ``<DB>`` SQL-executing ops.  These are the ops
# codegen lowers to the host database (``wasm/calls.py`` routes any ``DB.<op>``
# to ``$vera.db_<op>`` by qualifier NAME), so they are exactly the calls the
# literal-provenance gate must check.  The gate keys on ``parent_effect == "DB"``
# and membership here — the SAME axis codegen routes on — NOT on built-in OpInfo
# identity, which would gate only the ambient built-in and miss a user
# ``effect DB { op query(...) }`` shadow that still reaches the host.  Such a
# shadow is now separately rejected at its declaration (E152, #1149); the
# name keying stays as defence in depth, so this predicate gates the codegen
# set on its own.  A differential test pins this set against the built-in DB
# effect's declared ops.
DB_SQL_OP_NAMES: frozenset[str] = frozenset({"query", "execute"})


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
    # #1429: names of `data` declarations this module already refused as
    # NON-REGULAR (E129).  Recorded by the checker at the moment it emits the
    # diagnostic, and read by the ability derivations so a refused declaration
    # yields ONE root-cause diagnostic instead of a cascade — `==` over such a
    # value would otherwise report "does not derive Eq" (E243) beside it,
    # which is a true statement about a type the program is not allowed to
    # declare in the first place.  Distinct from asking `vera.regularity`
    # directly, which the derivations ALSO do: that answers for any type,
    # including one reached through an entry point that never ran the data
    # pass, and is what makes them terminate; this set is only about which
    # diagnostics the user is shown.
    refused_non_regular: set[str] = field(default_factory=set)

    # Type variables currently in scope (from forall<T>)
    type_params: dict[str, TypeVar] = field(default_factory=dict)

    # Context flags
    in_ensures: bool = False
    in_contract: bool = False
    # #861: stack of the RESOLVED base types of the refinement predicates
    # currently being type-checked (innermost last; empty = not in a
    # predicate).  Marks predicate context like ``in_contract``, but
    # additionally scopes the Byte-literal comparison allowance (§2.6): an
    # integer literal compared against a Byte-typed operand is typed
    # against Byte — matching the i32 runtime-guard lowering the predicate
    # compiles to (#766) — ONLY when the innermost base resolves to Byte.
    # A stack, not a boolean (PR #876 review): keyed on a boolean, a
    # Byte-typed operand inside an `@Int`-based refinement wrongly got the
    # allowance, and a predicate nested via a forall/exists binder must
    # use ITS base, not the enclosing predicate's.
    refinement_bases: list[Type] = field(default_factory=list)
    current_return_type: Type | None = None
    current_effect_row: EffectRowType | None = None
    # #1215: the RESOLUTION ORDER for a bare (unqualified) effect-op name —
    # innermost handled effect first, then each enclosing handler, then the
    # function's DECLARED row in SOURCE order.  `current_effect_row` carries
    # the same effects as a `frozenset`, which is the right shape for
    # subeffect containment but a hash-seed lottery to iterate; two effects
    # in one row may declare the SAME op name (the built-in `State` and
    # `Http` both declare `get`), and which signature bound flipped with
    # PYTHONHASHSEED.  Set in lock-step with `current_effect_row` at both
    # sites that assign it (checker/core.py `_check_fn`, checker/control.py's
    # handler-body scope); `lookup_effect_op` orders the row by this tuple.
    current_effect_order: tuple[EffectInstance, ...] = ()

    # #1208: the ONE per-module declaration counter that stamps
    # ``AdtInfo.decl_index`` and ``TypeAliasInfo.decl_index``.  Shared
    # deliberately: an alias body sees only what was registered before it, and
    # "before" has to order the two registries against EACH OTHER, not just
    # each within itself.
    _decl_counter: int = 0

    #: Memoised :func:`regularity_index` result, with the registry stamp it
    #: was built from.  Not a `field(default_factory=...)` because it is a
    #: cache, not state: any consumer may drop it and get the same answers.
    _regularity_cache: "tuple[tuple[int, int], RegularityIndex] | None" = None

    def regularity_index(self) -> "RegularityIndex":
        """This module's recursive groups and regularity verdicts (#1429).

        Shared by every consumer holding this env — the checker's E129 test
        and the `Eq` derivation's termination guard — so a module's groups are
        computed once rather than once per declaration or, worse, once per
        field of every `==`.  Deriving them per request re-walked reachability
        from every member of every group, which is cubic in the number of
        declarations: measured on a linked chain of 1000, 55.6 s against about
        a millisecond (PR #1432 re-verification).

        Rebuilt when the registry changes, keyed on the declaration counter —
        which every `data` registration bumps — AND on the registry's size, so
        a write that somehow skipped the counter still invalidates.  Built-ins
        are registered in ``__post_init__``, before any caller exists.
        """
        from vera.regularity import RegularityIndex

        stamp = (self._decl_counter, len(self.data_types))
        cached = self._regularity_cache
        if cached is None or cached[0] != stamp:
            index = RegularityIndex(self.data_types)
            self._regularity_cache = (stamp, index)
            return index
        return cached[1]

    def next_decl_index(self) -> int:
        """Allocate the next declaration index in this module's index space.

        Called once per ``data`` / ``type`` registration, in source order, by
        both the checker's and the verifier's registration passes.  The
        resulting total order is what :mod:`vera.naming` bounds alias-body
        resolution by, so it must be allocated at the moment of registration
        and never reordered.
        """
        idx = self._decl_counter
        self._decl_counter += 1
        return idx

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

        # Request / Response — HTTP server handler types (#305, §9.5.6).
        # Single-constructor ADTs so a `vera serve` handler is an
        # ordinary total function `handle(Request -> Response)` with
        # ordinary contracts.  Field order is load-bearing for the host
        # driver's marshalling (vera/runtime/server.py) and pinned by
        # the built-in ConstructorLayout in codegen/registration.py.
        self.data_types["Request"] = AdtInfo(
            name="Request",
            type_params=(),
            constructors={
                "Request": ConstructorInfo(
                    "Request", "Request", (),
                    (STRING, STRING, _MAP_STR_STR, STRING),
                ),
            },
        )
        self.constructors["Request"] = (
            self.data_types["Request"].constructors["Request"]
        )
        self.data_types["Response"] = AdtInfo(
            name="Response",
            type_params=(),
            constructors={
                "Response": ConstructorInfo(
                    "Response", "Response", (),
                    (INT, _MAP_STR_STR, STRING),
                ),
            },
        )
        self.constructors["Response"] = (
            self.data_types["Response"].constructors["Response"]
        )

        # State<T> effect with get/put
        self.effects["State"] = EffectInfo(
            name="State",
            type_params=("T",),
            operations={
                "get": OpInfo("get", (UNIT,), TypeVar("T"), "State"),
                "put": OpInfo("put", (TypeVar("T"),), UNIT, "State"),
            },
        )

        # Exn<E> effect — `throw` abandons the computation (return type
        # `Never`, so it never resumes).  Lowered by `handle[Exn<E>]` in
        # vera/wasm/calls_handlers.py rather than by a host import, but
        # registered here like every other built-in so it is in scope with no
        # declaration: a program writes `effects(<Exn<String>>)` and calls
        # `throw`.  Before #1149 it was codegen-only, so `handle[Exn<E>]`
        # forced every user to write the `effect Exn<E> { op throw(E ->
        # Never); }` block that E152 now rejects.
        self.effects["Exn"] = EffectInfo(
            name="Exn",
            type_params=("E",),
            operations={
                "throw": OpInfo("throw", (TypeVar("E"),), NEVER, "Exn"),
            },
        )

        # IO effect — built-in operations for console, file, and process I/O.
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
                # Single-character input — for real-time CLI
                # programs (paced REPLs, terminal games, navigation
                # tools).  Result-typed because raw-mode entry can
                # fail (no TTY, EOF, system error).  See #618.
                "read_char": OpInfo(
                    "read_char", (UNIT,),
                    AdtType("Result", (STRING, STRING)), "IO",
                ),
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

        # HttpServer effect — marker for verified HTTP request handling
        # (#305).  No operations: the accept loop lives in the host
        # `vera serve` driver, which calls the program's total
        # `handle(Request -> Response)` function once per request —
        # handlers need no Diverge and are termination-checked like any
        # other function.
        self.effects["HttpServer"] = EffectInfo(
            name="HttpServer",
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

        # DB effect — SQL database access via host imports (#229).
        # Functions using DB.query / DB.execute must declare effects(<DB>).
        # Phase 1 is positional and stringly-typed:
        #   - a parameter is `Option<String>` — Some binds a value, None binds
        #     SQL NULL (DESIGN principle 2: absence is a distinct value, never
        #     collapsed to "");
        #   - `query` returns the result grid as `Array<Array<Option<String>>>`
        #     — outer rows, inner columns, each cell nullable;
        #   - `execute` returns the affected-row count (`Int`; sqlite reports -1
        #     when it cannot count) or an `Err` message.
        # The SQL string is the FIRST argument.  The literal-provenance checker
        # (#309) rejects a non-literal there, making injection a compile-time
        # error; runtime `?`-parameterisation carries all data (a bound value
        # never becomes SQL).
        # Host-backed and un-mockable like Http / Inference — `handle[DB]` is
        # #372's class (host effects aren't user-handleable) and is a stated
        # limitation.  `DB` is a reserved host qualifier: a user
        # `effect DB { ... }` declaration would still route to the host, so the
        # #309 gate keys on `parent_effect == "DB"` + op name (`is_db_sql_op`),
        # the SAME axis codegen routes on, NOT the built-in op identity, which
        # would miss the shadow.  The shadow is also rejected outright at its
        # declaration (E152, #1149); the gate stays as defence in depth.
        _option_string = AdtType("Option", (STRING,))
        _param_array = AdtType("Array", (_option_string,))
        _row_grid = AdtType("Array", (AdtType("Array", (_option_string,)),))
        self.effects["DB"] = EffectInfo(
            name="DB",
            type_params=None,
            operations={
                "query": OpInfo(
                    "query", (STRING, _param_array),
                    AdtType("Result", (_row_grid, STRING)), "DB",
                ),
                "execute": OpInfo(
                    "execute", (STRING, _param_array),
                    AdtType("Result", (INT, STRING)), "DB",
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
        # for negative inputs and `-Infinity` at the zero pole —
        # JavaScript's `Math.log` does both natively, and the Python
        # host wrapper translates `math.log`'s `ValueError` ("math
        # domain error") to NaN except at the pole, where it returns
        # `-inf` (see `vera/runtime/math.py::_math_unary_host`, #790),
        # so both runtimes expose the same IEEE 754 behaviour to
        # Vera code.
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
        # fallthrough is intentional; tests/test_codegen_numeric.py
        # asserts it for both `clamp` (Int) and `float_clamp` (Float64).
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

        # #970: namespace every built-in generic's internal type-var names away
        # from the user's, so a user `forall<T>` (or E/A/B/K/U/V) can never
        # collide by name in the inference skip-guard (_unify_for_inference).
        self._namespace_builtin_typevars()

    def _namespace_builtin_typevars(self) -> None:
        """Alpha-rename each built-in generic's internal type-var names (#970).

        The inference skip-guard (``_unify_for_inference``) matches a concrete
        argument's type-args against the callee's ``forall_vars`` *by name*.
        The registry names its internal vars ``T``/``U``/``A``/``B``/``E``/
        ``K``/``V`` — identical to names a user is likely to pick — so an
        identically-named user ``forall`` var aborted unification, producing a
        spurious E202 whenever it was the immediate type-arg of a compound
        argument type (``@Array<Option<T>>``).  Suffixing each internal name
        with :data:`BUILTIN_TYPEVAR_MARKER` (a parser-unwritable form) makes the
        collision impossible while leaving the guard itself untouched.

        The rename is applied consistently to each signature's ``forall_vars``
        *and* to every ``TypeVar`` occurrence inside its ``param_types`` /
        ``return_type`` (via :func:`substitute` with a var→renamed-var map keyed
        on that signature's own ``forall_vars``) *and* to the ``type_var`` of
        each ``forall_constraints`` entry (``Eq<K>`` / ``Hash<K>`` on the
        ``map_*`` / ``set_*`` families), so the three never drift.  Skipping the
        constraints would leave, e.g., ``map_insert`` with
        ``forall_vars=('K#b','V#b')`` but ``[('Eq','K'),('Hash','K')]`` — inert
        today (built-in constraints don't route through
        ``monomorphize._check_constraints``) but a latent unsound-skip trap.
        """
        from vera.ast import AbilityConstraint

        for info in self.functions.values():
            if not info.forall_vars:
                continue
            original_vars = info.forall_vars
            rename: dict[str, Type] = {
                v: TypeVar(v + BUILTIN_TYPEVAR_MARKER) for v in original_vars
            }
            renamed_name: dict[str, str] = {
                v: v + BUILTIN_TYPEVAR_MARKER for v in original_vars
            }
            info.forall_vars = tuple(renamed_name[v] for v in original_vars)
            info.param_types = tuple(
                substitute(p, rename) for p in info.param_types
            )
            info.return_type = substitute(info.return_type, rename)
            if info.forall_constraints:
                info.forall_constraints = tuple(
                    AbilityConstraint(
                        ability_name=c.ability_name,
                        type_var=renamed_name.get(c.type_var, c.type_var),
                    )
                    if isinstance(c, AbilityConstraint)
                    else c
                    for c in info.forall_constraints
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

    def isolate_scopes(self) -> list[list[Binding]]:
        """Replace the scope stack with a single fresh empty scope and
        return the saved stack for :meth:`restore_scopes`.

        #861 (PR #876 review): a refinement predicate is checked with its
        binder as the SOLE slot in scope (spec §2.6).  A plain
        ``push_scope`` leaves enclosing scopes visible, so a predicate
        checked inside a function body could resolve slots beyond its
        binder (`@Int.1` reaching the enclosing fn's parameter).
        """
        saved = self._scopes
        self._scopes = [[]]
        return saved

    def restore_scopes(self, saved: list[list[Binding]]) -> None:
        """Restore a scope stack saved by :meth:`isolate_scopes`."""
        self._scopes = saved

    def bind(self, type_name: str, resolved_type: Type, source: str,
             literal_str: str | None = None,
             array_len: int | None = None) -> None:
        """Add a binding to the current (innermost) scope.

        ``literal_str`` (#309) is the binding's compile-time literal value when
        it is a String of literal provenance, else None; ``array_len`` (#1160)
        is its compile-time length when the value is an array literal, else
        None.  Both are defaulted so callers that do not track provenance are
        unaffected.
        """
        self._scopes[-1].append(
            Binding(type_name, resolved_type, source, literal_str, array_len))

    # -----------------------------------------------------------------
    # Slot reference resolution (De Bruijn counting)
    # -----------------------------------------------------------------

    def resolve_slot(self, type_name: str, index: int) -> Type | None:
        """Resolve @T.n to its type by counting bindings whose canonical
        type_name matches.  Returns the n-th match's resolved type, or None if
        fewer than n+1 bindings exist.
        """
        binding = self.resolve_slot_binding(type_name, index)
        return binding.resolved_type if binding is not None else None

    def resolve_slot_binding(
        self, type_name: str, index: int,
    ) -> Binding | None:
        """Resolve @T.n to its :class:`Binding`.

        Walks scopes innermost-to-outermost and bindings most-recent-first,
        returning the n-th match, or None if fewer than n+1 exist.  Single-
        sources the De Bruijn counting that :meth:`resolve_slot` (type only)
        and the #309 literal-provenance gate (needs ``Binding.literal_str``)
        both consume.
        """
        count = 0
        # Walk scopes from innermost to outermost
        for scope in reversed(self._scopes):
            # Walk bindings from most recent to earliest within each scope
            for binding in reversed(scope):
                if binding.type_name == type_name:
                    if count == index:
                        return binding
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

    def ordered_effect_row(self) -> tuple[EffectInstance, ...]:
        """The current effect row as an ORDERED sequence (#1215).

        ``current_effect_row.effects`` is a ``frozenset`` — the right shape
        for subeffect containment, the wrong one to *iterate*, because two
        effects in one row may declare the same op name and set iteration
        order is a function of ``PYTHONHASHSEED``.  ``current_effect_order``
        records the semantic order (innermost handled effect first, then each
        enclosing handler, then the declared row in source order); this
        returns the row sequenced by it.

        The result is TOTAL over the row: a member the order tuple does not
        mention (a row assigned without its companion order, e.g. by a
        consumer outside the checker) is not dropped, it follows the ordered
        prefix under a STRUCTURAL tiebreak — still independent of hash seed.
        The tiebreak keys on the effect name AND its rendered type arguments,
        because §7.3.3 lets one effect appear twice with different arguments:
        `State<Int>` and `State<Bool>` tie on name alone, and a stable sort
        then leaves them in the frozenset's own iteration order, which is the
        `PYTHONHASHSEED` dependence this method exists to remove.
        """
        row = self.current_effect_row
        if not isinstance(row, ConcreteEffectRow):
            return ()
        ordered: list[EffectInstance] = []
        seen: set[EffectInstance] = set()
        for ei in self.current_effect_order:
            if ei in row.effects and ei not in seen:
                seen.add(ei)
                ordered.append(ei)
        ordered.extend(sorted(row.effects - seen, key=effect_sort_key))
        return tuple(ordered)

    def lookup_effect_op(self, op_name: str,
                         qualifier: str | None = None) -> OpInfo | None:
        """Look up an effect operation, optionally qualified.

        If qualifier is given, look only in that effect — a deterministic,
        single-candidate lookup.

        A BARE op name can be declared by more than one effect in scope (the
        built-in ``State`` and ``Http`` both declare ``get``), so resolution
        walks ordered candidate lists rather than any set (#1215):

        1. ``ordered_effect_row()`` — innermost handled effect first, then
           each enclosing handler, then the function's DECLARED row in SOURCE
           order (spec §7.4).
        2. every registered effect, in REGISTRATION order.  ``self.effects``
           is a ``dict``, so this is insertion order: the built-ins in the
           order ``_register_builtins`` declares them, then any user
           ``effect`` in source order.  It is the fallback for a clause body
           checked outside its own handler's row, and is deterministic for
           the same reason step 1 is — no set is iterated on either path.
        """
        if qualifier:
            eff = self.effects.get(qualifier)
            if eff and op_name in eff.operations:
                return eff.operations[op_name]
            return None

        for ei in self.ordered_effect_row():
            eff = self.effects.get(ei.name)
            if eff and op_name in eff.operations:
                return eff.operations[op_name]

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

    def is_db_sql_op(self, op: OpInfo) -> bool:
        """Return True iff ``op`` is a ``<DB>`` SQL-executing operation
        (``DB.query`` / ``DB.execute``) — the calls the #309 literal-provenance
        gate must check.

        Keyed on ``parent_effect == "DB"`` and the op name (``DB_SQL_OP_NAMES``),
        which is the SAME axis codegen routes on: ``wasm/calls.py`` lowers any
        ``DB.<op>`` to the host import ``$vera.db_<op>`` by qualifier NAME.  So
        this predicate gates *exactly* the set codegen emits to the database
        (the CLAUDE.md cross-component-soundness invariant).

        It deliberately does NOT key on built-in ``OpInfo`` identity: ``DB`` is a
        reserved host qualifier, so a user ``effect DB { op query(...) }``
        declaration constructs a *distinct* ``OpInfo`` that still routes to the
        host.  An identity key gated only the ambient built-in and let the
        shadow's runtime SQL reach ``conn.execute`` ungated — a silent
        injection bypass (#309 review).  That shadow is separately rejected at
        its declaration since #1149 (E152); the name keying stays as defence in
        depth so this predicate does not depend on it.  A non-``DB`` effect with an op merely
        *named* ``query`` has a different ``parent_effect`` and is routed to the
        user's handler, not the host, so it is correctly not gated.
        """
        return op.parent_effect == "DB" and op.name in DB_SQL_OP_NAMES

    def is_type_name(self, name: str) -> bool:
        """Check if a name refers to a known type (primitive, ADT, or alias)."""
        return (name in PRIMITIVES
                or name in self.data_types
                or name in self.type_aliases)
