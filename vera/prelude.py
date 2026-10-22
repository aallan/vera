"""Standard prelude — built-in ADT and combinator injection.

The prelude makes ``Option<T>``, ``Result<T, E>``, ``Ordering``, and
``UrlParts`` available in every program without explicit ``data``
declarations.  It also injects combinator functions for Option/Result
and higher-order array operations.

All prelude declarations are prepended to the program's AST.  The prelude
is a module whose names are reserved (#1469): a declaration that takes one
is refused at check (E151 for a function, E158 for a type), so no
declaration a program makes stands in for a prelude one, and the prelude
injects its declarations whatever the program declares.
"""

from __future__ import annotations

import functools
import re
from collections.abc import Mapping
from types import MappingProxyType

from vera import ast


# #851 — synthetic origin filename for prelude-injected declarations.
# Injected FnDecls carry spans that index into the concatenated prelude
# source buffer (returned by :func:`inject_prelude`), NOT into the
# user's file.  Diagnostics about prelude declarations must cite this
# synthetic file and resolve source lines against that buffer, so a
# prelude line number is never rendered against user source (#851's
# misattribution defect).
PRELUDE_FILE = "<prelude>"

# The prelude's NAMESPACE token (#1316).  Spec §8.4.1 scopes the alias
# namespace to the declaring module, and the prelude is a namespace like any
# other: its combinator bodies are injected into whatever program is being
# compiled, but they were DECLARED here, so they resolve type names against the
# prelude's own aliases and data types — never the entry file's.  Shaped as a
# module path so codegen's `_module_alias_scope` can install it with no special
# case; `<` cannot begin a module-path segment (§8.1 restricts them to
# identifiers), so it can never collide with a real module.
PRELUDE_NAMESPACE: tuple[str, ...] = (PRELUDE_FILE,)


# =====================================================================
# Prelude Vera source
# =====================================================================

# Built-in ADTs — always injected; their names are reserved (#1469).
_PRELUDE_DATA = """\
data Option<T> { None, Some(T) }
data Result<T, E> { Ok(T), Err(E) }
data Ordering { Less, Equal, Greater }
data UrlParts { UrlParts(String, String, String, String, String) }
"""

# #305 — HttpServer handler types, injected only when the program
# mentions them (same conditional pattern as Json / HtmlNode: the Map
# headers field pulls heap and map machinery, which must not leak into
# pure programs' WAT).
# One block per HttpServer type: a module's demand for each is its own, so
# one that declares its own `Request` still takes the prelude's `Response`.
_HTTP_SERVER_TYPES = {
    "Request": (
        "data Request { Request(String, String, Map<String, String>, "
        "String) }\n"),
    "Response": "data Response { Response(Int, Map<String, String>, String) }\n",
}
_HTTP_SERVER_DATA = "".join(_HTTP_SERVER_TYPES.values())

_JSON_DATA = """\
data Json { JNull, JBool(Bool), JNumber(Float64), JString(String), JArray(Array<Json>), JObject(Map<String, Json>) }
"""

_HTML_DATA = """\
data HtmlNode { HtmlElement(String, Map<String, String>, Array<HtmlNode>), HtmlText(String), HtmlComment(String) }
"""

# Every source block above that declares an ADT.  Read only by
# :func:`prelude_adt_names`; a new prelude ADT block belongs here.
_PRELUDE_DATA_SOURCES = (
    _PRELUDE_DATA, _HTTP_SERVER_DATA, _JSON_DATA, _HTML_DATA,
)

_HTML_COMBINATORS = """\
private fn html_attr(@HtmlNode, @String -> @Option<String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @HtmlNode.0 {
    HtmlElement(@String, @Map<String, String>, @Array<HtmlNode>) -> map_get(@Map<String, String>.0, @String.1),
    HtmlText(@String) -> None,
    HtmlComment(@String) -> None
  }
}
"""

# Type aliases needed by closure-taking combinators.
#
# #1221 — the DECLARED names below carry the same reserved ``Vera`` prefix
# as the type parameters: they are codegen-internal, not a vocabulary user
# programs write.  ``inject_prelude`` runs at codegen and at the verifier's
# mono discovery, never at the checker, so every name it injects is a name
# codegen resolves and the checker leaves opaque — two namespaces
# disagreeing about one spelling.  Under the old user-facing names that
# disagreement was writable: a program mixing ``ArrayMapFn<Int, Bool>`` with
# the function type it aliases kept two parameter stacks at check and one at
# codegen, and the emitted export read parameter 2 where the binding table
# said parameter 1 (host-reachable, since the checker rejects every
# Vera-source argument for the opaque head).  Reserving the names makes the
# checker's ignorance correct by construction: E154 refuses a user
# declaration OR reference in this namespace (spec §8.4.1), so no spelling a
# program can contain resolves on one side only.  Function types have their
# one canonical spelling — ``fn(Int -> Bool) effects(pure)`` — and a user
# who wants a short name for it declares their own alias, visibly
# (DESIGN.md principles 2, 3 and 6).
#
# #869 — the type-PARAMETER identifiers below (and on the ``forall``
# combinators further down) use the reserved ``Vera``-prefixed names
# ``VeraA``/``VeraB``/``VeraE``/``VeraT``/``VeraU`` rather than the bare
# single letters ``A``/``B``/``E``/``T``/``U``.  A prelude generic is a
# *template*: it reaches WAT only through monomorphized clones (call
# sites are rewritten to mangled clone names in ``vera/wasm/calls.py``),
# so while a type parameter stays abstract the template body cannot lower
# and codegen's Pass-2 attempt is skipped.  A *user* ADT named with a
# bare single letter (``data A``) put that letter into ``_adt_layouts``,
# and codegen then resolved the identically-named prelude type parameter
# to the concrete user ADT — lowering the ``option_map`` template cleanly
# and emitting it as a bare-named function whose passed-in-closure
# ``call_indirect`` referenced a function table the module never declared
# (``unknown table 0`` at ``vera run`` on a check/verify-green program).
# Reserved parameter names no ordinary user ADT spells keep prelude
# internals invisible to user namespace decisions (spec §0.2 principle 4;
# DESIGN.md principle 2 "explicitness — no implicit behaviour").  These
# names are substitution keys only — they never appear in a mangled clone
# suffix (``Monomorphizer._mangle_fn_name`` escapes the concrete type
# *arguments*), so the rename is orthogonal to the #775/#883 injective
# name mangling.
_OPTION_TYPE_ALIASES = """\
type VeraOptionMapFn<VeraA, VeraB> = fn(VeraA -> VeraB) effects(pure);
type VeraOptionBindFn<VeraA, VeraB> = fn(VeraA -> Option<VeraB>) effects(pure);
"""

_RESULT_TYPE_ALIASES = """\
type VeraResultMapFn<VeraA, VeraB> = fn(VeraA -> VeraB) effects(pure);
"""

_ARRAY_TYPE_ALIASES = """\
type VeraArrayMapFn<VeraA, VeraB> = fn(VeraA -> VeraB) effects(pure);
type VeraArrayFilterFn<VeraT> = fn(VeraT -> Bool) effects(pure);
type VeraArrayFoldFn<VeraT, VeraU> = fn(VeraU, VeraT -> VeraU) effects(pure);
"""


# The blocks above are the ONE table of prelude alias declarations: both
# consumers of the injection — codegen (Pass 1.2) and the verifier's mono
# discovery — read it through :func:`inject_prelude`, so neither restates
# a name the other has to match.  They go in unconditionally with the
# bodies that need them (#1184): nothing a user program declares can take
# a name out of this namespace, so there is no shadowing case to skip an
# injection for, and a combinator whose parameter alias went missing would
# emit an ``Int``-typed closure parameter (WASM validation failure at
# ``vera run``) or silently produce a program with no exports.
#
# ``_ARRAY_COMBINATORS`` is empty, so no prelude declaration currently
# resolves through the array block; it stays injected so a future array
# combinator with a prelude body has its parameter aliases already in
# place (array_map / array_filter / array_fold are emitted as iterative
# WASM by codegen, #480).

# Array higher-order operations.
# array_map, array_filter, and array_fold are all emitted as iterative
# WASM loops by codegen (#480) — none of them have prelude bodies now.
# The ``_ARRAY_COMBINATORS`` source block is empty but kept for
# symmetry with the Option/Result injection pattern; if a future
# combinator lands as a prelude-injected recursive helper again, this
# is where it goes.  De Bruijn slot references are commented for
# clarity in any future additions.
_ARRAY_COMBINATORS = ""

_JSON_COMBINATORS = """\
private fn json_get(@Json, @String -> @Option<Json>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> None,
    JBool(@Bool) -> None,
    JNumber(@Float64) -> None,
    JString(@String) -> None,
    JArray(@Array<Json>) -> None,
    JObject(@Map<String, Json>) -> map_get(@Map<String, Json>.0, @String.0)
  }
}

private fn json_array_get(@Json, @Int -> @Option<Json>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> None,
    JBool(@Bool) -> None,
    JNumber(@Float64) -> None,
    JString(@String) -> None,
    JArray(@Array<Json>) ->
      if @Int.0 >= 0 && @Int.0 < array_length(@Array<Json>.0) then {
        Some(@Array<Json>.0[@Int.0])
      } else {
        None
      },
    JObject(@Map<String, Json>) -> None
  }
}

private fn json_array_length(@Json -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Json.0 {
    JNull -> 0,
    JBool(@Bool) -> 0,
    JNumber(@Float64) -> 0,
    JString(@String) -> 0,
    JArray(@Array<Json>) -> array_length(@Array<Json>.0),
    JObject(@Map<String, Json>) -> 0
  }
}

private fn json_keys(@Json -> @Array<String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> [],
    JBool(@Bool) -> [],
    JNumber(@Float64) -> [],
    JString(@String) -> [],
    JArray(@Array<Json>) -> [],
    JObject(@Map<String, Json>) -> map_keys(@Map<String, Json>.0)
  }
}

private fn json_has_field(@Json, @String -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> false,
    JBool(@Bool) -> false,
    JNumber(@Float64) -> false,
    JString(@String) -> false,
    JArray(@Array<Json>) -> false,
    JObject(@Map<String, Json>) -> map_contains(@Map<String, Json>.0, @String.0)
  }
}

private fn json_type(@Json -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> "null",
    JBool(@Bool) -> "bool",
    JNumber(@Float64) -> "number",
    JString(@String) -> "string",
    JArray(@Array<Json>) -> "array",
    JObject(@Map<String, Json>) -> "object"
  }
}

private fn json_as_string(@Json -> @Option<String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> None,
    JBool(@Bool) -> None,
    JNumber(@Float64) -> None,
    JString(@String) -> Some(@String.0),
    JArray(@Array<Json>) -> None,
    JObject(@Map<String, Json>) -> None
  }
}

private fn json_as_number(@Json -> @Option<Float64>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> None,
    JBool(@Bool) -> None,
    JNumber(@Float64) -> Some(@Float64.0),
    JString(@String) -> None,
    JArray(@Array<Json>) -> None,
    JObject(@Map<String, Json>) -> None
  }
}

private fn json_as_bool(@Json -> @Option<Bool>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> None,
    JBool(@Bool) -> Some(@Bool.0),
    JNumber(@Float64) -> None,
    JString(@String) -> None,
    JArray(@Array<Json>) -> None,
    JObject(@Map<String, Json>) -> None
  }
}

private fn json_as_int(@Json -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> None,
    JBool(@Bool) -> None,
    JNumber(@Float64) ->
      if float_is_nan(@Float64.0)
        || float_is_infinite(@Float64.0)
        || @Float64.0 >= 9223372036854775808.0
        || @Float64.0 < -9223372036854775808.0 then {
        None
      } else {
        Some(float_to_int(@Float64.0))
      },
    JString(@String) -> None,
    JArray(@Array<Json>) -> None,
    JObject(@Map<String, Json>) -> None
  }
}

private fn json_as_array(@Json -> @Option<Array<Json>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> None,
    JBool(@Bool) -> None,
    JNumber(@Float64) -> None,
    JString(@String) -> None,
    JArray(@Array<Json>) -> Some(@Array<Json>.0),
    JObject(@Map<String, Json>) -> None
  }
}

private fn json_as_object(@Json -> @Option<Map<String, Json>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
    JNull -> None,
    JBool(@Bool) -> None,
    JNumber(@Float64) -> None,
    JString(@String) -> None,
    JArray(@Array<Json>) -> None,
    JObject(@Map<String, Json>) -> Some(@Map<String, Json>.0)
  }
}

private fn json_get_string(@Json, @String -> @Option<String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_get(@Json.0, @String.0) {
    None -> None,
    Some(@Json) -> json_as_string(@Json.0)
  }
}

private fn json_get_number(@Json, @String -> @Option<Float64>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_get(@Json.0, @String.0) {
    None -> None,
    Some(@Json) -> json_as_number(@Json.0)
  }
}

private fn json_get_bool(@Json, @String -> @Option<Bool>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_get(@Json.0, @String.0) {
    None -> None,
    Some(@Json) -> json_as_bool(@Json.0)
  }
}

private fn json_get_int(@Json, @String -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_get(@Json.0, @String.0) {
    None -> None,
    Some(@Json) -> json_as_int(@Json.0)
  }
}

private fn json_get_array(@Json, @String -> @Option<Array<Json>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_get(@Json.0, @String.0) {
    None -> None,
    Some(@Json) -> json_as_array(@Json.0)
  }
}
"""

_OPTION_COMBINATORS = """\
private forall<VeraT> fn option_unwrap_or(@Option<VeraT>, @VeraT -> @VeraT)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<VeraT>.0 {
    None -> @VeraT.0,
    Some(@VeraT) -> @VeraT.0
  }
}

private forall<VeraA, VeraB> fn option_map(@Option<VeraA>, @VeraOptionMapFn<VeraA, VeraB> -> @Option<VeraB>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<VeraA>.0 {
    None -> None,
    Some(@VeraA) -> Some(apply_fn(@VeraOptionMapFn<VeraA, VeraB>.0, @VeraA.0))
  }
}

private forall<VeraA, VeraB> fn option_and_then(@Option<VeraA>, @VeraOptionBindFn<VeraA, VeraB> -> @Option<VeraB>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<VeraA>.0 {
    None -> None,
    Some(@VeraA) -> apply_fn(@VeraOptionBindFn<VeraA, VeraB>.0, @VeraA.0)
  }
}
"""

_RESULT_COMBINATORS = """\
private forall<VeraT, VeraE> fn result_unwrap_or(@Result<VeraT, VeraE>, @VeraT -> @VeraT)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Result<VeraT, VeraE>.0 {
    Ok(@VeraT) -> @VeraT.0,
    Err(@VeraE) -> @VeraT.0
  }
}

private forall<VeraA, VeraB, VeraE> fn result_map(@Result<VeraA, VeraE>, @VeraResultMapFn<VeraA, VeraB> -> @Result<VeraB, VeraE>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Result<VeraA, VeraE>.0 {
    Ok(@VeraA) -> Ok(apply_fn(@VeraResultMapFn<VeraA, VeraB>.0, @VeraA.0)),
    Err(@VeraE) -> Err(@VeraE.0)
  }
}
"""


def overridable_builtin_names() -> frozenset[str]:
    """Every function the prelude declares in Vera source.

    Each is a real Vera ``FnDecl`` injected by :func:`inject_prelude`.  Read
    by :func:`reserved_function_names`, which reserves them (#1469), and by
    code generation and the verifier, which tell a prelude body from a user
    one by name.

    Derived from the combinator source blocks so the set stays in step if a
    combinator is added or removed.  The iterative array built-ins
    (``array_map`` / ``array_filter`` / ``array_fold``) are not here:
    ``_ARRAY_COMBINATORS`` is empty (they are codegen-modelled, not
    prelude-injected Vera bodies), so they are built-ins like ``abs``.
    """
    names: set[str] = set()
    for block in (
        _OPTION_COMBINATORS,
        _RESULT_COMBINATORS,
        _JSON_COMBINATORS,
        _HTML_COMBINATORS,
        _ARRAY_COMBINATORS,
    ):
        names.update(re.findall(r"\bfn\s+([a-z_][A-Za-z0-9_]*)", block))
    return frozenset(names)


# =====================================================================
# Reserved names (#1469)
# =====================================================================
#
# The prelude is a module whose names are reserved: no declaration in the
# entry file or in any module may take one, whatever its shape.  This block
# is the ONE place the reserved set is composed; the checker's refusals
# (E151 for a function, E158 for a type) and the rendered lists in
# KNOWN_ISSUES.md and SKILL.md all read it.

#: The built-in data types the type checker registers itself rather than
#: from prelude source (spec §9.7.3).
BUILTIN_ADT_NAMES: tuple[str, ...] = ("MdBlock", "MdInline")

#: The built-in type names code generation recognises by name (spec §9.4):
#: how a value of one is rendered, compared and laid out.
BUILTIN_TYPE_NAMES: tuple[str, ...] = (
    "Array", "Decimal", "Future", "Map", "Set", "Tuple")


@functools.lru_cache(maxsize=1)
def reserved_function_names() -> frozenset[str]:
    """The function names no declaration may take: every function the
    prelude declares (#1469).  A ``fn`` or a ``where`` helper of one of
    these names is refused at check (E151), as a built-in's is."""
    return overridable_builtin_names()


@functools.lru_cache(maxsize=1)
def reserved_type_names() -> frozenset[str]:
    """The type names no declaration may take: the prelude's data types,
    the built-in data types and the built-in type names (#1469).  A
    ``data`` declaration, a ``type`` alias or a type parameter of one of
    these names is refused at check (E158)."""
    return (prelude_adt_names() | frozenset(BUILTIN_ADT_NAMES)
            | frozenset(BUILTIN_TYPE_NAMES))


# =====================================================================
# Detection helpers
# =====================================================================

#: The names through which a program uses each demand-injected block: its
#: type, its constructors, and the built-ins whose signatures carry it.
_JSON_NAMES = frozenset({
    "Json", "JNull", "JBool", "JNumber", "JString", "JArray", "JObject",
    "json_parse", "json_stringify",
    "json_get", "json_has_field", "json_type",
    "json_keys", "json_array_get", "json_array_length",
    # #366 — typed accessors and compound field accessors
    "json_as_string", "json_as_number", "json_as_bool", "json_as_int",
    "json_as_array", "json_as_object",
    "json_get_string", "json_get_number", "json_get_bool",
    "json_get_int", "json_get_array",
})
_HTML_NAMES = frozenset({
    "HtmlNode", "HtmlElement", "HtmlText", "HtmlComment",
    "html_parse", "html_to_string", "html_query", "html_text",
    "html_attr",
})
_HTTP_SERVER_NAMES = frozenset({"Request", "Response", "HttpServer"})
#: Per HttpServer type, the names that use that type: the type (which is
#: also its constructor's name) and the effect a handler declares.  The
#: entry's demand reads the block's names together (`_HTTP_SERVER_NAMES`);
#: a module's is per type (:func:`_modules_demand`).
_HTTP_SERVER_TYPE_NAMES = {
    "Request": frozenset({"Request", "HttpServer"}),
    "Response": frozenset({"Response", "HttpServer"}),
}


def _mentions(program: ast.Program, names: frozenset[str]) -> bool:
    """Whether any declaration of *program* names one of *names*: a type,
    a slot reference, a call or a constructor (:func:`_node_mentions`)."""
    return any(_node_mentions(tld.decl, names) for tld in program.declarations)


def _source_mentions_json(program: ast.Program) -> bool:
    """Check if user code references Json types or constructors.

    Walks all declarations (not just FnDecl) looking for Json-related
    AST nodes in parameters, return types, and bodies (via recursive
    field scan).  This catches modules that use Json values imported
    from other modules or received as parameters.
    """
    return _mentions(program, _JSON_NAMES)


def _source_mentions_html(program: ast.Program) -> bool:
    """Check if user code references HtmlNode types or constructors."""
    return _mentions(program, _HTML_NAMES)


def _source_mentions_http_server(program: ast.Program) -> bool:
    """Check if user code references the HttpServer handler types (#305)."""
    return _mentions(program, _HTTP_SERVER_NAMES)


def _imported_type_names(
    program: ast.Program,
    modules: Mapping[tuple[str, ...], ast.Program],
) -> set[str]:
    """The data type names *program* imports, and their constructors'.

    Importing a type brings its constructors with it (§8.4.2), so each of
    these names means the imported declaration in *program*, whatever the
    prelude calls by the same name.  What *program* imports is the one
    derivation the checker reads (:func:`vera.module_view.imported_data_types`).
    """
    from vera.module_view import imported_data_types

    names: set[str] = set()
    for type_name, suppliers in imported_data_types(program, modules).items():
        names.add(type_name)
        for path in suppliers:
            for tld in modules[path].declarations:
                decl = tld.decl
                if isinstance(decl, ast.DataDecl) and decl.name == type_name:
                    names.update(c.name for c in decl.constructors or ())
    return names


def _modules_demand(
    modules: Mapping[tuple[str, ...], ast.Program],
    names: frozenset[str],
) -> bool:
    """Whether an imported module uses a demand-injected prelude block.

    A module demands the block when it writes one of the block's *names*
    that means the PRELUDE's declaration there.  A type name the module
    imports, and a constructor of such a type, means the imported one and
    demands nothing: a module that imports `a`'s type with a `JNull`
    constructor means `a`'s by `JNull` (PR #1508 review).  The prelude's
    own type names are reserved (#1469, E158), so no module declares or
    exports one; every other mention demands the block: `json_parse`, or a
    constructor only the prelude's type declares, makes a value of the
    prelude's type.
    """
    for module in modules.values():
        if _mentions(module, names - _imported_type_names(module, modules)):
            return True
    return False


def _node_mentions(node: object, names: frozenset[str]) -> bool:
    """Recursively check if any AST node references one of the names."""
    if isinstance(node, ast.NamedType):
        if node.name in names:
            return True
    if isinstance(node, ast.SlotRef):
        if node.type_name in names:
            return True
    if isinstance(node, (ast.FnCall, ast.ConstructorCall)):
        if node.name in names:
            return True
    if isinstance(node, ast.NullaryConstructor):
        if node.name in names:
            return True
    # Recurse into dataclass fields
    if hasattr(node, "__dataclass_fields__"):
        for field_name in node.__dataclass_fields__:
            val = getattr(node, field_name, None)
            if val is None:
                continue
            if isinstance(val, (list, tuple)):
                for item in val:
                    if hasattr(item, "__dataclass_fields__"):
                        if _node_mentions(item, names):
                            return True
            elif hasattr(val, "__dataclass_fields__"):
                if _node_mentions(val, names):
                    return True
    return False


def mentioned_fn_names(node: object, targets: frozenset[str]) -> set[str]:
    """Collect which of ``targets`` appear as call targets in a subtree.

    Recursively walks the AST node's dataclass fields (same traversal
    as :func:`_node_mentions`) and records every ``FnCall`` /
    ``QualifiedCall`` / ``ModuleCall`` whose callee name is in
    ``targets``.  Used by codegen's #851 reachability pass to decide
    which prelude-injected functions a program actually references —
    named functions can only be referenced by calls in Vera (there is
    no bare-name function-value syntax), so call targets are the
    complete reference surface.  ``QualifiedCall`` / ``ModuleCall``
    targets resolve to effect ops / module functions rather than
    prelude combinators, but including them keeps the scan a safe
    over-approximation (a false "referenced" keeps a warning; it never
    hides one).
    """
    found: set[str] = set()
    _collect_mentioned_fn_names(node, targets, found)
    return found


def _collect_mentioned_fn_names(
    node: object, targets: frozenset[str], found: set[str],
) -> None:
    """Recursive worker for :func:`mentioned_fn_names`."""
    if isinstance(node, (ast.FnCall, ast.QualifiedCall, ast.ModuleCall)):
        if node.name in targets:
            found.add(node.name)
    if hasattr(node, "__dataclass_fields__"):
        for field_name in node.__dataclass_fields__:
            val = getattr(node, field_name, None)
            if val is None:
                continue
            if isinstance(val, (list, tuple)):
                for item in val:
                    if hasattr(item, "__dataclass_fields__"):
                        _collect_mentioned_fn_names(item, targets, found)
            elif hasattr(val, "__dataclass_fields__"):
                _collect_mentioned_fn_names(val, targets, found)


# =====================================================================
# Parsing helpers
# =====================================================================

def _parse_source(source: str) -> ast.Program:
    """Parse and transform Vera source into an AST Program."""
    from vera.parser import parse
    from vera.transform import transform

    tree = parse(source)
    return transform(tree)


# =====================================================================
# Public API
# =====================================================================

@functools.lru_cache(maxsize=1)
def prelude_data_decls() -> Mapping[str, ast.DataDecl]:
    """The prelude's own ``data`` declarations, by name (#1277).

    Derived by PARSING the same source blocks :func:`inject_prelude`
    concatenates, with the same parser, so a new prelude ADT joins by
    being written — no second list to keep in step, and no regex
    approximating the grammar.  Cached: the blocks are constants.

    Read through :func:`prelude_adt_names`, the one set of the prelude's
    type names that codegen's ADT-membership floor and the reserved type
    names (:func:`reserved_type_names`, #1469) both read.

    READ-ONLY, because the cache hands every caller the same object: a
    plain dict would let one consumer's mutation reach every later compile
    in the process.  The proxy makes the shared identity safe rather than
    merely undocumented.
    """
    parsed = _parse_source("\n".join(_PRELUDE_DATA_SOURCES))
    return MappingProxyType({
        tld.decl.name: tld.decl
        for tld in parsed.declarations
        if isinstance(tld.decl, ast.DataDecl)
    })


@functools.lru_cache(maxsize=1)
def prelude_adt_names() -> frozenset[str]:
    """Every ADT name the prelude can provide (#1277).

    The checker registers all of them in every ``TypeEnv``
    unconditionally (:mod:`vera.environment`), so they are data types in
    every namespace whatever a program declares — and codegen's
    per-namespace ADT membership (#1253) has to say the same, or the two
    sides disagree about what a NAME MEANS.  Its Pass-0.5 built-in
    snapshot covers only ``_register_builtin_adts``, which is taken
    before Pass 1.2 injects ``Json``, ``HtmlNode``, ``Request`` and
    ``Response``; this set is the floor that completes it.

    Unconditional, deliberately: whether a given program DEMANDS a block
    is `inject_prelude`'s question, and membership must not condition on
    it where the checker does not.  No declaration can take one of these
    names (:func:`reserved_type_names`, E158, #1469), so a name here never
    describes a user's layout.  Cached like :func:`prelude_data_decls`
    beneath it, and for the same reason: the blocks are constants, so the
    answer is too; ``_adt_members_in_scope`` reads it once per namespace.
    """
    return frozenset(prelude_data_decls())


def inject_prelude(
    program: ast.Program,
    modules: Mapping[tuple[str, ...], ast.Program] = MappingProxyType({}),
) -> str:
    """Prepend :func:`prelude_declarations` to *program*'s declarations.

    Mutates ``program.declarations``.  Returns the concatenated prelude
    source buffer the injected declarations' spans index into (#851).
    """
    new_decls, full_source = prelude_declarations(program, modules)
    if not new_decls:  # pragma: no cover
        return full_source
    # Program is a frozen dataclass, so we use object.__setattr__.
    object.__setattr__(
        program,
        "declarations",
        tuple(new_decls) + program.declarations,
    )
    return full_source


def prelude_declarations(
    program: ast.Program,
    modules: Mapping[tuple[str, ...], ast.Program] = MappingProxyType({}),
) -> tuple[tuple[ast.TopLevelDecl, ...], str]:
    """The prelude declarations *program* is compiled with, and the source
    buffer their spans index into; *program* is not changed.

    The buffer lets diagnostics about prelude code quote the actual
    prelude line under the synthetic :data:`PRELUDE_FILE` origin instead
    of misattributing the span's line number to the user's file (#851).
    The resolver pass (:mod:`vera.binding`) binds these declarations'
    calls, so the consumer that compiles them must compile these objects.

    The prelude provides, whatever the program declares (every name it
    takes is reserved, #1469):

    - ``data Option<T>``, ``data Result<T, E>``, ``data Ordering``,
      ``data UrlParts``.
    - Option combinators (``option_unwrap_or``, ``option_map``,
      ``option_and_then``) and Result combinators (``result_unwrap_or``,
      ``result_map``).
    - The closure-parameter type aliases the injected combinators
      resolve through (``VeraOptionMapFn``, ``VeraArrayMapFn``, …).
      Their names are in the prelude's reserved ``Vera`` namespace
      (#869/#1184/#1221), which E154 keeps user programs out of, so no
      user-written type expression resolves through them.  User code
      that wants a short name for a function type declares its own
      alias.
    - Array combinator bodies — none currently.  All three
      (``array_map``, ``array_filter``, ``array_fold``) are emitted
      as iterative WASM by codegen (#480), and ``_ARRAY_COMBINATORS`` is
      empty, so adding a future recursive helper stays a one-line
      change.

    *modules* maps the path of each module *program* imports, directly or
    not, to its program as the checker saw it.  The demand-injected blocks
    (``Json``, ``HtmlNode`` and the HttpServer types) are asked of them
    too, because their bodies are compiled into the same WASM module as
    *program*'s: a module that uses ``Json`` in a program whose entry never
    names it compiled against no ``Json`` at all (PR #1508 review).  A
    module's mention demands a block only where it means the prelude's
    declaration there, which an imported type's constructor of the name
    does not (:func:`_modules_demand`).  Code generation and the verifier's
    monomorphization discovery pass the same programs, so the two sides
    inject the same prelude.
    """
    # Every name a prelude declaration takes is reserved (#1469: E151 for a
    # function, E158 for a type), so no declaration a program makes stands
    # in for one, and none is skipped: the prelude is a module whose names
    # are its own.
    source_parts: list[str] = [_PRELUDE_DATA]
    source_parts.append(_OPTION_TYPE_ALIASES)
    source_parts.append(_OPTION_COMBINATORS)
    source_parts.append(_RESULT_TYPE_ALIASES)
    source_parts.append(_RESULT_COMBINATORS)
    # Array operations: the aliases always; the combinator bodies only when
    # there are any.  `array_map`, `array_filter` and `array_fold` are all
    # built-ins emitted as iterative WASM (#480), so `_ARRAY_COMBINATORS`
    # is empty, and a future array helper that needs a prelude body is a
    # one-line change here.
    source_parts.append(_ARRAY_TYPE_ALIASES)
    if _ARRAY_COMBINATORS:
        source_parts.append(_ARRAY_COMBINATORS)

    # The Json ADT and its utility functions, the HtmlNode ADT and
    # html_attr, and the HttpServer handler types (#305): each only when
    # the program or a module it imports uses it (a Json value triggers
    # heap allocation; the utilities call map_get and the like).  A
    # module's demand is per type (PR #1508 review).
    if _source_mentions_json(program) or _modules_demand(modules, _JSON_NAMES):
        source_parts.append(_JSON_DATA)
        source_parts.append(_JSON_COMBINATORS)
    if _source_mentions_html(program) or _modules_demand(modules, _HTML_NAMES):
        source_parts.append(_HTML_DATA)
        source_parts.append(_HTML_COMBINATORS)
    entry_http = _source_mentions_http_server(program)
    for http_type, http_source in _HTTP_SERVER_TYPES.items():
        if entry_http or _modules_demand(
                modules, _HTTP_SERVER_TYPE_NAMES[http_type]):
            source_parts.append(http_source)

    full_source = "\n".join(source_parts)
    parsed = _parse_source(full_source)
    new_decls = [
        ast.TopLevelDecl(visibility="private", decl=tld.decl, span=None,
                         node_id=tld.node_id)
        for tld in parsed.declarations
    ]
    return tuple(new_decls), full_source
