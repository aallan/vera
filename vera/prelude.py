"""Standard prelude — built-in ADT and combinator injection.

The prelude makes ``Option<T>``, ``Result<T, E>``, ``Ordering``, and
``UrlParts`` available in every program without explicit ``data``
declarations.  It also injects combinator functions for Option/Result
and higher-order array operations.

All prelude declarations are prepended to the program's AST.  User-
defined declarations with the same name shadow the prelude versions:

- A user ``data Option<T>`` replaces the prelude's ``data Option<T>``.
- A user ``fn option_map`` replaces the prelude's combinator.
- Option/Result combinators are skipped entirely if the user defines
  a non-standard variant (e.g. ``data Option<T> { None, Just(T) }``).
"""

from __future__ import annotations

import functools
import re
from collections.abc import Mapping
from types import MappingProxyType

from vera import ast
from vera.monomorphize import canonicalize_type_aliases


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

# Built-in ADTs — always injected (user definitions shadow these).
_PRELUDE_DATA = """\
data Option<T> { None, Some(T) }
data Result<T, E> { Ok(T), Err(E) }
data Ordering { Less, Equal, Greater }
data UrlParts { UrlParts(String, String, String, String, String) }
"""

# #305 — HttpServer handler types, injected only when the program
# mentions them (same conditional pattern as Json / HtmlNode: the Map
# headers field pulls heap/bucket machinery, which must not leak into
# pure programs' WAT).
_HTTP_SERVER_DATA = """\
data Request { Request(String, String, Map<String, String>, String) }
data Response { Response(Int, Map<String, String>, String) }
"""

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
    """Built-in names the prelude injects as *overridable* Vera combinators.

    Each is a real Vera ``FnDecl`` injected by :func:`inject_prelude`, so a
    user override is sound — the verifier and codegen both reason about
    whichever body is in the program — and ``inject_prelude`` deliberately
    skips its own injection when the user defines one (see the loop in that
    function).  These are therefore *exempt* from the E151 "redefines a
    built-in" check (#815): the unsoundness that motivates E151 is the
    idealized-model-vs-runtime desync of the *opaque*, verifier-modelled
    built-ins (``abs`` / ``min`` / ``max`` / …), which have no Vera body to
    fall back to.

    Derived from the combinator source blocks so the exempt set stays in
    sync automatically if a combinator is added or removed.  Note the
    iterative array built-ins (``array_map`` / ``array_filter`` /
    ``array_fold``) are *not* exempt: ``_ARRAY_COMBINATORS`` is empty
    (they are codegen-modelled, not prelude-injected Vera bodies), so
    redefining them is correctly rejected by E151.
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
# Detection helpers
# =====================================================================

def _is_type_param_ref(field_type: ast.TypeExpr, param_name: str) -> bool:
    """Check if a constructor field type is a bare reference to a type param."""
    return (isinstance(field_type, ast.NamedType)
            and field_type.name == param_name
            and not field_type.type_args)


def _has_standard_option(program: ast.Program) -> bool:
    """Check if the program defines Option<T> with exactly {None, Some(T)}.

    Requires exactly 2 constructors with the standard shape:
    - None: nullary (no fields)
    - Some: one field that references the type parameter T

    Rejects extra constructors, wrong arities, and concrete field types
    like ``Some(Int)`` — the prelude combinators are generic and would
    fail to type-check against a monomorphic variant.
    """
    for tld in program.declarations:
        decl = tld.decl
        if isinstance(decl, ast.DataDecl) and decl.name == "Option":
            if decl.type_params and len(decl.type_params) == 1:
                if len(decl.constructors) != 2:
                    return False
                ctors = {c.name: c for c in decl.constructors}
                if "None" not in ctors or "Some" not in ctors:
                    return False  # pragma: no cover
                none_ctor = ctors["None"]
                some_ctor = ctors["Some"]
                if none_ctor.fields is not None:
                    return False  # pragma: no cover
                if (some_ctor.fields is None
                        or len(some_ctor.fields) != 1):
                    return False  # pragma: no cover
                if not _is_type_param_ref(
                    some_ctor.fields[0], decl.type_params[0],
                ):
                    return False
                return True
    return False  # pragma: no cover


def _has_standard_result(program: ast.Program) -> bool:
    """Check if the program defines Result<T, E> with exactly {Ok(T), Err(E)}.

    Requires exactly 2 constructors with the standard shape:
    - Ok: one field referencing the first type parameter T
    - Err: one field referencing the second type parameter E

    Rejects concrete field types like ``Ok(Int)`` or ``Err(String)``.
    """
    for tld in program.declarations:
        decl = tld.decl
        if isinstance(decl, ast.DataDecl) and decl.name == "Result":
            if decl.type_params and len(decl.type_params) == 2:
                if len(decl.constructors) != 2:
                    return False
                ctors = {c.name: c for c in decl.constructors}
                if "Ok" not in ctors or "Err" not in ctors:
                    return False  # pragma: no cover
                ok_ctor = ctors["Ok"]
                err_ctor = ctors["Err"]
                if (ok_ctor.fields is None
                        or len(ok_ctor.fields) != 1):
                    return False  # pragma: no cover
                if (err_ctor.fields is None
                        or len(err_ctor.fields) != 1):
                    return False  # pragma: no cover
                if not _is_type_param_ref(
                    ok_ctor.fields[0], decl.type_params[0],
                ):
                    return False
                if not _is_type_param_ref(
                    err_ctor.fields[0], decl.type_params[1],
                ):
                    return False  # pragma: no cover
                return True
    return False  # pragma: no cover


def _has_standard_json(program: ast.Program) -> bool:
    """Check if user's ``data Json`` has the expected 6 constructors.

    The prelude Json combinators (json_get, json_type, etc.) pattern-match
    on the standard constructors: JNull, JBool, JNumber, JString, JArray,
    JObject.  If the user defines ``data Json`` with different constructors,
    we must skip injecting the combinators to avoid type errors.
    """
    _EXPECTED = {"JNull", "JBool", "JNumber", "JString", "JArray", "JObject"}
    for tld in program.declarations:
        decl = tld.decl
        if isinstance(decl, ast.DataDecl) and decl.name == "Json":
            ctor_names = {c.name for c in decl.constructors}
            return ctor_names == _EXPECTED
    return False  # pragma: no cover


def _user_defined_names(program: ast.Program) -> set[str]:
    """Collect all user-defined function and type alias names."""
    names: set[str] = set()
    for tld in program.declarations:
        decl = tld.decl
        if isinstance(decl, ast.FnDecl):
            names.add(decl.name)
        elif isinstance(decl, ast.TypeAliasDecl):
            names.add(decl.name)
    return names


def _source_mentions_json(program: ast.Program) -> bool:
    """Check if user code references Json types or constructors.

    Walks all declarations (not just FnDecl) looking for Json-related
    AST nodes in parameters, return types, and bodies (via recursive
    field scan).  This catches modules that use Json values imported
    from other modules or received as parameters.
    """
    json_names = frozenset({
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
    for tld in program.declarations:
        decl = tld.decl
        if _node_mentions(decl, json_names):
            return True
    return False


def _source_mentions_html(program: ast.Program) -> bool:
    """Check if user code references HtmlNode types or constructors."""
    html_names = frozenset({
        "HtmlNode", "HtmlElement", "HtmlText", "HtmlComment",
        "html_parse", "html_to_string", "html_query", "html_text",
        "html_attr",
    })
    for tld in program.declarations:
        decl = tld.decl
        if _node_mentions(decl, html_names):
            return True
    return False


def _source_mentions_http_server(program: ast.Program) -> bool:
    """Check if user code references the HttpServer handler types (#305)."""
    names = frozenset({"Request", "Response", "HttpServer"})
    for tld in program.declarations:
        decl = tld.decl
        if _node_mentions(decl, names):
            return True
    return False


def _has_standard_html(program: ast.Program) -> bool:
    """Check if user's ``data HtmlNode`` has the expected 3 constructors."""
    _EXPECTED = {"HtmlElement", "HtmlText", "HtmlComment"}
    for tld in program.declarations:
        decl = tld.decl
        if isinstance(decl, ast.DataDecl) and decl.name == "HtmlNode":
            ctor_names = {c.name for c in decl.constructors}
            return ctor_names == _EXPECTED
    return False  # pragma: no cover


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


def _user_defined_data_names(program: ast.Program) -> set[str]:
    """Collect all user-defined data type names."""
    names: set[str] = set()
    for tld in program.declarations:
        decl = tld.decl
        if isinstance(decl, ast.DataDecl):
            names.add(decl.name)
    return names


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

    Two consumers, one derivation: :func:`prelude_adt_names` (codegen's
    ADT-membership floor) and codegen's Pass-1.2 contention rail, which
    compares a module's declaration of one of these names against the
    prelude's own with :func:`data_decl_shape`.

    READ-ONLY, because the cache hands every caller the same object: a
    plain dict would let one consumer's mutation reach the other and
    every later compile in the process, and the AST nodes inside it are
    the ones the rail compares against.  The proxy makes the shared
    identity safe rather than merely undocumented.
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
    it where the checker does not.  Whether the name is CONTENDED is a
    third question, asked by codegen's Pass-1.2 rail on the declarations
    themselves — see ``_adt_members_in_scope`` for why naming an
    undemanded ADT here is inert (a property of today's consumer, not of
    the set) and why the contended case is refused rather than resolved.
    Cached like :func:`prelude_data_decls` beneath it, and for the same
    reason: the blocks are constants, so the answer is too.  Its consumer
    is ``_adt_members_in_scope``, which runs once per namespace, and
    rebuilding an identical frozenset per namespace bought nothing.
    """
    return frozenset(prelude_data_decls())


def data_decl_shape(
    decl: ast.DataDecl,
    aliases: Mapping[str, ast.TypeExpr] | None = None,
    alias_params: Mapping[str, tuple[str, ...]] | None = None,
) -> tuple[object, ...]:
    """*decl*'s LAYOUT identity — what two declarations must share (#1277).

    Two ``data`` declarations of one name can occupy codegen's single
    flat layout slot only if they describe the same layout, which is
    the type-parameter arity plus each constructor's name, tag position
    and field types.  Type parameters are normalised POSITIONALLY, so
    ``data Option<A> { None, Some(A) }`` is the prelude's ``Option`` and
    not a contention: a renamed parameter changes no layout.

    Constructor ORDER is significant, because the tag is the position —
    which is why this is a stronger test than the set comparison
    :func:`_has_standard_json` and its siblings make when deciding
    whether the prelude's combinators can be injected over a user's
    declaration.  Those answer "will the match arms type-check?"; this
    answers "can one registered layout serve both?".

    A field type this does not model reduces to its node class, which
    can only ever make two declarations compare DIFFERENT — the prelude's
    own fields are all named types, so the coarse arm is never on both
    sides of a comparison.  Different is the safe direction: it refuses
    a compile rather than sharing a layout that may not fit.

    *aliases* / *alias_params* canonicalize the field types first, and
    belong to the namespace THIS declaration was written in — a module's
    own alias maps for a module's declaration (§8.4.1 makes an alias
    module-local, so no other namespace's may answer here; #1111/#1253).
    Passing them for one side only is deliberate: a module that spells a
    restatement through its own alias (`type Payload = String;`) means
    the prelude's type and must not be refused, while resolving the
    PRELUDE's spelling through a module's aliases would let a module
    alias named after something the prelude spells — `type Array<T> =
    Int;` against the prelude's `JArray(Array<Json>)` — collapse two
    incompatible layouts into one key.  The prelude's declaration
    resolves through nothing, because the prelude is its own namespace.

    A type PARAMETER shadows an alias of the same name (`_resolve_named`'s
    branch order), so the declaration's own parameters are withheld from
    the map before substitution.
    """
    slots = {
        name: f"#{i}" for i, name in enumerate(decl.type_params or ())
    }
    if aliases:
        visible = {k: v for k, v in aliases.items() if k not in slots}
        params = {
            k: v for k, v in (alias_params or {}).items() if k not in slots
        }
        def key(te: ast.TypeExpr) -> str:
            return _type_shape_key(
                canonicalize_type_aliases(te, dict(visible), dict(params)),
                slots,
            )
    else:
        def key(te: ast.TypeExpr) -> str:
            return _type_shape_key(te, slots)
    return (
        len(decl.type_params or ()),
        tuple(
            (ctor.name, tuple(key(field) for field in (ctor.fields or ())))
            for ctor in decl.constructors
        ),
    )


def _type_shape_key(te: object, slots: dict[str, str]) -> str:
    """A deterministic key for a field type — see :func:`data_decl_shape`."""
    if isinstance(te, ast.NamedType):
        base = slots.get(te.name, te.name)
        args = te.type_args or ()
        if not args:
            return base
        inner = ",".join(_type_shape_key(a, slots) for a in args)
        return f"{base}<{inner}>"
    if isinstance(te, ast.FnType):
        params = ",".join(_type_shape_key(p, slots) for p in te.params)
        return f"fn({params})->{_type_shape_key(te.return_type, slots)}"
    if isinstance(te, ast.RefinementType):
        base = _type_shape_key(te.base_type, slots)
        return f"{{{base}|{ast.format_expr(te.predicate)}}}"
    return f"?{type(te).__name__}"


def inject_prelude(program: ast.Program) -> str:
    """Inject prelude ADTs, combinators, and array operations.

    Mutates ``program.declarations`` by prepending prelude declarations.
    Returns the concatenated prelude source buffer that the injected
    declarations' spans index into, so diagnostics about prelude code
    can quote the actual prelude line under the synthetic
    :data:`PRELUDE_FILE` origin instead of misattributing the span's
    line number to the user's file (#851).

    The prelude provides:

    - ``data Option<T>``, ``data Result<T, E>``, ``data Ordering``,
      ``data UrlParts`` — always injected unless the user defines a
      type with the same name (user definitions shadow the prelude).
    - Option combinators (``option_unwrap_or``, ``option_map``,
      ``option_and_then``) — injected unless the user defines a
      non-standard ``Option<T>`` or shadows the function names.
    - Result combinators (``result_unwrap_or``, ``result_map``) —
      injected unless the user defines a non-standard ``Result<T, E>``
      or shadows the function names.
    - The closure-parameter type aliases the injected combinators
      resolve through (``VeraOptionMapFn``, ``VeraArrayMapFn``, …) —
      injected exactly when those bodies are, and never skipped for a
      SHADOWING reason (the Option and Result blocks still ride their
      combinators' own conditions; the Array block has no combinator
      prerequisite and is appended unconditionally).  Their names are
      in the prelude's reserved ``Vera`` namespace (#869/#1184/#1221),
      which E154 keeps user programs out of, so nothing a user
      declares can re-type them and no user-written type expression
      resolves through them.  User code that wants a short name for a
      function type declares its own alias.
    - Array combinator bodies — none currently.  All three
      (``array_map``, ``array_filter``, ``array_fold``) are emitted
      as iterative WASM by codegen (#480).  ``_ARRAY_COMBINATORS`` is
      empty but still injected when non-empty and ``array_fn_names``
      isn't a subset of user names, so adding a future recursive
      helper stays a one-line change.
    """
    user_names = _user_defined_names(program)
    user_data_names = _user_defined_data_names(program)

    # Determine whether to inject Option/Result combinators.
    # If the user defines a standard Option/Result, combinators work.
    # If the user defines a non-standard variant, skip combinators.
    # If the user doesn't define them at all, the prelude provides both.
    user_has_option = "Option" in user_data_names
    user_has_result = "Result" in user_data_names
    inject_option_combinators = (
        not user_has_option or _has_standard_option(program)
    )
    inject_result_combinators = (
        not user_has_result or _has_standard_result(program)
    )

    # Build source text for all prelude declarations
    source_parts: list[str] = [_PRELUDE_DATA]

    option_fn_names = {"option_unwrap_or", "option_map", "option_and_then"}
    result_fn_names = {"result_unwrap_or", "result_map"}
    # array_map, array_filter, and array_fold are all built-ins
    # emitted as iterative WASM (#480); none of them have prelude
    # bodies any more.  The set stays explicit (rather than becoming
    # an empty constant) so adding future array helpers that DO need
    # prelude injection is a one-line change.
    array_fn_names: set[str] = set()

    # The alias blocks ride the bodies that resolve through them — no
    # injection is ever skipped for SHADOWING, because their names are in
    # the reserved prelude namespace (#1221), which no user declaration may
    # take, so there is no shadowing case to skip an injection for.  The
    # combinator conditions below still apply: an absent alias is inert
    # when the bodies that would resolve through it are absent too.
    if (inject_option_combinators
            and not option_fn_names.issubset(user_names)):
        source_parts.append(_OPTION_TYPE_ALIASES)
        source_parts.append(_OPTION_COMBINATORS)

    if (inject_result_combinators
            and not result_fn_names.issubset(user_names)):
        source_parts.append(_RESULT_TYPE_ALIASES)
        source_parts.append(_RESULT_COMBINATORS)

    # Array operations — always inject the aliases (no ADT
    # prerequisites); inject the combinator bodies only when needed.
    # Decoupled after all three combinators migrated to iterative
    # WASM (#480): ``array_fn_names`` is empty so the combinator-
    # injection branch is a no-op for current programs.  When a future
    # array helper lands as a prelude function (not a built-in), just
    # add it to ``array_fn_names`` and populate ``_ARRAY_COMBINATORS``
    # — its parameter aliases are already injected here.
    source_parts.append(_ARRAY_TYPE_ALIASES)
    if _ARRAY_COMBINATORS and not array_fn_names.issubset(user_names):
        source_parts.append(_ARRAY_COMBINATORS)

    # Json ADT and utility functions — inject only when Json is referenced
    # (Json ADT triggers heap allocation; utilities call map_get etc.)
    json_fn_names = {
        "json_get", "json_array_get", "json_array_length",
        "json_keys", "json_has_field", "json_type",
        # #366 — typed accessors and compound field accessors
        "json_as_string", "json_as_number", "json_as_bool", "json_as_int",
        "json_as_array", "json_as_object",
        "json_get_string", "json_get_number", "json_get_bool",
        "json_get_int", "json_get_array",
    }
    _json_ctors = {"JNull", "JBool", "JNumber", "JString", "JArray", "JObject"}
    _json_builtins = {"json_parse", "json_stringify"}
    user_uses_json = bool(
        (user_names & json_fn_names)
        or (user_names & _json_ctors)
        or (user_names & _json_builtins)
        or _source_mentions_json(program)
    )
    if user_uses_json:
        user_has_json = "Json" in user_data_names
        if not user_has_json:
            source_parts.append(_JSON_DATA)
        # Only inject combinators when the Json ADT has standard
        # constructors (JNull, JBool, etc.).  A user-defined
        # non-standard ``data Json`` would break the match arms.
        inject_json_combinators = (
            not user_has_json or _has_standard_json(program)
        )
        if inject_json_combinators and not json_fn_names.issubset(user_names):
            source_parts.append(_JSON_COMBINATORS)

    # HtmlNode ADT and html_attr — inject only when HtmlNode is referenced
    html_fn_names = {"html_attr"}
    _html_ctors = {"HtmlElement", "HtmlText", "HtmlComment"}
    _html_builtins = {
        "html_parse", "html_to_string", "html_query", "html_text",
    }
    user_uses_html = bool(
        (user_names & html_fn_names)
        or (user_names & _html_ctors)
        or (user_names & _html_builtins)
        or _source_mentions_html(program)
    )
    if user_uses_html:
        user_has_html = "HtmlNode" in user_data_names
        if not user_has_html:
            source_parts.append(_HTML_DATA)
        inject_html_combinators = (
            not user_has_html or _has_standard_html(program)
        )
        if inject_html_combinators and not html_fn_names.issubset(user_names):
            source_parts.append(_HTML_COMBINATORS)

    # HttpServer handler types (#305) — inject only when referenced;
    # a user-defined data Request / data Response shadows the prelude
    # (the extraction loop below skips user-defined names).
    if _source_mentions_http_server(program):
        if not {"Request", "Response"} <= user_data_names:
            source_parts.append(_HTTP_SERVER_DATA)

    full_source = "\n".join(source_parts)
    parsed = _parse_source(full_source)

    # Extract declarations, skipping those the user already defined.
    new_decls: list[ast.TopLevelDecl] = []
    for tld in parsed.declarations:
        decl = tld.decl
        if isinstance(decl, ast.DataDecl):
            if decl.name in user_data_names:
                continue  # User's data type shadows the prelude's
        elif isinstance(decl, ast.FnDecl):
            if decl.name in user_names:
                continue  # User shadowed this function
        elif isinstance(decl, ast.TypeAliasDecl):
            if decl.name in user_names:
                # User shadowed this type alias.  Only the user-facing
                # names are reachable here: the reserved twins the
                # combinators resolve through are not spellable by an
                # ordinary declaration (#1184).
                continue
        new_decls.append(ast.TopLevelDecl(
            visibility="private",
            decl=decl,
            span=None,
        ))

    if not new_decls:  # pragma: no cover
        return full_source

    # Prepend to declarations so user defs shadow during registration.
    # Program is a frozen dataclass, so we use object.__setattr__.
    object.__setattr__(
        program,
        "declarations",
        tuple(new_decls) + program.declarations,
    )
    return full_source
