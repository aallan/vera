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

from vera import ast


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

_JSON_DATA = """\
data Json { JNull, JBool(Bool), JNumber(Float64), JString(String), JArray(Array<Json>), JObject(Map<String, Json>) }
"""

_HTML_DATA = """\
data HtmlNode { HtmlElement(String, Map<String, String>, Array<HtmlNode>), HtmlText(String), HtmlComment(String) }
"""

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
_OPTION_TYPE_ALIASES = """\
type OptionMapFn<A, B> = fn(A -> B) effects(pure);
type OptionBindFn<A, B> = fn(A -> Option<B>) effects(pure);
"""

_RESULT_TYPE_ALIASES = """\
type ResultMapFn<A, B> = fn(A -> B) effects(pure);
"""

_ARRAY_TYPE_ALIASES = """\
type ArrayMapFn<A, B> = fn(A -> B) effects(pure);
type ArrayFilterFn<T> = fn(T -> Bool) effects(pure);
type ArrayFoldFn<T, U> = fn(U, T -> U) effects(pure);
"""

# Array higher-order operations.
# array_map is emitted as an iterative WASM loop by codegen (#480) —
# removed from this prelude injection.  array_filter and array_fold
# still use recursive helpers with an index parameter to walk the
# array; they will migrate to iterative implementations in follow-up
# PRs.  De Bruijn slot references are commented for clarity.
_ARRAY_COMBINATORS = """\
private forall<T> fn array_filter_go(@Array<T>, @ArrayFilterFn<T>, @Int, @Array<T> -> @Array<T>)
  requires(true)
  ensures(true)
  decreases(array_length(@Array<T>.1) - @Int.0)
  effects(pure)
{
  -- @Array<T>.0 = acc (most recent), @Int.0 = index,
  -- @ArrayFilterFn<T>.0 = predicate, @Array<T>.1 = input
  if @Int.0 >= array_length(@Array<T>.1) then {
    @Array<T>.0
  } else {
    if apply_fn(@ArrayFilterFn<T>.0, @Array<T>.1[@Int.0]) then {
      array_filter_go(
        @Array<T>.1,
        @ArrayFilterFn<T>.0,
        @Int.0 + 1,
        array_append(@Array<T>.0, @Array<T>.1[@Int.0])
      )
    } else {
      array_filter_go(
        @Array<T>.1,
        @ArrayFilterFn<T>.0,
        @Int.0 + 1,
        @Array<T>.0
      )
    }
  }
}

private forall<T> fn array_filter(@Array<T>, @ArrayFilterFn<T> -> @Array<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  -- @ArrayFilterFn<T>.0 = predicate (most recent), @Array<T>.0 = input
  array_filter_go(@Array<T>.0, @ArrayFilterFn<T>.0, 0, [])
}

private forall<T, U> fn array_fold_go(@Array<T>, @U, @ArrayFoldFn<T, U>, @Int -> @U)
  requires(true)
  ensures(true)
  decreases(array_length(@Array<T>.0) - @Int.0)
  effects(pure)
{
  -- @Int.0 = index (most recent), @ArrayFoldFn<T, U>.0 = fn,
  -- @U.0 = accumulator, @Array<T>.0 = input
  if @Int.0 >= array_length(@Array<T>.0) then {
    @U.0
  } else {
    array_fold_go(
      @Array<T>.0,
      apply_fn(@ArrayFoldFn<T, U>.0, @U.0, @Array<T>.0[@Int.0]),
      @ArrayFoldFn<T, U>.0,
      @Int.0 + 1
    )
  }
}

private forall<T, U> fn array_fold(@Array<T>, @U, @ArrayFoldFn<T, U> -> @U)
  requires(true)
  ensures(true)
  effects(pure)
{
  -- @ArrayFoldFn<T, U>.0 = fn (most recent), @U.0 = init,
  -- @Array<T>.0 = input
  array_fold_go(@Array<T>.0, @U.0, @ArrayFoldFn<T, U>.0, 0)
}
"""

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
"""

_OPTION_COMBINATORS = """\
private forall<T> fn option_unwrap_or(@Option<T>, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<T>.0 {
    None -> @T.0,
    Some(@T) -> @T.0
  }
}

private forall<A, B> fn option_map(@Option<A>, @OptionMapFn<A, B> -> @Option<B>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<A>.0 {
    None -> None,
    Some(@A) -> Some(apply_fn(@OptionMapFn<A, B>.0, @A.0))
  }
}

private forall<A, B> fn option_and_then(@Option<A>, @OptionBindFn<A, B> -> @Option<B>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<A>.0 {
    None -> None,
    Some(@A) -> apply_fn(@OptionBindFn<A, B>.0, @A.0)
  }
}
"""

_RESULT_COMBINATORS = """\
private forall<T, E> fn result_unwrap_or(@Result<T, E>, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Result<T, E>.0 {
    Ok(@T) -> @T.0,
    Err(@E) -> @T.0
  }
}

private forall<A, B, E> fn result_map(@Result<A, E>, @ResultMapFn<A, B> -> @Result<B, E>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Result<A, E>.0 {
    Ok(@A) -> Ok(apply_fn(@ResultMapFn<A, B>.0, @A.0)),
    Err(@E) -> Err(@E.0)
  }
}
"""


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
            names.add(decl.name)  # pragma: no cover
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

def inject_prelude(program: ast.Program) -> None:
    """Inject prelude ADTs, combinators, and array operations.

    Mutates ``program.declarations`` by prepending prelude declarations.
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
    - Array operations (``array_filter``, ``array_fold``) — always
      injected as recursive helpers until their own iterative
      migration lands.  ``array_map`` is emitted as iterative WASM
      by codegen (#480) and has no prelude body.
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
    option_alias_names = {"OptionMapFn", "OptionBindFn"}
    result_fn_names = {"result_unwrap_or", "result_map"}
    result_alias_names = {"ResultMapFn"}
    # array_map is a built-in emitted as iterative WASM (#480); it has
    # no prelude body any more.  array_filter / array_fold are still
    # injected as recursive helpers until their own iterative migration
    # lands.
    array_fn_names = {
        "array_filter", "array_filter_go",
        "array_fold", "array_fold_go",
    }
    array_alias_names = {"ArrayMapFn", "ArrayFilterFn", "ArrayFoldFn"}

    if (inject_option_combinators
            and not option_fn_names.issubset(user_names)):
        need_aliases = not (
            {"option_map", "option_and_then"}.issubset(user_names)
        )
        if need_aliases and not option_alias_names.issubset(user_names):
            source_parts.append(_OPTION_TYPE_ALIASES)
        source_parts.append(_OPTION_COMBINATORS)

    if (inject_result_combinators
            and not result_fn_names.issubset(user_names)):
        need_aliases = "result_map" not in user_names
        if need_aliases and not result_alias_names.issubset(user_names):
            source_parts.append(_RESULT_TYPE_ALIASES)
        source_parts.append(_RESULT_COMBINATORS)

    # Array operations — always inject (no ADT prerequisites)
    if not array_fn_names.issubset(user_names):
        if not array_alias_names.issubset(user_names):
            source_parts.append(_ARRAY_TYPE_ALIASES)
        source_parts.append(_ARRAY_COMBINATORS)

    # Json ADT and utility functions — inject only when Json is referenced
    # (Json ADT triggers heap allocation; utilities call map_get etc.)
    json_fn_names = {
        "json_get", "json_array_get", "json_array_length",
        "json_keys", "json_has_field", "json_type",
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
            if decl.name in user_names:  # pragma: no cover
                continue  # User shadowed this type alias
        new_decls.append(ast.TopLevelDecl(
            visibility="private",
            decl=decl,
            span=None,
        ))

    if not new_decls:  # pragma: no cover
        return

    # Prepend to declarations so user defs shadow during registration.
    # Program is a frozen dataclass, so we use object.__setattr__.
    object.__setattr__(
        program,
        "declarations",
        tuple(new_decls) + program.declarations,
    )
