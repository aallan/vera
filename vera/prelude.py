"""Prelude injection for Option/Result combinators.

Defines combinator functions as Vera source text, parses them into
AST nodes, and injects them into a program's declarations before
type checking.  The normal pipeline (type checking, monomorphization,
codegen) then handles them like any user-defined function.

Injection is conditional:
- Option combinators require ``data Option<T> { None, Some(T) }``
  (or equivalent with swapped constructor order).
- Result combinators require ``data Result<T, E> { Ok(T), Err(E) }``
  (or equivalent with swapped constructor order).
- A combinator is skipped if the user already defined a function
  with the same name.
"""

from __future__ import annotations

from vera import ast


# =====================================================================
# Combinator Vera source
# =====================================================================

# Type aliases needed by closure-taking combinators.
# These are injected alongside the functions that reference them.
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
# These use recursive helpers with an index parameter to walk the array.
# De Bruijn slot references are commented for clarity.
_ARRAY_COMBINATORS = """\
private forall<A, B> fn array_map_go(@Array<A>, @ArrayMapFn<A, B>, @Int, @Array<B> -> @Array<B>)
  requires(true)
  ensures(true)
  decreases(array_length(@Array<A>.0) - @Int.0)
  effects(pure)
{
  -- @Array<B>.0 = acc (most recent), @Int.0 = index,
  -- @ArrayMapFn<A, B>.0 = fn, @Array<A>.0 = input
  if @Int.0 >= array_length(@Array<A>.0) then {
    @Array<B>.0
  } else {
    array_map_go(
      @Array<A>.0,
      @ArrayMapFn<A, B>.0,
      @Int.0 + 1,
      array_append(@Array<B>.0, apply_fn(@ArrayMapFn<A, B>.0, @Array<A>.0[@Int.0]))
    )
  }
}

private forall<A, B> fn array_map(@Array<A>, @ArrayMapFn<A, B> -> @Array<B>)
  requires(true)
  ensures(true)
  effects(pure)
{
  -- @ArrayMapFn<A, B>.0 = fn (most recent), @Array<A>.0 = input
  array_map_go(@Array<A>.0, @ArrayMapFn<A, B>.0, 0, [])
}

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

def _has_standard_option(program: ast.Program) -> bool:
    """Check if the program defines Option<T> with None and Some(T)."""
    for tld in program.declarations:
        decl = tld.decl
        if isinstance(decl, ast.DataDecl) and decl.name == "Option":
            if decl.type_params and len(decl.type_params) == 1:
                ctor_names = {c.name for c in decl.constructors}
                if "None" in ctor_names and "Some" in ctor_names:
                    return True
    return False


def _has_standard_result(program: ast.Program) -> bool:
    """Check if the program defines Result<T, E> with Ok(T) and Err(E)."""
    for tld in program.declarations:
        decl = tld.decl
        if isinstance(decl, ast.DataDecl) and decl.name == "Result":
            if decl.type_params and len(decl.type_params) == 2:
                ctor_names = {c.name for c in decl.constructors}
                if "Ok" in ctor_names and "Err" in ctor_names:
                    return True
    return False


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
    """Inject combinator and array operation declarations into a program.

    Mutates ``program.declarations`` by prepending combinator
    function declarations and their type aliases.  Only injects
    combinators whose ADT prerequisites are met and whose names
    don't collide with user definitions.

    Array operations (array_map, array_filter, array_fold) are
    always injected (they have no ADT prerequisites).
    """
    user_names = _user_defined_names(program)
    inject_option = _has_standard_option(program)
    inject_result = _has_standard_result(program)

    # Build source for what we need to inject
    source_parts: list[str] = []

    option_fn_names = {"option_unwrap_or", "option_map", "option_and_then"}
    option_alias_names = {"OptionMapFn", "OptionBindFn"}
    result_fn_names = {"result_unwrap_or", "result_map"}
    result_alias_names = {"ResultMapFn"}
    array_fn_names = {
        "array_map", "array_map_go",
        "array_filter", "array_filter_go",
        "array_fold", "array_fold_go",
    }
    array_alias_names = {"ArrayMapFn", "ArrayFilterFn", "ArrayFoldFn"}

    if inject_option and not option_fn_names.issubset(user_names):
        # Check which aliases are needed (only if closure fns are not shadowed)
        need_aliases = not (
            {"option_map", "option_and_then"}.issubset(user_names)
        )
        if need_aliases and not option_alias_names.issubset(user_names):
            source_parts.append(_OPTION_TYPE_ALIASES)
        source_parts.append(_OPTION_COMBINATORS)

    if inject_result and not result_fn_names.issubset(user_names):
        need_aliases = "result_map" not in user_names
        if need_aliases and not result_alias_names.issubset(user_names):
            source_parts.append(_RESULT_TYPE_ALIASES)
        source_parts.append(_RESULT_COMBINATORS)

    # Array operations — always inject (no ADT prerequisites)
    if not array_fn_names.issubset(user_names):
        if not array_alias_names.issubset(user_names):
            source_parts.append(_ARRAY_TYPE_ALIASES)
        source_parts.append(_ARRAY_COMBINATORS)

    if not source_parts:
        return

    # We need a minimal program wrapper with the data declarations
    # so the parser can resolve constructor references in the combinator
    # source.  Build a full source with data defs + combinators.
    data_defs: list[str] = []
    if inject_option:
        data_defs.append("data Option<T> { None, Some(T) }")
    if inject_result:
        data_defs.append("data Result<T, E> { Ok(T), Err(E) }")

    full_source = "\n".join(data_defs) + "\n" + "\n".join(source_parts)
    parsed = _parse_source(full_source)

    # Extract the FnDecl and TypeAliasDecl nodes (skip the data defs
    # since those are already in the user's program)
    new_decls: list[ast.TopLevelDecl] = []
    for tld in parsed.declarations:
        decl = tld.decl
        if isinstance(decl, ast.DataDecl):
            continue  # Skip — user already has these
        if isinstance(decl, ast.FnDecl) and decl.name in user_names:
            continue  # User shadowed this function
        if isinstance(decl, ast.TypeAliasDecl) and decl.name in user_names:
            continue  # User shadowed this type alias
        # Mark as private (defensive — source already says private)
        new_decls.append(ast.TopLevelDecl(
            visibility="private",
            decl=decl,
            span=None,
        ))

    if not new_decls:
        return

    # Prepend to declarations so user defs shadow during registration.
    # Program is a frozen dataclass, so we use object.__setattr__.
    object.__setattr__(
        program,
        "declarations",
        tuple(new_decls) + program.declarations,
    )
