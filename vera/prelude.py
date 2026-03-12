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
    """Inject Option/Result combinator declarations into a program.

    Mutates ``program.declarations`` by prepending combinator
    function declarations and their type aliases.  Only injects
    combinators whose ADT prerequisites are met and whose names
    don't collide with user definitions.
    """
    user_names = _user_defined_names(program)
    inject_option = _has_standard_option(program)
    inject_result = _has_standard_result(program)

    if not inject_option and not inject_result:
        return

    # Build source for what we need to inject
    source_parts: list[str] = []

    option_fn_names = {"option_unwrap_or", "option_map", "option_and_then"}
    option_alias_names = {"OptionMapFn", "OptionBindFn"}
    result_fn_names = {"result_unwrap_or", "result_map"}
    result_alias_names = {"ResultMapFn"}

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
