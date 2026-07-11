"""Shared registration logic for checker and verifier.

Both the type checker and contract verifier need a registration pass to
populate the TypeEnv with function signatures before their main analysis.
This module extracts that shared logic to avoid duplication.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Callable

from vera import ast
from vera.environment import FunctionInfo, TypeEnv
from vera.obligations.cache import walk_nodes
from vera.types import EffectRowType, Type, TypeVar

if TYPE_CHECKING:
    pass


def _forall_vars_read(decl: ast.FnDecl) -> frozenset[str]:
    """Which of ``decl``'s forall type-vars are READ via a `@T.n` slot anywhere
    that lowers to WASM — the *body* OR a `requires` / `ensures` contract clause.

    A `@T.n` ``SlotRef`` lowers to a `local.get` (#900): the body lowers to the
    function body, and a `requires` / `ensures` clause lowers to the *runtime*
    pre / post-condition check (`_compile_preconditions` /
    `_compile_postconditions`).  Once monomorphized at `T = Unit`, that local
    does not exist (Unit is zero-size, erased from the ABI), so the read dangles
    and codegen crashes — a raw traceback on a `check`-green program (#900 for
    the body; #939 for the contract clauses, whose reads the original body-only
    walk missed).  A `@T` parameter that is never read — in the body or a
    contract — erases cleanly and runs fine, so it must not trip E206.

    Only `requires` / `ensures` are walked among the contracts: a `decreases` /
    `invariant` clause is verifier-only and never emits a `local.get`, so a
    `@T` read there does not dangle at Unit and must NOT be counted (that would
    over-reject a program that compiles fine).  ``where``-helpers are registered
    separately with their own forall scope.
    """
    if not decl.forall_vars:
        return frozenset()
    fvars = set(decl.forall_vars)
    nodes = list(walk_nodes(decl.body))
    for contract in decl.contracts:
        if isinstance(contract, (ast.Requires, ast.Ensures)):
            nodes.extend(walk_nodes(contract.expr))
    return frozenset(
        n.type_name
        for n in nodes
        if isinstance(n, ast.SlotRef) and n.type_name in fvars
    )


def build_fn_info(
    env: TypeEnv,
    decl: ast.FnDecl,
    resolve_type: Callable[[ast.TypeExpr], Type],
    resolve_effect_row: Callable[[ast.EffectRow], EffectRowType],
    visibility: str | None = None,
) -> FunctionInfo:
    """Resolve ``decl``'s signature into a :class:`FunctionInfo` without storing
    it in ``env.functions``.

    Factored out of :func:`register_fn` so a caller that needs a *scoped* lookup
    (the verifier resolving a bare ``where``-helper call to the nearest same-named
    helper, #991) can construct the right helper's info on demand instead of
    reading the flat, last-wins registry.  ``decl``'s forall vars are bound into
    ``env.type_params`` for the duration of type resolution, then restored.
    """
    saved_params = dict(env.type_params)
    if decl.forall_vars:
        for tv in decl.forall_vars:
            env.type_params[tv] = TypeVar(tv)
    try:
        return FunctionInfo(
            name=decl.name,
            forall_vars=decl.forall_vars,
            param_types=tuple(resolve_type(p) for p in decl.params),
            return_type=resolve_type(decl.return_type),
            effect=resolve_effect_row(decl.effect),
            span=decl.span,
            contracts=decl.contracts,
            param_type_exprs=decl.params,
            visibility=visibility,
            forall_constraints=decl.forall_constraints or (),
            forall_vars_read=_forall_vars_read(decl),
        )
    finally:
        env.type_params = saved_params


def register_fn(
    env: TypeEnv,
    decl: ast.FnDecl,
    resolve_type: Callable[[ast.TypeExpr], Type],
    resolve_effect_row: Callable[[ast.EffectRow], EffectRowType],
    visibility: str | None = None,
) -> None:
    """Register a function signature in the environment.

    Resolves type parameters, parameter types, return type, and effect
    row using the provided callbacks, then stores the FunctionInfo.
    Recursively registers where-block functions.
    """
    # Bind this function's forall vars for the duration of BOTH its own
    # signature resolution AND its where-helper registration: a helper of a
    # generic parent is written over the parent's ``@T`` (spec §5), so it must
    # be registered with the parent's type params still in scope.  ``build_fn_info``
    # re-binds/restores the same names internally (a no-op net of our binding,
    # since ``TypeVar`` equality is by name), leaving our binding live for the
    # recursion below.
    saved_params = dict(env.type_params)
    if decl.forall_vars:
        for tv in decl.forall_vars:
            env.type_params[tv] = TypeVar(tv)

    env.functions[decl.name] = build_fn_info(
        env, decl, resolve_type, resolve_effect_row, visibility,
    )

    if decl.where_fns:
        for wfn in decl.where_fns:
            register_fn(env, wfn, resolve_type, resolve_effect_row)

    env.type_params = saved_params
