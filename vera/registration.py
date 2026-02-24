"""Shared registration logic for checker and verifier.

Both the type checker and contract verifier need a registration pass to
populate the TypeEnv with function signatures before their main analysis.
This module extracts that shared logic to avoid duplication.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Callable

from vera import ast
from vera.environment import FunctionInfo, TypeEnv
from vera.types import EffectRowType, Type, TypeVar

if TYPE_CHECKING:
    pass


def register_fn(
    env: TypeEnv,
    decl: ast.FnDecl,
    resolve_type: Callable[[ast.TypeExpr], Type],
    resolve_effect_row: Callable[[ast.EffectRow], EffectRowType],
) -> None:
    """Register a function signature in the environment.

    Resolves type parameters, parameter types, return type, and effect
    row using the provided callbacks, then stores the FunctionInfo.
    Recursively registers where-block functions.
    """
    saved_params = dict(env.type_params)
    if decl.forall_vars:
        for tv in decl.forall_vars:
            env.type_params[tv] = TypeVar(tv)

    param_types = tuple(resolve_type(p) for p in decl.params)
    ret_type = resolve_type(decl.return_type)
    eff = resolve_effect_row(decl.effect)

    env.functions[decl.name] = FunctionInfo(
        name=decl.name,
        forall_vars=decl.forall_vars,
        param_types=param_types,
        return_type=ret_type,
        effect=eff,
        span=decl.span,
        contracts=decl.contracts,
        param_type_exprs=decl.params,
    )

    if decl.where_fns:
        for wfn in decl.where_fns:
            register_fn(env, wfn, resolve_type, resolve_effect_row)

    env.type_params = saved_params
