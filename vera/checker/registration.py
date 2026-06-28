"""Pass 1 registration mixin — forward-declares all top-level names."""

from __future__ import annotations

import functools

from vera import ast
from vera.environment import (
    AbilityInfo,
    AdtInfo,
    ConstructorInfo,
    EffectInfo,
    OpInfo,
    TypeAliasInfo,
)
from vera.types import TypeVar


@functools.lru_cache(maxsize=1)
def _builtin_reject_names() -> frozenset[str]:
    """Built-in function names a user/module ``fn`` must not redefine (E151).

    The full built-in registry minus the prelude-injected combinators, which
    the prelude lets the user override soundly (see
    :func:`vera.prelude.overridable_builtin_names`).  Cached: the built-in
    set is static.  Drives the #815 "one canonical form" check — redefining
    an opaque, verifier-modelled built-in (``abs`` / ``min`` / ``max`` / …)
    is the silent verifier↔runtime unsoundness that motivates the error.
    """
    from vera.environment import TypeEnv
    from vera.prelude import overridable_builtin_names

    return frozenset(TypeEnv().functions) - overridable_builtin_names()


class RegistrationMixin:
    """Methods that register top-level declarations into the type environment."""

    def _register_all(self, program: ast.Program) -> None:
        """Register all top-level declarations (forward reference support)."""
        for tld in program.declarations:
            # C7c: require explicit visibility on fn/data declarations
            if (tld.visibility is None
                    and isinstance(tld.decl, (ast.FnDecl, ast.DataDecl))):
                name = tld.decl.name
                kind = "fn" if isinstance(tld.decl, ast.FnDecl) else "data"
                self._error(
                    tld.decl,
                    f"Missing visibility on '{name}'. "
                    f"Add 'public' or 'private' before '{kind}'.",
                    rationale=(
                        "Every top-level function and data type must have "
                        "an explicit visibility annotation."
                    ),
                    fix=f"private {kind} {name}(...) or public {kind} {name}(...)",
                    spec_ref='Chapter 8, Section 8.4 "Visibility"',
                )
            # #815: redefining a built-in is a one-canonical-form violation
            # (and a silent verifier↔runtime unsoundness for the
            # verifier-modelled built-ins).  Covers top-level and module
            # functions and their where-helpers; prelude combinators exempt.
            if isinstance(tld.decl, ast.FnDecl):
                self._check_builtin_redefinition(tld.decl)
            self._register_decl(tld.decl, visibility=tld.visibility)

        # Post-registration cycle detection on type aliases (#648).
        # `_register_alias` resolves each alias's target one at a time;
        # when `type A = B` is processed before `B` is registered, the
        # forward-ref fallback in `_resolve_type` returns a placeholder
        # rather than chasing the chain, so `A = B; B = A` reaches the
        # post-loop state with no observable cycle in the resolved
        # types.  Codegen later stores the raw AST `type_expr` and
        # `_type_expr_to_wasm_type` chases the chain through the AST,
        # producing a `RecursionError` instead of a clean diagnostic.
        # Fix: walk the alias chain in the AST after all aliases have
        # registered, emit `[E132]` for any cycle we find.
        self._check_alias_cycles(program)

    def _check_builtin_redefinition(self, decl: ast.FnDecl) -> None:
        """Emit E151 if ``decl`` (or a nested where-helper) redefines a
        built-in (#815).

        Recurses into ``where_fns`` so a helper named after a built-in is
        caught too — otherwise the verifier models the call with the
        built-in's idealized model while codegen runs the where-body, the
        exact verify-proves / run-violates desync one scope deeper.  The
        prelude-injected combinators are exempt (see
        :func:`_builtin_reject_names`).
        """
        if decl.name in _builtin_reject_names():
            bn = decl.name
            self._error(
                decl,
                f"Function '{bn}' redefines a built-in.",
                rationale=(
                    f"'{bn}' is a built-in function (spec §9.6) — it is "
                    f"always in scope as the single canonical '{bn}'. "
                    f"Vera provides exactly one way to express each "
                    f"operation, so re-declaring a built-in is not "
                    f"allowed: there is nothing to gain by rolling your "
                    f"own, and a second definition is a second way to say "
                    f"the same thing. For the verifier-modelled built-ins "
                    f"it is also silently unsound — the verifier reasons "
                    f"about every call using the built-in's model while "
                    f"codegen runs your body, so a postcondition can be "
                    f"proved against the built-in yet violated at runtime "
                    f"by your version."
                ),
                fix=(
                    f"Delete this definition and call the built-in '{bn}' "
                    f"directly — it needs no import. If you intend "
                    f"genuinely different behaviour, give the function a "
                    f"distinct name (e.g. '{bn}_custom')."
                ),
                spec_ref='Chapter 9, Section 9.6 "Built-in Functions"',
                error_code="E151",
            )
        for wfn in decl.where_fns or ():
            self._check_builtin_redefinition(wfn)

    def _check_alias_cycles(self, program: ast.Program) -> None:
        """Detect cyclic type aliases and emit `[E132]`.

        Walks the alias-target chain following the same recursion
        the codegen helper `_type_expr_to_wasm_type` follows: into
        `RefinementType.base_type` (no shape change) and across
        `NamedType` references that name another alias.  Other
        constructors (`Array<T>`, `FnType`, `(A, B)`) terminate the
        walk because `_type_expr_to_wasm_type` returns a concrete
        WASM type at those nodes without recursing into their
        children — so cycles that pass *through* them are not the
        ones that trip codegen.
        """
        alias_decls: dict[str, ast.TypeAliasDecl] = {}
        for tld in program.declarations:
            if isinstance(tld.decl, ast.TypeAliasDecl):
                alias_decls.setdefault(tld.decl.name, tld.decl)

        walked: set[str] = set()
        for name, decl in alias_decls.items():
            if name in walked:
                continue
            seen = {name}
            chain = [name]
            te = decl.type_expr
            while True:
                target = self._alias_chain_target(te, alias_decls)
                if target is None:
                    break
                if target in seen:
                    cycle = " -> ".join(chain + [target])
                    self._error(
                        decl,
                        f"Cyclic type alias `{name}`: {cycle}.",
                        rationale=(
                            "Type aliases must eventually resolve to a "
                            "concrete type.  A cycle leaves the alias "
                            "with no underlying representation and "
                            "would crash codegen with unbounded "
                            "recursion."
                        ),
                        fix=(
                            "Replace one alias in the cycle with a "
                            "concrete type, or with an `ADT` declared "
                            "via `data` (which can be self-referential "
                            "because the indirection is a heap "
                            "pointer)."
                        ),
                        spec_ref='Chapter 4, Section 4.3 "Type Aliases"',
                        error_code="E132",
                    )
                    break
                seen.add(target)
                chain.append(target)
                te = alias_decls[target].type_expr
            walked.update(seen)

    @staticmethod
    def _alias_chain_target(
        te: ast.TypeExpr, aliases: dict[str, ast.TypeAliasDecl],
    ) -> str | None:
        """If `te` would cause codegen's alias walker to recurse into
        another alias, return that alias's name.  Else None.

        Mirrors the recursion shape of
        `vera/codegen/core.py::_type_expr_to_wasm_type`: peels
        `RefinementType` layers (which the codegen helper recurses
        through unconditionally) and stops at the first non-alias
        constructor or non-aliased `NamedType`.
        """
        while isinstance(te, ast.RefinementType):
            te = te.base_type
        if isinstance(te, ast.NamedType) and te.name in aliases:
            return te.name
        return None

    def _register_decl(
        self, decl: ast.Decl, visibility: str | None = None,
    ) -> None:
        """Register a single declaration's signature."""
        if isinstance(decl, ast.DataDecl):
            self._register_data(decl, visibility=visibility)
        elif isinstance(decl, ast.TypeAliasDecl):
            self._register_alias(decl)
        elif isinstance(decl, ast.EffectDecl):
            self._register_effect(decl)
        elif isinstance(decl, ast.FnDecl):
            self._register_fn(decl, visibility=visibility)
        elif isinstance(decl, ast.AbilityDecl):
            self._register_ability(decl)

    def _register_data(
        self, decl: ast.DataDecl, visibility: str | None = None,
    ) -> None:
        """Register an ADT and its constructors."""
        # Set up type params for resolving constructor field types
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ctors: dict[str, ConstructorInfo] = {}
        for ctor in decl.constructors:
            field_types = None
            if ctor.fields is not None:
                field_types = tuple(
                    self._resolve_type(f) for f in ctor.fields)
            ci = ConstructorInfo(
                name=ctor.name,
                parent_type=decl.name,
                parent_type_params=decl.type_params,
                field_types=field_types,
            )
            ctors[ctor.name] = ci
            self.env.constructors[ctor.name] = ci

        self.env.data_types[decl.name] = AdtInfo(
            name=decl.name,
            type_params=decl.type_params,
            constructors=ctors,
            visibility=visibility,
        )

        self.env.type_params = saved_params

    def _register_alias(self, decl: ast.TypeAliasDecl) -> None:
        """Register a type alias."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        resolved = self._resolve_type(decl.type_expr)
        self.env.type_aliases[decl.name] = TypeAliasInfo(
            name=decl.name,
            type_params=decl.type_params,
            resolved_type=resolved,
        )

        self.env.type_params = saved_params

    def _register_effect(self, decl: ast.EffectDecl) -> None:
        """Register an effect and its operations."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ops: dict[str, OpInfo] = {}
        for op in decl.operations:
            param_types = tuple(self._resolve_type(p) for p in op.param_types)
            ret_type = self._resolve_type(op.return_type)
            ops[op.name] = OpInfo(
                name=op.name,
                param_types=param_types,
                return_type=ret_type,
                parent_effect=decl.name,
            )

        self.env.effects[decl.name] = EffectInfo(
            name=decl.name,
            type_params=decl.type_params,
            operations=ops,
        )

        self.env.type_params = saved_params

    def _register_ability(self, decl: ast.AbilityDecl) -> None:
        """Register an ability and its operations."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ops: dict[str, OpInfo] = {}
        for op in decl.operations:
            param_types = tuple(
                self._resolve_type(p) for p in op.param_types)
            ret_type = self._resolve_type(op.return_type)
            ops[op.name] = OpInfo(
                name=op.name,
                param_types=param_types,
                return_type=ret_type,
                parent_effect=decl.name,  # stores ability name
            )

        self.env.abilities[decl.name] = AbilityInfo(
            name=decl.name,
            type_params=decl.type_params,
            operations=ops,
        )

        self.env.type_params = saved_params

    def _register_fn(
        self, decl: ast.FnDecl, visibility: str | None = None,
    ) -> None:
        """Register a function signature."""
        from vera.registration import register_fn
        register_fn(
            self.env, decl,
            self._resolve_type, self._resolve_effect_row,
            visibility=visibility,
        )
