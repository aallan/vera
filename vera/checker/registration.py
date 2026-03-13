"""Pass 1 registration mixin — forward-declares all top-level names."""

from __future__ import annotations

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
                    spec_ref='Chapter 5, Section 5.8 "Function Visibility"',
                )
            self._register_decl(tld.decl, visibility=tld.visibility)

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
