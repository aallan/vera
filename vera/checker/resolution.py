"""Type resolution mixin — AST TypeExpr to semantic Type conversion.

Provides _resolve_type, _resolve_named_type, _resolve_effect_row,
_resolve_effect_ref, _slot_type_name, _infer_type_args, and
_unify_for_inference methods extracted from TypeChecker.
"""

from __future__ import annotations

from vera import ast
from vera.types import (
    PRIMITIVES,
    REMOVED_ALIASES,
    AdtType,
    ConcreteEffectRow,
    EffectInstance,
    EffectRowType,
    FunctionType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    canonical_type_name,
    contains_typevar,
    substitute,
)


class ResolutionMixin:
    """Methods for resolving AST type expressions into semantic types."""

    # -----------------------------------------------------------------
    # Type resolution: AST TypeExpr -> semantic Type
    # -----------------------------------------------------------------

    def _resolve_type(self, te: ast.TypeExpr) -> Type:
        """Convert an AST TypeExpr into a resolved semantic Type."""
        if isinstance(te, ast.NamedType):
            return self._resolve_named_type(te)
        if isinstance(te, ast.FnType):
            params = tuple(self._resolve_type(p) for p in te.params)
            ret = self._resolve_type(te.return_type)
            eff = self._resolve_effect_row(te.effect)
            return FunctionType(params, ret, eff)
        if isinstance(te, ast.RefinementType):
            base = self._resolve_type(te.base_type)
            return RefinedType(base, te.predicate)
        return UnknownType()

    def _resolve_named_type(self, te: ast.NamedType) -> Type:
        """Resolve a named type (possibly parameterised)."""
        name = te.name

        # Type variable?
        if name in self.env.type_params:
            return self.env.type_params[name]

        # Primitive?
        if name in PRIMITIVES and not te.type_args:
            return PRIMITIVES[name]

        # Type alias?
        alias = self.env.type_aliases.get(name)
        if alias:
            if te.type_args and alias.type_params:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                mapping = dict(zip(alias.type_params, args))
                return substitute(alias.resolved_type, mapping)
            return alias.resolved_type

        # ADT or parameterised built-in?
        adt = self.env.data_types.get(name)
        if adt is not None:
            if te.type_args:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                return AdtType(name, args)
            return AdtType(name, ())

        # Decimal is a non-parameterised built-in opaque type
        if name == "Decimal":
            if te.type_args:
                self._error(
                    te, "Decimal does not accept type arguments.",
                    error_code="E130",
                )
            return AdtType(name, ())

        # Array, Tuple, Map, Set (built-in parameterised types)
        if name in ("Array", "Tuple", "Map", "Set"):
            if te.type_args:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                return AdtType(name, args)
            return AdtType(name, ())

        # Removed alias? — produce a helpful "did you mean" error.
        canonical = REMOVED_ALIASES.get(name)
        if canonical is not None:
            if name not in self._reported_alias_errors:
                self._reported_alias_errors.add(name)
                self._error(
                    te,
                    f"'{name}' is not a type. Did you mean '{canonical}'?",
                    rationale=(f"'{name}' was removed; "
                               f"use '{canonical}' instead."),
                    fix=f"Replace '{name}' with '{canonical}'.",
                    spec_ref="Chapter 2 — Primitive Types",
                )
            return UnknownType()

        # Unknown — might be a type from an unresolved import
        return AdtType(name, tuple(
            self._resolve_type(a) for a in te.type_args
        ) if te.type_args else ())

    def _resolve_effect_row(self, er: ast.EffectRow) -> EffectRowType:
        """Convert an AST EffectRow into a semantic EffectRowType."""
        if isinstance(er, ast.PureEffect):
            return PureEffectRow()
        if isinstance(er, ast.EffectSet):
            instances = []
            row_var = None
            for ref in er.effects:
                if isinstance(ref, ast.EffectRef):
                    # Check if it's a type variable (effect polymorphism)
                    if ref.name in self.env.type_params:
                        row_var = ref.name
                        continue
                    args = tuple(
                        self._resolve_type(a) for a in ref.type_args
                    ) if ref.type_args else ()
                    instances.append(EffectInstance(ref.name, args))
                elif isinstance(ref, ast.QualifiedEffectRef):
                    args = tuple(
                        self._resolve_type(a) for a in ref.type_args
                    ) if ref.type_args else ()
                    instances.append(
                        EffectInstance(f"{ref.module}.{ref.name}", args))
            return ConcreteEffectRow(frozenset(instances), row_var)
        return PureEffectRow()

    def _resolve_effect_ref(self, ref: ast.EffectRefNode) -> EffectInstance | None:
        """Resolve a single effect reference."""
        if isinstance(ref, ast.EffectRef):
            args = tuple(
                self._resolve_type(a) for a in ref.type_args
            ) if ref.type_args else ()
            return EffectInstance(ref.name, args)
        if isinstance(ref, ast.QualifiedEffectRef):
            args = tuple(
                self._resolve_type(a) for a in ref.type_args
            ) if ref.type_args else ()
            return EffectInstance(f"{ref.module}.{ref.name}", args)
        return None

    # -----------------------------------------------------------------
    # Canonical type name for slot references
    # -----------------------------------------------------------------

    def _slot_type_name(self, type_name: str,
                        type_args: tuple[ast.TypeExpr, ...] | None) -> str:
        """Form the canonical type name for slot reference matching."""
        if not type_args:
            return type_name
        resolved = tuple(self._resolve_type(a) for a in type_args)
        return canonical_type_name(type_name, resolved)

    # -----------------------------------------------------------------
    # Type inference helpers
    # -----------------------------------------------------------------

    def _infer_type_args(self, forall_vars: tuple[str, ...],
                         param_types: tuple[Type, ...],
                         arg_types: list[Type | None]) -> dict[str, Type]:
        """Infer type variable bindings by matching args against params."""
        mapping: dict[str, Type] = {}
        forall_set = set(forall_vars)
        for param_ty, arg_ty in zip(param_types, arg_types):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            self._unify_for_inference(param_ty, arg_ty, mapping, forall_set)
        return mapping

    def _unify_for_inference(self, pattern: Type, concrete: Type,
                             mapping: dict[str, Type],
                             forall_vars: set[str] | None = None,
                             ) -> None:
        """Simple unification for type argument inference."""
        # Skip when the concrete type has TypeVars matching the callee's
        # own forall vars (e.g. map_new() returns Map<K, V> where K, V
        # are the callee's forall vars — not yet resolved from args).
        # Other TypeVars (e.g. E$6 from constructor inference, or U from
        # an enclosing forall scope) are fine to unify with.
        if (forall_vars
                and isinstance(concrete, AdtType)
                and concrete.type_args
                and any(isinstance(a, TypeVar) and a.name in forall_vars
                        for a in concrete.type_args)):
            return
        if isinstance(pattern, TypeVar):
            if pattern.name not in mapping:
                mapping[pattern.name] = concrete
            return

        if isinstance(pattern, AdtType) and isinstance(concrete, AdtType):
            if pattern.name == concrete.name:
                for p_arg, c_arg in zip(pattern.type_args, concrete.type_args):
                    self._unify_for_inference(
                        p_arg, c_arg, mapping, forall_vars)

        if isinstance(pattern, FunctionType) and isinstance(concrete, FunctionType):
            for p_param, c_param in zip(pattern.params, concrete.params):
                self._unify_for_inference(
                    p_param, c_param, mapping, forall_vars)
            self._unify_for_inference(
                pattern.return_type, concrete.return_type,
                mapping, forall_vars)
