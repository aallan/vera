"""Mixin for generic function monomorphization (Pass 1.5).

Collects concrete instantiations of generic functions from call sites,
infers type variable bindings, and produces monomorphized FnDecl copies
with mangled names.  Also checks ability constraint satisfaction.
"""

from __future__ import annotations

from dataclasses import fields, replace
from typing import Any

from vera import ast

# Types that satisfy the built-in Eq ability.
_EQ_TYPES: frozenset[str] = frozenset({
    "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit",
})


class MonomorphizationMixin:
    """Methods for monomorphizing generic functions."""

    def _monomorphize(
        self, program: ast.Program,
    ) -> list[ast.FnDecl]:
        """Monomorphize generic functions for all concrete call sites.

        Returns a list of new FnDecl nodes with type variables replaced
        by concrete types and names mangled.
        """
        # Identify generic function declarations
        generic_decls: dict[str, ast.FnDecl] = {}
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and decl.forall_vars:
                generic_decls[decl.name] = decl

        if not generic_decls:
            return []

        # Build constructor → ADT name mapping
        ctor_to_adt: dict[str, str] = {}
        for adt_name in self._adt_layouts:
            for ctor_name in self._adt_layouts[adt_name]:
                ctor_to_adt[ctor_name] = adt_name

        # Collect concrete instantiations from non-generic function bodies
        instances: dict[str, set[tuple[str, ...]]] = {
            name: set() for name in generic_decls
        }
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and not decl.forall_vars:
                self._collect_calls_in_expr(
                    decl.body, generic_decls, ctor_to_adt, instances,
                )

        # Generate monomorphized FnDecls
        mono_decls: list[ast.FnDecl] = []
        for fn_name, type_arg_set in instances.items():
            for concrete_types in type_arg_set:
                decl = generic_decls[fn_name]
                if not self._check_constraints(decl, concrete_types):
                    continue  # constraint violation — error emitted
                mono = self._monomorphize_fn(decl, concrete_types)
                mono_decls.append(mono)

        # Store generic fn info for call rewriting in wasm.py
        self._generic_fn_info: dict[
            str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]
        ] = {}
        for name, decl in generic_decls.items():
            assert decl.forall_vars is not None
            self._generic_fn_info[name] = (decl.forall_vars, decl.params)

        return mono_decls

    def _collect_calls_in_expr(
        self,
        expr: ast.Expr,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
    ) -> None:
        """Walk an expression tree collecting generic call sites."""
        if isinstance(expr, ast.FnCall) and expr.name in generic_decls:
            decl = generic_decls[expr.name]
            type_args = self._infer_type_args_from_call(
                decl, expr, ctor_to_adt, generic_decls,
            )
            if type_args is not None:
                instances[expr.name].add(type_args)

        # Recurse into sub-expressions
        if isinstance(expr, ast.Block):
            for stmt in expr.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._collect_calls_in_expr(
                        stmt.value, generic_decls, ctor_to_adt, instances,
                    )
                elif isinstance(stmt, ast.ExprStmt):
                    self._collect_calls_in_expr(
                        stmt.expr, generic_decls, ctor_to_adt, instances,
                    )
            self._collect_calls_in_expr(
                expr.expr, generic_decls, ctor_to_adt, instances,
            )
        elif isinstance(expr, ast.BinaryExpr):
            self._collect_calls_in_expr(
                expr.left, generic_decls, ctor_to_adt, instances,
            )
            self._collect_calls_in_expr(
                expr.right, generic_decls, ctor_to_adt, instances,
            )
        elif isinstance(expr, ast.UnaryExpr):
            self._collect_calls_in_expr(
                expr.operand, generic_decls, ctor_to_adt, instances,
            )
        elif isinstance(expr, ast.IfExpr):
            self._collect_calls_in_expr(
                expr.condition, generic_decls, ctor_to_adt, instances,
            )
            self._collect_calls_in_expr(
                expr.then_branch, generic_decls, ctor_to_adt, instances,
            )
            self._collect_calls_in_expr(
                expr.else_branch, generic_decls, ctor_to_adt, instances,
            )
        elif isinstance(expr, ast.FnCall):
            for arg in expr.args:
                self._collect_calls_in_expr(
                    arg, generic_decls, ctor_to_adt, instances,
                )
        elif isinstance(expr, ast.ConstructorCall):
            for arg in expr.args:
                self._collect_calls_in_expr(
                    arg, generic_decls, ctor_to_adt, instances,
                )
        elif isinstance(expr, ast.MatchExpr):
            self._collect_calls_in_expr(
                expr.scrutinee, generic_decls, ctor_to_adt, instances,
            )
            for arm in expr.arms:
                self._collect_calls_in_expr(
                    arm.body, generic_decls, ctor_to_adt, instances,
                )
        elif isinstance(expr, ast.AnonFn):
            # Recurse into closure bodies for generic call collection
            self._collect_calls_in_expr(
                expr.body, generic_decls, ctor_to_adt, instances,
            )
        elif isinstance(expr, ast.ModuleCall):
            # C7e: recurse into ModuleCall args for generic call collection
            for arg in expr.args:
                self._collect_calls_in_expr(
                    arg, generic_decls, ctor_to_adt, instances,
                )

    def _infer_type_args_from_call(
        self,
        decl: ast.FnDecl,
        call: ast.FnCall,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> tuple[str, ...] | None:
        """Infer concrete type variable bindings from a call's arguments.

        Returns a tuple of concrete type names, one per forall_var, or
        None if inference fails.
        """
        forall_vars = decl.forall_vars
        if not forall_vars:
            return None

        mapping: dict[str, str] = {}
        for param_te, arg in zip(decl.params, call.args):
            self._unify_param_arg(param_te, arg, forall_vars, ctor_to_adt,
                                  mapping, generic_decls)

        # Check all type vars are resolved; default phantom vars to Unit
        result = []
        for tv in forall_vars:
            if tv not in mapping:
                # Phantom type variable (e.g. E in result_unwrap_or(Ok(x), d))
                # — the generated WASM is identical regardless of this type.
                # Use Bool (i32) rather than Unit (no WASM repr) so the
                # monomorphized body can still compile unused branches.
                mapping[tv] = "Bool"
            result.append(mapping[tv])
        return tuple(result)

    def _unify_param_arg(
        self,
        param_te: ast.TypeExpr,
        arg: ast.Expr,
        forall_vars: tuple[str, ...],
        ctor_to_adt: dict[str, str],
        mapping: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> None:
        """Unify a parameter TypeExpr against an argument to bind type vars."""
        if isinstance(param_te, ast.RefinementType):
            self._unify_param_arg(
                param_te.base_type, arg, forall_vars, ctor_to_adt, mapping,
                generic_decls,
            )
            return

        if not isinstance(param_te, ast.NamedType):
            return

        if param_te.name in forall_vars:
            # Direct type variable — infer from argument
            vera_type = self._infer_vera_type_name(
                arg, ctor_to_adt, generic_decls)
            if vera_type and param_te.name not in mapping:
                mapping[param_te.name] = vera_type
            return

        # Parameterized type like Option<T> — match type args
        if param_te.type_args:
            # Handle type alias for FnType matched against AnonFn arg
            if isinstance(arg, ast.AnonFn):
                alias_concrete = self._infer_fn_alias_type_args(
                    param_te, arg,
                )
                if alias_concrete is not None:
                    for param_ta, concrete_name in zip(
                        param_te.type_args, alias_concrete,
                    ):
                        if (isinstance(param_ta, ast.NamedType)
                                and param_ta.name in forall_vars
                                and param_ta.name not in mapping):
                            mapping[param_ta.name] = concrete_name
                    return

            arg_info = self._get_arg_type_info(arg, ctor_to_adt)
            if arg_info and arg_info[0] == param_te.name:
                for param_ta, arg_ta_name in zip(
                    param_te.type_args, arg_info[1]
                ):
                    if (isinstance(param_ta, ast.NamedType)
                            and param_ta.name in forall_vars
                            and param_ta.name not in mapping):
                        mapping[param_ta.name] = arg_ta_name

    def _infer_vera_type_name(
        self,
        expr: ast.Expr,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> str | None:
        """Infer the simple Vera type name of an expression."""
        if isinstance(expr, ast.IntLit):
            return "Int"
        if isinstance(expr, ast.BoolLit):
            return "Bool"
        if isinstance(expr, ast.FloatLit):
            return "Float64"
        if isinstance(expr, ast.UnitLit):
            return "Unit"
        if isinstance(expr, ast.SlotRef):
            return expr.type_name
        if isinstance(expr, ast.ConstructorCall):
            return ctor_to_adt.get(expr.name)
        if isinstance(expr, ast.NullaryConstructor):
            return ctor_to_adt.get(expr.name)
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in (ast.BinOp.EQ, ast.BinOp.NEQ, ast.BinOp.LT,
                           ast.BinOp.GT, ast.BinOp.LE, ast.BinOp.GE,
                           ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES):
                return "Bool"
            return self._infer_vera_type_name(
                expr.left, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.UnaryExpr):
            if expr.op == ast.UnaryOp.NOT:
                return "Bool"
            return self._infer_vera_type_name(
                expr.operand, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.IfExpr):
            return self._infer_vera_type_name(
                expr.then_branch.expr, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.FnCall) and generic_decls:
            return self._infer_fncall_vera_type(
                expr, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.FnCall):
            return self._infer_fncall_vera_type_simple(expr)
        return None

    def _infer_fncall_vera_type(
        self,
        call: ast.FnCall,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl],
    ) -> str | None:
        """Infer the Vera return type of a function call.

        For generic calls, infers type variable bindings from arguments,
        then substitutes into the return TypeExpr.
        """
        if call.name in generic_decls:
            decl = generic_decls[call.name]
            type_args = self._infer_type_args_from_call(
                decl, call, ctor_to_adt, generic_decls,
            )
            if type_args and decl.forall_vars:
                mapping = dict(zip(decl.forall_vars, type_args))
                ret_te = decl.return_type
                if isinstance(ret_te, ast.NamedType):
                    return mapping.get(ret_te.name, ret_te.name)
        return self._infer_fncall_vera_type_simple(call)

    def _infer_fncall_vera_type_simple(self, call: ast.FnCall) -> str | None:
        """Infer Vera return type from registered function signatures."""
        sig = self._fn_sigs.get(call.name)
        if sig:
            _, ret_wt = sig
            if ret_wt == "i64":
                return "Int"
            if ret_wt == "i32":
                return "Bool"
            if ret_wt == "f64":
                return "Float64"
        return None

    def _get_arg_type_info(
        self, expr: ast.Expr, ctor_to_adt: dict[str, str],
    ) -> tuple[str, tuple[str, ...]] | None:
        """Get (type_name, type_arg_names) for an argument expression.

        Used to match parameterized types like Option<T> against
        concrete arguments like @Option<Int>.0.
        """
        if isinstance(expr, ast.SlotRef):
            if expr.type_args:
                arg_names = []
                for ta in expr.type_args:
                    if isinstance(ta, ast.NamedType):
                        arg_names.append(ta.name)
                    else:
                        return None
                return (expr.type_name, tuple(arg_names))
            return (expr.type_name, ())
        if isinstance(expr, ast.ConstructorCall):
            adt_name = ctor_to_adt.get(expr.name)
            if adt_name:
                # Infer type args from constructor arguments
                arg_types = []
                for a in expr.args:
                    t = self._infer_vera_type_name(a, ctor_to_adt)
                    if t:
                        arg_types.append(t)
                    else:
                        return None
                return (adt_name, tuple(arg_types))
        return None

    def _infer_fn_alias_type_args(
        self,
        param_te: ast.NamedType,
        anon_fn: ast.AnonFn,
    ) -> tuple[str, ...] | None:
        """Infer concrete types for a type alias's params from an AnonFn.

        When ``param_te`` is e.g. ``NamedType("OptionMapFn", [A, B])``
        which aliases ``fn(A -> B)``, and the argument is an AnonFn
        with concrete param/return types, infer one concrete type name
        per alias type parameter.

        Returns a tuple of concrete type names aligned to the alias's
        type parameters, or None if inference fails.
        """
        type_aliases: dict[str, ast.TypeExpr] = getattr(
            self, "_type_aliases", {},
        )
        type_alias_params: dict[str, tuple[str, ...]] = getattr(
            self, "_type_alias_params", {},
        )

        alias_te = type_aliases.get(param_te.name)
        if not isinstance(alias_te, ast.FnType):
            return None

        alias_params = type_alias_params.get(param_te.name)
        if (
            not alias_params
            or not param_te.type_args
            or len(alias_params) != len(param_te.type_args)
        ):
            return None

        # Match the FnType body against the AnonFn to build an
        # alias-local mapping:  alias_param_name -> concrete_type_name
        alias_mapping: dict[str, str] = {}

        # Match parameter types positionally
        for fn_param_te, anon_param_te in zip(
            alias_te.params, anon_fn.params,
        ):
            if (
                isinstance(fn_param_te, ast.NamedType)
                and fn_param_te.name in alias_params
                and isinstance(anon_param_te, ast.NamedType)
            ):
                alias_mapping[fn_param_te.name] = anon_param_te.name

        # Match return type
        ret = alias_te.return_type
        if isinstance(ret, ast.NamedType) and ret.name in alias_params:
            if isinstance(anon_fn.return_type, ast.NamedType):
                alias_mapping[ret.name] = anon_fn.return_type.name
            elif isinstance(anon_fn.return_type, ast.FnType):
                # Return type is itself a FnType — map to "Fn"
                alias_mapping[ret.name] = "Fn"
        # Handle ADT return types like Option<B> where B is an alias param
        if isinstance(ret, ast.NamedType) and ret.type_args:
            for ret_ta in ret.type_args:
                if (
                    isinstance(ret_ta, ast.NamedType)
                    and ret_ta.name in alias_params
                    and isinstance(anon_fn.return_type, ast.NamedType)
                ):
                    # For Option<B> matched against Option<Int>, extract
                    # B from the AnonFn's return type args
                    if anon_fn.return_type.type_args:
                        idx = [
                            i for i, rta in enumerate(ret.type_args)
                            if (isinstance(rta, ast.NamedType)
                                and rta.name == ret_ta.name)
                        ]
                        if idx:
                            pos = idx[0]
                            if pos < len(anon_fn.return_type.type_args):
                                art = anon_fn.return_type.type_args[pos]
                                if isinstance(art, ast.NamedType):
                                    alias_mapping[ret_ta.name] = art.name

        # Produce result in alias param order
        result: list[str] = []
        for ap in alias_params:
            if ap not in alias_mapping:
                return None
            result.append(alias_mapping[ap])
        return tuple(result)

    @staticmethod
    def _mangle_fn_name(name: str, concrete_types: tuple[str, ...]) -> str:
        """Produce a mangled name for a monomorphized function.

        Example: identity + ("Int",) -> "identity$Int"
        """
        return f"{name}${'_'.join(concrete_types)}"

    def _monomorphize_fn(
        self,
        decl: ast.FnDecl,
        concrete_types: tuple[str, ...],
    ) -> ast.FnDecl:
        """Create a monomorphized copy of a generic function.

        Replaces type variables with concrete types throughout the AST
        and mangles the function name.
        """
        assert decl.forall_vars is not None
        mapping = dict(zip(decl.forall_vars, concrete_types))
        mangled = self._mangle_fn_name(decl.name, concrete_types)

        # Substitute type variables in the entire FnDecl
        substituted = self._substitute_in_ast(decl, mapping)
        assert isinstance(substituted, ast.FnDecl)

        # Override name and clear forall_vars/constraints
        return replace(
            substituted, name=mangled,
            forall_vars=None, forall_constraints=None,
        )

    def _substitute_in_ast(
        self, node: ast.Node, mapping: dict[str, str],
    ) -> ast.Node:
        """Recursively substitute type variable names in an AST subtree.

        Handles NamedType (type expressions) and SlotRef (slot references)
        as special cases; all other nodes are walked generically via
        dataclass fields.
        """
        # Special case: NamedType — substitute type variable names
        if isinstance(node, ast.NamedType):
            new_name = mapping.get(node.name, node.name)
            new_args: tuple[ast.TypeExpr, ...] | None = node.type_args
            if node.type_args:
                new_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )
            if new_name != node.name or new_args is not node.type_args:
                return replace(node, name=new_name, type_args=new_args)
            return node

        # Special case: SlotRef — substitute type_name and type_args
        if isinstance(node, ast.SlotRef):
            new_type_name = mapping.get(node.type_name, node.type_name)
            new_slot_args: tuple[ast.TypeExpr, ...] | None = node.type_args
            if node.type_args:
                new_slot_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )
            if (new_type_name != node.type_name
                    or new_slot_args is not node.type_args):
                return replace(
                    node, type_name=new_type_name, type_args=new_slot_args,
                )
            return node

        # Special case: ResultRef — substitute type_name and type_args
        if isinstance(node, ast.ResultRef):
            new_type_name = mapping.get(node.type_name, node.type_name)
            new_res_args: tuple[ast.TypeExpr, ...] | None = node.type_args
            if node.type_args:
                new_res_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )
            if (new_type_name != node.type_name
                    or new_res_args is not node.type_args):
                return replace(
                    node, type_name=new_type_name, type_args=new_res_args,
                )
            return node

        # Generic case: recurse into all dataclass fields
        changes: dict[str, Any] = {}
        for f in fields(node):
            if f.name == "span":
                continue
            val = getattr(node, f.name)
            new_val = self._substitute_value(val, mapping)
            if new_val is not val:
                changes[f.name] = new_val

        if changes:
            return replace(node, **changes)
        return node

    def _substitute_value(
        self, val: Any, mapping: dict[str, str],
    ) -> Any:
        """Recursively substitute type variables in a field value."""
        if isinstance(val, ast.Node):
            return self._substitute_in_ast(val, mapping)
        if isinstance(val, tuple):
            new_items = tuple(
                self._substitute_value(v, mapping) for v in val
            )
            if any(n is not o for n, o in zip(new_items, val)):
                return new_items
            return val
        return val

    def _substitute_type_expr(
        self, te: ast.TypeExpr, mapping: dict[str, str],
    ) -> ast.TypeExpr:
        """Substitute type variables in a TypeExpr, returning a TypeExpr."""
        result = self._substitute_in_ast(te, mapping)
        assert isinstance(result, ast.TypeExpr)
        return result

    def _check_constraints(
        self,
        decl: ast.FnDecl,
        concrete_types: tuple[str, ...],
    ) -> bool:
        """Verify all ability constraints are satisfied for an instantiation.

        Returns True if all constraints are satisfied, False otherwise
        (after emitting diagnostics).
        """
        if not decl.forall_constraints or not decl.forall_vars:
            return True

        from vera.errors import Diagnostic, SourceLocation

        mapping = dict(zip(decl.forall_vars, concrete_types))
        ok = True
        for constraint in decl.forall_constraints:
            concrete = mapping.get(constraint.type_var)
            if concrete is None:
                continue
            if constraint.ability_name == "Eq":
                if concrete not in _EQ_TYPES:
                    self.diagnostics.append(Diagnostic(
                        description=(
                            f"Type '{concrete}' does not satisfy ability "
                            f"'{constraint.ability_name}'. Only primitive "
                            f"types (Int, Bool, Float64, String, Byte, "
                            f"Nat, Unit) support Eq."
                        ),
                        location=SourceLocation(file=self.file),
                        severity="error",
                        error_code="E613",
                    ))
                    ok = False
            else:
                self.diagnostics.append(Diagnostic(
                    description=(
                        f"Ability '{constraint.ability_name}' is not yet "
                        f"supported for code generation."
                    ),
                    location=SourceLocation(file=self.file),
                    severity="error",
                    error_code="E613",
                ))
                ok = False
        return ok
