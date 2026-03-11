"""Mixin for function calls, constructor calls, and qualified/module calls.

Extracted from ``core.py`` so that call-checking logic lives in its
own file while the main :class:`TypeChecker` stays focused on
orchestration.
"""

from __future__ import annotations

from vera import ast
from vera.environment import (
    ConstructorInfo,
    FunctionInfo,
    OpInfo,
)
from vera.types import (
    AdtType,
    ConcreteEffectRow,
    PureEffectRow,
    Type,
    TypeVar,
    UnknownType,
    contains_typevar,
    is_effect_subtype,
    is_subtype,
    pretty_effect,
    pretty_type,
    substitute,
)


class CallsMixin:
    """Methods for checking function calls, constructors, and qualified calls."""

    # -----------------------------------------------------------------
    # Function calls
    # -----------------------------------------------------------------

    def _check_fn_call(self, expr: ast.FnCall) -> Type | None:
        """Type-check a function call."""
        return self._check_call_with_args(expr.name, expr.args, expr)

    def _check_call_with_args(self, name: str, args: tuple[ast.Expr, ...],
                              node: ast.Node) -> Type | None:
        """Check a call to function `name` with given arguments."""
        # Look up function
        fn_info = self.env.lookup_function(name)
        if fn_info:
            return self._check_fn_call_with_info(fn_info, args, node)

        # Maybe it's an effect operation
        op_info = self.env.lookup_effect_op(name)
        if op_info:
            self._effect_ops_used.add(op_info.parent_effect)
            return self._check_op_call(op_info, args, node)

        # Unresolved — emit warning and continue
        self._error(
            node,
            f"Unresolved function '{name}'.",
            rationale="The function is not defined in this file and may come "
                      "from an unresolved import.",
            severity="warning",
            error_code="E200",
        )
        # Still synth arg types to find errors within them
        for arg in args:
            self._synth_expr(arg)
        return UnknownType()

    def _check_fn_call_with_info(self, fn_info: FunctionInfo,
                                 args: tuple[ast.Expr, ...],
                                 node: ast.Node) -> Type | None:
        """Check a call against a known function signature."""
        # Synth arg types.  For non-generic functions pass the declared
        # param type as *expected* so that nested constructors can resolve
        # TypeVars from context (fixes #243).
        arg_types: list[Type | None] = []
        for i, arg in enumerate(args):
            exp: Type | None = None
            if (not fn_info.forall_vars
                    and i < len(fn_info.param_types)):
                pt = fn_info.param_types[i]
                if not contains_typevar(pt):
                    exp = pt
            arg_types.append(self._synth_expr(arg, expected=exp))

        # Arity check
        if len(args) != len(fn_info.param_types):
            self._error(
                node,
                f"Function '{fn_info.name}' expects {len(fn_info.param_types)}"
                f" argument(s), got {len(args)}.",
                spec_ref='Chapter 5, Section 5.1 "Function Declarations"',
                error_code="E201",
            )
            return fn_info.return_type

        # Generic inference
        param_types = fn_info.param_types
        return_type = fn_info.return_type
        if fn_info.forall_vars:
            mapping = self._infer_type_args(
                fn_info.forall_vars, fn_info.param_types, arg_types)
            if mapping:
                param_types = tuple(
                    substitute(p, mapping) for p in param_types)
                return_type = substitute(return_type, mapping)

        # Check each argument
        for i, (arg_ty, param_ty) in enumerate(zip(arg_types, param_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            # Re-synth if arg still has unresolved TypeVars (bidirectional)
            if contains_typevar(arg_ty) and not contains_typevar(param_ty):
                arg_ty = self._synth_expr(args[i], expected=param_ty)
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                arg_types[i] = arg_ty
            # Re-synth with expected type when subtype check would fail —
            # enables bidirectional coercion (e.g. IntLit → Byte).
            if (not is_subtype(arg_ty, param_ty)
                    and not contains_typevar(param_ty)):
                re = self._synth_expr(args[i], expected=param_ty)
                if re is not None and not isinstance(re, UnknownType):
                    if is_subtype(re, param_ty):
                        arg_ty = re
                        arg_types[i] = re
            if not is_subtype(arg_ty, param_ty):
                self._error(
                    args[i],
                    f"Argument {i} of '{fn_info.name}' has type "
                    f"{pretty_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    spec_ref='Chapter 5, Section 5.1 "Function Declarations"',
                    error_code="E202",
                )

        # Track effects
        if not isinstance(fn_info.effect, PureEffectRow):
            if isinstance(fn_info.effect, ConcreteEffectRow):
                for ei in fn_info.effect.effects:
                    self._effect_ops_used.add(ei.name)

        # Call-site effect check: callee's effects must be permitted
        # by the caller's context (Spec §7.8 subeffecting).
        if self.env.current_effect_row is not None:
            if not is_effect_subtype(fn_info.effect,
                                     self.env.current_effect_row):
                self._error(
                    node,
                    f"Function '{fn_info.name}' requires "
                    f"{pretty_effect(fn_info.effect)} but call site only "
                    f"allows {pretty_effect(self.env.current_effect_row)}.",
                    rationale="A function can only be called from a context "
                              "that permits all of its declared effects "
                              "(subeffecting).",
                    fix=f"Either add the missing effects to the calling "
                        f"function's effects clause, or handle the effects "
                        f"with a handler.",
                    spec_ref='Chapter 7, Section 7.8 "Effect Subtyping"',
                    error_code="E125",
                )

        return return_type

    def _check_op_call(self, op_info: OpInfo,
                       args: tuple[ast.Expr, ...],
                       node: ast.Node) -> Type | None:
        """Check a call to an effect operation."""
        arg_types: list[Type | None] = []
        for arg in args:
            arg_types.append(self._synth_expr(arg))

        # Resolve type params from current effect context
        mapping = self._effect_type_mapping(op_info.parent_effect)
        param_types = tuple(substitute(p, mapping) for p in op_info.param_types)
        return_type = substitute(op_info.return_type, mapping)

        if len(args) != len(param_types):
            self._error(
                node,
                f"Effect operation '{op_info.name}' expects "
                f"{len(param_types)} argument(s), got {len(args)}.",
                error_code="E203",
            )
            return return_type

        for i, (arg_ty, param_ty) in enumerate(zip(arg_types, param_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            if not is_subtype(arg_ty, param_ty):
                self._error(
                    args[i],
                    f"Argument {i} of '{op_info.name}' has type "
                    f"{pretty_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    error_code="E204",
                )

        return return_type

    def _effect_type_mapping(self, effect_name: str) -> dict[str, Type]:
        """Get the type argument mapping for an effect from the current
        effect row context."""
        if not isinstance(self.env.current_effect_row, ConcreteEffectRow):
            return {}
        for ei in self.env.current_effect_row.effects:
            if ei.name == effect_name:
                eff_info = self.env.lookup_effect(effect_name)
                if eff_info and eff_info.type_params and ei.type_args:
                    return dict(zip(eff_info.type_params, ei.type_args))
        return {}

    # -----------------------------------------------------------------
    # Constructors
    # -----------------------------------------------------------------

    def _check_constructor_call(self, expr: ast.ConstructorCall, *,
                                expected: Type | None = None) -> Type | None:
        """Type-check a constructor call: Ctor(args)."""
        # Tuple is a variadic built-in constructor — handle specially
        if expr.name == "Tuple":
            return self._check_tuple_constructor(expr)

        ci = self.env.lookup_constructor(expr.name)
        if ci is None:
            self._error(
                expr,
                f"Unknown constructor '{expr.name}'.",
                severity="warning",
                error_code="E210",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # Build expected-type mapping for bidirectional inference
        expected_mapping: dict[str, Type] = {}
        if (isinstance(expected, AdtType)
                and ci.parent_type_params
                and expected.name == ci.parent_type
                and len(expected.type_args) == len(ci.parent_type_params)):
            for tv, exp_arg in zip(ci.parent_type_params,
                                   expected.type_args):
                if not isinstance(exp_arg, TypeVar):
                    expected_mapping[tv] = exp_arg

        # Compute field types with expected-type substitution so we can
        # pass them as expected to nested constructor args (e.g. Some(None))
        field_types_for_expected: tuple[Type, ...] | None = None
        if ci.field_types is not None and expected_mapping:
            field_types_for_expected = tuple(
                substitute(ft, expected_mapping) for ft in ci.field_types)

        # Synth arg types, passing resolved field type as expected
        arg_types: list[Type | None] = []
        for i, arg in enumerate(expr.args):
            field_expected: Type | None = None
            if field_types_for_expected and i < len(field_types_for_expected):
                ft = field_types_for_expected[i]
                if not contains_typevar(ft):
                    field_expected = ft
            arg_types.append(self._synth_expr(arg, expected=field_expected))

        if ci.field_types is None:
            if expr.args:
                self._error(
                    expr,
                    f"Constructor '{expr.name}' is nullary but was given "
                    f"{len(expr.args)} argument(s).",
                    error_code="E211",
                )
            return self._ctor_result_type(ci, arg_types, expected=expected)

        if len(expr.args) != len(ci.field_types):
            self._error(
                expr,
                f"Constructor '{expr.name}' expects "
                f"{len(ci.field_types)} field(s), got {len(expr.args)}.",
                error_code="E212",
            )
            return self._ctor_result_type(ci, arg_types, expected=expected)

        # Infer type args for parameterised ADTs from arg types
        mapping = self._infer_ctor_type_args(ci, arg_types)

        # Merge expected-type mapping for unresolved vars
        for tv, exp_ty in expected_mapping.items():
            if tv not in mapping:
                mapping[tv] = exp_ty

        field_types = ci.field_types
        if mapping:
            field_types = tuple(substitute(ft, mapping) for ft in field_types)

        for i, (arg_ty, field_ty) in enumerate(zip(arg_types, field_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(field_ty, (TypeVar, UnknownType)):
                continue
            # Re-synth if arg still has unresolved TypeVars and the
            # subtype check would fail (e.g. List<T$2> vs List<Option<Int>>).
            if contains_typevar(arg_ty) and not is_subtype(arg_ty, field_ty):
                arg_ty = self._synth_expr(expr.args[i], expected=field_ty)
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                arg_types[i] = arg_ty
            if not is_subtype(arg_ty, field_ty):
                self._error(
                    expr.args[i],
                    f"Constructor '{expr.name}' field {i} has type "
                    f"{pretty_type(arg_ty)}, expected "
                    f"{pretty_type(field_ty)}.",
                    error_code="E213",
                )

        return self._ctor_result_type(ci, arg_types, expected=expected)

    def _check_tuple_constructor(
        self, expr: ast.ConstructorCall
    ) -> Type | None:
        """Type-check a variadic Tuple constructor: Tuple(a, b, ...)."""
        if not expr.args:
            self._error(
                expr,
                "Tuple constructor requires at least one field.",
                spec_ref='Chapter 2, Section 2.3.1 "Tuple Types"',
                error_code="E210",
            )
            return UnknownType()
        arg_types: list[Type] = []
        for arg in expr.args:
            t = self._synth_expr(arg)
            if t is not None and not isinstance(t, UnknownType):
                arg_types.append(t)
            else:
                arg_types.append(UnknownType())
        return AdtType("Tuple", tuple(arg_types))

    def _check_nullary_constructor(self, expr: ast.NullaryConstructor, *,
                                    expected: Type | None = None) -> Type | None:
        """Type-check a nullary constructor: None, Nil, etc."""
        ci = self.env.lookup_constructor(expr.name)
        if ci is None:
            self._error(expr, f"Unknown constructor '{expr.name}'.",
                        severity="warning", error_code="E214")
            return UnknownType()

        if ci.field_types is not None:
            self._error(
                expr,
                f"Constructor '{expr.name}' requires "
                f"{len(ci.field_types)} field(s) but was used as nullary.",
                error_code="E215",
            )

        return self._ctor_result_type(ci, [], expected=expected)

    def _fresh_typevar(self, name: str) -> TypeVar:
        """Return a TypeVar with a unique name derived from *name*.

        Fresh names prevent self-referential mappings when constructors
        from different ADTs share a type parameter name (e.g. both
        Option<T> and List<T> use ``T``).
        """
        self._fresh_id += 1
        return TypeVar(f"{name}${self._fresh_id}")

    def _ctor_result_type(self, ci: ConstructorInfo,
                          arg_types: list[Type | None], *,
                          expected: Type | None = None) -> Type:
        """Compute the result type of a constructor call.

        When *expected* is an AdtType with the same parent name, unresolved
        TypeVars are filled from the expected type args (bidirectional).
        Remaining unresolved TypeVars are freshened to avoid collisions.
        """
        if ci.parent_type_params:
            # Try to infer type args from argument types
            mapping = self._infer_ctor_type_args(ci, arg_types)

            # Fill unresolved TypeVars from expected type (bidirectional)
            if (isinstance(expected, AdtType)
                    and expected.name == ci.parent_type
                    and len(expected.type_args) == len(ci.parent_type_params)):
                for tv, exp_arg in zip(ci.parent_type_params,
                                       expected.type_args):
                    if tv not in mapping and not isinstance(exp_arg, TypeVar):
                        mapping[tv] = exp_arg

            # Use fresh TypeVars for any that remain unresolved — prevents
            # self-referential mappings when different ADTs share a param
            # name (e.g. both Option<T> and List<T> use "T").
            args = tuple(
                mapping.get(tv, self._fresh_typevar(tv))
                for tv in ci.parent_type_params
            )
            return AdtType(ci.parent_type, args)
        return AdtType(ci.parent_type, ())

    def _infer_ctor_type_args(self, ci: ConstructorInfo,
                              arg_types: list[Type | None]) -> dict[str, Type]:
        """Infer type arguments for a parameterised constructor."""
        if not ci.parent_type_params or not ci.field_types:
            return {}
        mapping: dict[str, Type] = {}
        for field_ty, arg_ty in zip(ci.field_types, arg_types):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            self._unify_for_inference(field_ty, arg_ty, mapping)
        return mapping

    # -----------------------------------------------------------------
    # Qualified / module calls
    # -----------------------------------------------------------------

    def _check_qualified_call(self, expr: ast.QualifiedCall) -> Type | None:
        """Type-check a qualified call: Effect.op(args)."""
        # Try as effect operation
        op_info = self.env.lookup_effect_op(expr.name, expr.qualifier)
        if op_info:
            self._effect_ops_used.add(op_info.parent_effect)
            return self._check_op_call(op_info, expr.args, expr)

        # Try as module-qualified function
        self._error(
            expr,
            f"Unresolved qualified call '{expr.qualifier}.{expr.name}'.",
            severity="warning",
            error_code="E220",
        )
        for arg in expr.args:
            self._synth_expr(arg)
        return UnknownType()

    def _check_module_call(self, expr: ast.ModuleCall) -> Type | None:
        """Type-check a module-qualified call: path.to.fn(args).

        Lookup order:
        1. Module not resolved → warning (same as C7a).
        2. Name not in selective import list → error.
        2.5. C7c: function is private → error.
        3. Function found (public) → delegate to ``_check_fn_call_with_info``.
        4. Function not found in module → warning with available list.
        """
        mod_path = tuple(expr.path)
        fn_name = expr.name
        mod_label = ".".join(expr.path)

        # 1. Module not resolved
        if mod_path not in self._resolved_module_paths:
            self._error(
                expr,
                f"Module '{mod_label}' not found. "
                f"Cannot resolve call to '{fn_name}'.",
                severity="warning",
                rationale=(
                    "No module matching this import path was resolved. "
                    "Check that the file exists and is imported."
                ),
                error_code="E230",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # 2. Selective import filter
        import_filter = self._import_names.get(mod_path)
        if import_filter is not None and fn_name not in import_filter:
            self._error(
                expr,
                f"'{fn_name}' is not imported from module "
                f"'{mod_label}'. "
                f"Imported names: {sorted(import_filter)}.",
                rationale=(
                    "The import declaration uses selective imports. "
                    "Add the name to the import list to use it."
                ),
                fix=(
                    f"Change the import to include '{fn_name}': "
                    f"import {mod_label}"
                    f"({', '.join(sorted(import_filter | {fn_name}))});"
                ),
                error_code="E231",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # 2.5 C7c: visibility check — is the function private?
        all_fns = self._module_all_functions.get(mod_path, {})
        fn_all = all_fns.get(fn_name)
        if fn_all is not None and not self._is_public(fn_all.visibility):
            self._error(
                expr,
                f"Function '{fn_name}' in module '{mod_label}' is "
                f"private and cannot be accessed from outside "
                f"its module.",
                rationale=(
                    "Only functions marked 'public' can be called "
                    "from other modules."
                ),
                fix=(
                    f"Mark the function as public in the module: "
                    f"public fn {fn_name}(...)"
                ),
                spec_ref=(
                    'Chapter 5, Section 5.8 "Function Visibility"'
                ),
                error_code="E232",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # 3. Look up function in module's registered declarations
        mod_fns = self._module_functions.get(mod_path, {})
        fn_info = mod_fns.get(fn_name)
        if fn_info is not None:
            return self._check_fn_call_with_info(fn_info, expr.args, expr)

        # 4. Function not found in module
        available = sorted(mod_fns.keys())
        self._error(
            expr,
            f"Function '{fn_name}' not found in module "
            f"'{mod_label}'."
            + (f" Available functions: {available}." if available else ""),
            severity="warning",
            error_code="E233",
        )
        for arg in expr.args:
            self._synth_expr(arg)
        return UnknownType()
