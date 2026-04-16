"""Function call and effect handler translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import (
    WasmSlotEnv,
    _element_mem_size,
    _element_store_op,
    _is_pair_element_type,
    gc_shadow_push,
)


class CallsMixin:
    """Methods for translating function calls and effect handlers to WASM."""

    def _translate_call(
        self, call: ast.FnCall, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a function call to WASM call instruction.

        If the call name matches an effect operation (e.g. get/put for
        State<T>), redirects to the corresponding host import.
        """
        # Built-in intrinsics — only when no user-defined function
        # with the same name exists.  User definitions take priority
        # so that e.g. a user-defined length(@List<Int> -> @Nat) is
        # not mistakenly compiled as the array-length built-in.
        if call.name not in self._known_fns:
            if call.name == "array_length" and len(call.args) == 1:
                return self._translate_array_length(call.args[0], env)
            if call.name == "string_length" and len(call.args) == 1:
                return self._translate_string_length(call.args[0], env)
            if call.name == "string_concat" and len(call.args) == 2:
                return self._translate_string_concat(
                    call.args[0], call.args[1], env,
                )
            if call.name == "string_slice" and len(call.args) == 3:
                return self._translate_string_slice(
                    call.args[0], call.args[1], call.args[2], env,
                )
            if call.name == "string_char_code" and len(call.args) == 2:
                return self._translate_char_code(
                    call.args[0], call.args[1], env,
                )
            if call.name == "string_from_char_code" and len(call.args) == 1:
                return self._translate_from_char_code(call.args[0], env)
            if call.name == "string_repeat" and len(call.args) == 2:
                return self._translate_string_repeat(
                    call.args[0], call.args[1], env,
                )
            if call.name == "parse_nat" and len(call.args) == 1:
                return self._translate_parse_nat(call.args[0], env)
            if call.name == "parse_int" and len(call.args) == 1:
                return self._translate_parse_int(call.args[0], env)
            if call.name == "parse_float64" and len(call.args) == 1:
                return self._translate_parse_float64(call.args[0], env)
            if call.name == "parse_bool" and len(call.args) == 1:
                return self._translate_parse_bool(call.args[0], env)
            if call.name == "base64_encode" and len(call.args) == 1:
                return self._translate_base64_encode(call.args[0], env)
            if call.name == "base64_decode" and len(call.args) == 1:
                return self._translate_base64_decode(call.args[0], env)
            if call.name == "url_encode" and len(call.args) == 1:
                return self._translate_url_encode(call.args[0], env)
            if call.name == "url_decode" and len(call.args) == 1:
                return self._translate_url_decode(call.args[0], env)
            if call.name == "url_parse" and len(call.args) == 1:
                return self._translate_url_parse(call.args[0], env)
            if call.name == "url_join" and len(call.args) == 1:
                return self._translate_url_join(call.args[0], env)
            # Async builtins — identity (eager evaluation, Future<T>
            # is WASM-transparent)
            # Markdown host-import builtins (pure, implemented in Python)
            # Json host-import builtins
            if call.name == "json_parse" and len(call.args) == 1:
                return self._translate_json_parse(call.args[0], env)
            if call.name == "json_stringify" and len(call.args) == 1:
                return self._translate_json_stringify(call.args[0], env)
            # Html host-import builtins
            if call.name == "html_parse" and len(call.args) == 1:
                return self._translate_html_parse(call.args[0], env)
            if call.name == "html_to_string" and len(call.args) == 1:
                return self._translate_html_to_string(call.args[0], env)
            if call.name == "html_query" and len(call.args) == 2:
                return self._translate_html_query(
                    call.args[0], call.args[1], env,
                )
            if call.name == "html_text" and len(call.args) == 1:
                return self._translate_html_text(call.args[0], env)
            if call.name == "md_parse" and len(call.args) == 1:
                return self._translate_md_parse(call.args[0], env)
            if call.name == "md_render" and len(call.args) == 1:
                return self._translate_md_render(call.args[0], env)
            if call.name == "md_has_heading" and len(call.args) == 2:
                return self._translate_md_has_heading(
                    call.args[0], call.args[1], env,
                )
            if call.name == "md_has_code_block" and len(call.args) == 2:
                return self._translate_md_has_code_block(
                    call.args[0], call.args[1], env,
                )
            if call.name == "md_extract_code_blocks" and len(call.args) == 2:
                return self._translate_md_extract_code_blocks(
                    call.args[0], call.args[1], env,
                )
            # Regex host-import builtins (pure, host-provided)
            if call.name == "regex_match" and len(call.args) == 2:
                return self._translate_regex_match(
                    call.args[0], call.args[1], env,
                )
            if call.name == "regex_find" and len(call.args) == 2:
                return self._translate_regex_find(
                    call.args[0], call.args[1], env,
                )
            if call.name == "regex_find_all" and len(call.args) == 2:
                return self._translate_regex_find_all(
                    call.args[0], call.args[1], env,
                )
            if call.name == "regex_replace" and len(call.args) == 3:
                return self._translate_regex_replace(
                    call.args[0], call.args[1], call.args[2], env,
                )
            if call.name == "async" and len(call.args) == 1:
                return self._translate_async(call.args[0], env)
            if call.name == "await" and len(call.args) == 1:
                return self._translate_await(call.args[0], env)
            if call.name == "to_string" and len(call.args) == 1:
                return self._translate_to_string(call.args[0], env)
            if call.name == "int_to_string" and len(call.args) == 1:
                return self._translate_to_string(call.args[0], env)
            if call.name == "nat_to_string" and len(call.args) == 1:
                return self._translate_to_string(call.args[0], env)
            if call.name == "bool_to_string" and len(call.args) == 1:
                return self._translate_bool_to_string(call.args[0], env)
            if call.name == "byte_to_string" and len(call.args) == 1:
                return self._translate_byte_to_string(call.args[0], env)
            if call.name == "float_to_string" and len(call.args) == 1:
                return self._translate_float_to_string(call.args[0], env)
            if call.name == "string_strip" and len(call.args) == 1:
                return self._translate_strip(call.args[0], env)
            # String search builtins
            if call.name == "string_contains" and len(call.args) == 2:
                return self._translate_string_contains(
                    call.args[0], call.args[1], env,
                )
            if call.name == "string_starts_with" and len(call.args) == 2:
                return self._translate_starts_with(
                    call.args[0], call.args[1], env,
                )
            if call.name == "string_ends_with" and len(call.args) == 2:
                return self._translate_ends_with(
                    call.args[0], call.args[1], env,
                )
            if call.name == "string_index_of" and len(call.args) == 2:
                return self._translate_index_of(
                    call.args[0], call.args[1], env,
                )
            # String transformation builtins
            if call.name == "string_upper" and len(call.args) == 1:
                return self._translate_to_upper(call.args[0], env)
            if call.name == "string_lower" and len(call.args) == 1:
                return self._translate_to_lower(call.args[0], env)
            if call.name == "string_replace" and len(call.args) == 3:
                return self._translate_replace(
                    call.args[0], call.args[1], call.args[2], env,
                )
            if call.name == "string_split" and len(call.args) == 2:
                return self._translate_split(
                    call.args[0], call.args[1], env,
                )
            if call.name == "string_join" and len(call.args) == 2:
                return self._translate_join(
                    call.args[0], call.args[1], env,
                )
            if call.name == "array_append" and len(call.args) == 2:
                return self._translate_array_append(
                    call.args[0], call.args[1], env,
                )
            if call.name == "array_range" and len(call.args) == 2:
                return self._translate_array_range(
                    call.args[0], call.args[1], env,
                )
            if call.name == "array_concat" and len(call.args) == 2:
                return self._translate_array_concat(
                    call.args[0], call.args[1], env,
                )
            if call.name == "array_slice" and len(call.args) == 3:
                return self._translate_array_slice(
                    call.args[0], call.args[1], call.args[2], env,
                )
            # Numeric math builtins
            if call.name == "abs" and len(call.args) == 1:
                return self._translate_abs(call.args[0], env)
            if call.name == "min" and len(call.args) == 2:
                return self._translate_min(
                    call.args[0], call.args[1], env,
                )
            if call.name == "max" and len(call.args) == 2:
                return self._translate_max(
                    call.args[0], call.args[1], env,
                )
            if call.name == "floor" and len(call.args) == 1:
                return self._translate_floor(call.args[0], env)
            if call.name == "ceil" and len(call.args) == 1:
                return self._translate_ceil(call.args[0], env)
            if call.name == "round" and len(call.args) == 1:
                return self._translate_round(call.args[0], env)
            if call.name == "sqrt" and len(call.args) == 1:
                return self._translate_sqrt(call.args[0], env)
            if call.name == "pow" and len(call.args) == 2:
                return self._translate_pow(
                    call.args[0], call.args[1], env,
                )
            # Numeric type conversions
            if call.name == "int_to_float" and len(call.args) == 1:
                return self._translate_to_float(call.args[0], env)
            if call.name == "float_to_int" and len(call.args) == 1:
                return self._translate_float_to_int(call.args[0], env)
            if call.name == "nat_to_int" and len(call.args) == 1:
                return self._translate_nat_to_int(call.args[0], env)
            if call.name == "int_to_nat" and len(call.args) == 1:
                return self._translate_int_to_nat(call.args[0], env)
            if call.name == "byte_to_int" and len(call.args) == 1:
                return self._translate_byte_to_int(call.args[0], env)
            if call.name == "int_to_byte" and len(call.args) == 1:
                return self._translate_int_to_byte(call.args[0], env)
            # Float64 predicates and constants
            if call.name == "float_is_nan" and len(call.args) == 1:
                return self._translate_is_nan(call.args[0], env)
            if call.name == "float_is_infinite" and len(call.args) == 1:
                return self._translate_is_infinite(call.args[0], env)
            if call.name == "nan" and len(call.args) == 0:
                return self._translate_nan()
            if call.name == "infinity" and len(call.args) == 0:
                return self._translate_infinity()
            # Ability operations dispatched at WASM level (§9.8)
            if call.name == "show" and len(call.args) == 1:
                return self._translate_show(call.args[0], env)
            if call.name == "hash" and len(call.args) == 1:
                return self._translate_hash(call.args[0], env)
            # Map builtins
            if call.name == "map_new" and len(call.args) == 0:
                return self._translate_map_new(call, env)
            if call.name == "map_insert" and len(call.args) == 3:
                return self._translate_map_insert(call, env)
            if call.name == "map_get" and len(call.args) == 2:
                return self._translate_map_get(call, env)
            if call.name == "map_contains" and len(call.args) == 2:
                return self._translate_map_contains(call, env)
            if call.name == "map_remove" and len(call.args) == 2:
                return self._translate_map_remove(call, env)
            if call.name == "map_size" and len(call.args) == 1:
                return self._translate_map_size(call.args[0], env)
            if call.name == "map_keys" and len(call.args) == 1:
                return self._translate_map_keys(call, env)
            if call.name == "map_values" and len(call.args) == 1:
                return self._translate_map_values(call, env)
            # Set builtins
            if call.name == "set_new" and len(call.args) == 0:
                return self._translate_set_new(call, env)
            if call.name == "set_add" and len(call.args) == 2:
                return self._translate_set_add(call, env)
            if call.name == "set_contains" and len(call.args) == 2:
                return self._translate_set_contains(call, env)
            if call.name == "set_remove" and len(call.args) == 2:
                return self._translate_set_remove(call, env)
            if call.name == "set_size" and len(call.args) == 1:
                return self._translate_set_size(call.args[0], env)
            if call.name == "set_to_array" and len(call.args) == 1:
                return self._translate_set_to_array(call, env)
            # Decimal builtins
            if call.name == "decimal_from_int" and len(call.args) == 1:
                return self._translate_decimal_unary(
                    call, env, "decimal_from_int", "i64", "i32")
            if call.name == "decimal_from_float" and len(call.args) == 1:
                return self._translate_decimal_unary(
                    call, env, "decimal_from_float", "f64", "i32")
            if call.name == "decimal_from_string" and len(call.args) == 1:
                return self._translate_decimal_from_string(call, env)
            if call.name == "decimal_to_string" and len(call.args) == 1:
                return self._translate_decimal_to_string(call, env)
            if call.name == "decimal_to_float" and len(call.args) == 1:
                return self._translate_decimal_unary(
                    call, env, "decimal_to_float", "i32", "f64")
            if call.name == "decimal_add" and len(call.args) == 2:
                return self._translate_decimal_binary(
                    call, env, "decimal_add")
            if call.name == "decimal_sub" and len(call.args) == 2:
                return self._translate_decimal_binary(
                    call, env, "decimal_sub")
            if call.name == "decimal_mul" and len(call.args) == 2:
                return self._translate_decimal_binary(
                    call, env, "decimal_mul")
            if call.name == "decimal_div" and len(call.args) == 2:
                return self._translate_decimal_div(call, env)
            if call.name == "decimal_neg" and len(call.args) == 1:
                return self._translate_decimal_unary(
                    call, env, "decimal_neg", "i32", "i32")
            if call.name == "decimal_compare" and len(call.args) == 2:
                return self._translate_decimal_compare(call, env)
            if call.name == "decimal_eq" and len(call.args) == 2:
                return self._translate_decimal_eq(call, env)
            if call.name == "decimal_round" and len(call.args) == 2:
                return self._translate_decimal_round(call, env)
            if call.name == "decimal_abs" and len(call.args) == 1:
                return self._translate_decimal_unary(
                    call, env, "decimal_abs", "i32", "i32")

        # Check if this is a closure application: apply_fn(closure, args...)
        if call.name == "apply_fn" and len(call.args) >= 2:
            return self._translate_apply_fn(call, env)

        # Check if this is an effect operation (e.g. get/put/throw)
        if call.name in self._effect_ops:
            target_name, _is_void = self._effect_ops[call.name]
            instructions: list[str] = []
            for arg in call.args:
                arg_instrs = self.translate_expr(arg, env)
                if arg_instrs is None:
                    return None
                instructions.extend(arg_instrs)
            # throw uses WASM throw instruction, not call
            if call.name == "throw":
                instructions.append(f"throw {target_name}")
            else:
                instructions.append(f"call {target_name}")
            return instructions

        # Resolve call target — rewrite generic calls to mangled names
        call_target = call.name
        if call.name in self._generic_fn_info:
            resolved = self._resolve_generic_call(call)
            if resolved is not None:
                call_target = resolved

        # Guard rail: reject calls to functions not defined in this module
        if (self._known_fns
                and call_target not in self._known_fns
                and call_target not in self._ctor_layouts):
            return None

        # Regular function call
        instructions = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            instructions.extend(arg_instrs)
        instructions.append(f"call ${call_target}")
        return instructions

    def _translate_qualified_call(
        self, call: ast.QualifiedCall, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a qualified call (e.g. IO.print) to host import call."""
        instructions: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            instructions.extend(arg_instrs)
        # User-defined effect ops (e.g. Exn.throw, State.get/put) — delegate to
        # the effect_ops table, exactly as the unqualified _translate_call path does.
        # Guard: skip for host-import built-ins (Http, Inference, IO) whose op names
        # are handled by the branches below. Http.get and Http.post share the names
        # "get"/"post" with possible user effect ops; the qualifier check prevents
        # misrouting Http.get into _effect_ops when inside a handle[State<T>] body
        # where _effect_ops["get"] is populated.
        _host_import_qualifiers = {"Http", "Inference", "IO"}
        if call.qualifier not in _host_import_qualifiers and call.name in self._effect_ops:
            target_name, _is_void = self._effect_ops[call.name]
            if call.name == "throw":
                instructions.append(f"throw {target_name}")
            else:
                instructions.append(f"call {target_name}")
            return instructions
        # Http operations use prefixed names to avoid collision
        if call.qualifier == "Http":
            wasm_name = f"http_{call.name}"
            self._http_ops_used.add(wasm_name)
            self.needs_alloc = True
            instructions.append(f"call $vera.{wasm_name}")
        elif call.qualifier == "Inference":
            wasm_name = f"inference_{call.name}"
            self._inference_ops_used.add(wasm_name)
            self.needs_alloc = True
            instructions.append(f"call $vera.{wasm_name}")
        else:
            instructions.append(f"call $vera.{call.name}")
        # IO.exit never returns — add unreachable to satisfy WASM validation
        if call.qualifier == "IO" and call.name == "exit":
            instructions.append("unreachable")
        return instructions

    def _resolve_generic_call(self, call: ast.FnCall) -> str | None:
        """Resolve a call to a generic function to its mangled name.

        Infers concrete type variable bindings from the call's argument
        expressions, then produces the mangled name like 'identity$Int'.
        Returns None if type inference fails.
        """
        forall_vars, param_types = self._generic_fn_info[call.name]
        mapping: dict[str, str] = {}

        for param_te, arg in zip(param_types, call.args):
            self._unify_param_arg_wasm(param_te, arg, forall_vars, mapping)

        # Build mangled name; default phantom vars to Unit
        parts = []
        for tv in forall_vars:
            if tv not in mapping:
                mapping[tv] = "Bool"
            # Sanitize parameterized type names for WAT identifiers
            s = mapping[tv].replace("<", "_").replace(">", "").replace(", ", "_")
            parts.append(s)
        return f"{call.name}${'_'.join(parts)}"

    def _unify_param_arg_wasm(
        self,
        param_te: ast.TypeExpr,
        arg: ast.Expr,
        forall_vars: tuple[str, ...],
        mapping: dict[str, str],
    ) -> None:
        """Unify a parameter TypeExpr against an argument to bind type vars.

        Mirrors CodeGenerator._unify_param_arg for use during WASM
        translation.
        """
        if isinstance(param_te, ast.RefinementType):
            self._unify_param_arg_wasm(
                param_te.base_type, arg, forall_vars, mapping,
            )
            return

        if not isinstance(param_te, ast.NamedType):
            return

        if param_te.name in forall_vars:
            vera_type = self._infer_vera_type(arg)
            if vera_type and param_te.name not in mapping:
                mapping[param_te.name] = vera_type
            return

        # Parameterized type like Option<T>
        if param_te.type_args:
            # Handle type alias for FnType matched against AnonFn arg
            if isinstance(arg, ast.AnonFn):
                alias_concrete = self._infer_fn_alias_type_args_wasm(
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

            arg_info = self._get_arg_type_info_wasm(arg)
            if arg_info and arg_info[0] == param_te.name:
                for param_ta, arg_ta_name in zip(
                    param_te.type_args, arg_info[1]
                ):
                    # arg_ta_name is None for unknown ADT type-param positions
                    # (e.g. T in Err(e) where only E is inferred from Err's field).
                    if (arg_ta_name is not None
                            and isinstance(param_ta, ast.NamedType)
                            and param_ta.name in forall_vars
                            and param_ta.name not in mapping):
                        mapping[param_ta.name] = arg_ta_name

    def _infer_fn_alias_type_args_wasm(
        self,
        param_te: ast.NamedType,
        anon_fn: ast.AnonFn,
    ) -> tuple[str, ...] | None:
        """Infer concrete types for a type alias's params from an AnonFn.

        Mirrors MonomorphizationMixin._infer_fn_alias_type_args for use
        during WASM call-site rewriting.
        """
        alias_te = self._type_aliases.get(param_te.name)
        if not isinstance(alias_te, ast.FnType):
            return None

        alias_params = self._type_alias_params.get(param_te.name)
        if (
            not alias_params
            or not param_te.type_args
            or len(alias_params) != len(param_te.type_args)
        ):
            return None

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
        # Handle ADT return types like Option<B>
        if isinstance(ret, ast.NamedType) and ret.type_args:
            for ret_ta in ret.type_args:
                if (
                    isinstance(ret_ta, ast.NamedType)
                    and ret_ta.name in alias_params
                    and isinstance(anon_fn.return_type, ast.NamedType)
                    and anon_fn.return_type.type_args
                ):
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

        result: list[str] = []
        for ap in alias_params:
            if ap not in alias_mapping:
                return None
            result.append(alias_mapping[ap])
        return tuple(result)

    def _infer_concat_elem_type(self, expr: ast.Expr) -> str | None:
        """Infer the element type name from an array-typed expression."""
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Array" and expr.type_args:
                ta = expr.type_args[0]
                if isinstance(ta, ast.NamedType):
                    return ta.name
        if isinstance(expr, ast.ArrayLit):
            if expr.elements:
                return self._infer_vera_type(expr.elements[0])
            return None
        if isinstance(expr, ast.FnCall):
            if expr.name == "array_range":
                return "Int"
            if expr.name in (
                "array_concat", "array_append", "array_slice",
                "array_filter",
            ) and expr.args:
                return self._infer_concat_elem_type(expr.args[0])
        return None

    def _translate_string_length(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate string_length(string) → Int (i64).

        String is (ptr, len) on stack; extract len and extend to i64.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        tmp_len = self.alloc_local("i32")
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        # Stack has (ptr, len); save len, drop ptr
        instructions.append(f"local.set {tmp_len}")
        instructions.append("drop")
        instructions.append(f"local.get {tmp_len}")
        instructions.append("i64.extend_i32_u")
        return instructions

    def _translate_string_concat(
        self, arg_a: ast.Expr, arg_b: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate string_concat(a, b) → String.

        Allocates a new buffer of size len_a + len_b, copies both
        strings into it, and returns (new_ptr, total_len).
        """
        a_instrs = self.translate_expr(arg_a, env)
        b_instrs = self.translate_expr(arg_b, env)
        if a_instrs is None or b_instrs is None:
            return None

        self.needs_alloc = True

        # Locals for both strings and the result
        ptr_a = self.alloc_local("i32")
        len_a = self.alloc_local("i32")
        ptr_b = self.alloc_local("i32")
        len_b = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate string a -> (ptr, len), save to locals
        instructions.extend(a_instrs)
        instructions.append(f"local.set {len_a}")
        instructions.append(f"local.set {ptr_a}")

        # Evaluate string b -> (ptr, len), save to locals
        instructions.extend(b_instrs)
        instructions.append(f"local.set {len_b}")
        instructions.append(f"local.set {ptr_b}")

        # Allocate: total_len = len_a + len_b
        instructions.append(f"local.get {len_a}")
        instructions.append(f"local.get {len_b}")
        instructions.append("i32.add")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))

        # Copy string a: byte-by-byte loop
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_a")
        instructions.append("  loop $lp_a")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {len_a}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_a")
        instructions.append(f"    local.get {dst}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {ptr_a}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append("    i32.store8 offset=0")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_a")
        instructions.append("  end")
        instructions.append("end")

        # Copy string b: byte-by-byte loop at offset len_a
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_b")
        instructions.append("  loop $lp_b")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {len_b}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_b")
        instructions.append(f"    local.get {dst}")
        instructions.append(f"    local.get {len_a}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {ptr_b}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append("    i32.store8 offset=0")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_b")
        instructions.append("  end")
        instructions.append("end")

        # Push result (ptr, len)
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {len_a}")
        instructions.append(f"local.get {len_b}")
        instructions.append("i32.add")
        return instructions

    def _translate_string_slice(
        self,
        arg_s: ast.Expr,
        arg_start: ast.Expr,
        arg_end: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate string_slice(s, start, end) → String.

        Allocates a new buffer of size (end - start), copies the
        substring, and returns (new_ptr, new_len).  start and end
        are Int (i64) and are wrapped to i32.
        """
        s_instrs = self.translate_expr(arg_s, env)
        start_instrs = self.translate_expr(arg_start, env)
        end_instrs = self.translate_expr(arg_end, env)
        if s_instrs is None or start_instrs is None or end_instrs is None:
            return None

        self.needs_alloc = True

        ptr_s = self.alloc_local("i32")
        len_s = self.alloc_local("i32")
        start = self.alloc_local("i32")
        end = self.alloc_local("i32")
        new_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        # Suppress unused-variable warning for len_s — reserved for
        # future bounds checking
        _ = len_s

        instructions: list[str] = []

        # Evaluate string -> (ptr, len)
        instructions.extend(s_instrs)
        instructions.append(f"local.set {len_s}")
        instructions.append(f"local.set {ptr_s}")

        # Evaluate start (i64 → i32)
        instructions.extend(start_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {start}")

        # Evaluate end (i64 → i32)
        instructions.extend(end_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {end}")

        # new_len = end - start
        instructions.append(f"local.get {end}")
        instructions.append(f"local.get {start}")
        instructions.append("i32.sub")
        instructions.append(f"local.set {new_len}")

        # Allocate new buffer
        instructions.append(f"local.get {new_len}")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))

        # Copy bytes: byte-by-byte loop
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_s")
        instructions.append("  loop $lp_s")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {new_len}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_s")
        instructions.append(f"    local.get {dst}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {ptr_s}")
        instructions.append(f"    local.get {start}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append("    i32.store8 offset=0")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_s")
        instructions.append("  end")
        instructions.append("end")

        # Push result (ptr, len)
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {new_len}")
        return instructions

    def _translate_char_code(
        self,
        arg_s: ast.Expr,
        arg_idx: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate char_code(s, idx) → Nat (i64).

        Returns the byte value at the given index in the string.
        """
        s_instrs = self.translate_expr(arg_s, env)
        idx_instrs = self.translate_expr(arg_idx, env)
        if s_instrs is None or idx_instrs is None:
            return None

        ptr_s = self.alloc_local("i32")
        len_s = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        _ = len_s  # reserved for future bounds checking

        instructions: list[str] = []

        # Evaluate string -> (ptr, len)
        instructions.extend(s_instrs)
        instructions.append(f"local.set {len_s}")
        instructions.append(f"local.set {ptr_s}")

        # Evaluate index (i64 → i32)
        instructions.extend(idx_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {idx}")

        # Load byte at ptr + idx, extend to i64
        instructions.append(f"local.get {ptr_s}")
        instructions.append(f"local.get {idx}")
        instructions.append("i32.add")
        instructions.append("i32.load8_u offset=0")
        instructions.append("i64.extend_i32_u")
        return instructions

    def _translate_from_char_code(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate from_char_code(n) → String (i32_pair).

        Allocates a 1-byte string and stores the byte value.
        Inverse of char_code.
        """
        n_instrs = self.translate_expr(arg, env)
        if n_instrs is None:
            return None

        self.needs_alloc = True

        byte_val = self.alloc_local("i32")
        ptr = self.alloc_local("i32")

        ins: list[str] = []

        # Evaluate arg (Nat = i64) → i32
        ins.extend(n_instrs)
        ins.append("i32.wrap_i64")
        ins.append(f"local.set {byte_val}")

        # Allocate 1-byte buffer
        ins.append("i32.const 1")
        ins.append("call $alloc")
        ins.append(f"local.set {ptr}")
        ins.extend(gc_shadow_push(ptr))

        # Store the byte
        ins.append(f"local.get {ptr}")
        ins.append(f"local.get {byte_val}")
        ins.append("i32.store8 offset=0")

        # Result: (ptr, 1)
        ins.append(f"local.get {ptr}")
        ins.append("i32.const 1")
        return ins

    def _translate_string_repeat(
        self,
        arg_s: ast.Expr,
        arg_n: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate string_repeat(s, n) → String (i32_pair).

        Allocates len(s)*n bytes and copies the source string n times.
        """
        s_instrs = self.translate_expr(arg_s, env)
        n_instrs = self.translate_expr(arg_n, env)
        if s_instrs is None or n_instrs is None:
            return None

        self.needs_alloc = True

        ptr_s = self.alloc_local("i32")
        len_s = self.alloc_local("i32")
        count = self.alloc_local("i32")
        total_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        out_idx = self.alloc_local("i32")

        ins: list[str] = []

        # Evaluate string → (ptr, len)
        ins.extend(s_instrs)
        ins.append(f"local.set {len_s}")
        ins.append(f"local.set {ptr_s}")

        # Evaluate count (Nat = i64 → i32)
        ins.extend(n_instrs)
        ins.append("i32.wrap_i64")
        ins.append(f"local.set {count}")

        # total_len = len_s * count
        ins.append(f"local.get {len_s}")
        ins.append(f"local.get {count}")
        ins.append("i32.mul")
        ins.append(f"local.set {total_len}")

        # Allocate output buffer
        ins.append(f"local.get {total_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # Copy loop: out_idx = 0..total_len-1
        ins.append("i32.const 0")
        ins.append(f"local.set {out_idx}")
        ins.append("block $brk_sr")
        ins.append("  loop $lp_sr")
        ins.append(f"    local.get {out_idx}")
        ins.append(f"    local.get {total_len}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_sr")
        # dst[out_idx] = src[out_idx % len_s]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {out_idx}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ptr_s}")
        ins.append(f"    local.get {out_idx}")
        ins.append(f"    local.get {len_s}")
        ins.append("    i32.rem_u")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")
        ins.append(f"    local.get {out_idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {out_idx}")
        ins.append("    br $lp_sr")
        ins.append("  end")
        ins.append("end")

        # Result: (dst, total_len)
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {total_len}")
        return ins

    def _translate_to_string(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate to_string(n) → String (i32_pair).

        Converts an integer to its decimal string representation.
        Uses a temporary 20-byte stack buffer (enough for i64),
        writes digits in reverse, then allocates and copies forward.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        val = self.alloc_local("i64")
        is_neg = self.alloc_local("i32")
        buf = self.alloc_local("i32")  # temp buffer ptr
        pos = self.alloc_local("i32")  # position in buffer (from end)
        dst = self.alloc_local("i32")  # result ptr
        slen = self.alloc_local("i32")
        digit = self.alloc_local("i64")

        instructions: list[str] = []

        # Evaluate argument
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {val}")

        # Allocate a 20-byte temporary buffer for digit reversal
        instructions.append("i32.const 20")
        instructions.append("call $alloc")
        instructions.append(f"local.set {buf}")
        instructions.extend(gc_shadow_push(buf))

        # Start position at end of buffer
        instructions.append("i32.const 20")
        instructions.append(f"local.set {pos}")

        # Check for negative
        instructions.append("i32.const 0")
        instructions.append(f"local.set {is_neg}")
        instructions.append(f"local.get {val}")
        instructions.append("i64.const 0")
        instructions.append("i64.lt_s")
        instructions.append("if")
        instructions.append("  i32.const 1")
        instructions.append(f"  local.set {is_neg}")
        instructions.append("  i64.const 0")
        instructions.append(f"  local.get {val}")
        instructions.append("  i64.sub")
        instructions.append(f"  local.set {val}")
        instructions.append("end")

        # Handle zero case
        instructions.append(f"local.get {val}")
        instructions.append("i64.const 0")
        instructions.append("i64.eq")
        instructions.append("if")
        # pos--, store '0'
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append(f"  local.set {pos}")
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append("  i32.const 48")
        instructions.append("  i32.store8 offset=0")
        instructions.append("else")
        # Extract digits in reverse
        instructions.append("  block $brk_ts")
        instructions.append("  loop $lp_ts")
        instructions.append(f"    local.get {val}")
        instructions.append("    i64.const 0")
        instructions.append("    i64.le_s")
        instructions.append("    br_if $brk_ts")
        # digit = val % 10
        instructions.append(f"    local.get {val}")
        instructions.append("    i64.const 10")
        instructions.append("    i64.rem_u")
        instructions.append(f"    local.set {digit}")
        # val = val / 10
        instructions.append(f"    local.get {val}")
        instructions.append("    i64.const 10")
        instructions.append("    i64.div_u")
        instructions.append(f"    local.set {val}")
        # pos--, store digit + 48
        instructions.append(f"    local.get {pos}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.sub")
        instructions.append(f"    local.set {pos}")
        instructions.append(f"    local.get {buf}")
        instructions.append(f"    local.get {pos}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {digit}")
        instructions.append("    i32.wrap_i64")
        instructions.append("    i32.const 48")
        instructions.append("    i32.add")
        instructions.append("    i32.store8 offset=0")
        instructions.append("    br $lp_ts")
        instructions.append("  end")
        instructions.append("  end")
        instructions.append("end")

        # Prepend '-' if negative
        instructions.append(f"local.get {is_neg}")
        instructions.append("if")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append(f"  local.set {pos}")
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append("  i32.const 45")
        instructions.append("  i32.store8 offset=0")
        instructions.append("end")

        # slen = 20 - pos (number of characters written)
        instructions.append("i32.const 20")
        instructions.append(f"local.get {pos}")
        instructions.append("i32.sub")
        instructions.append(f"local.set {slen}")

        # Allocate exact-size result buffer and copy digits forward.
        # (Avoids returning an interior pointer into the temp buffer,
        # which conservative GC would not recognise as a valid root.)
        instructions.append(f"local.get {slen}")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))
        # Copy loop: dst[i] = buf[pos + i] for i in 0..slen
        ci = self.alloc_local("i32")
        instructions.append("i32.const 0")
        instructions.append(f"local.set {ci}")
        instructions.append("block $brk_cp")
        instructions.append("loop $lp_cp")
        instructions.append(f"  local.get {ci}")
        instructions.append(f"  local.get {slen}")
        instructions.append("  i32.ge_u")
        instructions.append("  br_if $brk_cp")
        # dst[ci] = buf[pos + ci]
        instructions.append(f"  local.get {dst}")
        instructions.append(f"  local.get {ci}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {ci}")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.store8 offset=0")
        # ci++
        instructions.append(f"  local.get {ci}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.add")
        instructions.append(f"  local.set {ci}")
        instructions.append("  br $lp_cp")
        instructions.append("end")
        instructions.append("end")

        # Result: (dst, slen)
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {slen}")
        return instructions

    def _translate_bool_to_string(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate bool_to_string(b) → String (i32_pair).

        Returns the interned string "true" or "false" depending on
        the boolean value.  No heap allocation needed.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        true_off, true_len = self.string_pool.intern("true")
        false_off, false_len = self.string_pool.intern("false")

        instructions: list[str] = []
        instructions.extend(arg_instrs)
        # Bool is i32: 1 = true, 0 = false
        instructions.append(f"if (result i32 i32)")
        instructions.append(f"  i32.const {true_off}")
        instructions.append(f"  i32.const {true_len}")
        instructions.append("else")
        instructions.append(f"  i32.const {false_off}")
        instructions.append(f"  i32.const {false_len}")
        instructions.append("end")
        return instructions

    def _translate_byte_to_string(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate byte_to_string(b) → String (i32_pair).

        Allocates a 1-byte buffer and stores the byte value as a
        single character.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        bval = self.alloc_local("i32")
        dst = self.alloc_local("i32")

        instructions: list[str] = []
        instructions.extend(arg_instrs)
        # Byte is i32 in WASM (unlike Nat which is i64)
        instructions.append(f"local.set {bval}")

        # Allocate 1 byte
        instructions.append("i32.const 1")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))

        # Store the byte value
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {bval}")
        instructions.append("i32.store8 offset=0")

        # Return (ptr, 1)
        instructions.append(f"local.get {dst}")
        instructions.append("i32.const 1")
        return instructions

    def _translate_float_to_string(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate float_to_string(f) → String (i32_pair).

        Converts a Float64 to its decimal string representation.
        Uses a 32-byte buffer.  Writes sign, integer digits, decimal
        point, then up to 6 fractional digits (trailing zeros trimmed,
        but at least one decimal digit kept so 42.0 stays "42.0").
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        fval = self.alloc_local("f64")
        ival = self.alloc_local("i64")
        buf = self.alloc_local("i32")
        pos = self.alloc_local("i32")   # write position (forward)
        is_neg = self.alloc_local("i32")
        digit = self.alloc_local("i64")
        # For integer-part digit reversal
        tbuf = self.alloc_local("i32")  # temp buffer for int digits
        tpos = self.alloc_local("i32")  # position in temp buffer
        tlen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        frac_val = self.alloc_local("i64")

        instructions: list[str] = []

        # Evaluate argument
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {fval}")

        # Allocate 32-byte output buffer
        instructions.append("i32.const 32")
        instructions.append("call $alloc")
        instructions.append(f"local.set {buf}")
        instructions.extend(gc_shadow_push(buf))
        instructions.append("i32.const 0")
        instructions.append(f"local.set {pos}")

        # Check for negative
        instructions.append("i32.const 0")
        instructions.append(f"local.set {is_neg}")
        instructions.append(f"local.get {fval}")
        instructions.append("f64.const 0")
        instructions.append("f64.lt")
        instructions.append("if")
        instructions.append("  i32.const 1")
        instructions.append(f"  local.set {is_neg}")
        instructions.append(f"  local.get {fval}")
        instructions.append("  f64.neg")
        instructions.append(f"  local.set {fval}")
        instructions.append("end")

        # Write '-' if negative
        instructions.append(f"local.get {is_neg}")
        instructions.append("if")
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append("  i32.const 45")  # '-'
        instructions.append("  i32.store8 offset=0")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.add")
        instructions.append(f"  local.set {pos}")
        instructions.append("end")

        # Extract integer part: ival = i64.trunc_f64_s(fval)
        instructions.append(f"local.get {fval}")
        instructions.append("i64.trunc_f64_s")
        instructions.append(f"local.set {ival}")

        # Write integer digits using a temp buffer (reverse then copy)
        # Allocate 20-byte temp buffer for int digits
        instructions.append("i32.const 20")
        instructions.append("call $alloc")
        instructions.append(f"local.set {tbuf}")
        instructions.extend(gc_shadow_push(tbuf))
        instructions.append("i32.const 20")
        instructions.append(f"local.set {tpos}")

        # Handle zero integer part
        instructions.append(f"local.get {ival}")
        instructions.append("i64.const 0")
        instructions.append("i64.eq")
        instructions.append("if")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append(f"  local.set {tpos}")
        instructions.append(f"  local.get {tbuf}")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.add")
        instructions.append("  i32.const 48")
        instructions.append("  i32.store8 offset=0")
        instructions.append("else")
        # Extract digits in reverse
        instructions.append("  block $brk_fi")
        instructions.append("  loop $lp_fi")
        instructions.append(f"    local.get {ival}")
        instructions.append("    i64.const 0")
        instructions.append("    i64.le_s")
        instructions.append("    br_if $brk_fi")
        instructions.append(f"    local.get {ival}")
        instructions.append("    i64.const 10")
        instructions.append("    i64.rem_u")
        instructions.append(f"    local.set {digit}")
        instructions.append(f"    local.get {ival}")
        instructions.append("    i64.const 10")
        instructions.append("    i64.div_u")
        instructions.append(f"    local.set {ival}")
        instructions.append(f"    local.get {tpos}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.sub")
        instructions.append(f"    local.set {tpos}")
        instructions.append(f"    local.get {tbuf}")
        instructions.append(f"    local.get {tpos}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {digit}")
        instructions.append("    i32.wrap_i64")
        instructions.append("    i32.const 48")
        instructions.append("    i32.add")
        instructions.append("    i32.store8 offset=0")
        instructions.append("    br $lp_fi")
        instructions.append("  end")
        instructions.append("  end")
        instructions.append("end")

        # Copy integer digits from tbuf[tpos..20] to buf[pos..]
        # tlen = 20 - tpos
        instructions.append("i32.const 20")
        instructions.append(f"local.get {tpos}")
        instructions.append("i32.sub")
        instructions.append(f"local.set {tlen}")
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_cp")
        instructions.append("loop $lp_cp")
        instructions.append(f"  local.get {idx}")
        instructions.append(f"  local.get {tlen}")
        instructions.append("  i32.ge_u")
        instructions.append("  br_if $brk_cp")
        # buf[pos + idx] = tbuf[tpos + idx]
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {tbuf}")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.store8 offset=0")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.add")
        instructions.append(f"  local.set {idx}")
        instructions.append("  br $lp_cp")
        instructions.append("end")
        instructions.append("end")
        # pos += tlen
        instructions.append(f"local.get {pos}")
        instructions.append(f"local.get {tlen}")
        instructions.append("i32.add")
        instructions.append(f"local.set {pos}")

        # Write decimal point
        instructions.append(f"local.get {buf}")
        instructions.append(f"local.get {pos}")
        instructions.append("i32.add")
        instructions.append("i32.const 46")  # '.'
        instructions.append("i32.store8 offset=0")
        instructions.append(f"local.get {pos}")
        instructions.append("i32.const 1")
        instructions.append("i32.add")
        instructions.append(f"local.set {pos}")

        # Fractional part: frac = (fval - floor(fval)) * 1_000_000
        # Re-extract integer part as f64 for subtraction
        instructions.append(f"local.get {fval}")
        instructions.append(f"local.get {fval}")
        instructions.append("f64.floor")
        instructions.append("f64.sub")
        instructions.append("f64.const 1000000")
        instructions.append("f64.mul")
        # Round to nearest integer
        instructions.append("f64.const 0.5")
        instructions.append("f64.add")
        instructions.append("i64.trunc_f64_s")
        instructions.append(f"local.set {frac_val}")

        # Write exactly 6 fractional digits (will trim trailing zeros after)
        # We write them in reverse into tbuf, then copy forward
        instructions.append("i32.const 6")
        instructions.append(f"local.set {tlen}")
        instructions.append("i32.const 6")
        instructions.append(f"local.set {tpos}")

        instructions.append("block $brk_fd")
        instructions.append("loop $lp_fd")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.const 0")
        instructions.append("  i32.le_s")
        instructions.append("  br_if $brk_fd")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append(f"  local.set {tpos}")
        instructions.append(f"  local.get {tbuf}")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {frac_val}")
        instructions.append("  i64.const 10")
        instructions.append("  i64.rem_u")
        instructions.append("  i32.wrap_i64")
        instructions.append("  i32.const 48")
        instructions.append("  i32.add")
        instructions.append("  i32.store8 offset=0")
        instructions.append(f"  local.get {frac_val}")
        instructions.append("  i64.const 10")
        instructions.append("  i64.div_u")
        instructions.append(f"  local.set {frac_val}")
        instructions.append("  br $lp_fd")
        instructions.append("end")
        instructions.append("end")

        # Trim trailing zeros: tlen = 6, but keep at least 1 digit
        # Scan from position 5 down to 1
        instructions.append("block $brk_tz")
        instructions.append("loop $lp_tz")
        # If tlen <= 1, stop (keep at least 1 fractional digit)
        instructions.append(f"  local.get {tlen}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.le_s")
        instructions.append("  br_if $brk_tz")
        # Check if tbuf[tlen - 1] == '0' (48)
        instructions.append(f"  local.get {tbuf}")
        instructions.append(f"  local.get {tlen}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.const 48")
        instructions.append("  i32.ne")
        instructions.append("  br_if $brk_tz")
        instructions.append(f"  local.get {tlen}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append(f"  local.set {tlen}")
        instructions.append("  br $lp_tz")
        instructions.append("end")
        instructions.append("end")

        # Copy tlen fractional digits from tbuf[0..tlen] to buf[pos..]
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_cf")
        instructions.append("loop $lp_cf")
        instructions.append(f"  local.get {idx}")
        instructions.append(f"  local.get {tlen}")
        instructions.append("  i32.ge_u")
        instructions.append("  br_if $brk_cf")
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {tbuf}")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.store8 offset=0")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.add")
        instructions.append(f"  local.set {idx}")
        instructions.append("  br $lp_cf")
        instructions.append("end")
        instructions.append("end")

        # Final length = pos + tlen
        instructions.append(f"local.get {pos}")
        instructions.append(f"local.get {tlen}")
        instructions.append("i32.add")
        instructions.append(f"local.set {pos}")

        # Return (buf, pos) where pos is now the total length
        instructions.append(f"local.get {buf}")
        instructions.append(f"local.get {pos}")
        return instructions

    def _translate_strip(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate strip(s) → String (i32_pair).

        Trims leading and trailing ASCII whitespace (space, tab, CR, LF).
        Allocates a new buffer and copies the trimmed content to avoid
        returning an interior pointer (which conservative GC cannot track).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        start = self.alloc_local("i32")
        end = self.alloc_local("i32")
        byte = self.alloc_local("i32")
        new_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate string -> (ptr, len)
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {slen}")
        instructions.append(f"local.set {ptr}")

        # start = 0
        instructions.append("i32.const 0")
        instructions.append(f"local.set {start}")

        # Scan forward: skip leading whitespace
        instructions.append("block $brk_lw")
        instructions.append("  loop $lp_lw")
        instructions.append(f"    local.get {start}")
        instructions.append(f"    local.get {slen}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_lw")
        instructions.append(f"    local.get {ptr}")
        instructions.append(f"    local.get {start}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append(f"    local.set {byte}")
        # Check if whitespace: space(32), tab(9), CR(13), LF(10)
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 32")
        instructions.append("    i32.eq")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 9")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 10")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 13")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append("    i32.eqz")
        instructions.append("    br_if $brk_lw")
        instructions.append(f"    local.get {start}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {start}")
        instructions.append("    br $lp_lw")
        instructions.append("  end")
        instructions.append("end")

        # end = len
        instructions.append(f"local.get {slen}")
        instructions.append(f"local.set {end}")

        # Scan backward: skip trailing whitespace
        instructions.append("block $brk_tw")
        instructions.append("  loop $lp_tw")
        instructions.append(f"    local.get {end}")
        instructions.append(f"    local.get {start}")
        instructions.append("    i32.le_u")
        instructions.append("    br_if $brk_tw")
        instructions.append(f"    local.get {ptr}")
        instructions.append(f"    local.get {end}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.sub")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append(f"    local.set {byte}")
        # Check if whitespace
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 32")
        instructions.append("    i32.eq")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 9")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 10")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 13")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append("    i32.eqz")
        instructions.append("    br_if $brk_tw")
        instructions.append(f"    local.get {end}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.sub")
        instructions.append(f"    local.set {end}")
        instructions.append("    br $lp_tw")
        instructions.append("  end")
        instructions.append("end")

        # new_len = end - start
        instructions.append(f"local.get {end}")
        instructions.append(f"local.get {start}")
        instructions.append("i32.sub")
        instructions.append(f"local.set {new_len}")

        # Allocate new buffer and copy trimmed content
        instructions.append(f"local.get {new_len}")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))

        # Copy loop: dst[i] = ptr[start + i] for i in 0..new_len
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_st")
        instructions.append("loop $lp_st")
        instructions.append(f"  local.get {idx}")
        instructions.append(f"  local.get {new_len}")
        instructions.append("  i32.ge_u")
        instructions.append("  br_if $brk_st")
        instructions.append(f"  local.get {dst}")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {ptr}")
        instructions.append(f"  local.get {start}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.store8 offset=0")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.add")
        instructions.append(f"  local.set {idx}")
        instructions.append("  br $lp_st")
        instructions.append("end")
        instructions.append("end")

        # Result: (dst, new_len)
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {new_len}")
        return instructions

    # -----------------------------------------------------------------
    # String search builtins
    # -----------------------------------------------------------------

    def _translate_starts_with(
        self,
        arg_h: ast.Expr,
        arg_n: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate starts_with(haystack, needle) → Bool (i32).

        Returns 1 if haystack starts with needle, 0 otherwise.
        Compares prefix bytes; empty needle always matches.
        """
        h_instrs = self.translate_expr(arg_h, env)
        n_instrs = self.translate_expr(arg_n, env)
        if h_instrs is None or n_instrs is None:
            return None

        ptr_h = self.alloc_local("i32")
        len_h = self.alloc_local("i32")
        ptr_n = self.alloc_local("i32")
        len_n = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        ins: list[str] = []

        # Evaluate haystack → (ptr, len)
        ins.extend(h_instrs)
        ins.append(f"local.set {len_h}")
        ins.append(f"local.set {ptr_h}")

        # Evaluate needle → (ptr, len)
        ins.extend(n_instrs)
        ins.append(f"local.set {len_n}")
        ins.append(f"local.set {ptr_n}")

        # block $done_sw produces i32 result
        ins.append("block $done_sw (result i32)")

        # If needle longer than haystack → false
        ins.append(f"  local.get {len_n}")
        ins.append(f"  local.get {len_h}")
        ins.append("  i32.gt_u")
        ins.append("  if")
        ins.append("    i32.const 0")
        ins.append("    br $done_sw")
        ins.append("  end")

        # Compare loop
        ins.append("  i32.const 0")
        ins.append(f"  local.set {idx}")
        ins.append("  block $brk_sw")
        ins.append("    loop $lp_sw")
        ins.append(f"      local.get {idx}")
        ins.append(f"      local.get {len_n}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_sw")
        # Compare bytes
        ins.append(f"      local.get {ptr_h}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append(f"      local.get {ptr_n}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append("      i32.ne")
        ins.append("      if")
        ins.append("        i32.const 0")
        ins.append("        br $done_sw")
        ins.append("      end")
        # idx++
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("      br $lp_sw")
        ins.append("    end")
        ins.append("  end")

        # All bytes matched
        ins.append("  i32.const 1")
        ins.append("end")  # $done_sw

        return ins

    def _translate_ends_with(
        self,
        arg_h: ast.Expr,
        arg_n: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate ends_with(haystack, needle) → Bool (i32).

        Returns 1 if haystack ends with needle, 0 otherwise.
        Compares suffix bytes at offset (len_h - len_n).
        """
        h_instrs = self.translate_expr(arg_h, env)
        n_instrs = self.translate_expr(arg_n, env)
        if h_instrs is None or n_instrs is None:
            return None

        ptr_h = self.alloc_local("i32")
        len_h = self.alloc_local("i32")
        ptr_n = self.alloc_local("i32")
        len_n = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        offset = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(h_instrs)
        ins.append(f"local.set {len_h}")
        ins.append(f"local.set {ptr_h}")

        ins.extend(n_instrs)
        ins.append(f"local.set {len_n}")
        ins.append(f"local.set {ptr_n}")

        ins.append("block $done_ew (result i32)")

        # If needle longer than haystack → false
        ins.append(f"  local.get {len_n}")
        ins.append(f"  local.get {len_h}")
        ins.append("  i32.gt_u")
        ins.append("  if")
        ins.append("    i32.const 0")
        ins.append("    br $done_ew")
        ins.append("  end")

        # offset = len_h - len_n
        ins.append(f"  local.get {len_h}")
        ins.append(f"  local.get {len_n}")
        ins.append("  i32.sub")
        ins.append(f"  local.set {offset}")

        # Compare loop
        ins.append("  i32.const 0")
        ins.append(f"  local.set {idx}")
        ins.append("  block $brk_ew")
        ins.append("    loop $lp_ew")
        ins.append(f"      local.get {idx}")
        ins.append(f"      local.get {len_n}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_ew")
        # Compare haystack[offset + idx] vs needle[idx]
        ins.append(f"      local.get {ptr_h}")
        ins.append(f"      local.get {offset}")
        ins.append("      i32.add")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append(f"      local.get {ptr_n}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append("      i32.ne")
        ins.append("      if")
        ins.append("        i32.const 0")
        ins.append("        br $done_ew")
        ins.append("      end")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("      br $lp_ew")
        ins.append("    end")
        ins.append("  end")

        ins.append("  i32.const 1")
        ins.append("end")

        return ins

    def _translate_string_contains(
        self,
        arg_h: ast.Expr,
        arg_n: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate string_contains(haystack, needle) → Bool (i32).

        Naive O(n*m) substring search.  Returns 1 if needle is found
        anywhere in haystack, 0 otherwise.  Empty needle always matches.
        """
        h_instrs = self.translate_expr(arg_h, env)
        n_instrs = self.translate_expr(arg_n, env)
        if h_instrs is None or n_instrs is None:
            return None

        ptr_h = self.alloc_local("i32")
        len_h = self.alloc_local("i32")
        ptr_n = self.alloc_local("i32")
        len_n = self.alloc_local("i32")
        i = self.alloc_local("i32")
        j = self.alloc_local("i32")
        limit = self.alloc_local("i32")
        matched = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(h_instrs)
        ins.append(f"local.set {len_h}")
        ins.append(f"local.set {ptr_h}")

        ins.extend(n_instrs)
        ins.append(f"local.set {len_n}")
        ins.append(f"local.set {ptr_n}")

        ins.append("block $done_sc (result i32)")

        # Empty needle → true
        ins.append(f"  local.get {len_n}")
        ins.append("  i32.eqz")
        ins.append("  if")
        ins.append("    i32.const 1")
        ins.append("    br $done_sc")
        ins.append("  end")

        # Needle longer than haystack → false
        ins.append(f"  local.get {len_n}")
        ins.append(f"  local.get {len_h}")
        ins.append("  i32.gt_u")
        ins.append("  if")
        ins.append("    i32.const 0")
        ins.append("    br $done_sc")
        ins.append("  end")

        # limit = len_h - len_n + 1
        ins.append(f"  local.get {len_h}")
        ins.append(f"  local.get {len_n}")
        ins.append("  i32.sub")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {limit}")

        # Outer loop: try each starting position
        ins.append("  i32.const 0")
        ins.append(f"  local.set {i}")
        ins.append("  block $brk_sco")
        ins.append("    loop $lp_sco")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {limit}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_sco")

        # Inner loop: compare needle bytes
        ins.append("      i32.const 0")
        ins.append(f"      local.set {j}")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {matched}")
        ins.append("      block $brk_sci")
        ins.append("        loop $lp_sci")
        ins.append(f"          local.get {j}")
        ins.append(f"          local.get {len_n}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_sci")
        # Compare haystack[i+j] vs needle[j]
        ins.append(f"          local.get {ptr_h}")
        ins.append(f"          local.get {i}")
        ins.append("          i32.add")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append(f"          local.get {ptr_n}")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.ne")
        ins.append("          if")
        ins.append("            i32.const 0")
        ins.append(f"            local.set {matched}")
        ins.append("            br $brk_sci")
        ins.append("          end")
        ins.append(f"          local.get {j}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {j}")
        ins.append("          br $lp_sci")
        ins.append("        end")
        ins.append("      end")

        # If matched, return true
        ins.append(f"      local.get {matched}")
        ins.append("      if")
        ins.append("        i32.const 1")
        ins.append("        br $done_sc")
        ins.append("      end")

        # i++
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("      br $lp_sco")
        ins.append("    end")
        ins.append("  end")

        # No match found
        ins.append("  i32.const 0")
        ins.append("end")

        return ins

    # -----------------------------------------------------------------
    # String transformation builtins
    # -----------------------------------------------------------------

    def _translate_to_upper(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate to_upper(s) → String (i32_pair).

        Allocates a new buffer of the same size and converts ASCII
        lowercase letters (97–122) to uppercase by subtracting 32.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        byte = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Allocate same-size buffer
        ins.append(f"local.get {slen}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # Transform loop
        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("block $brk_tu")
        ins.append("  loop $lp_tu")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_tu")
        # Load byte
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {byte}")
        # Check: 97 <= byte <= 122 (lowercase ASCII)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 97")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 122")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    if")
        # Store byte - 32
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 32")
        ins.append("      i32.sub")
        ins.append("      i32.store8 offset=0")
        ins.append("    else")
        # Store byte as-is
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.store8 offset=0")
        ins.append("    end")
        # idx++
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_tu")
        ins.append("  end")
        ins.append("end")

        # Result: (dst, slen)
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {slen}")
        return ins

    def _translate_to_lower(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate to_lower(s) → String (i32_pair).

        Allocates a new buffer of the same size and converts ASCII
        uppercase letters (65–90) to lowercase by adding 32.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        byte = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        ins.append(f"local.get {slen}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("block $brk_tl")
        ins.append("  loop $lp_tl")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_tl")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {byte}")
        # Check: 65 <= byte <= 90 (uppercase ASCII)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 65")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 90")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    if")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 32")
        ins.append("      i32.add")
        ins.append("      i32.store8 offset=0")
        ins.append("    else")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.store8 offset=0")
        ins.append("    end")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_tl")
        ins.append("  end")
        ins.append("end")

        ins.append(f"local.get {dst}")
        ins.append(f"local.get {slen}")
        return ins

    def _translate_index_of(
        self,
        arg_h: ast.Expr,
        arg_n: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate index_of(haystack, needle) → Option<Nat> (i32 ptr).

        Returns a heap-allocated Option<Nat>:
          Some(Nat): [tag=1 : i32] [pad 4] [value : i64]  (16 bytes)
          None:      [tag=0 : i32] [pad 12]                (16 bytes)
        """
        h_instrs = self.translate_expr(arg_h, env)
        n_instrs = self.translate_expr(arg_n, env)
        if h_instrs is None or n_instrs is None:
            return None

        self.needs_alloc = True

        ptr_h = self.alloc_local("i32")
        len_h = self.alloc_local("i32")
        ptr_n = self.alloc_local("i32")
        len_n = self.alloc_local("i32")
        i = self.alloc_local("i32")
        j = self.alloc_local("i32")
        limit = self.alloc_local("i32")
        matched = self.alloc_local("i32")
        out = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(h_instrs)
        ins.append(f"local.set {len_h}")
        ins.append(f"local.set {ptr_h}")

        ins.extend(n_instrs)
        ins.append(f"local.set {len_n}")
        ins.append(f"local.set {ptr_n}")

        # Allocate Option<Nat> (16 bytes)
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.set {out}")

        ins.append("block $done_io")

        # Empty needle → Some(0)
        ins.append(f"  local.get {len_n}")
        ins.append("  i32.eqz")
        ins.append("  if")
        ins.append(f"    local.get {out}")
        ins.append("    i32.const 1")
        ins.append("    i32.store")              # tag = 1 (Some)
        ins.extend(f"    {x}" for x in gc_shadow_push(out))
        ins.append(f"    local.get {out}")
        ins.append("    i64.const 0")
        ins.append("    i64.store offset=8")     # value = 0
        ins.append("    br $done_io")
        ins.append("  end")

        # Needle longer than haystack → None
        ins.append(f"  local.get {len_n}")
        ins.append(f"  local.get {len_h}")
        ins.append("  i32.gt_u")
        ins.append("  if")
        ins.append(f"    local.get {out}")
        ins.append("    i32.const 0")
        ins.append("    i32.store")              # tag = 0 (None)
        ins.extend(f"    {x}" for x in gc_shadow_push(out))
        ins.append("    br $done_io")
        ins.append("  end")

        # limit = len_h - len_n + 1
        ins.append(f"  local.get {len_h}")
        ins.append(f"  local.get {len_n}")
        ins.append("  i32.sub")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {limit}")

        # Outer loop
        ins.append("  i32.const 0")
        ins.append(f"  local.set {i}")
        ins.append("  block $brk_ioo")
        ins.append("    loop $lp_ioo")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {limit}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_ioo")

        # Inner loop
        ins.append("      i32.const 0")
        ins.append(f"      local.set {j}")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {matched}")
        ins.append("      block $brk_ioi")
        ins.append("        loop $lp_ioi")
        ins.append(f"          local.get {j}")
        ins.append(f"          local.get {len_n}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_ioi")
        ins.append(f"          local.get {ptr_h}")
        ins.append(f"          local.get {i}")
        ins.append("          i32.add")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append(f"          local.get {ptr_n}")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.ne")
        ins.append("          if")
        ins.append("            i32.const 0")
        ins.append(f"            local.set {matched}")
        ins.append("            br $brk_ioi")
        ins.append("          end")
        ins.append(f"          local.get {j}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {j}")
        ins.append("          br $lp_ioi")
        ins.append("        end")
        ins.append("      end")

        # If matched → Some(i)
        ins.append(f"      local.get {matched}")
        ins.append("      if")
        ins.append(f"        local.get {out}")
        ins.append("        i32.const 1")
        ins.append("        i32.store")          # tag = 1 (Some)
        ins.extend(f"        {x}" for x in gc_shadow_push(out))
        ins.append(f"        local.get {out}")
        ins.append(f"        local.get {i}")
        ins.append("        i64.extend_i32_u")
        ins.append("        i64.store offset=8") # value = i
        ins.append("        br $done_io")
        ins.append("      end")

        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("      br $lp_ioo")
        ins.append("    end")
        ins.append("  end")

        # No match → None
        ins.append(f"  local.get {out}")
        ins.append("  i32.const 0")
        ins.append("  i32.store")                # tag = 0 (None)
        ins.extend(f"  {x}" for x in gc_shadow_push(out))

        ins.append("end")  # $done_io

        ins.append(f"local.get {out}")
        return ins

    def _translate_replace(
        self,
        arg_h: ast.Expr,
        arg_n: ast.Expr,
        arg_r: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate replace(haystack, needle, replacement) → String.

        Two-pass algorithm:
        1. Count non-overlapping occurrences of needle.
        2. Allocate result buffer and copy with replacements.
        Empty needle returns a copy of the haystack unchanged.
        """
        h_instrs = self.translate_expr(arg_h, env)
        n_instrs = self.translate_expr(arg_n, env)
        r_instrs = self.translate_expr(arg_r, env)
        if h_instrs is None or n_instrs is None or r_instrs is None:
            return None

        self.needs_alloc = True

        ptr_h = self.alloc_local("i32")
        len_h = self.alloc_local("i32")
        ptr_n = self.alloc_local("i32")
        len_n = self.alloc_local("i32")
        ptr_r = self.alloc_local("i32")
        len_r = self.alloc_local("i32")
        count = self.alloc_local("i32")
        i = self.alloc_local("i32")
        j = self.alloc_local("i32")
        matched = self.alloc_local("i32")
        new_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        out_idx = self.alloc_local("i32")
        copy_idx = self.alloc_local("i32")

        ins: list[str] = []

        # Evaluate all three strings
        ins.extend(h_instrs)
        ins.append(f"local.set {len_h}")
        ins.append(f"local.set {ptr_h}")
        ins.extend(n_instrs)
        ins.append(f"local.set {len_n}")
        ins.append(f"local.set {ptr_n}")
        ins.extend(r_instrs)
        ins.append(f"local.set {len_r}")
        ins.append(f"local.set {ptr_r}")

        # Wrap main computation in a block so the empty-needle edge case
        # can skip it with br instead of return (return would exit the
        # enclosing function, breaking subexpressions like length(replace(...))).
        ins.append("block $rp_main")

        # Edge case: empty needle → copy haystack
        ins.append(f"local.get {len_n}")
        ins.append("i32.eqz")
        ins.append("if")
        # Allocate and copy haystack as-is
        ins.append(f"  local.get {len_h}")
        ins.append("  call $alloc")
        ins.append(f"  local.set {dst}")
        ins.extend(f"  {x}" for x in gc_shadow_push(dst))
        ins.append("  i32.const 0")
        ins.append(f"  local.set {i}")
        ins.append("  block $brk_rce")
        ins.append("    loop $lp_rce")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_h}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_rce")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append(f"      local.get {ptr_h}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("      br $lp_rce")
        ins.append("    end")
        ins.append("  end")
        ins.append(f"  local.get {len_h}")
        ins.append(f"  local.set {new_len}")
        ins.append("  br $rp_main")
        ins.append("end")

        # ---- Pass 1: count occurrences ----
        ins.append("i32.const 0")
        ins.append(f"local.set {count}")
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")

        ins.append("block $brk_rp1")
        ins.append("  loop $lp_rp1")
        # i + len_n > len_h → break
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {len_n}")
        ins.append("    i32.add")
        ins.append(f"    local.get {len_h}")
        ins.append("    i32.gt_u")
        ins.append("    br_if $brk_rp1")
        # Inner: compare needle
        ins.append("    i32.const 0")
        ins.append(f"    local.set {j}")
        ins.append("    i32.const 1")
        ins.append(f"    local.set {matched}")
        ins.append("    block $brk_rp1i")
        ins.append("      loop $lp_rp1i")
        ins.append(f"        local.get {j}")
        ins.append(f"        local.get {len_n}")
        ins.append("        i32.ge_u")
        ins.append("        br_if $brk_rp1i")
        ins.append(f"        local.get {ptr_h}")
        ins.append(f"        local.get {i}")
        ins.append("        i32.add")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append(f"        local.get {ptr_n}")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append("        i32.ne")
        ins.append("        if")
        ins.append("          i32.const 0")
        ins.append(f"          local.set {matched}")
        ins.append("          br $brk_rp1i")
        ins.append("        end")
        ins.append(f"        local.get {j}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {j}")
        ins.append("        br $lp_rp1i")
        ins.append("      end")
        ins.append("    end")
        # If matched: count++, i += len_n; else i++
        ins.append(f"    local.get {matched}")
        ins.append("    if")
        ins.append(f"      local.get {count}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {count}")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_n}")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    else")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    end")
        ins.append("    br $lp_rp1")
        ins.append("  end")
        ins.append("end")

        # Compute new_len = len_h - count * len_n + count * len_r
        ins.append(f"local.get {len_h}")
        ins.append(f"local.get {count}")
        ins.append(f"local.get {len_n}")
        ins.append("i32.mul")
        ins.append("i32.sub")
        ins.append(f"local.get {count}")
        ins.append(f"local.get {len_r}")
        ins.append("i32.mul")
        ins.append("i32.add")
        ins.append(f"local.set {new_len}")

        # Allocate result
        ins.append(f"local.get {new_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # ---- Pass 2: copy with replacements ----
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {out_idx}")

        ins.append("block $brk_rp2")
        ins.append("  loop $lp_rp2")
        # i >= len_h → break
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {len_h}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_rp2")

        # Check if needle matches at position i (only if i+len_n <= len_h)
        ins.append("    i32.const 0")
        ins.append(f"    local.set {matched}")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {len_n}")
        ins.append("    i32.add")
        ins.append(f"    local.get {len_h}")
        ins.append("    i32.le_u")
        ins.append("    if")
        ins.append("      i32.const 0")
        ins.append(f"      local.set {j}")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {matched}")
        ins.append("      block $brk_rp2i")
        ins.append("        loop $lp_rp2i")
        ins.append(f"          local.get {j}")
        ins.append(f"          local.get {len_n}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_rp2i")
        ins.append(f"          local.get {ptr_h}")
        ins.append(f"          local.get {i}")
        ins.append("          i32.add")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append(f"          local.get {ptr_n}")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.ne")
        ins.append("          if")
        ins.append("            i32.const 0")
        ins.append(f"            local.set {matched}")
        ins.append("            br $brk_rp2i")
        ins.append("          end")
        ins.append(f"          local.get {j}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {j}")
        ins.append("          br $lp_rp2i")
        ins.append("        end")
        ins.append("      end")
        ins.append("    end")

        # If matched: copy replacement, advance i by len_n
        ins.append(f"    local.get {matched}")
        ins.append("    if")
        # Copy replacement bytes
        ins.append("      i32.const 0")
        ins.append(f"      local.set {copy_idx}")
        ins.append("      block $brk_rpc")
        ins.append("        loop $lp_rpc")
        ins.append(f"          local.get {copy_idx}")
        ins.append(f"          local.get {len_r}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_rpc")
        ins.append(f"          local.get {dst}")
        ins.append(f"          local.get {out_idx}")
        ins.append("          i32.add")
        ins.append(f"          local.get {ptr_r}")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.store8 offset=0")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {copy_idx}")
        ins.append(f"          local.get {out_idx}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {out_idx}")
        ins.append("          br $lp_rpc")
        ins.append("        end")
        ins.append("      end")
        # Advance i by len_n
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_n}")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    else")
        # Copy one byte from haystack
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {out_idx}")
        ins.append("      i32.add")
        ins.append(f"      local.get {ptr_h}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {out_idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {out_idx}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    end")
        ins.append("    br $lp_rp2")
        ins.append("  end")
        ins.append("end")

        ins.append("end")  # end $rp_main

        # Result: (dst, new_len)
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {new_len}")
        return ins

    def _translate_split(
        self,
        arg_s: ast.Expr,
        arg_d: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate split(string, delimiter) → Array<String> (i32_pair).

        Two-pass algorithm:
        1. Count delimiter occurrences to determine segment count.
        2. Allocate array buffer (seg_count * 8 bytes), then for each
           segment allocate a string buffer and copy bytes.
        Returns (arr_ptr, seg_count).
        """
        s_instrs = self.translate_expr(arg_s, env)
        d_instrs = self.translate_expr(arg_d, env)
        if s_instrs is None or d_instrs is None:
            return None

        self.needs_alloc = True

        ptr_s = self.alloc_local("i32")
        len_s = self.alloc_local("i32")
        ptr_d = self.alloc_local("i32")
        len_d = self.alloc_local("i32")
        count = self.alloc_local("i32")
        seg_count = self.alloc_local("i32")
        arr = self.alloc_local("i32")
        seg_idx = self.alloc_local("i32")
        seg_start = self.alloc_local("i32")
        i = self.alloc_local("i32")
        j = self.alloc_local("i32")
        matched = self.alloc_local("i32")
        seg_len = self.alloc_local("i32")
        seg_ptr = self.alloc_local("i32")
        copy_idx = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(s_instrs)
        ins.append(f"local.set {len_s}")
        ins.append(f"local.set {ptr_s}")
        ins.extend(d_instrs)
        ins.append(f"local.set {len_d}")
        ins.append(f"local.set {ptr_d}")

        # Wrap main computation in a block so the empty-delimiter edge case
        # can skip it with br instead of return (return would exit the
        # enclosing function, breaking subexpressions like length(split(...))).
        ins.append("block $sp_main")

        # Edge case: empty delimiter → single-element array
        ins.append(f"local.get {len_d}")
        ins.append("i32.eqz")
        ins.append("if")
        # Allocate array of 1 element (8 bytes)
        ins.append("  i32.const 8")
        ins.append("  call $alloc")
        ins.append(f"  local.set {arr}")
        ins.extend(f"  {x}" for x in gc_shadow_push(arr))
        # Allocate copy of the string
        ins.append(f"  local.get {len_s}")
        ins.append("  call $alloc")
        ins.append(f"  local.set {seg_ptr}")
        ins.extend(f"  {x}" for x in gc_shadow_push(seg_ptr))
        # Copy string bytes
        ins.append("  i32.const 0")
        ins.append(f"  local.set {i}")
        ins.append("  block $brk_spe")
        ins.append("    loop $lp_spe")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_s}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_spe")
        ins.append(f"      local.get {seg_ptr}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append(f"      local.get {ptr_s}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("      br $lp_spe")
        ins.append("    end")
        ins.append("  end")
        # Store (seg_ptr, len_s) at arr[0]
        ins.append(f"  local.get {arr}")
        ins.append(f"  local.get {seg_ptr}")
        ins.append("  i32.store offset=0")
        ins.append(f"  local.get {arr}")
        ins.append(f"  local.get {len_s}")
        ins.append("  i32.store offset=4")
        # Set seg_count = 1, skip main computation
        ins.append("  i32.const 1")
        ins.append(f"  local.set {seg_count}")
        ins.append("  br $sp_main")
        ins.append("end")

        # ---- Pass 1: count delimiter occurrences ----
        ins.append("i32.const 0")
        ins.append(f"local.set {count}")
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("block $brk_sp1")
        ins.append("  loop $lp_sp1")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {len_d}")
        ins.append("    i32.add")
        ins.append(f"    local.get {len_s}")
        ins.append("    i32.gt_u")
        ins.append("    br_if $brk_sp1")
        # Inner: compare delimiter
        ins.append("    i32.const 0")
        ins.append(f"    local.set {j}")
        ins.append("    i32.const 1")
        ins.append(f"    local.set {matched}")
        ins.append("    block $brk_sp1i")
        ins.append("      loop $lp_sp1i")
        ins.append(f"        local.get {j}")
        ins.append(f"        local.get {len_d}")
        ins.append("        i32.ge_u")
        ins.append("        br_if $brk_sp1i")
        ins.append(f"        local.get {ptr_s}")
        ins.append(f"        local.get {i}")
        ins.append("        i32.add")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append(f"        local.get {ptr_d}")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append("        i32.ne")
        ins.append("        if")
        ins.append("          i32.const 0")
        ins.append(f"          local.set {matched}")
        ins.append("          br $brk_sp1i")
        ins.append("        end")
        ins.append(f"        local.get {j}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {j}")
        ins.append("        br $lp_sp1i")
        ins.append("      end")
        ins.append("    end")
        ins.append(f"    local.get {matched}")
        ins.append("    if")
        ins.append(f"      local.get {count}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {count}")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_d}")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    else")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    end")
        ins.append("    br $lp_sp1")
        ins.append("  end")
        ins.append("end")

        # seg_count = count + 1
        ins.append(f"local.get {count}")
        ins.append("i32.const 1")
        ins.append("i32.add")
        ins.append(f"local.set {seg_count}")

        # Allocate array: seg_count * 8 bytes
        ins.append(f"local.get {seg_count}")
        ins.append("i32.const 8")
        ins.append("i32.mul")
        ins.append("call $alloc")
        ins.append(f"local.set {arr}")
        ins.extend(gc_shadow_push(arr))

        # ---- Pass 2: fill segments ----
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {seg_idx}")
        ins.append("i32.const 0")
        ins.append(f"local.set {seg_start}")

        ins.append("block $brk_sp2")
        ins.append("  loop $lp_sp2")
        # Check if i + len_d > len_s → break
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {len_d}")
        ins.append("    i32.add")
        ins.append(f"    local.get {len_s}")
        ins.append("    i32.gt_u")
        ins.append("    br_if $brk_sp2")
        # Inner: compare delimiter
        ins.append("    i32.const 0")
        ins.append(f"    local.set {j}")
        ins.append("    i32.const 1")
        ins.append(f"    local.set {matched}")
        ins.append("    block $brk_sp2i")
        ins.append("      loop $lp_sp2i")
        ins.append(f"        local.get {j}")
        ins.append(f"        local.get {len_d}")
        ins.append("        i32.ge_u")
        ins.append("        br_if $brk_sp2i")
        ins.append(f"        local.get {ptr_s}")
        ins.append(f"        local.get {i}")
        ins.append("        i32.add")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append(f"        local.get {ptr_d}")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append("        i32.ne")
        ins.append("        if")
        ins.append("          i32.const 0")
        ins.append(f"          local.set {matched}")
        ins.append("          br $brk_sp2i")
        ins.append("        end")
        ins.append(f"        local.get {j}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {j}")
        ins.append("        br $lp_sp2i")
        ins.append("      end")
        ins.append("    end")
        ins.append(f"    local.get {matched}")
        ins.append("    if")
        # Found delimiter: emit segment [seg_start, i)
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {seg_start}")
        ins.append("      i32.sub")
        ins.append(f"      local.set {seg_len}")
        # Allocate segment string
        ins.append(f"      local.get {seg_len}")
        ins.append("      call $alloc")
        ins.append(f"      local.set {seg_ptr}")
        ins.extend(f"      {x}" for x in gc_shadow_push(seg_ptr))
        # Copy segment bytes
        ins.append("      i32.const 0")
        ins.append(f"      local.set {copy_idx}")
        ins.append("      block $brk_spc")
        ins.append("        loop $lp_spc")
        ins.append(f"          local.get {copy_idx}")
        ins.append(f"          local.get {seg_len}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_spc")
        ins.append(f"          local.get {seg_ptr}")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.add")
        ins.append(f"          local.get {ptr_s}")
        ins.append(f"          local.get {seg_start}")
        ins.append("          i32.add")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.store8 offset=0")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {copy_idx}")
        ins.append("          br $lp_spc")
        ins.append("        end")
        ins.append("      end")
        # Store (seg_ptr, seg_len) in array
        ins.append(f"      local.get {arr}")
        ins.append(f"      local.get {seg_idx}")
        ins.append("      i32.const 8")
        ins.append("      i32.mul")
        ins.append("      i32.add")
        ins.append(f"      local.get {seg_ptr}")
        ins.append("      i32.store offset=0")
        ins.append(f"      local.get {arr}")
        ins.append(f"      local.get {seg_idx}")
        ins.append("      i32.const 8")
        ins.append("      i32.mul")
        ins.append("      i32.add")
        ins.append(f"      local.get {seg_len}")
        ins.append("      i32.store offset=4")
        # Advance
        ins.append(f"      local.get {seg_idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {seg_idx}")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_d}")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.set {seg_start}")
        ins.append("    else")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    end")
        ins.append("    br $lp_sp2")
        ins.append("  end")
        ins.append("end")

        # Handle last segment: [seg_start, len_s)
        ins.append(f"local.get {len_s}")
        ins.append(f"local.get {seg_start}")
        ins.append("i32.sub")
        ins.append(f"local.set {seg_len}")
        ins.append(f"local.get {seg_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {seg_ptr}")
        ins.extend(gc_shadow_push(seg_ptr))
        # Copy last segment
        ins.append("i32.const 0")
        ins.append(f"local.set {copy_idx}")
        ins.append("block $brk_spl")
        ins.append("  loop $lp_spl")
        ins.append(f"    local.get {copy_idx}")
        ins.append(f"    local.get {seg_len}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_spl")
        ins.append(f"    local.get {seg_ptr}")
        ins.append(f"    local.get {copy_idx}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ptr_s}")
        ins.append(f"    local.get {seg_start}")
        ins.append("    i32.add")
        ins.append(f"    local.get {copy_idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")
        ins.append(f"    local.get {copy_idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {copy_idx}")
        ins.append("    br $lp_spl")
        ins.append("  end")
        ins.append("end")
        # Store last segment in array
        ins.append(f"local.get {arr}")
        ins.append(f"local.get {seg_idx}")
        ins.append("i32.const 8")
        ins.append("i32.mul")
        ins.append("i32.add")
        ins.append(f"local.get {seg_ptr}")
        ins.append("i32.store offset=0")
        ins.append(f"local.get {arr}")
        ins.append(f"local.get {seg_idx}")
        ins.append("i32.const 8")
        ins.append("i32.mul")
        ins.append("i32.add")
        ins.append(f"local.get {seg_len}")
        ins.append("i32.store offset=4")

        ins.append("end")  # end $sp_main

        # Return (arr, seg_count)
        ins.append(f"local.get {arr}")
        ins.append(f"local.get {seg_count}")
        return ins

    def _translate_join(
        self,
        arg_a: ast.Expr,
        arg_s: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate join(array, separator) → String (i32_pair).

        Two-pass algorithm:
        1. Sum all string lengths plus separators.
        2. Allocate result buffer and copy strings with separator
           between them.
        Array<String> is (arr_ptr, count).  Each element is 8 bytes:
        (str_ptr: i32, str_len: i32) at arr_ptr + i*8.
        """
        a_instrs = self.translate_expr(arg_a, env)
        s_instrs = self.translate_expr(arg_s, env)
        if a_instrs is None or s_instrs is None:
            return None

        self.needs_alloc = True

        arr_ptr = self.alloc_local("i32")
        arr_count = self.alloc_local("i32")
        ptr_sep = self.alloc_local("i32")
        len_sep = self.alloc_local("i32")
        total_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        i = self.alloc_local("i32")
        out_idx = self.alloc_local("i32")
        str_ptr = self.alloc_local("i32")
        str_len = self.alloc_local("i32")
        copy_idx = self.alloc_local("i32")

        ins: list[str] = []

        # Evaluate array → (ptr, count)
        ins.extend(a_instrs)
        ins.append(f"local.set {arr_count}")
        ins.append(f"local.set {arr_ptr}")
        # Evaluate separator → (ptr, len)
        ins.extend(s_instrs)
        ins.append(f"local.set {len_sep}")
        ins.append(f"local.set {ptr_sep}")

        # ---- Pass 1: compute total length ----
        ins.append("i32.const 0")
        ins.append(f"local.set {total_len}")
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("block $brk_j1")
        ins.append("  loop $lp_j1")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {arr_count}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_j1")
        # Load str_len at arr_ptr + i*8 + 4
        ins.append(f"    local.get {arr_ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 8")
        ins.append("    i32.mul")
        ins.append("    i32.add")
        ins.append("    i32.load offset=4")
        ins.append(f"    local.set {str_len}")
        ins.append(f"    local.get {total_len}")
        ins.append(f"    local.get {str_len}")
        ins.append("    i32.add")
        ins.append(f"    local.set {total_len}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_j1")
        ins.append("  end")
        ins.append("end")

        # Add separator lengths: (count - 1) * len_sep (if count > 0)
        ins.append(f"local.get {arr_count}")
        ins.append("i32.const 1")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {total_len}")
        ins.append(f"  local.get {arr_count}")
        ins.append("  i32.const 1")
        ins.append("  i32.sub")
        ins.append(f"  local.get {len_sep}")
        ins.append("  i32.mul")
        ins.append("  i32.add")
        ins.append(f"  local.set {total_len}")
        ins.append("end")

        # Allocate result
        ins.append(f"local.get {total_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # ---- Pass 2: copy strings with separators ----
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {out_idx}")

        ins.append("block $brk_j2")
        ins.append("  loop $lp_j2")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {arr_count}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_j2")
        # Load (str_ptr, str_len) from array
        ins.append(f"    local.get {arr_ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 8")
        ins.append("    i32.mul")
        ins.append("    i32.add")
        ins.append("    i32.load offset=0")
        ins.append(f"    local.set {str_ptr}")
        ins.append(f"    local.get {arr_ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 8")
        ins.append("    i32.mul")
        ins.append("    i32.add")
        ins.append("    i32.load offset=4")
        ins.append(f"    local.set {str_len}")
        # Copy string bytes
        ins.append("    i32.const 0")
        ins.append(f"    local.set {copy_idx}")
        ins.append("    block $brk_jc")
        ins.append("      loop $lp_jc")
        ins.append(f"        local.get {copy_idx}")
        ins.append(f"        local.get {str_len}")
        ins.append("        i32.ge_u")
        ins.append("        br_if $brk_jc")
        ins.append(f"        local.get {dst}")
        ins.append(f"        local.get {out_idx}")
        ins.append("        i32.add")
        ins.append(f"        local.get {str_ptr}")
        ins.append(f"        local.get {copy_idx}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append("        i32.store8 offset=0")
        ins.append(f"        local.get {out_idx}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {out_idx}")
        ins.append(f"        local.get {copy_idx}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {copy_idx}")
        ins.append("        br $lp_jc")
        ins.append("      end")
        ins.append("    end")
        # If not last element, copy separator
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {arr_count}")
        ins.append("    i32.const 1")
        ins.append("    i32.sub")
        ins.append("    i32.lt_u")
        ins.append("    if")
        ins.append("      i32.const 0")
        ins.append(f"      local.set {copy_idx}")
        ins.append("      block $brk_js")
        ins.append("        loop $lp_js")
        ins.append(f"          local.get {copy_idx}")
        ins.append(f"          local.get {len_sep}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_js")
        ins.append(f"          local.get {dst}")
        ins.append(f"          local.get {out_idx}")
        ins.append("          i32.add")
        ins.append(f"          local.get {ptr_sep}")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.store8 offset=0")
        ins.append(f"          local.get {out_idx}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {out_idx}")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {copy_idx}")
        ins.append("          br $lp_js")
        ins.append("        end")
        ins.append("      end")
        ins.append("    end")
        # i++
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_j2")
        ins.append("  end")
        ins.append("end")

        # Result: (dst, total_len)
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {total_len}")
        return ins
