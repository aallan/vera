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

    def _translate_array_length(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_length(array) → Int (i64).

        Evaluates the array → (ptr, len), drops ptr, extends len to i64.
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

    def _translate_array_append(
        self,
        arr_arg: ast.Expr,
        elem_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_append(array, element) → Array<T>.

        Allocates a new array of size (len + 1), copies the old elements
        byte-by-byte, appends the new element, and returns (new_ptr, new_len).
        """
        arr_instrs = self.translate_expr(arr_arg, env)
        elem_instrs = self.translate_expr(elem_arg, env)
        if arr_instrs is None or elem_instrs is None:
            return None

        # Infer element type from the pushed element
        elem_type = self._infer_vera_type(elem_arg)
        if elem_type is None:
            return None
        elem_size = _element_mem_size(elem_type)
        if elem_size is None:
            return None

        is_pair = _is_pair_element_type(elem_type)
        store_op = _element_store_op(elem_type)
        if store_op is None and not is_pair:
            return None

        self.needs_alloc = True

        # Locals for old array
        ptr_arr = self.alloc_local("i32")
        len_arr = self.alloc_local("i32")
        # Locals for new element
        if is_pair:
            elem_ptr = self.alloc_local("i32")
            elem_len = self.alloc_local("i32")
        else:
            elem_val = self.alloc_local(
                "i64" if elem_type in ("Int", "Nat") else
                "f64" if elem_type == "Float64" else "i32"
            )
        # Locals for copy loop and destination
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        old_bytes = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate array arg → (ptr, len), save to locals
        instructions.extend(arr_instrs)
        instructions.append(f"local.set {len_arr}")
        instructions.append(f"local.set {ptr_arr}")

        # Evaluate element arg, save to locals
        instructions.extend(elem_instrs)
        if is_pair:
            instructions.append(f"local.set {elem_len}")
            instructions.append(f"local.set {elem_ptr}")
        else:
            instructions.append(f"local.set {elem_val}")

        # Compute old_bytes = len_arr * elem_size
        instructions.append(f"local.get {len_arr}")
        instructions.append(f"i32.const {elem_size}")
        instructions.append("i32.mul")
        instructions.append(f"local.set {old_bytes}")

        # Allocate: (len_arr + 1) * elem_size = old_bytes + elem_size
        instructions.append(f"local.get {old_bytes}")
        instructions.append(f"i32.const {elem_size}")
        instructions.append("i32.add")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))

        # Copy old elements: byte-by-byte loop
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_copy")
        instructions.append("  loop $lp_copy")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {old_bytes}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_copy")
        instructions.append(f"    local.get {dst}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {ptr_arr}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append("    i32.store8 offset=0")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_copy")
        instructions.append("  end")
        instructions.append("end")

        # Store new element at dst + old_bytes
        if is_pair:
            # Store ptr at old_bytes offset
            instructions.append(f"local.get {dst}")
            instructions.append(f"local.get {old_bytes}")
            instructions.append("i32.add")
            instructions.append(f"local.get {elem_ptr}")
            instructions.append("i32.store offset=0")
            # Store len at old_bytes + 4
            instructions.append(f"local.get {dst}")
            instructions.append(f"local.get {old_bytes}")
            instructions.append("i32.add")
            instructions.append(f"local.get {elem_len}")
            instructions.append("i32.store offset=4")
        else:
            instructions.append(f"local.get {dst}")
            instructions.append(f"local.get {old_bytes}")
            instructions.append("i32.add")
            instructions.append(f"local.get {elem_val}")
            instructions.append(f"{store_op} offset=0")

        # Push result: (new_ptr, new_len)
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {len_arr}")
        instructions.append("i32.const 1")
        instructions.append("i32.add")
        return instructions

    def _translate_array_range(
        self,
        start_arg: ast.Expr,
        end_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_range(start, end) → Array<Int>.

        Allocates an array of max(0, end - start) Int elements and fills
        it with consecutive integers [start, end).
        """
        start_instrs = self.translate_expr(start_arg, env)
        end_instrs = self.translate_expr(end_arg, env)
        if start_instrs is None or end_instrs is None:
            return None

        self.needs_alloc = True

        start_val = self.alloc_local("i64")
        end_val = self.alloc_local("i64")
        n_i64 = self.alloc_local("i64")
        n_i32 = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate start and end
        instructions.extend(start_instrs)
        instructions.append(f"local.set {start_val}")
        instructions.extend(end_instrs)
        instructions.append(f"local.set {end_val}")

        # n = max(0, end - start)
        instructions.append(f"local.get {end_val}")
        instructions.append(f"local.get {start_val}")
        instructions.append("i64.sub")
        instructions.append(f"local.set {n_i64}")
        instructions.append(f"local.get {n_i64}")
        instructions.append("i64.const 0")
        instructions.append("i64.lt_s")
        instructions.append(f"if")
        instructions.append("  i64.const 0")
        instructions.append(f"  local.set {n_i64}")
        instructions.append("end")
        instructions.append(f"local.get {n_i64}")
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {n_i32}")

        # Empty check: if n == 0 return (0, 0)
        instructions.append(f"local.get {n_i32}")
        instructions.append("i32.eqz")
        instructions.append("if (result i32 i32)")
        instructions.append("  i32.const 0")
        instructions.append("  i32.const 0")
        instructions.append("else")

        # Allocate n * 8 bytes (Int elements are i64 = 8 bytes each)
        instructions.append(f"  local.get {n_i32}")
        instructions.append("  i32.const 8")
        instructions.append("  i32.mul")
        instructions.append("  call $alloc")
        instructions.append(f"  local.set {dst}")
        instructions.extend(f"  {line}" for line in gc_shadow_push(dst))

        # Fill loop: dst[i*8] = start + i for i = 0..n-1
        instructions.append("  i32.const 0")
        instructions.append(f"  local.set {idx}")
        instructions.append("  block $brk_fill")
        instructions.append("    loop $lp_fill")
        instructions.append(f"      local.get {idx}")
        instructions.append(f"      local.get {n_i32}")
        instructions.append("      i32.ge_u")
        instructions.append("      br_if $brk_fill")
        # Store start + idx at dst + idx*8
        instructions.append(f"      local.get {dst}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 8")
        instructions.append("      i32.mul")
        instructions.append("      i32.add")
        instructions.append(f"      local.get {start_val}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i64.extend_i32_u")
        instructions.append("      i64.add")
        instructions.append("      i64.store offset=0")
        # idx++
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("      br $lp_fill")
        instructions.append("    end")
        instructions.append("  end")

        # Push result: (dst, n)
        instructions.append(f"  local.get {dst}")
        instructions.append(f"  local.get {n_i32}")
        instructions.append("end")
        return instructions

    def _translate_array_concat(
        self,
        arr_a_arg: ast.Expr,
        arr_b_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_concat(array_a, array_b) → Array<T>.

        Allocates a new array of size (len_a + len_b), copies both arrays'
        bytes contiguously, and returns (new_ptr, new_len).
        """
        arr_a_instrs = self.translate_expr(arr_a_arg, env)
        arr_b_instrs = self.translate_expr(arr_b_arg, env)
        if arr_a_instrs is None or arr_b_instrs is None:
            return None

        # Infer element type — try first arg, fall back to second
        elem_type = (
            self._infer_concat_elem_type(arr_a_arg)
            or self._infer_concat_elem_type(arr_b_arg)
        )
        if elem_type is None:
            # Both empty literals — no bytes to copy, use any size
            elem_size = 8
        else:
            size = _element_mem_size(elem_type)
            if size is None:
                return None
            elem_size = size

        self.needs_alloc = True

        ptr_a = self.alloc_local("i32")
        len_a = self.alloc_local("i32")
        ptr_b = self.alloc_local("i32")
        len_b = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        total_len = self.alloc_local("i32")
        bytes_a = self.alloc_local("i32")
        total_bytes = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate array A → (ptr, len)
        instructions.extend(arr_a_instrs)
        instructions.append(f"local.set {len_a}")
        instructions.append(f"local.set {ptr_a}")

        # Evaluate array B → (ptr, len)
        instructions.extend(arr_b_instrs)
        instructions.append(f"local.set {len_b}")
        instructions.append(f"local.set {ptr_b}")

        # total_len = len_a + len_b
        instructions.append(f"local.get {len_a}")
        instructions.append(f"local.get {len_b}")
        instructions.append("i32.add")
        instructions.append(f"local.set {total_len}")

        # Empty check: if total_len == 0 return (0, 0)
        instructions.append(f"local.get {total_len}")
        instructions.append("i32.eqz")
        instructions.append("if (result i32 i32)")
        instructions.append("  i32.const 0")
        instructions.append("  i32.const 0")
        instructions.append("else")

        # bytes_a = len_a * elem_size
        instructions.append(f"  local.get {len_a}")
        instructions.append(f"  i32.const {elem_size}")
        instructions.append("  i32.mul")
        instructions.append(f"  local.set {bytes_a}")

        # total_bytes = total_len * elem_size
        instructions.append(f"  local.get {total_len}")
        instructions.append(f"  i32.const {elem_size}")
        instructions.append("  i32.mul")
        instructions.append(f"  local.set {total_bytes}")

        # Allocate
        instructions.append(f"  local.get {total_bytes}")
        instructions.append("  call $alloc")
        instructions.append(f"  local.set {dst}")
        instructions.extend(f"  {line}" for line in gc_shadow_push(dst))

        # Copy array A bytes: byte-by-byte loop
        instructions.append("  i32.const 0")
        instructions.append(f"  local.set {idx}")
        instructions.append("  block $brk_a")
        instructions.append("    loop $lp_a")
        instructions.append(f"      local.get {idx}")
        instructions.append(f"      local.get {bytes_a}")
        instructions.append("      i32.ge_u")
        instructions.append("      br_if $brk_a")
        instructions.append(f"      local.get {dst}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append(f"      local.get {ptr_a}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append("      i32.load8_u offset=0")
        instructions.append("      i32.store8 offset=0")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("      br $lp_a")
        instructions.append("    end")
        instructions.append("  end")

        # Copy array B bytes at offset bytes_a
        instructions.append("  i32.const 0")
        instructions.append(f"  local.set {idx}")
        instructions.append("  block $brk_b")
        instructions.append("    loop $lp_b")
        instructions.append(f"      local.get {idx}")
        instructions.append(f"      local.get {total_bytes}")
        instructions.append(f"      local.get {bytes_a}")
        instructions.append("      i32.sub")  # bytes_b = total_bytes - bytes_a
        instructions.append("      i32.ge_u")
        instructions.append("      br_if $brk_b")
        instructions.append(f"      local.get {dst}")
        instructions.append(f"      local.get {bytes_a}")
        instructions.append("      i32.add")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append(f"      local.get {ptr_b}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append("      i32.load8_u offset=0")
        instructions.append("      i32.store8 offset=0")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("      br $lp_b")
        instructions.append("    end")
        instructions.append("  end")

        # Push result: (dst, total_len)
        instructions.append(f"  local.get {dst}")
        instructions.append(f"  local.get {total_len}")
        instructions.append("end")
        return instructions

    def _translate_array_slice(
        self,
        arr_arg: ast.Expr,
        start_arg: ast.Expr,
        end_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_slice(array, start, end) → Array<T>.

        Returns a new array containing elements from index start (inclusive)
        to end (exclusive).  Clamps indices to [0, len] so out-of-range
        values produce shorter slices rather than traps.
        """
        arr_instrs = self.translate_expr(arr_arg, env)
        start_instrs = self.translate_expr(start_arg, env)
        end_instrs = self.translate_expr(end_arg, env)
        if arr_instrs is None or start_instrs is None or end_instrs is None:
            return None

        elem_type = self._infer_concat_elem_type(arr_arg)
        if elem_type is None:
            # Only safe for provably empty arrays; otherwise bail
            if isinstance(arr_arg, ast.ArrayLit) and not arr_arg.elements:
                elem_size = 8
            else:
                return None
        else:
            size = _element_mem_size(elem_type)
            if size is None:
                return None
            elem_size = size

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        arr_len = self.alloc_local("i32")
        s = self.alloc_local("i32")
        e = self.alloc_local("i32")
        slice_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        total_bytes = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate array → (ptr, len)
        instructions.extend(arr_instrs)
        instructions.append(f"local.set {arr_len}")
        instructions.append(f"local.set {ptr}")

        # Evaluate start → i64, wrap to i32
        instructions.extend(start_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {s}")

        # Evaluate end → i64, wrap to i32
        instructions.extend(end_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {e}")

        # Clamp start: s = max(0, min(s, arr_len))
        instructions.append(f"local.get {s}")
        instructions.append("i32.const 0")
        instructions.append("i32.lt_s")
        instructions.append("if (result i32)")
        instructions.append("  i32.const 0")
        instructions.append("else")
        instructions.append(f"  local.get {s}")
        instructions.append(f"  local.get {arr_len}")
        instructions.append("  i32.gt_s")
        instructions.append("  if (result i32)")
        instructions.append(f"    local.get {arr_len}")
        instructions.append("  else")
        instructions.append(f"    local.get {s}")
        instructions.append("  end")
        instructions.append("end")
        instructions.append(f"local.set {s}")

        # Clamp end: e = max(s, min(e, arr_len))
        instructions.append(f"local.get {e}")
        instructions.append(f"local.get {arr_len}")
        instructions.append("i32.gt_s")
        instructions.append("if (result i32)")
        instructions.append(f"  local.get {arr_len}")
        instructions.append("else")
        instructions.append(f"  local.get {e}")
        instructions.append("end")
        instructions.append(f"local.set {e}")
        # Ensure e >= s
        instructions.append(f"local.get {e}")
        instructions.append(f"local.get {s}")
        instructions.append("i32.lt_s")
        instructions.append("if")
        instructions.append(f"  local.get {s}")
        instructions.append(f"  local.set {e}")
        instructions.append("end")

        # slice_len = e - s
        instructions.append(f"local.get {e}")
        instructions.append(f"local.get {s}")
        instructions.append("i32.sub")
        instructions.append(f"local.set {slice_len}")

        # Empty check
        instructions.append(f"local.get {slice_len}")
        instructions.append("i32.eqz")
        instructions.append("if (result i32 i32)")
        instructions.append("  i32.const 0")
        instructions.append("  i32.const 0")
        instructions.append("else")

        # total_bytes = slice_len * elem_size
        instructions.append(f"  local.get {slice_len}")
        instructions.append(f"  i32.const {elem_size}")
        instructions.append("  i32.mul")
        instructions.append(f"  local.set {total_bytes}")

        # Allocate
        instructions.append(f"  local.get {total_bytes}")
        instructions.append("  call $alloc")
        instructions.append(f"  local.set {dst}")
        instructions.extend(f"  {line}" for line in gc_shadow_push(dst))

        # Copy bytes: dst[i] = src[s * elem_size + i] for i in [0, total_bytes)
        instructions.append("  i32.const 0")
        instructions.append(f"  local.set {idx}")
        instructions.append("  block $brk")
        instructions.append("    loop $lp")
        instructions.append(f"      local.get {idx}")
        instructions.append(f"      local.get {total_bytes}")
        instructions.append("      i32.ge_u")
        instructions.append("      br_if $brk")
        # dst[idx]
        instructions.append(f"      local.get {dst}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        # src[s * elem_size + idx]
        instructions.append(f"      local.get {ptr}")
        instructions.append(f"      local.get {s}")
        instructions.append(f"      i32.const {elem_size}")
        instructions.append("      i32.mul")
        instructions.append("      i32.add")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append("      i32.load8_u offset=0")
        instructions.append("      i32.store8 offset=0")
        # idx++
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("      br $lp")
        instructions.append("    end")
        instructions.append("  end")

        # Push result: (dst, slice_len)
        instructions.append(f"  local.get {dst}")
        instructions.append(f"  local.get {slice_len}")
        instructions.append("end")
        return instructions

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

    def _translate_parse_nat(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate parse_nat(s) → Result<Nat, String> (i32 pointer).

        Returns an ADT heap object:
          Ok(Nat):     [tag=0 : i32] [pad 4] [value : i64]   (16 bytes)
          Err(String): [tag=1 : i32] [ptr : i32] [len : i32]  (16 bytes)

        Validates that the input contains at least one digit (0-9) and
        only digits/spaces.  Skips leading and trailing spaces.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        result = self.alloc_local("i64")
        byte = self.alloc_local("i32")
        out = self.alloc_local("i32")
        has_digit = self.alloc_local("i32")

        # Intern error strings
        empty_off, empty_len = self.string_pool.intern("empty string")
        invalid_off, invalid_len = self.string_pool.intern("invalid digit")

        ins: list[str] = []

        # Evaluate string → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Initialise: result = 0, idx = 0, has_digit = 0
        ins.append("i64.const 0")
        ins.append(f"local.set {result}")
        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("i32.const 0")
        ins.append(f"local.set {has_digit}")

        # -- block structure: block $done { block $err { parse } Err }
        ins.append("block $done_pn")
        ins.append("block $err_pn")

        # -- Parse loop ------------------------------------------------
        ins.append("block $brk_pn")
        ins.append("  loop $lp_pn")
        # idx >= len → break
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_pn")
        # Load byte
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {byte}")
        # Skip space (byte 32)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 32")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("      br $lp_pn")
        ins.append("    end")
        # Check byte < '0' (48) → error
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.lt_u")
        ins.append("    br_if $err_pn")
        # Check byte > '9' (57) → error
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 57")
        ins.append("    i32.gt_u")
        ins.append("    br_if $err_pn")
        # Digit: result = result * 10 + (byte - 48)
        ins.append(f"    local.get {result}")
        ins.append("    i64.const 10")
        ins.append("    i64.mul")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.sub")
        ins.append("    i64.extend_i32_u")
        ins.append("    i64.add")
        ins.append(f"    local.set {result}")
        # Mark that we saw a digit
        ins.append("    i32.const 1")
        ins.append(f"    local.set {has_digit}")
        # idx++
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_pn")
        ins.append("  end")   # loop
        ins.append("end")     # block $brk_pn

        # -- After loop: no digits seen → error
        ins.append(f"local.get {has_digit}")
        ins.append("i32.eqz")
        ins.append("br_if $err_pn")

        # -- Ok path: allocate 16 bytes, tag=0, Nat at offset 8 ----------
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")           # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {result}")
        ins.append("i64.store offset=8")  # Nat value
        ins.append("br $done_pn")

        ins.append("end")  # block $err_pn

        # -- Err path: allocate 16 bytes, tag=1, String at offsets 4,8 ---
        # Choose error message: if idx < slen the loop exited early on an
        # invalid character → "invalid digit"; otherwise the string was
        # empty or all spaces → "empty string".
        ins.append(f"local.get {idx}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {invalid_off}")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append(f"local.set {idx}")   # reuse idx for err string ptr
        ins.append(f"local.get {idx}")   # idx now holds the err string ptr
        ins.append(f"i32.const {invalid_off}")
        ins.append("i32.eq")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {invalid_len}")
        ins.append("else")
        ins.append(f"  i32.const {empty_len}")
        ins.append("end")
        ins.append(f"local.set {byte}")  # reuse byte for err string len
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")           # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {idx}")
        ins.append("i32.store offset=4")  # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"local.get {byte}")
        ins.append("i32.store offset=8")  # string len

        ins.append("end")  # block $done_pn

        ins.append(f"local.get {out}")
        return ins

    def _translate_parse_int(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate parse_int(s) → Result<Int, String> (i32 pointer).

        Like parse_nat but handles optional leading sign (+ or -).

        Returns an ADT heap object:
          Ok(Int):     [tag=0 : i32] [pad 4] [value : i64]   (16 bytes)
          Err(String): [tag=1 : i32] [ptr : i32] [len : i32]  (16 bytes)
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        result = self.alloc_local("i64")
        byte = self.alloc_local("i32")
        out = self.alloc_local("i32")
        has_digit = self.alloc_local("i32")
        is_neg = self.alloc_local("i32")

        # Intern error strings
        empty_off, empty_len = self.string_pool.intern("empty string")
        invalid_off, invalid_len = self.string_pool.intern("invalid digit")

        ins: list[str] = []

        # Evaluate string → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Initialise
        ins.append("i64.const 0")
        ins.append(f"local.set {result}")
        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("i32.const 0")
        ins.append(f"local.set {has_digit}")
        ins.append("i32.const 0")
        ins.append(f"local.set {is_neg}")

        ins.append("block $done_pi")
        ins.append("block $err_pi")

        # -- Skip leading spaces -------------------------------------------
        ins.append("block $brk_sp_pi")
        ins.append("  loop $lp_sp_pi")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_sp_pi")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    br_if $brk_sp_pi")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_sp_pi")
        ins.append("  end")
        ins.append("end")

        # -- Check for sign character (+/-) --------------------------------
        ins.append(f"local.get {idx}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {idx}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {byte}")
        # Check minus (45)
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 45")
        ins.append("  i32.eq")
        ins.append("  if")
        ins.append("    i32.const 1")
        ins.append(f"    local.set {is_neg}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("  else")
        # Check plus (43)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 43")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("    end")
        ins.append("  end")
        ins.append("end")

        # -- Parse digit loop ---------------------------------------------
        ins.append("block $brk_pi")
        ins.append("  loop $lp_pi")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_pi")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {byte}")
        # Skip trailing space (byte 32)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 32")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("      br $lp_pi")
        ins.append("    end")
        # Check byte < '0' (48) → error
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.lt_u")
        ins.append("    br_if $err_pi")
        # Check byte > '9' (57) → error
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 57")
        ins.append("    i32.gt_u")
        ins.append("    br_if $err_pi")
        # Digit: result = result * 10 + (byte - 48)
        ins.append(f"    local.get {result}")
        ins.append("    i64.const 10")
        ins.append("    i64.mul")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.sub")
        ins.append("    i64.extend_i32_u")
        ins.append("    i64.add")
        ins.append(f"    local.set {result}")
        # Mark that we saw a digit
        ins.append("    i32.const 1")
        ins.append(f"    local.set {has_digit}")
        # idx++
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_pi")
        ins.append("  end")   # loop
        ins.append("end")     # block $brk_pi

        # -- After loop: no digits seen → error
        ins.append(f"local.get {has_digit}")
        ins.append("i32.eqz")
        ins.append("br_if $err_pi")

        # -- Apply sign: if is_neg, negate result
        ins.append(f"local.get {is_neg}")
        ins.append("if")
        ins.append("  i64.const 0")
        ins.append(f"  local.get {result}")
        ins.append("  i64.sub")
        ins.append(f"  local.set {result}")
        ins.append("end")

        # -- Ok path: allocate 16 bytes, tag=0, Int at offset 8 -----------
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")           # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {result}")
        ins.append("i64.store offset=8")  # Int value
        ins.append("br $done_pi")

        ins.append("end")  # block $err_pi

        # -- Err path: allocate 16 bytes, tag=1, String at offsets 4,8 ----
        ins.append(f"local.get {idx}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {invalid_off}")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append(f"local.set {idx}")
        ins.append(f"local.get {idx}")
        ins.append(f"i32.const {invalid_off}")
        ins.append("i32.eq")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {invalid_len}")
        ins.append("else")
        ins.append(f"  i32.const {empty_len}")
        ins.append("end")
        ins.append(f"local.set {byte}")
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")           # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {idx}")
        ins.append("i32.store offset=4")  # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"local.get {byte}")
        ins.append("i32.store offset=8")  # string len

        ins.append("end")  # block $done_pi

        ins.append(f"local.get {out}")
        return ins

    def _translate_parse_bool(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate parse_bool(s) → Result<Bool, String> (i32 pointer).

        Accepts only strict lowercase "true" or "false" (with optional
        leading/trailing whitespace).  Returns Ok(1) for true, Ok(0) for
        false, or Err("expected true or false") otherwise.

        ADT layout (16 bytes):
          Ok(Bool):    [tag=0 : i32] [value : i32] [pad 8]
          Err(String): [tag=1 : i32] [ptr : i32]   [len : i32]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        start = self.alloc_local("i32")
        end = self.alloc_local("i32")
        content_len = self.alloc_local("i32")
        out = self.alloc_local("i32")

        err_off, err_len = self.string_pool.intern("expected true or false")

        ins: list[str] = []

        # Evaluate string → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Skip leading spaces → start
        ins.append("i32.const 0")
        ins.append(f"local.set {start}")
        ins.append("block $brk_ls")
        ins.append("  loop $lp_ls")
        ins.append(f"    local.get {start}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_ls")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {start}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    br_if $brk_ls")
        ins.append(f"    local.get {start}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {start}")
        ins.append("    br $lp_ls")
        ins.append("  end")
        ins.append("end")

        # Skip trailing spaces → end (points past last non-space)
        ins.append(f"local.get {slen}")
        ins.append(f"local.set {end}")
        ins.append("block $brk_ts")
        ins.append("  loop $lp_ts")
        ins.append(f"    local.get {end}")
        ins.append(f"    local.get {start}")
        ins.append("    i32.le_u")
        ins.append("    br_if $brk_ts")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {end}")
        ins.append("    i32.const 1")
        ins.append("    i32.sub")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    br_if $brk_ts")
        ins.append(f"    local.get {end}")
        ins.append("    i32.const 1")
        ins.append("    i32.sub")
        ins.append(f"    local.set {end}")
        ins.append("    br $lp_ts")
        ins.append("  end")
        ins.append("end")

        # content_len = end - start
        ins.append(f"local.get {end}")
        ins.append(f"local.get {start}")
        ins.append("i32.sub")
        ins.append(f"local.set {content_len}")

        ins.append("block $done_pb")
        ins.append("block $err_pb")

        # -- Check length 4 → "true" (bytes: 116, 114, 117, 101) ---------
        ins.append(f"local.get {content_len}")
        ins.append("i32.const 4")
        ins.append("i32.eq")
        ins.append("if")
        # Check byte 0 = 't' (116)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.const 116")
        ins.append("  i32.eq")
        # Check byte 1 = 'r' (114)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=1")
        ins.append("  i32.const 114")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        # Check byte 2 = 'u' (117)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=2")
        ins.append("  i32.const 117")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        # Check byte 3 = 'e' (101)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=3")
        ins.append("  i32.const 101")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        ins.append("  if")
        # Matched "true" → Ok(1)
        ins.append("    i32.const 16")
        ins.append("    call $alloc")
        ins.append(f"    local.tee {out}")
        ins.append("    i32.const 0")
        ins.append("    i32.store")          # tag = 0 (Ok)
        ins.extend(["    " + i for i in gc_shadow_push(out)])
        ins.append(f"    local.get {out}")
        ins.append("    i32.const 1")
        ins.append("    i32.store offset=4") # Bool = true (1)
        ins.append("    br $done_pb")
        ins.append("  end")
        ins.append("end")

        # -- Check length 5 → "false" (bytes: 102, 97, 108, 115, 101) ----
        ins.append(f"local.get {content_len}")
        ins.append("i32.const 5")
        ins.append("i32.eq")
        ins.append("if")
        # Check byte 0 = 'f' (102)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.const 102")
        ins.append("  i32.eq")
        # Check byte 1 = 'a' (97)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=1")
        ins.append("  i32.const 97")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        # Check byte 2 = 'l' (108)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=2")
        ins.append("  i32.const 108")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        # Check byte 3 = 's' (115)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=3")
        ins.append("  i32.const 115")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        # Check byte 4 = 'e' (101)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=4")
        ins.append("  i32.const 101")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        ins.append("  if")
        # Matched "false" → Ok(0)
        ins.append("    i32.const 16")
        ins.append("    call $alloc")
        ins.append(f"    local.tee {out}")
        ins.append("    i32.const 0")
        ins.append("    i32.store")          # tag = 0 (Ok)
        ins.extend(["    " + i for i in gc_shadow_push(out)])
        ins.append(f"    local.get {out}")
        ins.append("    i32.const 0")
        ins.append("    i32.store offset=4") # Bool = false (0)
        ins.append("    br $done_pb")
        ins.append("  end")
        ins.append("end")

        # -- Fall through to Err ------------------------------------------
        ins.append("br $err_pb")

        ins.append("end")  # block $err_pb

        # -- Err path: allocate 16 bytes, tag=1, String at offsets 4,8 ----
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")           # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_off}")
        ins.append("i32.store offset=4")  # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_len}")
        ins.append("i32.store offset=8")  # string len

        ins.append("end")  # block $done_pb

        ins.append(f"local.get {out}")
        return ins

    def _translate_parse_float64(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate parse_float64(s) → Result<Float64, String> (i32 ptr).

        Parses a decimal string (with optional sign and decimal point)
        to a 64-bit float.  Handles: optional leading spaces, optional
        sign (+/-), integer part, optional fractional part (.digits).
        Returns Ok(Float64) on success, Err(String) on failure.

        ADT layout (16 bytes):
          Ok(Float64): [tag=0 : i32] [pad 4] [value : f64]
          Err(String): [tag=1 : i32] [ptr : i32] [len : i32]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        sign = self.alloc_local("f64")
        int_part = self.alloc_local("f64")
        frac_part = self.alloc_local("f64")
        frac_div = self.alloc_local("f64")
        byte = self.alloc_local("i32")
        has_digit = self.alloc_local("i32")
        out = self.alloc_local("i32")

        # Intern error strings
        empty_off, empty_len = self.string_pool.intern("empty string")
        invalid_off, invalid_len = self.string_pool.intern(
            "invalid character",
        )

        ins: list[str] = []

        # Evaluate string → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Initialize
        ins.append("f64.const 1.0")
        ins.append(f"local.set {sign}")
        ins.append("f64.const 0.0")
        ins.append(f"local.set {int_part}")
        ins.append("f64.const 0.0")
        ins.append(f"local.set {frac_part}")
        ins.append("f64.const 1.0")
        ins.append(f"local.set {frac_div}")
        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("i32.const 0")
        ins.append(f"local.set {has_digit}")

        ins.append("block $done_pf")
        ins.append("block $err_pf")

        # -- Skip leading spaces -------------------------------------------
        ins.append("block $brk_sp")
        ins.append("  loop $lp_sp")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_sp")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    br_if $brk_sp")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_sp")
        ins.append("  end")
        ins.append("end")

        # -- Check for sign character (+/-) --------------------------------
        ins.append(f"local.get {idx}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {idx}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {byte}")
        # Check minus (45)
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 45")
        ins.append("  i32.eq")
        ins.append("  if")
        ins.append("    f64.const -1.0")
        ins.append(f"    local.set {sign}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("  else")
        # Check plus (43)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 43")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("    end")
        ins.append("  end")
        ins.append("end")

        # -- Parse integer part (digits before decimal point) --------------
        ins.append("block $brk_int")
        ins.append("  loop $lp_int")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_int")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {byte}")
        # Break if not a digit (byte < 48 || byte > 57) — catches '.'
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.lt_u")
        ins.append("    br_if $brk_int")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 57")
        ins.append("    i32.gt_u")
        ins.append("    br_if $brk_int")
        # int_part = int_part * 10 + (byte - 48)
        ins.append(f"    local.get {int_part}")
        ins.append("    f64.const 10.0")
        ins.append("    f64.mul")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.sub")
        ins.append("    f64.convert_i32_u")
        ins.append("    f64.add")
        ins.append(f"    local.set {int_part}")
        # Mark that we saw a digit
        ins.append("    i32.const 1")
        ins.append(f"    local.set {has_digit}")
        # idx++
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_int")
        ins.append("  end")
        ins.append("end")

        # -- Check for decimal point (46) ----------------------------------
        ins.append(f"local.get {idx}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {idx}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {byte}")
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 46")
        ins.append("  i32.eq")
        ins.append("  if")
        # Skip the '.'
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        # Parse fractional digits
        ins.append("    block $brk_frac")
        ins.append("    loop $lp_frac")
        ins.append(f"      local.get {idx}")
        ins.append(f"      local.get {slen}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_frac")
        ins.append(f"      local.get {ptr}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append(f"      local.set {byte}")
        # Space → break (trailing space)
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 32")
        ins.append("      i32.eq")
        ins.append("      br_if $brk_frac")
        # Not a digit → error (set has_digit=1 so error path
        # picks "invalid character" not "empty string")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 48")
        ins.append("      i32.lt_u")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 57")
        ins.append("      i32.gt_u")
        ins.append("      i32.or")
        ins.append("      if")
        ins.append(f"        i32.const 1")
        ins.append(f"        local.set {has_digit}")
        ins.append("        br $err_pf")
        ins.append("      end")
        # frac_div *= 10, frac_part = frac_part * 10 + (byte - 48)
        ins.append(f"      local.get {frac_div}")
        ins.append("      f64.const 10.0")
        ins.append("      f64.mul")
        ins.append(f"      local.set {frac_div}")
        ins.append(f"      local.get {frac_part}")
        ins.append("      f64.const 10.0")
        ins.append("      f64.mul")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 48")
        ins.append("      i32.sub")
        ins.append("      f64.convert_i32_u")
        ins.append("      f64.add")
        ins.append(f"      local.set {frac_part}")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {has_digit}")
        # idx++
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("      br $lp_frac")
        ins.append("    end")
        ins.append("    end")
        ins.append("  else")
        # Non-digit, non-dot after integer part → check if it's space
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    if")
        ins.append(f"      i32.const 1")
        ins.append(f"      local.set {has_digit}")
        ins.append("      br $err_pf")
        ins.append("    end")
        ins.append("  end")
        ins.append("end")

        # -- Skip trailing spaces ------------------------------------------
        ins.append("block $brk_ts")
        ins.append("  loop $lp_ts")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_ts")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    if")
        ins.append(f"      i32.const 1")
        ins.append(f"      local.set {has_digit}")
        ins.append("      br $err_pf")
        ins.append("    end")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_ts")
        ins.append("  end")
        ins.append("end")

        # -- After parsing: no digits seen → error
        ins.append(f"local.get {has_digit}")
        ins.append("i32.eqz")
        ins.append("br_if $err_pf")

        # -- Ok path: allocate 16 bytes, tag=0, f64 at offset 8 -----------
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")             # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        # Compute: sign * (int_part + frac_part / frac_div)
        ins.append(f"local.get {sign}")
        ins.append(f"local.get {int_part}")
        ins.append(f"local.get {frac_part}")
        ins.append(f"local.get {frac_div}")
        ins.append("f64.div")
        ins.append("f64.add")
        ins.append("f64.mul")
        ins.append("f64.store offset=8")    # Float64 value
        ins.append("br $done_pf")

        ins.append("end")  # block $err_pf

        # -- Err path: allocate 16 bytes, tag=1, String at offsets 4,8 ----
        ins.append(f"local.get {has_digit}")
        ins.append("i32.eqz")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {empty_off}")
        ins.append("else")
        ins.append(f"  i32.const {invalid_off}")
        ins.append("end")
        ins.append(f"local.set {idx}")   # reuse idx for err ptr
        ins.append(f"local.get {has_digit}")
        ins.append("i32.eqz")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {empty_len}")
        ins.append("else")
        ins.append(f"  i32.const {invalid_len}")
        ins.append("end")
        ins.append(f"local.set {byte}")  # reuse byte for err len
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")             # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {idx}")
        ins.append("i32.store offset=4")    # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"local.get {byte}")
        ins.append("i32.store offset=8")    # string len

        ins.append("end")  # block $done_pf

        ins.append(f"local.get {out}")
        return ins

    # -----------------------------------------------------------------
    # Base64 encoding / decoding (RFC 4648)
    # -----------------------------------------------------------------

    def _translate_base64_encode(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate base64_encode(s) → String (i32_pair).

        Every 3 input bytes produce 4 output chars from the standard
        Base64 alphabet.  Remaining 1 or 2 bytes are padded with '='.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        # Intern the Base64 alphabet in the string pool so we can
        # look up output characters by 6-bit index.
        alpha_off, _ = self.string_pool.intern(
            "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
        )
        empty_off, empty_len = self.string_pool.intern("")

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        out_len = self.alloc_local("i32")
        i = self.alloc_local("i32")   # input index
        j = self.alloc_local("i32")   # output index
        b0 = self.alloc_local("i32")
        b1 = self.alloc_local("i32")
        b2 = self.alloc_local("i32")
        rem = self.alloc_local("i32")
        full = self.alloc_local("i32")  # slen - remainder

        ins: list[str] = []

        # Evaluate string arg → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Empty input → empty output
        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if (result i32 i32)")
        ins.append(f"  i32.const {empty_off}")
        ins.append(f"  i32.const {empty_len}")
        ins.append("else")

        # out_len = ((slen + 2) / 3) * 4
        ins.append(f"local.get {slen}")
        ins.append("i32.const 2")
        ins.append("i32.add")
        ins.append("i32.const 3")
        ins.append("i32.div_u")
        ins.append("i32.const 4")
        ins.append("i32.mul")
        ins.append(f"local.set {out_len}")

        # Allocate output buffer
        ins.append(f"local.get {out_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # rem = slen % 3; full = slen - rem
        ins.append(f"local.get {slen}")
        ins.append("i32.const 3")
        ins.append("i32.rem_u")
        ins.append(f"local.set {rem}")
        ins.append(f"local.get {slen}")
        ins.append(f"local.get {rem}")
        ins.append("i32.sub")
        ins.append(f"local.set {full}")

        # --- Main loop: process complete 3-byte groups ----------------
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {j}")
        ins.append("block $brk_e3")
        ins.append("  loop $lp_e3")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {full}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_e3")

        # Load b0, b1, b2
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {b0}")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=1")
        ins.append(f"    local.set {b1}")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=2")
        ins.append(f"    local.set {b2}")

        # Output char 0: alphabet[b0 >> 2]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {alpha_off}")
        ins.append(f"    local.get {b0}")
        ins.append("    i32.const 2")
        ins.append("    i32.shr_u")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")

        # Output char 1: alphabet[((b0 & 3) << 4) | (b1 >> 4)]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {alpha_off}")
        ins.append(f"    local.get {b0}")
        ins.append("    i32.const 3")
        ins.append("    i32.and")
        ins.append("    i32.const 4")
        ins.append("    i32.shl")
        ins.append(f"    local.get {b1}")
        ins.append("    i32.const 4")
        ins.append("    i32.shr_u")
        ins.append("    i32.or")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=1")

        # Output char 2: alphabet[((b1 & 0xF) << 2) | (b2 >> 6)]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {alpha_off}")
        ins.append(f"    local.get {b1}")
        ins.append("    i32.const 15")
        ins.append("    i32.and")
        ins.append("    i32.const 2")
        ins.append("    i32.shl")
        ins.append(f"    local.get {b2}")
        ins.append("    i32.const 6")
        ins.append("    i32.shr_u")
        ins.append("    i32.or")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=2")

        # Output char 3: alphabet[b2 & 0x3F]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {alpha_off}")
        ins.append(f"    local.get {b2}")
        ins.append("    i32.const 63")
        ins.append("    i32.and")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=3")

        # i += 3; j += 4
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 3")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.const 4")
        ins.append("    i32.add")
        ins.append(f"    local.set {j}")
        ins.append("    br $lp_e3")
        ins.append("  end")
        ins.append("end")

        # --- Handle remainder (1 or 2 bytes) --------------------------
        # rem == 1: 2 base64 chars + "=="
        ins.append(f"local.get {rem}")
        ins.append("i32.const 1")
        ins.append("i32.eq")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {i}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {b0}")
        # char 0: alphabet[b0 >> 2]
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {alpha_off}")
        ins.append(f"  local.get {b0}")
        ins.append("  i32.const 2")
        ins.append("  i32.shr_u")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.store8 offset=0")
        # char 1: alphabet[(b0 & 3) << 4]
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {alpha_off}")
        ins.append(f"  local.get {b0}")
        ins.append("  i32.const 3")
        ins.append("  i32.and")
        ins.append("  i32.const 4")
        ins.append("  i32.shl")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.store8 offset=1")
        # char 2-3: '=' (61)
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append("  i32.const 61")
        ins.append("  i32.store8 offset=2")
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append("  i32.const 61")
        ins.append("  i32.store8 offset=3")
        ins.append("end")

        # rem == 2: 3 base64 chars + "="
        ins.append(f"local.get {rem}")
        ins.append("i32.const 2")
        ins.append("i32.eq")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {i}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {b0}")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {i}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=1")
        ins.append(f"  local.set {b1}")
        # char 0: alphabet[b0 >> 2]
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {alpha_off}")
        ins.append(f"  local.get {b0}")
        ins.append("  i32.const 2")
        ins.append("  i32.shr_u")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.store8 offset=0")
        # char 1: alphabet[((b0 & 3) << 4) | (b1 >> 4)]
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {alpha_off}")
        ins.append(f"  local.get {b0}")
        ins.append("  i32.const 3")
        ins.append("  i32.and")
        ins.append("  i32.const 4")
        ins.append("  i32.shl")
        ins.append(f"  local.get {b1}")
        ins.append("  i32.const 4")
        ins.append("  i32.shr_u")
        ins.append("  i32.or")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.store8 offset=1")
        # char 2: alphabet[(b1 & 0xF) << 2]
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {alpha_off}")
        ins.append(f"  local.get {b1}")
        ins.append("  i32.const 15")
        ins.append("  i32.and")
        ins.append("  i32.const 2")
        ins.append("  i32.shl")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.store8 offset=2")
        # char 3: '='
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append("  i32.const 61")
        ins.append("  i32.store8 offset=3")
        ins.append("end")

        # Leave (dst, out_len) on the stack
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {out_len}")

        ins.append("end")  # else branch of empty check

        return ins

    def _translate_base64_decode(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate base64_decode(s) → Result<String, String> (i32 ptr).

        Decodes a standard Base64 string (RFC 4648).  Returns Err on
        invalid length (not a multiple of 4) or invalid characters.

        ADT layout (16 bytes):
          Ok(String):  [tag=0 : i32] [ptr : i32] [len : i32] [pad 4]
          Err(String): [tag=1 : i32] [ptr : i32] [len : i32] [pad 4]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        err_len_off, err_len_ln = self.string_pool.intern(
            "invalid base64 length"
        )
        err_chr_off, err_chr_ln = self.string_pool.intern("invalid base64")
        empty_off, empty_len = self.string_pool.intern("")

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        out = self.alloc_local("i32")    # Result ADT pointer
        dst = self.alloc_local("i32")    # decoded bytes pointer
        out_len = self.alloc_local("i32")
        pad = self.alloc_local("i32")    # padding count (0-2)
        i = self.alloc_local("i32")      # input index
        k = self.alloc_local("i32")      # output index
        ch = self.alloc_local("i32")     # current input byte
        val = self.alloc_local("i32")    # decoded 6-bit value
        acc = self.alloc_local("i32")    # accumulated 24-bit value
        gi = self.alloc_local("i32")     # group-internal index (0-3)

        ins: list[str] = []

        # Evaluate string arg → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        ins.append("block $done_bd")
        ins.append("block $err_chr_bd")
        ins.append("block $err_len_bd")

        # Validate: slen % 4 must be 0
        ins.append(f"local.get {slen}")
        ins.append("i32.const 3")
        ins.append("i32.and")        # slen & 3 (faster than rem_u)
        ins.append("i32.const 0")
        ins.append("i32.ne")
        ins.append("br_if $err_len_bd")

        # Empty input → Ok("")
        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if")
        ins.append("  i32.const 16")
        ins.append("  call $alloc")
        ins.append(f"  local.tee {out}")
        ins.append("  i32.const 0")
        ins.append("  i32.store")          # tag = 0 (Ok)
        ins.extend(["  " + x for x in gc_shadow_push(out)])
        ins.append(f"  local.get {out}")
        ins.append(f"  i32.const {empty_off}")
        ins.append("  i32.store offset=4") # ptr
        ins.append(f"  local.get {out}")
        ins.append(f"  i32.const {empty_len}")
        ins.append("  i32.store offset=8") # len
        ins.append("  br $done_bd")
        ins.append("end")

        # Count trailing '=' padding
        ins.append("i32.const 0")
        ins.append(f"local.set {pad}")
        # Check last byte: ptr + slen - 1
        ins.append(f"local.get {ptr}")
        ins.append(f"local.get {slen}")
        ins.append("i32.add")
        ins.append("i32.const 1")
        ins.append("i32.sub")
        ins.append("i32.load8_u offset=0")
        ins.append("i32.const 61")         # '='
        ins.append("i32.eq")
        ins.append("if")
        ins.append(f"  local.get {pad}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {pad}")
        # Check second-to-last byte: ptr + slen - 2
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {slen}")
        ins.append("  i32.add")
        ins.append("  i32.const 2")
        ins.append("  i32.sub")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.const 61")
        ins.append("  i32.eq")
        ins.append("  if")
        ins.append(f"    local.get {pad}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {pad}")
        ins.append("  end")
        ins.append("end")

        # out_len = (slen / 4) * 3 - pad
        ins.append(f"local.get {slen}")
        ins.append("i32.const 2")
        ins.append("i32.shr_u")           # slen / 4
        ins.append("i32.const 3")
        ins.append("i32.mul")
        ins.append(f"local.get {pad}")
        ins.append("i32.sub")
        ins.append(f"local.set {out_len}")

        # Allocate decoded buffer
        ins.append(f"local.get {out_len}")
        ins.append("i32.const 1")
        ins.append("i32.or")              # at least 1 byte for alloc
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # --- Decode loop: 4 input chars → 3 output bytes -------------
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {k}")

        ins.append("block $brk_dl")
        ins.append("  loop $lp_dl")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_dl")

        # Decode 4 chars into acc (24 bits)
        ins.append("    i32.const 0")
        ins.append(f"    local.set {acc}")
        ins.append("    i32.const 0")
        ins.append(f"    local.set {gi}")
        ins.append("    block $brk_g")
        ins.append("      loop $lp_g")
        ins.append(f"        local.get {gi}")
        ins.append("        i32.const 4")
        ins.append("        i32.ge_u")
        ins.append("        br_if $brk_g")

        # Load input char
        ins.append(f"        local.get {ptr}")
        ins.append(f"        local.get {i}")
        ins.append(f"        local.get {gi}")
        ins.append("        i32.add")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append(f"        local.set {ch}")

        # Decode char → 6-bit value via branching
        ins.append("        block $valid_d")
        ins.append("        block $invalid_d")

        # A-Z (65-90) → 0-25
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 65")
        ins.append("        i32.ge_u")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 90")
        ins.append("        i32.le_u")
        ins.append("        i32.and")
        ins.append("        if")
        ins.append(f"          local.get {ch}")
        ins.append("          i32.const 65")
        ins.append("          i32.sub")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # a-z (97-122) → 26-51
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 97")
        ins.append("        i32.ge_u")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 122")
        ins.append("        i32.le_u")
        ins.append("        i32.and")
        ins.append("        if")
        ins.append(f"          local.get {ch}")
        ins.append("          i32.const 97")
        ins.append("          i32.sub")
        ins.append("          i32.const 26")
        ins.append("          i32.add")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # 0-9 (48-57) → 52-61
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 48")
        ins.append("        i32.ge_u")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 57")
        ins.append("        i32.le_u")
        ins.append("        i32.and")
        ins.append("        if")
        ins.append(f"          local.get {ch}")
        ins.append("          i32.const 48")
        ins.append("          i32.sub")
        ins.append("          i32.const 52")
        ins.append("          i32.add")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # '+' (43) → 62
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 43")
        ins.append("        i32.eq")
        ins.append("        if")
        ins.append("          i32.const 62")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # '/' (47) → 63
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 47")
        ins.append("        i32.eq")
        ins.append("        if")
        ins.append("          i32.const 63")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # '=' (61) → 0 (padding)
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 61")
        ins.append("        i32.eq")
        ins.append("        if")
        ins.append("          i32.const 0")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # Invalid character
        ins.append("        br $invalid_d")
        ins.append("        end")  # block $invalid_d
        ins.append("        br $err_chr_bd")

        ins.append("        end")  # block $valid_d

        # acc = (acc << 6) | val
        ins.append(f"        local.get {acc}")
        ins.append("        i32.const 6")
        ins.append("        i32.shl")
        ins.append(f"        local.get {val}")
        ins.append("        i32.or")
        ins.append(f"        local.set {acc}")

        # gi++
        ins.append(f"        local.get {gi}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {gi}")
        ins.append("        br $lp_g")
        ins.append("      end")  # loop $lp_g
        ins.append("    end")    # block $brk_g

        # Extract up to 3 bytes from acc and store if within out_len
        # Byte 0: (acc >> 16) & 0xFF
        ins.append(f"    local.get {k}")
        ins.append(f"    local.get {out_len}")
        ins.append("    i32.lt_u")
        ins.append("    if")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {k}")
        ins.append("      i32.add")
        ins.append(f"      local.get {acc}")
        ins.append("      i32.const 16")
        ins.append("      i32.shr_u")
        ins.append("      i32.const 255")
        ins.append("      i32.and")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {k}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {k}")
        ins.append("    end")

        # Byte 1: (acc >> 8) & 0xFF
        ins.append(f"    local.get {k}")
        ins.append(f"    local.get {out_len}")
        ins.append("    i32.lt_u")
        ins.append("    if")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {k}")
        ins.append("      i32.add")
        ins.append(f"      local.get {acc}")
        ins.append("      i32.const 8")
        ins.append("      i32.shr_u")
        ins.append("      i32.const 255")
        ins.append("      i32.and")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {k}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {k}")
        ins.append("    end")

        # Byte 2: acc & 0xFF
        ins.append(f"    local.get {k}")
        ins.append(f"    local.get {out_len}")
        ins.append("    i32.lt_u")
        ins.append("    if")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {k}")
        ins.append("      i32.add")
        ins.append(f"      local.get {acc}")
        ins.append("      i32.const 255")
        ins.append("      i32.and")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {k}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {k}")
        ins.append("    end")

        # i += 4
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 4")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_dl")
        ins.append("  end")  # loop $lp_dl
        ins.append("end")    # block $brk_dl

        # --- Ok path: wrap (dst, out_len) in Result -------------------
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")            # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {dst}")
        ins.append("i32.store offset=4")   # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"local.get {out_len}")
        ins.append("i32.store offset=8")   # string len
        ins.append("br $done_bd")

        # --- Err path: invalid length ---------------------------------
        ins.append("end")  # block $err_len_bd
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")            # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_len_off}")
        ins.append("i32.store offset=4")
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_len_ln}")
        ins.append("i32.store offset=8")
        ins.append("br $done_bd")

        # --- Err path: invalid character ------------------------------
        ins.append("end")  # block $err_chr_bd
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")            # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_chr_off}")
        ins.append("i32.store offset=4")
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_chr_ln}")
        ins.append("i32.store offset=8")

        ins.append("end")  # block $done_bd

        ins.append(f"local.get {out}")
        return ins

    def _translate_url_encode(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate url_encode(s) → String (i32_pair).

        Percent-encodes all bytes except RFC 3986 unreserved characters:
        A-Z, a-z, 0-9, '-', '_', '.', '~'.
        Each reserved byte becomes %XX (uppercase hex).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        # Intern the hex digit alphabet for fast lookup
        hex_off, _ = self.string_pool.intern("0123456789ABCDEF")
        empty_off, empty_len = self.string_pool.intern("")

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        out_len = self.alloc_local("i32")
        i = self.alloc_local("i32")    # input index
        j = self.alloc_local("i32")    # output index
        ch = self.alloc_local("i32")   # current byte

        ins: list[str] = []

        # Evaluate string arg → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Empty input → empty output
        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if (result i32 i32)")
        ins.append(f"  i32.const {empty_off}")
        ins.append(f"  i32.const {empty_len}")
        ins.append("else")

        # First pass: count output length
        # Each byte is either 1 (unreserved) or 3 (%XX)
        ins.append("i32.const 0")
        ins.append(f"local.set {out_len}")
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("block $brk_cnt")
        ins.append("  loop $lp_cnt")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_cnt")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {ch}")

        # Check if unreserved: A-Z || a-z || 0-9 || '-' || '_' || '.' || '~'
        ins.append("    block $unreserved_c")
        # A-Z (65-90)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 65")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 90")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_c")
        # a-z (97-122)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 97")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 122")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_c")
        # 0-9 (48-57)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 48")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 57")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_c")
        # '-' (45)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 45")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_c")
        # '_' (95)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 95")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_c")
        # '.' (46)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 46")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_c")
        # '~' (126)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 126")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_c")

        # Reserved: out_len += 3
        ins.append(f"    local.get {out_len}")
        ins.append("    i32.const 3")
        ins.append("    i32.add")
        ins.append(f"    local.set {out_len}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_cnt")
        ins.append("    end")  # block $unreserved_c

        # Unreserved: out_len += 1
        ins.append(f"    local.get {out_len}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {out_len}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_cnt")
        ins.append("  end")  # loop
        ins.append("end")    # block $brk_cnt

        # Allocate output buffer
        ins.append(f"local.get {out_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # Second pass: write encoded output
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {j}")
        ins.append("block $brk_enc")
        ins.append("  loop $lp_enc")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_enc")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {ch}")

        # Check if unreserved (same logic as counting pass)
        ins.append("    block $unreserved_e")
        # A-Z
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 65")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 90")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_e")
        # a-z
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 97")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 122")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_e")
        # 0-9
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 48")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 57")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_e")
        # '-'
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 45")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_e")
        # '_'
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 95")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_e")
        # '.'
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 46")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_e")
        # '~'
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 126")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_e")

        # Reserved: write '%', hex_hi, hex_lo
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append("    i32.const 37")         # '%'
        ins.append("    i32.store8 offset=0")
        # High nibble: hex[ch >> 4]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {hex_off}")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 4")
        ins.append("    i32.shr_u")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=1")
        # Low nibble: hex[ch & 0xF]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {hex_off}")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 15")
        ins.append("    i32.and")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=2")
        # j += 3
        ins.append(f"    local.get {j}")
        ins.append("    i32.const 3")
        ins.append("    i32.add")
        ins.append(f"    local.set {j}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_enc")
        ins.append("    end")  # block $unreserved_e

        # Unreserved: copy byte directly
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.store8 offset=0")
        # j += 1
        ins.append(f"    local.get {j}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {j}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_enc")
        ins.append("  end")  # loop
        ins.append("end")    # block $brk_enc

        # Leave (dst, out_len) on the stack
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {out_len}")

        ins.append("end")  # else branch of empty check

        return ins

    def _translate_url_decode(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate url_decode(s) → Result<String, String> (i32 ptr).

        Decodes percent-encoded strings (RFC 3986).  Each %XX sequence
        is converted to the byte with that hex value.  Returns Err on
        invalid sequences (truncated %, invalid hex digits).

        ADT layout (16 bytes):
          Ok(String):  [tag=0 : i32] [ptr : i32] [len : i32] [pad 4]
          Err(String): [tag=1 : i32] [ptr : i32] [len : i32] [pad 4]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        err_off, err_ln = self.string_pool.intern("invalid percent-encoding")
        empty_off, empty_len = self.string_pool.intern("")

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        out = self.alloc_local("i32")    # Result ADT pointer
        dst = self.alloc_local("i32")    # decoded bytes pointer
        out_len = self.alloc_local("i32")
        i = self.alloc_local("i32")      # input index
        k = self.alloc_local("i32")      # output index
        ch = self.alloc_local("i32")     # current byte
        hi = self.alloc_local("i32")     # high hex nibble value
        lo = self.alloc_local("i32")     # low hex nibble value

        ins: list[str] = []

        # Evaluate string arg → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        ins.append("block $done_ud")
        ins.append("block $err_ud")

        # Empty input → Ok("")
        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if")
        ins.append("  i32.const 16")
        ins.append("  call $alloc")
        ins.append(f"  local.tee {out}")
        ins.append("  i32.const 0")
        ins.append("  i32.store")              # tag = 0 (Ok)
        ins.extend(["  " + x for x in gc_shadow_push(out)])
        ins.append(f"  local.get {out}")
        ins.append(f"  i32.const {empty_off}")
        ins.append("  i32.store offset=4")
        ins.append(f"  local.get {out}")
        ins.append(f"  i32.const {empty_len}")
        ins.append("  i32.store offset=8")
        ins.append("  br $done_ud")
        ins.append("end")

        # Allocate output buffer (at most slen bytes — decoding shrinks)
        ins.append(f"local.get {slen}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # Decode loop
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {k}")

        ins.append("block $brk_dl")
        ins.append("  loop $lp_dl")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_dl")

        # Load current byte
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {ch}")

        # Check if '%' (37)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 37")
        ins.append("    i32.eq")
        ins.append("    if")

        # Need at least 2 more bytes
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 2")
        ins.append("      i32.add")
        ins.append(f"      local.get {slen}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $err_ud")

        # Decode high nibble (i+1)
        ins.append(f"      local.get {ptr}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=1")
        ins.append(f"      local.set {ch}")

        # Convert hex char to value (hi)
        ins.append("      block $hi_ok")
        ins.append("      block $hi_bad")
        # 0-9 (48-57) → 0-9
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 48")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 57")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 48")
        ins.append("        i32.sub")
        ins.append(f"        local.set {hi}")
        ins.append("        br $hi_ok")
        ins.append("      end")
        # A-F (65-70) → 10-15
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 65")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 70")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 55")
        ins.append("        i32.sub")
        ins.append(f"        local.set {hi}")
        ins.append("        br $hi_ok")
        ins.append("      end")
        # a-f (97-102) → 10-15
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 97")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 102")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 87")
        ins.append("        i32.sub")
        ins.append(f"        local.set {hi}")
        ins.append("        br $hi_ok")
        ins.append("      end")
        ins.append("      br $hi_bad")
        ins.append("      end")  # block $hi_bad
        ins.append("      br $err_ud")
        ins.append("      end")  # block $hi_ok

        # Decode low nibble (i+2)
        ins.append(f"      local.get {ptr}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=2")
        ins.append(f"      local.set {ch}")

        # Convert hex char to value (lo)
        ins.append("      block $lo_ok")
        ins.append("      block $lo_bad")
        # 0-9
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 48")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 57")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 48")
        ins.append("        i32.sub")
        ins.append(f"        local.set {lo}")
        ins.append("        br $lo_ok")
        ins.append("      end")
        # A-F
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 65")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 70")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 55")
        ins.append("        i32.sub")
        ins.append(f"        local.set {lo}")
        ins.append("        br $lo_ok")
        ins.append("      end")
        # a-f
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 97")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 102")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 87")
        ins.append("        i32.sub")
        ins.append(f"        local.set {lo}")
        ins.append("        br $lo_ok")
        ins.append("      end")
        ins.append("      br $lo_bad")
        ins.append("      end")  # block $lo_bad
        ins.append("      br $err_ud")
        ins.append("      end")  # block $lo_ok

        # Store decoded byte: (hi << 4) | lo
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {k}")
        ins.append("      i32.add")
        ins.append(f"      local.get {hi}")
        ins.append("      i32.const 4")
        ins.append("      i32.shl")
        ins.append(f"      local.get {lo}")
        ins.append("      i32.or")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {k}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {k}")
        # i += 3
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 3")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")

        ins.append("    else")

        # Not '%': copy byte directly
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {k}")
        ins.append("      i32.add")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {k}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {k}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")

        ins.append("    end")  # if '%'

        ins.append("    br $lp_dl")
        ins.append("  end")  # loop
        ins.append("end")    # block $brk_dl

        # --- Ok path ---
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")                # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {dst}")
        ins.append("i32.store offset=4")       # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"local.get {k}")
        ins.append("i32.store offset=8")       # string len
        ins.append("br $done_ud")

        # --- Err path ---
        ins.append("end")  # block $err_ud
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")                # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_off}")
        ins.append("i32.store offset=4")
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_ln}")
        ins.append("i32.store offset=8")

        ins.append("end")  # block $done_ud

        ins.append(f"local.get {out}")
        return ins

    def _translate_url_parse(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate url_parse(s) → Result<UrlParts, String> (i32 ptr).

        RFC 3986 simplified URL decomposition.  Scans the input for
        delimiters (:, ://, /, ?, #) and records each component as a
        substring of the original input (no copies needed for scheme,
        authority, path, query, fragment).

        UrlParts layout (48 bytes):
          [tag=0     : i32 @ 0 ]
          [scheme_ptr: i32 @ 4 ] [scheme_len: i32 @ 8 ]
          [auth_ptr  : i32 @ 12] [auth_len  : i32 @ 16]
          [path_ptr  : i32 @ 20] [path_len  : i32 @ 24]
          [query_ptr : i32 @ 28] [query_len : i32 @ 32]
          [frag_ptr  : i32 @ 36] [frag_len  : i32 @ 40]
          [pad 4     @ 44]

        Result layout (16 bytes):
          Ok(UrlParts):  [tag=0 : i32] [urlparts_ptr : i32] [pad 8]
          Err(String):   [tag=1 : i32] [ptr : i32] [len : i32] [pad 4]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        err_off, err_ln = self.string_pool.intern("missing scheme")
        empty_off, empty_len = self.string_pool.intern("")

        # Input string
        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        # Scanning index
        i = self.alloc_local("i32")
        ch = self.alloc_local("i32")
        # Component boundaries (offsets relative to ptr)
        colon_pos = self.alloc_local("i32")   # position of first ':'
        auth_start = self.alloc_local("i32")  # start of authority
        auth_end = self.alloc_local("i32")    # end of authority
        path_start = self.alloc_local("i32")  # start of path
        path_end = self.alloc_local("i32")    # end of path
        query_start = self.alloc_local("i32")  # start of query (after '?')
        query_end = self.alloc_local("i32")    # end of query
        frag_start = self.alloc_local("i32")   # start of fragment (after '#')
        has_auth = self.alloc_local("i32")     # bool: found ://
        has_query = self.alloc_local("i32")    # bool: found ?
        has_frag = self.alloc_local("i32")     # bool: found #
        # Output pointers
        up = self.alloc_local("i32")   # UrlParts heap pointer
        out = self.alloc_local("i32")  # Result heap pointer

        ins: list[str] = []

        # Evaluate string arg → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        ins.append("block $done_up")
        ins.append("block $err_up")

        # ---- Step 1: Find colon (scheme delimiter) ----
        # Scan for first ':'
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const -1")
        ins.append(f"local.set {colon_pos}")

        ins.append("block $found_colon")
        ins.append("  loop $scan_colon")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    if")
        # No colon found → Err
        ins.append("      br $err_up")
        ins.append("    end")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {ch}")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 58")   # ':'
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.set {colon_pos}")
        ins.append("      br $found_colon")
        ins.append("    end")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $scan_colon")
        ins.append("  end")  # loop
        ins.append("end")    # block $found_colon

        # scheme is input[0..colon_pos]
        # Now check if :// follows the colon

        # ---- Step 2: Check for :// (authority indicator) ----
        ins.append("i32.const 0")
        ins.append(f"local.set {has_auth}")

        # Need colon_pos + 3 <= slen  and  input[colon_pos+1] == '/'
        # and input[colon_pos+2] == '/'
        ins.append(f"local.get {colon_pos}")
        ins.append("i32.const 3")
        ins.append("i32.add")
        ins.append(f"local.get {slen}")
        ins.append("i32.le_u")
        ins.append("if")
        # Check input[colon_pos+1] == '/' (47)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {colon_pos}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=1")
        ins.append("  i32.const 47")
        ins.append("  i32.eq")
        ins.append("  if")
        # Check input[colon_pos+2] == '/' (47)
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {colon_pos}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=2")
        ins.append("    i32.const 47")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {has_auth}")
        ins.append("    end")
        ins.append("  end")
        ins.append("end")

        # ---- Step 3: Determine authority, path, query, fragment ----
        # Set cursor position after scheme
        ins.append("i32.const 0")
        ins.append(f"local.set {has_query}")
        ins.append("i32.const 0")
        ins.append(f"local.set {has_frag}")

        # If has_auth: cursor = colon_pos + 3 (after ://)
        # Else: cursor = colon_pos + 1 (after :)
        ins.append(f"local.get {has_auth}")
        ins.append("if")
        ins.append(f"  local.get {colon_pos}")
        ins.append("  i32.const 3")
        ins.append("  i32.add")
        ins.append(f"  local.set {auth_start}")
        ins.append("else")
        # No authority — set auth to empty
        ins.append(f"  local.get {colon_pos}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {auth_start}")
        ins.append("end")

        # auth_end = auth_start initially (will scan to find end)
        ins.append(f"local.get {auth_start}")
        ins.append(f"local.set {auth_end}")

        # If has_auth: scan authority until /, ?, #, or end
        ins.append(f"local.get {has_auth}")
        ins.append("if")
        ins.append(f"  local.get {auth_start}")
        ins.append(f"  local.set {i}")
        ins.append("  block $auth_done")
        ins.append("    loop $scan_auth")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {slen}")
        ins.append("      i32.ge_u")
        ins.append("      if")
        ins.append(f"        local.get {i}")
        ins.append(f"        local.set {auth_end}")
        ins.append("        br $auth_done")
        ins.append("      end")
        ins.append(f"      local.get {ptr}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append(f"      local.set {ch}")
        # Check for / (47), ? (63), # (35)
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 47")
        ins.append("      i32.eq")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 63")
        ins.append("      i32.eq")
        ins.append("      i32.or")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 35")
        ins.append("      i32.eq")
        ins.append("      i32.or")
        ins.append("      if")
        ins.append(f"        local.get {i}")
        ins.append(f"        local.set {auth_end}")
        ins.append("        br $auth_done")
        ins.append("      end")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("      br $scan_auth")
        ins.append("    end")  # loop
        ins.append("  end")    # block $auth_done
        ins.append("else")
        # No authority: auth_end = auth_start (empty)
        ins.append(f"  local.get {auth_start}")
        ins.append(f"  local.set {auth_end}")
        ins.append("end")

        # ---- Path: from auth_end until ? or # or end ----
        ins.append(f"local.get {auth_end}")
        ins.append(f"local.set {path_start}")
        ins.append(f"local.get {auth_end}")
        ins.append(f"local.set {i}")

        ins.append("block $path_done")
        ins.append("  loop $scan_path")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    if")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.set {path_end}")
        ins.append("      br $path_done")
        ins.append("    end")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {ch}")
        # Check for ? (63) or # (35)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 63")
        ins.append("    i32.eq")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 35")
        ins.append("    i32.eq")
        ins.append("    i32.or")
        ins.append("    if")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.set {path_end}")
        ins.append("      br $path_done")
        ins.append("    end")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $scan_path")
        ins.append("  end")  # loop
        ins.append("end")    # block $path_done

        # ---- Query: if input[path_end] == '?', scan until # or end ----
        ins.append(f"local.get {path_end}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {path_end}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.const 63")   # '?'
        ins.append("  i32.eq")
        ins.append("  if")
        ins.append("    i32.const 1")
        ins.append(f"    local.set {has_query}")
        ins.append(f"    local.get {path_end}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {query_start}")
        # Scan query until # or end
        ins.append(f"    local.get {query_start}")
        ins.append(f"    local.set {i}")
        ins.append("    block $query_done")
        ins.append("      loop $scan_query")
        ins.append(f"        local.get {i}")
        ins.append(f"        local.get {slen}")
        ins.append("        i32.ge_u")
        ins.append("        if")
        ins.append(f"          local.get {i}")
        ins.append(f"          local.set {query_end}")
        ins.append("          br $query_done")
        ins.append("        end")
        ins.append(f"        local.get {ptr}")
        ins.append(f"        local.get {i}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append("        i32.const 35")   # '#'
        ins.append("        i32.eq")
        ins.append("        if")
        ins.append(f"          local.get {i}")
        ins.append(f"          local.set {query_end}")
        ins.append("          br $query_done")
        ins.append("        end")
        ins.append(f"        local.get {i}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {i}")
        ins.append("        br $scan_query")
        ins.append("      end")  # loop
        ins.append("    end")    # block $query_done
        ins.append("  end")  # if '?'
        ins.append("end")   # if path_end < slen

        # ---- Fragment: check after query (or after path if no query) ----
        # The fragment start is wherever we stopped + 1 if we see '#'
        # We need to check: if has_query, check at query_end; else at path_end
        ins.append(f"local.get {has_query}")
        ins.append("if")
        # Check if query_end < slen and input[query_end] == '#'
        ins.append(f"  local.get {query_end}")
        ins.append(f"  local.get {slen}")
        ins.append("  i32.lt_u")
        ins.append("  if")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {query_end}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 35")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {has_frag}")
        ins.append(f"      local.get {query_end}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {frag_start}")
        ins.append("    end")
        ins.append("  end")
        ins.append("else")
        # No query — check at path_end for '#'
        ins.append(f"  local.get {path_end}")
        ins.append(f"  local.get {slen}")
        ins.append("  i32.lt_u")
        ins.append("  if")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {path_end}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 35")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {has_frag}")
        ins.append(f"      local.get {path_end}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {frag_start}")
        ins.append("    end")
        ins.append("  end")
        ins.append("end")

        # ---- Step 4: Allocate UrlParts (48 bytes) ----
        ins.append("i32.const 48")
        ins.append("call $alloc")
        ins.append(f"local.tee {up}")
        ins.append("i32.const 0")
        ins.append("i32.store")              # tag = 0 (UrlParts constructor)
        ins.extend(gc_shadow_push(up))

        # Scheme: input[0..colon_pos]
        ins.append(f"local.get {up}")
        ins.append(f"local.get {ptr}")
        ins.append("i32.store offset=4")     # scheme_ptr
        ins.append(f"local.get {up}")
        ins.append(f"local.get {colon_pos}")
        ins.append("i32.store offset=8")     # scheme_len

        # Authority: input[auth_start..auth_end]  (empty if no ://)
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_auth}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {auth_start}")
        ins.append("  i32.add")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append("i32.store offset=12")    # auth_ptr
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_auth}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {auth_end}")
        ins.append(f"  local.get {auth_start}")
        ins.append("  i32.sub")
        ins.append("else")
        ins.append(f"  i32.const {empty_len}")
        ins.append("end")
        ins.append("i32.store offset=16")    # auth_len

        # Path: input[path_start..path_end]
        ins.append(f"local.get {up}")
        ins.append(f"local.get {path_start}")
        ins.append(f"local.get {path_end}")
        ins.append("i32.lt_u")
        ins.append("if (result i32)")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {path_start}")
        ins.append("  i32.add")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append("i32.store offset=20")    # path_ptr
        ins.append(f"local.get {up}")
        ins.append(f"local.get {path_end}")
        ins.append(f"local.get {path_start}")
        ins.append("i32.sub")
        ins.append("i32.store offset=24")    # path_len

        # Query: input[query_start..query_end]  (empty if no ?)
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_query}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {query_start}")
        ins.append("  i32.add")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append("i32.store offset=28")    # query_ptr
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_query}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {query_end}")
        ins.append(f"  local.get {query_start}")
        ins.append("  i32.sub")
        ins.append("else")
        ins.append(f"  i32.const {empty_len}")
        ins.append("end")
        ins.append("i32.store offset=32")    # query_len

        # Fragment: input[frag_start..slen]  (empty if no #)
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_frag}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {frag_start}")
        ins.append("  i32.add")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append("i32.store offset=36")    # frag_ptr
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_frag}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {slen}")
        ins.append(f"  local.get {frag_start}")
        ins.append("  i32.sub")
        ins.append("else")
        ins.append(f"  i32.const {empty_len}")
        ins.append("end")
        ins.append("i32.store offset=40")    # frag_len

        # ---- Step 5: Allocate Result (16 bytes), Ok(UrlParts) ----
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")              # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {up}")
        ins.append("i32.store offset=4")     # UrlParts ptr
        ins.append("br $done_up")

        # ---- Err path ----
        ins.append("end")  # block $err_up
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")              # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_off}")
        ins.append("i32.store offset=4")
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_ln}")
        ins.append("i32.store offset=8")

        ins.append("end")  # block $done_up

        ins.append(f"local.get {out}")
        return ins

    def _translate_url_join(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate url_join(parts) → String (i32_pair).

        Takes a UrlParts heap pointer and reassembles a URL string.
        Components: scheme://authority/path?query#fragment
        Empty components are omitted (including their delimiters).

        The argument is an i32 (heap pointer to UrlParts struct).
        Returns i32_pair (ptr, len) on the stack.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        # Intern "://" for the scheme separator
        sep_off, sep_len = self.string_pool.intern("://")
        q_off, _ = self.string_pool.intern("?")
        h_off, _ = self.string_pool.intern("#")

        # UrlParts pointer
        up = self.alloc_local("i32")
        # Component locals (5 pairs: ptr, len)
        s_ptr = self.alloc_local("i32")    # scheme
        s_len = self.alloc_local("i32")
        a_ptr = self.alloc_local("i32")    # authority
        a_len = self.alloc_local("i32")
        p_ptr = self.alloc_local("i32")    # path
        p_len = self.alloc_local("i32")
        q_ptr = self.alloc_local("i32")    # query
        q_len = self.alloc_local("i32")
        f_ptr = self.alloc_local("i32")    # fragment
        f_len = self.alloc_local("i32")
        # Output
        total = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        k = self.alloc_local("i32")        # write cursor

        ins: list[str] = []

        # Evaluate arg → i32 (UrlParts heap pointer)
        ins.extend(arg_instrs)
        ins.append(f"local.set {up}")

        # Load all 5 String fields (each is ptr + len at known offsets)
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=4")
        ins.append(f"local.set {s_ptr}")
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=8")
        ins.append(f"local.set {s_len}")

        ins.append(f"local.get {up}")
        ins.append("i32.load offset=12")
        ins.append(f"local.set {a_ptr}")
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=16")
        ins.append(f"local.set {a_len}")

        ins.append(f"local.get {up}")
        ins.append("i32.load offset=20")
        ins.append(f"local.set {p_ptr}")
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=24")
        ins.append(f"local.set {p_len}")

        ins.append(f"local.get {up}")
        ins.append("i32.load offset=28")
        ins.append(f"local.set {q_ptr}")
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=32")
        ins.append(f"local.set {q_len}")

        ins.append(f"local.get {up}")
        ins.append("i32.load offset=36")
        ins.append(f"local.set {f_ptr}")
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=40")
        ins.append(f"local.set {f_len}")

        # ---- Pass 1: compute total output length ----
        # total = scheme_len + path_len
        ins.append(f"local.get {s_len}")
        ins.append(f"local.get {p_len}")
        ins.append("i32.add")
        ins.append(f"local.set {total}")
        # If scheme_len > 0: total += 3 (for "://")
        ins.append(f"local.get {s_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {total}")
        ins.append("  i32.const 3")
        ins.append("  i32.add")
        ins.append(f"  local.set {total}")
        ins.append("end")
        # total += auth_len
        ins.append(f"local.get {total}")
        ins.append(f"local.get {a_len}")
        ins.append("i32.add")
        ins.append(f"local.set {total}")
        # If query_len > 0: total += 1 + query_len
        ins.append(f"local.get {q_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {total}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.get {q_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {total}")
        ins.append("end")
        # If frag_len > 0: total += 1 + frag_len
        ins.append(f"local.get {f_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {total}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.get {f_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {total}")
        ins.append("end")

        # If total == 0: skip allocation, use empty string
        empty_off2, empty_len2 = self.string_pool.intern("")
        ins.append(f"local.get {total}")
        ins.append("i32.eqz")
        ins.append("if")
        ins.append(f"  i32.const {empty_off2}")
        ins.append(f"  local.set {dst}")
        ins.append("end")

        ins.append("block $uj_done")
        ins.append(f"local.get {total}")
        ins.append("i32.eqz")
        ins.append("br_if $uj_done")

        # ---- Pass 2: allocate and write ----
        ins.append(f"local.get {total}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        ins.append("i32.const 0")
        ins.append(f"local.set {k}")

        # If scheme non-empty: copy scheme, write "://"
        ins.append(f"local.get {s_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        # memory.copy(dst+k, s_ptr, s_len)
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  local.get {s_ptr}")
        ins.append(f"  local.get {s_len}")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append(f"  local.get {s_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        # Write "://" (3 bytes from string pool)
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {sep_off}")
        ins.append("  i32.const 3")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append("  i32.const 3")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        ins.append("end")

        # Copy authority (even if empty — zero-length copy is a no-op)
        ins.append(f"local.get {a_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  local.get {a_ptr}")
        ins.append(f"  local.get {a_len}")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append(f"  local.get {a_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        ins.append("end")

        # Copy path
        ins.append(f"local.get {p_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  local.get {p_ptr}")
        ins.append(f"  local.get {p_len}")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append(f"  local.get {p_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        ins.append("end")

        # If query non-empty: write "?" + query
        ins.append(f"local.get {q_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        # Write '?' (1 byte)
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append("  i32.const 63")   # '?'
        ins.append("  i32.store8 offset=0")
        ins.append(f"  local.get {k}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        # Copy query
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  local.get {q_ptr}")
        ins.append(f"  local.get {q_len}")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append(f"  local.get {q_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        ins.append("end")

        # If fragment non-empty: write "#" + fragment
        ins.append(f"local.get {f_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        # Write '#' (1 byte)
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append("  i32.const 35")   # '#'
        ins.append("  i32.store8 offset=0")
        ins.append(f"  local.get {k}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        # Copy fragment
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  local.get {f_ptr}")
        ins.append(f"  local.get {f_len}")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append(f"  local.get {f_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        ins.append("end")

        ins.append("end")  # block $uj_done

        # Return (dst, total) as i32_pair
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {total}")
        return ins

    # ---- Json host-import builtins ------------------------------------

    def _translate_json_parse(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """json_parse(s) → Result<Json, String> via host import.

        String arg is (ptr, len) pair on stack → call $vera.json_parse → i32.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        self._json_ops_used.add("json_parse")
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.json_parse")
        return ins

    def _translate_json_stringify(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """json_stringify(j) → String via host import.

        Json arg is i32 heap pointer → call $vera.json_stringify → (i32, i32).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        self._json_ops_used.add("json_stringify")
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.json_stringify")
        return ins

    # ---- Html host-import builtins ------------------------------------

    def _translate_html_parse(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """html_parse(s) -> Result<HtmlNode, String> via host import.

        String arg is (ptr, len) pair on stack -> call $vera.html_parse -> i32.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        self._html_ops_used.add("html_parse")
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.html_parse")
        return ins

    def _translate_html_to_string(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """html_to_string(node) -> String via host import.

        HtmlNode arg is i32 heap pointer -> call $vera.html_to_string -> (i32, i32).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        self._html_ops_used.add("html_to_string")
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.html_to_string")
        return ins

    def _translate_html_query(
        self, node_arg: ast.Expr, sel_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """html_query(node, selector) -> Array<HtmlNode> via host import.

        HtmlNode is i32, selector String is (ptr, len) -> call $vera.html_query -> (i32, i32).
        """
        node_instrs = self.translate_expr(node_arg, env)
        sel_instrs = self.translate_expr(sel_arg, env)
        if node_instrs is None or sel_instrs is None:
            return None
        self.needs_alloc = True
        self._html_ops_used.add("html_query")
        ins: list[str] = []
        ins.extend(node_instrs)
        ins.extend(sel_instrs)
        ins.append("call $vera.html_query")
        return ins

    def _translate_html_text(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """html_text(node) -> String via host import.

        HtmlNode is i32 heap pointer -> call $vera.html_text -> (i32, i32).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        self._html_ops_used.add("html_text")
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.html_text")
        return ins

    # ---- Markdown host-import builtins ---------------------------------

    def _translate_md_parse(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """md_parse(s) → Result<MdBlock, String> via host import.

        String arg is (ptr, len) pair on stack → call $vera.md_parse → i32.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.md_parse")
        return ins

    def _translate_md_render(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """md_render(block) → String via host import.

        MdBlock arg is i32 (heap ptr) → call $vera.md_render → (i32, i32).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.md_render")
        return ins

    def _translate_md_has_heading(
        self, block_arg: ast.Expr, level_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """md_has_heading(block, level) → Bool via host import.

        (i32 ptr, i64 level) → call $vera.md_has_heading → i32.
        """
        b_instrs = self.translate_expr(block_arg, env)
        l_instrs = self.translate_expr(level_arg, env)
        if b_instrs is None or l_instrs is None:
            return None
        ins: list[str] = []
        ins.extend(b_instrs)
        ins.extend(l_instrs)
        ins.append("call $vera.md_has_heading")
        return ins

    def _translate_md_has_code_block(
        self, block_arg: ast.Expr, lang_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """md_has_code_block(block, lang) → Bool via host import.

        (i32 ptr, i32 lang_ptr, i32 lang_len) → call → i32.
        """
        b_instrs = self.translate_expr(block_arg, env)
        l_instrs = self.translate_expr(lang_arg, env)
        if b_instrs is None or l_instrs is None:
            return None
        ins: list[str] = []
        ins.extend(b_instrs)
        ins.extend(l_instrs)
        ins.append("call $vera.md_has_code_block")
        return ins

    def _translate_md_extract_code_blocks(
        self, block_arg: ast.Expr, lang_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """md_extract_code_blocks(block, lang) → Array<String> via host import.

        (i32 ptr, i32 lang_ptr, i32 lang_len) → call → (i32, i32).
        """
        b_instrs = self.translate_expr(block_arg, env)
        l_instrs = self.translate_expr(lang_arg, env)
        if b_instrs is None or l_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(b_instrs)
        ins.extend(l_instrs)
        ins.append("call $vera.md_extract_code_blocks")
        return ins

    # ---- Regex host-import builtins -------------------------------------

    def _translate_regex_match(
        self, input_arg: ast.Expr, pattern_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """regex_match(input, pattern) → Result<Bool, String> via host import.

        Two string args → (i32, i32, i32, i32) → call $vera.regex_match → i32.
        """
        in_instrs = self.translate_expr(input_arg, env)
        pat_instrs = self.translate_expr(pattern_arg, env)
        if in_instrs is None or pat_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(in_instrs)
        ins.extend(pat_instrs)
        ins.append("call $vera.regex_match")
        return ins

    def _translate_regex_find(
        self, input_arg: ast.Expr, pattern_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """regex_find(input, pattern) → Result<Option<String>, String>.

        Two string args → (i32, i32, i32, i32) → call $vera.regex_find → i32.
        """
        in_instrs = self.translate_expr(input_arg, env)
        pat_instrs = self.translate_expr(pattern_arg, env)
        if in_instrs is None or pat_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(in_instrs)
        ins.extend(pat_instrs)
        ins.append("call $vera.regex_find")
        return ins

    def _translate_regex_find_all(
        self, input_arg: ast.Expr, pattern_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """regex_find_all(input, pattern) → Result<Array<String>, String>.

        Two string args → (i32, i32, i32, i32) → call → i32.
        """
        in_instrs = self.translate_expr(input_arg, env)
        pat_instrs = self.translate_expr(pattern_arg, env)
        if in_instrs is None or pat_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(in_instrs)
        ins.extend(pat_instrs)
        ins.append("call $vera.regex_find_all")
        return ins

    def _translate_regex_replace(
        self, input_arg: ast.Expr, pattern_arg: ast.Expr,
        replacement_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """regex_replace(input, pattern, replacement) → Result<String, String>.

        Three string args → (i32, i32, i32, i32, i32, i32) → call → i32.
        """
        in_instrs = self.translate_expr(input_arg, env)
        pat_instrs = self.translate_expr(pattern_arg, env)
        rep_instrs = self.translate_expr(replacement_arg, env)
        if in_instrs is None or pat_instrs is None or rep_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(in_instrs)
        ins.extend(pat_instrs)
        ins.extend(rep_instrs)
        ins.append("call $vera.regex_replace")
        return ins

    # ---- Async builtins -----------------------------------------------

    def _translate_async(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate async(expr) → Future<T> (identity, eager evaluation).

        The reference implementation evaluates async(expr) eagerly.
        Future<T> is WASM-transparent — same representation as T.
        True concurrency will be available via WASI 0.3 (#237).
        """
        return self.translate_expr(arg, env)

    def _translate_await(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate await(future) → T (identity unwrap).

        Future<T> is WASM-transparent, so await is a no-op.
        """
        return self.translate_expr(arg, env)

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

    # -----------------------------------------------------------------
    # Numeric math builtins
    # -----------------------------------------------------------------

    def _translate_abs(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate abs(@Int) → @Nat (i64).

        WASM has no i64.abs; uses ``select`` on (value, -value, value>=0).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        tmp = self.alloc_local("i64")
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {tmp}")
        # select(val_if_true, val_if_false, cond)
        instructions.append(f"local.get {tmp}")          # value (cond true)
        instructions.append("i64.const 0")
        instructions.append(f"local.get {tmp}")
        instructions.append("i64.sub")                    # -value (cond false)
        instructions.append(f"local.get {tmp}")
        instructions.append("i64.const 0")
        instructions.append("i64.ge_s")                   # value >= 0
        instructions.append("select")
        return instructions

    def _translate_min(
        self, arg_a: ast.Expr, arg_b: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate min(@Int, @Int) → @Int.

        Uses ``i64.lt_s`` + ``select``.
        """
        a_instrs = self.translate_expr(arg_a, env)
        b_instrs = self.translate_expr(arg_b, env)
        if a_instrs is None or b_instrs is None:
            return None
        tmp_a = self.alloc_local("i64")
        tmp_b = self.alloc_local("i64")
        instructions: list[str] = []
        instructions.extend(a_instrs)
        instructions.append(f"local.set {tmp_a}")
        instructions.extend(b_instrs)
        instructions.append(f"local.set {tmp_b}")
        # select(a, b, a < b) → a if a < b else b
        instructions.append(f"local.get {tmp_a}")
        instructions.append(f"local.get {tmp_b}")
        instructions.append(f"local.get {tmp_a}")
        instructions.append(f"local.get {tmp_b}")
        instructions.append("i64.lt_s")
        instructions.append("select")
        return instructions

    def _translate_max(
        self, arg_a: ast.Expr, arg_b: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate max(@Int, @Int) → @Int.

        Uses ``i64.gt_s`` + ``select``.
        """
        a_instrs = self.translate_expr(arg_a, env)
        b_instrs = self.translate_expr(arg_b, env)
        if a_instrs is None or b_instrs is None:
            return None
        tmp_a = self.alloc_local("i64")
        tmp_b = self.alloc_local("i64")
        instructions: list[str] = []
        instructions.extend(a_instrs)
        instructions.append(f"local.set {tmp_a}")
        instructions.extend(b_instrs)
        instructions.append(f"local.set {tmp_b}")
        # select(a, b, a > b) → a if a > b else b
        instructions.append(f"local.get {tmp_a}")
        instructions.append(f"local.get {tmp_b}")
        instructions.append(f"local.get {tmp_a}")
        instructions.append(f"local.get {tmp_b}")
        instructions.append("i64.gt_s")
        instructions.append("select")
        return instructions

    def _translate_floor(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate floor(@Float64) → @Int.

        WASM: ``f64.floor`` then ``i64.trunc_f64_s``.
        Traps on NaN or values outside the i64 range.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        instructions.append("f64.floor")
        instructions.append("i64.trunc_f64_s")
        return instructions

    def _translate_ceil(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate ceil(@Float64) → @Int.

        WASM: ``f64.ceil`` then ``i64.trunc_f64_s``.
        Traps on NaN or values outside the i64 range.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        instructions.append("f64.ceil")
        instructions.append("i64.trunc_f64_s")
        return instructions

    def _translate_round(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate round(@Float64) → @Int.

        WASM: ``f64.nearest`` (IEEE 754 roundTiesToEven, aka banker's
        rounding) then ``i64.trunc_f64_s``.
        Traps on NaN or values outside the i64 range.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        instructions.append("f64.nearest")
        instructions.append("i64.trunc_f64_s")
        return instructions

    def _translate_sqrt(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate sqrt(@Float64) → @Float64.

        Single WASM instruction: ``f64.sqrt``.
        Returns NaN for negative inputs (IEEE 754).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        instructions.append("f64.sqrt")
        return instructions

    def _translate_pow(
        self, base_arg: ast.Expr, exp_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate pow(@Float64, @Int) → @Float64.

        Exponentiation by squaring.  Handles negative exponents by
        computing the reciprocal: ``pow(x, -n) = 1.0 / pow(x, n)``.
        """
        base_instrs = self.translate_expr(base_arg, env)
        exp_instrs = self.translate_expr(exp_arg, env)
        if base_instrs is None or exp_instrs is None:
            return None
        base_tmp = self.alloc_local("f64")
        exp_tmp = self.alloc_local("i64")
        result_tmp = self.alloc_local("f64")
        b_tmp = self.alloc_local("f64")
        neg_flag = self.alloc_local("i32")
        instructions: list[str] = []
        # Evaluate and store base
        instructions.extend(base_instrs)
        instructions.append(f"local.set {base_tmp}")
        # Evaluate exponent (already i64 from Int)
        instructions.extend(exp_instrs)
        instructions.append(f"local.set {exp_tmp}")
        # Handle negative exponent: save flag, negate if needed
        instructions.append(f"local.get {exp_tmp}")
        instructions.append("i64.const 0")
        instructions.append("i64.lt_s")
        instructions.append(f"local.set {neg_flag}")
        instructions.append(f"local.get {neg_flag}")
        instructions.append("if")
        instructions.append(f"  i64.const 0")
        instructions.append(f"  local.get {exp_tmp}")
        instructions.append(f"  i64.sub")
        instructions.append(f"  local.set {exp_tmp}")
        instructions.append("end")
        # result = 1.0, b = base
        instructions.append("f64.const 1.0")
        instructions.append(f"local.set {result_tmp}")
        instructions.append(f"local.get {base_tmp}")
        instructions.append(f"local.set {b_tmp}")
        # Loop: exponentiation by squaring
        instructions.append("block $pow_break")
        instructions.append("  loop $pow_loop")
        instructions.append(f"    local.get {exp_tmp}")
        instructions.append("    i64.eqz")
        instructions.append("    br_if $pow_break")
        # if exp & 1: result *= b
        instructions.append(f"    local.get {exp_tmp}")
        instructions.append("    i64.const 1")
        instructions.append("    i64.and")
        instructions.append("    i64.const 1")
        instructions.append("    i64.eq")
        instructions.append("    if")
        instructions.append(f"      local.get {result_tmp}")
        instructions.append(f"      local.get {b_tmp}")
        instructions.append("      f64.mul")
        instructions.append(f"      local.set {result_tmp}")
        instructions.append("    end")
        # b *= b
        instructions.append(f"    local.get {b_tmp}")
        instructions.append(f"    local.get {b_tmp}")
        instructions.append("    f64.mul")
        instructions.append(f"    local.set {b_tmp}")
        # exp >>= 1
        instructions.append(f"    local.get {exp_tmp}")
        instructions.append("    i64.const 1")
        instructions.append("    i64.shr_u")
        instructions.append(f"    local.set {exp_tmp}")
        instructions.append("    br $pow_loop")
        instructions.append("  end")
        instructions.append("end")
        # If negative exponent: result = 1.0 / result
        instructions.append(f"local.get {neg_flag}")
        instructions.append("if")
        instructions.append("  f64.const 1.0")
        instructions.append(f"  local.get {result_tmp}")
        instructions.append("  f64.div")
        instructions.append(f"  local.set {result_tmp}")
        instructions.append("end")
        instructions.append(f"local.get {result_tmp}")
        return instructions

    # ------------------------------------------------------------------
    # Numeric type conversions
    # ------------------------------------------------------------------

    def _translate_to_float(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate to_float(@Int) → @Float64.  WASM: f64.convert_i64_s."""
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        instructions.append("f64.convert_i64_s")
        return instructions

    def _translate_float_to_int(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate float_to_int(@Float64) → @Int.

        WASM: i64.trunc_f64_s (truncation toward zero).
        Traps on NaN/Infinity, consistent with floor/ceil/round.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        instructions.append("i64.trunc_f64_s")
        return instructions

    def _translate_nat_to_int(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate nat_to_int(@Nat) → @Int.  Identity (both i64)."""
        return self.translate_expr(arg, env)

    def _translate_int_to_nat(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate int_to_nat(@Int) → @Option<Nat> (i32 heap pointer).

        Option<Nat> layout (16 bytes, uniform for both variants):
          None:      [tag=0 : i32] [pad 12]
          Some(Nat): [tag=1 : i32] [pad 4] [value : i64]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True
        val = self.alloc_local("i64")
        out = self.alloc_local("i32")

        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append(f"local.set {val}")

        # Allocate 16 bytes (largest variant: Some(i64))
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.set {out}")

        # Check: val >= 0?
        ins.append(f"local.get {val}")
        ins.append("i64.const 0")
        ins.append("i64.ge_s")
        ins.append("if")
        # -- Some path: tag=1, value at offset 8
        ins.append(f"  local.get {out}")
        ins.append("  i32.const 1")
        ins.append("  i32.store")           # tag = 1 (Some)
        ins.extend(f"  {x}" for x in gc_shadow_push(out))
        ins.append(f"  local.get {out}")
        ins.append(f"  local.get {val}")
        ins.append("  i64.store offset=8")  # Nat value
        ins.append("else")
        # -- None path: tag=0
        ins.append(f"  local.get {out}")
        ins.append("  i32.const 0")
        ins.append("  i32.store")           # tag = 0 (None)
        ins.extend(f"  {x}" for x in gc_shadow_push(out))
        ins.append("end")

        ins.append(f"local.get {out}")
        return ins

    def _translate_byte_to_int(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate byte_to_int(@Byte) → @Int.  WASM: i64.extend_i32_u."""
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        instructions.append("i64.extend_i32_u")
        return instructions

    def _translate_int_to_byte(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate int_to_byte(@Int) → @Option<Byte> (i32 heap pointer).

        Option<Byte> layout (8 bytes, uniform for both variants):
          None:       [tag=0 : i32] [pad 4]
          Some(Byte): [tag=1 : i32] [value : i32]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True
        val = self.alloc_local("i64")
        out = self.alloc_local("i32")

        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append(f"local.set {val}")

        # Allocate 8 bytes (both variants fit in 8)
        ins.append("i32.const 8")
        ins.append("call $alloc")
        ins.append(f"local.set {out}")

        # Check: 0 <= val <= 255
        ins.append(f"local.get {val}")
        ins.append("i64.const 0")
        ins.append("i64.ge_s")
        ins.append(f"local.get {val}")
        ins.append("i64.const 255")
        ins.append("i64.le_s")
        ins.append("i32.and")
        ins.append("if")
        # -- Some path: tag=1, i32.wrap_i64(val) at offset 4
        ins.append(f"  local.get {out}")
        ins.append("  i32.const 1")
        ins.append("  i32.store")            # tag = 1 (Some)
        ins.extend(f"  {x}" for x in gc_shadow_push(out))
        ins.append(f"  local.get {out}")
        ins.append(f"  local.get {val}")
        ins.append("  i32.wrap_i64")
        ins.append("  i32.store offset=4")   # Byte value
        ins.append("else")
        # -- None path: tag=0
        ins.append(f"  local.get {out}")
        ins.append("  i32.const 0")
        ins.append("  i32.store")            # tag = 0 (None)
        ins.extend(f"  {x}" for x in gc_shadow_push(out))
        ins.append("end")

        ins.append(f"local.get {out}")
        return ins

    # -- Float64 predicates and constants ----------------------------

    def _translate_is_nan(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate is_nan(@Float64) → @Bool.

        WASM: NaN is the only float value not equal to itself.
        ``f64.ne(x, x)`` returns i32(1) for NaN, i32(0) otherwise.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        tmp = self.alloc_local("f64")
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        instructions.append(f"local.tee {tmp}")
        instructions.append(f"local.get {tmp}")
        instructions.append("f64.ne")
        return instructions

    def _translate_is_infinite(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate is_infinite(@Float64) → @Bool.

        WASM: ``f64.abs(x) == inf`` returns i32(1) for ±∞, i32(0) otherwise.
        This correctly returns false for NaN since NaN comparisons are false.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        instructions.append("f64.abs")
        instructions.append("f64.const inf")
        instructions.append("f64.eq")
        return instructions

    def _translate_nan(self) -> list[str]:
        """Translate nan() → @Float64.

        WASM: ``f64.const nan`` pushes a quiet NaN onto the stack.
        """
        return ["f64.const nan"]

    def _translate_infinity(self) -> list[str]:
        """Translate infinity() → @Float64.

        WASM: ``f64.const inf`` pushes positive infinity onto the stack.
        """
        return ["f64.const inf"]

    # -----------------------------------------------------------------
    # Decimal built-in operations (§9.7.2)
    # -----------------------------------------------------------------

    def _register_decimal_import(
        self, op: str, params: list[str], results: list[str],
    ) -> str:
        """Register a Decimal host import and return the WASM call name."""
        wasm_name = f"$vera.{op}"
        param_str = " ".join(f"(param {p})" for p in params)
        result_str = " ".join(f"(result {r})" for r in results)
        sig = f"(func {wasm_name} {param_str} {result_str})"
        self._decimal_imports.add(f'  (import "vera" "{op}" {sig})')
        self._decimal_ops_used.add(op)
        return wasm_name

    def _translate_decimal_unary(
        self, call: "ast.FnCall", env: WasmSlotEnv,
        op: str, param_type: str, result_type: str,
    ) -> list[str] | None:
        """Translate a unary Decimal operation (one param, one result)."""
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            op, [param_type], [result_type])
        return arg_instrs + [f"call {wasm_name}"]

    def _translate_decimal_binary(
        self, call: "ast.FnCall", env: WasmSlotEnv,
        op: str,
    ) -> list[str] | None:
        """Translate a binary Decimal operation (two handles → handle)."""
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            op, ["i32", "i32"], ["i32"])
        return a_instrs + b_instrs + [f"call {wasm_name}"]

    def _translate_decimal_from_string(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_from_string(s) → Option<Decimal> (i32 heap ptr)."""
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_from_string", ["i32", "i32"], ["i32"])
        self.needs_alloc = True
        return arg_instrs + [f"call {wasm_name}"]

    def _translate_decimal_to_string(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_to_string(d) → String (i32_pair)."""
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_to_string", ["i32"], ["i32", "i32"])
        self.needs_alloc = True
        return arg_instrs + [f"call {wasm_name}"]

    def _translate_decimal_div(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_div(a, b) → Option<Decimal> (i32 heap ptr)."""
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_div", ["i32", "i32"], ["i32"])
        self.needs_alloc = True
        return a_instrs + b_instrs + [f"call {wasm_name}"]

    def _translate_decimal_compare(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_compare(a, b) → Ordering (i32 heap ptr)."""
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_compare", ["i32", "i32"], ["i32"])
        self.needs_alloc = True
        return a_instrs + b_instrs + [f"call {wasm_name}"]

    def _translate_decimal_eq(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_eq(a, b) → Bool (i32)."""
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_eq", ["i32", "i32"], ["i32"])
        return a_instrs + b_instrs + [f"call {wasm_name}"]

    def _translate_decimal_round(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_round(d, places) → Decimal handle (i32)."""
        d_instrs = self.translate_expr(call.args[0], env)
        p_instrs = self.translate_expr(call.args[1], env)
        if d_instrs is None or p_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_round", ["i32", "i64"], ["i32"])
        return d_instrs + p_instrs + [f"call {wasm_name}"]

    # -----------------------------------------------------------------
    # Ability operation dispatch: show and hash (§9.8)
    # -----------------------------------------------------------------

    # Dispatch map: Vera type → to_string builtin name
    _SHOW_DISPATCH: dict[str, str] = {
        "Int": "to_string",
        "Nat": "nat_to_string",
        "Bool": "bool_to_string",
        "Byte": "byte_to_string",
        "Float64": "float_to_string",
    }

    def _translate_show(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate show(x) to the appropriate to_string builtin.

        Dispatches based on the inferred Vera type of the argument:
        - Int/Nat/Bool/Byte/Float64 → corresponding to_string call
        - String → identity (the string IS its own representation)
        - Unit → literal "unit"
        """
        vera_type = self._infer_vera_type(arg)
        if vera_type is None:
            return None

        # String → identity: show("hello") == "hello"
        if vera_type == "String":
            return self.translate_expr(arg, env)

        # Unit → literal "unit" string
        if vera_type == "Unit":
            offset, length = self.string_pool.intern("unit")
            return [f"i32.const {offset}", f"i32.const {length}"]

        # Decimal → decimal_to_string host import
        if vera_type == "Decimal":
            desugared = ast.FnCall(
                name="decimal_to_string", args=(arg,), span=arg.span,
            )
            return self._translate_call(desugared, env)

        # Dispatch to existing to_string builtins
        builtin = self._SHOW_DISPATCH.get(vera_type)
        if builtin is not None:
            # Reuse existing translate methods by constructing a FnCall
            desugared = ast.FnCall(
                name=builtin, args=(arg,), span=arg.span,
            )
            return self._translate_call(desugared, env)

        return None

    # ── Map<K, V> host-import builtins ──────────────────────────────

    @staticmethod
    def _map_wasm_tag(vera_type: str | None) -> str:
        """Map a Vera type name to a single-char WASM type tag.

        Used to build monomorphized host import names like
        ``map_insert$ki_vi`` (key=i64, value=i64).
        """
        if vera_type in ("Int", "Nat"):
            return "i"   # i64
        if vera_type == "Float64":
            return "f"   # f64
        if vera_type == "String":
            return "s"   # i32_pair
        # Bool, Byte, ADTs, Map handles → i32
        return "b"

    @staticmethod
    def _map_wasm_types(tag: str) -> list[str]:
        """Return WAT param types for a type tag."""
        if tag == "i":
            return ["i64"]
        if tag == "f":
            return ["f64"]
        if tag == "s":
            return ["i32", "i32"]
        return ["i32"]

    def _map_import_name(self, op: str, key_tag: str | None = None,
                         val_tag: str | None = None) -> str:
        """Build a mangled Map host import name and register it."""
        if key_tag is not None and val_tag is not None:
            suffix = f"$k{key_tag}_v{val_tag}"
        elif key_tag is not None:
            suffix = f"$k{key_tag}"
        elif val_tag is not None:
            suffix = f"$v{val_tag}"
        else:
            suffix = ""
        name = f"{op}{suffix}"
        self._map_ops_used.add(name)
        return name

    def _register_map_import(
        self, op: str, key_tag: str | None = None,
        val_tag: str | None = None,
        extra_params: list[str] | None = None,
        results: list[str] | None = None,
    ) -> str:
        """Register a Map host import and return the WASM call name."""
        name = self._map_import_name(op, key_tag, val_tag)
        wasm_name = f"$vera.{name}"
        params: list[str] = []
        if extra_params:
            params.extend(extra_params)
        param_str = " ".join(f"(param {p})" for p in params)
        result_str = ""
        if results:
            result_str = " ".join(f"(result {r})" for r in results)
        sig = f"(func {wasm_name} {param_str} {result_str})".rstrip()
        import_line = f'  (import "vera" "{name}" {sig})'
        self._map_imports.add(import_line)
        return wasm_name

    def _infer_map_key_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Map's key from the call arguments."""
        # For map_insert(m, k, v): key is arg[1]
        # For map_get/contains/remove(m, k): key is arg[1]
        # For map_new(): no key arg, infer from type context
        if call.name == "map_new":
            return None
        if len(call.args) >= 2:
            return self._infer_vera_type(call.args[1])
        return None

    def _infer_map_val_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Map's value from the call arguments."""
        # For map_insert(m, k, v): value is arg[2]
        if call.name == "map_insert" and len(call.args) >= 3:
            return self._infer_vera_type(call.args[2])
        return None

    def _translate_map_new(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_new() → i32 handle via host import.

        Since map_new has no arguments, we use a single unparameterised
        host import that returns a fresh empty map handle.
        """
        wasm_name = "$vera.map_new"
        sig = "(func $vera.map_new (result i32))"
        self._map_imports.add(f'  (import "vera" "map_new" {sig})')
        self._map_ops_used.add("map_new")
        return [f"call {wasm_name}"]

    def _translate_map_insert(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_insert(m, k, v) → i32 (new handle) via host import.

        Emits a type-specific host import based on the key and value types.
        """
        key_type = self._infer_vera_type(call.args[1])
        val_type = self._infer_vera_type(call.args[2])
        kt = self._map_wasm_tag(key_type)
        vt = self._map_wasm_tag(val_type)

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        params.extend(self._map_wasm_types(vt))  # value
        wasm_name = self._register_map_import(
            "map_insert", kt, vt,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_get(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_get(m, k) → i32 (Option<V> heap pointer) via host import.

        The host reads the value from its internal dict, constructs an
        Option ADT (Some/None) in WASM memory, and returns the pointer.
        """
        key_type = self._infer_vera_type(call.args[1])
        kt = self._map_wasm_tag(key_type)
        # We need the value tag too, so the host knows how to build Option<V>.
        # Infer from the map's type — look at the slot ref for arg[0].
        val_type = self._infer_map_value_from_map_arg(call.args[0])
        vt = self._map_wasm_tag(val_type)

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        wasm_name = self._register_map_import(
            "map_get", kt, vt,
            extra_params=params, results=["i32"],
        )
        self.needs_alloc = True
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _infer_map_value_from_map_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the value type V from a Map<K, V> expression."""
        # If the map arg is a slot ref like @Map<String, Int>.0,
        # extract V from the type_args (not the type_name string).
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Map" and expr.type_args:
                if len(expr.type_args) == 2:
                    val_te = expr.type_args[1]
                    if isinstance(val_te, ast.NamedType):
                        return val_te.name
            # Fallback: parse from composite type_name string
            # Uses depth-aware split to handle nested generics
            # like Map<Result<Int, Bool>, String>
            name = expr.type_name
            if name.startswith("Map<") and name.endswith(">"):
                v = self._split_map_type_args(name)
                if v is not None:
                    return v[1]
        # If it's a function call that returns Map, try to infer
        if isinstance(expr, ast.FnCall):
            if expr.name in ("map_new", "map_insert", "map_remove"):
                if expr.name == "map_insert" and len(expr.args) >= 3:
                    return self._infer_vera_type(expr.args[2])
                # Recurse into the map argument
                if expr.args:
                    return self._infer_map_value_from_map_arg(expr.args[0])
        return None

    def _translate_map_contains(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_contains(m, k) → i32 (Bool) via host import."""
        key_type = self._infer_vera_type(call.args[1])
        kt = self._map_wasm_tag(key_type)

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        wasm_name = self._register_map_import(
            "map_contains", kt, None,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_remove(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_remove(m, k) → i32 (new handle) via host import."""
        key_type = self._infer_vera_type(call.args[1])
        kt = self._map_wasm_tag(key_type)

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        wasm_name = self._register_map_import(
            "map_remove", kt, None,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_size(
        self, arg: "ast.Expr", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_size(m) → i64 (Int) via host import."""
        wasm_name = "$vera.map_size"
        sig = "(func $vera.map_size (param i32) (result i64))"
        self._map_imports.add(f'  (import "vera" "map_size" {sig})')
        self._map_ops_used.add("map_size")
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_keys(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_keys(m) → (i32, i32) Array<K> via host import."""
        # Infer key type from the map argument
        key_type = self._infer_map_key_from_map_arg(call.args[0])
        kt = self._map_wasm_tag(key_type)

        wasm_name = self._register_map_import(
            "map_keys", kt, None,
            extra_params=["i32"], results=["i32", "i32"],
        )
        self.needs_alloc = True
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_values(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_values(m) → (i32, i32) Array<V> via host import."""
        val_type = self._infer_map_value_from_map_arg(call.args[0])
        vt = self._map_wasm_tag(val_type)

        wasm_name = self._register_map_import(
            "map_values", val_tag=vt,
            extra_params=["i32"], results=["i32", "i32"],
        )
        self.needs_alloc = True
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    @staticmethod
    def _split_map_type_args(name: str) -> tuple[str, str] | None:
        """Split 'Map<K, V>' into (K, V) with nesting-aware comma split.

        Handles nested generics like Map<Result<Int, Bool>, String>
        by tracking angle-bracket depth.
        """
        inner = name[4:-1]  # strip "Map<" and ">"
        depth = 0
        for i, ch in enumerate(inner):
            if ch == "<":
                depth += 1
            elif ch == ">":
                depth -= 1
            elif ch == "," and depth == 0:
                k = inner[:i].strip()
                v = inner[i + 1:].strip()
                if k and v:
                    return (k, v)
        return None

    def _infer_map_key_from_map_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the key type K from a Map<K, V> expression."""
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Map" and expr.type_args:
                if len(expr.type_args) >= 1:
                    key_te = expr.type_args[0]
                    if isinstance(key_te, ast.NamedType):
                        return key_te.name
            name = expr.type_name
            if name.startswith("Map<") and name.endswith(">"):
                v = self._split_map_type_args(name)
                if v is not None:
                    return v[0]
        if isinstance(expr, ast.FnCall):
            if expr.name == "map_insert" and len(expr.args) >= 2:
                return self._infer_vera_type(expr.args[1])
            if expr.args:
                return self._infer_map_key_from_map_arg(expr.args[0])
        return None

    # ── Set<T> host-import builtins ──────────────────────────────

    def _set_import_name(self, op: str, elem_tag: str | None = None) -> str:
        """Build a mangled Set host import name."""
        suffix = f"$e{elem_tag}" if elem_tag is not None else ""
        name = f"{op}{suffix}"
        self._set_ops_used.add(name)
        return name

    def _register_set_import(
        self, op: str, elem_tag: str | None = None,
        extra_params: list[str] | None = None,
        results: list[str] | None = None,
    ) -> str:
        """Register a Set host import and return the WASM call name."""
        name = self._set_import_name(op, elem_tag)
        wasm_name = f"$vera.{name}"
        params: list[str] = []
        if extra_params:
            params.extend(extra_params)
        param_str = " ".join(f"(param {p})" for p in params)
        result_str = ""
        if results:
            result_str = " ".join(f"(result {r})" for r in results)
        sig = f"(func {wasm_name} {param_str} {result_str})".rstrip()
        import_line = f'  (import "vera" "{name}" {sig})'
        self._set_imports.add(import_line)
        return wasm_name

    def _infer_set_elem_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Set's element from call arguments."""
        if call.name == "set_new":
            return None
        if len(call.args) >= 2:
            return self._infer_vera_type(call.args[1])
        return None

    def _infer_set_elem_from_set_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the element type T from a Set<T> expression."""
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Set" and expr.type_args:
                if len(expr.type_args) >= 1:
                    elem_te = expr.type_args[0]
                    if isinstance(elem_te, ast.NamedType):
                        return elem_te.name
            name = expr.type_name
            if name.startswith("Set<") and name.endswith(">"):
                return name[4:-1]
        if isinstance(expr, ast.FnCall):
            if expr.name == "set_add" and len(expr.args) >= 2:
                return self._infer_vera_type(expr.args[1])
            # Only recurse into set-returning functions
            if expr.name in ("set_new", "set_add", "set_remove"):
                if expr.args:
                    return self._infer_set_elem_from_set_arg(expr.args[0])
        return None

    def _translate_set_new(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_new() → i32 handle via host import."""
        wasm_name = "$vera.set_new"
        sig = "(func $vera.set_new (result i32))"
        self._set_imports.add(f'  (import "vera" "set_new" {sig})')
        self._set_ops_used.add("set_new")
        return [f"call {wasm_name}"]

    def _translate_set_add(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_add(s, elem) → i32 (new handle) via host import."""
        elem_type = self._infer_vera_type(call.args[1])
        et = self._map_wasm_tag(elem_type)

        params = ["i32"]  # set handle
        params.extend(self._map_wasm_types(et))  # element
        wasm_name = self._register_set_import(
            "set_add", et,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_contains(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_contains(s, elem) → i32 (Bool) via host import."""
        elem_type = self._infer_vera_type(call.args[1])
        et = self._map_wasm_tag(elem_type)

        params = ["i32"]  # set handle
        params.extend(self._map_wasm_types(et))  # element
        wasm_name = self._register_set_import(
            "set_contains", et,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_remove(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_remove(s, elem) → i32 (new handle) via host import."""
        elem_type = self._infer_vera_type(call.args[1])
        et = self._map_wasm_tag(elem_type)

        params = ["i32"]  # set handle
        params.extend(self._map_wasm_types(et))  # element
        wasm_name = self._register_set_import(
            "set_remove", et,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_size(
        self, arg: "ast.Expr", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_size(s) → i64 (Int) via host import."""
        wasm_name = "$vera.set_size"
        sig = "(func $vera.set_size (param i32) (result i64))"
        self._set_imports.add(f'  (import "vera" "set_size" {sig})')
        self._set_ops_used.add("set_size")
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_to_array(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_to_array(s) → (i32, i32) Array<T> via host import."""
        elem_type = self._infer_set_elem_from_set_arg(call.args[0])
        et = self._map_wasm_tag(elem_type)

        wasm_name = self._register_set_import(
            "set_to_array", et,
            extra_params=["i32"], results=["i32", "i32"],
        )
        self.needs_alloc = True
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_hash(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate hash(x) to a type-specific hash implementation.

        Returns an i64 hash value:
        - Int/Nat → identity (the value IS the hash)
        - Bool/Byte → i64.extend_i32_u (widen to i64)
        - Float64 → i64.reinterpret_f64 (bit pattern)
        - Unit → i64.const 0
        - String → FNV-1a hash
        """
        vera_type = self._infer_vera_type(arg)
        if vera_type is None:
            return None

        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        # Int/Nat → identity: hash(42) == 42
        if vera_type in ("Int", "Nat"):
            return arg_instrs

        # Bool/Byte → extend to i64
        if vera_type in ("Bool", "Byte"):
            return arg_instrs + ["i64.extend_i32_u"]

        # Float64 → bit-level reinterpretation
        if vera_type == "Float64":
            return arg_instrs + ["i64.reinterpret_f64"]

        # Unit → constant 0
        if vera_type == "Unit":
            return ["i64.const 0"]

        # String → FNV-1a hash
        if vera_type == "String":
            return self._translate_hash_string(arg_instrs)

        return None

    def _translate_hash_string(
        self, arg_instrs: list[str],
    ) -> list[str]:
        """Generate FNV-1a hash for a string (ptr, len) pair.

        FNV-1a: for each byte, hash = (hash XOR byte) * FNV_prime.
        Uses the 64-bit FNV-1a variant:
        - offset basis: 14695981039346656037
        - prime: 1099511628211
        """
        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        hash_val = self.alloc_local("i64")

        # FNV-1a offset basis (as signed i64)
        fnv_basis = -3750763034362895579  # 14695981039346656037 as signed
        fnv_prime = 1099511628211

        instructions: list[str] = []
        # Evaluate arg → (ptr, len) on stack
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {slen}")
        instructions.append(f"local.set {ptr}")

        # Initialize hash to FNV offset basis
        instructions.append(f"i64.const {fnv_basis}")
        instructions.append(f"local.set {hash_val}")

        # idx = 0
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")

        # Loop over each byte
        instructions.append("block $hbreak")
        instructions.append("  loop $hloop")
        # if idx >= len → break
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {slen}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $hbreak")
        # byte = mem[ptr + idx]
        instructions.append(f"    local.get {ptr}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u")
        instructions.append("    i64.extend_i32_u")
        # hash = hash XOR byte
        instructions.append(f"    local.get {hash_val}")
        instructions.append("    i64.xor")
        # hash = hash * FNV_prime
        instructions.append(f"    i64.const {fnv_prime}")
        instructions.append("    i64.mul")
        instructions.append(f"    local.set {hash_val}")
        # idx++
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $hloop")
        instructions.append("  end")
        instructions.append("end")

        # Push result
        instructions.append(f"local.get {hash_val}")
        return instructions

    def _translate_handle_expr(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate a handle expression to WASM.

        Supports State<T> handlers via host imports and Exn<E>
        handlers via WASM exception handling (try_table/catch/throw).
        Other handler types cause the function to be skipped.
        """
        effect = expr.effect
        if not isinstance(effect, ast.EffectRef):
            return None

        if effect.name == "State" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_state(expr, env)

        if effect.name == "Exn" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_exn(expr, env)

        # Unsupported handler type
        return None

    def _translate_handle_state(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate handle[State<T>](@T = init) { ... } in { body }.

        Compiles by:
        1. Evaluating init_expr and calling state_put_T to set initial state
        2. Temporarily injecting get/put effect ops for the body
        3. Compiling the body with these ops active
        4. Restoring the previous effect ops
        """
        assert isinstance(expr.effect, ast.EffectRef)  # noqa: S101
        type_arg = expr.effect.type_args[0]  # type: ignore[index]
        if isinstance(type_arg, ast.NamedType):
            type_name = type_arg.name
        else:
            return None

        wasm_type = self._type_name_to_wasm(type_name)
        put_import = f"$vera.state_put_{type_name}"
        get_import = f"$vera.state_get_{type_name}"

        instructions: list[str] = []

        # 1. Initialize state: compile init_expr, call state_put
        if expr.state is not None:
            init_instrs = self.translate_expr(expr.state.init_expr, env)
            if init_instrs is None:
                return None
            instructions.extend(init_instrs)
            instructions.append(f"call {put_import}")
        # If no state clause, state starts at default (0)

        # 2. Save current effect_ops and inject handler ops
        saved_ops = dict(self._effect_ops)
        self._effect_ops["get"] = (get_import, False)
        self._effect_ops["put"] = (put_import, True)

        # 3. Compile handler body
        body_instrs = self.translate_block(expr.body, env)

        # 4. Restore effect_ops
        self._effect_ops = saved_ops

        if body_instrs is None:
            return None

        instructions.extend(body_instrs)
        return instructions

    def _translate_handle_exn(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate handle[Exn<E>] { throw(@E) -> handler } in { body }.

        Uses WASM exception handling (try_table/catch/throw):
          block $done (result T)
            block $catch (result E)
              try_table (result T) (catch $exn_E $catch)
                <body>
              end
              br $done
            end
            ;; caught value on stack
            local.set $thrown
            <handler clause body>
          end
        """
        assert isinstance(expr.effect, ast.EffectRef)  # noqa: S101
        type_arg = expr.effect.type_args[0]  # type: ignore[index]
        if not isinstance(type_arg, ast.NamedType):
            return None
        type_name = type_arg.name
        tag_name = f"$exn_{type_name}"
        is_pair = self._is_pair_type_name(type_name)

        # Unique label ids for nested handlers
        hid = self._next_handle_id
        self._next_handle_id += 1
        done_label = f"$hd_{hid}"
        catch_label = f"$hc_{hid}"

        # Infer result type: try handler clause first (body may always
        # throw, making its inferred type None), then fall back to body.
        result_wt = None
        if expr.clauses:
            clause_body = expr.clauses[0].body
            if isinstance(clause_body, ast.Block):
                result_wt = self._infer_block_result_type(clause_body)
        if result_wt is None:
            result_wt = self._infer_block_result_type(expr.body)

        # Save/inject throw as an effect op for the body
        saved_ops = dict(self._effect_ops)
        self._effect_ops["throw"] = (tag_name, False)

        # Compile body
        body_instrs = self.translate_block(expr.body, env)

        # Restore effect_ops
        self._effect_ops = saved_ops

        if body_instrs is None:
            return None

        # Compile handler clause body
        if not expr.clauses:
            return None
        clause = expr.clauses[0]  # Exn<E> has exactly one op: throw

        # Allocate locals for the caught exception value.
        # Pair types (String, Array<T>) use two consecutive i32 locals
        # (ptr at thrown_local, len at thrown_local + 1) matching the
        # convention used by _translate_slot_ref for pair types.
        if is_pair:
            thrown_local = self.alloc_local("i32")  # ptr
            _len_local = self.alloc_local("i32")    # len (consecutive: thrown_local + 1)
        else:
            thrown_wt = self._type_name_to_wasm(type_name)
            thrown_local = self.alloc_local(thrown_wt)

        # Push caught value into slot env for handler body
        handler_env = env.push(type_name, thrown_local)
        handler_instrs = self.translate_expr(clause.body, handler_env)
        if handler_instrs is None:
            return None  # pragma: no cover

        # Assemble the try_table structure.
        # i32_pair (String, Array<T>) must expand to "i32 i32" in WAT result
        # annotations; "i32_pair" is an internal representation, not valid WAT.
        if result_wt == "i32_pair":
            result_spec = " (result i32 i32)"
        elif result_wt:
            result_spec = f" (result {result_wt})"
        else:
            result_spec = ""  # pragma: no cover
        if is_pair:
            thrown_spec = " (result i32 i32)"
        else:
            thrown_spec = f" (result {thrown_wt})" if thrown_wt else ""

        instructions: list[str] = []
        instructions.append(f"block {done_label}{result_spec}")
        instructions.append(f"  block {catch_label}{thrown_spec}")
        instructions.append(
            f"    try_table{result_spec}"
            f" (catch {tag_name} {catch_label})"
        )
        instructions.extend(f"      {i}" for i in body_instrs)
        instructions.append("    end")
        instructions.append(f"    br {done_label}")
        instructions.append("  end")
        # Caught value(s) are on the stack — store into local(s).
        # Pair types: catch pushes (ptr, len); set len first (LIFO), then ptr.
        if is_pair:
            instructions.append(f"  local.set {_len_local}")
            instructions.append(f"  local.set {thrown_local}")
        else:
            instructions.append(f"  local.set {thrown_local}")
        instructions.extend(f"  {i}" for i in handler_instrs)
        instructions.append("end")

        return instructions
