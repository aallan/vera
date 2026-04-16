"""Function call and effect handler translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class CallsMixin:
    """Core dispatch mixin for WasmContext.

    Houses the primary ``_translate_call`` and ``_translate_qualified_call``
    dispatchers, generic-call resolution helpers, and the shared
    ``_infer_concat_elem_type`` utility (used by both arrays and strings
    for element-type inference).

    Individual built-in families live in sibling mixins:

    - ``CallsArraysMixin``      (calls_arrays.py)
    - ``CallsContainersMixin``  (calls_containers.py) — Map/Set/Decimal
    - ``CallsEncodingMixin``    (calls_encoding.py)   — Base64/URL
    - ``CallsHandlersMixin``    (calls_handlers.py)   — Show/Hash/handle
    - ``CallsMarkupMixin``      (calls_markup.py)     — JSON/HTML/Md/Regex
    - ``CallsMathMixin``        (calls_math.py)
    - ``CallsParsingMixin``     (calls_parsing.py)
    - ``CallsStringsMixin``     (calls_strings.py)
    """

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
