"""Function call and effect handler translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.monomorphize import Monomorphizer, resolve_fn_type_alias
from vera.skip import CodegenSkip
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
            # String utilities (#470)
            if call.name == "string_chars" and len(call.args) == 1:
                return self._translate_string_chars(call.args[0], env)
            if call.name == "string_lines" and len(call.args) == 1:
                return self._translate_string_lines(call.args[0], env)
            if call.name == "string_words" and len(call.args) == 1:
                return self._translate_string_words(call.args[0], env)
            if call.name == "string_pad_start" and len(call.args) == 3:
                return self._translate_string_pad_start(
                    call.args[0], call.args[1], call.args[2], env,
                )
            if call.name == "string_pad_end" and len(call.args) == 3:
                return self._translate_string_pad_end(
                    call.args[0], call.args[1], call.args[2], env,
                )
            if call.name == "string_reverse" and len(call.args) == 1:
                return self._translate_string_reverse(call.args[0], env)
            if call.name == "string_trim_start" and len(call.args) == 1:
                return self._translate_string_trim_start(call.args[0], env)
            if call.name == "string_trim_end" and len(call.args) == 1:
                return self._translate_string_trim_end(call.args[0], env)
            # Character classification + case conversion (#471)
            if call.name == "is_digit" and len(call.args) == 1:
                return self._translate_is_digit(call.args[0], env)
            if call.name == "is_alpha" and len(call.args) == 1:
                return self._translate_is_alpha(call.args[0], env)
            if call.name == "is_alphanumeric" and len(call.args) == 1:
                return self._translate_is_alphanumeric(call.args[0], env)
            if call.name == "is_whitespace" and len(call.args) == 1:
                return self._translate_is_whitespace(call.args[0], env)
            if call.name == "is_upper" and len(call.args) == 1:
                return self._translate_is_upper(call.args[0], env)
            if call.name == "is_lower" and len(call.args) == 1:
                return self._translate_is_lower(call.args[0], env)
            if call.name == "char_to_upper" and len(call.args) == 1:
                return self._translate_char_to_upper(call.args[0], env)
            if call.name == "char_to_lower" and len(call.args) == 1:
                return self._translate_char_to_lower(call.args[0], env)
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
            # Higher-order array combinators — iterative WASM (#480).
            # array_map / array_filter / array_fold were previously
            # injected as recursive Vera functions via prelude.py.
            # Intercepted here instead so the loop uses O(1) shadow
            # stack space regardless of input length.
            if call.name == "array_map" and len(call.args) == 2:
                return self._translate_array_map(
                    call.args[0], call.args[1], env,
                )
            if call.name == "array_filter" and len(call.args) == 2:
                return self._translate_array_filter(
                    call.args[0], call.args[1], env,
                )
            if call.name == "array_fold" and len(call.args) == 3:
                return self._translate_array_fold(
                    call.args[0], call.args[1], call.args[2], env,
                )
            # Array utilities (#466 phase 1) — iterative, no ability
            # dispatch required.  Sort/contains/index_of are tracked
            # separately as they need compare$T/eq$T invocation
            # reified as a primitive.
            if call.name == "array_mapi" and len(call.args) == 2:
                return self._translate_array_mapi(
                    call.args[0], call.args[1], env,
                )
            if call.name == "array_reverse" and len(call.args) == 1:
                return self._translate_array_reverse(call.args[0], env)
            if call.name == "array_find" and len(call.args) == 2:
                return self._translate_array_find(
                    call.args[0], call.args[1], env,
                )
            if call.name == "array_any" and len(call.args) == 2:
                return self._translate_array_any(
                    call.args[0], call.args[1], env,
                )
            if call.name == "array_all" and len(call.args) == 2:
                return self._translate_array_all(
                    call.args[0], call.args[1], env,
                )
            if call.name == "array_flatten" and len(call.args) == 1:
                return self._translate_array_flatten(call.args[0], env)
            if call.name == "array_sort_by" and len(call.args) == 2:
                return self._translate_array_sort_by(
                    call.args[0], call.args[1], env,
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
            # Math builtins (#467) — log/trig via host imports,
            # constants and sign/clamp inlined as WAT.
            if call.name in (
                "log", "log2", "log10",
                "sin", "cos", "tan", "asin", "acos", "atan",
            ) and len(call.args) == 1:
                return self._translate_math_unary_host(
                    call.name, call.args[0], env,
                )
            if call.name == "atan2" and len(call.args) == 2:
                return self._translate_atan2(
                    call.args[0], call.args[1], env,
                )
            if call.name == "pi" and len(call.args) == 0:
                return self._translate_pi()
            if call.name == "e" and len(call.args) == 0:
                return self._translate_e()
            if call.name == "sign" and len(call.args) == 1:
                return self._translate_sign(call.args[0], env)
            if call.name == "clamp" and len(call.args) == 3:
                return self._translate_clamp(
                    call.args[0], call.args[1], call.args[2], env,
                )
            if call.name == "float_clamp" and len(call.args) == 3:
                return self._translate_float_clamp(
                    call.args[0], call.args[1], call.args[2], env,
                )
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

        # #976 option C: a get/put under a handle with registered clauses
        # inlines the clause body at the call site (intrinsic-hybrid
        # semantics) instead of the bare host-cell call below.
        if call.name in self._state_clause_ops:
            return self._translate_state_clause_op(call, env)
        # Inside an inlined State clause, resume(v)'s value IS the op's
        # result at the original call site (single-shot, tail position —
        # enforced before inlining).  resume(()) is a UnitLit: no value,
        # matching put's void result.
        if call.name == "resume" and self._in_state_clause:
            return self.translate_expr(call.args[0], env)

        # Check if this is an effect operation (e.g. get/put/throw)
        if call.name in self._effect_ops:
            target_name, _is_void = self._effect_ops[call.name]
            instructions: list[str] = []
            # #747: the effect-op-argument @Int -> @Nat narrowing is the one
            # runtime-guard site left unguarded here — `_effect_ops` carries
            # only the dispatch target, not the op's formal types, so a
            # concrete-@Nat-formal check would need a new op-parameter
            # registry across the handler-dispatch path.  It is the rarest
            # site, already obligated statically by the verifier and flagged
            # E504 when Tier-3; the runtime guard is tracked as a follow-up.
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

        # #814 C2: inside an emitted ``mod$…`` body, redirect a bare call to a
        # locally-shadowed same-module sibling to the module's ``mod$``
        # version (the rename map is empty for every non-mod$ body, so normal
        # compilation is unaffected).  Shadowed siblings are non-generic, so
        # this never collides with the generic rewrite above.
        if call_target in self._intra_module_renames:
            call_target = self._intra_module_renames[call_target]

        if call_target in self._skipped_fns:
            raise CodegenSkip(
                call,
                f"call target {call_target!r} was skipped during code generation",
            )

        # Guard rail: reject calls to functions not defined in this module.
        # In practice the cross-module check upstream has already emitted
        # a diagnostic for genuine unknown-fn cases.  This path also fires
        # for prelude-mangled / forward-reference edge cases (e.g. the
        # #604 option_map mono-suffix mismatch) where the call target's
        # name was rewritten by mono but the rewritten name isn't yet
        # in `_known_fns`.
        if (self._known_fns
                and call_target not in self._known_fns
                and call_target not in self._ctor_layouts):
            raise CodegenSkip(
                call,
                f"call target {call_target!r} not registered in this module",
            )

        # Regular function call
        instructions = []
        # #747 (CR #756): key the @Nat-parameter guard bitmap on the *resolved*
        # ``call_target``, not ``call.name``.  Monomorphisation registers the
        # specialised instance (`pick$Nat`) with its concrete @Nat flags
        # ``(True, …)`` while the generic decl (`pick`) keeps the erased
        # ``(False, …)``; looking up ``call.name`` would miss the guard on the
        # actual callee.  So `f<Nat>(@Int.0)` runtime-guards the narrowing
        # exactly like a concrete `f(@Nat -> …)` call.
        nat_params = self._fn_nat_params.get(call_target, ())
        # #813: dual bitmap — concrete-@Int formals receiving a @Nat-typed
        # argument widen it; a @Nat above i64.MAX reinterprets to a negative
        # @Int, so the call site needs the runtime widening guard.  Disjoint
        # from `nat_params` (a formal resolves to one base or neither).
        int_params = self._fn_int_params.get(call_target, ())
        # #865: concrete-@Byte formals.  `@Byte` is i32 (spec §11), but an int
        # literal defaults to `i64.const`; a literal argument to a Byte formal
        # must lower at i32 so the pushed value matches the callee's parameter
        # width.  Mirrors the #766 binop-operand coercion at the call-arg
        # position.  Disjoint from `nat_params` / `int_params`.
        byte_params = self._fn_byte_params.get(call_target, ())
        for i, arg in enumerate(call.args):
            if (i < len(byte_params) and byte_params[i]
                    and isinstance(arg, ast.IntLit)):
                # The bidirectional checker (`_synth_expr(expected=Byte)`)
                # accepts a 0..255 int literal as a Byte argument (spec §11);
                # lower it as i32 rather than the default i64 to match the
                # callee's i32 Byte parameter.  Non-literal Byte arguments (a
                # Byte slot ref, a Byte-returning call) already yield i32 via
                # `translate_expr`, so only the literal needs the override.
                instructions.append(f"i32.const {arg.value}")
                continue
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            if (i < len(nat_params) and nat_params[i]
                    and self._narrows_into_nat(arg)):
                arg_instrs = self._emit_nat_bind_guard(arg_instrs)
            elif (i < len(int_params) and int_params[i]
                    and self._result_is_nat(arg)):
                arg_instrs = self._emit_int_widen_guard(arg_instrs)
            instructions.extend(arg_instrs)

        # #517 — emit ``return_call $target`` for tail-position
        # calls whose WASM signature matches the current function's.
        # The analyzer in ``vera/codegen/tail_position.py`` populates
        # ``self._tail_call_sites`` with ids of syntactically tail-
        # position FnCalls; the type-match guard ensures WASM
        # ``return_call`` semantics are valid (the callee must
        # return the same type the caller returns).  Falls back to
        # plain ``call`` if either condition fails — never an error,
        # just a missed optimization.  See the post-process at the
        # end of ``_compile_fn`` in ``vera/codegen/functions.py``:
        # for allocating functions (#549) it PREPENDS a ``$gc_sp``
        # restore before each ``return_call`` so the shadow stack
        # stays bounded; for functions with a runtime postcondition
        # it REVERTS ``return_call`` → ``call`` so the post-check
        # runs.
        is_tail = id(call) in self._tail_call_sites
        callee_ret_wt: str | None = None
        if is_tail:
            sig = self._fn_ret_types.get(call_target)
            callee_ret_wt = sig if isinstance(sig, str) else None
        if is_tail and callee_ret_wt == self._self_ret_wt:
            instructions.append(f"return_call ${call_target}")
        else:
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
        _host_import_qualifiers = {"Http", "Inference", "IO", "Random"}
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
        elif call.qualifier == "Random":
            # #465 — op names already begin with `random_`, so the
            # WASM import keeps the same name (`vera.random_int`,
            # `vera.random_float`, `vera.random_bool`).  None of the
            # Random ops allocate or return heap data, so $alloc is
            # not required.
            self._random_ops_used.add(call.name)
            instructions.append(f"call $vera.{call.name}")
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
        constrained_vars = self._generic_constrained_vars.get(
            call.name, frozenset())
        mapping: dict[str, str] = {}
        # #898: mirror the discovery-side sparse-multi-parameter merge
        # (Monomorphizer._infer_type_args_from_args) so the call-site mangled
        # name matches the clone Pass 1.5 emitted — else `main`'s call to
        # `eq2(MkErr(5), MkOk("x"))` references a `$Res` clone the emitter named
        # `$Res_LString_C_Int_R`, is dropped, and `main` vanishes (the #878 class).
        partial_adt: dict[str, tuple[str, list[str | None]]] = {}

        for param_te, arg in zip(param_types, call.args):
            self._unify_param_arg_wasm(
                param_te, arg, forall_vars, mapping, constrained_vars,
                partial_adt)

        for tv, (base_name, slots) in partial_adt.items():
            if all(s is not None for s in slots):
                resolved = [s for s in slots if s is not None]
                mapping[tv] = f"{base_name}<{', '.join(resolved)}>"
            elif tv in constrained_vars:
                # Partial recovery — mirror the discovery-side sentinel
                # materialisation (Monomorphizer._infer_type_args_from_args) so
                # the two stay in lockstep.  Such an instance is always rejected
                # by the ability gate and never emitted, but keeping the names
                # identical means the call-rewrite↔emitted-clone differential
                # never sees a phantom mismatch for the under-determined shape.
                from vera.monomorphize import _FREE_TYPE_PARAM
                rendered = [s if s is not None else _FREE_TYPE_PARAM
                            for s in slots]
                mapping[tv] = f"{base_name}<{', '.join(rendered)}>"

        # Build mangled name; default phantom vars to Bool (i32 repr — Unit
        # has no WASM representation), matching Monomorphizer's clone-side
        # default so the symbol is identical.
        # MUST produce the same symbol as clone emission, so delegate to
        # the shared injective mangler (#775) instead of duplicating the
        # encoding here — a drift means the call site references a symbol
        # Pass 1.5 never emitted.
        parts = []
        for tv in forall_vars:
            if tv not in mapping:
                mapping[tv] = "Bool"
            parts.append(mapping[tv])
        return Monomorphizer._mangle_fn_name(call.name, tuple(parts))

    def _unify_param_arg_wasm(
        self,
        param_te: ast.TypeExpr,
        arg: ast.Expr,
        forall_vars: tuple[str, ...],
        mapping: dict[str, str],
        constrained_vars: frozenset[str] = frozenset(),
        partial_adt: dict[str, tuple[str, list[str | None]]] | None = None,
    ) -> None:
        """Unify a parameter TypeExpr against an argument to bind type vars.

        Mirrors CodeGenerator._unify_param_arg for use during WASM
        translation.
        """
        if isinstance(param_te, ast.RefinementType):
            self._unify_param_arg_wasm(
                param_te.base_type, arg, forall_vars, mapping,
                constrained_vars, partial_adt,
            )
            return

        if not isinstance(param_te, ast.NamedType):
            return

        if param_te.name in forall_vars:
            vera_type = self._infer_vera_type(arg)
            if isinstance(arg, ast.FnCall):
                # #899 issue 2: for CLONE NAMING a user fn's declared return
                # type must be the RAW (un-alias-resolved) name discovery keys
                # the clone on (`-> @Age` → `pick$Age`, not the alias-resolved
                # `pick$Int` that general Vera-type inference returns).  Prefer
                # the raw declared name when available; else keep `_infer_vera_type`.
                raw = self._declared_return_clone_name(arg)
                if raw is not None:
                    vera_type = raw
            if (param_te.name in constrained_vars
                    and isinstance(arg, ast.ConstructorCall)):
                # Recover the type argument a `ConstructorCall` drops, so the
                # call-site mangled name matches the parameterized clone Pass 1.5
                # emitted for a constrained var (`eq2$Box<String>`, not the bare
                # `eq2$Box`).  Mirrors the discovery-side recovery in
                # `Monomorphizer._unify_param_arg` (#772).
                info = self._get_arg_type_info_wasm(arg)
                if info is not None:
                    base_name, arg_names = info
                    if arg_names and all(a is not None for a in arg_names):
                        resolved = [a for a in arg_names if a is not None]
                        vera_type = f"{base_name}<{', '.join(resolved)}>"
                    elif arg_names and partial_adt is not None:
                        # #898: PARTIAL recovery merged across arguments —
                        # mirrors Monomorphizer._unify_param_arg so the mangled
                        # call name matches the emitted clone.
                        prev = partial_adt.get(param_te.name)
                        if prev is None or prev[0] != base_name:
                            slots: list[str | None] = list(arg_names)
                            partial_adt[param_te.name] = (base_name, slots)
                        else:
                            slots = prev[1]
                            for i, name in enumerate(arg_names):
                                if name is not None and i < len(slots):
                                    slots[i] = name
            if vera_type and param_te.name not in mapping:
                mapping[param_te.name] = vera_type
            return

        # Parameterized type like Option<T>
        if param_te.type_args:
            # Handle type alias for FnType matched against a callable
            # arg (AnonFn literal or SlotRef typed as an FnType alias).
            # #604 parallel to the monomorphizer-side fix in
            # vera/codegen/monomorphize.py — see
            # MonomorphizationMixin._resolve_arg_fn_shape for the
            # full rationale.
            alias_concrete = self._infer_fn_alias_type_args_wasm(
                param_te, arg,
            )
            if alias_concrete is not None:
                for param_ta, concrete_name in zip(
                    param_te.type_args, alias_concrete,
                ):
                    # #769 gap 2: recursive — binds vars at any depth, via
                    # the SAME shared implementation discovery uses.
                    Monomorphizer._unify_type_arg_pair(
                        param_ta, concrete_name, forall_vars, mapping,
                    )
                return

            arg_info = self._get_arg_type_info_wasm(arg)
            if arg_info and arg_info[0] == param_te.name:
                for param_ta, arg_ta_name in zip(
                    param_te.type_args, arg_info[1]
                ):
                    # arg_ta_name is None for unknown ADT type-param positions
                    # (e.g. T in Err(e) where only E is inferred from Err's field).
                    # #769 gap 2: recursive — binds vars at any depth, via the
                    # SAME shared implementation discovery uses.
                    if arg_ta_name is not None:
                        Monomorphizer._unify_type_arg_pair(
                            param_ta, arg_ta_name, forall_vars, mapping,
                        )

    def _resolve_arg_fn_shape_wasm(
        self,
        arg: ast.Expr,
    ) -> tuple[tuple[ast.TypeExpr, ...], ast.TypeExpr] | None:
        """Return ``(param_types, return_type)`` for a callable arg.

        Mirrors :meth:`MonomorphizationMixin._resolve_arg_fn_shape` for
        WASM call-site rewriting.  Handles both ``AnonFn`` literals and
        ``SlotRef`` args whose static type is an FnType alias (#604) —
        resolved **transitively** through the alias chain with the
        SlotRef's type_args substituted per hop, via the shared
        :func:`vera.monomorphize.resolve_fn_type_alias` (#867 / PR #880
        review: the single-hop lookup here made a two-hop-alias-typed
        closure slot fail shape resolution, so a closure-bound type
        param fell to the phantom-var default — wrong mono suffix,
        ``call_indirect`` trap).  For parameterised aliases like
        ``type Mapper<T> = fn(T -> T)``, the substitution yields the
        instantiated shape (CR-5 on PR #659); without it,
        ``_resolve_generic_call`` would mangle the call to a name like
        ``$option_map$T_JT`` that doesn't match the mono-clone names
        Pass 1.5 registered.
        """
        if isinstance(arg, ast.AnonFn):
            return (tuple(arg.params), arg.return_type)
        if isinstance(arg, ast.SlotRef):
            fn_type = resolve_fn_type_alias(
                ast.NamedType(name=arg.type_name, type_args=arg.type_args),
                self._type_aliases,
                self._type_alias_params,
            )
            if fn_type is not None:
                return (tuple(fn_type.params), fn_type.return_type)
        return None

    def _infer_fn_alias_type_args_wasm(
        self,
        param_te: ast.NamedType,
        arg: ast.Expr,
    ) -> tuple[str, ...] | None:
        """Infer concrete types for a type alias's params from a callable arg.

        Mirrors :meth:`MonomorphizationMixin._infer_fn_alias_type_args`
        for use during WASM call-site rewriting.  Accepts either an
        ``AnonFn`` literal or a ``SlotRef`` typed as an FnType alias.

        The param alias's body is resolved **transitively** (#867 / PR
        #880 review): the HOF's declared fn param may itself be an alias
        chain (``type MapFn2<X, Y> = MapFn<X, Y>;``).  The chain is
        resolved instantiated at the alias's *own* param names, so the
        terminal ``FnType`` body stays expressed in ``alias_params``
        names — including across renaming hops — and the positional
        matching below is untouched.
        """
        arg_shape = self._resolve_arg_fn_shape_wasm(arg)
        if arg_shape is None:
            return None
        arg_params, arg_return = arg_shape

        alias_params = self._type_alias_params.get(param_te.name)
        if (
            not alias_params
            or not param_te.type_args
            or len(alias_params) != len(param_te.type_args)
        ):
            return None

        alias_te = resolve_fn_type_alias(
            ast.NamedType(
                name=param_te.name,
                type_args=tuple(
                    ast.NamedType(name=p, type_args=None)
                    for p in alias_params
                ),
            ),
            self._type_aliases,
            self._type_alias_params,
        )
        if alias_te is None:
            return None

        alias_mapping: dict[str, str] = {}

        # Match parameter types positionally
        for fn_param_te, arg_param_te in zip(
            alias_te.params, arg_params,
        ):
            if (
                isinstance(fn_param_te, ast.NamedType)
                and fn_param_te.name in alias_params
                and isinstance(arg_param_te, ast.NamedType)
            ):
                alias_mapping[fn_param_te.name] = arg_param_te.name

        # Match return type
        ret = alias_te.return_type
        if isinstance(ret, ast.NamedType) and ret.name in alias_params:
            if isinstance(arg_return, ast.NamedType):
                alias_mapping[ret.name] = arg_return.name
            elif isinstance(arg_return, ast.FnType):
                # Return type is itself a FnType — map to "Fn" to mirror
                # the monomorphiser-side binding in
                # `MonomorphizationMixin._infer_fn_alias_type_args`.
                # CR-8 on PR #659: without this, a higher-order alias
                # (e.g. `type Lifter<F> = fn(Int -> F) effects(pure)`
                # called with a fn-returning AnonFn / alias) leaves
                # the return-type var unbound, falls back to the
                # `"Bool"` phantom-var default at result-building,
                # and `_resolve_generic_call` rewrites the call to a
                # mangled name that doesn't match the mono clone
                # Pass 1.5 registered.
                alias_mapping[ret.name] = "Fn"
        # Handle ADT return types like Option<B>
        if isinstance(ret, ast.NamedType) and ret.type_args:
            for ret_ta in ret.type_args:
                if (
                    isinstance(ret_ta, ast.NamedType)
                    and ret_ta.name in alias_params
                    and isinstance(arg_return, ast.NamedType)
                    and arg_return.type_args
                ):
                    idx = [
                        i for i, rta in enumerate(ret.type_args)
                        if (isinstance(rta, ast.NamedType)
                            and rta.name == ret_ta.name)
                    ]
                    if idx:
                        pos = idx[0]
                        if pos < len(arg_return.type_args):
                            art = arg_return.type_args[pos]
                            if isinstance(art, ast.NamedType):
                                alias_mapping[ret_ta.name] = art.name

        result: list[str] = []
        for ap in alias_params:
            if ap not in alias_mapping:
                return None
            result.append(alias_mapping[ap])
        return tuple(result)

    def _infer_concat_elem_type(self, expr: ast.Expr) -> str | None:
        """Infer the element type name from an array-typed expression.

        The raw inference can surface an ALIAS name for the element —
        the direct arm's type-arg name (`@Array<Row>.0` gives "Row"), the
        alias-spelled-collection arm's inner name, or an ArrayLit element's
        Vera type.  Canonicalize the result to its target's compound
        spelling at this single exit (#1067): the size/pair classification
        downstream (`_element_mem_size` / `_is_pair_element_type`) would
        otherwise fall to the 4-byte opaque-pointer default for what is
        really an 8-byte (ptr, len) pair, silently mis-copying every array
        combinator's elements (`array_reverse(@Grid.0)` via
        `type Row = Array<Int>; type Grid = Array<Row>` returned garbage;
        `array_concat` and depth-2 `array_flatten` read past their
        allocations).  The exit canonicalization is idempotent over the
        per-arm canonical returns documented on `_raw` (#1057/#1062/
        #1064/#1074) — a compound or already-canonical spelling passes
        through unchanged.
        """
        t = self._infer_concat_elem_type_raw(expr)
        if t is None:
            return None
        return self._canonicalize_alias_slot_name(t)[0]

    def _concat_elem_name_from_named(self, elem: ast.NamedType) -> str:
        """Element-type name for a ``NamedType`` array element on the
        concat-inference path, shared by the three arms of
        :meth:`_infer_concat_elem_type_raw` so they classify identically
        (#1097).

        A representation-transparent ``Future<…>`` element (#841) returns
        its FULL canonicalized spelling: the array-element size / store
        helpers ``_strip_future`` the wrapper and size the payload, but a
        bare head ``"Future"`` (type argument dropped) collapses to the
        4-byte i32 default and the copy loop runs a wrong stride over the
        8-byte (or two-word pair) elements — silent garbage on a
        check+verify-green program (#1057).  An alias INSIDE the payload is
        canonicalized (``Future<FlagA>`` -> ``Future<Bool>``, #1074).  A
        bare name canonicalizes + resolves (``type FI = Future<Int>``
        element -> ``Future<Int>``, #1062).  A parameterized non-``Future``
        element keeps its bare head — the name-only canonicalizer cannot
        substitute arguments.  The ``map_values(...)`` FnCall and
        rebuilt-SlotRef arms (#1053) previously returned this element's bare
        head unconditionally, so ``array_concat(map_values(m), …)`` over a
        ``Map<_, Future<Int>>`` ran the wrong stride (the site-2 latent half
        of #1097).
        """
        if elem.name == "Future" and elem.type_args:
            canon, _ = self._canonicalize_alias_slot_name(
                self._format_named_type(elem))
            return canon
        if not elem.type_args:
            canon, _ = self._canonicalize_alias_slot_name(elem.name)
            return self._resolve_base_type_name(canon)
        return elem.name

    def _infer_concat_elem_type_raw(self, expr: ast.Expr) -> str | None:
        """Uncanonicalized element-name inference — see the public wrapper.

        All three element-bearing arms (the direct `Array<T>` SlotRef, the
        #1053 rebuilt-SlotRef arm, and the #1053 FnCall-return arm) classify
        a `NamedType` element through the shared
        :meth:`_concat_elem_name_from_named` so they agree exactly (#1097);
        the two rebuilt arms previously returned the element's bare head, so
        `array_concat(map_values(m), …)` over a `Map<_, Future<Int>>` ran a
        wrong stride while the let-bound `@Array<Future<Int>>` SlotRef (the
        direct arm) was correct.

        For a `Future<T>` element the FULL `Future<…>` spelling is
        preserved (not the bare head `"Future"`), mirroring the sibling
        `_infer_index_element_type` fix (#1045): `Future<T>` is
        representation-transparent (#841), so its array-element width is
        its payload T's.  A bare `"Future"` (args dropped) collapses to
        the i32 default in the element-size / store deciders, so a
        combinator's copy loop runs a 4-byte stride over 8-byte (or
        two-word pair) elements and returns garbage — silent-wrong on a
        check+verify-green program (#1057).  `_strip_future` in the
        element helpers recovers the payload only from the full name.  An
        alias INSIDE that payload (`Future<FlagA>`, `type FlagA = Bool`)
        is canonicalized to `Future<Bool>` before returning (#1074) — the
        full spelling is preserved but the bare alias `FlagA` would
        otherwise itself fall to the 4-byte default under `_strip_future`.

        An ALIAS-spelled element (a bare name like `type FI =
        Future<Int>` in `Array<FI>`) is canonicalized to its target's
        full compound spelling first (#1062): the raw alias name means
        nothing to the module-level element helpers (no alias table
        there), so it fell to the same i32 default — the alias-spelled
        sibling of the #1057 garbage (unmasked for Future aliases once
        #1058 made `Array<FI>` literals buildable; a scalar alias like
        `type Flag = Bool` was reachable-and-wrong before).  The
        canonicalize-then-resolve order mirrors the #1058 literal-store
        fix; a parameterized element (args present) keeps the bare-head
        behavior — the name-only canonicalizer cannot substitute its
        arguments.

        An alias-named COLLECTION (`type Flags = Array<Bool>` — the slot
        name itself, not the element) and a literal whose elements are
        alias-typed slots are canonicalized the same way (#1064; see the
        inline comments on the two arms below), with the #1053 rebuilder
        arm as the broader fall-through for alias-spelled array arguments
        the name-keyed arm cannot resolve.

        A ``Block``-wrapped expression (``array_reverse({ ... })``)
        resolves via its tail expression, matching the container
        emissions' Block handling (#1071).
        """
        while isinstance(expr, ast.Block):
            expr = expr.expr
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Array" and expr.type_args:
                ta = expr.type_args[0]
                if isinstance(ta, ast.NamedType):
                    # Element handling (Future full-spelling #1074, bare-name
                    # canonicalize #1062, parameterized bare head) is shared
                    # with the two rebuilt arms below via the #1097 helper.
                    return self._concat_elem_name_from_named(ta)
            # #1064: alias-named COLLECTION (`type Flags = Array<Bool>;`
            # concat of `@Flags` slots) — the slot name misses the
            # "Array" match above, so the probe returned None and each
            # consumer fell back: concat to an 8-byte default stride
            # (coincidentally right for Int / String / pair elements,
            # silently wrong for 1-byte Bool / Byte), slice and the
            # map-family to a loud skip.  Canonicalize the collection
            # name to its target's full spelling, take the element
            # spelling, and canonicalize a bare element name in turn
            # (`type Grid = Array<Row>` — the target spelling keeps
            # `Row` opaque, and the raw alias would fall to the 4-byte
            # default the #1062 element fix closed).  A parameterized
            # collection (args present) keeps the old fallback — the
            # name-only canonicalizer cannot substitute arguments.
            if expr.type_name != "Array" and not expr.type_args:
                canon, _ = self._canonicalize_alias_slot_name(
                    expr.type_name)
                canon = self._resolve_base_type_name(canon)
                if canon.startswith("Array<") and canon.endswith(">"):
                    elem = canon[len("Array<"):-1]
                    if "<" not in elem:
                        e_canon, _ = self._canonicalize_alias_slot_name(
                            elem)
                        return self._resolve_base_type_name(e_canon)
                    return elem
            # #1053 alias extension: an alias-spelled array argument
            # (`type Row = Array<Int>;` then `@Row.0`) carries its bare
            # alias name with no type args, so the direct arm above never
            # fires and every combinator's element-type triad dropped the
            # function.  Resolve through the shared rebuilder, which
            # canonicalizes a bare alias to its target's compound spelling
            # (#1055) — the call-emission dual of the index-side fix.
            # Runs after the #1064 name-keyed arm: that arm returns on
            # success, so this is the broader fall-through.
            nt = self._named_type_from_arg_info(expr)
            if nt is not None and nt.name == "Array" and nt.type_args:
                elem = nt.type_args[0]
                if isinstance(elem, ast.NamedType):
                    # #1097: mirror the direct arm — a Future<T> element
                    # keeps its full spelling, not the bare "Future" head.
                    return self._concat_elem_name_from_named(elem)
        if isinstance(expr, ast.ArrayLit):
            if expr.elements:
                t = self._infer_vera_type(expr.elements[0])
                # #1064 (literal branch): an element that is itself an
                # alias-typed slot (`array_concat([@Flags.0], …)`)
                # infers to the bare alias name, which the element
                # helpers size at the 4-byte default — the copy mangled
                # the two-word pairs and indexing the result trapped
                # `unreachable`.  Canonicalize a bare name; compound
                # spellings (`Future<Int>`, `Array<Bool>`) and non-alias
                # names pass through unchanged.
                if t is not None and "<" not in t:
                    t, _ = self._canonicalize_alias_slot_name(t)
                    t = self._resolve_base_type_name(t)
                return t
            return None
        if isinstance(expr, ast.FnCall):
            if expr.name == "array_range":
                return "Int"
            # array_map / array_mapi output element type = closure's
            # return type.  Not the input array's element type (that's
            # the *input* of the map, not what we hand to the next
            # combinator).
            if expr.name in ("array_map", "array_mapi") and len(expr.args) == 2:
                return self._infer_closure_return_vera_type(expr.args[1])
            if expr.name in (
                "array_concat", "array_append", "array_slice",
                "array_filter", "array_reverse", "array_sort_by",
            ) and expr.args:
                return self._infer_concat_elem_type(expr.args[0])
            # array_flatten<T>(Array<Array<T>>) → Array<T>: the
            # element type is the inner array's element type.
            if expr.name == "array_flatten" and expr.args:
                outer = self._infer_concat_elem_type(expr.args[0])
                if outer and outer.startswith("Array<") and outer.endswith(">"):
                    return outer[len("Array<"):-len(">")]
            # Array<String>-returning string operations: split, chars,
            # lines, words.  Element type is always String — useful so
            # downstream array combinators (array_map, array_filter)
            # can resolve T to String when chaining off these calls.
            if expr.name in (
                "string_split", "string_chars",
                "string_lines", "string_words",
            ):
                return "String"
            # #1053: any Array-returning builtin whose element type the arms
            # above could not resolve — notably array_flatten of a SlotRef
            # `@Array<Array<T>>`, whose inner `<T>` layer the bare-name helpers
            # drop (they return "Array", not "Array<T>"), so the unwrap above
            # fails.  Derive the full return NamedType via the shared #1051
            # `_builtin_call_ret_named_type` chain and read back its element
            # name.  This lets a type-variable-element builtin (array_flatten,
            # array_reverse, …) nest as another combinator's argument
            # (`array_reverse(array_flatten(x))`) resolve its element type on
            # this call-emission inference path — the sibling of the #1051
            # index-path fix.  A genuinely unresolvable call still yields None,
            # keeping the loud [E602] skip.
            ret_nt = self._builtin_call_ret_named_type(expr)
            if (ret_nt is not None and ret_nt.name == "Array"
                    and ret_nt.type_args):
                elem = ret_nt.type_args[0]
                if isinstance(elem, ast.NamedType):
                    # #1097: mirror the direct arm — a Future<T> element of
                    # an Array-returning builtin (e.g. map_values over a
                    # Map<_, Future<Int>>) keeps its full spelling so the
                    # concat copy loop strides at the payload width, not the
                    # bare "Future" head's 4-byte default.
                    return self._concat_elem_name_from_named(elem)
        return None
