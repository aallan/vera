"""Function call and effect handler translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.monomorphize import Monomorphizer, resolve_fn_type_alias
from vera.skip import CodegenSkip
from vera.slots import bare_call_denotes_user_fn
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
        self, call: ast.FnCall, env: WasmSlotEnv,
        *, denotes_op: bool | None = None,
    ) -> list[str] | None:
        """Translate a function call to WASM call instruction.

        If the call name matches an effect operation (e.g. get/put for
        State<T>), redirects to the corresponding host import.

        *denotes_op* overrides the bare-call ownership question (#1284) for
        a call this dispatcher did not receive bare.  ``None`` — every
        ordinary ``ast.FnCall`` — asks :meth:`_bare_call_denotes_op`.
        ``True`` is for the QUALIFIED spellings that delegate here by
        synthesizing a bare node (``State.get``/``State.put``/``Exn.throw``,
        below): the qualifier already named the effect, so no user
        declaration can shadow it and the synthesized node must not be
        re-asked as if the user had written the bare form.
        """
        # Built-in intrinsics — only when no user-defined function
        # with the same name exists.  User definitions take priority
        # so that e.g. a user-defined length(@List<Int> -> @Nat) is
        # not mistakenly compiled as the array-length built-in.  Same
        # ownership rule the effect-op dispatch below applies, over the
        # same table (#1284); spelled through the shared predicate so a
        # change to the rule reaches both.  The table is the LEXICAL one
        # (#1299) — an intrinsic must not be displaced by a declaration
        # this call site cannot see, any more than an operation must.
        if not bare_call_denotes_user_fn(call.name, self._scoped_fns):
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

        # #1284: whose declaration this call site names, asked ONCE and
        # consumed by every op route below.  The op registries are keyed by
        # op NAME and say which cell that name reaches; they do NOT say
        # whether this call is the operation at all, and reading them as if
        # they did is the defect: a program declaring `fn get` had its
        # ordinary calls lowered to the host cell intrinsic under any
        # enclosing `handle[State<T>]` — a silently wrong value, a module
        # WASM validation rejected, or a spurious [E602] naming a State
        # operation the source never contained.  The checker resolved every
        # one of those call sites to the user's declaration (E201/E202
        # report against the user's signature), so this is that answer.
        if denotes_op is None:
            denotes_op = self._bare_call_denotes_op(call.name)

        if denotes_op:
            # #1233: inside an inlined clause body, an outward-routed op of
            # the SAME cell family cannot address the enclosing cell — the
            # intrinsics only reach the innermost cell of a family.  Refuse
            # it here, before either dispatch below picks a route, so both
            # the clause-inline and the bare-import path are covered by one
            # gate (and so is the qualified `State.get`/`State.put`
            # spelling, which delegates here).  Gated on ownership with the
            # dispatch it guards: a user function's call reaches no cell, so
            # asking whether it can address one refused compilable programs.
            self._reject_unaddressable_clause_op(call)

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
            if self._state_clause_family_base is not None:
                # #865/#1212: the resumed value is the op's result at the
                # call site, so a Byte cell's `resume(1)` — and
                # `resume(if c then { 1 } else { 2 })`, the very form the
                # E602 clause skip message recommends — must lower at i32.
                # Marked before translating; the ONE branch descent.
                self._mark_state_byte_write(
                    call.args[0], self._state_clause_family_base)
            return self.translate_expr(call.args[0], env)

        # Check if this is an effect operation (e.g. get/put/throw)
        if denotes_op and call.name in self._effect_ops:
            target_name, _is_void = self._effect_ops[call.name]
            instructions: list[str] = []
            # #747: the effect-op-argument @Int -> @Nat narrowing is in
            # general unguarded here — `_effect_ops` carries only the
            # dispatch target, not the op's formal types (#754 tracks the
            # general registry).  The builtin State `put` is the exception
            # (#1203, PR #1202 adversarial round): the cell it writes is
            # recorded beside the dispatch target, so the same nat/widen
            # guard pair the clause-inlined path emits wraps the argument on
            # the bare path too — a handler with no `put` clause, a `put`
            # inside another clause's body, and a delegated bare `put`
            # (handler in the caller) all previously stored a negative
            # silently.
            #
            # The cell's REPRESENTATION name, read from `_effect_op_cells`
            # (#1218).  This used to SLICE the family back out of the
            # dispatch target (`target_name[len("$vera.state_put_"):]`) and
            # hand the MANGLED result to `_resolve_base_type_name`, which
            # expects a canonical one — a second derivation of the family
            # that worked only because `Nat`/`Int`/`Byte` mangle to
            # themselves.  A refined `Nat` cell does not (its family carries
            # the predicate), so the slice would have matched nothing and
            # switched this guard off silently, while the verifier went on
            # recording the obligation as `tier3_runtime`.
            # ONE normalisation for all three sibling decisions (PR #1238
            # review).  The Nat/Int guards resolved `cell.base` and the Byte
            # width coercion did not, so a base that still needs alias
            # resolution — which `family_fallback_name`'s residue can produce
            # — would fire the guards and skip the coercion, putting an
            # `i64.const` into an i32 cell.
            cell = self._effect_op_cells.get(call.name)
            is_state_put = (
                call.name == "put" and len(call.args) == 1
                and cell is not None
            )
            # `throw`'s payload is the OTHER cell-carrying write boundary
            # (#1269).  The `Exn<E>` tag is declared at the payload's
            # representation width — i32 for a `@Byte` payload, refined or
            # not — while an int literal defaults to `i64.const`, so
            # `throw(5)` into `Exn<{ @Byte | … }>` emitted a module WASM
            # validation rejects at load.  Same marking, same derivation,
            # different op — and, since #1268, the same narrowing GUARDS
            # below: the payload is a write boundary in the full sense, not
            # only in its width.
            is_exn_throw = (
                call.name == "throw" and len(call.args) == 1
                and cell is not None
            )
            # `_boundary_base`'s composition with its FIRST hop already
            # performed, at registration: the registry carries a name, not
            # the type expression, so this site cannot call the named helper
            # and applies the residue chase itself.  Two of the three
            # producers (both `handle` sites) store an already-chased base,
            # so this is a no-op for them; the declaration-row producer
            # (`codegen/functions.py`) has no `_resolve_base_type_name` to
            # reach, which is the only reason the hop still lives here.
            #
            # UNTESTED as of #1273: deleting the chase leaves the suite green,
            # because `family_base_name` already answers `Byte` for every
            # refinement and alias reachable today, so no producer stores a
            # base that still needs chasing.  It is defence for the residue
            # `family_fallback_name` can return (a function or unknown type),
            # which no boundary that asks this question can currently carry.
            # A fixture exercising it needs a producer that stores an
            # UNCHASED base — construct one and this becomes testable.
            base = (
                self._resolve_base_type_name(cell.base)
                if (is_state_put or is_exn_throw) and cell is not None
                else None
            )
            if is_state_put or is_exn_throw:
                # #865/#1212: mark the Byte width BEFORE the argument is
                # translated, so a literal — or the literal leaves of an
                # `if` / `match` argument — lowers at the cell's i32 width.
                # The general entry rather than `_mark_state_byte_write`,
                # which names the State cell this branch no longer only
                # serves.
                self._mark_byte_write_value(call.args[0], base or "")
            for arg in call.args:
                arg_instrs = self.translate_expr(arg, env)
                if arg_instrs is None:
                    return None
                instructions.extend(arg_instrs)
            # The write boundary's guards.  `throw` joined `put` here in
            # #1268: its payload narrows into the `Exn<E>` slot exactly as
            # `put`'s argument narrows into the cell, but it crossed no
            # function boundary, so none of §2.6.5's composing guards covered
            # it — `throw(0 - 5)` into an `Exn<Nat>` ran to completion and
            # handed `-5` to a clause that had assumed non-negativity, and a
            # `@Nat`-typed consumer's Tier-1-PROVED `ensures` then failed at
            # run time.  The three arms mirror the verifier's
            # `_obligate_binding_triple` one-for-one, refined FIRST for the
            # same reason it is: the refinement's own predicate carries the
            # base's implicit range (`_refinement_guard_parts` conjoins it),
            # so the sign guards would be redundant under it, and running
            # them instead of it would check `>= 0` where the boundary
            # invariant is `> 0`.
            refined_payload: ast.TypeExpr | None = None
            if is_exn_throw and cell is not None:
                refined_payload = self._refined_exn_payload_type(cell, call)
                if refined_payload is not None:
                    instructions = self._emit_exn_payload_refine_guard(
                        instructions, refined_payload, cell, call, env)
                    # #820 INTERSECTION (PR #1325 review): the predicate does
                    # not imply fit-in-i64, so a refinement OVER `@Int` keeps
                    # the widening guard BESIDE its predicate guard rather
                    # than replacing it.  Without this, adding a refinement
                    # weakened the boundary: `Exn<Int>` fed a @Nat of u64.MAX
                    # trapped, `Exn<{ @Int | true }>` returned -1.  The
                    # verifier's `_obligate_binding_triple` records the pair
                    # in the same shape, so obligation and guard still match
                    # one-for-one.
                    if base == "Int" and self._result_is_nat(call.args[0]):
                        instructions = self._emit_int_widen_guard(instructions)
            if refined_payload is None and (is_state_put or is_exn_throw):
                if base == "Nat" and self._narrows_into_nat(call.args[0]):
                    instructions = self._emit_nat_bind_guard(instructions)
                elif base == "Int" and self._result_is_nat(call.args[0]):
                    instructions = self._emit_int_widen_guard(instructions)
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
            if i < len(byte_params) and byte_params[i]:
                # The bidirectional checker (`_synth_expr(expected=Byte)`)
                # accepts a 0..255 int literal as a Byte argument (spec §11);
                # lower it as i32 rather than the default i64 to match the
                # callee's i32 Byte parameter.  Non-literal Byte arguments (a
                # Byte slot ref, a Byte-returning call) already yield i32 via
                # `translate_expr`, so only the literal needs the override.
                # #1212: the same coercion for a literal inside an `if` /
                # `match` argument, through the ONE branch descent — the
                # bare-`IntLit` test this replaced left
                # `byte_id(if c then { 1 } else { 2 })` invalid WASM.
                self._mark_byte_write_value(arg, "Byte")
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
        if (call.qualifier == "State" and call.name in ("get", "put")
                and (call.name in self._state_clause_ops
                     or call.name in self._effect_ops)):
            # The builtin State ops route through the UNQUALIFIED
            # dispatcher, which owns the clause-inline registry, the
            # #1203 argument guards, and the #865 Byte coercion — the
            # qualified spelling previously took a bare unguarded call:
            # `State.put(x)` inside a handled body skipped the clause's
            # `with` transform, stored a negative into a @Nat cell
            # silently, and emitted a Byte literal at i64 (round-4
            # review).  Delegation makes the two spellings identical by
            # construction — guarded on the op resolving, so a row that
            # registered no State cell still falls through to the legacy
            # path's loud unknown-func failure.
            #
            # `denotes_op=True` (#1284): the qualifier NAMED the effect, so
            # this call site is the operation whatever the program's
            # declarations are called.  Without it, the synthesized bare
            # node would be re-asked the ownership question and, in a
            # program that also declares `fn get`, silently dispatch to the
            # user's function — the round-5 hazard, which the pre-#1284
            # `_fn_sigs` registry guard sidestepped only by making the
            # registry incomplete (and so failing this spelling loudly at
            # the declared-row site: `unknown func: $vera.get`).
            return self._translate_call(
                ast.FnCall(name=call.name, args=call.args, span=call.span),
                env, denotes_op=True,
            )
        if (call.qualifier == "Exn" and call.name == "throw"
                and "throw" in self._effect_ops):
            # `Exn.throw(x)` delegates for exactly the reason `State.put(x)`
            # does: the payload's #1212 Byte marking lives on the bare
            # dispatcher (#1269), and a qualified spelling that skipped it
            # emitted an `i64.const` under an i32 tag while the bare one
            # compiled.  Guarded on the op resolving, same as the State
            # twin — an unresolved `throw` falls through to the legacy path
            # below rather than synthesizing a bare call that would miss.
            # `denotes_op=True` for the same reason as the State twin.
            return self._translate_call(
                ast.FnCall(name=call.name, args=call.args, span=call.span),
                env, denotes_op=True,
            )
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
        _host_import_qualifiers = {"Http", "Inference", "IO", "Random", "DB"}
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
        elif call.qualifier == "DB":
            # #229 — DB.query / DB.execute → `call $vera.db_<op>`; both return
            # a Result ADT heap pointer, so $alloc is required.
            wasm_name = f"db_{call.name}"
            self._db_ops_used.add(wasm_name)
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
        # #1327/#1366: the rewrite side's leg of the fail-closed default —
        # see the result loop below.
        unnamed_direct: set[str] = set()

        for param_te, arg in zip(param_types, call.args):
            self._unify_param_arg_wasm(
                param_te, arg, forall_vars, mapping, constrained_vars,
                partial_adt, unnamed_direct)

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
                # #1327/#1366 — FAIL CLOSED before defaulting.  A var bound by
                # a DIRECT `@T` parameter is determined by that argument's
                # type; arriving here means no arm named the argument, so
                # `Bool` would be a guess.  Answer "inference failed" (this
                # method's documented `None`), which leaves the call on its
                # bare name and reaches the guard rail's source-located
                # [E602] — rather than mangling a symbol on a guess, which
                # either dangles or, worse, names a clone whose WASM types do
                # not match the value being passed.  The phantom-var default
                # is retained for every other var: one no parameter position
                # determines is not inferable by construction, and the emitted
                # WASM is identical whatever it is named.
                if tv in unnamed_direct:
                    return None
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
        unnamed_direct: set[str] | None = None,
    ) -> None:
        """Unify a parameter TypeExpr against an argument to bind type vars.

        Mirrors CodeGenerator._unify_param_arg for use during WASM
        translation — ``unnamed_direct`` included (#1327/#1366): the set of
        type variables a DIRECT ``@T`` parameter binds whose argument this
        namer could not type, which is the rewrite side's evidence that a
        mangled name would be a guess rather than a resolution.
        """
        if isinstance(param_te, ast.RefinementType):
            self._unify_param_arg_wasm(
                param_te.base_type, arg, forall_vars, mapping,
                constrained_vars, partial_adt, unnamed_direct,
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
            elif not vera_type and unnamed_direct is not None:
                # #1327/#1366: the parameter IS the type variable, so this
                # argument's type is the instantiation — and no arm named it.
                # Mirrors `Monomorphizer._unify_param_arg`'s record so the two
                # consultors fail closed on the same shapes.
                unnamed_direct.add(param_te.name)
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
                self._alias_env.aliases,
                self._alias_env.alias_params,
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

        alias_params = self._alias_env.alias_params.get(param_te.name)
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
            self._alias_env.aliases,
            self._alias_env.alias_params,
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
