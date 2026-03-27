"""Type inference and utility mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import _element_wasm_type


class InferenceMixin:
    """Mixin providing type inference and type-mapping utilities.

    Extracted methods:
    - _infer_expr_wasm_type
    - _infer_fncall_wasm_type
    - _infer_block_result_type
    - _infer_vera_type
    - _infer_fncall_vera_type
    - _ctor_to_adt_name
    - _is_array_type_name (staticmethod)
    - _is_pair_type_name (staticmethod)
    - _infer_array_element_type
    - _infer_index_element_type
    - _get_arg_type_info_wasm
    - _infer_apply_fn_return_type
    - _fn_type_return_wasm
    - _fn_type_param_wasm_types
    - _type_expr_name
    - _type_name_to_wasm
    - _type_expr_to_slot_name
    - _resolve_base_type_name
    - _slot_name_to_wasm_type
    """

    # -----------------------------------------------------------------
    # Binary operators
    # -----------------------------------------------------------------

    # Arithmetic: i64 ops (default for Int/Nat)
    _ARITH_OPS: dict[ast.BinOp, str] = {
        ast.BinOp.ADD: "i64.add",
        ast.BinOp.SUB: "i64.sub",
        ast.BinOp.MUL: "i64.mul",
        ast.BinOp.DIV: "i64.div_s",
        ast.BinOp.MOD: "i64.rem_s",
    }

    # Arithmetic: f64 ops (Float64)
    _ARITH_OPS_F64: dict[ast.BinOp, str] = {
        ast.BinOp.ADD: "f64.add",
        ast.BinOp.SUB: "f64.sub",
        ast.BinOp.MUL: "f64.mul",
        ast.BinOp.DIV: "f64.div",
        # MOD: handled by _translate_f64_mod() — WASM has no f64.rem
    }

    # Comparison: i64 → i32 (default)
    _CMP_OPS: dict[ast.BinOp, str] = {
        ast.BinOp.EQ: "i64.eq",
        ast.BinOp.NEQ: "i64.ne",
        ast.BinOp.LT: "i64.lt_s",
        ast.BinOp.GT: "i64.gt_s",
        ast.BinOp.LE: "i64.le_s",
        ast.BinOp.GE: "i64.ge_s",
    }

    # Comparison: f64 → i32 (Float64)
    _CMP_OPS_F64: dict[ast.BinOp, str] = {
        ast.BinOp.EQ: "f64.eq",
        ast.BinOp.NEQ: "f64.ne",
        ast.BinOp.LT: "f64.lt",
        ast.BinOp.GT: "f64.gt",
        ast.BinOp.LE: "f64.le",
        ast.BinOp.GE: "f64.ge",
    }

    def _infer_expr_wasm_type(self, expr: ast.Expr) -> str | None:
        """Infer the WAT result type of an expression.

        Returns "i64" for Int/Nat, "f64" for Float64, "i32" for Bool,
        None for unknown/Unit.  Used to select the correct operators.
        """
        if isinstance(expr, ast.IntLit):
            return "i64"
        if isinstance(expr, ast.FloatLit):
            return "f64"
        if isinstance(expr, ast.BoolLit):
            return "i32"
        if isinstance(expr, ast.UnitLit):
            return None
        if isinstance(expr, ast.SlotRef):
            resolved = self._resolve_base_type_name(expr.type_name)
            if resolved in ("Int", "Nat"):
                return "i64"
            if resolved == "Float64":
                return "f64"
            if resolved in ("Bool", "Byte"):
                return "i32"
            if self._is_pair_type_name(resolved):
                return "i32_pair"
            base = (resolved.split("<")[0]
                    if "<" in resolved else resolved)
            # Opaque handle types — i32 handles managed by host runtime
            if base in ("Decimal", "Map", "Set"):
                return "i32"
            if base in self._adt_type_names:
                return "i32"
            # Function type aliases → i32 (closure pointer)
            alias_te = self._type_aliases.get(expr.type_name)
            if isinstance(alias_te, ast.FnType):
                return "i32"
            return None
        if isinstance(expr, ast.ResultRef):
            if expr.type_name in ("Int", "Nat"):
                return "i64"
            if expr.type_name == "Float64":
                return "f64"
            if expr.type_name in ("Bool", "Byte"):
                return "i32"
            return None  # pragma: no cover
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in self._ARITH_OPS:
                # Propagate operand type: f64 if operands are f64
                inner = self._infer_expr_wasm_type(expr.left)
                return inner if inner == "f64" else "i64"
            if expr.op in self._CMP_OPS:
                return "i32"
            if expr.op in (ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES):
                return "i32"
        if isinstance(expr, ast.UnaryExpr):
            if expr.op == ast.UnaryOp.NEG:
                inner = self._infer_expr_wasm_type(expr.operand)
                return inner if inner == "f64" else "i64"
            if expr.op == ast.UnaryOp.NOT:
                return "i32"
        if isinstance(expr, ast.FnCall):
            return self._infer_fncall_wasm_type(expr)
        if isinstance(expr, ast.ConstructorCall):
            return "i32" if expr.name in self._ctor_layouts else None
        if isinstance(expr, ast.NullaryConstructor):
            return "i32" if expr.name in self._ctor_layouts else None
        if isinstance(expr, ast.MatchExpr):
            if expr.arms:
                return self._infer_expr_wasm_type(expr.arms[0].body)
            return None  # pragma: no cover
        if isinstance(expr, ast.HandleExpr):
            # Handle expression result type is the body's result type
            if expr.body.expr:
                return self._infer_expr_wasm_type(expr.body.expr)
            return None  # pragma: no cover
        if isinstance(expr, ast.IndexExpr):
            elem_type = self._infer_index_element_type(expr)
            return _element_wasm_type(elem_type) if elem_type else None
        if isinstance(expr, ast.ArrayLit):
            return "i32_pair"
        if isinstance(expr, ast.StringLit):
            return "i32_pair"
        if isinstance(expr, ast.InterpolatedString):
            return "i32_pair"
        if isinstance(expr, ast.QualifiedCall):
            return self._infer_qualified_call_wasm_type(expr)
        if isinstance(expr, ast.IfExpr):
            return self._infer_block_result_type(expr.then_branch)
        if isinstance(expr, ast.Block):
            return self._infer_block_result_type(expr)
        if isinstance(expr, (ast.ForallExpr, ast.ExistsExpr)):
            return "i32"  # quantifiers return Bool
        if isinstance(expr, (ast.AssertExpr, ast.AssumeExpr)):
            return None  # assert/assume return Unit
        return None

    _IO_WASM_TYPES: dict[str, str | None] = {
        "print": None,
        "read_line": "i32_pair",
        "read_file": "i32",
        "write_file": "i32",
        "args": "i32_pair",
        "exit": None,
        "get_env": "i32",
    }

    def _infer_qualified_call_wasm_type(
        self, expr: ast.QualifiedCall,
    ) -> str | None:
        """Infer the WASM return type of a qualified call (IO/Http ops)."""
        if expr.qualifier == "IO":
            return self._IO_WASM_TYPES.get(expr.name)
        if expr.qualifier == "Http":
            # Both get and post return Result<String, String> (i32 heap ptr)
            return "i32"
        if expr.qualifier == "Inference":
            # complete returns Result<String, String> (i32 heap ptr)
            return "i32"
        return None  # pragma: no cover

    def _infer_fncall_wasm_type(self, expr: ast.FnCall) -> str | None:
        """Infer the WASM return type of a function call.

        For generic calls, resolves the mangled name and looks up its
        registered return type.  For non-generic calls, uses the
        registered return type directly.  For apply_fn, infers from
        the closure's function type.
        """
        # array_length(array) → Int (i64)
        if expr.name == "array_length":
            return "i64"
        # array_range(start, end) → Array<Int> (i32_pair)
        if expr.name in ("array_range", "array_slice"):
            return "i32_pair"
        # string_length(string) → Int (i64)
        if expr.name == "string_length":
            return "i64"
        # string_concat / string_slice / string_strip → String (i32_pair)
        if expr.name in ("string_concat", "string_slice", "string_strip",
                          "to_string", "int_to_string",
                          "bool_to_string", "nat_to_string",
                          "byte_to_string", "float_to_string"):
            return "i32_pair"
        # string_char_code → Nat (i64)
        if expr.name == "string_char_code":
            return "i64"
        # string_from_char_code → String (i32_pair)
        if expr.name == "string_from_char_code":
            return "i32_pair"
        # string_repeat → String (i32_pair)
        if expr.name == "string_repeat":
            return "i32_pair"
        # String search builtins
        if expr.name in ("string_contains", "string_starts_with",
                          "string_ends_with"):
            return "i32"
        if expr.name == "string_index_of":
            return "i32"
        # String transformation builtins
        if expr.name in ("string_upper", "string_lower", "string_replace",
                          "string_join"):
            return "i32_pair"
        if expr.name == "string_split":
            return "i32_pair"
        # parse/decode builtins → Result<T, String> (i32 heap pointer)
        if expr.name in (
            "parse_nat", "parse_int", "parse_float64", "parse_bool",
            "base64_decode", "url_decode",
        ):
            return "i32"
        if expr.name in ("base64_encode", "url_encode", "url_join"):
            return "i32_pair"
        if expr.name == "url_parse":
            return "i32"
        # Markdown builtins
        if expr.name in ("md_parse", "md_has_heading", "md_has_code_block"):
            return "i32"
        if expr.name in ("md_render", "md_extract_code_blocks"):
            return "i32_pair"
        # Regex builtins — all return Result<T, String> → heap ptr (i32)
        if expr.name in (
            "regex_match", "regex_find", "regex_find_all",
            "regex_replace",
        ):
            return "i32"
        # Ability operations: show → String (i32_pair), hash → Int (i64)
        if expr.name == "show":
            return "i32_pair"
        if expr.name == "hash":
            return "i64"
        # Async builtins — identity operations (Future<T> is transparent)
        if expr.name in ("async", "await") and expr.args:
            return self._infer_expr_wasm_type(expr.args[0])
        # Decimal builtins
        if expr.name in ("decimal_from_int", "decimal_from_float",
                          "decimal_add", "decimal_sub", "decimal_mul",
                          "decimal_neg", "decimal_round", "decimal_abs"):
            return "i32"  # opaque handle
        if expr.name in ("decimal_from_string", "decimal_div"):
            return "i32"  # Option<Decimal> heap pointer
        if expr.name == "decimal_compare":
            return "i32"  # Ordering heap pointer
        if expr.name == "decimal_eq":
            return "i32"  # Bool
        if expr.name == "decimal_to_float":
            return "f64"
        if expr.name == "decimal_to_string":
            return "i32_pair"  # String (ptr, len)
        # Map builtins
        if expr.name in ("map_new", "map_insert", "map_remove"):
            return "i32"  # opaque handle
        if expr.name == "map_get":
            return "i32"  # Option heap pointer
        if expr.name == "map_contains":
            return "i32"  # Bool
        if expr.name == "map_size":
            return "i64"
        if expr.name in ("map_keys", "map_values"):
            return "i32_pair"  # Array (ptr, len)
        # Set builtins
        if expr.name in ("set_new", "set_add", "set_remove"):
            return "i32"  # opaque handle
        if expr.name == "set_contains":
            return "i32"  # Bool
        if expr.name == "set_size":
            return "i64"
        if expr.name == "set_to_array":
            return "i32_pair"  # Array (ptr, len)
        # Json builtins
        if expr.name == "json_parse":
            return "i32"  # Result<Json, String> heap pointer
        if expr.name == "json_stringify":
            return "i32_pair"  # String (ptr, len)
        # Html builtins
        if expr.name == "html_parse":
            return "i32"  # Result<HtmlNode, String> heap pointer
        if expr.name == "html_to_string":
            return "i32_pair"  # String (ptr, len)
        if expr.name == "html_query":
            return "i32_pair"  # Array<HtmlNode> (ptr, len)
        if expr.name == "html_text":
            return "i32_pair"  # String (ptr, len)
        # Numeric math builtins
        if expr.name in ("abs", "min", "max", "floor", "ceil", "round"):
            return "i64"
        if expr.name in ("sqrt", "pow"):
            return "f64"
        # Numeric type conversions
        if expr.name == "int_to_float":
            return "f64"
        if expr.name in ("float_to_int", "nat_to_int", "byte_to_int"):
            return "i64"
        if expr.name in ("int_to_nat", "int_to_byte"):
            return "i32"
        # Float64 predicates and constants
        if expr.name in ("float_is_nan", "float_is_infinite"):
            return "i32"
        if expr.name in ("nan", "infinity"):
            return "f64"
        # apply_fn(closure, args...) — infer from closure type
        if expr.name == "apply_fn" and len(expr.args) >= 1:
            return self._infer_apply_fn_return_type(expr.args[0])
        # Try generic call resolution first
        if expr.name in self._generic_fn_info:
            mangled = self._resolve_generic_call(expr)
            if mangled and mangled in self._fn_ret_types:
                return self._fn_ret_types[mangled]
        # Non-generic function — direct lookup
        if expr.name in self._fn_ret_types:
            return self._fn_ret_types[expr.name]
        return None

    def _infer_block_result_type(self, block: ast.Block) -> str | None:
        """Infer the WAT result type of a block from its final expression."""
        expr = block.expr
        if isinstance(expr, ast.IntLit):
            return "i64"
        if isinstance(expr, ast.FloatLit):
            return "f64"
        if isinstance(expr, ast.BoolLit):
            return "i32"
        if isinstance(expr, ast.UnitLit):
            return None
        if isinstance(expr, ast.SlotRef):
            # Check type name to infer WAT type
            name = self._resolve_base_type_name(expr.type_name)
            if name in ("Int", "Nat"):
                return "i64"
            if name == "Float64":
                return "f64"
            if name in ("Bool", "Byte"):
                return "i32"
            if self._is_pair_type_name(name):
                return "i32_pair"
            base = name.split("<")[0] if "<" in name else name
            # Opaque handle types — i32 handles managed by host runtime
            if base in ("Decimal", "Map", "Set"):
                return "i32"
            if base in self._adt_type_names:
                return "i32"
            return None  # pragma: no cover
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in self._ARITH_OPS:
                inner = self._infer_expr_wasm_type(expr.left)
                return inner if inner == "f64" else "i64"
            if expr.op in self._CMP_OPS:
                return "i32"
            if expr.op in (ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES):
                return "i32"
        if isinstance(expr, ast.UnaryExpr):
            if expr.op == ast.UnaryOp.NEG:
                inner = self._infer_expr_wasm_type(expr.operand)
                return inner if inner == "f64" else "i64"
            if expr.op == ast.UnaryOp.NOT:
                return "i32"
        if isinstance(expr, ast.IfExpr):
            return self._infer_block_result_type(expr.then_branch)
        if isinstance(expr, ast.FnCall):
            return self._infer_fncall_wasm_type(expr)
        if isinstance(expr, ast.QualifiedCall):
            return self._infer_qualified_call_wasm_type(expr)
        if isinstance(expr, ast.StringLit):
            return "i32_pair"
        if isinstance(expr, ast.InterpolatedString):
            return "i32_pair"
        if isinstance(expr, ast.Block):
            return self._infer_block_result_type(expr)
        if isinstance(expr, ast.ConstructorCall):
            return "i32" if expr.name in self._ctor_layouts else None
        if isinstance(expr, ast.NullaryConstructor):
            return "i32" if expr.name in self._ctor_layouts else None
        if isinstance(expr, ast.MatchExpr):
            if expr.arms:
                return self._infer_expr_wasm_type(expr.arms[0].body)
            return None  # pragma: no cover
        if isinstance(expr, ast.IndexExpr):
            elem_type = self._infer_index_element_type(expr)
            return _element_wasm_type(elem_type) if elem_type else None
        if isinstance(expr, ast.ArrayLit):
            return "i32_pair"
        if isinstance(expr, (ast.ForallExpr, ast.ExistsExpr)):
            return "i32"  # quantifiers return Bool
        if isinstance(expr, (ast.AssertExpr, ast.AssumeExpr)):
            return None  # pragma: no cover — assert/assume return Unit
        return None  # pragma: no cover

    @staticmethod
    def _format_named_type(te: ast.NamedType) -> str:
        """Format a NamedType as a full type name including type args.

        Note: duplicated in MonomorphizationMixin._format_type_name
        (monomorphize.py). Both must remain in sync.
        """
        if not te.type_args:
            return te.name
        arg_names = []
        for ta in te.type_args:
            if isinstance(ta, ast.NamedType):
                arg_names.append(
                    InferenceMixin._format_named_type(ta))
            else:
                return te.name
        return f"{te.name}<{', '.join(arg_names)}>"

    def _infer_vera_type(self, expr: ast.Expr) -> str | None:
        """Infer the Vera type name of an expression for call rewriting."""
        if isinstance(expr, ast.IntLit):
            return "Int"
        if isinstance(expr, ast.BoolLit):
            return "Bool"
        if isinstance(expr, ast.FloatLit):
            return "Float64"
        if isinstance(expr, ast.UnitLit):
            return "Unit"
        if isinstance(expr, ast.SlotRef):
            if expr.type_args:
                arg_names = []
                for ta in expr.type_args:
                    if isinstance(ta, ast.NamedType):
                        arg_names.append(self._format_named_type(ta))
                    else:
                        return expr.type_name
                return f"{expr.type_name}<{', '.join(arg_names)}>"
            return expr.type_name
        if isinstance(expr, ast.ConstructorCall):
            return self._ctor_to_adt_name(expr.name)
        if isinstance(expr, ast.NullaryConstructor):
            return self._ctor_to_adt_name(expr.name)
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in (ast.BinOp.EQ, ast.BinOp.NEQ, ast.BinOp.LT,
                           ast.BinOp.GT, ast.BinOp.LE, ast.BinOp.GE,
                           ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES):
                return "Bool"
            return self._infer_vera_type(expr.left)
        if isinstance(expr, ast.UnaryExpr):
            if expr.op == ast.UnaryOp.NOT:
                return "Bool"
            return self._infer_vera_type(expr.operand)
        if isinstance(expr, ast.FnCall):
            return self._infer_fncall_vera_type(expr)
        if isinstance(expr, ast.StringLit):
            return "String"
        if isinstance(expr, ast.InterpolatedString):
            return "String"
        if isinstance(expr, ast.ArrayLit):
            return "Array"
        if isinstance(expr, ast.IndexExpr):
            elem = self._infer_index_element_type(expr)
            return elem
        if isinstance(expr, ast.IfExpr):
            if expr.then_branch.expr is not None:
                return self._infer_vera_type(expr.then_branch.expr)
            return None  # pragma: no cover
        return None  # pragma: no cover

    def _infer_fncall_vera_type(self, call: ast.FnCall) -> str | None:
        """Infer Vera return type of a function call.

        For generic calls, resolves type args and substitutes into
        the return TypeExpr.  For non-generic calls, maps from WASM
        return type back to Vera type name.
        """
        if call.name == "array_length":
            return "Int"
        if call.name in ("array_range", "array_slice"):
            return "Array"
        if call.name == "string_length":
            return "Int"
        if call.name in ("string_concat", "string_slice", "string_strip",
                          "to_string", "int_to_string",
                          "bool_to_string", "nat_to_string",
                          "byte_to_string", "float_to_string"):
            return "String"
        if call.name == "string_char_code":
            return "Nat"
        if call.name == "string_from_char_code":
            return "String"
        if call.name == "string_repeat":
            return "String"
        # String search builtins
        if call.name in ("string_contains", "string_starts_with",
                          "string_ends_with"):
            return "Bool"
        if call.name == "string_index_of":
            return "Option"
        # String transformation builtins
        if call.name in ("string_upper", "string_lower", "string_replace",
                          "string_join"):
            return "String"
        if call.name == "string_split":
            return "Array"
        if call.name in (
            "parse_nat", "parse_int", "parse_float64", "parse_bool",
            "base64_decode", "url_decode",
        ):
            return "Result"
        if call.name in ("base64_encode", "url_encode", "url_join"):
            return "String"
        if call.name == "url_parse":
            return "Result"
        # Markdown builtins
        if call.name == "md_parse":
            return "Result"
        if call.name == "md_render":
            return "String"
        # Json builtins
        if call.name == "json_parse":
            return "Result"
        if call.name == "json_stringify":
            return "String"
        # Html builtins
        if call.name == "html_parse":
            return "Result"
        if call.name == "html_to_string":
            return "String"
        if call.name == "html_query":
            return "Array"
        if call.name == "html_text":
            return "String"
        if call.name == "html_attr":
            return "Option"
        if call.name in ("md_has_heading", "md_has_code_block"):
            return "Bool"
        if call.name == "md_extract_code_blocks":
            return "Array"
        # Regex builtins — all return Result
        if call.name in (
            "regex_match", "regex_find", "regex_find_all",
            "regex_replace",
        ):
            return "Result"
        # apply_fn(closure, args...) — infer from closure's return type
        if call.name == "apply_fn" and call.args:
            closure_arg = call.args[0]
            if isinstance(closure_arg, ast.SlotRef):
                alias_te = self._type_aliases.get(closure_arg.type_name)
                if isinstance(alias_te, ast.FnType):
                    alias_params = self._type_alias_params.get(
                        closure_arg.type_name)
                    if (alias_params and closure_arg.type_args
                            and len(alias_params)
                            == len(closure_arg.type_args)):
                        # Substitute type args into the return type
                        alias_map = dict(zip(alias_params,
                                             closure_arg.type_args))
                        ret = alias_te.return_type
                        if isinstance(ret, ast.NamedType):
                            if ret.name in alias_map:
                                ta = alias_map[ret.name]
                                if isinstance(ta, ast.NamedType):
                                    return ta.name
                            return ret.name
                    elif isinstance(alias_te.return_type, ast.NamedType):
                        return alias_te.return_type.name
        # Map builtins
        if call.name in ("map_new", "map_insert", "map_remove"):
            return "Map"
        if call.name == "map_get":
            return "Option"
        if call.name == "map_contains":
            return "Bool"
        if call.name == "map_size":
            return "Int"
        if call.name in ("map_keys", "map_values"):
            return "Array"
        # Set builtins
        if call.name in ("set_new", "set_add", "set_remove"):
            return "Set"
        if call.name == "set_contains":
            return "Bool"
        if call.name == "set_size":
            return "Int"
        if call.name == "set_to_array":
            return "Array"
        # Decimal builtins
        if call.name in ("decimal_from_int", "decimal_from_float",
                          "decimal_add", "decimal_sub", "decimal_mul",
                          "decimal_neg", "decimal_round", "decimal_abs"):
            return "Decimal"
        if call.name == "decimal_from_string":
            return "Option"
        if call.name == "decimal_div":
            return "Option"
        if call.name == "decimal_to_string":
            return "String"
        if call.name == "decimal_to_float":
            return "Float64"
        if call.name == "decimal_compare":
            return "Ordering"
        if call.name == "decimal_eq":
            return "Bool"
        # Ability operations: show → String, hash → Int
        if call.name == "show":
            return "String"
        if call.name == "hash":
            return "Int"
        # Async builtins — Future<T> is transparent
        if call.name == "async" and call.args:
            inner = self._infer_fncall_vera_type(call.args[0]) \
                if isinstance(call.args[0], ast.FnCall) \
                else self._infer_vera_type(call.args[0])
            return f"Future<{inner}>" if inner else "Future"
        if call.name == "await" and call.args:
            # await(Future<T>) → T; at WASM level it's the inner type
            inner = self._infer_fncall_vera_type(call.args[0]) \
                if isinstance(call.args[0], ast.FnCall) \
                else self._infer_vera_type(call.args[0])
            # Strip the Future<...> wrapper if present
            if inner and inner.startswith("Future<") and inner.endswith(">"):
                return inner[7:-1]
            return inner
        # Numeric math builtins
        if call.name == "abs":
            return "Nat"
        if call.name in ("min", "max", "floor", "ceil", "round"):
            return "Int"
        if call.name in ("sqrt", "pow"):
            return "Float64"
        # Numeric type conversions
        if call.name == "int_to_float":
            return "Float64"
        if call.name in ("float_to_int", "nat_to_int", "byte_to_int"):
            return "Int"
        if call.name in ("int_to_nat", "int_to_byte"):
            return "Option"
        # Float64 predicates and constants
        if call.name in ("float_is_nan", "float_is_infinite"):
            return "Bool"
        if call.name in ("nan", "infinity"):
            return "Float64"
        if call.name in self._generic_fn_info:
            forall_vars, param_types = self._generic_fn_info[call.name]
            mapping: dict[str, str] = {}
            for pt, arg in zip(param_types, call.args):
                self._unify_param_arg_wasm(pt, arg, forall_vars, mapping)
            # Use the first param's type to determine return type
            # (Generic fn return type is typically a type var)
            # We need to figure out the return type from forall info
            # Actually, look at the monomorphized fn sig
            parts = []
            for tv in forall_vars:
                if tv not in mapping:  # pragma: no cover
                    return None
                parts.append(mapping[tv])
            mangled = f"{call.name}${'_'.join(parts)}"
            # Look up WASM return type and map back
            ret_wt = self._fn_ret_types.get(mangled)
            if ret_wt == "i64":
                return "Int"
            if ret_wt == "i32":
                return "Bool"
            if ret_wt == "f64":
                return "Float64"
            return None
        # Non-generic: map from WASM return type
        ret_wt = self._fn_ret_types.get(call.name)
        if ret_wt == "i64":
            return "Int"
        if ret_wt == "i32":
            return "Bool"
        if ret_wt == "f64":
            return "Float64"
        return None

    def _ctor_to_adt_name(self, ctor_name: str) -> str | None:
        """Find the ADT type name for a constructor name."""
        return self._ctor_to_adt.get(ctor_name)

    @staticmethod
    def _is_array_type_name(type_name: str) -> bool:
        """Check if a slot type name is an Array<T> type."""
        return type_name.startswith("Array<")

    @staticmethod
    def _is_pair_type_name(type_name: str) -> bool:
        """Check if a slot type name is a pair type (ptr, len).

        String and Array<T> are represented as two consecutive i32 locals.
        Bare "Array" also matches — monomorphization may produce slot
        references with type_name="Array" (no type args in the name).
        """
        return (type_name == "String"
                or type_name == "Array"
                or type_name.startswith("Array<"))

    def _infer_array_element_type(self, expr: ast.ArrayLit) -> str | None:
        """Infer the Vera element type name from an array literal."""
        if not expr.elements:
            return None
        return self._infer_vera_type(expr.elements[0])

    def _infer_index_element_type(self, expr: ast.IndexExpr) -> str | None:
        """Infer the Vera element type from an index expression's collection.

        The collection should be a slot ref like @Array<Int>.0, whose
        type_name is "Array" with type_args (NamedType("Int"),).
        Also handles chained indexing (e.g. @Array<Array<Int>>.0[0][1])
        by recursively resolving the inner collection's element type.
        """
        te = self._infer_index_element_type_expr(expr)
        return te.name if te is not None else None

    def _infer_index_element_type_expr(
        self, expr: ast.IndexExpr,
    ) -> ast.NamedType | None:
        """Get the full NamedType of the element from an IndexExpr.

        Returns the NamedType so that chained indexing can inspect
        nested type_args (e.g. Array<Array<Int>> → Array<Int> → Int).
        """
        coll = expr.collection
        if isinstance(coll, ast.SlotRef):
            if coll.type_name == "Array" and coll.type_args:
                ta = coll.type_args[0]
                if isinstance(ta, ast.NamedType):
                    return ta
        # Chained indexing: collection is itself an IndexExpr
        if isinstance(coll, ast.IndexExpr):
            inner_te = self._infer_index_element_type_expr(coll)
            if (inner_te is not None
                    and inner_te.name == "Array" and inner_te.type_args):
                ta = inner_te.type_args[0]
                if isinstance(ta, ast.NamedType):
                    return ta
        return None

    def _get_arg_type_info_wasm(
        self, expr: ast.Expr,
    ) -> tuple[str, tuple[str, ...]] | None:
        """Get (type_name, type_arg_names) for an argument expression."""
        if isinstance(expr, ast.SlotRef):
            if expr.type_args:
                arg_names = []
                for ta in expr.type_args:
                    if isinstance(ta, ast.NamedType):
                        arg_names.append(self._format_named_type(ta))
                    else:  # pragma: no cover
                        return None
                return (expr.type_name, tuple(arg_names))
            return (expr.type_name, ())
        if isinstance(expr, ast.ConstructorCall):
            # Infer from constructor args
            adt_name = self._ctor_to_adt_name(expr.name)
            if adt_name:
                arg_types = []
                for a in expr.args:
                    t = self._infer_vera_type(a)
                    if t:
                        arg_types.append(t)
                    else:  # pragma: no cover
                        return None
                return (adt_name, tuple(arg_types))
        return None

    def _infer_apply_fn_return_type(
        self, closure_arg: ast.Expr,
    ) -> str | None:
        """Infer the WASM return type for a closure application.

        Looks at the closure argument's type (via slot ref type name
        and type alias resolution) to determine the return type.

        For generic type aliases like ``OptionMapFn<Int, String>``
        (defined as ``fn(A -> B) effects(pure)``), the slot ref
        carries type_args that must be substituted into the alias
        body before inferring the WASM return type.
        """
        if isinstance(closure_arg, ast.SlotRef):
            type_name = closure_arg.type_name
            # Check if this is a type alias for a function type
            alias_te = self._type_aliases.get(type_name)
            if isinstance(alias_te, ast.FnType):
                # Handle generic type aliases: substitute type_args
                alias_params = self._type_alias_params.get(type_name)
                if (
                    alias_params
                    and closure_arg.type_args
                    and len(alias_params) == len(closure_arg.type_args)
                ):
                    return self._resolve_generic_fn_return(
                        alias_te, alias_params, closure_arg.type_args,
                    )
                return self._fn_type_return_wasm(alias_te)
        return "i64"  # pragma: no cover — safe default for most cases

    def _resolve_generic_fn_return(
        self,
        fn_type: ast.FnType,
        alias_params: tuple[str, ...],
        type_args: tuple[ast.TypeExpr, ...],
    ) -> str | None:
        """Resolve the return type of a generic FnType alias.

        Builds a substitution map from alias type params to concrete
        type args, then resolves the return type to a WASM type.
        """
        # Build substitution: param_name -> concrete NamedType name
        subst: dict[str, str] = {}
        for param, arg in zip(alias_params, type_args):
            if isinstance(arg, ast.NamedType):
                subst[param] = arg.name

        ret = fn_type.return_type
        if isinstance(ret, ast.NamedType):
            # If the return type is a type variable, substitute it
            name = subst.get(ret.name, ret.name)
            return self._named_type_to_wasm(name)
        return "i64"  # pragma: no cover — default

    @staticmethod
    def _named_type_to_wasm(name: str) -> str | None:
        """Map a concrete type name to its WASM representation."""
        if name in ("Int", "Nat"):
            return "i64"
        if name == "Float64":
            return "f64"
        if name == "Bool":
            return "i32"
        if name == "Unit":
            return None
        return "i32"  # ADT or other pointer type

    def _fn_type_return_wasm(self, fn_type: ast.FnType) -> str | None:
        """Get the WASM return type from a FnType AST node."""
        ret = fn_type.return_type
        if isinstance(ret, ast.NamedType):
            return self._named_type_to_wasm(ret.name)
        return "i64"  # pragma: no cover — default

    def _fn_type_param_wasm_types(
        self, fn_type: ast.FnType,
    ) -> list[str]:
        """Get WASM parameter types from a FnType AST node."""
        types: list[str] = []
        for p in fn_type.params:
            if isinstance(p, ast.NamedType):
                name = p.name
                if name in ("Int", "Nat"):
                    types.append("i64")
                elif name == "Float64":
                    types.append("f64")
                elif name == "Bool":
                    types.append("i32")
                elif name == "Unit":
                    pass  # skip Unit params
                else:
                    types.append("i32")  # ADT pointer
            else:  # pragma: no cover
                types.append("i64")  # default
        return types

    def _type_expr_name(self, te: ast.TypeExpr) -> str | None:
        """Extract a simple type name from a TypeExpr."""
        if isinstance(te, ast.NamedType):
            if te.type_args:
                arg_names = []
                for a in te.type_args:
                    if isinstance(a, ast.NamedType):
                        arg_names.append(a.name)
                    else:  # pragma: no cover
                        return None
                return f"{te.name}<{', '.join(arg_names)}>"
            return te.name
        if isinstance(te, ast.RefinementType):
            return self._type_expr_name(te.base_type)
        return None  # pragma: no cover

    def _type_name_to_wasm(self, type_name: str) -> str:
        """Map a Vera type name string to a WASM type string."""
        if type_name in ("Int", "Nat"):
            return "i64"
        if type_name == "Float64":
            return "f64"
        if type_name in ("Bool", "Byte"):
            return "i32"
        if type_name == "Unit":  # pragma: no cover
            return "i32"  # shouldn't appear, safe fallback
        # ADT or function type alias → i32 pointer
        return "i32"

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str | None:
        """Extract the slot name from a type expression."""
        if isinstance(te, ast.NamedType):
            if te.type_args:
                arg_names = []
                for a in te.type_args:
                    if isinstance(a, ast.NamedType):
                        arg_names.append(a.name)
                    else:  # pragma: no cover
                        return None
                return f"{te.name}<{', '.join(arg_names)}>"
            return te.name
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_slot_name(te.base_type)
        return None  # pragma: no cover

    def _resolve_base_type_name(self, name: str) -> str:
        """Resolve a type alias to its base type name.

        Follows alias chains through refinement types to the underlying
        primitive or ADT name.  E.g. "PosInt" -> "Int".
        """
        if name not in self._type_aliases:
            return name
        alias = self._type_aliases[name]
        if isinstance(alias, ast.RefinementType):
            if isinstance(alias.base_type, ast.NamedType):
                return self._resolve_base_type_name(alias.base_type.name)
        if isinstance(alias, ast.NamedType):
            return self._resolve_base_type_name(alias.name)
        return name

    def _slot_name_to_wasm_type(self, name: str) -> str | None:
        """Map a slot type name to a WAT type string."""
        name = self._resolve_base_type_name(name)
        if name in ("Int", "Nat"):
            return "i64"
        if name == "Float64":
            return "f64"
        if name in ("Bool", "Byte"):
            return "i32"
        # Future<T> is WASM-transparent — same representation as T
        if name.startswith("Future<") and name.endswith(">"):
            inner = name[7:-1]
            return self._slot_name_to_wasm_type(inner)
        # Map/Set/Decimal are opaque host-import handles (i32)
        if name.startswith("Map<") or name.startswith("Set<") or name == "Decimal":
            return "i32"
        # ADT types are heap pointers
        base = name.split("<")[0] if "<" in name else name
        if base in self._adt_type_names:
            return "i32"
        # Function type aliases are closure pointers (i32)
        if name in self._type_aliases:
            alias_te = self._type_aliases[name]
            if isinstance(alias_te, ast.FnType):
                return "i32"
        # Bare "Fn" for anonymous function types
        if name == "Fn":
            return "i32"
        return None
