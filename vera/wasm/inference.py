"""Type inference and utility mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import _element_wasm_type


def substitute_type_vars(
    te: ast.TypeExpr,
    subst: dict[str, ast.TypeExpr],
) -> ast.TypeExpr:
    """Substitute type variables inside a TypeExpr.

    Module-level so it's accessible from `InferenceMixin`
    (`vera/wasm/inference.py` — the canonicaliser, called from
    interpolation/apply_fn inference), `CodeGenerator`
    (`vera/codegen/core.py` — the compilability check
    `_type_expr_to_wasm_type`), and the parameterised-FnType-alias
    resolver in `MonomorphizationMixin._resolve_arg_fn_shape` /
    `CallsMixin._resolve_arg_fn_shape_wasm` (#604 / #659 CR-4 +
    CR-5).  All sites need the same substitution semantics when
    following a parameterised alias (`type Box<T> = Array<T>`,
    `type Mapper<T> = fn(T -> T)`) so the alias's own type-param
    references in the body get bound to the concrete type arguments
    from the call site (#635 closes the compilability-side gap that
    PR #631's walker fix didn't reach).

    A "type variable reference" is a bare `NamedType(name=X,
    type_args=None|())` whose name is a key in `subst`; it gets
    replaced wholesale by `subst[X]`.  `NamedType` with non-bare
    type_args is recursed into (substituting in each arg).
    `RefinementType` substitutes its `base_type`; the `predicate`
    is left untouched (predicates are `Expr`, not `TypeExpr`, and
    canonicalisation is type-level only).  `FnType` substitutes
    through each param and the return type (added by #659 CR-4 +
    CR-5 for parameterised FnType aliases).  Other shapes pass
    through unchanged.
    """
    if isinstance(te, ast.NamedType):
        if not te.type_args and te.name in subst:
            return subst[te.name]
        if te.type_args:
            new_args = tuple(
                substitute_type_vars(a, subst) for a in te.type_args
            )
            return ast.NamedType(name=te.name, type_args=new_args)
        return te
    if isinstance(te, ast.RefinementType):
        new_base = substitute_type_vars(te.base_type, subst)
        return ast.RefinementType(
            base_type=new_base, predicate=te.predicate)
    if isinstance(te, ast.FnType):
        new_params = tuple(
            substitute_type_vars(p, subst) for p in te.params
        )
        new_return = substitute_type_vars(te.return_type, subst)
        # `effect` is passed through unchanged.  All current
        # parameterised FnType aliases use `effects(pure)` or
        # similarly-monomorphic effects.  If a future type
        # introduces `effects(<State<T>>)` or similar where `T`
        # is an alias parameter, the substitution would NOT
        # propagate into the effect row — this is a deliberate
        # gap noted in the #659 review (type-design analyzer
        # finding 3).  The corresponding regression test in
        # `tests/test_wasm.py::TestSubstituteTypeVarsFnType`
        # pins this contract so a future refactor doesn't
        # silently change behaviour.
        return ast.FnType(
            params=new_params,
            return_type=new_return,
            effect=te.effect,
        )
    return te


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
    - _is_pair_type_name
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

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.)
        #
        # Handled (explicit isinstance branch):
        #   IntLit            → "i64"
        #   FloatLit          → "f64"
        #   BoolLit           → "i32"
        #   UnitLit           → None
        #   StringLit         → "i32_pair"
        #   InterpolatedString → "i32_pair"
        #   SlotRef           → from resolved type name
        #   ResultRef         → from declared @Type
        #   BinaryExpr        → from op + operands (arith/cmp/logic)
        #   UnaryExpr         → from op + operand (neg/not)
        #   FnCall            → from `_infer_fncall_wasm_type`
        #   QualifiedCall     → from `_infer_qualified_call_wasm_type`
        #   ConstructorCall   → "i32" (heap ptr) if known
        #   NullaryConstructor → "i32" (heap ptr) if known
        #   MatchExpr         → from first arm body
        #   IfExpr            → from then-branch
        #   Block             → from trailing expr
        #   HandleExpr        → from body
        #   IndexExpr         → from element type
        #   ArrayLit          → "i32_pair"
        #   ForallExpr        → "i32" (Bool)
        #   ExistsExpr        → "i32" (Bool)
        #   AssertExpr        → None (Unit)
        #   AssumeExpr        → None (Unit)
        #   AnonFn            → "i32" (closure ptr — defensive add #597)
        #   ModuleCall        → from `_infer_fncall_wasm_type` shape
        #                       (defensive add #597; today the type
        #                       checker resolves ModuleCalls to
        #                       FnCalls before this helper runs, but
        #                       a regression there would un-mask the
        #                       gap)
        #
        # Cannot occur (rejected before reaching this codegen-time
        # helper):
        #   HoleExpr          → parser placeholder; check time rejects
        #   OldExpr           → contract-only; not in body codegen
        #   NewExpr           → contract-only; not in body codegen
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
        # Defensive add (#597): AnonFn literals are typically lifted
        # before reaching this helper, but if one does flow here it
        # represents a closure handle on the WASM stack (i32 ptr).
        if isinstance(expr, ast.AnonFn):
            return "i32"
        # Defensive add (#597): ModuleCall resolves to a FnCall on
        # the imported target.  If a regression lands a ModuleCall
        # at this helper, look up the imported fn's return type via
        # the FnCall machinery (which already handles module-qualified
        # names).  Wrapping in a fake FnCall preserves the dispatch.
        if isinstance(expr, ast.ModuleCall):
            return self._infer_fncall_wasm_type(
                ast.FnCall(name=expr.name, args=expr.args)
            )
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
        # User-defined effect ops (e.g. Exn.throw, State.get/put)
        if expr.name in self._effect_ops:
            target_name, is_void = self._effect_ops[expr.name]
            if expr.name == "throw" or is_void:
                return None  # throw → Never; void ops return no value
            return self._fn_ret_types.get(target_name)
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
        # Array utilities (#466 phase 1):
        # array_mapi / array_reverse / array_flatten / array_sort_by
        # → Array<T> (i32_pair). array_find → Option<T> (i32 pointer).
        # array_any / array_all → Bool (i32).
        if expr.name in (
            "array_mapi", "array_reverse", "array_flatten", "array_sort_by",
        ):
            return "i32_pair"
        if expr.name == "array_find":
            return "i32"
        if expr.name in ("array_any", "array_all"):
            return "i32"
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
        # String utility built-ins (#470).  string_chars / lines /
        # words return Array<String> (i32_pair); pad / reverse /
        # trim_start / trim_end return String (i32_pair).
        if expr.name in (
            "string_chars", "string_lines", "string_words",
            "string_pad_start", "string_pad_end",
            "string_reverse", "string_trim_start", "string_trim_end",
        ):
            return "i32_pair"
        # Character classification (#471) → Bool (i32).
        if expr.name in (
            "is_digit", "is_alpha", "is_alphanumeric",
            "is_whitespace", "is_upper", "is_lower",
        ):
            return "i32"
        # Single-character case conversion (#471) → String (i32_pair).
        if expr.name in ("char_to_upper", "char_to_lower"):
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
        # Math builtins (#467).  Log/trig/constants all return
        # Float64.  sign returns Int (i64); clamp returns Int;
        # float_clamp returns Float64.
        if expr.name in (
            "log", "log2", "log10",
            "sin", "cos", "tan", "asin", "acos", "atan", "atan2",
            "pi", "e", "float_clamp",
        ):
            return "f64"
        if expr.name in ("sign", "clamp"):
            return "i64"
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

    def _canonical_named_type(
        self,
        te: ast.TypeExpr,
        alias_map: dict[str, ast.TypeExpr] | None = None,
    ) -> ast.NamedType | None:
        """Walk a TypeExpr to its canonical `NamedType` form.

        The single canonicalisation walker that consolidates the
        `RefinementType` unwrap + alias-chain follow + generic
        substitution shape replicated across many sites in this
        module pre-#630.  Each ad-hoc walk handled a subset of the
        concerns and missed the rest, accumulating ten distinct
        triggers of the #602 i32_pair-into-i64 mismatch bug class
        across `f()` baseline, type aliases over String, single
        and nested `RefinementType` returns, refinement-over-alias,
        `apply_fn` over `FnType`-aliased / nested-refinement /
        inline-`AnonFn` arguments, and the parallel
        `IndexExpr`-of-`FnCall` path.  See [#630] for the full
        narrative.

        Iteratively (until fixed point or cycle):

        1. Unwraps `RefinementType` layers (any nesting depth).
        2. If `alias_map` is provided and the current `NamedType`'s
           name is in the map, substitutes the mapped type and
           re-loops.  (Used by generic FnType-alias resolution where
           the alias's type params bind concrete types from the
           call site.)
        3. Follows `NamedType` alias chains via `self._type_aliases`
           one step per outer iteration, so any `RefinementType`
           wrapping the alias body is unwrapped on the next
           iteration.

        Returns the final `NamedType` — with `type_args` taken from
        the **terminal** `NamedType` reached during the walk — or
        `None` if the walk terminates at a non-`NamedType` (`FnType`,
        refinement-over-non-`NamedType` base, alias body that is
        itself a `FnType`, etc.).

        Type-args follow the *terminal* `NamedType` so that an alias
        whose body carries type_args propagates them through.
        Concrete cases:

          - `type IntList = Array<Int>` resolves
            `NamedType("IntList")` to `NamedType("Array", [Int])` —
            the alias body's `type_args` are preserved.
          - `alias_map["T"] = NamedType("Array", [Int])` resolves
            `NamedType("T")` to `NamedType("Array", [Int])` — the
            substituted type's `type_args` are preserved.
          - `type Str = String` resolves `NamedType("Str")` to
            `NamedType("String")` — neither has `type_args`,
            unchanged.

        Edge case: the outermost `NamedType` may carry `type_args`
        that the alias body discards (e.g. `NamedType("Box", [Int])`
        with a non-parameterised `type Box = Holder`).  Since
        non-parameterised aliases applied with type_args are
        ill-formed at the type-check level, we accept this
        information loss; parameterised-alias substitution proper
        (where `type Box<T> = Holder<T>` would push the outer `T`
        into the resolved body via per-alias type-param binding)
        is **out of scope** for #630 and remains a separate latent
        gap.
        """
        seen: set[str] = set()
        while True:
            # Unwrap RefinementType layers — any nesting depth.
            while isinstance(te, ast.RefinementType):
                te = te.base_type
            if not isinstance(te, ast.NamedType):
                return None
            # Unified cycle guard for both `alias_map` substitution
            # and `_type_aliases` chain following.  Without this, an
            # alias_map self-reference (`{T: NamedType("T")}`) or a
            # cyclic chain through a mix of substitutions and follows
            # would loop forever.
            if te.name in seen:
                break
            seen.add(te.name)
            # alias_map substitution (generic type-param binding).
            # Checked before alias-chain follow so generic params
            # take precedence over any same-named type alias.
            if alias_map is not None and te.name in alias_map:
                te = alias_map[te.name]
                continue
            # Follow NamedType alias chain — one step per iteration so
            # any RefinementType wrapping the alias body is unwrapped
            # on the next pass.  When the alias is parameterised
            # (`type Box<T> = Array<T>` etc.), substitute the alias's
            # type params with the concrete `te.type_args` *before*
            # continuing — otherwise the alias body's type variables
            # leak into the returned NamedType.
            alias = self._type_aliases.get(te.name)
            if alias is None:
                break
            if isinstance(alias, (ast.NamedType, ast.RefinementType)):
                alias_params = self._type_alias_params.get(te.name)
                if (alias_params and te.type_args
                        and len(alias_params) == len(te.type_args)):
                    local_subst = dict(zip(alias_params, te.type_args))
                    alias = self._substitute_type_vars(alias, local_subst)
                te = alias
                continue
            # FnType-bodied alias or other non-resolvable shape.
            return None
        # `te` is the terminal NamedType; preserve its type_args.
        return ast.NamedType(name=te.name, type_args=te.type_args)

    def _substitute_type_vars(
        self,
        te: ast.TypeExpr,
        subst: dict[str, ast.TypeExpr],
    ) -> ast.TypeExpr:
        """Instance-method wrapper around the module-level
        `substitute_type_vars` so existing call sites on
        `InferenceMixin` keep working.  See the free function for
        full documentation of the substitution contract.
        """
        return substitute_type_vars(te, subst)

    def _canonical_wasm_type(
        self,
        te: ast.TypeExpr,
        alias_map: dict[str, ast.TypeExpr] | None = None,
    ) -> str | None:
        """Walk a TypeExpr to its canonical WASM-type string.

        Same walk as `_canonical_named_type` but maps the resolved
        name to the WASM representation:

          - `"i32_pair"` for `String` / `Array` (two-i32 layout).
          - `"i64"` for `Int` / `Nat`.
          - `"f64"` for `Float64`.
          - `"i32"` for `Bool` / `Byte` / ADTs / pointer types.
          - `None` for `Unit` (no WASM representation — caller
            usually omits the result clause entirely).
          - `"i64"` as the safe default when the walker can't reach
            a `NamedType` (matches the pre-#630 fallthroughs at
            every WASM-type-walk site).

        Note that the `Unit → None` and `unreachable-NamedType →
        "i64"` cases are intentionally distinct: `None` says "no
        WASM type, omit the slot"; `"i64"` says "we couldn't infer,
        default to the i64 word size".  Callers handling `None` for
        Unit must not conflate the two.

        `Future<T>` is treated as transparent (same WASM
        representation as `T`), parallel to `_slot_name_to_wasm_type`'s
        `Future<...>` strip-and-recurse handling.  Without this, a
        `Future<String>` return at an `apply_fn` / FnType-alias
        position would canonicalise to `NamedType("Future", [String])`
        and `_named_type_to_wasm("Future")` would default to `"i32"`
        — producing a `call_indirect` sig mismatch against the
        actual `i32_pair` emit.
        """
        canonical = self._canonical_named_type(te, alias_map)
        if canonical is None:
            # Walker bailed without reaching a NamedType.  The most
            # common reachable case is a `FnType` (or an alias chain
            # terminating in `FnType`) at a closure-pointer return
            # position — e.g. `type Outer = fn(Int -> Inner)
            # effects(pure)` where `Inner` is itself a `FnType`
            # alias.  Higher-order returns must use the `i32`
            # closure-pointer ABI; defaulting to `"i64"` mismatches
            # the call_indirect sig vs the actual emit and traps at
            # WASM validation.  Symmetric to the explicit FnType
            # branch in `_type_expr_to_wasm_type` (codegen/core.py).
            if self._reaches_fn_type(te, alias_map):
                return "i32"
            return "i64"
        # Future<T> is transparent — recurse on the inner type.
        if (canonical.name == "Future" and canonical.type_args
                and len(canonical.type_args) == 1):
            return self._canonical_wasm_type(
                canonical.type_args[0], alias_map)
        if canonical.name in ("String", "Array"):
            return "i32_pair"
        return self._named_type_to_wasm(canonical.name)

    def _reaches_fn_type(
        self,
        te: ast.TypeExpr,
        alias_map: dict[str, ast.TypeExpr] | None = None,
    ) -> bool:
        """True if walking `te` through `RefinementType` /
        `alias_map` / `_type_aliases` lands on a `FnType`.

        Used by `_canonical_wasm_type` to distinguish the
        FnType-return case (closure-pointer ABI, `"i32"`) from
        other walker-bail cases (default `"i64"`).  Mirrors the
        traversal logic in `_canonical_named_type` but with a
        different terminal classification — needed because the
        walker collapses both terminal kinds into `None` for the
        NamedType-returning contract, losing the FnType signal.
        """
        seen: set[str] = set()
        while True:
            while isinstance(te, ast.RefinementType):
                te = te.base_type
            if isinstance(te, ast.FnType):
                return True
            if not isinstance(te, ast.NamedType):
                return False
            if te.name in seen:
                return False
            seen.add(te.name)
            if alias_map is not None and te.name in alias_map:
                te = alias_map[te.name]
                continue
            alias = self._type_aliases.get(te.name)
            if alias is None:
                return False
            if isinstance(alias, ast.FnType):
                return True
            if isinstance(alias, (ast.NamedType, ast.RefinementType)):
                te = alias
                continue
            return False

    def _format_named_type_canonical(self, te: ast.NamedType) -> str:
        """Format a NamedType to its canonical Vera-type-name string.

        Resolves the outer name through the type alias chain (and
        any `RefinementType` wrappers along the way) via
        `_canonical_named_type`, then formats the result with the
        terminal `type_args`.  Examples:

          - `NamedType("Str")` where `type Str = String` → `"String"`
          - `NamedType("IntList")` where `type IntList = Array<Int>`
            → `"Array<Int>"` — the terminal type's args propagate.
          - `NamedType("PosInt")` where `type PosInt = { @Int | p }`
            → `"Int"`

        If the walk can't reach a `NamedType` (e.g. terminates at a
        `FnType`-bodied alias), falls back to `_format_named_type(te)`
        — bare-name format without resolution.  This is a deliberate
        post-#630 simplification: the pre-#630 fallback resolved the
        outer name via `_resolve_base_type_name` and formatted with
        the outer `type_args`, but that path is unreachable when the
        canonical walker returns None (the walker covers every shape
        the old fallback did and more), so the unresolved
        `_format_named_type` fallback is structurally adequate.
        """
        canonical = self._canonical_named_type(te)
        if canonical is None:
            return self._format_named_type(te)
        return self._format_named_type(canonical)

    def _infer_vera_type(self, expr: ast.Expr) -> str | None:
        """Infer the Vera type name of an expression for call rewriting.

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.)
        #
        # Handled (explicit isinstance branch):
        #   IntLit            → "Int"
        #   BoolLit           → "Bool"
        #   FloatLit          → "Float64"
        #   UnitLit           → "Unit"
        #   StringLit         → "String"
        #   InterpolatedString → "String"
        #   SlotRef           → slot type name (with type-args)
        #   ConstructorCall   → parent ADT name
        #   NullaryConstructor → parent ADT name
        #   BinaryExpr        → "Bool" for cmp/logic, else left's type
        #   UnaryExpr         → "Bool" for `not`, else operand's type
        #   FnCall            → from `_infer_fncall_vera_type`
        #   ArrayLit          → "Array"
        #   IndexExpr         → element type
        #   IfExpr            → from then-branch
        #   Block             → from trailing expr (defensive add #597)
        #   MatchExpr         → from first arm body (defensive add #597)
        #   HandleExpr        → from body (defensive add #597)
        #   AssertExpr        → "Unit" (defensive add #597)
        #   AssumeExpr        → "Unit" (defensive add #597)
        #   AnonFn            → "Fn" (defensive add #597 — closure
        #                       handle's Vera type isn't typically
        #                       needed for call rewriting, but a
        #                       placeholder beats `None`)
        #   QualifiedCall     → from `_infer_fncall_vera_type`
        #                       (defensive add #597)
        #   ModuleCall        → from `_infer_fncall_vera_type`
        #                       (defensive add #597)
        #
        # Cannot occur (contract-only or check-time rejected):
        #   ResultRef         → only valid in `ensures`; not at call site
        #   OldExpr           → contract-only
        #   NewExpr           → contract-only
        #   ForallExpr        → contract-only quantifier
        #   ExistsExpr        → contract-only quantifier
        #   HoleExpr          → parser placeholder, check time rejects
        """
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
        # Defensive adds (#597) — these compound expressions could
        # flow in here from generic-arg inference paths, but today
        # most callers preprocess first.  Returning the right Vera
        # type instead of None hardens against a future caller
        # extending the surface.
        if isinstance(expr, ast.Block):
            return (self._infer_vera_type(expr.expr)
                    if expr.expr is not None else None)
        if isinstance(expr, ast.MatchExpr):
            if expr.arms:
                return self._infer_vera_type(expr.arms[0].body)
            return None
        if isinstance(expr, ast.HandleExpr):
            if expr.body.expr is not None:
                return self._infer_vera_type(expr.body.expr)
            return None
        if isinstance(expr, (ast.AssertExpr, ast.AssumeExpr)):
            return "Unit"
        if isinstance(expr, ast.AnonFn):
            return "Fn"  # closure handle — placeholder for any
            # downstream code that just needs to know it's a fn-typed
            # arg; the precise FnType shape isn't needed here.
        if isinstance(expr, (ast.QualifiedCall, ast.ModuleCall)):
            # Treat as a FnCall lookup; reuses the existing dispatch.
            return self._infer_fncall_vera_type(
                ast.FnCall(name=expr.name, args=expr.args)
            )
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
        # Array utilities (#466 phase 1).
        if call.name in (
            "array_mapi", "array_reverse", "array_flatten", "array_sort_by",
        ):
            return "Array"
        if call.name == "array_find":
            return "Option"
        if call.name in ("array_any", "array_all"):
            return "Bool"
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
        # String utility built-ins (#470).
        if call.name in (
            "string_pad_start", "string_pad_end",
            "string_reverse", "string_trim_start", "string_trim_end",
            "char_to_upper", "char_to_lower",
        ):
            return "String"
        if call.name in ("string_chars", "string_lines", "string_words"):
            return "Array"
        # Character classification (#471) → Bool.
        if call.name in (
            "is_digit", "is_alpha", "is_alphanumeric",
            "is_whitespace", "is_upper", "is_lower",
        ):
            return "Bool"
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
        # apply_fn(closure, args...) — infer from closure's return type.
        #
        # Post-#630: both `SlotRef` (let-bound closure ref into a
        # `FnType` type alias) and `AnonFn` (inline closure literal)
        # paths feed into the centralised `_canonical_named_type`
        # walker.  Pre-#630 each shape had its own ad-hoc walk with
        # subset-of-the-concerns coverage — accounting for triggers
        # 7 (SlotRef + nested-RefinementType return), 8 (SlotRef +
        # `FnType`-aliased-String return), 9 (AnonFn + plain return),
        # and 10 (AnonFn + nested-RefinementType return) of the #602
        # bug class.  Future closure-arg shapes (e.g. a `FnCall`
        # returning a closure) can plug into the same walker call
        # by adding an `elif` that extracts `ret_te` and reuses the
        # canonicalisation below — no per-shape canonicalisation
        # logic needed.  Shapes without a single `return_type` field
        # (`IfExpr` between two closures with the same Vera-level
        # type, `MatchExpr` arms, etc.) need a unifying step that's
        # genuinely additional dispatch work, not "plug-in".
        if call.name == "apply_fn" and call.args:
            closure_arg = call.args[0]
            ret_te: ast.TypeExpr | None = None
            alias_map: dict[str, ast.TypeExpr] | None = None
            if isinstance(closure_arg, ast.SlotRef):
                alias_te = self._type_aliases.get(closure_arg.type_name)
                if isinstance(alias_te, ast.FnType):
                    ret_te = alias_te.return_type
                    alias_params = self._type_alias_params.get(
                        closure_arg.type_name)
                    if (alias_params and closure_arg.type_args
                            and len(alias_params)
                            == len(closure_arg.type_args)):
                        alias_map = dict(zip(
                            alias_params, closure_arg.type_args))
            elif isinstance(closure_arg, ast.AnonFn):
                ret_te = closure_arg.return_type
            if ret_te is not None:
                canonical = self._canonical_named_type(ret_te, alias_map)
                if canonical is not None:
                    return self._format_named_type(canonical)
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
        # Math builtins (#467) — mirror the WASM-type branches
        # above so Vera-level type inference also handles these.
        # Without these, code that nests a math call inside an
        # expression whose Vera type is needed upstream (e.g.
        # generics inference, `show`, `hash`) falls back to None
        # and triggers mis-compiles.
        if call.name in (
            "log", "log2", "log10",
            "sin", "cos", "tan", "asin", "acos", "atan", "atan2",
            "pi", "e", "float_clamp",
        ):
            return "Float64"
        if call.name in ("sign", "clamp"):
            return "Int"
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
            # Mirror the non-generic `i32_pair` branch below: a
            # monomorphised generic fn returning `String` or `Array<T>`
            # has the same disambiguation need.  Without this, a
            # `forall<T> fn id(@T -> @T)` instantiated at `String` and
            # called inside interpolation would still fall through to
            # `to_string(...)` — same #602 failure mode in a different
            # call shape.  `_register_fn` populates `_fn_ret_type_exprs`
            # for monomorphised names too (`codegen/core.py:333`).  Currently
            # latent — generic instantiation over `String` is blocked
            # upstream by the bare-type-var-param lowering gap (same
            # class as #604) — but kept symmetric with the non-generic
            # branch so the fix lands automatically when that gap closes.
            if ret_wt == "i32_pair":
                resolved = self._resolve_i32_pair_ret_te(
                    self._fn_ret_type_exprs.get(mangled),
                )
                if resolved is not None:
                    return resolved
            return None
        # Non-generic: map from WASM return type
        ret_wt = self._fn_ret_types.get(call.name)
        if ret_wt == "i64":
            return "Int"
        if ret_wt == "i32":
            return "Bool"
        if ret_wt == "f64":
            return "Float64"
        # i32_pair → String or Array.  WAT type alone can't
        # disambiguate, so consult the full Vera return-type registry
        # populated by `_register_fn` (see #614 — same registry, same
        # pattern).  Without this branch, a user fn returning `String`
        # was mapped to `None` here, which made
        # `_translate_interpolated_string` fall through to the
        # `to_string(...)` fallback wrapper.  `to_string` reads its
        # arg as an `i64`, but the FnCall pushed `i32_pair` — hence
        # the `expected i64, found i32` trap at WASM validation
        # (#602).  Same inference gap that #614 exposed for the
        # *element-type* of an indexed FnCall result; this is the
        # *return-type* inference half.
        if ret_wt == "i32_pair":
            resolved = self._resolve_i32_pair_ret_te(
                self._fn_ret_type_exprs.get(call.name),
            )
            if resolved is not None:
                return resolved
        return None

    def _resolve_i32_pair_ret_te(
        self, ret_te: ast.TypeExpr | None,
    ) -> str | None:
        """Canonicalise a fn's return TypeExpr for `i32_pair` lookup.

        Several shapes can appear at user-fn return positions for
        `String` / `Array<T>` (i32_pair) returns:

          - `NamedType("String")` — bare type, common case.
          - `NamedType("MyAlias")` where the alias resolves to String —
            `_resolve_base_type_name` follows the chain to `"String"`.
          - `RefinementType(base_type=NamedType("String"), ...)` — the
            inline `@{ @String | predicate }` form.  `_register_fn`
            stores the literal AST, so the registry holds a
            `RefinementType` directly.
          - **Nested refinements** (`@{ @{ @String | p1 } | p2 }`) —
            the grammar admits `refinement_type` over any `type_expr`,
            so refinements can wrap refinements.  Empirically reachable
            via valid Vera (the type checker accepts the nested form
            at fn return positions).  The unwrap below loops to handle
            arbitrary nesting depth.

        Without unwrapping these shapes, a fn declared with any of the
        wrapper forms reproduces the original #602 trap inside
        interpolation — `_fn_ret_type_exprs.get(name)` returns the
        un-canonical AST, the downstream consumer's `vera_type ==
        "String"` check fails, and `_translate_interpolated_string`
        falls through to `to_string(...)` over an `i32_pair` value
        (`expected i64, found i32` at WASM validation).

        See [#626](https://github.com/aallan/vera/issues/626) — every
        `return None` here is an instance of the broader silent-skip
        pattern.  The downstream `to_string` fallback at
        `vera/wasm/operators.py` carries the matching commentary.

        Returns the canonical Vera type name (`"String"` / `"Array"` /
        etc.), or None for shapes the unwrap can't reduce to a
        `NamedType` (e.g. `FnType`, or a `RefinementType` whose
        innermost base is non-`NamedType`).  None-returns are
        currently triggered for cross-module imports too (the
        registry isn't populated cross-module — see #628).

        Post-#630: thin delegate over `_canonical_named_type`, the
        single canonicalisation walker.  The bare-name return
        (without `type_args`) matches both consumers' expectations
        — they compare against `"String"` / `"Array"` and ignore
        parameterisation.
        """
        if ret_te is None:
            return None
        canonical = self._canonical_named_type(ret_te)
        return canonical.name if canonical is not None else None

    def _ctor_to_adt_name(self, ctor_name: str) -> str | None:
        """Find the ADT type name for a constructor name."""
        return self._ctor_to_adt.get(ctor_name)

    @staticmethod
    def _is_array_type_name(type_name: str) -> bool:
        """Check if a slot type name is an Array<T> type."""
        return type_name.startswith("Array<")

    def _is_pair_type_name(self, type_name: str) -> bool:
        """Check if a slot type name is a pair type (ptr, len).

        String and Array<T> are represented as two consecutive i32 locals.
        Bare "Array" also matches — monomorphization may produce slot
        references with type_name="Array" (no type args in the name).

        Resolves type aliases first so `type Row = Array<Bool>` compiles
        identically to writing `Array<Bool>` directly: a SlotRef with
        type_name "Row" must emit `(local.get ptr; local.get len)` like
        any other Array slot, not just the ptr (#583).
        """
        resolved = self._resolve_base_type_name(type_name)
        return (resolved == "String"
                or resolved == "Array"
                or resolved.startswith("Array<"))

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
        Type aliases on the collection (`type Row = Array<Bool>`) are
        followed to their underlying Array<...> definition before
        extracting the element type — without this, indexing through
        an aliased slot like `@Row.0[1]` silently fails with E602 (#583).
        """
        coll = expr.collection
        if isinstance(coll, ast.SlotRef):
            ta_te = self._alias_array_element(coll.type_name, coll.type_args)
            if ta_te is not None:
                return ta_te
        # Chained indexing: collection is itself an IndexExpr
        if isinstance(coll, ast.IndexExpr):
            inner_te = self._infer_index_element_type_expr(coll)
            if (inner_te is not None
                    and inner_te.name == "Array" and inner_te.type_args):
                ta = inner_te.type_args[0]
                if isinstance(ta, ast.NamedType):
                    return ta
        # FnCall returning Array<T>: e.g. `s_arr(x)[i]`.  Pre-fix this
        # branch was missing — collection-is-a-call fell through to
        # `return None` below, `_translate_index_expr` then returned
        # None, and the enclosing function (or closure) was dropped
        # from the WAT output.  At top level this surfaced as the #604-
        # class "function body contains unsupported expressions —
        # skipped" warning; inside a closure body the registered
        # closure_id was never added to the function table, so the
        # `call_indirect` at the use site referenced a missing entry
        # and WASM validation rejected the module with "unknown table 0:
        # table index out of bounds" (#614).
        if isinstance(coll, ast.FnCall):
            ret_te = self._fn_ret_type_exprs.get(coll.name)
            # Walk RefinementType layers to a base NamedType so that
            # inline-refinement return types — both single-layer
            # `@{ @Array<Int> | predicate }` and nested
            # `@{ @{ @Array<Int> | p1 } | p2 }` — resolve the same as
            # a plain `@Array<Int>` return.  Without this, an
            # IndexExpr-of-FnCall against a refinement-returning fn
            # silently failed inference, the enclosing function got
            # dropped, and the symptom matched the original #614 bug.
            #
            # Post-#630: delegated to `_canonical_named_type`, which
            # gives back the canonical `NamedType` (with type_args
            # preserved) so we can feed `_alias_array_element` —
            # that helper inspects `.type_args` on the NamedType.
            canonical = self._canonical_named_type(ret_te)
            if canonical is not None:
                ta_te = self._alias_array_element(
                    canonical.name, canonical.type_args)
                if ta_te is not None:
                    return ta_te
        return None

    def _alias_array_element(
        self,
        type_name: str,
        type_args: tuple[ast.TypeExpr, ...] | None,
    ) -> ast.NamedType | None:
        """If (type_name, type_args) names an Array<T> (possibly via alias
        or refinement-of-alias), return T as a *canonical* NamedType —
        i.e. with any alias chain on the element type itself fully
        resolved.  Returns None otherwise.

        Canonicalisation on the returned element type matters for
        nested aliases (#559).  Example: ``type Row = Array<Int>;
        type Grid = Array<Row>`` — without canonicalisation, indexing
        ``@Grid.0[0]`` returns ``NamedType("Row")``.  The chained-
        indexing branch in ``_infer_index_element_type_expr`` then
        checks ``inner_te.name == "Array"`` and fails (it's
        ``"Row"``), so ``@Grid.0[0][1]`` falls back to ``None``.
        Worse, downstream element-WASM-type lookups treat the
        opaque alias name as a scalar and emit a load-as-i32 +
        ``i64.extend_i32_u`` against what is actually a heap
        pointer to an array pair, producing a stack-shape mismatch
        at WASM validation.  Returning the *canonical* element
        ensures the chained-indexing branch matches and downstream
        size lookups see the real shape.
        """
        # Direct Array<T>
        if type_name == "Array" and type_args:
            ta = type_args[0]
            if isinstance(ta, ast.NamedType):
                # #559: canonicalise the element type so nested
                # aliases (`type Row = Array<Int>` used as the
                # element of an outer `Array<Row>`) resolve through
                # the chain instead of stopping at the alias name.
                # ``_canonical_named_type`` returns ``None`` for
                # non-NamedType terminals (e.g. element is a
                # ``FnType`` — not a useful array shape today); fall
                # back to the original NamedType in that case so we
                # don't regress the pre-#559 behaviour of returning
                # *something* for a direct ``Array<T>``.
                canonical = self._canonical_named_type(ta)
                return canonical if canonical is not None else ta
            return None
        # Type alias — follow to its target.  Only handles the common case
        # of a non-generic alias pointing at a concrete Array<T>; generic
        # aliases (`type Box<T> = Array<T>`) would need substitution,
        # which we don't attempt here.
        #
        # Refinement-of-alias unwrap (#655 Shape B): if the alias target
        # is a `RefinementType` (e.g.
        # `type NonEmptyArray = { @Array<Int> | array_length(@Array<Int>.0) > 0 }`),
        # peel any `RefinementType` layers before checking whether the
        # base is a `NamedType` pointing at an array.  Without this, the
        # IndexExpr translator returns None for `@NonEmptyArray.0[0]`,
        # the enclosing function (`head`) gets dropped via [E602], and
        # the call site references a non-existent `$head` — the symptom
        # documented in #655 Shape B.
        if type_name in self._type_aliases:
            target = self._type_aliases[type_name]
            while isinstance(target, ast.RefinementType):
                target = target.base_type
            if isinstance(target, ast.NamedType):
                return self._alias_array_element(target.name, target.type_args)
        return None

    def _get_arg_type_info_wasm(
        self, expr: ast.Expr,
    ) -> tuple[str, tuple[str | None, ...]] | None:
        """Get (type_name, type_arg_names) for an argument expression.

        Type arg entries may be None for positions that cannot be inferred
        from the argument (e.g. T in Err(e) where only E is resolved).
        """
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
            # Infer from constructor args, respecting field→type-param index mapping
            # so sparse constructors like Err(e) bind to the correct ADT type param.
            adt_name = self._ctor_to_adt_name(expr.name)
            if adt_name:
                field_tp_idx = self._ctor_adt_tp_indices.get(expr.name)
                adt_tp_count = self._adt_tp_counts.get(adt_name, 0)
                if field_tp_idx is not None and adt_tp_count > 0:
                    result_tps: list[str | None] = [None] * adt_tp_count
                    for field_i, tp_idx in enumerate(field_tp_idx):
                        if tp_idx is not None and field_i < len(expr.args):
                            t = self._infer_vera_type(expr.args[field_i])
                            if t is not None:
                                result_tps[tp_idx] = t
                            # If t is None, leave position as None (unknown)
                    return (adt_name, tuple(result_tps))
                # Fall back to positional inference for unmapped constructors.
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

        Walks `closure_arg` to extract its declared return TypeExpr
        and feeds it (with any generic alias_map binding) to the
        centralised `_canonical_wasm_type` walker.  Two arg shapes
        are supported today:

          - `SlotRef` into a `FnType` type alias (let-bound closure
            ref, possibly with generic type_args bound at the call
            site like `OptionMapFn<Int, String>`).
          - `AnonFn` (inline closure literal).

        Future closure-arg shapes with a single `return_type` field
        (e.g. `FnCall` returning a closure) can be added as an extra
        `elif` that extracts `ret_te` and reuses the walker call —
        no per-shape canonicalisation logic needed.  Shapes without
        a single return type (e.g. `IfExpr` selecting between two
        closures with the same Vera-level type) need a unifying
        step that's genuinely additional dispatch work, not "plug-in".

        Defaults to `"i64"` if no return TypeExpr can be extracted.
        This default *is* reachable for unhandled shapes — the
        pre-#630 `# pragma: no cover` claim that closure returns
        weren't refinement types was disproved (#629); this method's
        own fallthrough remains reachable for any closure-arg shape
        not in the `if`/`elif` ladder.  Unlike the interpolation
        path (where #630's Tier 2 wires a specific [E615]), this
        site's fallthrough still surfaces only as a `call_indirect`
        type mismatch at WASM validation — diagnosable but not
        source-located.  Bringing this site under the same
        diagnostic discipline as Tier 2 is queued for the #626
        Layer 1 work.
        """
        ret_te: ast.TypeExpr | None = None
        alias_map: dict[str, ast.TypeExpr] | None = None
        if isinstance(closure_arg, ast.SlotRef):
            alias_te = self._type_aliases.get(closure_arg.type_name)
            if isinstance(alias_te, ast.FnType):
                ret_te = alias_te.return_type
                alias_params = self._type_alias_params.get(
                    closure_arg.type_name)
                if (alias_params and closure_arg.type_args
                        and len(alias_params)
                        == len(closure_arg.type_args)):
                    alias_map = dict(zip(
                        alias_params, closure_arg.type_args))
        elif isinstance(closure_arg, ast.AnonFn):
            ret_te = closure_arg.return_type
        if ret_te is not None:
            return self._canonical_wasm_type(ret_te, alias_map)
        return "i64"

    def _resolve_generic_fn_return(
        self,
        fn_type: ast.FnType,
        alias_params: tuple[str, ...],
        type_args: tuple[ast.TypeExpr, ...],
    ) -> str | None:
        """Resolve the return type of a generic FnType alias.

        Builds an alias_map from the FnType alias's type params to
        the concrete type args bound at the call site, then delegates
        to the centralised `_canonical_wasm_type` walker (#630).

        Pre-#630: this site re-implemented the substitute-and-resolve
        sequence ad-hoc, with a single-level RefinementType unwrap
        and a string→string substitution dict.  That worked for the
        bare-NamedType type-arg case but missed RefinementType-wrapped
        type args; the centralised walker handles both uniformly.
        """
        alias_map = dict(zip(alias_params, type_args))
        return self._canonical_wasm_type(fn_type.return_type, alias_map)

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
        """Get the WASM return type from a FnType AST node.

        Post-#630: thin delegate over `_canonical_wasm_type`.  The
        pre-#630 ad-hoc `while`-loop + alias-resolve + i32_pair
        check has been folded into the centralised walker; see its
        docstring for the full canonicalisation contract.
        """
        return self._canonical_wasm_type(fn_type.return_type)

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

    def _resolve_base_type_name(
        self,
        name: str,
        _seen: frozenset[str] = frozenset(),
        _root_name: str | None = None,
    ) -> str:
        """Resolve a type alias to its base type name.

        Follows alias chains through refinement types to the underlying
        primitive or ADT name.  E.g. "PosInt" -> "Int".

        ``_seen`` is an internal cycle-detection accumulator — when the
        same name is encountered twice along an alias chain (cyclic
        aliases such as ``type A = B; type B = A``), the recursion is
        cut and the **caller's original** name is returned via the
        threaded ``_root_name``.  This matters for prefix-chain cycles
        like ``{A: B, B: C, C: B}`` (A leads into a B↔C cycle that
        doesn't include A): the caller asked about ``A``, so the
        return must be ``A``, not the revisited-cycle node ``B``.
        Cyclic aliases are user errors caught by the type checker's
        ``_check_alias_cycles`` pass which emits ``[E132]`` (closed
        in #648); this guard is defence-in-depth so a future
        regression in the upstream check cannot turn into a
        ``RecursionError`` inside codegen.  Closes #633 — the sibling
        walker ``_canonical_named_type`` (PR #631) already has this
        guard; this restores consistency.

        ``_root_name`` defaults to ``None`` on the public-entry call;
        the first recursion sets it to the original ``name`` so all
        deeper calls share the same caller-visible identity.
        """
        if _root_name is None:
            _root_name = name
        if name in _seen:
            # Cycle — return the caller's original name unchanged
            # (treat as opaque, no resolution available).
            return _root_name
        if name not in self._type_aliases:
            # Not an alias — this is the underlying base name.
            return name
        _seen = _seen | {name}
        alias = self._type_aliases[name]
        if isinstance(alias, ast.RefinementType):
            if isinstance(alias.base_type, ast.NamedType):
                return self._resolve_base_type_name(
                    alias.base_type.name, _seen, _root_name,
                )
        if isinstance(alias, ast.NamedType):
            return self._resolve_base_type_name(
                alias.name, _seen, _root_name,
            )
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
