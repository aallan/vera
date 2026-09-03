"""Type inference and utility mixin for WasmContext."""

from __future__ import annotations

from typing import ClassVar

from vera import ast, naming
from vera.monomorphize import (
    Monomorphizer,
    checker_clone_type_name,
    _BUILTIN_PARAMETERIZED_RETURNS,
    _BUILTIN_VERA_RETURN_TYPES,
    declared_return_clone_key,
    pipe_desugared_call,
    resolve_fn_type_alias,
    substitute_type_vars,
)
from vera.slots import (
    bare_call_denotes_user_fn,
    family_fallback_name,
    type_expr_slot_name,
)
from vera.wasm.helpers import _element_wasm_type, state_type_arg

# `substitute_type_vars` was relocated to `vera.monomorphize` (the codegen-free
# shared monomorphizer, #732) so the verifier can reuse it without importing the
# WASM backend.  Re-exported here so the existing
# `from vera.wasm.inference import substitute_type_vars` call sites
# (codegen/core.py, codegen/registration.py, codegen/contracts.py)
# keep working.  (wasm/calls.py now imports `resolve_fn_type_alias`
# from `vera.monomorphize` directly instead — PR #880.)
__all__ = ["InferenceMixin", "substitute_type_vars"]


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
    _ARITH_OPS: ClassVar[dict[ast.BinOp, str]] = {
        ast.BinOp.ADD: "i64.add",
        ast.BinOp.SUB: "i64.sub",
        ast.BinOp.MUL: "i64.mul",
        ast.BinOp.DIV: "i64.div_s",
        ast.BinOp.MOD: "i64.rem_s",
    }

    # Arithmetic: f64 ops (Float64)
    _ARITH_OPS_F64: ClassVar[dict[ast.BinOp, str]] = {
        ast.BinOp.ADD: "f64.add",
        ast.BinOp.SUB: "f64.sub",
        ast.BinOp.MUL: "f64.mul",
        ast.BinOp.DIV: "f64.div",
        # MOD: handled by _translate_f64_mod() — WASM has no f64.rem
    }

    # Comparison: i64 → i32 (default)
    _CMP_OPS: ClassVar[dict[ast.BinOp, str]] = {
        ast.BinOp.EQ: "i64.eq",
        ast.BinOp.NEQ: "i64.ne",
        ast.BinOp.LT: "i64.lt_s",
        ast.BinOp.GT: "i64.gt_s",
        ast.BinOp.LE: "i64.le_s",
        ast.BinOp.GE: "i64.ge_s",
    }

    # Comparison: f64 → i32 (Float64)
    _CMP_OPS_F64: ClassVar[dict[ast.BinOp, str]] = {
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

        One exception to the Int/Nat rule: an ``IntLit`` carrying the #1212
        Byte-width mark returns "i32", because that is what the lowering
        emits for it — the two deciders read the same mark so a marked leaf
        cannot be inferred at one width and lowered at the other.

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
        #   MatchExpr         → from the first arm whose body infers a type
        #                       (an all-throwing arm contributes none, #1276)
        #   IfExpr            → from the then-branch, falling back to the else
        #                       branch when the then-branch is typeless (#1276)
        #   Block             → from trailing expr
        #   HandleExpr        → from body
        #   IndexExpr         → from element type
        #   ArrayLit          → "i32_pair"
        #   ForallExpr        → "i32" (Bool)
        #   ExistsExpr        → "i32" (Bool)
        #   AssertExpr        → None (Unit)
        #   AssumeExpr        → None (Unit)
        #   AnonFn            → "i32" (closure ptr — defensive add #597)
        #   ModuleCall        → resolve target via
        #                       `_resolve_module_call_wasm_name` (the
        #                       single shared resolver), then reuse
        #                       `_infer_fncall_wasm_type` (#905 — a
        #                       ModuleCall in a constructor field needs
        #                       its WASM return type; the resolver
        #                       consumes `path`, so no wrong-name lookup)
        #   OldExpr           → State<T>'s WAT type (postcondition
        #                       snapshot read; #914 finding 1)
        #   NewExpr           → State<T>'s WAT type (postcondition
        #                       fresh state read; #914 finding 1)
        #
        # Cannot occur (rejected before reaching this codegen-time
        # helper):
        #   HoleExpr          → parser placeholder; check time rejects
        """
        if isinstance(expr, ast.IntLit):
            # #1212: same Byte-width mark the lowering reads — a `match`
            # result type is inferred from an arm BODY through here, so the
            # two deciders must agree about a marked leaf.
            return "i32" if id(expr) in self._byte_literal_ids else "i64"
        if isinstance(expr, ast.FloatLit):
            return "f64"
        if isinstance(expr, ast.BoolLit):
            return "i32"
        if isinstance(expr, ast.UnitLit):
            return None
        if isinstance(expr, ast.SlotRef):
            return self._ref_type_name_wasm_type(
                expr.type_name, expr.type_args)
        if isinstance(expr, ast.ResultRef):
            # #891: a `@T.result` in a monomorphized clone carries the same
            # concrete `type_name` as `@T.0` (e.g. `Box` once `T = Box`), so it
            # must lower through the SAME type-name → WAT-type logic.  Inferring
            # only the scalar primitives here left an ADT-bound (pointer-
            # represented) return inferred as `None`, so the postcondition
            # `@T.result == @T.0` fell through to the i64 comparison default
            # while both operands were i32 heap pointers — an ill-typed
            # `i64.eq` that traps `gid$Box` at run with `expected i64, found
            # i32`.  Sharing `_ref_type_name_wasm_type` keeps the ResultRef and
            # SlotRef operands in agreement (ADT, pair, and handle types alike).
            return self._ref_type_name_wasm_type(
                expr.type_name, expr.type_args)
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
            # #1276 (F4): the FIRST arm that yields a type, not arm 0.  An arm
            # whose every path throws contributes no WAT type, and reading only
            # arm 0 answered `None` for the whole match — so an enclosing
            # `handle` block was emitted result-less while the completing arms
            # left a value in it (`values remaining on stack at end of block`,
            # from check-green source).  Arms that DO complete must agree on
            # their type (the checker enforces that), so the first answer is the
            # answer.
            for arm in expr.arms:
                arm_wt = self._infer_expr_wasm_type(arm.body)
                if arm_wt is not None:
                    return arm_wt
            return None
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
            # #1276 (F4): fall through to the ELSE branch when the THEN branch
            # yields no type.  A `then` that always throws is typeless, and
            # answering `None` for the whole `if` on that basis mistyped every
            # consumer of the result — see the MatchExpr arm above, same shape.
            then_wt = self._infer_block_result_type(expr.then_branch)
            if then_wt is not None:
                return then_wt
            return self._infer_block_result_type(expr.else_branch)
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
        # #905: a non-void ModuleCall used *directly* as a constructor argument
        # (a Tuple/ADT field) reaches this helper via
        # `_translate_constructor_call`, which needs the field's WASM type to lay
        # out offsets.  Resolve the qualified target through the SAME single
        # resolver the desugar and the statement-position result-shape predicates
        # (`_is_void_expr` / `_is_pair_result_expr`) already use —
        # `_resolve_module_call_wasm_name` returns the bare name, the `mod$…`
        # name when a local shadows it, or a shadowed generic's per-
        # instantiation clone — then reuse the FnCall inference on that resolved
        # target.  This does NOT drop the path (the earlier #597 concern): the
        # resolver consumes it, so a same-name local from a different module can
        # never be matched.  Keeping all four sites on one resolver means they
        # can never disagree on which function `m::f(...)` reaches.  Before this,
        # returning None made `_translate_constructor_call` raise CodegenSkip and
        # silently drop the enclosing function — a check-green program then
        # dangled its call at run (`unknown func $mkt`).
        if isinstance(expr, ast.ModuleCall):
            target = self._resolve_module_call_wasm_name(expr)
            return self._infer_fncall_wasm_type(
                ast.FnCall(name=target, args=expr.args, span=expr.span))
        # #914 finding 1: `old(State<T>)` / `new(State<T>)` in a postcondition
        # each yield a value of type T — the snapshot local (old) or a fresh
        # `state_get` (new).  Without a width here a composite `old == new`
        # over a pointer-typed T (`Option<Int>` → i32) fell through to the
        # i64 comparison default and emitted an ill-typed `i64.eq` on two
        # i32 pointers (`expected i64, found i32`).  Resolve T's WAT type via
        # the shared canonical-slot-name → WASM map so the `==` picks i32.
        if isinstance(expr, (ast.OldExpr, ast.NewExpr)):
            # The cell's REPRESENTATION name, not the source spelling, before
            # the WT map — `old(State<Count>)` over `type Count = Nat` is an
            # i64 read, not the unknown-name i32 default (#1205).  The base
            # rather than the family (#1218): a refined cell's identity
            # carries its predicate and would miss every entry in the map,
            # silently defaulting a refined `Int` cell's `old`/`new` read to
            # i32 — the base is the width both sides of the comparison have.
            return self._type_name_to_wasm(
                self._state_effect_family_base(expr.effect_ref))
        return None

    _IO_WASM_TYPES: ClassVar[dict[str, str | None]] = {
        "print": None,
        "read_line": "i32_pair",
        "read_file": "i32",
        "write_file": "i32",
        "args": "i32_pair",
        "exit": None,
        "get_env": "i32",
        "read_char": "i32",  # Result<String,String> pointer (#618)
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
        if expr.qualifier == "DB":
            # query / execute both return a Result ADT (i32 heap ptr) (#229)
            return "i32"
        # User-defined effect ops (e.g. Exn.throw, State.get/put)
        if expr.name in self._effect_ops:
            _target_name, is_void = self._effect_ops[expr.name]
            if expr.name == "throw" or is_void:
                return None  # throw → Never; void ops return no value
            # #914: the op's result type is its State<T> parameter's WAT type,
            # recorded in `_effect_op_result_wt` at the injection site — NOT a
            # `_fn_ret_types` lookup on the dispatch target (`$vera.state_get_T`
            # is never a `_fn_ret_types` key, so the old lookup returned None
            # for every value-producing op, composite or primitive).
            return self._effect_op_result_wt.get(expr.name)
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
        # Ability operations: show → String (i32_pair), hash → Int (i64).
        # #908: these are name special-cases the checker does NOT reserve
        # (unlike E151 registry builtins), so a user may define `fn show` /
        # `fn hash` with a different return width.  `_translate_call` gates its
        # ability-op dispatch on `call.name not in self._known_fns`, so a
        # user-defined `show`/`hash` is emitted as a plain call to the USER
        # function — its DECLARED return width, not the ability-op width.  Defer
        # to `_fn_ret_types` (the same registry the general user-fn branch below
        # consults) when the name resolves to a user fn, so the field/element
        # WASM type matches the emit.  A GENUINE ability op has no `_fn_ret_types`
        # entry, so it falls through to the special-case width.
        if expr.name in ("show", "hash") and expr.name in self._fn_ret_types:
            return self._fn_ret_types[expr.name]
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
        # #914: a bare effect-op call (`get(())` inside a State<T> handler /
        # a fn declaring `<State<T>>`) is an `ast.FnCall`, not a
        # `QualifiedCall`.  Its result WAT type is the op's registered
        # result type — needed when the call sits directly in a
        # constructor-argument (A1) or match-scrutinee (A2) position.
        # #1284: the registry is complete (it says which cell an op name
        # reaches, shadowed or not), so whether THIS site is the op is the
        # ownership predicate's question — a same-named user fn falls
        # through to the `_fn_ret_types` lookup below, the same answer the
        # dispatch in `_translate_call` will emit a call for.
        if self._bare_call_denotes_op(expr.name) and expr.name in self._effect_ops:
            _target, is_void = self._effect_ops[expr.name]
            if expr.name == "throw" or is_void:
                return None
            return self._effect_op_result_wt.get(expr.name)
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
        """Infer the WAT result type of a block from its final expression.

        #1212: a literal marked for the i32 Byte width lowers as
        ``i32.const``, so the join built over it must be annotated
        ``(result i32)`` — the decider and the lowering read the same marks
        (`_mark_byte_literal_leaves`), which is what keeps the `if` / `match`
        result type and its arms in agreement.
        """
        expr = block.expr
        if isinstance(expr, ast.IntLit):
            return "i32" if id(expr) in self._byte_literal_ids else "i64"
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
            # #1276 (F4): the twin of the `_infer_expr_wasm_type` arm — a
            # `then` branch whose every path throws yields no type, and
            # answering `None` for the whole `if` on that basis left an
            # enclosing `handle` block result-less while the completing branch
            # pushed a value into it.
            then_wt = self._infer_block_result_type(expr.then_branch)
            if then_wt is not None:
                return then_wt
            return self._infer_block_result_type(expr.else_branch)
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
            # #1276 (F4): the first arm that yields a type — see the twin arm
            # in `_infer_expr_wasm_type`.
            for arm in expr.arms:
                arm_wt = self._infer_expr_wasm_type(arm.body)
                if arm_wt is not None:
                    return arm_wt
            return None
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

        Note: duplicated in Monomorphizer._format_type_name
        (vera/monomorphize.py). Both must remain in sync.
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
        3. Follows `NamedType` alias chains via `self._alias_env.aliases`
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
            # and `_alias_env.aliases` chain following.  Without this, an
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
            alias = self._alias_env.aliases.get(te.name)
            if alias is None:
                break
            if isinstance(alias, (ast.NamedType, ast.RefinementType)):
                alias_params = self._alias_env.alias_params.get(te.name)
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
        `alias_map` / `_alias_env.aliases` lands on a `FnType`.

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
            alias = self._alias_env.aliases.get(te.name)
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

    def _ref_vera_type_name(
        self, type_name: str, type_args: tuple[ast.TypeExpr, ...] | None,
    ) -> str | None:
        """Vera type name of a slot/result reference (`@T` / `@T.result`).

        Shared by the `SlotRef` and `ResultRef` arms of `_infer_vera_type` —
        both carry the same declared @Type shape (`type_name` + optional
        `type_args`).  A parameterized ref (`@Option<Int>`) renders its type
        arguments (`"Option<Int>"`) so the composite structural-`==` dispatch
        can resolve the concrete field types; a ref whose type argument is not a
        plain `NamedType` (a generic type variable, say) falls back to the bare
        `type_name` rather than emitting a malformed name.
        """
        if type_args:
            arg_names = []
            for ta in type_args:
                if isinstance(ta, ast.NamedType):
                    arg_names.append(self._format_named_type(ta))
                else:
                    return type_name
            return f"{type_name}<{', '.join(arg_names)}>"
        return type_name

    def _infer_vera_type(self, expr: ast.Expr) -> str | None:
        """The Vera type name of an expression for call rewriting, from one
        source: this walker first, the CHECKER second.

        The precedence and its rationale are stated once, on
        :func:`vera.monomorphize.checker_clone_type_name`.  The discovery twin
        (``Monomorphizer._infer_vera_type_name``) asks the same two sources in
        the same order over the same table, so a shape either walker cannot
        name is named identically for both rather than becoming a clone only
        one of them believes in — which is what every member of the #1327
        family was.
        """
        walked = self._walk_vera_type(expr)
        if walked is not None:
            return walked
        return checker_clone_type_name(self._expr_semantic_types, expr)

    def _walk_vera_type(self, expr: ast.Expr) -> str | None:
        """Infer the Vera type name of an expression, syntactically.

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
        #   ResultRef         → declared @Type name (with type-args) —
        #                       shares the SlotRef arm.  A `@T.result`
        #                       operand of `==`/`!=` in an `ensures`
        #                       reaches here through the runtime
        #                       postcondition-check lowering; without a
        #                       Vera-type name the composite structural-
        #                       `==` dispatch is skipped and the compare
        #                       falls back to scalar `i32.eq` (a pointer
        #                       compare) → a spurious trap on a proved
        #                       composite postcondition (#912).
        #   ConstructorCall   → parent ADT name
        #   NullaryConstructor → parent ADT name
        #   BinaryExpr        → "Bool" for cmp/logic, else left's type
        #   UnaryExpr         → "Bool" for `not`, else operand's type
        #   FnCall            → effect-op result registry first (#1006 —
        #                       `get(())` as an array-literal element),
        #                       else from `_infer_fncall_vera_type`
        #   ArrayLit          → "Array"
        #   IndexExpr         → element type
        #   IfExpr            → from the first branch that yields a name
        #                       (#1286 — the Vera-level twin of #1276's
        #                       WAT join; a diverging `then` names nothing)
        #   Block             → from trailing expr (defensive add #597)
        #   MatchExpr         → from the first arm body that yields a name
        #                       (defensive add #597; #1286 join)
        #   HandleExpr        → from body (defensive add #597)
        #   AssertExpr        → "Unit" (defensive add #597)
        #   AssumeExpr        → "Unit" (defensive add #597)
        #   AnonFn            → None (defensive add #597 — closure
        #                       handle has no simple Vera-type
        #                       name suitable for call rewriting;
        #                       None lets callers handle the
        #                       unknown-type case explicitly)
        #   QualifiedCall     → None (defensive add #597 — the
        #                       `qualifier` field can't be threaded
        #                       through the bare-name FnCall
        #                       dispatcher; None instead of a
        #                       wrong same-name lookup)
        #   ModuleCall        → resolve target via
        #                       `_resolve_module_call_wasm_name`, then
        #                       reuse `_infer_fncall_vera_type` (#905 —
        #                       a ModuleCall as an array-literal element
        #                       needs its Vera return type; the resolver
        #                       consumes `path`, so no wrong-name lookup)
        #
        # Cannot occur (contract-only or check-time rejected):
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
            return self._ref_vera_type_name(expr.type_name, expr.type_args)
        if isinstance(expr, ast.ResultRef):
            # #912: a `@T.result` operand of `==`/`!=` in an `ensures` reaches
            # here from the runtime postcondition-check lowering, carrying the
            # same declared @Type shape as a SlotRef (`type_name` + optional
            # `type_args`, no `index`).  Sharing the SlotRef name logic lets the
            # composite structural-`==` dispatch in `operators.py` resolve
            # `@Box.result` → "Box" (or "Option<Int>", "Tuple<Int, Int>", …) and
            # route to structural equality instead of the scalar `i32.eq`
            # pointer compare that spuriously trapped a proved composite
            # postcondition.  `_infer_expr_wasm_type` already handled the
            # ResultRef *width* (#891); this closes the parallel Vera-type gap.
            return self._ref_vera_type_name(expr.type_name, expr.type_args)
        if isinstance(expr, ast.ConstructorCall):
            return self._ctor_to_adt_name(expr.name)
        if isinstance(expr, ast.NullaryConstructor):
            return self._ctor_to_adt_name(expr.name)
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in (ast.BinOp.EQ, ast.BinOp.NEQ, ast.BinOp.LT,
                           ast.BinOp.GT, ast.BinOp.LE, ast.BinOp.GE,
                           ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES):
                return "Bool"
            piped = pipe_desugared_call(expr)
            if piped is not None:
                # #1365: a PIPE names its RIGHT-hand call's RESULT, not the
                # piped-in value — see the discovery twin
                # (`Monomorphizer._infer_vera_type_name`), which carries the
                # identical arm over the identical shared desugar.  Reading
                # the left operand made a type-CHANGING stage instantiate the
                # generic at the pre-stage type, and since both consultors
                # read it the same way they agreed confidently on the wrong
                # clone: no diagnostic anywhere, and an invalid module.
                return self._infer_vera_type(piped)
            return self._infer_vera_type(expr.left)
        if isinstance(expr, ast.UnaryExpr):
            if expr.op == ast.UnaryOp.NOT:
                return "Bool"
            return self._infer_vera_type(expr.operand)
        if isinstance(expr, ast.FnCall):
            # #1006: an effect op in a Vera-type-needing position (the
            # array-literal ELEMENT case) — the op is not in the fn tables,
            # so consult the op registry first.  Guarded on `_effect_ops`
            # membership (op names only bind where ops are injected) AND on
            # bare-call ownership (#1284), so a user fn shadowing an op name
            # resolves through the normal fn path below — the registry
            # itself no longer withholds the name, because it answers which
            # cell the op reaches rather than whose name this is.  `get`
            # maps to State<T>'s T; `put`/`throw` record no Vera result type
            # and return None (unchanged skip for value-position uses).
            if (self._bare_call_denotes_op(expr.name)
                    and expr.name in self._effect_ops):
                return self._effect_op_result_vera.get(expr.name)
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
            # #1286: the FIRST branch that yields a name, not the `then`
            # branch alone — the Vera-level twin of the #1276 WAT join
            # (`_infer_expr_wasm_type` / `_infer_block_result_type`).  A
            # `then` whose every path throws names no type, and answering
            # `None` for the whole `if` on that basis lost the type the
            # completing branch carries: as an array-literal element the
            # literal was dropped with the loud [E602] skip, and as a
            # generic argument the instantiation fell to the phantom-var
            # default (`idg$Bool` for an `Int` argument) and the module
            # failed to load — both from check- and verify-green source.
            # Branches that DO complete must agree on their type (the
            # checker enforces that), so the first answer is the answer.
            then_vt = self._infer_vera_type(expr.then_branch.expr)
            if then_vt is not None:
                return then_vt
            return self._infer_vera_type(expr.else_branch.expr)
        # Defensive adds (#597) — these compound expressions could
        # flow in here from generic-arg inference paths, but today
        # most callers preprocess first.  Returning the right Vera
        # type instead of None hardens against a future caller
        # extending the surface.
        # Block.expr is non-Optional (vera/ast.py:470).
        if isinstance(expr, ast.Block):
            return self._infer_vera_type(expr.expr)
        if isinstance(expr, ast.MatchExpr):
            # #1286: the first arm that yields a name — see the `IfExpr`
            # arm above, same shape and same two symptoms.
            for arm in expr.arms:
                arm_vt = self._infer_vera_type(arm.body)
                if arm_vt is not None:
                    return arm_vt
            return None
        # HandleExpr.body is non-Optional Block; its .expr is also
        # non-Optional (vera/ast.py:481, 470).
        if isinstance(expr, ast.HandleExpr):
            return self._infer_vera_type(expr.body.expr)
        if isinstance(expr, (ast.AssertExpr, ast.AssumeExpr)):
            return "Unit"
        # #905 (array-literal sibling): a ModuleCall used as the FIRST element
        # of an array literal reaches here via `_infer_array_element_type`,
        # which needs the element's Vera type name to lay the array out.
        # Resolve the qualified target through the SAME single resolver the
        # desugar uses (`_resolve_module_call_wasm_name` — it CONSUMES `path`,
        # so no same-name-local mismatch, the earlier #597 concern) and delegate
        # to the FnCall Vera-type inference.  Without this, `[m::f(x), …]` inferred
        # a None element type → the array-let binding was dropped and the
        # enclosing function silently vanished from the exports on a check-green
        # program (same class as the constructor-field crash, quieter symptom).
        if isinstance(expr, ast.ModuleCall):
            target = self._resolve_module_call_wasm_name(expr)
            return self._infer_fncall_vera_type(
                ast.FnCall(name=target, args=expr.args, span=expr.span))
        # AnonFn / QualifiedCall: return None rather than a placeholder string.
        # AnonFn's Vera type would be a full `FnType` shape that isn't typically
        # needed for call rewriting; QualifiedCall carries a `qualifier` the
        # bare-name `FnCall` dispatcher cannot consume — synthesising a fake
        # `FnCall` would drop it and could match a same-name local fn instead.
        # None lets callers handle the unknown-type case explicitly rather than
        # propagating a wrong type silently.
        if isinstance(expr, (ast.AnonFn, ast.QualifiedCall)):
            return None
        return None  # pragma: no cover

    def _infer_fncall_vera_type(self, call: ast.FnCall) -> str | None:
        """Infer Vera return type of a function call.

        For generic calls, resolves type args and substitutes into
        the return TypeExpr.  For non-generic calls, maps from WASM
        return type back to Vera type name.
        """
        # apply_fn(closure, args...) — infer from closure's return type.
        #
        # The closure-arg return TypeExpr is extracted by the shared
        # `_closure_arg_return_type` dispatch: a `SlotRef` resolves
        # **transitively** through the alias chain to the terminal
        # `FnType` (via `resolve_fn_type_alias`, #867 — with any generic
        # alias's type params substituted), an inline `AnonFn` yields its
        # declared return type.  Pre-#630 each shape had its own ad-hoc
        # walk with subset-of-the-concerns coverage — accounting for
        # triggers 7 (SlotRef + nested-RefinementType return), 8 (SlotRef
        # + `FnType`-aliased-String return), 9 (AnonFn + plain return),
        # and 10 (AnonFn + nested-RefinementType return) of the #602 bug
        # class; the extracted TypeExpr then feeds the centralised
        # `_canonical_named_type` walker.  Shapes without a single
        # `return_type` field (`IfExpr` between two closures with the same
        # Vera-level type, `MatchExpr` arms, etc.) need a unifying step
        # that's genuinely additional dispatch work, not "plug-in".
        if call.name == "apply_fn" and call.args:
            ret_te = self._closure_arg_return_type(call.args[0])
            if ret_te is not None:
                canonical = self._canonical_named_type(ret_te)
                if canonical is not None:
                    return self._format_named_type(canonical)
        # Ability operations: show → String, hash → Int.  #908: skip the name
        # special-case when the user has defined `fn show` / `fn hash` (the
        # checker doesn't reserve these ability-op names), so the Vera element
        # type falls through to the general non-generic user-fn resolution below
        # (which reads the DECLARED return type from `_fn_ret_type_exprs` /
        # `_fn_ret_types`).  A GENUINE ability op has no `_fn_ret_types` entry, so
        # it keeps the special-case.  Mirrors the WASM-width guard in
        # `_infer_fncall_wasm_type` and the `not in self._known_fns` gate in
        # `_translate_call`.
        if call.name not in self._fn_ret_types:
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
        # Registry-complete builtin simple-name table (#769 gap 1b) — the SAME
        # dict instantiation discovery consults
        # (Monomorphizer._infer_fncall_vera_type_simple), so the two clone-name
        # consultors cannot drift: an entry added there lands here atomically.
        # Consulted AFTER the logic arms above (apply_fn / show / hash /
        # async / await), which need call-shape context no fixed table has —
        # e.g. `async` prefers the richer "Future<Int>" over the dict's bare
        # "Future".  Gated on non-registration: a name in _fn_ret_types is a
        # REAL declaration — a user fn, or a user OVERRIDE of an E151-exempt
        # prelude combinator (#815: option_map, the json_* family, html_attr)
        # — whose declared type must win, exactly like the #908 show/hash
        # gate (adversarial panel, PR #972).  Opaque builtins are never
        # registered there and fall through to the dict.
        if call.name not in self._fn_ret_types:
            builtin_simple = _BUILTIN_VERA_RETURN_TYPES.get(call.name)
            if builtin_simple is not None:
                return builtin_simple
        if call.name in self._generic_fn_info:
            forall_vars, param_types = self._generic_fn_info[call.name]
            constrained_vars = self._generic_constrained_vars.get(
                call.name, frozenset())
            mapping: dict[str, str] = {}
            for pt, arg in zip(param_types, call.args):
                self._unify_param_arg_wasm(
                    pt, arg, forall_vars, mapping, constrained_vars)
            # Use the first param's type to determine return type
            # (Generic fn return type is typically a type var)
            # We need to figure out the return type from forall info
            # Actually, look at the monomorphized fn sig
            parts = []
            for tv in forall_vars:
                if tv not in mapping:  # pragma: no cover
                    return None
                parts.append(mapping[tv])
            # Shared injective mangler (#775) — the registry below is keyed
            # by the clone names Pass 1.5 emitted, so the lookup key must be
            # built by the same encoding.  (The pre-#775 site joined RAW
            # type names with "_", which additionally missed every
            # parameterized instantiation like Map<String, Int>.)
            # #769: prefer the callee's DECLARED return TypeExpr substituted
            # with the inferred instantiation — exactly the substitution
            # discovery performs (Monomorphizer._infer_fncall_vera_type), so
            # both sides mangle the same clone for a generic call in
            # argument position.  The WAT collapse below names an i32-handle
            # return "Bool" and a declared-Nat i64 return "Int" — names
            # discovery never emits (dangling-E602 desyncs pre-#769).
            decl_ret = self._fn_ret_type_exprs.get(call.name)
            if isinstance(decl_ret, ast.RefinementType):
                decl_ret = decl_ret.base_type
            if isinstance(decl_ret, ast.NamedType):
                sub_map = dict(zip(forall_vars, parts))
                return sub_map.get(decl_ret.name, decl_ret.name)
            mangled = Monomorphizer._mangle_fn_name(call.name, tuple(parts))
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
        # Non-generic user-fn call: prefer the PRECISE declared return type
        # name (#878).  The WAT-type map below collapses every i32 handle
        # (Decimal, an ADT, an Option/Result pointer) to "Bool" — the exact
        # phantom-var default value — so a user helper `d` returning `@Decimal`
        # used in a generic's bare `@VeraT` argument position resolved to the
        # Bool clone (`option_unwrap_or$Bool`), a symbol Pass 1.5 never emitted.
        # The declared return TypeExpr (registered by `_register_fn`) carries
        # the real name, mirroring how the #732 verifier builds `fn_ret_types`
        # from declared types.  Only the i32-collapse ambiguity needs this;
        # i64/f64/i32_pair are already unambiguous, and a bare scalar declared
        # return (`Int`, `Bool`) still yields the same name.
        #
        # NB: this returns the ALIAS-RESOLVED name for scalar-resolving aliases
        # (`type Age = Int` → "Int"), which is what non-clone-naming callers
        # (interpolation, container element/key typing, `show`/`hash`) require.
        # The clone-naming path needs the RAW alias name instead and gets it
        # from `_declared_return_clone_name` (used by `_unify_param_arg_wasm`),
        # NOT from here — see #899 issue 2.
        ret_te = self._fn_ret_type_exprs.get(call.name)
        if isinstance(ret_te, ast.RefinementType):
            ret_te = ret_te.base_type
        if isinstance(ret_te, ast.NamedType) and not ret_te.type_args:
            # Only override the ambiguous i32 collapse: an i32-returning user
            # fn whose declared base is not a scalar (Decimal, an ADT, …) must
            # keep its true name.  Gate on the ALIAS-RESOLVED base (so
            # `type Money = Decimal` is recognised as non-scalar), returning the
            # raw declared name for it.  i64/f64/i32_pair fall through.
            if self._resolve_base_type_name(ret_te.name) not in (
                "Int", "Nat", "Bool", "Byte", "Float64", "String",
            ):
                return ret_te.name
        # #911: a PARAMETERIZED i32-pointer return (`Option<Int>`,
        # `Result<Int, String>`, a generic ADT) is the same ambiguous
        # i32-collapse as the scalar-guard above, but the `not ret_te.type_args`
        # clause skipped it — so it fell through to `i32 → "Bool"` and mis-typed
        # a composite `show`/`hash` argument.  Return the base head; the
        # `show`/`hash` site recovers the type args separately via
        # `_get_arg_type_info_wasm`.  Array is excluded: it is i32_pair, already
        # disambiguated to "Array" by the `_resolve_i32_pair_ret_te` branch
        # below — intercepting it here would be a redundant second path.
        if (
            isinstance(ret_te, ast.NamedType)
            and ret_te.type_args
            and self._fn_ret_types.get(call.name) == "i32"
            and self._resolve_base_type_name(ret_te.name) not in (
                "Int", "Nat", "Bool", "Byte", "Float64", "String", "Array",
            )
        ):
            return ret_te.name
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

    def _declared_return_clone_name(self, call: ast.FnCall) -> str | None:
        """The clone-name KEY a non-generic user fn call's declared return
        contributes when its result is bound to a generic's bare ``@T``, for
        CLONE NAMING only (#878 / #899).

        Delegates to the shared
        :func:`vera.monomorphize.declared_return_clone_key` — THE single source
        of truth that instantiation discovery (``_simple_return_type_name``) and
        the #732 verifier (``_simple_type_name``) also route through — so the
        call-rewrite cannot desync from the emitted clone by construction.  This
        ends the three-round whack-a-mole: the previous ad-hoc gate
        (``not ret_te.type_args``) BAILED for a parameterized return
        (``-> @Option<Decimal>``) and fell through to the ``i32 → "Bool"``
        collapse, so the call site referenced ``pick$Bool`` while discovery
        emitted ``pick$Option`` — a NET regression vs base, which linked both to
        ``$Bool``.  The shared key gives the base name for a parameterized
        return (``Option``), the raw name for an alias/refinement (``Age``), and
        the plain name for a scalar/handle (``Decimal``), identically to
        discovery for EVERY shape.

        The general ``_infer_fncall_vera_type`` deliberately alias-RESOLVES
        scalars for its OTHER callers (interpolation, container typing,
        ``show``/``hash`` need the canonical ``Int``/``String``), which is why
        the clone-naming path must consult THIS method instead.  Returns
        ``None`` for builtins, generics, and fns with no NamedType return, so
        the caller falls back to ``_infer_vera_type``.

        Gated on the #1284 ownership predicate over the LEXICAL scope
        (#1299).  ``_fn_ret_type_exprs`` is flat — it holds every declaration
        the compilation absorbed, including an imported module's private one
        — and this override BEATS ``_infer_vera_type``, so an invisible
        ``fn get(@Unit -> @Bool)`` named the clone ``idg$Bool`` at a call site
        where the general inference had correctly answered the ``State<Int>``
        cell's ``Int``.  A name no visible declaration owns contributes no
        declared return: the caller falls back, and reaches the operation.
        """
        if call.name in self._generic_fn_info:
            return None
        if not bare_call_denotes_user_fn(call.name, self._scoped_fns):
            return None
        return declared_return_clone_key(
            self._fn_ret_type_exprs.get(call.name))

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

    def _is_pair_type_name(
        self, type_name: str, _seen: frozenset[str] = frozenset(),
    ) -> bool:
        """Check if a slot type name is a pair type (ptr, len).

        String and Array<T> are represented as two consecutive i32 locals.
        Bare "Array" also matches — monomorphization may produce slot
        references with type_name="Array" (no type args in the name).

        An alias is canonicalized to its target's FULL compound spelling
        first (the shared :meth:`_canonicalize_alias_slot_name` walk, #1046):
        the name-only ``_resolve_base_type_name`` hop drops type arguments,
        so ``type FS = Future<String>`` resolved to bare ``"Future"``, missed
        the Future arm below, and the let binding E602-skipped its enclosing
        function on a check+verify-green program — the pair-payload sibling
        of the #1037 scalar-alias fix, which wired the canonicalizer into
        ``_slot_name_to_wasm_type`` but not into this predicate.

        Resolves type aliases first so `type Row = Array<Bool>` compiles
        identically to writing `Array<Bool>` directly: a SlotRef with
        type_name "Row" must emit `(local.get ptr; local.get len)` like
        any other Array slot, not just the ptr (#583).

        `Future<T>` is representation-transparent (#841): a `Future<String>`
        / `Future<Array<T>>` has the SAME `i32_pair` layout as its payload,
        so it binds and reads as two locals exactly like a bare String /
        Array.  The transparency is to the PAYLOAD's representation — a
        scalar payload (`Future<Int>` → i64) or a pointer payload
        (`Future<Box>` → i32) is NOT a pair.  Mirrors the string-form
        strip-and-recurse in `_slot_name_to_wasm_type`'s Future arm, and
        covers both composite-string sites in the let path — the binding
        (`translate_block`) and the read emit (`_translate_slot_ref`).
        Without it a `let @Future<String>` fell to the scalar branch, where
        `_slot_name_to_wasm_type` recursed through the wrapper to a pair
        inner and returned None, and the whole function was dropped with the
        [E602] loud skip on a check/verify-green program (#1039).
        """
        type_name, _seen = self._canonicalize_alias_slot_name(type_name, _seen)
        resolved = self._resolve_base_type_name(type_name)
        if resolved.startswith("Future<") and resolved.endswith(">"):
            return self._is_pair_type_name(resolved[7:-1], _seen)
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

        Normally returns the bare element name (`te.name`) — dropping the
        element's own type args is safe because every ADT element is an i32
        heap pointer and String/Array match on the bare head, so the
        representation deciders (`_element_mem_size` / `_element_load_op` /
        `_element_store_op` / `_element_wasm_type` / `_is_pair_element_type`)
        need no args.  The ONE exception is `Future<T>` (#1045): it is
        representation-transparent (#841), so its width IS its payload's —
        a bare "Future" (args dropped) collapses to the i32 default and
        mis-sizes an i64 payload (`i32.load` on i64 data) or a pair payload
        (single i32 load of a two-word String).  Render the full
        `Future<…>` name so `_strip_future` can recover the payload, keeping
        this in agreement with the array-literal store side, which gets the
        full name from `_infer_array_element_type` -> `_infer_vera_type`.
        An alias INSIDE the payload (`Future<FlagA>`, `type FlagA = Bool`) is
        canonicalized to `Future<Bool>` first (#1074) so the bare alias does
        not itself fall to the 4-byte default under `_strip_future`.
        """
        te = self._infer_index_element_type_expr(expr)
        if te is None:
            return None
        if te.name == "Future" and te.type_args:
            # #1074: canonicalize an alias sitting inside the payload
            # (`Future<FlagA>` -> `Future<Bool>`) so `_strip_future` in the
            # element helpers hands a resolved payload to the size / load
            # deciders, not a bare alias that falls to the 4-byte default.
            canon, _ = self._canonicalize_alias_slot_name(
                self._format_named_type(te))
            return canon
        return te.name

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
            if canonical is None:
                # #1048: a BUILTIN call has no `_fn_ret_type_exprs` entry
                # (that registry holds user functions only), so `canonical`
                # is None above and — pre-fix — the collection fell through
                # to `return None`, `_translate_index_expr` returned None,
                # and the enclosing function was dropped via [E602].  Only
                # the let-bound form (`let @Array<Int> = array_concat(...);
                # @Array<Int>.0[i]`) worked — it resolves through the SlotRef
                # arm above, not this FnCall arm.  Recover the builtin's
                # return NamedType via the same `_get_arg_type_info_wasm`
                # consultor the sibling Vera-type inference
                # (`_infer_fncall_vera_type`) and instantiation discovery use,
                # so all three agree on the shape.  Type-variable-element
                # builtins (`array_map`/`array_reverse`/`map_keys`/…) are
                # absent from that consultor's tables — their element type
                # depends on the arguments — so `_builtin_call_ret_named_type`
                # derives their return NamedType from the call's arguments per
                # mechanism class (#1051).  A genuinely unresolvable argument
                # shape still yields None, so the function keeps the loud
                # [E602] skip rather than being mis-typed.
                canonical = self._builtin_call_ret_named_type(coll)
            if canonical is not None:
                ta_te = self._alias_array_element(
                    canonical.name, canonical.type_args)
                if ta_te is not None:
                    return ta_te
        return None

    def _builtin_call_ret_named_type(
        self, call: ast.FnCall,
    ) -> ast.NamedType | None:
        """Full return ``NamedType`` of a builtin ``call`` whose result is a
        parameterized type (e.g. ``array_concat(...)`` → ``Array<Int>``), or
        ``None`` if the shape cannot be resolved.

        Two resolution paths:

        1. Builtins whose return NamedType is recoverable from the shared
           ``(type_name, type_arg_names)`` consultor
           (:py:meth:`_get_arg_type_info_wasm`, via
           :py:meth:`_named_type_from_arg_info`): arg-forwarding for
           ``array_concat`` / ``array_append`` / ``array_slice`` /
           ``array_filter``, plus the ``_BUILTIN_PARAMETERIZED_RETURNS`` table
           for the concrete-Array builtins (``array_range``, ``string_split``,
           ``json_keys``, …).  Sharing that consultor keeps the index element
           type in lockstep with clone-name discovery (#1048).

        2. #1051: the eight *type-variable-element* Array-returning builtins
           (``array_reverse`` / ``array_sort_by`` / ``array_flatten`` /
           ``map_keys`` / ``map_values`` / ``set_to_array`` / ``array_map`` /
           ``array_mapi``) are deliberately ABSENT from that consultor's tables
           — their element type depends on the CALL's arguments, not a fixed
           signature, and ``_BUILTIN_PARAMETERIZED_RETURNS`` is registry-locked
           to type-var-free returns (``test_parameterized_table_matches_registry``
           rejects any TypeVar-carrying entry, else discovery would bind a
           phantom var).  Their return NamedType is derived from the arguments
           in :py:meth:`_typevar_elem_builtin_ret_named_type`, kept OFF the
           shared consultor (this helper is only reached from
           :py:meth:`_infer_index_element_type_expr`), so clone-name discovery
           is untouched.
        """
        nt = self._named_type_from_arg_info(call)
        if nt is not None:
            return nt
        return self._typevar_elem_builtin_ret_named_type(call)

    def _named_type_from_arg_info(
        self, expr: ast.Expr,
    ) -> ast.NamedType | None:
        """Rebuild an expression's parameterized Vera type as a ``NamedType``
        from the shared :py:meth:`_get_arg_type_info_wasm` consultor:
        ``(type_name, type_arg_names)`` → ``NamedType``, nested inners parsed
        via ``Monomorphizer._parse_type_name`` (which handles shapes like
        ``Array<Json>``).  ``None`` when neither the consultor nor the
        off-consultor fallbacks below can resolve the shape.

        Alias spellings resolve here so every consumer sees the target
        type: a bare alias slot canonicalizes (#1055), a GENERIC alias's
        args substitute through its target (#1068 — `MyMap<Int>` with
        `type MyMap<V> = Map<String, V>` resolves to `Map<String, Int>`,
        never a blind read of the alias's own args), and a registered
        user fn's declared return recovers shapes the consultor reports
        incompletely or not at all — nested type args (#1053) and bare
        alias returns (#1071) — OFF the consultor, so clone-name
        discovery is untouched.  A Block argument resolves via its tail
        expression (#1071).
        """
        # #1071: a Block-wrapped argument (`map_values({ @M.0 })`) types as
        # its tail expression.
        while isinstance(expr, ast.Block):
            expr = expr.expr
        info = self._get_arg_type_info_wasm(expr)
        if info is None:
            # #1071: a user fn whose declared return is a BARE alias of a
            # container (`fn mkm(-> @M)` with `type M = Map<String, Int>`)
            # has no type args for the consultor's user-fn arm to report,
            # so it exits None before any alias handling — recover the
            # declared return directly.
            return self._user_fn_declared_ret_named_type(expr)
        type_name, type_arg_names = info
        # #1055: an alias-spelled argument (`type Grid = Array<Array<Int>>;`
        # then `@Grid.0`) arrives as its bare alias name with NO type args,
        # so the class derivations never see the container shape and the
        # index E602-dropped where the direct spelling compiled.
        # Canonicalize to the target's full compound spelling (the #1037
        # walk) and parse that instead.  A GENERIC alias name is excluded —
        # its target carries the alias's own free type params, which must
        # not leak; without args it is unresolvable (falls through to the
        # arity-checked substitution path below, which yields None).
        # `alias_params` keys EVERY alias, mapping a non-parameterised one to
        # `None` (the former flat map simply omitted it), so "is this alias
        # generic?" is a None test here, not a membership test (#1208).
        if (not type_arg_names
                and self._alias_env.alias_params.get(type_name) is None):
            canonical, _ = self._canonicalize_alias_slot_name(type_name)
            if canonical != type_name:
                parsed = Monomorphizer._parse_type_name(canonical)
                if isinstance(parsed, ast.NamedType):
                    return parsed
                return None
        if any(a is None for a in type_arg_names):
            # #1053 user-fn extension: a registered non-generic user fn's
            # PARAMETERIZED return reaches the consultor with nested type-arg
            # positions blanked to None (its user-fn arm deliberately reports
            # only depth-one names, staying in clone-name-discovery lockstep),
            # so `array_flatten(mkn())` with `mkn(-> @Array<Array<Int>>)`
            # rebuilt as `("Array", (None,))` and stayed unresolvable.  The
            # declared return TypeExpr carries the full nesting — canonicalize
            # it directly, OFF the consultor, so discovery is untouched.
            return self._user_fn_declared_ret_named_type(expr)
        # #1068: a GENERIC alias spelling (`type MyMap<V> = Map<String, V>;`
        # then a `@MyMap<Int>`-returning argument) must never have its type
        # args consumed as the TARGET's — `("MyMap", ("Int",))`'s single arg
        # is the alias's V, not the Map's K.  Substitute the args through
        # the alias target and canonicalize; an arity mismatch (or a target
        # that resolves to no NamedType) is unresolvable — return None so
        # the caller keeps the loud skip.
        alias_params = self._alias_env.alias_params.get(type_name)
        if alias_params is not None:
            target = self._alias_env.aliases.get(type_name)
            if (target is not None
                    and type_arg_names
                    and len(type_arg_names) == len(alias_params)):
                subst: dict[str, ast.TypeExpr] = {
                    p: Monomorphizer._parse_type_name(a)
                    for p, a in zip(alias_params, type_arg_names)
                    if a is not None
                }
                resolved = substitute_type_vars(target, subst)
                return self._canonical_named_type(resolved)
            return None
        type_args = tuple(
            Monomorphizer._parse_type_name(a)
            for a in type_arg_names
            if a is not None
        )
        return ast.NamedType(name=type_name, type_args=type_args or None)

    def _user_fn_declared_ret_named_type(
        self, expr: ast.Expr,
    ) -> ast.NamedType | None:
        """Canonical ``NamedType`` of a registered NON-generic user fn call's
        declared return — the off-consultor recovery behind
        :py:meth:`_named_type_from_arg_info` for return shapes the shared
        consultor cannot report: nested type args (#1053, blanked for
        discovery lockstep) and bare alias returns (#1071, no type args to
        report at all).  ``None`` for anything else — non-calls, generic
        fns (their declared return is over their OWN type vars), builtins,
        and unresolvable return TypeExprs — so callers keep the loud skip.
        """
        if (not isinstance(expr, ast.FnCall)
                or expr.name in self._generic_fn_info):
            return None
        ret_te = self._fn_ret_type_exprs.get(expr.name)
        if ret_te is None:
            return None
        return self._canonical_named_type(ret_te)

    def _arg_named_type_deep(self, arg: ast.Expr) -> ast.NamedType | None:
        """Resolve a type-variable-element builtin argument's value
        ``NamedType`` to full depth.  A ``FnCall`` argument goes through
        :py:meth:`_builtin_call_ret_named_type` — the shared consultor first,
        then the per-class derivation in
        :py:meth:`_typevar_elem_builtin_ret_named_type` — so an inner
        type-variable-element builtin (``array_reverse(array_reverse(x))``,
        ``array_reverse(map_values(m))``, ``array_flatten(array_reverse(x))``)
        resolves rather than dropping the enclosing index.  Every other
        argument shape (``SlotRef``, ``ArrayLit``, ``ConstructorCall``) goes
        through the shared consultor directly, so alias- and literal-spelled
        arguments resolve exactly as before.  Routing a ``FnCall`` through
        :py:meth:`_builtin_call_ret_named_type` can only add resolutions — it
        tries the same consultor first — and recursion is bounded by the
        argument's call-nesting depth (each step strips one ``FnCall`` layer).
        A ``Block``-wrapped argument (``array_reverse({ array_reverse(x) })``)
        resolves via its tail expression, matching the container emissions'
        Block handling (#1071).
        """
        while isinstance(arg, ast.Block):
            arg = arg.expr
        if isinstance(arg, ast.FnCall):
            return self._builtin_call_ret_named_type(arg)
        return self._named_type_from_arg_info(arg)

    def _typevar_elem_builtin_ret_named_type(
        self, call: ast.FnCall,
    ) -> ast.NamedType | None:
        """#1051: derive the return ``NamedType`` of a type-variable-element
        Array-returning builtin from its arguments, per mechanism class.  Any
        argument shape that cannot be resolved yields ``None`` — the caller
        then keeps the loud [E602] skip rather than guessing an element type.

        Arguments are resolved by :py:meth:`_arg_named_type_deep`: a ``SlotRef``
        array/container argument and a *consultor-resolvable* builtin call
        (``array_concat`` / ``array_range`` / …) resolve through the shared
        consultor, and an argument that is itself a type-variable-element
        builtin (``array_reverse(array_reverse(x))``,
        ``array_reverse(map_values(m))``, ``array_flatten(array_reverse(x))``)
        resolves by recursing through :py:meth:`_builtin_call_ret_named_type`
        back into this per-class derivation.
        """
        name = call.name
        args = call.args
        # ---- Class 1: argument-forwarding --------------------------------
        # array_reverse(Array<T>) and array_sort_by(Array<T>, cmp) return
        # arg0's type verbatim; array_flatten(Array<Array<T>>) returns arg0's
        # type with one Array<> layer unwrapped.
        if name in ("array_reverse", "array_sort_by") and args:
            return self._arg_named_type_deep(args[0])
        if name == "array_flatten" and args:
            outer = self._arg_named_type_deep(args[0])
            if (outer is not None and outer.name == "Array"
                    and outer.type_args
                    and isinstance(outer.type_args[0], ast.NamedType)):
                return outer.type_args[0]
            return None
        # ---- Class 2: container-arg-derived ------------------------------
        # map_keys(Map<K, V>) -> Array<K>; map_values(Map<K, V>) -> Array<V>;
        # set_to_array(Set<T>) -> Array<T>.
        if name in ("map_keys", "map_values", "set_to_array") and args:
            container = self._arg_named_type_deep(args[0])
            # #1068: verify the resolved argument type IS the expected
            # container before reading K/V/T off its type args.  The
            # rebuilder resolves alias spellings (including a generic
            # alias's substitution through its target), so a well-formed
            # aliased argument arrives here named `Map`/`Set`; anything
            # else must not have its args consumed positionally — a
            # `("MyMap", ("Int",))` read K = Int where the target says
            # String, deriving an element type the emission contradicts
            # (a validation-failing module behind a clean `vera compile`).
            expected = "Set" if name == "set_to_array" else "Map"
            if (container is None or container.name != expected
                    or not container.type_args):
                return None
            if name == "map_values":
                if len(container.type_args) < 2:
                    return None
                elem = container.type_args[1]
            else:
                elem = container.type_args[0]
            if isinstance(elem, ast.NamedType):
                return ast.NamedType(name="Array", type_args=(elem,))
            return None
        # ---- Class 3: closure-return-derived -----------------------------
        # array_map(Array<A>, fn(A -> B)) and
        # array_mapi(Array<A>, fn(A, Nat -> B)) return Array<B>; B is the
        # closure argument's declared return type.
        if name in ("array_map", "array_mapi") and len(args) >= 2:
            ret_te = self._closure_arg_return_type(args[1])
            if ret_te is not None:
                elem_nt = self._canonical_named_type(ret_te)
                if elem_nt is not None:
                    return ast.NamedType(name="Array", type_args=(elem_nt,))
            return None
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
        if type_name in self._alias_env.aliases:
            target = self._alias_env.aliases[type_name]
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
        if isinstance(expr, ast.ArrayLit):
            # #913: an array literal matched against an `Array<T>` formal must
            # expose its element type so `T` binds from THIS argument.  Mirrors
            # the discovery-side `Monomorphizer._get_arg_type_info` ArrayLit
            # branch (vera/monomorphize.py) — without it, the WASM call-rewrite
            # consultor left `T` unbound for `map_ident([1, 2, 3])`, fell to the
            # phantom-var `Bool` default, and mangled the call to
            # `map_ident$Bool` while discovery emitted `map_ident$Int` — a
            # dangling reference that dropped the enclosing fn.
            # #769 gap 2: FULL-DEPTH element name (nested literal /
            # constructor element), mirroring the discovery-side
            # `_array_elem_type_name` exactly — element-name granularity is
            # part of the clone-name agreement contract (#772), so the two
            # sides must move together.
            if expr.elements:
                elem = expr.elements[0]
                elem_type: str | None = None
                elem_info = self._get_arg_type_info_wasm(elem)
                if elem_info is not None:
                    outer, args = elem_info
                    if args and all(a is not None for a in args):
                        joined = ", ".join(a for a in args if a is not None)
                        elem_type = f"{outer}<{joined}>"
                if elem_type is None:
                    elem_type = self._infer_vera_type(elem)
                if elem_type:
                    return ("Array", (elem_type,))
            return ("Array", ())
        if isinstance(expr, ast.FnCall):
            # #878: a call whose result is itself a parameterized type
            # (`Option<Decimal>`, `Array<Int>`) matched against a
            # parameterized formal (`Option<VeraT>`) must expose its type
            # args so the type var binds from THIS argument.  Mirrors the
            # discovery-side `Monomorphizer._get_arg_type_info` FnCall branch
            # (vera/monomorphize.py) so the WASM call-rewrite consultor and
            # instantiation discovery agree on the concrete instantiation.
            # Without it, `option_unwrap_or(decimal_div(a, b), …)` bound
            # nothing from arg0 and fell through to the phantom-var default.
            # Gated on non-registration, mirroring the discovery side: a
            # registered name may be a user override of an E151-exempt
            # prelude combinator (#815) whose declared return must win
            # (adversarial panel, PR #972).
            if expr.name not in self._fn_ret_types:
                param_ret = _BUILTIN_PARAMETERIZED_RETURNS.get(expr.name)
                if param_ret is not None:
                    return param_ret
            if expr.name in ("array_concat", "array_append",
                             "array_slice", "array_filter"):
                if expr.args:
                    return self._get_arg_type_info_wasm(expr.args[0])
            # User-fn call returning a parameterized type: read the declared
            # return TypeExpr (registered by `_register_fn`).  A NON-generic
            # user helper returning `Option<Decimal>` in `Option<VeraT>`
            # position resolves `VeraT = Decimal` here — the user-fn half of
            # #878, symmetric with the builtin table above.
            #
            # A GENERIC call (`option_map(None, …)` → `Option<B>`) is excluded:
            # its declared return type is parameterized over the callee's OWN
            # type vars (`B`), not concrete types, so its type args would bind
            # a phantom `B` here.  Such calls fall through to the generic-return
            # resolution in `_infer_fncall_vera_type` instead, and the outer
            # generic then binds from another argument (e.g. the `0` default) —
            # exactly as instantiation discovery does (its FnCall branch has no
            # user-generic case either, so the two consultors stay in lockstep).
            if expr.name in self._generic_fn_info:
                return None
            ret_te = self._fn_ret_type_exprs.get(expr.name)
            if isinstance(ret_te, ast.RefinementType):
                ret_te = ret_te.base_type
            if (isinstance(ret_te, ast.NamedType)
                    and ret_te.type_args):
                ta_names: list[str | None] = []
                for ta in ret_te.type_args:
                    if isinstance(ta, ast.NamedType) and not ta.type_args:
                        ta_names.append(self._format_named_type(ta))
                    else:
                        ta_names.append(None)
                return (ret_te.name, tuple(ta_names))
        return None

    def _closure_arg_return_type(
        self, closure_arg: ast.Expr,
    ) -> ast.TypeExpr | None:
        """Declared return TypeExpr of the closure an ``apply_fn`` applies.

        The mixin-side shape dispatch shared by both inference consultors
        (``_infer_apply_fn_return_type`` — the ``call_indirect`` signature
        — and ``_infer_fncall_vera_type``'s ``apply_fn`` arm — the
        Vera-type inference).  A ``SlotRef`` is resolved through the shared
        :func:`resolve_fn_type_alias`, which follows the alias chain
        **transitively** to the terminal ``FnType`` (``type Fetcher =
        InnerFetcher;`` — #867) and substitutes any generic alias's type
        params from the slot's bound type args; an inline ``AnonFn`` yields
        its declared return type directly.  Any other shape yields
        ``None``.

        This is the same resolution the fused-await classifier's
        ``_apply_fn_closure_ret_type`` (``vera/wasm/async_fusion.py``)
        performs — both route the ``SlotRef`` through
        :func:`resolve_fn_type_alias`, so the signature this builds and
        the classification that gates the runtime fused-handle check can
        never consult a differently-resolved return type.
        """
        if isinstance(closure_arg, ast.SlotRef):
            fn_type = resolve_fn_type_alias(
                ast.NamedType(
                    name=closure_arg.type_name,
                    type_args=closure_arg.type_args,
                ),
                self._alias_env.aliases,
                self._alias_env.alias_params,
            )
            return fn_type.return_type if fn_type is not None else None
        if isinstance(closure_arg, ast.AnonFn):
            return closure_arg.return_type
        return None

    def _closure_arg_param_types(
        self, closure_arg: ast.Expr,
    ) -> tuple[ast.TypeExpr, ...] | None:
        """Declared *parameter* TypeExprs of the closure an ``apply_fn`` applies
        (#820) — the formal-type recovery the @Nat -> @Int argument widening
        guard needs, the parameter dual of :py:meth:`_closure_arg_return_type`.

        A ``SlotRef`` is resolved through the shared
        :func:`resolve_fn_type_alias` (transitively to the terminal ``FnType``),
        an inline ``AnonFn`` yields its declared params directly; any other
        shape yields ``None``.  The closure *return* direction (widening #820,
        narrowing #984) is handled separately — those gates read the
        ``AnonFn``'s own ``return_type`` in ``_compile_lifted_closure``, not a
        recovered formal — so this argument-side recovery stands alone.
        """
        if isinstance(closure_arg, ast.SlotRef):
            fn_type = resolve_fn_type_alias(
                ast.NamedType(
                    name=closure_arg.type_name,
                    type_args=closure_arg.type_args,
                ),
                self._alias_env.aliases,
                self._alias_env.alias_params,
            )
            return tuple(fn_type.params) if fn_type is not None else None
        if isinstance(closure_arg, ast.AnonFn):
            return tuple(closure_arg.params)
        return None

    def _type_expr_base_is_int(self, te: ast.TypeExpr) -> bool:
        """True iff *te* resolves (through aliases / refinements) to ``@Int``
        (#820).  Alias-aware (`type Age = Int`), so a closure formal declared
        with an @Int alias is guarded like a bare @Int.  Deliberately narrow —
        a @Nat / generic / other formal is not @Int and must not be guarded."""
        name = self._type_expr_to_slot_name(te)
        if name is None:
            return False
        return self._resolve_base_type_name(name) == "Int"

    def _type_expr_base_is_nat(self, te: ast.TypeExpr) -> bool:
        """True iff *te* resolves (through aliases) to ``@Nat`` (#984) — the
        narrowing dual of :py:meth:`_type_expr_base_is_int`.  Alias-aware
        (`type Count = Nat`), so a closure return declared with a @Nat alias is
        guarded like a bare @Nat.  A refinement over @Nat also resolves to
        ``Nat`` here; the closure-return narrow gate additionally excludes
        refinements (`_refinement_guard_parts`), leaving them to the refinement
        boundary path, exactly as the top-level narrow-return gate does."""
        name = self._type_expr_to_slot_name(te)
        if name is None:
            return False
        return self._resolve_base_type_name(name) == "Nat"

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
            site like a user `MapFn<Int, String>`).
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
        ret_te = self._closure_arg_return_type(closure_arg)
        if ret_te is not None:
            return self._canonical_wasm_type(ret_te)
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
        """Extract a simple type name from a TypeExpr.

        Delegates to :func:`vera.naming.slot_name` (#1208) so a closure's
        parameter-count keys (`param_type_counts`) use the same name that
        `_translate_slot_ref` / `_walk_free_vars` resolve against — and that
        the checker bound the slot under.
        """
        return naming.slot_name_or_none(te, self._alias_env)

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
        """The slot-binding name of *te*, as the checker binds it (#1208).

        Delegates to :func:`vera.naming.slot_name` against this context's
        alias environment: syntactic head, RESOLVED type arguments, so a
        parameter written ``@Option<Cnt>`` keys the ``Option<Int>`` stack the
        checker created and the reference side (``naming.slot_ref_key``)
        looks up.  Nested composites stay fully qualified (#914 finding 2).
        """
        return naming.slot_name_or_none(te, self._alias_env)

    def _family_name(self, te: ast.TypeExpr) -> str:
        """The ``State<T>``/``Exn<E>`` host-import/tag FAMILY name for a
        type argument (#1209) — :func:`vera.naming.family_name` over this
        context's alias environment, so the family names the CELL the
        checker typed.  Every spelling that resolves to one cell (a scalar
        alias, #1205; a composite or parameterised alias, #1209) is one
        import and one tag; only :func:`vera.slots.family_fallback_name`'s
        residue stays syntactic.  The env is the DECLARING module's
        (``set_alias_env``), so a name means what it meant where it was
        written."""
        return naming.family_name(
            te, self._alias_env, family_fallback_name(te))

    def _family_base(self, te: ast.TypeExpr) -> str:
        """The same cell's REPRESENTATION name (#1218).

        :func:`vera.naming.family_base_name` over this context's alias
        environment: the family with its refinements stripped, which is what
        decides i32/i64/f64/pair, pointer-ness for the GC shadow stack, and
        which #1203 write guard applies.  A refined cell has its OWN family
        (that is #1218) and its BASE's representation, so the two names are
        derived side by side at every handle site and never substituted for
        each other — this one is never a symbol and never compared against
        another cell's."""
        return naming.family_base_name(
            te, self._alias_env, family_fallback_name(te))

    def _boundary_base(self, te: ast.TypeExpr) -> str:
        """The REPRESENTATION base name of a declared WRITE boundary (#1256).

        ONE derivation for every #1212 marking site that holds a type
        expression — the named and closure RETURN, the ``apply_fn``
        argument, the ``throw`` payload.  Composes the two hops each site
        used to spell for itself: :meth:`_family_base` resolves the type
        expression to its representation (an alias chased, a refinement
        stripped), and :meth:`_resolve_base_type_name` chases the one
        residue that can survive it — :func:`vera.slots.family_fallback_name`
        returns a syntactic name when the resolution reaches a function or
        unknown type.  ``_translate_handle_exn`` already wrote exactly this
        composition; the return boundary wrote a different one (slot name
        then resolve), which is two derivations of one fact and the shape
        #1213 is about.

        Never a cell IDENTITY: a refined boundary and its base share a
        width and share this answer, which is the whole point.
        """
        return self._resolve_base_type_name(self._family_base(te))

    def _state_effect_family(self, effect_ref: ast.EffectRefNode) -> str:
        """The cell FAMILY named by a ``State<T>`` effect REFERENCE (#1209).

        The one derivation behind ``old(State<T>)`` and ``new(State<T>)``:
        the snapshot map (``_collect_old_types``) and the import registry
        (``_state_types``) are keyed by the family, so a read that named the
        reference any other way misses a registered entry and the
        ``old(State<T>)`` lowering raises (#914 finding 1).  Naming it here,
        once, is what keeps the three call sites from re-deriving it three
        ways.  Shape validation belongs to
        :func:`~vera.wasm.helpers.state_type_arg`, which raises for anything
        that is not a one-argument ``State``.
        """
        return self._family_name(state_type_arg(effect_ref))

    def _state_effect_family_base(
        self, effect_ref: ast.EffectRefNode,
    ) -> str:
        """The REPRESENTATION name of the cell a ``State<T>`` effect
        reference denotes (#1218) — :meth:`_state_effect_family`'s twin over
        :meth:`_family_base`, for the width decisions rather than the
        registry lookups."""
        return self._family_base(state_type_arg(effect_ref))

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
        if name not in self._alias_env.aliases:
            # Not an alias — this is the underlying base name.
            return name
        _seen = _seen | {name}
        alias = self._alias_env.aliases[name]
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

    def _ref_type_name_wasm_type(
        self,
        type_name: str,
        type_args: tuple[ast.TypeExpr, ...] | None = None,
        _seen: frozenset[str] = frozenset(),
    ) -> str | None:
        """Map a slot/result ref's ``type_name`` to its WAT stack type.

        The result-value type of a ``SlotRef`` or ``ResultRef``: ``"i64"`` for
        Int/Nat, ``"f64"`` for Float64, ``"i32"`` for Bool/Byte and pointer-
        represented types (ADTs, Decimal/Map/Set handles, closure pointers),
        ``"i32_pair"`` for the two-word String/Array representation, or ``None``
        for Unit / unknown.

        Shared by the ``SlotRef`` and ``ResultRef`` arms of
        :meth:`_infer_expr_wasm_type` so a monomorphized clone's
        ``@T.result`` and ``@T.0`` — which carry the *same* concrete
        ``type_name`` after substitution — agree on their WAT type.  Before
        #891 the ResultRef arm inferred only the scalar primitives, so an
        ADT-bound return defaulted to ``None`` and the postcondition equality
        compared two i32 heap pointers with ``i64.eq`` (a WASM validation
        trap).

        An alias is canonicalized to its target's FULL compound spelling
        first (the shared :meth:`_canonicalize_alias_slot_name` walk,
        #1054): the name-only ``_resolve_base_type_name`` hop drops type
        arguments, so ``type FA = Future<Option<Int>>`` resolved to bare
        ``"Future"`` and — since an alias-spelled slot ref carries no AST
        ``type_args`` — missed the Future arm below, E602-skipping the
        scrutinee and constructor-argument sites the direct spelling
        compiles.  The string-form Future arm below handles the
        canonicalized compound spelling, mirroring
        ``_slot_name_to_wasm_type``; the alias analog of #1046, in the last
        mapper of the family without the canonicalizer."""
        type_name, _seen = self._canonicalize_alias_slot_name(type_name, _seen)
        resolved = self._resolve_base_type_name(type_name)
        if resolved in ("Int", "Nat"):
            return "i64"
        if resolved == "Float64":
            return "f64"
        if resolved in ("Bool", "Byte"):
            return "i32"
        if self._is_pair_type_name(resolved):
            return "i32_pair"
        # Future<T> is WASM-transparent — same representation as its single type
        # argument.  Mirrors `_slot_name_to_wasm_type`'s string-form Future arm
        # and `_named_type_to_wasm`'s canonical-walk Future arm; this SlotRef /
        # ResultRef mapper was the odd one out that lacked it, so a
        # `match await(@Future<T>.0) { ... }` scrutinee — whose `await` FnCall
        # arm of `_infer_expr_wasm_type` delegates to this mapper on the
        # `@Future<T>` slot ref — inferred None and E602-skipped the enclosing
        # function on a check/verify-green program (#1038).  Delegating to
        # `_canonical_wasm_type` lowers the inner type through the same walk the
        # let-binding path uses, so a scalar inner (Future<Int> -> i64), an ADT
        # inner (Future<Option<Int>>, Future<UserADT> -> i32), and a pair inner
        # (Future<String> -> i32_pair) all map correctly here.  (A Future<String>
        # *scrutinee* stays blocked upstream by the separate `let @Future<String>`
        # pair-binding gap, so this mapper fix alone doesn't reach it end-to-end.)
        if resolved == "Future" and type_args and len(type_args) == 1:
            return self._canonical_wasm_type(type_args[0])
        # String-form dual of the arm above (#1054): an alias-canonicalized
        # spelling arrives as the full compound STRING ("Future<Option<Int>>")
        # with no AST type_args — strip the wrapper and recurse on the payload
        # spelling, exactly like _slot_name_to_wasm_type's Future arm.
        if resolved.startswith("Future<") and resolved.endswith(">"):
            return self._ref_type_name_wasm_type(resolved[7:-1], None, _seen)
        base = resolved.split("<")[0] if "<" in resolved else resolved
        # Opaque handle types — i32 handles managed by host runtime
        if base in ("Decimal", "Map", "Set"):
            return "i32"
        if base in self._adt_type_names:
            return "i32"
        # Function type aliases → i32 (closure pointer).  Resolved through the
        # shared transitive resolver so an alias chain (`type MyFn = InnerFn;`,
        # #867 / PR #880) classifies the same as a direct FnType alias — the
        # depth-1 behaviour is unchanged (a direct alias resolves in one hop).
        if resolve_fn_type_alias(
            ast.NamedType(name=type_name, type_args=type_args),
            self._alias_env.aliases,
            self._alias_env.alias_params,
        ) is not None:
            return "i32"
        return None

    def _canonicalize_alias_slot_name(
        self, name: str, _seen: frozenset[str] = frozenset(),
    ) -> tuple[str, frozenset[str]]:
        """Resolve an alias slot name to its target's FULL compound spelling.

        Hop by hop through alias-of-alias chains (``FUB -> FUA ->
        Future<UA>``), keeping type arguments intact — unlike
        ``_resolve_base_type_name``, which recurses on the target's NAME only
        and drops them (``type FU = Future<Unit>`` resolved to ``"Future"`` —
        PR #1035 review; ``type FI = Future<Int>`` likewise — #1037).  The
        shared walk under ``_slot_name_erases_to_unit`` and
        ``_slot_name_to_wasm_type``, so the zero-size test and the WAT-type
        mapper canonicalize identically: an alias behaves exactly like
        writing its target's spelling directly.

        After the top-level hops, an alias sitting INSIDE a transparent
        ``Future<…>`` payload is canonicalized too (``Future<FlagA>`` ->
        ``Future<Bool>``, #1074) — the hop-by-hop walk resolves only the
        outer NAME, so the four array-element-type deciders that route the
        result to the module-level element-size / store-op helpers
        (``_infer_concat_elem_type``, ``_translate_array_lit``, the
        ``array_flatten`` inner walk, ``_infer_index_element_type``) get a
        payload the size dict can key on, not a bare alias that falls to the
        4-byte i32 default.

        Returns the canonical name plus the accumulated seen-set; callers
        whose own recursion re-enters this walk (the transparent
        ``Future<...>`` payload peel) thread it through so a self-referential
        type argument (``type F = Future<F>``) terminates.  Alias cycles are
        a user-facing E132 upstream — the cut here is defence-in-depth,
        matching ``_resolve_base_type_name``.  A non-alias name, or an alias
        whose target has no nameable slot form, is returned unchanged for
        the caller's own fallthrough handling.
        """
        while name in self._alias_env.aliases and name not in _seen:
            target = type_expr_slot_name(self._alias_env.aliases[name])
            if target is None or target == name:
                break
            _seen = _seen | {name}
            name = target
        # #1074: recurse into a representation-transparent ``Future<…>``
        # payload so an alias sitting INSIDE the wrapper is canonicalized
        # too (``Future<FlagA>`` -> ``Future<Bool>``, ``type BigF =
        # Future<Big>`` -> ``Future<Int>``).  The hop-by-hop walk above
        # resolves only a top-level alias NAME (or an alias chain landing
        # on a ``Future<…>`` compound); the payload spelling it terminates
        # on is left verbatim.  An aliased payload therefore reached the
        # module-level element-size / store-op deciders unresolved (they
        # ``_strip_future`` the wrapper and hand the bare alias to a
        # name-keyed size dict with no alias table) and fell to the 4-byte
        # i32 default — a 4-byte stride over 1-byte-packed Bool/Byte
        # (silent-wrong values) or an ``i32.store`` of an i64/pair payload
        # (a WASM-validation trap behind an exit-0 compile).  Thread
        # ``_seen`` through so a self-referential payload (``type F =
        # Future<F>``) still terminates.
        if name.startswith("Future<") and name.endswith(">"):
            inner = name[len("Future<"):-1]
            inner, _seen = self._canonicalize_alias_slot_name(inner, _seen)
            name = f"Future<{inner}>"
        return name, _seen

    def _slot_name_to_wasm_type(
        self, name: str, _seen: frozenset[str] = frozenset(),
    ) -> str | None:
        """Map a slot type name to a WAT type string.

        An alias is canonicalized to its target's full compound spelling
        first (the shared :meth:`_canonicalize_alias_slot_name` walk): the
        prior name-only ``_resolve_base_type_name`` hop dropped type
        arguments, so an alias TO a compound transparent wrapper (``type FI
        = Future<Int>``) resolved to bare ``"Future"``, matched no branch,
        and returned ``None`` — E602-skipping the enclosing function of a
        destructure / match / let binding on a check+verify-green program
        (#1037; the zero-size dual of the same disease was PR #1035's
        review finding), while the direct ``Future<Int>`` spelling
        compiled.  Canonicalizing makes an alias map exactly like its
        target written directly.
        """
        name, _seen = self._canonicalize_alias_slot_name(name, _seen)
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
            return self._slot_name_to_wasm_type(inner, _seen)
        # Map/Set/Decimal are opaque host-import handles (i32)
        if name.startswith("Map<") or name.startswith("Set<") or name == "Decimal":
            return "i32"
        # ADT types are heap pointers
        base = name.split("<")[0] if "<" in name else name
        if base in self._adt_type_names:
            return "i32"
        # Function type aliases are closure pointers (i32) — resolved
        # **transitively** through the shared resolver (#867 / PR #880
        # 4th site) so a refinement-wrapped (`type Foo = { @fn(...) | p }`)
        # or chained-through-a-refinement fn alias classifies as a
        # closure, not `None`.  Without this the let/param binding is
        # rejected with `CodegenSkip` and its whole function is dropped
        # ("has no WASM representation"), on a check/verify-green program.
        # A plain `NamedType` chain (`type Foo = Bar;` where `Bar` is a
        # bare `FnType`) is already collapsed to `Bar` by the
        # `_resolve_base_type_name` call above; the resolver additionally
        # covers the refinement-peeling and generic-alias hops that walk
        # cannot.  The `name` string may carry type args for a generic
        # alias (`Mapper<Int>`); the resolver keys on `base` and
        # substitutes at each hop.
        if resolve_fn_type_alias(
            ast.NamedType(name=base, type_args=None),
            self._alias_env.aliases,
            self._alias_env.alias_params,
        ) is not None:
            return "i32"
        # Bare "Fn" for anonymous function types
        if name == "Fn":
            return "i32"
        return None

    def _slot_name_erases_to_unit(
        self, name: str, _seen: frozenset[str] = frozenset(),
    ) -> bool:
        """True if a slot type name is *zero-size* — no WASM representation.

        Zero-size means ``Unit``, or a transparent ``Future<…>`` whose payload
        is itself zero-size (``Future<Unit>``, ``Future<Future<Unit>>``, …).
        This is the slot-name mirror of :func:`vera.types.erases_to_unit` and
        codegen's ``_type_expr_to_wasm_type`` (``Future<T>`` is
        representation-identical to ``T`` — #841), and it follows the same
        ``Future<…>`` recursion as :meth:`_slot_name_to_wasm_type`.

        An alias is canonicalized to its target's **full compound spelling**
        first (the shared :meth:`_canonicalize_alias_slot_name` walk, hop by
        hop for chains, cycle-cut by ``_seen``) — NOT through
        ``_resolve_base_type_name``, which recurses on the target's name only
        and drops type arguments (``type FU = Future<Unit>`` resolved to
        ``"Future"``, missed the ``Future<…>`` branch, and E602-skipped the
        function on a check+verify-green program; PR #1035 review).  The
        seen-set threads through the ``Future<…>`` recursion so a
        self-referential type argument also terminates, and the
        ``_resolve_base_type_name`` fallthrough still handles what the
        canonicalizer cannot name (a no-op for non-aliases).

        Distinct from ``_slot_name_to_wasm_type(name) is None``: that predicate
        ALSO fires for genuinely unrepresentable types (an unknown ADT, a bare
        type variable), which are a real codegen gap that must still ``CodegenSkip``
        rather than silently erase.  The declaration-position guards need to tell
        "erase this zero-size field" apart from "skip — cannot represent", so
        they key on THIS check, not on ``_slot_name_to_wasm_type`` being ``None``
        (#1031: the guards previously compared the bare string ``"Unit"``, so a
        ``Future<Unit>`` component missed the zero-size branch and skipped the
        whole function on a check-green program).
        """
        name, _seen = self._canonicalize_alias_slot_name(name, _seen)
        name = self._resolve_base_type_name(name)
        if name == "Unit":
            return True
        if name.startswith("Future<") and name.endswith(">"):
            return self._slot_name_erases_to_unit(name[7:-1], _seen)
        return False
