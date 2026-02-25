"""Vera WASM translation layer — AST to WAT bridge.

Translates Vera AST expressions into WebAssembly Text format (WAT)
instructions for compilation to WASM binary.  Manages slot environments,
local variable allocation, string pool, and instruction generation.

See spec/11-compilation.md for the compilation specification.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from vera import ast

if TYPE_CHECKING:
    from vera.codegen import ConstructorLayout
from vera.types import (
    BOOL,
    FLOAT64,
    FunctionType,
    INT,
    NAT,
    STRING,
    UNIT,
    PrimitiveType,
    Type,
    base_type,
)


# =====================================================================
# Slot environment — De Bruijn → WASM local mapping
# =====================================================================

@dataclass
class WasmSlotEnv:
    """Maps Vera typed De Bruijn indices to WASM local indices.

    Mirrors SlotEnv in smt.py.  Maintains a stack per type name.
    Index 0 = most recent binding (last element in the list),
    matching De Bruijn convention.
    """

    _stacks: dict[str, list[int]] = field(default_factory=dict)

    def resolve(self, type_name: str, index: int) -> int | None:
        """Look up @Type.index → WASM local index."""
        stack = self._stacks.get(type_name, [])
        pos = len(stack) - 1 - index
        if 0 <= pos < len(stack):
            return stack[pos]
        return None

    def push(self, type_name: str, local_idx: int) -> WasmSlotEnv:
        """Return a new environment with *local_idx* pushed for *type_name*."""
        new_stacks = {k: list(v) for k, v in self._stacks.items()}
        new_stacks.setdefault(type_name, []).append(local_idx)
        return WasmSlotEnv(new_stacks)


# =====================================================================
# String pool — deduplicated string constants
# =====================================================================

@dataclass
class StringPool:
    """Manages string literal constants in the WASM data section.

    Deduplicates identical strings and tracks their offsets in
    linear memory.
    """

    _strings: dict[str, tuple[int, int]] = field(default_factory=dict)
    _offset: int = 0

    def intern(self, value: str) -> tuple[int, int]:
        """Return (offset, length) for a string, deduplicating."""
        if value in self._strings:
            return self._strings[value]
        encoded = value.encode("utf-8")
        entry = (self._offset, len(encoded))
        self._strings[value] = entry
        self._offset += len(encoded)
        return entry

    def entries(self) -> list[tuple[str, int, int]]:
        """Return all (value, offset, length) sorted by offset."""
        return [
            (value, offset, length)
            for value, (offset, length) in sorted(
                self._strings.items(), key=lambda x: x[1][0]
            )
        ]

    def has_strings(self) -> bool:
        """Whether any strings have been interned."""
        return len(self._strings) > 0

    @property
    def heap_offset(self) -> int:
        """First byte after all string data — heap starts here."""
        return self._offset


# =====================================================================
# Alignment helper
# =====================================================================


def _align_up(offset: int, align: int) -> int:
    """Round offset up to the next multiple of align."""
    return (offset + align - 1) & ~(align - 1)


# =====================================================================
# Type mapping
# =====================================================================

def wasm_type(t: Type) -> str | None:
    """Map a Vera type to a WAT type string.

    Returns None for types with no WASM representation (Unit).
    Returns "unsupported" for types that cannot be compiled.
    """
    t = base_type(t)
    if isinstance(t, PrimitiveType):
        if t.name in ("Int", "Nat"):
            return "i64"
        if t.name in ("Float64", "Float"):
            return "f64"
        if t.name == "Bool":
            return "i32"
        if t.name == "Unit":
            return None
        if t.name == "String":
            return "unsupported"  # handled specially in 5e
    if isinstance(t, FunctionType):
        return "i32"  # closure pointer (heap-allocated struct)
    return "unsupported"


def wasm_type_or_none(t: Type) -> str | None:
    """Map a Vera type to a WAT type string, returning None for
    both Unit (no representation) and unsupported types."""
    wt = wasm_type(t)
    if wt == "unsupported":
        return None
    return wt


def is_compilable_type(t: Type) -> bool:
    """Check if a type can be compiled to WASM."""
    return wasm_type(t) != "unsupported"


# =====================================================================
# WASM context — instruction generation
# =====================================================================

class WasmContext:
    """Generates WAT instructions for a single function body.

    Manages local variable allocation and dispatches expression
    translation.  Mirrors SmtContext in smt.py.
    """

    def __init__(
        self,
        string_pool: StringPool,
        effect_ops: dict[str, tuple[str, bool]] | None = None,
        ctor_layouts: dict[str, ConstructorLayout] | None = None,
        adt_type_names: set[str] | None = None,
        generic_fn_info: (
            dict[str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]] | None
        ) = None,
        ctor_to_adt: dict[str, str] | None = None,
    ) -> None:
        self.string_pool = string_pool
        self._next_local: int = 0
        self._locals: list[tuple[str, str]] = []  # (name, wat_type)
        self._result_local: int | None = None
        # Effect operation mapping: op_name -> (wasm_call_target, is_void)
        # e.g. {"get": ("$vera.state_get_Int", False),
        #        "put": ("$vera.state_put_Int", True)}
        self._effect_ops = effect_ops or {}
        # Constructor layout mapping: ctor_name -> ConstructorLayout
        self._ctor_layouts: dict[str, ConstructorLayout] = ctor_layouts or {}
        # ADT type names for slot/param type resolution
        self._adt_type_names: set[str] = adt_type_names or set()
        # Generic function info for call rewriting:
        # fn_name -> (forall_vars, param_type_exprs)
        self._generic_fn_info: dict[
            str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]
        ] = generic_fn_info or {}
        # Constructor name → ADT name reverse mapping
        self._ctor_to_adt: dict[str, str] = ctor_to_adt or {}
        # Function return WASM types for type inference:
        # fn_name → return_wasm_type (str | None)
        self._fn_ret_types: dict[str, str | None] = {}
        # Closure compilation state — accumulated during translation
        # Each entry: (anon_fn, captures, closure_id)
        # captures: list of (type_name, outer_de_bruijn, wasm_type)
        self._pending_closures: list[
            tuple[ast.AnonFn, list[tuple[str, int, str]], int]
        ] = []
        # Type aliases: alias_name -> TypeExpr (for FnType resolution)
        self._type_aliases: dict[str, ast.TypeExpr] = {}
        # Closure signature registry: sig_key -> (type_name, param/result WAT)
        self._closure_sigs: dict[str, str] = {}
        # Next closure id (may be overwritten by codegen)
        self._next_closure_id: int = 0

    def set_fn_ret_types(
        self, ret_types: dict[str, str | None],
    ) -> None:
        """Set function return WASM types for FnCall type inference."""
        self._fn_ret_types = ret_types

    def set_type_aliases(
        self, aliases: dict[str, ast.TypeExpr],
    ) -> None:
        """Set type alias mappings for FnType resolution."""
        self._type_aliases = aliases

    def set_closure_id_start(self, start: int) -> None:
        """Set the starting closure ID for this context."""
        self._next_closure_id = start

    def set_result_local(self, local_idx: int) -> None:
        """Set the local index used for @T.result in postconditions."""
        self._result_local = local_idx

    def alloc_param(self) -> int:
        """Allocate a parameter slot (already in WASM signature).

        Returns the local index for this parameter.
        """
        idx = self._next_local
        self._next_local += 1
        return idx

    def alloc_local(self, wat_type: str) -> int:
        """Allocate a new local variable.  Returns local index."""
        idx = self._next_local
        name = f"$l{idx}"
        self._locals.append((name, wat_type))
        self._next_local += 1
        return idx

    def extra_locals_wat(self) -> list[str]:
        """Return WAT local declarations for non-parameter locals."""
        return [f"(local {name} {wt})" for name, wt in self._locals]

    # -----------------------------------------------------------------
    # Expression translation
    # -----------------------------------------------------------------

    def translate_expr(
        self, expr: ast.Expr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a Vera AST expression to WAT instructions.

        Returns a list of WAT instruction strings, or None if the
        expression contains unsupported constructs (function skipped).
        """
        if isinstance(expr, ast.IntLit):
            return [f"i64.const {expr.value}"]

        if isinstance(expr, ast.BoolLit):
            return [f"i32.const {1 if expr.value else 0}"]

        if isinstance(expr, ast.FloatLit):
            return [f"f64.const {expr.value}"]

        if isinstance(expr, ast.UnitLit):
            return []  # Unit produces no value on the stack

        if isinstance(expr, ast.SlotRef):
            return self._translate_slot_ref(expr, env)

        if isinstance(expr, ast.BinaryExpr):
            return self._translate_binary(expr, env)

        if isinstance(expr, ast.UnaryExpr):
            return self._translate_unary(expr, env)

        if isinstance(expr, ast.IfExpr):
            return self._translate_if(expr, env)

        if isinstance(expr, ast.Block):
            return self.translate_block(expr, env)

        if isinstance(expr, ast.FnCall):
            return self._translate_call(expr, env)

        if isinstance(expr, ast.QualifiedCall):
            return self._translate_qualified_call(expr, env)

        if isinstance(expr, ast.StringLit):
            return self._translate_string_lit(expr)

        if isinstance(expr, ast.ResultRef):
            return self._translate_result_ref()

        if isinstance(expr, ast.ConstructorCall):
            return self._translate_constructor_call(expr, env)

        if isinstance(expr, ast.NullaryConstructor):
            return self._translate_nullary_constructor(expr)

        if isinstance(expr, ast.MatchExpr):
            return self._translate_match(expr, env)

        if isinstance(expr, ast.AnonFn):
            return self._translate_anon_fn(expr, env)

        # Unsupported: handle,
        # quantifiers, old/new, assert/assume, arrays, etc.
        return None

    # -----------------------------------------------------------------
    # Slot references
    # -----------------------------------------------------------------

    def _translate_slot_ref(
        self, ref: ast.SlotRef, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate @Type.n to local.get."""
        type_name = ref.type_name
        if ref.type_args:
            # Parameterised type — build canonical name
            arg_names = []
            for ta in ref.type_args:
                if isinstance(ta, ast.NamedType):
                    arg_names.append(ta.name)
                else:
                    return None
            type_name = f"{ref.type_name}<{', '.join(arg_names)}>"
        local_idx = env.resolve(type_name, ref.index)
        if local_idx is None:
            return None
        return [f"local.get {local_idx}"]

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
        # MOD: WASM has no f64.rem — unsupported for floats
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

    def _translate_binary(
        self, expr: ast.BinaryExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate binary operators to WAT."""
        left = self.translate_expr(expr.left, env)
        right = self.translate_expr(expr.right, env)
        if left is None or right is None:
            return None

        op = expr.op
        ltype = self._infer_expr_wasm_type(expr.left)

        # Arithmetic
        if op in self._ARITH_OPS:
            if ltype == "f64":
                if op not in self._ARITH_OPS_F64:
                    return None  # MOD unsupported for f64
                return left + right + [self._ARITH_OPS_F64[op]]
            return left + right + [self._ARITH_OPS[op]]

        # Comparison — choose i32/i64/f64 based on operand types
        if op in self._CMP_OPS:
            rtype = self._infer_expr_wasm_type(expr.right)
            if ltype == "f64" or rtype == "f64":
                return left + right + [self._CMP_OPS_F64[op]]
            if ltype == "i32" and rtype == "i32":
                # Bool operands — use i32 comparison
                i32_op = self._CMP_OPS[op].replace("i64.", "i32.")
                return left + right + [i32_op]
            return left + right + [self._CMP_OPS[op]]

        # Boolean
        if op == ast.BinOp.AND:
            return left + right + ["i32.and"]
        if op == ast.BinOp.OR:
            return left + right + ["i32.or"]

        # IMPLIES: a ==> b  ≡  (not a) or b
        if op == ast.BinOp.IMPLIES:
            return left + ["i32.eqz"] + right + ["i32.or"]

        # Pipe — unsupported
        return None

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
            if expr.type_name in ("Int", "Nat"):
                return "i64"
            if expr.type_name in ("Float64", "Float"):
                return "f64"
            if expr.type_name == "Bool":
                return "i32"
            base = (expr.type_name.split("<")[0]
                    if "<" in expr.type_name else expr.type_name)
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
            if expr.type_name in ("Float64", "Float"):
                return "f64"
            if expr.type_name == "Bool":
                return "i32"
            return None
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
            return None
        return None

    def _infer_fncall_wasm_type(self, expr: ast.FnCall) -> str | None:
        """Infer the WASM return type of a function call.

        For generic calls, resolves the mangled name and looks up its
        registered return type.  For non-generic calls, uses the
        registered return type directly.  For apply_fn, infers from
        the closure's function type.
        """
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

    # -----------------------------------------------------------------
    # Unary operators
    # -----------------------------------------------------------------

    def _translate_unary(
        self, expr: ast.UnaryExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate unary operators to WAT."""
        operand = self.translate_expr(expr.operand, env)
        if operand is None:
            return None

        if expr.op == ast.UnaryOp.NOT:
            return operand + ["i32.eqz"]
        if expr.op == ast.UnaryOp.NEG:
            if self._infer_expr_wasm_type(expr.operand) == "f64":
                return operand + ["f64.neg"]
            return ["i64.const 0"] + operand + ["i64.sub"]
        return None

    # -----------------------------------------------------------------
    # Control flow
    # -----------------------------------------------------------------

    def _translate_if(
        self, expr: ast.IfExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate if-then-else to WASM if/else."""
        cond = self.translate_expr(expr.condition, env)
        then = self.translate_block(expr.then_branch, env)
        else_ = self.translate_block(expr.else_branch, env)
        if cond is None or then is None or else_ is None:
            return None

        # Determine result type from then branch
        # For now, assume the type is the same for both branches
        # We use the then_branch's last expression type
        result_type = self._infer_block_result_type(expr.then_branch)
        if result_type is None:
            # Unit result — no (result) annotation
            return (
                cond
                + ["if"]
                + ["  " + i for i in then]
                + ["else"]
                + ["  " + i for i in else_]
                + ["end"]
            )

        return (
            cond
            + [f"if (result {result_type})"]
            + ["  " + i for i in then]
            + ["else"]
            + ["  " + i for i in else_]
            + ["end"]
        )

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
            name = expr.type_name
            if name in ("Int", "Nat"):
                return "i64"
            if name in ("Float64", "Float"):
                return "f64"
            if name == "Bool":
                return "i32"
            base = name.split("<")[0] if "<" in name else name
            if base in self._adt_type_names:
                return "i32"
            return None
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
            return None  # effect ops return Unit (void)
        if isinstance(expr, ast.StringLit):
            return None  # strings are (i32, i32) — handled specially
        if isinstance(expr, ast.Block):
            return self._infer_block_result_type(expr)
        if isinstance(expr, ast.ConstructorCall):
            return "i32" if expr.name in self._ctor_layouts else None
        if isinstance(expr, ast.NullaryConstructor):
            return "i32" if expr.name in self._ctor_layouts else None
        if isinstance(expr, ast.MatchExpr):
            if expr.arms:
                return self._infer_expr_wasm_type(expr.arms[0].body)
            return None
        return None

    # -----------------------------------------------------------------
    # Blocks and statements
    # -----------------------------------------------------------------

    def translate_block(
        self, block: ast.Block, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a block: process statements, then final expression."""
        current_env = env
        instructions: list[str] = []

        for stmt in block.statements:
            if isinstance(stmt, ast.LetStmt):
                val_instrs = self.translate_expr(stmt.value, current_env)
                if val_instrs is None:
                    return None
                # Determine WAT type for this let binding
                type_name = self._type_expr_to_slot_name(stmt.type_expr)
                if type_name is None:
                    return None
                wat_t = self._slot_name_to_wasm_type(type_name)
                if wat_t is None:
                    return None
                local_idx = self.alloc_local(wat_t)
                instructions.extend(val_instrs)
                instructions.append(f"local.set {local_idx}")
                current_env = current_env.push(type_name, local_idx)
            elif isinstance(stmt, ast.ExprStmt):
                stmt_instrs = self.translate_expr(stmt.expr, current_env)
                if stmt_instrs is None:
                    return None
                instructions.extend(stmt_instrs)
                # Drop the value if the expression produces one.
                # QualifiedCalls (effect ops like IO.print) return void.
                # UnitLit produces nothing.
                if stmt_instrs and not self._is_void_expr(stmt.expr):
                    instructions.append("drop")
            else:
                # LetDestruct or unknown
                return None

        # Final expression
        expr_instrs = self.translate_expr(block.expr, current_env)
        if expr_instrs is None:
            return None
        instructions.extend(expr_instrs)
        return instructions

    # -----------------------------------------------------------------
    # Function calls
    # -----------------------------------------------------------------

    def _translate_call(
        self, call: ast.FnCall, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a function call to WASM call instruction.

        If the call name matches an effect operation (e.g. get/put for
        State<T>), redirects to the corresponding host import.
        """
        # Check if this is a closure application: apply_fn(closure, args...)
        if call.name == "apply_fn" and len(call.args) >= 2:
            return self._translate_apply_fn(call, env)

        # Check if this is an effect operation (e.g. get/put)
        if call.name in self._effect_ops:
            import_name, _is_void = self._effect_ops[call.name]
            instructions: list[str] = []
            for arg in call.args:
                arg_instrs = self.translate_expr(arg, env)
                if arg_instrs is None:
                    return None
                instructions.extend(arg_instrs)
            instructions.append(f"call {import_name}")
            return instructions

        # Resolve call target — rewrite generic calls to mangled names
        call_target = call.name
        if call.name in self._generic_fn_info:
            resolved = self._resolve_generic_call(call)
            if resolved is not None:
                call_target = resolved

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
        # Only IO effect operations are supported in C5
        instructions: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            instructions.extend(arg_instrs)
        instructions.append(f"call $vera.{call.name}")
        return instructions

    # -----------------------------------------------------------------
    # Generic call resolution
    # -----------------------------------------------------------------

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

        # Build mangled name
        parts = []
        for tv in forall_vars:
            if tv not in mapping:
                return None
            parts.append(mapping[tv])
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
            arg_info = self._get_arg_type_info_wasm(arg)
            if arg_info and arg_info[0] == param_te.name:
                for param_ta, arg_ta_name in zip(
                    param_te.type_args, arg_info[1]
                ):
                    if (isinstance(param_ta, ast.NamedType)
                            and param_ta.name in forall_vars
                            and param_ta.name not in mapping):
                        mapping[param_ta.name] = arg_ta_name

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
        return None

    def _infer_fncall_vera_type(self, call: ast.FnCall) -> str | None:
        """Infer Vera return type of a function call.

        For generic calls, resolves type args and substitutes into
        the return TypeExpr.  For non-generic calls, maps from WASM
        return type back to Vera type name.
        """
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
                if tv not in mapping:
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

    def _get_arg_type_info_wasm(
        self, expr: ast.Expr,
    ) -> tuple[str, tuple[str, ...]] | None:
        """Get (type_name, type_arg_names) for an argument expression."""
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
            # Infer from constructor args
            adt_name = self._ctor_to_adt_name(expr.name)
            if adt_name:
                arg_types = []
                for a in expr.args:
                    t = self._infer_vera_type(a)
                    if t:
                        arg_types.append(t)
                    else:
                        return None
                return (adt_name, tuple(arg_types))
        return None

    # -----------------------------------------------------------------
    # String literals
    # -----------------------------------------------------------------

    def _translate_string_lit(self, expr: ast.StringLit) -> list[str]:
        """Translate a string literal to (ptr, len) on the stack."""
        offset, length = self.string_pool.intern(expr.value)
        return [f"i32.const {offset}", f"i32.const {length}"]

    # -----------------------------------------------------------------
    # Closures — anonymous function compilation
    # -----------------------------------------------------------------

    def _translate_anon_fn(
        self, expr: ast.AnonFn, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate an anonymous function to a closure value (i32 pointer).

        Creates a heap-allocated closure struct:
          [func_table_idx: i32] [capture_0] [capture_1] ...

        Records the AnonFn for later lifting by codegen.py.
        """
        # Collect free variables (captures from enclosing scope)
        param_type_counts: dict[str, int] = {}
        for p in expr.params:
            pname = self._type_expr_name(p)
            if pname:
                param_type_counts[pname] = param_type_counts.get(pname, 0) + 1

        captures = self._collect_free_vars(expr.body, param_type_counts)

        # Assign closure ID and register for later lifting
        closure_id = self._next_closure_id
        self._next_closure_id += 1
        self._pending_closures.append((expr, captures, closure_id))

        # Compute closure struct layout
        # offset 0: func_table_idx (i32, 4 bytes)
        field_offsets: list[tuple[int, str]] = []
        offset = 4  # skip func_table_idx
        for _tname, _idx, cap_wt in captures:
            align = 8 if cap_wt in ("i64", "f64") else 4
            offset = _align_up(offset, align)
            field_offsets.append((offset, cap_wt))
            offset += 8 if cap_wt in ("i64", "f64") else 4
        total_size = max(_align_up(offset, 8), 8)  # at least 8 bytes

        # Emit allocation + stores
        instructions: list[str] = []
        tmp = self.alloc_local("i32")

        # Allocate closure struct
        instructions.append(f"i32.const {total_size}")
        instructions.append("call $alloc")
        instructions.append(f"local.set {tmp}")

        # Store func_table_idx at offset 0
        instructions.append(f"local.get {tmp}")
        instructions.append(f"i32.const {closure_id}")
        instructions.append("i32.store offset=0")

        # Store each captured value
        for i, (tname, cap_idx, cap_wt) in enumerate(captures):
            cap_offset, _wt = field_offsets[i]
            local_idx = env.resolve(tname, cap_idx)
            if local_idx is None:
                return None  # capture reference unresolvable
            instructions.append(f"local.get {tmp}")
            instructions.append(f"local.get {local_idx}")
            store_op = (
                "i64.store" if cap_wt == "i64"
                else "f64.store" if cap_wt == "f64"
                else "i32.store"
            )
            instructions.append(f"{store_op} offset={cap_offset}")

        # Leave closure pointer on stack
        instructions.append(f"local.get {tmp}")
        return instructions

    def _translate_apply_fn(
        self, call: ast.FnCall, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate apply_fn(closure, arg0, arg1, ...) to call_indirect.

        The closure is an i32 pointer to:
          [func_table_idx: i32] [captures...]

        The lifted function signature is:
          (param $env i32) (param $p0 <type>) ... (result <type>)
        """
        instructions: list[str] = []
        closure_arg = call.args[0]
        value_args = call.args[1:]

        # Translate the closure argument — get i32 pointer
        closure_instrs = self.translate_expr(closure_arg, env)
        if closure_instrs is None:
            return None

        # Save closure pointer to temp local
        tmp = self.alloc_local("i32")
        instructions.extend(closure_instrs)
        instructions.append(f"local.set {tmp}")

        # Push closure pointer as first arg (env for lifted function)
        instructions.append(f"local.get {tmp}")

        # Translate and push remaining arguments
        arg_wasm_types: list[str] = []
        for arg in value_args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            instructions.extend(arg_instrs)
            # Infer WASM type for call_indirect type signature
            wt = self._infer_expr_wasm_type(arg)
            arg_wasm_types.append(wt or "i64")  # default to i64

        # Load func_table_idx from closure struct
        instructions.append(f"local.get {tmp}")
        instructions.append("i32.load offset=0")

        # Build call_indirect type signature
        # Return type: infer from the enclosing function's expected return
        # or from the closure's type if available
        ret_wt = self._infer_apply_fn_return_type(closure_arg)
        param_parts = " ".join(
            f"(param {wt})" for wt in ["i32"] + arg_wasm_types
        )
        result_part = f" (result {ret_wt})" if ret_wt else ""
        sig_key = f"{param_parts}{result_part}"

        # Register this signature for the codegen to emit as a type decl
        if sig_key not in self._closure_sigs:
            sig_name = f"$closure_sig_{len(self._closure_sigs)}"
            self._closure_sigs[sig_key] = sig_name

        sig_name = self._closure_sigs[sig_key]
        instructions.append(f"call_indirect (type {sig_name})")
        return instructions

    def _infer_apply_fn_return_type(
        self, closure_arg: ast.Expr,
    ) -> str | None:
        """Infer the WASM return type for a closure application.

        Looks at the closure argument's type (via slot ref type name
        and type alias resolution) to determine the return type.
        """
        if isinstance(closure_arg, ast.SlotRef):
            type_name = closure_arg.type_name
            # Check if this is a type alias for a function type
            alias_te = self._type_aliases.get(type_name)
            if isinstance(alias_te, ast.FnType):
                return self._fn_type_return_wasm(alias_te)
        return "i64"  # safe default for most cases

    def _fn_type_return_wasm(self, fn_type: ast.FnType) -> str | None:
        """Get the WASM return type from a FnType AST node."""
        ret = fn_type.return_type
        if isinstance(ret, ast.NamedType):
            name = ret.name
            if name in ("Int", "Nat"):
                return "i64"
            if name in ("Float64", "Float"):
                return "f64"
            if name == "Bool":
                return "i32"
            if name == "Unit":
                return None
            return "i32"  # ADT or other pointer type
        return "i64"  # default

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
                elif name in ("Float64", "Float"):
                    types.append("f64")
                elif name == "Bool":
                    types.append("i32")
                elif name == "Unit":
                    pass  # skip Unit params
                else:
                    types.append("i32")  # ADT pointer
            else:
                types.append("i64")  # default
        return types

    def _collect_free_vars(
        self,
        body: ast.Expr,
        param_counts: dict[str, int],
    ) -> list[tuple[str, int, str]]:
        """Collect free variables in an anonymous function body.

        Walks the body and finds SlotRef nodes that reference bindings
        from the enclosing scope (De Bruijn index >= param count for
        that type). Returns list of (type_name, adjusted_index, wasm_type).
        The adjusted_index is the De Bruijn index in the OUTER scope.
        """
        free: list[tuple[str, int, str]] = []
        seen: set[tuple[str, int]] = set()
        self._walk_free_vars(body, param_counts, free, seen)
        return free

    def _walk_free_vars(
        self,
        expr: ast.Expr,
        param_counts: dict[str, int],
        free: list[tuple[str, int, str]],
        seen: set[tuple[str, int]],
    ) -> None:
        """Recursively walk an expression to find free variable references."""
        if isinstance(expr, ast.SlotRef):
            type_name = expr.type_name
            if expr.type_args:
                arg_names = []
                for ta in expr.type_args:
                    if isinstance(ta, ast.NamedType):
                        arg_names.append(ta.name)
                    else:
                        return
                type_name = f"{expr.type_name}<{', '.join(arg_names)}>"
            count = param_counts.get(type_name, 0)
            if expr.index >= count:
                # This refers to an outer scope binding
                outer_idx = expr.index - count
                key = (type_name, outer_idx)
                if key not in seen:
                    seen.add(key)
                    # Infer wasm type from type name
                    wt = self._type_name_to_wasm(type_name)
                    free.append((type_name, outer_idx, wt))
            return

        if isinstance(expr, ast.BinaryExpr):
            self._walk_free_vars(expr.left, param_counts, free, seen)
            self._walk_free_vars(expr.right, param_counts, free, seen)
        elif isinstance(expr, ast.UnaryExpr):
            self._walk_free_vars(expr.operand, param_counts, free, seen)
        elif isinstance(expr, ast.IfExpr):
            self._walk_free_vars(expr.condition, param_counts, free, seen)
            self._walk_free_vars(expr.then_branch, param_counts, free, seen)
            self._walk_free_vars(expr.else_branch, param_counts, free, seen)
        elif isinstance(expr, ast.Block):
            extra = dict(param_counts)
            for stmt in expr.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._walk_free_vars(stmt.value, extra, free, seen)
                    # The let binding adds to the local scope
                    let_name = self._type_expr_name(stmt.type_expr)
                    if let_name:
                        extra[let_name] = extra.get(let_name, 0) + 1
                elif isinstance(stmt, ast.ExprStmt):
                    self._walk_free_vars(stmt.expr, extra, free, seen)
            if expr.expr:
                self._walk_free_vars(expr.expr, extra, free, seen)
        elif isinstance(expr, ast.FnCall):
            for arg in expr.args:
                self._walk_free_vars(arg, param_counts, free, seen)
        elif isinstance(expr, ast.QualifiedCall):
            for arg in expr.args:
                self._walk_free_vars(arg, param_counts, free, seen)
        elif isinstance(expr, ast.ConstructorCall):
            for arg in expr.args:
                self._walk_free_vars(arg, param_counts, free, seen)
        elif isinstance(expr, ast.MatchExpr):
            self._walk_free_vars(expr.scrutinee, param_counts, free, seen)
            for arm in expr.arms:
                arm_extra = dict(param_counts)
                # Match arm bindings add to scope
                self._collect_pattern_bindings(
                    arm.pattern, arm_extra,
                )
                self._walk_free_vars(arm.body, arm_extra, free, seen)
        # Other expression types (literals, etc.) have no sub-expressions

    def _collect_pattern_bindings(
        self,
        pattern: ast.Pattern,
        counts: dict[str, int],
    ) -> None:
        """Collect type bindings introduced by a match pattern."""
        if isinstance(pattern, ast.BindingPattern):
            b_name = self._type_expr_name(pattern.type_expr)
            if b_name:
                counts[b_name] = counts.get(b_name, 0) + 1
        elif isinstance(pattern, ast.ConstructorPattern):
            for sub in pattern.sub_patterns:
                self._collect_pattern_bindings(sub, counts)

    def _type_expr_name(self, te: ast.TypeExpr) -> str | None:
        """Extract a simple type name from a TypeExpr."""
        if isinstance(te, ast.NamedType):
            if te.type_args:
                arg_names = []
                for a in te.type_args:
                    if isinstance(a, ast.NamedType):
                        arg_names.append(a.name)
                    else:
                        return None
                return f"{te.name}<{', '.join(arg_names)}>"
            return te.name
        if isinstance(te, ast.RefinementType):
            return self._type_expr_name(te.base_type)
        return None

    def _type_name_to_wasm(self, type_name: str) -> str:
        """Map a Vera type name string to a WASM type string."""
        if type_name in ("Int", "Nat"):
            return "i64"
        if type_name in ("Float64", "Float"):
            return "f64"
        if type_name == "Bool":
            return "i32"
        if type_name == "Unit":
            return "i32"  # shouldn't appear, safe fallback
        # ADT or function type alias → i32 pointer
        return "i32"

    # -----------------------------------------------------------------
    # Result references (postconditions)
    # -----------------------------------------------------------------

    def _translate_result_ref(self) -> list[str] | None:
        """Translate @T.result to local.get of the result temp."""
        if self._result_local is not None:
            return [f"local.get {self._result_local}"]
        return None

    # -----------------------------------------------------------------
    # Constructors
    # -----------------------------------------------------------------

    def _translate_nullary_constructor(
        self, expr: ast.NullaryConstructor
    ) -> list[str] | None:
        """Translate a nullary constructor (e.g., None, Red) to WAT.

        Emits: alloc → store tag → return pointer.
        """
        layout = self._ctor_layouts.get(expr.name)
        if layout is None:
            return None

        tmp = self.alloc_local("i32")
        return [
            f"i32.const {layout.total_size}",
            "call $alloc",
            f"local.tee {tmp}",
            f"i32.const {layout.tag}",
            "i32.store",
            f"local.get {tmp}",
        ]

    def _translate_constructor_call(
        self, expr: ast.ConstructorCall, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a constructor call (e.g., Some(42)) to WAT.

        Emits: alloc → store tag → store each field → return pointer.
        Field offsets are computed from the concrete argument types so that
        generic constructors (e.g. Some(T) instantiated as Some(Int))
        use the correct WASM types and alignment.
        """
        layout = self._ctor_layouts.get(expr.name)
        if layout is None:
            return None

        # Translate all arguments and infer their concrete WASM types
        arg_instrs_list: list[list[str]] = []
        arg_wasm_types: list[str] = []
        for arg in expr.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            arg_wt = self._infer_expr_wasm_type(arg)
            if arg_wt is None:
                return None
            arg_instrs_list.append(arg_instrs)
            arg_wasm_types.append(arg_wt)

        # Compute field offsets from concrete argument types
        _sizes = {"i32": 4, "i64": 8, "f64": 8}
        _aligns = {"i32": 4, "i64": 8, "f64": 8}
        offset = 4  # after tag (i32, 4 bytes)
        field_offsets: list[tuple[int, str]] = []
        for wt in arg_wasm_types:
            align = _aligns.get(wt, 8)
            offset = (offset + align - 1) & ~(align - 1)  # align up
            field_offsets.append((offset, wt))
            offset += _sizes.get(wt, 8)
        total_size = ((offset + 7) & ~7) if offset > 0 else 8  # 8-byte aligned

        tmp = self.alloc_local("i32")
        instructions: list[str] = [
            f"i32.const {total_size}",
            "call $alloc",
            f"local.tee {tmp}",
            f"i32.const {layout.tag}",
            "i32.store",
        ]

        # Store each field at its computed offset
        for i, (fo, wt) in enumerate(field_offsets):
            instructions.append(f"local.get {tmp}")
            instructions.extend(arg_instrs_list[i])
            instructions.append(f"{wt}.store offset={fo}")

        # Leave pointer as result
        instructions.append(f"local.get {tmp}")
        return instructions

    # -----------------------------------------------------------------
    # Match expressions
    # -----------------------------------------------------------------

    def _translate_match(
        self, expr: ast.MatchExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a match expression to WAT.

        Evaluates the scrutinee once, saves to a local, then emits a
        chained if-else cascade for each arm.
        """
        # Translate scrutinee
        scr_instrs = self.translate_expr(expr.scrutinee, env)
        if scr_instrs is None:
            return None

        scr_wasm_type = self._infer_expr_wasm_type(expr.scrutinee)
        if scr_wasm_type is None:
            return None

        # Save scrutinee to a local
        scr_local = self.alloc_local(scr_wasm_type)
        instructions: list[str] = list(scr_instrs)
        instructions.append(f"local.set {scr_local}")

        # Infer result type of the match
        result_type = self._infer_match_result_type(expr)

        # Compile arms as chained if-else
        arm_instrs = self._compile_match_arms(
            expr.arms, scr_local, scr_wasm_type, result_type, env
        )
        if arm_instrs is None:
            return None

        instructions.extend(arm_instrs)
        return instructions

    def _infer_match_result_type(
        self, expr: ast.MatchExpr
    ) -> str | None:
        """Infer the WASM result type from the first arm body."""
        for arm in expr.arms:
            wt = self._infer_expr_wasm_type(arm.body)
            if wt is not None:
                return wt
        return None

    def _compile_match_arms(
        self,
        arms: tuple[ast.MatchArm, ...],
        scr_local: int,
        scr_wasm_type: str,
        result_type: str | None,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Compile match arms as a chained if-else cascade."""
        if not arms:
            return None

        arm = arms[0]
        remaining = arms[1:]

        # Check if this arm needs a condition
        cond = self._translate_match_condition(
            arm.pattern, scr_local, scr_wasm_type
        )

        if cond is None or not remaining:
            # Unconditional arm (catch-all) or last arm — emit directly
            setup = self._setup_match_arm_env(
                arm.pattern, scr_local, scr_wasm_type, env
            )
            if setup is None:
                return None
            setup_instrs, arm_env = setup
            body = self.translate_expr(arm.body, arm_env)
            if body is None:
                return None
            return setup_instrs + body

        # Conditional arm with more arms following
        setup = self._setup_match_arm_env(
            arm.pattern, scr_local, scr_wasm_type, env
        )
        if setup is None:
            return None
        setup_instrs, arm_env = setup
        body = self.translate_expr(arm.body, arm_env)
        if body is None:
            return None

        # Compile remaining arms (else branch)
        else_instrs = self._compile_match_arms(
            remaining, scr_local, scr_wasm_type, result_type, env
        )
        if else_instrs is None:
            return None

        # Build if-else block
        result_annot = f" (result {result_type})" if result_type else ""
        instrs: list[str] = list(cond)
        instrs.append(f"if{result_annot}")
        for i in setup_instrs:
            instrs.append(f"  {i}")
        for i in body:
            instrs.append(f"  {i}")
        instrs.append("else")
        for i in else_instrs:
            instrs.append(f"  {i}")
        instrs.append("end")
        return instrs

    def _translate_match_condition(
        self,
        pattern: ast.Pattern,
        scr_local: int,
        scr_wasm_type: str,
    ) -> list[str] | None:
        """Emit i32 condition for a pattern check.

        Returns None for unconditional patterns (wildcard/binding).
        """
        if isinstance(pattern, (ast.NullaryPattern, ast.ConstructorPattern)):
            name = pattern.name
            layout = self._ctor_layouts.get(name)
            if layout is None:
                return None
            return [
                f"local.get {scr_local}",
                "i32.load",
                f"i32.const {layout.tag}",
                "i32.eq",
            ]

        if isinstance(pattern, ast.BoolPattern):
            if pattern.value:
                return [f"local.get {scr_local}"]
            else:
                return [f"local.get {scr_local}", "i32.eqz"]

        if isinstance(pattern, ast.IntPattern):
            return [
                f"local.get {scr_local}",
                f"i64.const {pattern.value}",
                "i64.eq",
            ]

        # WildcardPattern, BindingPattern — unconditional
        return None

    def _setup_match_arm_env(
        self,
        pattern: ast.Pattern,
        scr_local: int,
        scr_wasm_type: str,
        env: WasmSlotEnv,
    ) -> tuple[list[str], WasmSlotEnv] | None:
        """Extract fields and set up environment bindings for a match arm.

        Returns (instructions, new_env) or None on failure.
        """
        if isinstance(pattern, (ast.WildcardPattern, ast.NullaryPattern,
                                ast.BoolPattern, ast.IntPattern)):
            return ([], env)

        if isinstance(pattern, ast.BindingPattern):
            # Bind the scrutinee itself to a new local
            type_name = self._type_expr_to_slot_name(pattern.type_expr)
            if type_name is None:
                return None
            local_idx = self.alloc_local(scr_wasm_type)
            instrs = [
                f"local.get {scr_local}",
                f"local.set {local_idx}",
            ]
            new_env = env.push(type_name, local_idx)
            return (instrs, new_env)

        if isinstance(pattern, ast.ConstructorPattern):
            layout = self._ctor_layouts.get(pattern.name)
            if layout is None:
                return None
            return self._extract_constructor_fields(
                pattern, scr_local, layout, env
            )

        return None

    def _extract_constructor_fields(
        self,
        pattern: ast.ConstructorPattern,
        scr_local: int,
        layout: ConstructorLayout,
        env: WasmSlotEnv,
    ) -> tuple[list[str], WasmSlotEnv] | None:
        """Extract fields from a constructor match into locals.

        Computes field offsets from concrete binding types (same
        monomorphization approach as _translate_constructor_call).
        """
        _sizes = {"i32": 4, "i64": 8, "f64": 8}
        _aligns = {"i32": 4, "i64": 8, "f64": 8}
        offset = 4  # after tag (i32, 4 bytes)
        instrs: list[str] = []
        new_env = env

        for i, sub_pat in enumerate(pattern.sub_patterns):
            if isinstance(sub_pat, ast.BindingPattern):
                # Resolve concrete WASM type from the binding's type_expr
                type_name = self._type_expr_to_slot_name(sub_pat.type_expr)
                if type_name is None:
                    return None
                wt = self._slot_name_to_wasm_type(type_name)
                if wt is None:
                    return None
                # Compute aligned offset for this field
                align = _aligns.get(wt, 8)
                offset = (offset + align - 1) & ~(align - 1)
                # Load field from scrutinee pointer
                local_idx = self.alloc_local(wt)
                instrs.append(f"local.get {scr_local}")
                instrs.append(f"{wt}.load offset={offset}")
                instrs.append(f"local.set {local_idx}")
                new_env = new_env.push(type_name, local_idx)
                offset += _sizes.get(wt, 8)

            elif isinstance(sub_pat, ast.WildcardPattern):
                # Skip this field but advance offset using layout's type
                if i < len(layout.field_offsets):
                    _, generic_wt = layout.field_offsets[i]
                    align = _aligns.get(generic_wt, 8)
                    offset = (offset + align - 1) & ~(align - 1)
                    offset += _sizes.get(generic_wt, 8)

            else:
                # Nested constructor patterns — deferred
                return None

        return (instrs, new_env)

    # -----------------------------------------------------------------
    # Helpers
    # -----------------------------------------------------------------

    def _is_void_expr(self, expr: ast.Expr) -> bool:
        """Check if an expression produces no value on the WASM stack.

        QualifiedCalls (effect operations like IO.print) return Unit
        and produce no stack value.  UnitLit also produces nothing.
        Effect op calls like put() are also void.
        """
        if isinstance(expr, ast.QualifiedCall):
            return True  # effect ops return Unit (void)
        if isinstance(expr, ast.UnitLit):
            return True
        if isinstance(expr, ast.FnCall) and expr.name in self._effect_ops:
            _name, is_void = self._effect_ops[expr.name]
            return is_void
        return False

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str | None:
        """Extract the slot name from a type expression."""
        if isinstance(te, ast.NamedType):
            if te.type_args:
                arg_names = []
                for a in te.type_args:
                    if isinstance(a, ast.NamedType):
                        arg_names.append(a.name)
                    else:
                        return None
                return f"{te.name}<{', '.join(arg_names)}>"
            return te.name
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_slot_name(te.base_type)
        return None

    def _slot_name_to_wasm_type(self, name: str) -> str | None:
        """Map a slot type name to a WAT type string."""
        if name in ("Int", "Nat"):
            return "i64"
        if name in ("Float64", "Float"):
            return "f64"
        if name == "Bool":
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
