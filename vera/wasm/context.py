"""Vera WASM translation layer — AST to WAT bridge.

Translates Vera AST expressions into WebAssembly Text format (WAT)
instructions for compilation to WASM binary.  Manages slot environments,
local variable allocation, string pool, and instruction generation.

The ``WasmContext`` class is composed from several mixin modules that
each handle a specific concern:

* :mod:`~vera.wasm.inference` — type inference and utility methods
* :mod:`~vera.wasm.operators` — binary/unary operators, control flow,
  quantifiers, assert/assume, old/new
* :mod:`~vera.wasm.calls` — function calls, generic resolution, handle
* :mod:`~vera.wasm.closures` — closures and free variable analysis
* :mod:`~vera.wasm.data` — constructors, match, arrays, indexing

See spec/11-compilation.md for the compilation specification.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from vera import ast

if TYPE_CHECKING:
    from vera.codegen import ConstructorLayout

from vera.wasm.helpers import (  # noqa: F401 — re-exported for consumers
    StringPool,
    WasmSlotEnv,
    wasm_type,
)
from vera.wasm.inference import InferenceMixin
from vera.wasm.operators import OperatorsMixin
from vera.wasm.calls import CallsMixin
from vera.wasm.closures import ClosuresMixin
from vera.wasm.data import DataMixin


# =====================================================================
# WASM translation context
# =====================================================================

class WasmContext(
    InferenceMixin,
    OperatorsMixin,
    CallsMixin,
    ClosuresMixin,
    DataMixin,
):
    """Generates WAT instructions for a single function body.

    Manages local variable allocation and dispatches expression
    translation.  Mirrors SmtContext in smt.py.

    Composed from five mixin classes, each in its own module.
    This class provides __init__, configuration setters, local
    allocation, the expression dispatcher (translate_expr), and
    block translation (translate_block).
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
        known_fns: set[str] | None = None,
        ctor_adt_tp_indices: dict[str, tuple[int | None, ...]] | None = None,
        adt_tp_counts: dict[str, int] | None = None,
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
        # Known locally-defined function names (for cross-module guard rail)
        self._known_fns: set[str] = known_fns or set()
        # Per-field ADT type-param indices for sparse constructors (e.g. Err → (1,))
        self._ctor_adt_tp_indices: dict[str, tuple[int | None, ...]] = (
            ctor_adt_tp_indices or {}
        )
        # Maps ADT name → number of type parameters
        self._adt_tp_counts: dict[str, int] = adt_tp_counts or {}
        # Map host-import tracking (propagated to codegen core)
        self._map_imports: set[str] = set()
        self._map_ops_used: set[str] = set()
        # Set host-import tracking (propagated to codegen core)
        self._set_imports: set[str] = set()
        self._set_ops_used: set[str] = set()
        # Decimal host-import tracking (propagated to codegen core)
        self._decimal_imports: set[str] = set()
        self._decimal_ops_used: set[str] = set()
        # Json host-import tracking (propagated to codegen core)
        self._json_ops_used: set[str] = set()
        # Html host-import tracking (propagated to codegen core)
        self._html_ops_used: set[str] = set()
        # Http host-import tracking (propagated to codegen core)
        self._http_ops_used: set[str] = set()
        # Inference host-import tracking (propagated to codegen core)
        self._inference_ops_used: set[str] = set()
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
        # Type alias parameters: alias_name -> param names (for generic aliases)
        self._type_alias_params: dict[str, tuple[str, ...]] = {}
        # Closure signature registry: sig_key -> (type_name, param/result WAT)
        self._closure_sigs: dict[str, str] = {}
        # Flags for resource requirements detected during translation
        self.needs_alloc: bool = False
        # Next closure id (may be overwritten by codegen)
        self._next_closure_id: int = 0
        # Next quantifier label id (for unique block/loop labels)
        self._next_quant_id: int = 0
        # Next handle expression label id (for unique try_table labels)
        self._next_handle_id: int = 0
        # Old state snapshots: type_name -> local_idx (for old() in postconditions)
        self._old_state_locals: dict[str, int] = {}

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

    def set_type_alias_params(
        self, params: dict[str, tuple[str, ...]],
    ) -> None:
        """Set type alias parameter names for generic alias resolution."""
        self._type_alias_params = params

    def set_closure_id_start(self, start: int) -> None:
        """Set the starting closure ID for this context."""
        self._next_closure_id = start

    def set_closure_sigs(self, sigs: dict[str, str]) -> None:
        """Seed with accumulated module-level closure signatures.

        Each context independently numbers ``$closure_sig_N`` from zero.
        When multiple functions use closures with different signatures,
        the names collide after module-level merge.  By seeding the
        context with signatures already registered at module level, new
        signatures get unique numbers and existing ones reuse their names.
        """
        self._closure_sigs = dict(sigs)

    def set_result_local(self, local_idx: int) -> None:
        """Set the local index used for @T.result in postconditions."""
        self._result_local = local_idx

    def set_old_state_locals(
        self, locals_map: dict[str, int],
    ) -> None:
        """Set old-state snapshot locals for old() in postconditions."""
        self._old_state_locals = locals_map

    def get_old_state_local(self, type_name: str) -> int | None:
        """Get the local index holding the old() snapshot for a State type."""
        return self._old_state_locals.get(type_name)

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

        if isinstance(expr, ast.ModuleCall):
            # C7e: desugar to flat FnCall — imported function is compiled
            # into the same WASM module via flattening.
            desugared = ast.FnCall(
                name=expr.name,
                args=expr.args,
                span=expr.span,
            )
            return self._translate_call(desugared, env)

        if isinstance(expr, ast.StringLit):
            return self._translate_string_lit(expr)

        if isinstance(expr, ast.InterpolatedString):
            return self._translate_interpolated_string(expr, env)

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

        if isinstance(expr, ast.HandleExpr):
            return self._translate_handle_expr(expr, env)

        if isinstance(expr, ast.ArrayLit):
            return self._translate_array_lit(expr, env)

        if isinstance(expr, ast.IndexExpr):
            return self._translate_index_expr(expr, env)

        if isinstance(expr, ast.AssertExpr):
            return self._translate_assert(expr, env)

        if isinstance(expr, ast.AssumeExpr):
            return self._translate_assume()

        if isinstance(expr, ast.ForallExpr):
            return self._translate_forall(expr, env)

        if isinstance(expr, ast.ExistsExpr):
            return self._translate_exists(expr, env)

        if isinstance(expr, ast.OldExpr):
            return self._translate_old_expr(expr)

        if isinstance(expr, ast.NewExpr):
            return self._translate_new_expr(expr)

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
                # Pair bindings (String, Array<T>) need two locals: (ptr, len)
                if self._is_pair_type_name(type_name):
                    ptr_idx = self.alloc_local("i32")
                    len_idx = self.alloc_local("i32")
                    instructions.extend(val_instrs)
                    instructions.append(f"local.set {len_idx}")
                    instructions.append(f"local.set {ptr_idx}")
                    current_env = current_env.push(type_name, ptr_idx)
                    continue
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
                    if self._is_pair_result_expr(stmt.expr):
                        instructions.extend(["drop", "drop"])
                    else:
                        instructions.append("drop")
            elif isinstance(stmt, ast.LetDestruct):
                result = self._translate_let_destruct(stmt, current_env)
                if result is None:
                    return None
                destr_instrs, current_env = result
                instructions.extend(destr_instrs)
            else:
                # Unknown statement type
                return None

        # Final expression
        expr_instrs = self.translate_expr(block.expr, current_env)
        if expr_instrs is None:
            return None
        instructions.extend(expr_instrs)
        return instructions

    # -----------------------------------------------------------------
    # Helpers
    # -----------------------------------------------------------------

    def _is_void_expr(self, expr: ast.Expr) -> bool:
        """Check if an expression produces no value on the WASM stack.

        QualifiedCalls (effect operations like IO.print) return Unit
        and produce no stack value.  UnitLit also produces nothing.
        Effect op calls like put() are also void.
        Compound expressions (match, if, block) are void when all
        branches/the final expression are void.
        """
        if isinstance(expr, ast.QualifiedCall):
            # IO.print returns void; IO.exit never returns (unreachable).
            # Other IO ops (read_line, read_file, etc.) produce values.
            if expr.qualifier == "IO":
                return expr.name in ("print", "exit")
            # Http ops return Result<String, String> — not void
            if expr.qualifier == "Http":
                return False
            # State ops are desugared to FnCall, not QualifiedCall.
            # Future qualified effects should be added explicitly above.
            # Default to void for unknown qualified calls as a safe
            # fallback — WASM validation will catch mismatches.
            return True
        if isinstance(expr, ast.UnitLit):
            return True
        if isinstance(expr, ast.FnCall) and expr.name in self._effect_ops:
            _name, is_void = self._effect_ops[expr.name]
            return is_void
        if isinstance(expr, (ast.AssertExpr, ast.AssumeExpr)):
            return True  # assert/assume return Unit (void)
        # Compound expressions: void if all branches are void
        if isinstance(expr, ast.MatchExpr):
            return all(self._is_void_expr(arm.body) for arm in expr.arms)
        if isinstance(expr, ast.IfExpr):
            return (self._is_void_expr(expr.then_branch)
                    and self._is_void_expr(expr.else_branch))
        if isinstance(expr, ast.Block):
            return self._is_void_expr(expr.expr)
        return False

    def _is_pair_result_expr(self, expr: ast.Expr) -> bool:
        """Check if an expression produces two values (ptr, len) on the stack.

        String literals, array literals, pair-type slot refs, and function
        calls returning i32_pair all produce two values.
        """
        if isinstance(expr, ast.StringLit):
            return True
        if isinstance(expr, ast.InterpolatedString):
            return True
        if isinstance(expr, ast.ArrayLit):
            return True
        if isinstance(expr, ast.SlotRef):
            name = self._resolve_base_type_name(expr.type_name)
            return self._is_pair_type_name(name)
        if isinstance(expr, ast.FnCall):
            ret = self._infer_fncall_wasm_type(expr)
            return ret == "i32_pair"
        if isinstance(expr, ast.QualifiedCall):
            ret = self._infer_qualified_call_wasm_type(expr)
            return ret == "i32_pair"
        return False
