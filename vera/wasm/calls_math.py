"""Math and numeric conversion translation mixin for WasmContext.

Handles: abs, min, max, floor, ceil, round, sqrt, pow, float_is_nan,
float_is_infinite, nan, infinity; log/log2/log10, sin/cos/tan/asin/
acos/atan/atan2, pi/e constants, sign/clamp/float_clamp (#467);
and numeric conversions (int_to_float, float_to_int, nat_to_int,
int_to_nat, byte_to_int, int_to_byte).
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv, gc_shadow_push


class CallsMathMixin:
    """Methods for translating math and numeric conversion built-ins."""

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
    # Math built-ins — #467: log, trig, constants, numeric utilities.
    # -----------------------------------------------------------------

    def _translate_math_unary_host(
        self, op_name: str, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate log/log2/log10/sin/cos/tan/asin/acos/atan → host call.

        These aren't expressible as WASM instructions — there's no
        ``f64.log`` or ``f64.sin``.  We emit a host import call
        (``call $vera.{op_name}``) and add the op to
        ``_math_ops_used`` so ``codegen/assembly.py`` emits the
        matching ``(import "vera" "{op_name}" ...)`` declaration.
        IEEE 754 semantics (NaN for out-of-domain, ±inf for
        overflow) are preserved by the underlying Python ``math``
        or JS ``Math`` implementations.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self._math_ops_used.add(op_name)
        return [*arg_instrs, f"call $vera.{op_name}"]

    def _translate_atan2(
        self, y_arg: ast.Expr, x_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate ``atan2(y, x) → Float64`` — quadrant-correct angle.

        Host-imported two-arg version.  Unlike ``atan(x)`` which is
        single-arg and ambiguous about quadrant, ``atan2(y, x)``
        returns the angle from `+x` to the vector `(x, y)` in
        ``[-π, π]``.  The argument order mirrors POSIX / IEEE /
        Python / JS conventions: `atan2(y, x)`, not `atan2(x, y)`.
        """
        y_instrs = self.translate_expr(y_arg, env)
        x_instrs = self.translate_expr(x_arg, env)
        if y_instrs is None or x_instrs is None:
            return None
        self._math_ops_used.add("atan2")
        return [*y_instrs, *x_instrs, "call $vera.atan2"]

    def _translate_pi(self) -> list[str]:
        """Translate ``pi() → Float64`` as ``f64.const 3.14…``.

        Inlined rather than host-imported — a host call round trip
        just to return a constant would waste a dozen nanoseconds
        per call.  Uses the same 17-digit representation as
        ``math.pi`` / ``Math.PI`` so the value round-trips exactly
        across Python / browser runtimes.
        """
        return ["f64.const 3.141592653589793"]

    def _translate_e(self) -> list[str]:
        """Translate ``e() → Float64`` as ``f64.const 2.71…``.

        Same rationale as ``_translate_pi``.
        """
        return ["f64.const 2.718281828459045"]

    def _translate_sign(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate ``sign(@Int) → @Int`` inline as `(x > 0) - (x < 0)`.

        Returns `-1`, `0`, or `+1`.  Encoded as two comparisons and
        a subtraction: `i64.gt_s` minus `i64.lt_s`, widened back to
        i64 via ``i64.extend_i32_s``.  No branches.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        tmp = self.alloc_local("i64")
        return [
            *arg_instrs,
            f"local.set {tmp}",
            # (x > 0)
            f"local.get {tmp}",
            "i64.const 0",
            "i64.gt_s",
            "i64.extend_i32_s",
            # (x < 0)
            f"local.get {tmp}",
            "i64.const 0",
            "i64.lt_s",
            "i64.extend_i32_s",
            # gt - lt  ∈ {-1, 0, +1}
            "i64.sub",
        ]

    def _translate_clamp(
        self,
        val_arg: ast.Expr,
        min_arg: ast.Expr,
        max_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate ``clamp(@Int, @Int, @Int) → @Int`` inline.

        `clamp(v, lo, hi)` = `min(max(v, lo), hi)`.  Uses two
        ``select`` sequences — no branches.  When ``lo > hi`` the
        outer ``min`` wins, so the result is ``hi`` (consistent
        with Rust's `i64::clamp` before its 1.50 panic was added).
        Callers with strict ordering expectations should pre-check.

        WASM ``select`` pops `[val1, val2, cond]` and pushes
        ``val1`` if ``cond != 0`` else ``val2``.  For ``max(v, lo)``
        we want ``v`` when ``v > lo``: stack = ``v; lo; (v > lo)``.
        Saving the intermediate into a local keeps the second
        ``select`` readable.
        """
        val_instrs = self.translate_expr(val_arg, env)
        min_instrs = self.translate_expr(min_arg, env)
        max_instrs = self.translate_expr(max_arg, env)
        if val_instrs is None or min_instrs is None or max_instrs is None:
            return None
        v = self.alloc_local("i64")
        lo = self.alloc_local("i64")
        hi = self.alloc_local("i64")
        mx = self.alloc_local("i64")  # max(v, lo) — intermediate
        return [
            *val_instrs, f"local.set {v}",
            *min_instrs, f"local.set {lo}",
            *max_instrs, f"local.set {hi}",
            # max(v, lo): select v if (v > lo) else lo.
            f"local.get {v}",
            f"local.get {lo}",
            f"local.get {v}",
            f"local.get {lo}",
            "i64.gt_s",
            "select",
            f"local.set {mx}",
            # min(mx, hi): select mx if (mx < hi) else hi.
            f"local.get {mx}",
            f"local.get {hi}",
            f"local.get {mx}",
            f"local.get {hi}",
            "i64.lt_s",
            "select",
        ]

    def _translate_float_clamp(
        self,
        val_arg: ast.Expr,
        min_arg: ast.Expr,
        max_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate ``float_clamp(@Float64, @Float64, @Float64) → @Float64``.

        Uses ``f64.max`` and ``f64.min`` which have native WASM
        instructions.  IEEE 754 semantics: NaN propagates through
        both ``f64.max`` and ``f64.min`` (result is NaN if any
        input is NaN) — intentional, matches Python / JS fallbacks.
        """
        val_instrs = self.translate_expr(val_arg, env)
        min_instrs = self.translate_expr(min_arg, env)
        max_instrs = self.translate_expr(max_arg, env)
        if val_instrs is None or min_instrs is None or max_instrs is None:
            return None
        v = self.alloc_local("f64")
        lo = self.alloc_local("f64")
        hi = self.alloc_local("f64")
        return [
            *val_instrs, f"local.set {v}",
            *min_instrs, f"local.set {lo}",
            *max_instrs, f"local.set {hi}",
            # max(v, lo)
            f"local.get {v}",
            f"local.get {lo}",
            "f64.max",
            # min(that, hi)
            f"local.get {hi}",
            "f64.min",
        ]
