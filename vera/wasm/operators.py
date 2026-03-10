"""Operator and simple expression translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class OperatorsMixin:
    """Mixin providing operator and simple expression translation methods.

    Methods here translate slot references, binary/unary operators,
    control flow, string literals, assert/assume, quantifiers, and
    old/new state expressions into WAT instructions.  They rely on
    attributes and methods provided by the main WasmContext class
    through mixin composition.
    """

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
        # Pair types (String, Array<T>) push (ptr, len) — two locals
        if self._is_pair_type_name(type_name):
            return [f"local.get {local_idx}", f"local.get {local_idx + 1}"]
        return [f"local.get {local_idx}"]

    # -----------------------------------------------------------------
    # Binary operators
    # -----------------------------------------------------------------

    def _translate_binary(
        self, expr: ast.BinaryExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate binary operators to WAT."""
        # Pipe: a |> f(x, y) → f(a, x, y)
        if expr.op == ast.BinOp.PIPE:
            if isinstance(expr.right, ast.FnCall):
                desugared = ast.FnCall(
                    name=expr.right.name,
                    args=(expr.left,) + expr.right.args,
                    span=expr.span,
                )
                return self._translate_call(desugared, env)
            # C7e: a |> Module.f(x) → f(a, x)
            if isinstance(expr.right, ast.ModuleCall):
                desugared = ast.FnCall(
                    name=expr.right.name,
                    args=(expr.left,) + expr.right.args,
                    span=expr.span,
                )
                return self._translate_call(desugared, env)
            return None  # non-FnCall RHS — unsupported

        left = self.translate_expr(expr.left, env)
        right = self.translate_expr(expr.right, env)
        if left is None or right is None:
            return None

        op = expr.op
        ltype = self._infer_expr_wasm_type(expr.left)

        # Arithmetic
        if op in self._ARITH_OPS:
            if ltype == "f64":
                if op == ast.BinOp.MOD:
                    return self._translate_f64_mod(left, right)
                if op not in self._ARITH_OPS_F64:
                    return None  # unsupported float op
                return left + right + [self._ARITH_OPS_F64[op]]
            return left + right + [self._ARITH_OPS[op]]

        # Comparison — choose i32/i64/f64 based on operand types
        if op in self._CMP_OPS:
            rtype = self._infer_expr_wasm_type(expr.right)
            if ltype == "f64" or rtype == "f64":
                return left + right + [self._CMP_OPS_F64[op]]
            if ltype == "i32" and rtype == "i32":
                # Byte operands use unsigned i32 comparison
                lv = self._infer_vera_type(expr.left)
                rv = self._infer_vera_type(expr.right)
                if lv == "Byte" or rv == "Byte":
                    i32_op = self._CMP_OPS[op].replace("i64.", "i32.")
                    i32_op = i32_op.replace("_s", "_u")
                    return left + right + [i32_op]
                # Bool operands — use i32 comparison (signed)
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

        return None

    def _translate_f64_mod(
        self, left: list[str], right: list[str]
    ) -> list[str]:
        """Translate f64 modulo: a % b = a - trunc(a / b) * b.

        WASM has no f64.rem instruction, so we decompose using
        f64.trunc (truncation toward zero), matching C fmod semantics
        and consistent with i64.rem_s for integer modulo.
        """
        tmp_a = self.alloc_local("f64")
        tmp_b = self.alloc_local("f64")
        return [
            *left,
            f"local.set {tmp_a}",
            *right,
            f"local.set {tmp_b}",
            f"local.get {tmp_a}",          # a
            f"local.get {tmp_a}",          # a  (for a / b)
            f"local.get {tmp_b}",          # b  (for a / b)
            "f64.div",                      # a / b
            "f64.trunc",                    # trunc(a / b)
            f"local.get {tmp_b}",          # b  (for * b)
            "f64.mul",                      # trunc(a / b) * b
            "f64.sub",                      # a - trunc(a / b) * b
        ]

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

        # Determine result type from branches — try then first, fall back
        # to else (handles cases where one branch ends with throw/unreachable)
        result_type = self._infer_block_result_type(expr.then_branch)
        if result_type is None and expr.else_branch is not None:
            result_type = self._infer_block_result_type(expr.else_branch)
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

        # i32_pair → two i32 results (ptr, len)
        if result_type == "i32_pair":
            result_annot = "if (result i32 i32)"
        else:
            result_annot = f"if (result {result_type})"

        return (
            cond
            + [result_annot]
            + ["  " + i for i in then]
            + ["else"]
            + ["  " + i for i in else_]
            + ["end"]
        )

    # -----------------------------------------------------------------
    # String literals
    # -----------------------------------------------------------------

    def _translate_string_lit(self, expr: ast.StringLit) -> list[str]:
        """Translate a string literal to (ptr, len) on the stack."""
        offset, length = self.string_pool.intern(expr.value)
        return [f"i32.const {offset}", f"i32.const {length}"]

    # -----------------------------------------------------------------
    # String interpolation
    # -----------------------------------------------------------------

    # Type -> to_string builtin dispatch (must match checker's map)
    _INTERP_TO_STRING: dict[str, str] = {
        "Int": "to_string",
        "Nat": "nat_to_string",
        "Bool": "bool_to_string",
        "Byte": "byte_to_string",
        "Float64": "float_to_string",
    }

    def _translate_interpolated_string(
        self, expr: ast.InterpolatedString, env: "WasmSlotEnv",
    ) -> list[str] | None:
        """Translate an interpolated string to a chain of string_concat calls.

        Desugars at the WASM level: ``"a\\(x)b"`` becomes
        ``string_concat(string_concat("a", to_string(x)), "b")``.
        Each part is translated to ``(ptr, len)`` on the stack, then
        folded left with ``string_concat``.
        """
        # Collect non-empty parts as AST nodes ready for translation
        parts: list[ast.Expr] = []
        for p in expr.parts:
            if isinstance(p, str):
                if p:  # skip empty string fragments
                    parts.append(ast.StringLit(value=p, span=expr.span))
            else:
                # Determine Vera type for auto-conversion
                vera_type = self._infer_vera_type(p)
                if vera_type == "String":
                    parts.append(p)
                elif vera_type in self._INTERP_TO_STRING:
                    # Wrap with the appropriate to_string call
                    fn_name = self._INTERP_TO_STRING[vera_type]
                    parts.append(ast.FnCall(
                        name=fn_name, args=(p,), span=expr.span,
                    ))
                else:
                    # Fallback: try to_string (Int-compatible types)
                    parts.append(ast.FnCall(
                        name="to_string", args=(p,), span=expr.span,
                    ))

        if not parts:
            # All fragments were empty -> empty string
            offset, length = self.string_pool.intern("")
            return [f"i32.const {offset}", f"i32.const {length}"]

        if len(parts) == 1:
            # Single part -- translate directly
            return self.translate_expr(parts[0], env)

        # Left-fold with string_concat: concat(concat(a, b), c) ...
        result = ast.FnCall(
            name="string_concat",
            args=(parts[0], parts[1]),
            span=expr.span,
        )
        for part in parts[2:]:
            result = ast.FnCall(
                name="string_concat",
                args=(result, part),
                span=expr.span,
            )
        return self.translate_expr(result, env)

    # -----------------------------------------------------------------
    # Result references (postconditions)
    # -----------------------------------------------------------------

    def _translate_result_ref(self) -> list[str] | None:
        """Translate @T.result to local.get of the result temp."""
        if self._result_local is not None:
            return [f"local.get {self._result_local}"]
        return None

    # -----------------------------------------------------------------
    # Assert and assume
    # -----------------------------------------------------------------

    def _translate_assert(
        self, expr: ast.AssertExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate assert(expr) → trap if false.

        Evaluates the condition; if it's false (i32.eqz), executes
        unreachable (WASM trap).  Returns no value (Unit).
        """
        cond = self.translate_expr(expr.expr, env)
        if cond is None:
            return None
        return cond + ["i32.eqz", "if", "unreachable", "end"]

    def _translate_assume(self) -> list[str]:
        """Translate assume(expr) → no-op at runtime.

        The verifier uses assume as an axiom; at runtime it has no
        effect.  Returns empty instructions (Unit).
        """
        return []

    # -----------------------------------------------------------------
    # Quantifiers — forall/exists as runtime loops
    # -----------------------------------------------------------------

    def _translate_forall(
        self, expr: ast.ForallExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate forall(@T, domain, predicate) → loop returning Bool.

        Iterates counter from 0 to domain-1, inlining the predicate
        body with counter as the @T binding.  Short-circuits on the
        first false result.
        """
        return self._translate_quantifier(expr, env, is_forall=True)

    def _translate_exists(
        self, expr: ast.ExistsExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate exists(@T, domain, predicate) → loop returning Bool.

        Iterates counter from 0 to domain-1, inlining the predicate
        body with counter as the @T binding.  Short-circuits on the
        first true result.
        """
        return self._translate_quantifier(expr, env, is_forall=False)

    def _translate_quantifier(
        self,
        expr: ast.ForallExpr | ast.ExistsExpr,
        env: WasmSlotEnv,
        *,
        is_forall: bool,
    ) -> list[str] | None:
        """Shared implementation for forall/exists compilation.

        Layout:
          counter (i64) = 0
          limit   (i64) = domain
          result  (i32) = 1 (forall) or 0 (exists)
          block $qbreak_N
            loop $qloop_N
              if counter >= limit → br $qbreak_N
              push counter as @T binding
              evaluate predicate body → i32
              forall: if false → result=0, br $qbreak_N
              exists: if true  → result=1, br $qbreak_N
              counter++
              br $qloop_N
            end
          end
          local.get result
        """
        # Evaluate domain
        domain_instrs = self.translate_expr(expr.domain, env)
        if domain_instrs is None:
            return None

        # Translate predicate body with counter as binding
        pred = expr.predicate
        if not pred.params:
            return None
        param_te = pred.params[0]
        if not isinstance(param_te, ast.NamedType):
            return None
        param_type_name = param_te.name
        counter_local = self.alloc_local("i64")
        limit_local = self.alloc_local("i64")
        result_local = self.alloc_local("i32")
        inner_env = env.push(param_type_name, counter_local)

        body_instrs = self.translate_block(pred.body, inner_env)
        if body_instrs is None:
            return None

        # Unique labels
        qid = self._next_quant_id
        self._next_quant_id += 1
        brk = f"$qbreak_{qid}"
        lp = f"$qloop_{qid}"

        init_val = "1" if is_forall else "0"
        instructions: list[str] = []

        # Initialize
        instructions.extend(domain_instrs)
        instructions.append(f"local.set {limit_local}")
        instructions.append("i64.const 0")
        instructions.append(f"local.set {counter_local}")
        instructions.append(f"i32.const {init_val}")
        instructions.append(f"local.set {result_local}")

        # Loop structure
        instructions.append(f"block {brk}")
        instructions.append(f"  loop {lp}")

        # Termination check: counter >= limit → break
        instructions.append(f"    local.get {counter_local}")
        instructions.append(f"    local.get {limit_local}")
        instructions.append("    i64.ge_s")
        instructions.append(f"    br_if {brk}")

        # Evaluate predicate body (counter is in env as @T)
        for instr in body_instrs:
            instructions.append(f"    {instr}")

        # Short-circuit check
        if is_forall:
            # forall: if predicate is false → result=0, break
            instructions.append("    i32.eqz")
            instructions.append("    if")
            instructions.append(f"      i32.const 0")
            instructions.append(f"      local.set {result_local}")
            instructions.append(f"      br {brk}")
            instructions.append("    end")
        else:
            # exists: if predicate is true → result=1, break
            instructions.append("    if")
            instructions.append(f"      i32.const 1")
            instructions.append(f"      local.set {result_local}")
            instructions.append(f"      br {brk}")
            instructions.append("    end")

        # Increment counter
        instructions.append(f"    local.get {counter_local}")
        instructions.append("    i64.const 1")
        instructions.append("    i64.add")
        instructions.append(f"    local.set {counter_local}")
        instructions.append(f"    br {lp}")

        instructions.append("  end")  # loop
        instructions.append("end")    # block

        # Push result
        instructions.append(f"local.get {result_local}")

        return instructions

    # -----------------------------------------------------------------
    # old/new state expressions (postconditions)
    # -----------------------------------------------------------------

    def _translate_old_expr(self, expr: ast.OldExpr) -> list[str] | None:
        """Translate old(State<T>) → local.get of saved pre-execution state."""
        type_name = self._extract_state_type_name(expr.effect_ref)
        if type_name is None:
            return None
        local_idx = self.get_old_state_local(type_name)
        if local_idx is None:
            return None
        return [f"local.get {local_idx}"]

    def _translate_new_expr(self, expr: ast.NewExpr) -> list[str] | None:
        """Translate new(State<T>) → call state_get to read current value."""
        type_name = self._extract_state_type_name(expr.effect_ref)
        if type_name is None:
            return None
        # Look up the state getter import
        if "get" not in self._effect_ops:
            return None
        call_target, _is_void = self._effect_ops["get"]
        return [f"call {call_target}"]

    @staticmethod
    def _extract_state_type_name(
        effect_ref: ast.EffectRefNode,
    ) -> str | None:
        """Extract the type name from a State<T> effect reference."""
        if not isinstance(effect_ref, ast.EffectRef):
            return None
        if effect_ref.name != "State":
            return None
        if not effect_ref.type_args or len(effect_ref.type_args) != 1:
            return None
        arg = effect_ref.type_args[0]
        if isinstance(arg, ast.NamedType):
            return arg.name
        return None
