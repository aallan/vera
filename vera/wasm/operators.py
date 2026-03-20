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
                    return None  # pragma: no cover
            type_name = f"{ref.type_name}<{', '.join(arg_names)}>"
        local_idx = env.resolve(type_name, ref.index)
        if local_idx is None:
            return None  # pragma: no cover
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
            return None  # pragma: no cover — non-FnCall RHS unsupported

        left = self.translate_expr(expr.left, env)
        right = self.translate_expr(expr.right, env)
        if left is None or right is None:
            return None  # pragma: no cover

        op = expr.op
        ltype = self._infer_expr_wasm_type(expr.left)

        # Arithmetic
        if op in self._ARITH_OPS:
            if ltype == "f64":
                if op == ast.BinOp.MOD:
                    return self._translate_f64_mod(left, right)
                if op not in self._ARITH_OPS_F64:  # pragma: no cover
                    return None  # unsupported float op
                return left + right + [self._ARITH_OPS_F64[op]]
            return left + right + [self._ARITH_OPS[op]]

        # Comparison — choose i32/i64/f64 based on operand types
        if op in self._CMP_OPS:
            rtype = self._infer_expr_wasm_type(expr.right)
            if ltype == "f64" or rtype == "f64":
                return left + right + [self._CMP_OPS_F64[op]]
            # String equality — byte-by-byte comparison
            if (ltype == "i32_pair" and rtype == "i32_pair"
                    and op in (ast.BinOp.EQ, ast.BinOp.NEQ)):
                result = self._translate_string_eq(left, right)
                if op == ast.BinOp.NEQ:
                    result.append("i32.eqz")
                return result
            if ltype == "i32" and rtype == "i32":
                # Byte operands use unsigned i32 comparison
                lv = self._infer_vera_type(expr.left)
                rv = self._infer_vera_type(expr.right)
                if lv == "Byte" or rv == "Byte":
                    i32_op = self._CMP_OPS[op].replace("i64.", "i32.")
                    i32_op = i32_op.replace("_s", "_u")
                    return left + right + [i32_op]
                # ADT structural equality (§9.8 auto-derivation)
                if (op in (ast.BinOp.EQ, ast.BinOp.NEQ)
                        and lv is not None
                        and lv not in ("Bool", "Byte")
                        and lv in self._adt_type_names):
                    adt_eq = self._translate_adt_eq(left, right, lv)
                    if adt_eq is not None:
                        if op == ast.BinOp.NEQ:
                            adt_eq.append("i32.eqz")
                        return adt_eq
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

        return None  # pragma: no cover

    # -----------------------------------------------------------------
    # ADT structural equality
    # -----------------------------------------------------------------

    def _translate_adt_eq(
        self, left: list[str], right: list[str], adt_name: str,
    ) -> list[str] | None:
        """Generate WASM for structural equality of two ADT values.

        Compares two heap-allocated ADT pointers structurally:
        1. Load tags from both pointers (i32.load at offset 0)
        2. If tags differ → false
        3. If tags match and the constructor has no fields → true
        4. If tags match with fields → load and compare each field

        Only handles fields with scalar WASM types (i64, i32, f64).
        String/Array (i32_pair) fields are not auto-derivable.
        """
        # Build list of (ctor_name, layout) for this ADT, sorted by tag
        adt_ctors: list[tuple[str, object]] = []
        for ctor_name, parent_adt in self._ctor_to_adt.items():
            if parent_adt == adt_name and ctor_name in self._ctor_layouts:
                adt_ctors.append((ctor_name, self._ctor_layouts[ctor_name]))
        if not adt_ctors:
            return None  # pragma: no cover
        adt_ctors.sort(key=lambda x: x[1].tag)

        # Store operands in temp locals
        tmp_l = self.alloc_local("i32")
        tmp_r = self.alloc_local("i32")
        instrs: list[str] = (
            left + [f"local.set {tmp_l}"]
            + right + [f"local.set {tmp_r}"]
        )

        # Simple enum: all constructors have 0 fields → compare tags
        if all(len(lay.field_offsets) == 0 for _, lay in adt_ctors):
            instrs += [
                f"local.get {tmp_l}", "i32.load",
                f"local.get {tmp_r}", "i32.load",
                "i32.eq",
            ]
            return instrs

        # General case: compare tags, then dispatch on tag for fields
        tag_local = self.alloc_local("i32")
        instrs += [
            f"local.get {tmp_l}", "i32.load",
            f"local.set {tag_local}",
            # Tags must match
            f"local.get {tag_local}",
            f"local.get {tmp_r}", "i32.load",
            "i32.eq",
            "if (result i32)",
        ]

        # Inner: dispatch on tag value for constructors that have fields
        ctors_with_fields = [
            (name, lay) for name, lay in adt_ctors if lay.field_offsets
        ]

        if not ctors_with_fields:  # pragma: no cover
            # All fieldless — tags matching is sufficient
            instrs.append("  i32.const 1")
        else:
            # Nested if-else chain for each constructor with fields
            for i, (_cname, layout) in enumerate(ctors_with_fields):
                pad = "  " * (i + 1)
                instrs.append(f"{pad}local.get {tag_local}")
                instrs.append(f"{pad}i32.const {layout.tag}")
                instrs.append(f"{pad}i32.eq")
                instrs.append(f"{pad}if (result i32)")
                # Compare all fields for this constructor
                fpad = pad + "  "
                first_field = True
                for offset, wasm_type in layout.field_offsets:
                    load_op = self._adt_field_load(wasm_type)
                    eq_op = self._adt_field_eq(wasm_type)
                    if load_op is None or eq_op is None:
                        return None  # pragma: no cover — unsupported field type
                    instrs.append(f"{fpad}local.get {tmp_l}")
                    instrs.append(f"{fpad}{load_op} offset={offset}")
                    instrs.append(f"{fpad}local.get {tmp_r}")
                    instrs.append(f"{fpad}{load_op} offset={offset}")
                    instrs.append(f"{fpad}{eq_op}")
                    if not first_field:
                        instrs.append(f"{fpad}i32.and")
                    first_field = False
                instrs.append(f"{pad}else")
            # Innermost else: fieldless constructor, tags match → true
            inner_pad = "  " * (len(ctors_with_fields) + 1)
            instrs.append(f"{inner_pad}i32.const 1")
            # Close all nested if/else blocks
            for i in range(len(ctors_with_fields) - 1, -1, -1):
                pad = "  " * (i + 1)
                instrs.append(f"{pad}end")

        # Close outer tags-match if
        instrs += ["else", "  i32.const 0", "end"]
        return instrs

    @staticmethod
    def _adt_field_load(wasm_type: str) -> str | None:
        """WASM load instruction for an ADT field type."""
        return {"i64": "i64.load", "i32": "i32.load",
                "f64": "f64.load"}.get(wasm_type)

    @staticmethod
    def _adt_field_eq(wasm_type: str) -> str | None:
        """WASM equality instruction for an ADT field type."""
        return {"i64": "i64.eq", "i32": "i32.eq",
                "f64": "f64.eq"}.get(wasm_type)

    # -----------------------------------------------------------------
    # String equality
    # -----------------------------------------------------------------

    def _translate_string_eq(
        self, left: list[str], right: list[str],
    ) -> list[str]:
        """Generate WASM for string equality (byte-by-byte).

        Compares two (ptr, len) pairs:
        1. Quick length check — if lengths differ, false
        2. Same pointer shortcut — if ptrs match, true
        3. Byte-by-byte comparison loop
        """
        ptr1 = self.alloc_local("i32")
        len1 = self.alloc_local("i32")
        ptr2 = self.alloc_local("i32")
        len2 = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        result = self.alloc_local("i32")

        instrs: list[str] = []
        # Store both strings
        instrs += left + [f"local.set {len1}", f"local.set {ptr1}"]
        instrs += right + [f"local.set {len2}", f"local.set {ptr2}"]

        # Default: equal (1)
        instrs += [f"i32.const 1", f"local.set {result}"]

        # Length check
        instrs += [
            f"local.get {len1}", f"local.get {len2}", "i32.ne",
            "if",
            f"  i32.const 0", f"  local.set {result}",
            "else",
        ]

        # Pointer check (fast path for interned strings)
        instrs += [
            f"  local.get {ptr1}", f"  local.get {ptr2}", "  i32.ne",
            "  if",
        ]

        # Byte-by-byte comparison loop
        instrs += [
            f"    i32.const 0", f"    local.set {idx}",
            "    block $seq_break",
            "      loop $seq_loop",
            f"        local.get {idx}",
            f"        local.get {len1}",
            "        i32.ge_u",
            "        br_if $seq_break",
            # Compare bytes at idx
            f"        local.get {ptr1}",
            f"        local.get {idx}",
            "        i32.add",
            "        i32.load8_u",
            f"        local.get {ptr2}",
            f"        local.get {idx}",
            "        i32.add",
            "        i32.load8_u",
            "        i32.ne",
            "        if",
            f"          i32.const 0",
            f"          local.set {result}",
            "          br $seq_break",
            "        end",
            # Increment idx
            f"        local.get {idx}",
            "        i32.const 1",
            "        i32.add",
            f"        local.set {idx}",
            "        br $seq_loop",
            "      end",  # loop
            "    end",    # block
        ]

        # Close pointer-check if and length-check if
        instrs += ["  end", "end"]
        instrs += [f"local.get {result}"]
        return instrs

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
            return None  # pragma: no cover

        if expr.op == ast.UnaryOp.NOT:
            return operand + ["i32.eqz"]
        if expr.op == ast.UnaryOp.NEG:
            if self._infer_expr_wasm_type(expr.operand) == "f64":
                return operand + ["f64.neg"]
            return ["i64.const 0"] + operand + ["i64.sub"]
        return None  # pragma: no cover

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
                else:  # pragma: no cover
                    # Fallback: try to_string (Int-compatible types)
                    parts.append(ast.FnCall(
                        name="to_string", args=(p,), span=expr.span,
                    ))

        if not parts:  # pragma: no cover
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
        return None  # pragma: no cover

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
            return None  # pragma: no cover
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
            return None  # pragma: no cover

        # Translate predicate body with counter as binding
        pred = expr.predicate
        if not pred.params:
            return None  # pragma: no cover
        param_te = pred.params[0]
        if not isinstance(param_te, ast.NamedType):
            return None  # pragma: no cover
        param_type_name = param_te.name
        counter_local = self.alloc_local("i64")
        limit_local = self.alloc_local("i64")
        result_local = self.alloc_local("i32")
        inner_env = env.push(param_type_name, counter_local)

        body_instrs = self.translate_block(pred.body, inner_env)
        if body_instrs is None:
            return None  # pragma: no cover

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
            return None  # pragma: no cover
        local_idx = self.get_old_state_local(type_name)
        if local_idx is None:
            return None  # pragma: no cover
        return [f"local.get {local_idx}"]

    def _translate_new_expr(self, expr: ast.NewExpr) -> list[str] | None:
        """Translate new(State<T>) → call state_get to read current value."""
        type_name = self._extract_state_type_name(expr.effect_ref)
        if type_name is None:
            return None  # pragma: no cover
        # Look up the state getter import
        if "get" not in self._effect_ops:
            return None  # pragma: no cover
        call_target, _is_void = self._effect_ops["get"]
        return [f"call {call_target}"]

    @staticmethod
    def _extract_state_type_name(
        effect_ref: ast.EffectRefNode,
    ) -> str | None:
        """Extract the type name from a State<T> effect reference."""
        if not isinstance(effect_ref, ast.EffectRef):
            return None  # pragma: no cover
        if effect_ref.name != "State":
            return None  # pragma: no cover
        if not effect_ref.type_args or len(effect_ref.type_args) != 1:
            return None  # pragma: no cover
        arg = effect_ref.type_args[0]
        if isinstance(arg, ast.NamedType):
            return arg.name
        return None  # pragma: no cover
