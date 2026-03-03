"""Function call and effect handler translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class CallsMixin:
    """Methods for translating function calls and effect handlers to WASM."""

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
            if call.name == "length" and len(call.args) == 1:
                return self._translate_length(call.args[0], env)
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
            if call.name == "char_code" and len(call.args) == 2:
                return self._translate_char_code(
                    call.args[0], call.args[1], env,
                )
            if call.name == "parse_nat" and len(call.args) == 1:
                return self._translate_parse_nat(call.args[0], env)
            if call.name == "parse_float64" and len(call.args) == 1:
                return self._translate_parse_float64(call.args[0], env)
            if call.name == "to_string" and len(call.args) == 1:
                return self._translate_to_string(call.args[0], env)
            if call.name == "strip" and len(call.args) == 1:
                return self._translate_strip(call.args[0], env)

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

        # Guard rail: reject calls to functions not defined in this module
        if (self._known_fns
                and call_target not in self._known_fns
                and call_target not in self._ctor_layouts):
            return None

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

    def _translate_length(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate length(array) → Int (i64).

        Evaluates the array → (ptr, len), drops ptr, extends len to i64.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        tmp_len = self.alloc_local("i32")
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        # Stack has (ptr, len); save len, drop ptr
        instructions.append(f"local.set {tmp_len}")
        instructions.append("drop")
        instructions.append(f"local.get {tmp_len}")
        instructions.append("i64.extend_i32_u")
        return instructions

    def _translate_string_length(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate string_length(string) → Int (i64).

        String is (ptr, len) on stack; extract len and extend to i64.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        tmp_len = self.alloc_local("i32")
        instructions: list[str] = []
        instructions.extend(arg_instrs)
        # Stack has (ptr, len); save len, drop ptr
        instructions.append(f"local.set {tmp_len}")
        instructions.append("drop")
        instructions.append(f"local.get {tmp_len}")
        instructions.append("i64.extend_i32_u")
        return instructions

    def _translate_string_concat(
        self, arg_a: ast.Expr, arg_b: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate string_concat(a, b) → String.

        Allocates a new buffer of size len_a + len_b, copies both
        strings into it, and returns (new_ptr, total_len).
        """
        a_instrs = self.translate_expr(arg_a, env)
        b_instrs = self.translate_expr(arg_b, env)
        if a_instrs is None or b_instrs is None:
            return None

        self.needs_alloc = True

        # Locals for both strings and the result
        ptr_a = self.alloc_local("i32")
        len_a = self.alloc_local("i32")
        ptr_b = self.alloc_local("i32")
        len_b = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate string a -> (ptr, len), save to locals
        instructions.extend(a_instrs)
        instructions.append(f"local.set {len_a}")
        instructions.append(f"local.set {ptr_a}")

        # Evaluate string b -> (ptr, len), save to locals
        instructions.extend(b_instrs)
        instructions.append(f"local.set {len_b}")
        instructions.append(f"local.set {ptr_b}")

        # Allocate: total_len = len_a + len_b
        instructions.append(f"local.get {len_a}")
        instructions.append(f"local.get {len_b}")
        instructions.append("i32.add")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")

        # Copy string a: byte-by-byte loop
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_a")
        instructions.append("  loop $lp_a")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {len_a}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_a")
        instructions.append(f"    local.get {dst}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {ptr_a}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append("    i32.store8 offset=0")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_a")
        instructions.append("  end")
        instructions.append("end")

        # Copy string b: byte-by-byte loop at offset len_a
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_b")
        instructions.append("  loop $lp_b")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {len_b}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_b")
        instructions.append(f"    local.get {dst}")
        instructions.append(f"    local.get {len_a}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {ptr_b}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append("    i32.store8 offset=0")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_b")
        instructions.append("  end")
        instructions.append("end")

        # Push result (ptr, len)
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {len_a}")
        instructions.append(f"local.get {len_b}")
        instructions.append("i32.add")
        return instructions

    def _translate_string_slice(
        self,
        arg_s: ast.Expr,
        arg_start: ast.Expr,
        arg_end: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate string_slice(s, start, end) → String.

        Allocates a new buffer of size (end - start), copies the
        substring, and returns (new_ptr, new_len).  start and end
        are Int (i64) and are wrapped to i32.
        """
        s_instrs = self.translate_expr(arg_s, env)
        start_instrs = self.translate_expr(arg_start, env)
        end_instrs = self.translate_expr(arg_end, env)
        if s_instrs is None or start_instrs is None or end_instrs is None:
            return None

        self.needs_alloc = True

        ptr_s = self.alloc_local("i32")
        len_s = self.alloc_local("i32")
        start = self.alloc_local("i32")
        end = self.alloc_local("i32")
        new_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        # Suppress unused-variable warning for len_s — reserved for
        # future bounds checking
        _ = len_s

        instructions: list[str] = []

        # Evaluate string -> (ptr, len)
        instructions.extend(s_instrs)
        instructions.append(f"local.set {len_s}")
        instructions.append(f"local.set {ptr_s}")

        # Evaluate start (i64 → i32)
        instructions.extend(start_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {start}")

        # Evaluate end (i64 → i32)
        instructions.extend(end_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {end}")

        # new_len = end - start
        instructions.append(f"local.get {end}")
        instructions.append(f"local.get {start}")
        instructions.append("i32.sub")
        instructions.append(f"local.set {new_len}")

        # Allocate new buffer
        instructions.append(f"local.get {new_len}")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")

        # Copy bytes: byte-by-byte loop
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_s")
        instructions.append("  loop $lp_s")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {new_len}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_s")
        instructions.append(f"    local.get {dst}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {ptr_s}")
        instructions.append(f"    local.get {start}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append("    i32.store8 offset=0")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_s")
        instructions.append("  end")
        instructions.append("end")

        # Push result (ptr, len)
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {new_len}")
        return instructions

    def _translate_char_code(
        self,
        arg_s: ast.Expr,
        arg_idx: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate char_code(s, idx) → Nat (i64).

        Returns the byte value at the given index in the string.
        """
        s_instrs = self.translate_expr(arg_s, env)
        idx_instrs = self.translate_expr(arg_idx, env)
        if s_instrs is None or idx_instrs is None:
            return None

        ptr_s = self.alloc_local("i32")
        len_s = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        _ = len_s  # reserved for future bounds checking

        instructions: list[str] = []

        # Evaluate string -> (ptr, len)
        instructions.extend(s_instrs)
        instructions.append(f"local.set {len_s}")
        instructions.append(f"local.set {ptr_s}")

        # Evaluate index (i64 → i32)
        instructions.extend(idx_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {idx}")

        # Load byte at ptr + idx, extend to i64
        instructions.append(f"local.get {ptr_s}")
        instructions.append(f"local.get {idx}")
        instructions.append("i32.add")
        instructions.append("i32.load8_u offset=0")
        instructions.append("i64.extend_i32_u")
        return instructions

    def _translate_parse_nat(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate parse_nat(s) → Nat (i64).

        Parses a decimal string to a non-negative integer.
        Iterates through bytes: result = result * 10 + (byte - 48).
        Skips leading spaces.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        result = self.alloc_local("i64")
        byte = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate string -> (ptr, len)
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {slen}")
        instructions.append(f"local.set {ptr}")

        # result = 0, idx = 0
        instructions.append("i64.const 0")
        instructions.append(f"local.set {result}")
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")

        # Loop through bytes
        instructions.append("block $brk_pn")
        instructions.append("  loop $lp_pn")
        # Check idx < len
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {slen}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_pn")
        # Load byte
        instructions.append(f"    local.get {ptr}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append(f"    local.set {byte}")
        # Skip spaces (byte 32)
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 32")
        instructions.append("    i32.eq")
        instructions.append("    if")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("      br $lp_pn")
        instructions.append("    end")
        # result = result * 10 + (byte - 48)
        instructions.append(f"    local.get {result}")
        instructions.append("    i64.const 10")
        instructions.append("    i64.mul")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 48")
        instructions.append("    i32.sub")
        instructions.append("    i64.extend_i32_u")
        instructions.append("    i64.add")
        instructions.append(f"    local.set {result}")
        # idx++
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_pn")
        instructions.append("  end")
        instructions.append("end")

        instructions.append(f"local.get {result}")
        return instructions

    def _translate_parse_float64(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate parse_float64(s) → Float64 (f64).

        Parses a decimal string (with optional sign and decimal point)
        to a 64-bit float.  Handles: optional leading spaces, optional
        sign (+/-), integer part, optional fractional part (.digits).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        sign = self.alloc_local("f64")
        int_part = self.alloc_local("f64")
        frac_part = self.alloc_local("f64")
        frac_div = self.alloc_local("f64")
        byte = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate string -> (ptr, len)
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {slen}")
        instructions.append(f"local.set {ptr}")

        # Initialize
        instructions.append("f64.const 1.0")
        instructions.append(f"local.set {sign}")
        instructions.append("f64.const 0.0")
        instructions.append(f"local.set {int_part}")
        instructions.append("f64.const 0.0")
        instructions.append(f"local.set {frac_part}")
        instructions.append("f64.const 1.0")
        instructions.append(f"local.set {frac_div}")
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")

        # Skip leading spaces
        instructions.append("block $brk_sp")
        instructions.append("  loop $lp_sp")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {slen}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_sp")
        instructions.append(f"    local.get {ptr}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append("    i32.const 32")
        instructions.append("    i32.ne")
        instructions.append("    br_if $brk_sp")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_sp")
        instructions.append("  end")
        instructions.append("end")

        # Check for sign character
        instructions.append(f"local.get {idx}")
        instructions.append(f"local.get {slen}")
        instructions.append("i32.lt_u")
        instructions.append("if")
        # Load current byte
        instructions.append(f"  local.get {ptr}")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append(f"  local.set {byte}")
        # Check minus (45)
        instructions.append(f"  local.get {byte}")
        instructions.append("  i32.const 45")
        instructions.append("  i32.eq")
        instructions.append("  if")
        instructions.append("    f64.const -1.0")
        instructions.append(f"    local.set {sign}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("  else")
        # Check plus (43)
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 43")
        instructions.append("    i32.eq")
        instructions.append("    if")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("    end")
        instructions.append("  end")
        instructions.append("end")

        # Parse integer part (digits before decimal point)
        instructions.append("block $brk_int")
        instructions.append("  loop $lp_int")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {slen}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_int")
        instructions.append(f"    local.get {ptr}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append(f"    local.set {byte}")
        # Break if not a digit (byte < 48 || byte > 57) — catches '.'
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 48")
        instructions.append("    i32.lt_u")
        instructions.append("    br_if $brk_int")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 57")
        instructions.append("    i32.gt_u")
        instructions.append("    br_if $brk_int")
        # int_part = int_part * 10 + (byte - 48)
        instructions.append(f"    local.get {int_part}")
        instructions.append("    f64.const 10.0")
        instructions.append("    f64.mul")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 48")
        instructions.append("    i32.sub")
        instructions.append("    f64.convert_i32_u")
        instructions.append("    f64.add")
        instructions.append(f"    local.set {int_part}")
        # idx++
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_int")
        instructions.append("  end")
        instructions.append("end")

        # Check for decimal point (46)
        instructions.append(f"local.get {idx}")
        instructions.append(f"local.get {slen}")
        instructions.append("i32.lt_u")
        instructions.append("if")
        instructions.append(f"  local.get {ptr}")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.const 46")
        instructions.append("  i32.eq")
        instructions.append("  if")
        # Skip the '.'
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        # Parse fractional digits
        instructions.append("    block $brk_frac")
        instructions.append("    loop $lp_frac")
        instructions.append(f"      local.get {idx}")
        instructions.append(f"      local.get {slen}")
        instructions.append("      i32.ge_u")
        instructions.append("      br_if $brk_frac")
        instructions.append(f"      local.get {ptr}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append("      i32.load8_u offset=0")
        instructions.append(f"      local.set {byte}")
        # Break if not a digit
        instructions.append(f"      local.get {byte}")
        instructions.append("      i32.const 48")
        instructions.append("      i32.lt_u")
        instructions.append("      br_if $brk_frac")
        instructions.append(f"      local.get {byte}")
        instructions.append("      i32.const 57")
        instructions.append("      i32.gt_u")
        instructions.append("      br_if $brk_frac")
        # frac_div *= 10, frac_part = frac_part * 10 + (byte - 48)
        instructions.append(f"      local.get {frac_div}")
        instructions.append("      f64.const 10.0")
        instructions.append("      f64.mul")
        instructions.append(f"      local.set {frac_div}")
        instructions.append(f"      local.get {frac_part}")
        instructions.append("      f64.const 10.0")
        instructions.append("      f64.mul")
        instructions.append(f"      local.get {byte}")
        instructions.append("      i32.const 48")
        instructions.append("      i32.sub")
        instructions.append("      f64.convert_i32_u")
        instructions.append("      f64.add")
        instructions.append(f"      local.set {frac_part}")
        # idx++
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("      br $lp_frac")
        instructions.append("    end")
        instructions.append("    end")
        instructions.append("  end")
        instructions.append("end")

        # Result: sign * (int_part + frac_part / frac_div)
        instructions.append(f"local.get {sign}")
        instructions.append(f"local.get {int_part}")
        instructions.append(f"local.get {frac_part}")
        instructions.append(f"local.get {frac_div}")
        instructions.append("f64.div")
        instructions.append("f64.add")
        instructions.append("f64.mul")
        return instructions

    def _translate_to_string(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate to_string(n) → String (i32_pair).

        Converts an integer to its decimal string representation.
        Uses a temporary 20-byte stack buffer (enough for i64),
        writes digits in reverse, then allocates and copies forward.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        val = self.alloc_local("i64")
        is_neg = self.alloc_local("i32")
        buf = self.alloc_local("i32")  # temp buffer ptr
        pos = self.alloc_local("i32")  # position in buffer (from end)
        dst = self.alloc_local("i32")  # result ptr
        slen = self.alloc_local("i32")
        digit = self.alloc_local("i64")

        instructions: list[str] = []

        # Evaluate argument
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {val}")

        # Allocate a 20-byte temporary buffer for digit reversal
        instructions.append("i32.const 20")
        instructions.append("call $alloc")
        instructions.append(f"local.set {buf}")

        # Start position at end of buffer
        instructions.append("i32.const 20")
        instructions.append(f"local.set {pos}")

        # Check for negative
        instructions.append("i32.const 0")
        instructions.append(f"local.set {is_neg}")
        instructions.append(f"local.get {val}")
        instructions.append("i64.const 0")
        instructions.append("i64.lt_s")
        instructions.append("if")
        instructions.append("  i32.const 1")
        instructions.append(f"  local.set {is_neg}")
        instructions.append("  i64.const 0")
        instructions.append(f"  local.get {val}")
        instructions.append("  i64.sub")
        instructions.append(f"  local.set {val}")
        instructions.append("end")

        # Handle zero case
        instructions.append(f"local.get {val}")
        instructions.append("i64.const 0")
        instructions.append("i64.eq")
        instructions.append("if")
        # pos--, store '0'
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append(f"  local.set {pos}")
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append("  i32.const 48")
        instructions.append("  i32.store8 offset=0")
        instructions.append("else")
        # Extract digits in reverse
        instructions.append("  block $brk_ts")
        instructions.append("  loop $lp_ts")
        instructions.append(f"    local.get {val}")
        instructions.append("    i64.const 0")
        instructions.append("    i64.le_s")
        instructions.append("    br_if $brk_ts")
        # digit = val % 10
        instructions.append(f"    local.get {val}")
        instructions.append("    i64.const 10")
        instructions.append("    i64.rem_u")
        instructions.append(f"    local.set {digit}")
        # val = val / 10
        instructions.append(f"    local.get {val}")
        instructions.append("    i64.const 10")
        instructions.append("    i64.div_u")
        instructions.append(f"    local.set {val}")
        # pos--, store digit + 48
        instructions.append(f"    local.get {pos}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.sub")
        instructions.append(f"    local.set {pos}")
        instructions.append(f"    local.get {buf}")
        instructions.append(f"    local.get {pos}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {digit}")
        instructions.append("    i32.wrap_i64")
        instructions.append("    i32.const 48")
        instructions.append("    i32.add")
        instructions.append("    i32.store8 offset=0")
        instructions.append("    br $lp_ts")
        instructions.append("  end")
        instructions.append("  end")
        instructions.append("end")

        # Prepend '-' if negative
        instructions.append(f"local.get {is_neg}")
        instructions.append("if")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append(f"  local.set {pos}")
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append("  i32.const 45")
        instructions.append("  i32.store8 offset=0")
        instructions.append("end")

        # slen = 20 - pos (number of characters written)
        instructions.append("i32.const 20")
        instructions.append(f"local.get {pos}")
        instructions.append("i32.sub")
        instructions.append(f"local.set {slen}")

        # Result is (buf + pos, slen) — point into the temp buffer
        # We can return a view since the buffer is heap-allocated
        instructions.append(f"local.get {buf}")
        instructions.append(f"local.get {pos}")
        instructions.append("i32.add")
        instructions.append(f"local.get {slen}")
        return instructions

    def _translate_strip(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate strip(s) → String (i32_pair).

        Trims leading and trailing ASCII whitespace (space, tab, CR, LF).
        Returns a slice into the original string (no allocation needed).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        start = self.alloc_local("i32")
        end = self.alloc_local("i32")
        byte = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate string -> (ptr, len)
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {slen}")
        instructions.append(f"local.set {ptr}")

        # start = 0
        instructions.append("i32.const 0")
        instructions.append(f"local.set {start}")

        # Scan forward: skip leading whitespace
        instructions.append("block $brk_lw")
        instructions.append("  loop $lp_lw")
        instructions.append(f"    local.get {start}")
        instructions.append(f"    local.get {slen}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_lw")
        instructions.append(f"    local.get {ptr}")
        instructions.append(f"    local.get {start}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append(f"    local.set {byte}")
        # Check if whitespace: space(32), tab(9), CR(13), LF(10)
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 32")
        instructions.append("    i32.eq")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 9")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 10")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 13")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append("    i32.eqz")
        instructions.append("    br_if $brk_lw")
        instructions.append(f"    local.get {start}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {start}")
        instructions.append("    br $lp_lw")
        instructions.append("  end")
        instructions.append("end")

        # end = len
        instructions.append(f"local.get {slen}")
        instructions.append(f"local.set {end}")

        # Scan backward: skip trailing whitespace
        instructions.append("block $brk_tw")
        instructions.append("  loop $lp_tw")
        instructions.append(f"    local.get {end}")
        instructions.append(f"    local.get {start}")
        instructions.append("    i32.le_u")
        instructions.append("    br_if $brk_tw")
        instructions.append(f"    local.get {ptr}")
        instructions.append(f"    local.get {end}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.sub")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append(f"    local.set {byte}")
        # Check if whitespace
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 32")
        instructions.append("    i32.eq")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 9")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 10")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append(f"    local.get {byte}")
        instructions.append("    i32.const 13")
        instructions.append("    i32.eq")
        instructions.append("    i32.or")
        instructions.append("    i32.eqz")
        instructions.append("    br_if $brk_tw")
        instructions.append(f"    local.get {end}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.sub")
        instructions.append(f"    local.set {end}")
        instructions.append("    br $lp_tw")
        instructions.append("  end")
        instructions.append("end")

        # Result: (ptr + start, end - start)
        instructions.append(f"local.get {ptr}")
        instructions.append(f"local.get {start}")
        instructions.append("i32.add")
        instructions.append(f"local.get {end}")
        instructions.append(f"local.get {start}")
        instructions.append("i32.sub")
        return instructions

    def _translate_handle_expr(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate a handle expression to WASM.

        Currently supports State<T> handlers via host imports.
        Other handler types cause the function to be skipped.
        """
        effect = expr.effect
        if not isinstance(effect, ast.EffectRef):
            return None

        if effect.name == "State" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_state(expr, env)

        # Unsupported handler type
        return None

    def _translate_handle_state(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate handle[State<T>](@T = init) { ... } in { body }.

        Compiles by:
        1. Evaluating init_expr and calling state_put_T to set initial state
        2. Temporarily injecting get/put effect ops for the body
        3. Compiling the body with these ops active
        4. Restoring the previous effect ops
        """
        assert isinstance(expr.effect, ast.EffectRef)
        type_arg = expr.effect.type_args[0]  # type: ignore[index]
        if isinstance(type_arg, ast.NamedType):
            type_name = type_arg.name
        else:
            return None

        wasm_type = self._type_name_to_wasm(type_name)
        put_import = f"$vera.state_put_{type_name}"
        get_import = f"$vera.state_get_{type_name}"

        instructions: list[str] = []

        # 1. Initialize state: compile init_expr, call state_put
        if expr.state is not None:
            init_instrs = self.translate_expr(expr.state.init_expr, env)
            if init_instrs is None:
                return None
            instructions.extend(init_instrs)
            instructions.append(f"call {put_import}")
        # If no state clause, state starts at default (0)

        # 2. Save current effect_ops and inject handler ops
        saved_ops = dict(self._effect_ops)
        self._effect_ops["get"] = (get_import, False)
        self._effect_ops["put"] = (put_import, True)

        # 3. Compile handler body
        body_instrs = self.translate_block(expr.body, env)

        # 4. Restore effect_ops
        self._effect_ops = saved_ops

        if body_instrs is None:
            return None

        instructions.extend(body_instrs)
        return instructions
