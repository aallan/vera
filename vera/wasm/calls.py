"""Function call and effect handler translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import (
    WasmSlotEnv,
    _element_mem_size,
    _element_store_op,
    _is_pair_element_type,
    gc_shadow_push,
)


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
            if call.name == "strip" and len(call.args) == 1:
                return self._translate_strip(call.args[0], env)
            if call.name == "array_push" and len(call.args) == 2:
                return self._translate_array_push(
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

        # Check if this is a closure application: apply_fn(closure, args...)
        if call.name == "apply_fn" and len(call.args) >= 2:
            return self._translate_apply_fn(call, env)

        # Check if this is an effect operation (e.g. get/put/throw)
        if call.name in self._effect_ops:
            target_name, _is_void = self._effect_ops[call.name]
            instructions: list[str] = []
            for arg in call.args:
                arg_instrs = self.translate_expr(arg, env)
                if arg_instrs is None:
                    return None
                instructions.extend(arg_instrs)
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
        instructions: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            instructions.extend(arg_instrs)
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

    def _translate_array_push(
        self,
        arr_arg: ast.Expr,
        elem_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_push(array, element) → Array<T>.

        Allocates a new array of size (len + 1), copies the old elements
        byte-by-byte, appends the new element, and returns (new_ptr, new_len).
        """
        arr_instrs = self.translate_expr(arr_arg, env)
        elem_instrs = self.translate_expr(elem_arg, env)
        if arr_instrs is None or elem_instrs is None:
            return None

        # Infer element type from the pushed element
        elem_type = self._infer_vera_type(elem_arg)
        if elem_type is None:
            return None
        elem_size = _element_mem_size(elem_type)
        if elem_size is None:
            return None

        is_pair = _is_pair_element_type(elem_type)
        store_op = _element_store_op(elem_type)
        if store_op is None and not is_pair:
            return None

        self.needs_alloc = True

        # Locals for old array
        ptr_arr = self.alloc_local("i32")
        len_arr = self.alloc_local("i32")
        # Locals for new element
        if is_pair:
            elem_ptr = self.alloc_local("i32")
            elem_len = self.alloc_local("i32")
        else:
            elem_val = self.alloc_local(
                "i64" if elem_type in ("Int", "Nat") else
                "f64" if elem_type == "Float64" else "i32"
            )
        # Locals for copy loop and destination
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        old_bytes = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate array arg → (ptr, len), save to locals
        instructions.extend(arr_instrs)
        instructions.append(f"local.set {len_arr}")
        instructions.append(f"local.set {ptr_arr}")

        # Evaluate element arg, save to locals
        instructions.extend(elem_instrs)
        if is_pair:
            instructions.append(f"local.set {elem_len}")
            instructions.append(f"local.set {elem_ptr}")
        else:
            instructions.append(f"local.set {elem_val}")

        # Compute old_bytes = len_arr * elem_size
        instructions.append(f"local.get {len_arr}")
        instructions.append(f"i32.const {elem_size}")
        instructions.append("i32.mul")
        instructions.append(f"local.set {old_bytes}")

        # Allocate: (len_arr + 1) * elem_size = old_bytes + elem_size
        instructions.append(f"local.get {old_bytes}")
        instructions.append(f"i32.const {elem_size}")
        instructions.append("i32.add")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))

        # Copy old elements: byte-by-byte loop
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_copy")
        instructions.append("  loop $lp_copy")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {old_bytes}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_copy")
        instructions.append(f"    local.get {dst}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {ptr_arr}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u offset=0")
        instructions.append("    i32.store8 offset=0")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_copy")
        instructions.append("  end")
        instructions.append("end")

        # Store new element at dst + old_bytes
        if is_pair:
            # Store ptr at old_bytes offset
            instructions.append(f"local.get {dst}")
            instructions.append(f"local.get {old_bytes}")
            instructions.append("i32.add")
            instructions.append(f"local.get {elem_ptr}")
            instructions.append("i32.store offset=0")
            # Store len at old_bytes + 4
            instructions.append(f"local.get {dst}")
            instructions.append(f"local.get {old_bytes}")
            instructions.append("i32.add")
            instructions.append(f"local.get {elem_len}")
            instructions.append("i32.store offset=4")
        else:
            instructions.append(f"local.get {dst}")
            instructions.append(f"local.get {old_bytes}")
            instructions.append("i32.add")
            instructions.append(f"local.get {elem_val}")
            instructions.append(f"{store_op} offset=0")

        # Push result: (new_ptr, new_len)
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {len_arr}")
        instructions.append("i32.const 1")
        instructions.append("i32.add")
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
        instructions.extend(gc_shadow_push(dst))

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
        instructions.extend(gc_shadow_push(dst))

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
        """Translate parse_nat(s) → Result<Nat, String> (i32 pointer).

        Returns an ADT heap object:
          Ok(Nat):     [tag=0 : i32] [pad 4] [value : i64]   (16 bytes)
          Err(String): [tag=1 : i32] [ptr : i32] [len : i32]  (16 bytes)

        Validates that the input contains at least one digit (0-9) and
        only digits/spaces.  Skips leading and trailing spaces.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        result = self.alloc_local("i64")
        byte = self.alloc_local("i32")
        out = self.alloc_local("i32")
        has_digit = self.alloc_local("i32")

        # Intern error strings
        empty_off, empty_len = self.string_pool.intern("empty string")
        invalid_off, invalid_len = self.string_pool.intern("invalid digit")

        ins: list[str] = []

        # Evaluate string → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Initialise: result = 0, idx = 0, has_digit = 0
        ins.append("i64.const 0")
        ins.append(f"local.set {result}")
        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("i32.const 0")
        ins.append(f"local.set {has_digit}")

        # -- block structure: block $done { block $err { parse } Err }
        ins.append("block $done_pn")
        ins.append("block $err_pn")

        # -- Parse loop ------------------------------------------------
        ins.append("block $brk_pn")
        ins.append("  loop $lp_pn")
        # idx >= len → break
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_pn")
        # Load byte
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {byte}")
        # Skip space (byte 32)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 32")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("      br $lp_pn")
        ins.append("    end")
        # Check byte < '0' (48) → error
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.lt_u")
        ins.append("    br_if $err_pn")
        # Check byte > '9' (57) → error
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 57")
        ins.append("    i32.gt_u")
        ins.append("    br_if $err_pn")
        # Digit: result = result * 10 + (byte - 48)
        ins.append(f"    local.get {result}")
        ins.append("    i64.const 10")
        ins.append("    i64.mul")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.sub")
        ins.append("    i64.extend_i32_u")
        ins.append("    i64.add")
        ins.append(f"    local.set {result}")
        # Mark that we saw a digit
        ins.append("    i32.const 1")
        ins.append(f"    local.set {has_digit}")
        # idx++
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_pn")
        ins.append("  end")   # loop
        ins.append("end")     # block $brk_pn

        # -- After loop: no digits seen → error
        ins.append(f"local.get {has_digit}")
        ins.append("i32.eqz")
        ins.append("br_if $err_pn")

        # -- Ok path: allocate 16 bytes, tag=0, Nat at offset 8 ----------
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")           # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {result}")
        ins.append("i64.store offset=8")  # Nat value
        ins.append("br $done_pn")

        ins.append("end")  # block $err_pn

        # -- Err path: allocate 16 bytes, tag=1, String at offsets 4,8 ---
        # Choose error message: if idx < slen the loop exited early on an
        # invalid character → "invalid digit"; otherwise the string was
        # empty or all spaces → "empty string".
        ins.append(f"local.get {idx}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {invalid_off}")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append(f"local.set {idx}")   # reuse idx for err string ptr
        ins.append(f"local.get {idx}")   # idx now holds the err string ptr
        ins.append(f"i32.const {invalid_off}")
        ins.append("i32.eq")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {invalid_len}")
        ins.append("else")
        ins.append(f"  i32.const {empty_len}")
        ins.append("end")
        ins.append(f"local.set {byte}")  # reuse byte for err string len
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")           # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {idx}")
        ins.append("i32.store offset=4")  # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"local.get {byte}")
        ins.append("i32.store offset=8")  # string len

        ins.append("end")  # block $done_pn

        ins.append(f"local.get {out}")
        return ins

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
        instructions.extend(gc_shadow_push(buf))

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

        # Allocate exact-size result buffer and copy digits forward.
        # (Avoids returning an interior pointer into the temp buffer,
        # which conservative GC would not recognise as a valid root.)
        instructions.append(f"local.get {slen}")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))
        # Copy loop: dst[i] = buf[pos + i] for i in 0..slen
        ci = self.alloc_local("i32")
        instructions.append("i32.const 0")
        instructions.append(f"local.set {ci}")
        instructions.append("block $brk_cp")
        instructions.append("loop $lp_cp")
        instructions.append(f"  local.get {ci}")
        instructions.append(f"  local.get {slen}")
        instructions.append("  i32.ge_u")
        instructions.append("  br_if $brk_cp")
        # dst[ci] = buf[pos + ci]
        instructions.append(f"  local.get {dst}")
        instructions.append(f"  local.get {ci}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {ci}")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.store8 offset=0")
        # ci++
        instructions.append(f"  local.get {ci}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.add")
        instructions.append(f"  local.set {ci}")
        instructions.append("  br $lp_cp")
        instructions.append("end")
        instructions.append("end")

        # Result: (dst, slen)
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {slen}")
        return instructions

    def _translate_bool_to_string(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate bool_to_string(b) → String (i32_pair).

        Returns the interned string "true" or "false" depending on
        the boolean value.  No heap allocation needed.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        true_off, true_len = self.string_pool.intern("true")
        false_off, false_len = self.string_pool.intern("false")

        instructions: list[str] = []
        instructions.extend(arg_instrs)
        # Bool is i32: 1 = true, 0 = false
        instructions.append(f"if (result i32 i32)")
        instructions.append(f"  i32.const {true_off}")
        instructions.append(f"  i32.const {true_len}")
        instructions.append("else")
        instructions.append(f"  i32.const {false_off}")
        instructions.append(f"  i32.const {false_len}")
        instructions.append("end")
        return instructions

    def _translate_byte_to_string(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate byte_to_string(b) → String (i32_pair).

        Allocates a 1-byte buffer and stores the byte value as a
        single character.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        bval = self.alloc_local("i32")
        dst = self.alloc_local("i32")

        instructions: list[str] = []
        instructions.extend(arg_instrs)
        # Byte is i32 in WASM (unlike Nat which is i64)
        instructions.append(f"local.set {bval}")

        # Allocate 1 byte
        instructions.append("i32.const 1")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))

        # Store the byte value
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {bval}")
        instructions.append("i32.store8 offset=0")

        # Return (ptr, 1)
        instructions.append(f"local.get {dst}")
        instructions.append("i32.const 1")
        return instructions

    def _translate_float_to_string(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate float_to_string(f) → String (i32_pair).

        Converts a Float64 to its decimal string representation.
        Uses a 32-byte buffer.  Writes sign, integer digits, decimal
        point, then up to 6 fractional digits (trailing zeros trimmed,
        but at least one decimal digit kept so 42.0 stays "42.0").
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        fval = self.alloc_local("f64")
        ival = self.alloc_local("i64")
        buf = self.alloc_local("i32")
        pos = self.alloc_local("i32")   # write position (forward)
        is_neg = self.alloc_local("i32")
        digit = self.alloc_local("i64")
        # For integer-part digit reversal
        tbuf = self.alloc_local("i32")  # temp buffer for int digits
        tpos = self.alloc_local("i32")  # position in temp buffer
        tlen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        frac_val = self.alloc_local("i64")

        instructions: list[str] = []

        # Evaluate argument
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {fval}")

        # Allocate 32-byte output buffer
        instructions.append("i32.const 32")
        instructions.append("call $alloc")
        instructions.append(f"local.set {buf}")
        instructions.extend(gc_shadow_push(buf))
        instructions.append("i32.const 0")
        instructions.append(f"local.set {pos}")

        # Check for negative
        instructions.append("i32.const 0")
        instructions.append(f"local.set {is_neg}")
        instructions.append(f"local.get {fval}")
        instructions.append("f64.const 0")
        instructions.append("f64.lt")
        instructions.append("if")
        instructions.append("  i32.const 1")
        instructions.append(f"  local.set {is_neg}")
        instructions.append(f"  local.get {fval}")
        instructions.append("  f64.neg")
        instructions.append(f"  local.set {fval}")
        instructions.append("end")

        # Write '-' if negative
        instructions.append(f"local.get {is_neg}")
        instructions.append("if")
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append("  i32.const 45")  # '-'
        instructions.append("  i32.store8 offset=0")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.add")
        instructions.append(f"  local.set {pos}")
        instructions.append("end")

        # Extract integer part: ival = i64.trunc_f64_s(fval)
        instructions.append(f"local.get {fval}")
        instructions.append("i64.trunc_f64_s")
        instructions.append(f"local.set {ival}")

        # Write integer digits using a temp buffer (reverse then copy)
        # Allocate 20-byte temp buffer for int digits
        instructions.append("i32.const 20")
        instructions.append("call $alloc")
        instructions.append(f"local.set {tbuf}")
        instructions.extend(gc_shadow_push(tbuf))
        instructions.append("i32.const 20")
        instructions.append(f"local.set {tpos}")

        # Handle zero integer part
        instructions.append(f"local.get {ival}")
        instructions.append("i64.const 0")
        instructions.append("i64.eq")
        instructions.append("if")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append(f"  local.set {tpos}")
        instructions.append(f"  local.get {tbuf}")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.add")
        instructions.append("  i32.const 48")
        instructions.append("  i32.store8 offset=0")
        instructions.append("else")
        # Extract digits in reverse
        instructions.append("  block $brk_fi")
        instructions.append("  loop $lp_fi")
        instructions.append(f"    local.get {ival}")
        instructions.append("    i64.const 0")
        instructions.append("    i64.le_s")
        instructions.append("    br_if $brk_fi")
        instructions.append(f"    local.get {ival}")
        instructions.append("    i64.const 10")
        instructions.append("    i64.rem_u")
        instructions.append(f"    local.set {digit}")
        instructions.append(f"    local.get {ival}")
        instructions.append("    i64.const 10")
        instructions.append("    i64.div_u")
        instructions.append(f"    local.set {ival}")
        instructions.append(f"    local.get {tpos}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.sub")
        instructions.append(f"    local.set {tpos}")
        instructions.append(f"    local.get {tbuf}")
        instructions.append(f"    local.get {tpos}")
        instructions.append("    i32.add")
        instructions.append(f"    local.get {digit}")
        instructions.append("    i32.wrap_i64")
        instructions.append("    i32.const 48")
        instructions.append("    i32.add")
        instructions.append("    i32.store8 offset=0")
        instructions.append("    br $lp_fi")
        instructions.append("  end")
        instructions.append("  end")
        instructions.append("end")

        # Copy integer digits from tbuf[tpos..20] to buf[pos..]
        # tlen = 20 - tpos
        instructions.append("i32.const 20")
        instructions.append(f"local.get {tpos}")
        instructions.append("i32.sub")
        instructions.append(f"local.set {tlen}")
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_cp")
        instructions.append("loop $lp_cp")
        instructions.append(f"  local.get {idx}")
        instructions.append(f"  local.get {tlen}")
        instructions.append("  i32.ge_u")
        instructions.append("  br_if $brk_cp")
        # buf[pos + idx] = tbuf[tpos + idx]
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {tbuf}")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.store8 offset=0")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.add")
        instructions.append(f"  local.set {idx}")
        instructions.append("  br $lp_cp")
        instructions.append("end")
        instructions.append("end")
        # pos += tlen
        instructions.append(f"local.get {pos}")
        instructions.append(f"local.get {tlen}")
        instructions.append("i32.add")
        instructions.append(f"local.set {pos}")

        # Write decimal point
        instructions.append(f"local.get {buf}")
        instructions.append(f"local.get {pos}")
        instructions.append("i32.add")
        instructions.append("i32.const 46")  # '.'
        instructions.append("i32.store8 offset=0")
        instructions.append(f"local.get {pos}")
        instructions.append("i32.const 1")
        instructions.append("i32.add")
        instructions.append(f"local.set {pos}")

        # Fractional part: frac = (fval - floor(fval)) * 1_000_000
        # Re-extract integer part as f64 for subtraction
        instructions.append(f"local.get {fval}")
        instructions.append(f"local.get {fval}")
        instructions.append("f64.floor")
        instructions.append("f64.sub")
        instructions.append("f64.const 1000000")
        instructions.append("f64.mul")
        # Round to nearest integer
        instructions.append("f64.const 0.5")
        instructions.append("f64.add")
        instructions.append("i64.trunc_f64_s")
        instructions.append(f"local.set {frac_val}")

        # Write exactly 6 fractional digits (will trim trailing zeros after)
        # We write them in reverse into tbuf, then copy forward
        instructions.append("i32.const 6")
        instructions.append(f"local.set {tlen}")
        instructions.append("i32.const 6")
        instructions.append(f"local.set {tpos}")

        instructions.append("block $brk_fd")
        instructions.append("loop $lp_fd")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.const 0")
        instructions.append("  i32.le_s")
        instructions.append("  br_if $brk_fd")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append(f"  local.set {tpos}")
        instructions.append(f"  local.get {tbuf}")
        instructions.append(f"  local.get {tpos}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {frac_val}")
        instructions.append("  i64.const 10")
        instructions.append("  i64.rem_u")
        instructions.append("  i32.wrap_i64")
        instructions.append("  i32.const 48")
        instructions.append("  i32.add")
        instructions.append("  i32.store8 offset=0")
        instructions.append(f"  local.get {frac_val}")
        instructions.append("  i64.const 10")
        instructions.append("  i64.div_u")
        instructions.append(f"  local.set {frac_val}")
        instructions.append("  br $lp_fd")
        instructions.append("end")
        instructions.append("end")

        # Trim trailing zeros: tlen = 6, but keep at least 1 digit
        # Scan from position 5 down to 1
        instructions.append("block $brk_tz")
        instructions.append("loop $lp_tz")
        # If tlen <= 1, stop (keep at least 1 fractional digit)
        instructions.append(f"  local.get {tlen}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.le_s")
        instructions.append("  br_if $brk_tz")
        # Check if tbuf[tlen - 1] == '0' (48)
        instructions.append(f"  local.get {tbuf}")
        instructions.append(f"  local.get {tlen}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.const 48")
        instructions.append("  i32.ne")
        instructions.append("  br_if $brk_tz")
        instructions.append(f"  local.get {tlen}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.sub")
        instructions.append(f"  local.set {tlen}")
        instructions.append("  br $lp_tz")
        instructions.append("end")
        instructions.append("end")

        # Copy tlen fractional digits from tbuf[0..tlen] to buf[pos..]
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_cf")
        instructions.append("loop $lp_cf")
        instructions.append(f"  local.get {idx}")
        instructions.append(f"  local.get {tlen}")
        instructions.append("  i32.ge_u")
        instructions.append("  br_if $brk_cf")
        instructions.append(f"  local.get {buf}")
        instructions.append(f"  local.get {pos}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {tbuf}")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.store8 offset=0")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.add")
        instructions.append(f"  local.set {idx}")
        instructions.append("  br $lp_cf")
        instructions.append("end")
        instructions.append("end")

        # Final length = pos + tlen
        instructions.append(f"local.get {pos}")
        instructions.append(f"local.get {tlen}")
        instructions.append("i32.add")
        instructions.append(f"local.set {pos}")

        # Return (buf, pos) where pos is now the total length
        instructions.append(f"local.get {buf}")
        instructions.append(f"local.get {pos}")
        return instructions

    def _translate_strip(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate strip(s) → String (i32_pair).

        Trims leading and trailing ASCII whitespace (space, tab, CR, LF).
        Allocates a new buffer and copies the trimmed content to avoid
        returning an interior pointer (which conservative GC cannot track).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        start = self.alloc_local("i32")
        end = self.alloc_local("i32")
        byte = self.alloc_local("i32")
        new_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")

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

        # new_len = end - start
        instructions.append(f"local.get {end}")
        instructions.append(f"local.get {start}")
        instructions.append("i32.sub")
        instructions.append(f"local.set {new_len}")

        # Allocate new buffer and copy trimmed content
        instructions.append(f"local.get {new_len}")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))

        # Copy loop: dst[i] = ptr[start + i] for i in 0..new_len
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_st")
        instructions.append("loop $lp_st")
        instructions.append(f"  local.get {idx}")
        instructions.append(f"  local.get {new_len}")
        instructions.append("  i32.ge_u")
        instructions.append("  br_if $brk_st")
        instructions.append(f"  local.get {dst}")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {ptr}")
        instructions.append(f"  local.get {start}")
        instructions.append("  i32.add")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.add")
        instructions.append("  i32.load8_u offset=0")
        instructions.append("  i32.store8 offset=0")
        instructions.append(f"  local.get {idx}")
        instructions.append("  i32.const 1")
        instructions.append("  i32.add")
        instructions.append(f"  local.set {idx}")
        instructions.append("  br $lp_st")
        instructions.append("end")
        instructions.append("end")

        # Result: (dst, new_len)
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {new_len}")
        return instructions

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

    def _translate_handle_expr(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate a handle expression to WASM.

        Supports State<T> handlers via host imports and Exn<E>
        handlers via WASM exception handling (try_table/catch/throw).
        Other handler types cause the function to be skipped.
        """
        effect = expr.effect
        if not isinstance(effect, ast.EffectRef):
            return None

        if effect.name == "State" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_state(expr, env)

        if effect.name == "Exn" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_exn(expr, env)

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

    def _translate_handle_exn(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate handle[Exn<E>] { throw(@E) -> handler } in { body }.

        Uses WASM exception handling (try_table/catch/throw):
          block $done (result T)
            block $catch (result E)
              try_table (result T) (catch $exn_E $catch)
                <body>
              end
              br $done
            end
            ;; caught value on stack
            local.set $thrown
            <handler clause body>
          end
        """
        assert isinstance(expr.effect, ast.EffectRef)
        type_arg = expr.effect.type_args[0]  # type: ignore[index]
        if not isinstance(type_arg, ast.NamedType):
            return None
        type_name = type_arg.name
        tag_name = f"$exn_{type_name}"
        thrown_wt = self._type_name_to_wasm(type_name)

        # Unique label ids for nested handlers
        hid = self._next_handle_id
        self._next_handle_id += 1
        done_label = f"$hd_{hid}"
        catch_label = f"$hc_{hid}"

        # Infer result type: try handler clause first (body may always
        # throw, making its inferred type None), then fall back to body.
        result_wt = None
        if expr.clauses:
            clause_body = expr.clauses[0].body
            if isinstance(clause_body, ast.Block):
                result_wt = self._infer_block_result_type(clause_body)
        if result_wt is None:
            result_wt = self._infer_block_result_type(expr.body)

        # Save/inject throw as an effect op for the body
        saved_ops = dict(self._effect_ops)
        self._effect_ops["throw"] = (tag_name, False)

        # Compile body
        body_instrs = self.translate_block(expr.body, env)

        # Restore effect_ops
        self._effect_ops = saved_ops

        if body_instrs is None:
            return None

        # Compile handler clause body
        if not expr.clauses:
            return None
        clause = expr.clauses[0]  # Exn<E> has exactly one op: throw

        # Allocate a local for the caught exception value
        thrown_local = self.alloc_local(thrown_wt)

        # Push caught value into slot env for handler body
        handler_env = env.push(type_name, thrown_local)
        handler_instrs = self.translate_expr(clause.body, handler_env)
        if handler_instrs is None:
            return None

        # Assemble the try_table structure
        result_spec = f" (result {result_wt})" if result_wt else ""
        thrown_spec = f" (result {thrown_wt})" if thrown_wt else ""

        instructions: list[str] = []
        instructions.append(f"block {done_label}{result_spec}")
        instructions.append(f"  block {catch_label}{thrown_spec}")
        instructions.append(
            f"    try_table{result_spec}"
            f" (catch {tag_name} {catch_label})"
        )
        instructions.extend(f"      {i}" for i in body_instrs)
        instructions.append("    end")
        instructions.append(f"    br {done_label}")
        instructions.append("  end")
        # Caught value is on the stack — store it in the local
        instructions.append(f"  local.set {thrown_local}")
        instructions.extend(f"  {i}" for i in handler_instrs)
        instructions.append("end")

        return instructions
