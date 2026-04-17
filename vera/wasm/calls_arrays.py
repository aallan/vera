"""Array built-in translation mixin for WasmContext.

Handles: array_length, array_append, array_range, array_concat, array_slice,
array_map.
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import (
    WasmSlotEnv,
    _element_load_op,
    _element_mem_size,
    _element_store_op,
    _element_wasm_type,
    _is_pair_element_type,
    gc_shadow_push,
)


class CallsArraysMixin:
    """Methods for translating array built-in functions."""

    def _translate_array_length(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_length(array) → Int (i64).

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

    def _translate_array_append(
        self,
        arr_arg: ast.Expr,
        elem_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_append(array, element) → Array<T>.

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

    def _translate_array_range(
        self,
        start_arg: ast.Expr,
        end_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_range(start, end) → Array<Int>.

        Allocates an array of max(0, end - start) Int elements and fills
        it with consecutive integers [start, end).
        """
        start_instrs = self.translate_expr(start_arg, env)
        end_instrs = self.translate_expr(end_arg, env)
        if start_instrs is None or end_instrs is None:
            return None

        self.needs_alloc = True

        start_val = self.alloc_local("i64")
        end_val = self.alloc_local("i64")
        n_i64 = self.alloc_local("i64")
        n_i32 = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate start and end
        instructions.extend(start_instrs)
        instructions.append(f"local.set {start_val}")
        instructions.extend(end_instrs)
        instructions.append(f"local.set {end_val}")

        # n = max(0, end - start)
        instructions.append(f"local.get {end_val}")
        instructions.append(f"local.get {start_val}")
        instructions.append("i64.sub")
        instructions.append(f"local.set {n_i64}")
        instructions.append(f"local.get {n_i64}")
        instructions.append("i64.const 0")
        instructions.append("i64.lt_s")
        instructions.append(f"if")
        instructions.append("  i64.const 0")
        instructions.append(f"  local.set {n_i64}")
        instructions.append("end")
        instructions.append(f"local.get {n_i64}")
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {n_i32}")

        # Empty check: if n == 0 return (0, 0)
        instructions.append(f"local.get {n_i32}")
        instructions.append("i32.eqz")
        instructions.append("if (result i32 i32)")
        instructions.append("  i32.const 0")
        instructions.append("  i32.const 0")
        instructions.append("else")

        # Allocate n * 8 bytes (Int elements are i64 = 8 bytes each)
        instructions.append(f"  local.get {n_i32}")
        instructions.append("  i32.const 8")
        instructions.append("  i32.mul")
        instructions.append("  call $alloc")
        instructions.append(f"  local.set {dst}")
        instructions.extend(f"  {line}" for line in gc_shadow_push(dst))

        # Fill loop: dst[i*8] = start + i for i = 0..n-1
        instructions.append("  i32.const 0")
        instructions.append(f"  local.set {idx}")
        instructions.append("  block $brk_fill")
        instructions.append("    loop $lp_fill")
        instructions.append(f"      local.get {idx}")
        instructions.append(f"      local.get {n_i32}")
        instructions.append("      i32.ge_u")
        instructions.append("      br_if $brk_fill")
        # Store start + idx at dst + idx*8
        instructions.append(f"      local.get {dst}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 8")
        instructions.append("      i32.mul")
        instructions.append("      i32.add")
        instructions.append(f"      local.get {start_val}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i64.extend_i32_u")
        instructions.append("      i64.add")
        instructions.append("      i64.store offset=0")
        # idx++
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("      br $lp_fill")
        instructions.append("    end")
        instructions.append("  end")

        # Push result: (dst, n)
        instructions.append(f"  local.get {dst}")
        instructions.append(f"  local.get {n_i32}")
        instructions.append("end")
        return instructions

    def _translate_array_concat(
        self,
        arr_a_arg: ast.Expr,
        arr_b_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_concat(array_a, array_b) → Array<T>.

        Allocates a new array of size (len_a + len_b), copies both arrays'
        bytes contiguously, and returns (new_ptr, new_len).
        """
        arr_a_instrs = self.translate_expr(arr_a_arg, env)
        arr_b_instrs = self.translate_expr(arr_b_arg, env)
        if arr_a_instrs is None or arr_b_instrs is None:
            return None

        # Infer element type — try first arg, fall back to second
        elem_type = (
            self._infer_concat_elem_type(arr_a_arg)
            or self._infer_concat_elem_type(arr_b_arg)
        )
        if elem_type is None:
            # Both empty literals — no bytes to copy, use any size
            elem_size = 8
        else:
            size = _element_mem_size(elem_type)
            if size is None:
                return None
            elem_size = size

        self.needs_alloc = True

        ptr_a = self.alloc_local("i32")
        len_a = self.alloc_local("i32")
        ptr_b = self.alloc_local("i32")
        len_b = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        total_len = self.alloc_local("i32")
        bytes_a = self.alloc_local("i32")
        total_bytes = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate array A → (ptr, len)
        instructions.extend(arr_a_instrs)
        instructions.append(f"local.set {len_a}")
        instructions.append(f"local.set {ptr_a}")

        # Evaluate array B → (ptr, len)
        instructions.extend(arr_b_instrs)
        instructions.append(f"local.set {len_b}")
        instructions.append(f"local.set {ptr_b}")

        # total_len = len_a + len_b
        instructions.append(f"local.get {len_a}")
        instructions.append(f"local.get {len_b}")
        instructions.append("i32.add")
        instructions.append(f"local.set {total_len}")

        # Empty check: if total_len == 0 return (0, 0)
        instructions.append(f"local.get {total_len}")
        instructions.append("i32.eqz")
        instructions.append("if (result i32 i32)")
        instructions.append("  i32.const 0")
        instructions.append("  i32.const 0")
        instructions.append("else")

        # bytes_a = len_a * elem_size
        instructions.append(f"  local.get {len_a}")
        instructions.append(f"  i32.const {elem_size}")
        instructions.append("  i32.mul")
        instructions.append(f"  local.set {bytes_a}")

        # total_bytes = total_len * elem_size
        instructions.append(f"  local.get {total_len}")
        instructions.append(f"  i32.const {elem_size}")
        instructions.append("  i32.mul")
        instructions.append(f"  local.set {total_bytes}")

        # Allocate
        instructions.append(f"  local.get {total_bytes}")
        instructions.append("  call $alloc")
        instructions.append(f"  local.set {dst}")
        instructions.extend(f"  {line}" for line in gc_shadow_push(dst))

        # Copy array A bytes: byte-by-byte loop
        instructions.append("  i32.const 0")
        instructions.append(f"  local.set {idx}")
        instructions.append("  block $brk_a")
        instructions.append("    loop $lp_a")
        instructions.append(f"      local.get {idx}")
        instructions.append(f"      local.get {bytes_a}")
        instructions.append("      i32.ge_u")
        instructions.append("      br_if $brk_a")
        instructions.append(f"      local.get {dst}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append(f"      local.get {ptr_a}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append("      i32.load8_u offset=0")
        instructions.append("      i32.store8 offset=0")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("      br $lp_a")
        instructions.append("    end")
        instructions.append("  end")

        # Copy array B bytes at offset bytes_a
        instructions.append("  i32.const 0")
        instructions.append(f"  local.set {idx}")
        instructions.append("  block $brk_b")
        instructions.append("    loop $lp_b")
        instructions.append(f"      local.get {idx}")
        instructions.append(f"      local.get {total_bytes}")
        instructions.append(f"      local.get {bytes_a}")
        instructions.append("      i32.sub")  # bytes_b = total_bytes - bytes_a
        instructions.append("      i32.ge_u")
        instructions.append("      br_if $brk_b")
        instructions.append(f"      local.get {dst}")
        instructions.append(f"      local.get {bytes_a}")
        instructions.append("      i32.add")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append(f"      local.get {ptr_b}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append("      i32.load8_u offset=0")
        instructions.append("      i32.store8 offset=0")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("      br $lp_b")
        instructions.append("    end")
        instructions.append("  end")

        # Push result: (dst, total_len)
        instructions.append(f"  local.get {dst}")
        instructions.append(f"  local.get {total_len}")
        instructions.append("end")
        return instructions

    def _translate_array_slice(
        self,
        arr_arg: ast.Expr,
        start_arg: ast.Expr,
        end_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array_slice(array, start, end) → Array<T>.

        Returns a new array containing elements from index start (inclusive)
        to end (exclusive).  Clamps indices to [0, len] so out-of-range
        values produce shorter slices rather than traps.
        """
        arr_instrs = self.translate_expr(arr_arg, env)
        start_instrs = self.translate_expr(start_arg, env)
        end_instrs = self.translate_expr(end_arg, env)
        if arr_instrs is None or start_instrs is None or end_instrs is None:
            return None

        elem_type = self._infer_concat_elem_type(arr_arg)
        if elem_type is None:
            # Only safe for provably empty arrays; otherwise bail
            if isinstance(arr_arg, ast.ArrayLit) and not arr_arg.elements:
                elem_size = 8
            else:
                return None
        else:
            size = _element_mem_size(elem_type)
            if size is None:
                return None
            elem_size = size

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        arr_len = self.alloc_local("i32")
        s = self.alloc_local("i32")
        e = self.alloc_local("i32")
        slice_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        total_bytes = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        instructions: list[str] = []

        # Evaluate array → (ptr, len)
        instructions.extend(arr_instrs)
        instructions.append(f"local.set {arr_len}")
        instructions.append(f"local.set {ptr}")

        # Evaluate start → i64, wrap to i32
        instructions.extend(start_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {s}")

        # Evaluate end → i64, wrap to i32
        instructions.extend(end_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {e}")

        # Clamp start: s = max(0, min(s, arr_len))
        instructions.append(f"local.get {s}")
        instructions.append("i32.const 0")
        instructions.append("i32.lt_s")
        instructions.append("if (result i32)")
        instructions.append("  i32.const 0")
        instructions.append("else")
        instructions.append(f"  local.get {s}")
        instructions.append(f"  local.get {arr_len}")
        instructions.append("  i32.gt_s")
        instructions.append("  if (result i32)")
        instructions.append(f"    local.get {arr_len}")
        instructions.append("  else")
        instructions.append(f"    local.get {s}")
        instructions.append("  end")
        instructions.append("end")
        instructions.append(f"local.set {s}")

        # Clamp end: e = max(s, min(e, arr_len))
        instructions.append(f"local.get {e}")
        instructions.append(f"local.get {arr_len}")
        instructions.append("i32.gt_s")
        instructions.append("if (result i32)")
        instructions.append(f"  local.get {arr_len}")
        instructions.append("else")
        instructions.append(f"  local.get {e}")
        instructions.append("end")
        instructions.append(f"local.set {e}")
        # Ensure e >= s
        instructions.append(f"local.get {e}")
        instructions.append(f"local.get {s}")
        instructions.append("i32.lt_s")
        instructions.append("if")
        instructions.append(f"  local.get {s}")
        instructions.append(f"  local.set {e}")
        instructions.append("end")

        # slice_len = e - s
        instructions.append(f"local.get {e}")
        instructions.append(f"local.get {s}")
        instructions.append("i32.sub")
        instructions.append(f"local.set {slice_len}")

        # Empty check
        instructions.append(f"local.get {slice_len}")
        instructions.append("i32.eqz")
        instructions.append("if (result i32 i32)")
        instructions.append("  i32.const 0")
        instructions.append("  i32.const 0")
        instructions.append("else")

        # total_bytes = slice_len * elem_size
        instructions.append(f"  local.get {slice_len}")
        instructions.append(f"  i32.const {elem_size}")
        instructions.append("  i32.mul")
        instructions.append(f"  local.set {total_bytes}")

        # Allocate
        instructions.append(f"  local.get {total_bytes}")
        instructions.append("  call $alloc")
        instructions.append(f"  local.set {dst}")
        instructions.extend(f"  {line}" for line in gc_shadow_push(dst))

        # Copy bytes: dst[i] = src[s * elem_size + i] for i in [0, total_bytes)
        instructions.append("  i32.const 0")
        instructions.append(f"  local.set {idx}")
        instructions.append("  block $brk")
        instructions.append("    loop $lp")
        instructions.append(f"      local.get {idx}")
        instructions.append(f"      local.get {total_bytes}")
        instructions.append("      i32.ge_u")
        instructions.append("      br_if $brk")
        # dst[idx]
        instructions.append(f"      local.get {dst}")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        # src[s * elem_size + idx]
        instructions.append(f"      local.get {ptr}")
        instructions.append(f"      local.get {s}")
        instructions.append(f"      i32.const {elem_size}")
        instructions.append("      i32.mul")
        instructions.append("      i32.add")
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.add")
        instructions.append("      i32.load8_u offset=0")
        instructions.append("      i32.store8 offset=0")
        # idx++
        instructions.append(f"      local.get {idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {idx}")
        instructions.append("      br $lp")
        instructions.append("    end")
        instructions.append("  end")

        # Push result: (dst, slice_len)
        instructions.append(f"  local.get {dst}")
        instructions.append(f"  local.get {slice_len}")
        instructions.append("end")
        return instructions

    def _infer_closure_return_vera_type(
        self, closure_arg: ast.Expr,
    ) -> str | None:
        """Return the Vera element type name for a closure's return value.

        Needed so array_map knows the size / load / store ops for the
        output element type.  Handles the common case of an anonymous
        function literal (``fn(...) -> T { ... }``).  Returns ``None``
        when the return type can't be inferred from the AST alone.
        """
        if isinstance(closure_arg, ast.AnonFn):
            ret = closure_arg.return_type
            if isinstance(ret, ast.NamedType):
                return self._resolve_type_name_to_wasm_canonical(ret.name)
        return None

    def _translate_array_map(
        self,
        arr_arg: ast.Expr,
        fn_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate ``array_map<A, B>(arr, fn) -> Array<B>`` iteratively.

        The translator emits a single WAT ``loop`` that walks the source
        array once, invoking the closure via ``call_indirect`` at each
        element.  This gives O(1) shadow-stack depth regardless of
        input length — the old prelude implementation was recursive and
        ran out of stack space past ~4K elements.

        WAT shape::

            ;; evaluate arr → (ptr, len), save + GC-root arr_ptr
            ;; evaluate fn → i32 closure handle, save + GC-root fn_tmp
            ;; call $alloc(len * sizeof(B)), save as dst, GC-root dst
            ;; loop idx in [0, len):
            ;;   push fn (env); load arr[idx]; push fn.func_table_idx
            ;;   call_indirect (type $closure_sig_N)
            ;;   save result; compute dst_slot; store
            ;; push (dst, len)
        """
        arr_instrs = self.translate_expr(arr_arg, env)
        fn_instrs = self.translate_expr(fn_arg, env)
        if arr_instrs is None or fn_instrs is None:
            return None

        a_type = self._infer_concat_elem_type(arr_arg)
        if a_type is None:
            return None
        a_size = _element_mem_size(a_type)
        if a_size is None:
            return None
        a_is_pair = _is_pair_element_type(a_type)
        a_wasm = _element_wasm_type(a_type)
        if a_wasm is None:
            return None

        b_type = self._infer_closure_return_vera_type(fn_arg)
        if b_type is None:
            return None
        b_size = _element_mem_size(b_type)
        if b_size is None:
            return None
        b_is_pair = _is_pair_element_type(b_type)
        b_wasm = _element_wasm_type(b_type)
        if b_wasm is None:
            return None

        self.needs_alloc = True

        arr_ptr = self.alloc_local("i32")
        arr_len = self.alloc_local("i32")
        fn_tmp = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        src_slot = self.alloc_local("i32")
        dst_slot = self.alloc_local("i32")
        if b_is_pair:
            ret_ptr = self.alloc_local("i32")
            ret_len = self.alloc_local("i32")
        else:
            ret_scalar = self.alloc_local(b_wasm)

        instructions: list[str] = []

        # Evaluate arr → (ptr, len), save.  Shadow-push arr_ptr before
        # fn_instrs and the dst $alloc: both can trigger GC, so the
        # input array must stay rooted across them.
        instructions.extend(arr_instrs)
        instructions.append(f"local.set {arr_len}")
        instructions.append(f"local.set {arr_ptr}")
        instructions.extend(gc_shadow_push(arr_ptr))

        instructions.extend(fn_instrs)
        instructions.append(f"local.set {fn_tmp}")
        instructions.extend(gc_shadow_push(fn_tmp))

        instructions.append(f"local.get {arr_len}")
        instructions.append(f"i32.const {b_size}")
        instructions.append("i32.mul")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))

        # Register a closure signature: env (i32) + A-expanded params,
        # B-expanded result.
        a_param_types = ["i32", "i32"] if a_is_pair else [a_wasm]
        param_parts = " ".join(
            f"(param {wt})" for wt in ["i32"] + a_param_types
        )
        if b_is_pair:
            result_part = " (result i32 i32)"
        elif b_wasm:
            result_part = f" (result {b_wasm})"
        else:
            result_part = ""
        sig_key = f"{param_parts}{result_part}"
        if sig_key not in self._closure_sigs:
            sig_name = f"$closure_sig_{len(self._closure_sigs)}"
            self._closure_sigs[sig_key] = sig_name
        sig_name = self._closure_sigs[sig_key]

        # Loop.
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_map")
        instructions.append("  loop $lp_map")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {arr_len}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_map")

        # src_slot = arr_ptr + idx * sizeof(A).
        instructions.append(f"    local.get {arr_ptr}")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    i32.const {a_size}")
        instructions.append("    i32.mul")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {src_slot}")

        # Push env; load src[idx]; push fn_idx; call_indirect.
        instructions.append(f"    local.get {fn_tmp}")
        if a_is_pair:
            instructions.append(f"    local.get {src_slot}")
            instructions.append("    i32.load offset=0")
            instructions.append(f"    local.get {src_slot}")
            instructions.append("    i32.load offset=4")
        else:
            a_load = _element_load_op(a_type)
            if a_load is None:
                return None
            instructions.append(f"    local.get {src_slot}")
            instructions.append(f"    {a_load} offset=0")
        instructions.append(f"    local.get {fn_tmp}")
        instructions.append("    i32.load offset=0")
        instructions.append(f"    call_indirect (type {sig_name})")

        # Save result(s); compute dst_slot = dst + idx * sizeof(B); store.
        if b_is_pair:
            instructions.append(f"    local.set {ret_len}")
            instructions.append(f"    local.set {ret_ptr}")
        else:
            instructions.append(f"    local.set {ret_scalar}")
        instructions.append(f"    local.get {dst}")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    i32.const {b_size}")
        instructions.append("    i32.mul")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {dst_slot}")
        if b_is_pair:
            instructions.append(f"    local.get {dst_slot}")
            instructions.append(f"    local.get {ret_ptr}")
            instructions.append("    i32.store offset=0")
            instructions.append(f"    local.get {dst_slot}")
            instructions.append(f"    local.get {ret_len}")
            instructions.append("    i32.store offset=4")
        else:
            b_store = _element_store_op(b_type)
            if b_store is None:
                return None
            instructions.append(f"    local.get {dst_slot}")
            instructions.append(f"    local.get {ret_scalar}")
            instructions.append(f"    {b_store} offset=0")

        # idx++, loop.
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_map")
        instructions.append("  end")
        instructions.append("end")

        # Result: (dst, arr_len).
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {arr_len}")
        return instructions

    def _translate_array_filter(
        self,
        arr_arg: ast.Expr,
        fn_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate ``array_filter<T>(arr, pred) -> Array<T>`` iteratively.

        The output length is not known up-front, so we over-allocate
        ``len * sizeof(T)`` bytes (worst case — every element passes),
        walk the input once invoking the predicate, copy passing
        elements into ``dst[write_idx]``, and return ``(dst,
        write_idx)``.  The unused tail is unreachable via the
        returned pair and gets reclaimed by the sweeper.

        Single-pass deliberately: calling the predicate twice (once
        to count, once to copy) would double cost and, more
        importantly, assume purity at evaluation granularity.  A
        single pass is also closer to what a programmer would write
        by hand.

        WAT shape::

            ;; evaluate arr → (ptr, len), save + GC-root arr_ptr
            ;; evaluate fn → i32 handle, save + GC-root fn_tmp
            ;; call $alloc(len * sizeof(T)), save as dst, GC-root dst
            ;; write_idx = 0
            ;; loop idx in [0, len):
            ;;   push fn (env); load src[idx]; push fn_idx;
            ;;   call_indirect → i32 (Bool)
            ;;   if result != 0:
            ;;     compute dst_slot = dst + write_idx * sizeof(T)
            ;;     copy src[idx] to dst[write_idx] (1 or 2 loads+stores)
            ;;     write_idx++
            ;; push (dst, write_idx)
        """
        arr_instrs = self.translate_expr(arr_arg, env)
        fn_instrs = self.translate_expr(fn_arg, env)
        if arr_instrs is None or fn_instrs is None:
            return None

        t_type = self._infer_concat_elem_type(arr_arg)
        if t_type is None:
            return None
        t_size = _element_mem_size(t_type)
        if t_size is None:
            return None
        t_is_pair = _is_pair_element_type(t_type)
        t_wasm = _element_wasm_type(t_type)
        if t_wasm is None:
            return None

        self.needs_alloc = True

        arr_ptr = self.alloc_local("i32")
        arr_len = self.alloc_local("i32")
        fn_tmp = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        write_idx = self.alloc_local("i32")
        src_slot = self.alloc_local("i32")
        dst_slot = self.alloc_local("i32")
        # Temp for the loaded source element (so we can reload it into
        # both the call_indirect arg and the dst store without a
        # second memory read).
        if t_is_pair:
            src_ptr = self.alloc_local("i32")
            src_len = self.alloc_local("i32")
        else:
            src_val = self.alloc_local(t_wasm)

        instructions: list[str] = []

        # Evaluate arr → (ptr, len), save, shadow-push.
        instructions.extend(arr_instrs)
        instructions.append(f"local.set {arr_len}")
        instructions.append(f"local.set {arr_ptr}")
        instructions.extend(gc_shadow_push(arr_ptr))

        # Evaluate fn → closure handle, save, shadow-push.
        instructions.extend(fn_instrs)
        instructions.append(f"local.set {fn_tmp}")
        instructions.extend(gc_shadow_push(fn_tmp))

        # Worst-case allocation: every element passes the predicate.
        instructions.append(f"local.get {arr_len}")
        instructions.append(f"i32.const {t_size}")
        instructions.append("i32.mul")
        instructions.append("call $alloc")
        instructions.append(f"local.set {dst}")
        instructions.extend(gc_shadow_push(dst))

        # Predicate closure sig: (env:i32, T-expanded) -> Bool (i32).
        t_param_types = ["i32", "i32"] if t_is_pair else [t_wasm]
        param_parts = " ".join(
            f"(param {wt})" for wt in ["i32"] + t_param_types
        )
        sig_key = f"{param_parts} (result i32)"
        if sig_key not in self._closure_sigs:
            sig_name = f"$closure_sig_{len(self._closure_sigs)}"
            self._closure_sigs[sig_key] = sig_name
        sig_name = self._closure_sigs[sig_key]

        # write_idx = 0; loop idx in [0, arr_len).
        instructions.append("i32.const 0")
        instructions.append(f"local.set {write_idx}")
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_flt")
        instructions.append("  loop $lp_flt")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {arr_len}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_flt")

        # src_slot = arr_ptr + idx * sizeof(T).
        instructions.append(f"    local.get {arr_ptr}")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    i32.const {t_size}")
        instructions.append("    i32.mul")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {src_slot}")

        # Load src[idx] into temp local(s) — reused for the predicate
        # call below AND the conditional store further down.
        if t_is_pair:
            instructions.append(f"    local.get {src_slot}")
            instructions.append("    i32.load offset=0")
            instructions.append(f"    local.set {src_ptr}")
            instructions.append(f"    local.get {src_slot}")
            instructions.append("    i32.load offset=4")
            instructions.append(f"    local.set {src_len}")
        else:
            t_load = _element_load_op(t_type)
            if t_load is None:
                return None
            instructions.append(f"    local.get {src_slot}")
            instructions.append(f"    {t_load} offset=0")
            instructions.append(f"    local.set {src_val}")

        # Invoke predicate: push env, push element, push fn_idx,
        # call_indirect → i32 (Bool).
        instructions.append(f"    local.get {fn_tmp}")
        if t_is_pair:
            instructions.append(f"    local.get {src_ptr}")
            instructions.append(f"    local.get {src_len}")
        else:
            instructions.append(f"    local.get {src_val}")
        instructions.append(f"    local.get {fn_tmp}")
        instructions.append("    i32.load offset=0")
        instructions.append(f"    call_indirect (type {sig_name})")

        # if predicate returned true: copy element, bump write_idx.
        instructions.append("    if")
        # dst_slot = dst + write_idx * sizeof(T).
        instructions.append(f"      local.get {dst}")
        instructions.append(f"      local.get {write_idx}")
        instructions.append(f"      i32.const {t_size}")
        instructions.append("      i32.mul")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {dst_slot}")
        if t_is_pair:
            instructions.append(f"      local.get {dst_slot}")
            instructions.append(f"      local.get {src_ptr}")
            instructions.append("      i32.store offset=0")
            instructions.append(f"      local.get {dst_slot}")
            instructions.append(f"      local.get {src_len}")
            instructions.append("      i32.store offset=4")
        else:
            t_store = _element_store_op(t_type)
            if t_store is None:
                return None
            instructions.append(f"      local.get {dst_slot}")
            instructions.append(f"      local.get {src_val}")
            instructions.append(f"      {t_store} offset=0")
        # write_idx++.
        instructions.append(f"      local.get {write_idx}")
        instructions.append("      i32.const 1")
        instructions.append("      i32.add")
        instructions.append(f"      local.set {write_idx}")
        instructions.append("    end")

        # idx++, loop.
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_flt")
        instructions.append("  end")
        instructions.append("end")

        # Result: (dst, write_idx).  Tail past write_idx is unused
        # but still inside the allocated block; sweeper reclaims it
        # when dst itself becomes unreachable.
        instructions.append(f"local.get {dst}")
        instructions.append(f"local.get {write_idx}")
        return instructions

    def _infer_fold_init_vera_type(
        self, init_arg: ast.Expr, fn_arg: ast.Expr,
    ) -> str | None:
        """Infer the Vera type name for a fold's accumulator (U).

        Strategy: first try the closure's return type (same helper
        the other combinators use); fall back to inspecting the init
        argument directly for common shapes (SlotRef, primitive
        literals, to_string-style calls).
        """
        # Primary: closure return type — most reliable for AnonFn
        # literals.
        ret = self._infer_closure_return_vera_type(fn_arg)
        if ret is not None:
            return ret
        # Fallback: inspect the init expression.
        if isinstance(init_arg, ast.SlotRef):
            return init_arg.type_name
        if isinstance(init_arg, ast.StringLit):
            return "String"
        if isinstance(init_arg, ast.IntLit):
            return "Int"
        if isinstance(init_arg, ast.BoolLit):
            return "Bool"
        return None

    def _translate_array_fold(
        self,
        arr_arg: ast.Expr,
        init_arg: ast.Expr,
        fn_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate ``array_fold<T, U>(arr, init, fn) -> U`` iteratively.

        Structurally different from map/filter: the result is a
        scalar ``U``, not an ``Array<U>``, so there's no output
        allocation and no write-index bookkeeping — just a running
        accumulator updated in-place each iteration.

        Closure signature: ``(env, U, T) -> U``.  Each iteration
        pushes env + current acc + loaded element, call_indirects,
        and stores the result back into the accumulator local(s).

        GC rooting: for scalar ``U`` (Int/Nat/Float64/Bool/Byte),
        the accumulator lives in a plain WASM local — not scanned
        by the conservative GC, but also not a heap reference so
        it doesn't need to be.  For pair-typed ``U`` (String,
        ``Array<T>``) and ADT ``U`` (i32 heap handles), the
        accumulator's pointer part IS a live heap reference and
        must survive closure-invocation GC cycles.  We shadow-push
        the pointer once before the loop and OVERWRITE that slot
        in place each iteration with the new pointer returned by
        the closure.  This keeps ``gc_sp`` stable across iterations
        (no per-iteration push/pop) and keeps exactly one root for
        the accumulator on the shadow stack.

        WAT shape::

            ;; eval arr → (ptr, len), save + shadow-push arr_ptr
            ;; eval init → acc (1 or 2 vals), save to acc local(s)
            ;;   if U is pair/ADT: shadow-push acc_ptr
            ;; eval fn → handle, save + shadow-push fn_tmp
            ;; loop idx in [0, len):
            ;;   push env; push acc; load src[idx]; push fn_idx;
            ;;   call_indirect (env:i32, U-expanded, T-expanded) -> U
            ;;   local.set acc from result
            ;;   if U is pair/ADT: overwrite shadow slot with new acc_ptr
            ;; push acc (1 or 2 vals)
        """
        arr_instrs = self.translate_expr(arr_arg, env)
        init_instrs = self.translate_expr(init_arg, env)
        fn_instrs = self.translate_expr(fn_arg, env)
        if arr_instrs is None or init_instrs is None or fn_instrs is None:
            return None

        t_type = self._infer_concat_elem_type(arr_arg)
        if t_type is None:
            return None
        t_size = _element_mem_size(t_type)
        if t_size is None:
            return None
        t_is_pair = _is_pair_element_type(t_type)
        t_wasm = _element_wasm_type(t_type)
        if t_wasm is None:
            return None

        u_type = self._infer_fold_init_vera_type(init_arg, fn_arg)
        if u_type is None:
            return None
        u_is_pair = _is_pair_element_type(u_type)
        u_wasm = _element_wasm_type(u_type)
        if u_wasm is None:
            return None

        # Pair-U and ADT-U (4-byte i32 handle) are both "heap ptr"
        # from the GC's perspective — rooting required.  The
        # ``_element_wasm_type`` helper returns ``"i32_pair"`` for
        # pair types and ``"i32"`` for ADT handles.  Primitives
        # (i64/f64/i32 for Bool-Byte) don't need rooting.
        u_is_adt = (
            u_wasm == "i32"
            and u_type not in ("Bool", "Byte")
            and not u_is_pair
        )
        u_needs_root = u_is_pair or u_is_adt

        arr_ptr = self.alloc_local("i32")
        arr_len = self.alloc_local("i32")
        fn_tmp = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        src_slot = self.alloc_local("i32")
        if u_is_pair:
            acc_ptr = self.alloc_local("i32")
            acc_len = self.alloc_local("i32")
        else:
            acc = self.alloc_local(u_wasm)

        instructions: list[str] = []

        # 1. Evaluate arr → (ptr, len), save, shadow-push arr_ptr.
        instructions.extend(arr_instrs)
        instructions.append(f"local.set {arr_len}")
        instructions.append(f"local.set {arr_ptr}")
        instructions.extend(gc_shadow_push(arr_ptr))

        # 2. Evaluate init → U, save.  For pair U, stack order is
        # (ptr, len) from most recent push; pop len then ptr.
        instructions.extend(init_instrs)
        if u_is_pair:
            instructions.append(f"local.set {acc_len}")
            instructions.append(f"local.set {acc_ptr}")
            instructions.extend(gc_shadow_push(acc_ptr))
        else:
            instructions.append(f"local.set {acc}")
            if u_needs_root:
                instructions.extend(gc_shadow_push(acc))

        # 3. Evaluate fn → handle, save, shadow-push.
        instructions.extend(fn_instrs)
        instructions.append(f"local.set {fn_tmp}")
        instructions.extend(gc_shadow_push(fn_tmp))

        # 4. Register the closure signature.
        u_param_types = ["i32", "i32"] if u_is_pair else [u_wasm]
        t_param_types = ["i32", "i32"] if t_is_pair else [t_wasm]
        param_parts = " ".join(
            f"(param {wt})" for wt in ["i32"] + u_param_types + t_param_types
        )
        if u_is_pair:
            result_part = " (result i32 i32)"
        else:
            result_part = f" (result {u_wasm})"
        sig_key = f"{param_parts}{result_part}"
        if sig_key not in self._closure_sigs:
            sig_name = f"$closure_sig_{len(self._closure_sigs)}"
            self._closure_sigs[sig_key] = sig_name
        sig_name = self._closure_sigs[sig_key]

        # 5. Loop.
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")
        instructions.append("block $brk_fold")
        instructions.append("  loop $lp_fold")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {arr_len}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $brk_fold")

        # src_slot = arr_ptr + idx * sizeof(T).
        instructions.append(f"    local.get {arr_ptr}")
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    i32.const {t_size}")
        instructions.append("    i32.mul")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {src_slot}")

        # Push env, current acc, loaded element, fn_idx.
        instructions.append(f"    local.get {fn_tmp}")
        if u_is_pair:
            instructions.append(f"    local.get {acc_ptr}")
            instructions.append(f"    local.get {acc_len}")
        else:
            instructions.append(f"    local.get {acc}")
        if t_is_pair:
            instructions.append(f"    local.get {src_slot}")
            instructions.append("    i32.load offset=0")
            instructions.append(f"    local.get {src_slot}")
            instructions.append("    i32.load offset=4")
        else:
            t_load = _element_load_op(t_type)
            if t_load is None:
                return None
            instructions.append(f"    local.get {src_slot}")
            instructions.append(f"    {t_load} offset=0")
        instructions.append(f"    local.get {fn_tmp}")
        instructions.append("    i32.load offset=0")
        instructions.append(f"    call_indirect (type {sig_name})")

        # Save new acc from result.  Pair: result stack is (ptr, len);
        # pop len first then ptr.
        if u_is_pair:
            instructions.append(f"    local.set {acc_len}")
            instructions.append(f"    local.set {acc_ptr}")
            # Overwrite shadow-stack root with the new acc_ptr.
            # The slot was pushed second-to-last (after arr_ptr and
            # before fn_tmp), so its address is gc_sp - 8.
            instructions.append("    global.get $gc_sp")
            instructions.append("    i32.const 8")
            instructions.append("    i32.sub")
            instructions.append(f"    local.get {acc_ptr}")
            instructions.append("    i32.store")
        else:
            instructions.append(f"    local.set {acc}")
            if u_needs_root:
                # ADT handle acc: slot is at gc_sp - 8 (same layout).
                instructions.append("    global.get $gc_sp")
                instructions.append("    i32.const 8")
                instructions.append("    i32.sub")
                instructions.append(f"    local.get {acc}")
                instructions.append("    i32.store")

        # idx++, loop.
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $lp_fold")
        instructions.append("  end")
        instructions.append("end")

        # Result: push acc.
        if u_is_pair:
            instructions.append(f"local.get {acc_ptr}")
            instructions.append(f"local.get {acc_len}")
        else:
            instructions.append(f"local.get {acc}")
        return instructions
