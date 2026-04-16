"""Array built-in translation mixin for WasmContext.

Handles: array_length, array_append, array_range, array_concat, array_slice.
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import (
    WasmSlotEnv,
    _element_mem_size,
    _element_store_op,
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
