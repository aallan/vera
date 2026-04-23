"""String built-in translation mixin for WasmContext.

Handles: string_length, string_concat, string_slice, string_char_code,
string_from_char_code, string_repeat, string_contains, string_starts_with,
string_ends_with, string_strip, string_upper, string_lower, string_index_of,
string_replace, string_split, string_join, plus to-string conversions
(to_string, bool_to_string, byte_to_string, float_to_string).

Also handles #470 utilities (string_chars, string_lines, string_words,
string_pad_start, string_pad_end, string_reverse, string_trim_start,
string_trim_end) and #471 character classification + case conversion
(is_digit, is_alpha, is_alphanumeric, is_whitespace, is_upper, is_lower,
char_to_upper, char_to_lower).
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv, gc_shadow_push


class CallsStringsMixin:
    """Methods for translating string built-in functions."""

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

    def _translate_from_char_code(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate from_char_code(n) → String (i32_pair).

        Allocates a 1-byte string and stores the byte value.
        Inverse of char_code.
        """
        n_instrs = self.translate_expr(arg, env)
        if n_instrs is None:
            return None

        self.needs_alloc = True

        byte_val = self.alloc_local("i32")
        ptr = self.alloc_local("i32")

        ins: list[str] = []

        # Evaluate arg (Nat = i64) → i32
        ins.extend(n_instrs)
        ins.append("i32.wrap_i64")
        ins.append(f"local.set {byte_val}")

        # Allocate 1-byte buffer
        ins.append("i32.const 1")
        ins.append("call $alloc")
        ins.append(f"local.set {ptr}")
        ins.extend(gc_shadow_push(ptr))

        # Store the byte
        ins.append(f"local.get {ptr}")
        ins.append(f"local.get {byte_val}")
        ins.append("i32.store8 offset=0")

        # Result: (ptr, 1)
        ins.append(f"local.get {ptr}")
        ins.append("i32.const 1")
        return ins

    def _translate_string_repeat(
        self,
        arg_s: ast.Expr,
        arg_n: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate string_repeat(s, n) → String (i32_pair).

        Allocates len(s)*n bytes and copies the source string n times.
        """
        s_instrs = self.translate_expr(arg_s, env)
        n_instrs = self.translate_expr(arg_n, env)
        if s_instrs is None or n_instrs is None:
            return None

        self.needs_alloc = True

        ptr_s = self.alloc_local("i32")
        len_s = self.alloc_local("i32")
        count = self.alloc_local("i32")
        total_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        out_idx = self.alloc_local("i32")

        ins: list[str] = []

        # Evaluate string → (ptr, len)
        ins.extend(s_instrs)
        ins.append(f"local.set {len_s}")
        ins.append(f"local.set {ptr_s}")

        # Evaluate count (Nat = i64 → i32)
        ins.extend(n_instrs)
        ins.append("i32.wrap_i64")
        ins.append(f"local.set {count}")

        # total_len = len_s * count
        ins.append(f"local.get {len_s}")
        ins.append(f"local.get {count}")
        ins.append("i32.mul")
        ins.append(f"local.set {total_len}")

        # Allocate output buffer
        ins.append(f"local.get {total_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # Copy loop: out_idx = 0..total_len-1
        ins.append("i32.const 0")
        ins.append(f"local.set {out_idx}")
        ins.append("block $brk_sr")
        ins.append("  loop $lp_sr")
        ins.append(f"    local.get {out_idx}")
        ins.append(f"    local.get {total_len}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_sr")
        # dst[out_idx] = src[out_idx % len_s]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {out_idx}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ptr_s}")
        ins.append(f"    local.get {out_idx}")
        ins.append(f"    local.get {len_s}")
        ins.append("    i32.rem_u")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")
        ins.append(f"    local.get {out_idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {out_idx}")
        ins.append("    br $lp_sr")
        ins.append("  end")
        ins.append("end")

        # Result: (dst, total_len)
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {total_len}")
        return ins

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
    # String search builtins
    # -----------------------------------------------------------------

    def _translate_starts_with(
        self,
        arg_h: ast.Expr,
        arg_n: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate starts_with(haystack, needle) → Bool (i32).

        Returns 1 if haystack starts with needle, 0 otherwise.
        Compares prefix bytes; empty needle always matches.
        """
        h_instrs = self.translate_expr(arg_h, env)
        n_instrs = self.translate_expr(arg_n, env)
        if h_instrs is None or n_instrs is None:
            return None

        ptr_h = self.alloc_local("i32")
        len_h = self.alloc_local("i32")
        ptr_n = self.alloc_local("i32")
        len_n = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        ins: list[str] = []

        # Evaluate haystack → (ptr, len)
        ins.extend(h_instrs)
        ins.append(f"local.set {len_h}")
        ins.append(f"local.set {ptr_h}")

        # Evaluate needle → (ptr, len)
        ins.extend(n_instrs)
        ins.append(f"local.set {len_n}")
        ins.append(f"local.set {ptr_n}")

        # block $done_sw produces i32 result
        ins.append("block $done_sw (result i32)")

        # If needle longer than haystack → false
        ins.append(f"  local.get {len_n}")
        ins.append(f"  local.get {len_h}")
        ins.append("  i32.gt_u")
        ins.append("  if")
        ins.append("    i32.const 0")
        ins.append("    br $done_sw")
        ins.append("  end")

        # Compare loop
        ins.append("  i32.const 0")
        ins.append(f"  local.set {idx}")
        ins.append("  block $brk_sw")
        ins.append("    loop $lp_sw")
        ins.append(f"      local.get {idx}")
        ins.append(f"      local.get {len_n}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_sw")
        # Compare bytes
        ins.append(f"      local.get {ptr_h}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append(f"      local.get {ptr_n}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append("      i32.ne")
        ins.append("      if")
        ins.append("        i32.const 0")
        ins.append("        br $done_sw")
        ins.append("      end")
        # idx++
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("      br $lp_sw")
        ins.append("    end")
        ins.append("  end")

        # All bytes matched
        ins.append("  i32.const 1")
        ins.append("end")  # $done_sw

        return ins

    def _translate_ends_with(
        self,
        arg_h: ast.Expr,
        arg_n: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate ends_with(haystack, needle) → Bool (i32).

        Returns 1 if haystack ends with needle, 0 otherwise.
        Compares suffix bytes at offset (len_h - len_n).
        """
        h_instrs = self.translate_expr(arg_h, env)
        n_instrs = self.translate_expr(arg_n, env)
        if h_instrs is None or n_instrs is None:
            return None

        ptr_h = self.alloc_local("i32")
        len_h = self.alloc_local("i32")
        ptr_n = self.alloc_local("i32")
        len_n = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        offset = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(h_instrs)
        ins.append(f"local.set {len_h}")
        ins.append(f"local.set {ptr_h}")

        ins.extend(n_instrs)
        ins.append(f"local.set {len_n}")
        ins.append(f"local.set {ptr_n}")

        ins.append("block $done_ew (result i32)")

        # If needle longer than haystack → false
        ins.append(f"  local.get {len_n}")
        ins.append(f"  local.get {len_h}")
        ins.append("  i32.gt_u")
        ins.append("  if")
        ins.append("    i32.const 0")
        ins.append("    br $done_ew")
        ins.append("  end")

        # offset = len_h - len_n
        ins.append(f"  local.get {len_h}")
        ins.append(f"  local.get {len_n}")
        ins.append("  i32.sub")
        ins.append(f"  local.set {offset}")

        # Compare loop
        ins.append("  i32.const 0")
        ins.append(f"  local.set {idx}")
        ins.append("  block $brk_ew")
        ins.append("    loop $lp_ew")
        ins.append(f"      local.get {idx}")
        ins.append(f"      local.get {len_n}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_ew")
        # Compare haystack[offset + idx] vs needle[idx]
        ins.append(f"      local.get {ptr_h}")
        ins.append(f"      local.get {offset}")
        ins.append("      i32.add")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append(f"      local.get {ptr_n}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append("      i32.ne")
        ins.append("      if")
        ins.append("        i32.const 0")
        ins.append("        br $done_ew")
        ins.append("      end")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("      br $lp_ew")
        ins.append("    end")
        ins.append("  end")

        ins.append("  i32.const 1")
        ins.append("end")

        return ins

    def _translate_string_contains(
        self,
        arg_h: ast.Expr,
        arg_n: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate string_contains(haystack, needle) → Bool (i32).

        Naive O(n*m) substring search.  Returns 1 if needle is found
        anywhere in haystack, 0 otherwise.  Empty needle always matches.
        """
        h_instrs = self.translate_expr(arg_h, env)
        n_instrs = self.translate_expr(arg_n, env)
        if h_instrs is None or n_instrs is None:
            return None

        ptr_h = self.alloc_local("i32")
        len_h = self.alloc_local("i32")
        ptr_n = self.alloc_local("i32")
        len_n = self.alloc_local("i32")
        i = self.alloc_local("i32")
        j = self.alloc_local("i32")
        limit = self.alloc_local("i32")
        matched = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(h_instrs)
        ins.append(f"local.set {len_h}")
        ins.append(f"local.set {ptr_h}")

        ins.extend(n_instrs)
        ins.append(f"local.set {len_n}")
        ins.append(f"local.set {ptr_n}")

        ins.append("block $done_sc (result i32)")

        # Empty needle → true
        ins.append(f"  local.get {len_n}")
        ins.append("  i32.eqz")
        ins.append("  if")
        ins.append("    i32.const 1")
        ins.append("    br $done_sc")
        ins.append("  end")

        # Needle longer than haystack → false
        ins.append(f"  local.get {len_n}")
        ins.append(f"  local.get {len_h}")
        ins.append("  i32.gt_u")
        ins.append("  if")
        ins.append("    i32.const 0")
        ins.append("    br $done_sc")
        ins.append("  end")

        # limit = len_h - len_n + 1
        ins.append(f"  local.get {len_h}")
        ins.append(f"  local.get {len_n}")
        ins.append("  i32.sub")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {limit}")

        # Outer loop: try each starting position
        ins.append("  i32.const 0")
        ins.append(f"  local.set {i}")
        ins.append("  block $brk_sco")
        ins.append("    loop $lp_sco")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {limit}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_sco")

        # Inner loop: compare needle bytes
        ins.append("      i32.const 0")
        ins.append(f"      local.set {j}")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {matched}")
        ins.append("      block $brk_sci")
        ins.append("        loop $lp_sci")
        ins.append(f"          local.get {j}")
        ins.append(f"          local.get {len_n}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_sci")
        # Compare haystack[i+j] vs needle[j]
        ins.append(f"          local.get {ptr_h}")
        ins.append(f"          local.get {i}")
        ins.append("          i32.add")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append(f"          local.get {ptr_n}")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.ne")
        ins.append("          if")
        ins.append("            i32.const 0")
        ins.append(f"            local.set {matched}")
        ins.append("            br $brk_sci")
        ins.append("          end")
        ins.append(f"          local.get {j}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {j}")
        ins.append("          br $lp_sci")
        ins.append("        end")
        ins.append("      end")

        # If matched, return true
        ins.append(f"      local.get {matched}")
        ins.append("      if")
        ins.append("        i32.const 1")
        ins.append("        br $done_sc")
        ins.append("      end")

        # i++
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("      br $lp_sco")
        ins.append("    end")
        ins.append("  end")

        # No match found
        ins.append("  i32.const 0")
        ins.append("end")

        return ins

    # -----------------------------------------------------------------
    # String transformation builtins
    # -----------------------------------------------------------------

    def _translate_to_upper(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate to_upper(s) → String (i32_pair).

        Allocates a new buffer of the same size and converts ASCII
        lowercase letters (97–122) to uppercase by subtracting 32.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        byte = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Allocate same-size buffer
        ins.append(f"local.get {slen}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # Transform loop
        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("block $brk_tu")
        ins.append("  loop $lp_tu")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_tu")
        # Load byte
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {byte}")
        # Check: 97 <= byte <= 122 (lowercase ASCII)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 97")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 122")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    if")
        # Store byte - 32
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 32")
        ins.append("      i32.sub")
        ins.append("      i32.store8 offset=0")
        ins.append("    else")
        # Store byte as-is
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.store8 offset=0")
        ins.append("    end")
        # idx++
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_tu")
        ins.append("  end")
        ins.append("end")

        # Result: (dst, slen)
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {slen}")
        return ins

    def _translate_to_lower(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate to_lower(s) → String (i32_pair).

        Allocates a new buffer of the same size and converts ASCII
        uppercase letters (65–90) to lowercase by adding 32.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        byte = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        ins.append(f"local.get {slen}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("block $brk_tl")
        ins.append("  loop $lp_tl")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_tl")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {byte}")
        # Check: 65 <= byte <= 90 (uppercase ASCII)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 65")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 90")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    if")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 32")
        ins.append("      i32.add")
        ins.append("      i32.store8 offset=0")
        ins.append("    else")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.store8 offset=0")
        ins.append("    end")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_tl")
        ins.append("  end")
        ins.append("end")

        ins.append(f"local.get {dst}")
        ins.append(f"local.get {slen}")
        return ins

    def _translate_index_of(
        self,
        arg_h: ast.Expr,
        arg_n: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate index_of(haystack, needle) → Option<Nat> (i32 ptr).

        Returns a heap-allocated Option<Nat>:
          Some(Nat): [tag=1 : i32] [pad 4] [value : i64]  (16 bytes)
          None:      [tag=0 : i32] [pad 12]                (16 bytes)
        """
        h_instrs = self.translate_expr(arg_h, env)
        n_instrs = self.translate_expr(arg_n, env)
        if h_instrs is None or n_instrs is None:
            return None

        self.needs_alloc = True

        ptr_h = self.alloc_local("i32")
        len_h = self.alloc_local("i32")
        ptr_n = self.alloc_local("i32")
        len_n = self.alloc_local("i32")
        i = self.alloc_local("i32")
        j = self.alloc_local("i32")
        limit = self.alloc_local("i32")
        matched = self.alloc_local("i32")
        out = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(h_instrs)
        ins.append(f"local.set {len_h}")
        ins.append(f"local.set {ptr_h}")

        ins.extend(n_instrs)
        ins.append(f"local.set {len_n}")
        ins.append(f"local.set {ptr_n}")

        # Allocate Option<Nat> (16 bytes)
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.set {out}")

        ins.append("block $done_io")

        # Empty needle → Some(0)
        ins.append(f"  local.get {len_n}")
        ins.append("  i32.eqz")
        ins.append("  if")
        ins.append(f"    local.get {out}")
        ins.append("    i32.const 1")
        ins.append("    i32.store")              # tag = 1 (Some)
        ins.extend(f"    {x}" for x in gc_shadow_push(out))
        ins.append(f"    local.get {out}")
        ins.append("    i64.const 0")
        ins.append("    i64.store offset=8")     # value = 0
        ins.append("    br $done_io")
        ins.append("  end")

        # Needle longer than haystack → None
        ins.append(f"  local.get {len_n}")
        ins.append(f"  local.get {len_h}")
        ins.append("  i32.gt_u")
        ins.append("  if")
        ins.append(f"    local.get {out}")
        ins.append("    i32.const 0")
        ins.append("    i32.store")              # tag = 0 (None)
        ins.extend(f"    {x}" for x in gc_shadow_push(out))
        ins.append("    br $done_io")
        ins.append("  end")

        # limit = len_h - len_n + 1
        ins.append(f"  local.get {len_h}")
        ins.append(f"  local.get {len_n}")
        ins.append("  i32.sub")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {limit}")

        # Outer loop
        ins.append("  i32.const 0")
        ins.append(f"  local.set {i}")
        ins.append("  block $brk_ioo")
        ins.append("    loop $lp_ioo")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {limit}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_ioo")

        # Inner loop
        ins.append("      i32.const 0")
        ins.append(f"      local.set {j}")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {matched}")
        ins.append("      block $brk_ioi")
        ins.append("        loop $lp_ioi")
        ins.append(f"          local.get {j}")
        ins.append(f"          local.get {len_n}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_ioi")
        ins.append(f"          local.get {ptr_h}")
        ins.append(f"          local.get {i}")
        ins.append("          i32.add")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append(f"          local.get {ptr_n}")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.ne")
        ins.append("          if")
        ins.append("            i32.const 0")
        ins.append(f"            local.set {matched}")
        ins.append("            br $brk_ioi")
        ins.append("          end")
        ins.append(f"          local.get {j}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {j}")
        ins.append("          br $lp_ioi")
        ins.append("        end")
        ins.append("      end")

        # If matched → Some(i)
        ins.append(f"      local.get {matched}")
        ins.append("      if")
        ins.append(f"        local.get {out}")
        ins.append("        i32.const 1")
        ins.append("        i32.store")          # tag = 1 (Some)
        ins.extend(f"        {x}" for x in gc_shadow_push(out))
        ins.append(f"        local.get {out}")
        ins.append(f"        local.get {i}")
        ins.append("        i64.extend_i32_u")
        ins.append("        i64.store offset=8") # value = i
        ins.append("        br $done_io")
        ins.append("      end")

        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("      br $lp_ioo")
        ins.append("    end")
        ins.append("  end")

        # No match → None
        ins.append(f"  local.get {out}")
        ins.append("  i32.const 0")
        ins.append("  i32.store")                # tag = 0 (None)
        ins.extend(f"  {x}" for x in gc_shadow_push(out))

        ins.append("end")  # $done_io

        ins.append(f"local.get {out}")
        return ins

    def _translate_replace(
        self,
        arg_h: ast.Expr,
        arg_n: ast.Expr,
        arg_r: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate replace(haystack, needle, replacement) → String.

        Two-pass algorithm:
        1. Count non-overlapping occurrences of needle.
        2. Allocate result buffer and copy with replacements.
        Empty needle returns a copy of the haystack unchanged.
        """
        h_instrs = self.translate_expr(arg_h, env)
        n_instrs = self.translate_expr(arg_n, env)
        r_instrs = self.translate_expr(arg_r, env)
        if h_instrs is None or n_instrs is None or r_instrs is None:
            return None

        self.needs_alloc = True

        ptr_h = self.alloc_local("i32")
        len_h = self.alloc_local("i32")
        ptr_n = self.alloc_local("i32")
        len_n = self.alloc_local("i32")
        ptr_r = self.alloc_local("i32")
        len_r = self.alloc_local("i32")
        count = self.alloc_local("i32")
        i = self.alloc_local("i32")
        j = self.alloc_local("i32")
        matched = self.alloc_local("i32")
        new_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        out_idx = self.alloc_local("i32")
        copy_idx = self.alloc_local("i32")

        ins: list[str] = []

        # Evaluate all three strings
        ins.extend(h_instrs)
        ins.append(f"local.set {len_h}")
        ins.append(f"local.set {ptr_h}")
        ins.extend(n_instrs)
        ins.append(f"local.set {len_n}")
        ins.append(f"local.set {ptr_n}")
        ins.extend(r_instrs)
        ins.append(f"local.set {len_r}")
        ins.append(f"local.set {ptr_r}")

        # Wrap main computation in a block so the empty-needle edge case
        # can skip it with br instead of return (return would exit the
        # enclosing function, breaking subexpressions like length(replace(...))).
        ins.append("block $rp_main")

        # Edge case: empty needle → copy haystack
        ins.append(f"local.get {len_n}")
        ins.append("i32.eqz")
        ins.append("if")
        # Allocate and copy haystack as-is
        ins.append(f"  local.get {len_h}")
        ins.append("  call $alloc")
        ins.append(f"  local.set {dst}")
        ins.extend(f"  {x}" for x in gc_shadow_push(dst))
        ins.append("  i32.const 0")
        ins.append(f"  local.set {i}")
        ins.append("  block $brk_rce")
        ins.append("    loop $lp_rce")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_h}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_rce")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append(f"      local.get {ptr_h}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("      br $lp_rce")
        ins.append("    end")
        ins.append("  end")
        ins.append(f"  local.get {len_h}")
        ins.append(f"  local.set {new_len}")
        ins.append("  br $rp_main")
        ins.append("end")

        # ---- Pass 1: count occurrences ----
        ins.append("i32.const 0")
        ins.append(f"local.set {count}")
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")

        ins.append("block $brk_rp1")
        ins.append("  loop $lp_rp1")
        # i + len_n > len_h → break
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {len_n}")
        ins.append("    i32.add")
        ins.append(f"    local.get {len_h}")
        ins.append("    i32.gt_u")
        ins.append("    br_if $brk_rp1")
        # Inner: compare needle
        ins.append("    i32.const 0")
        ins.append(f"    local.set {j}")
        ins.append("    i32.const 1")
        ins.append(f"    local.set {matched}")
        ins.append("    block $brk_rp1i")
        ins.append("      loop $lp_rp1i")
        ins.append(f"        local.get {j}")
        ins.append(f"        local.get {len_n}")
        ins.append("        i32.ge_u")
        ins.append("        br_if $brk_rp1i")
        ins.append(f"        local.get {ptr_h}")
        ins.append(f"        local.get {i}")
        ins.append("        i32.add")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append(f"        local.get {ptr_n}")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append("        i32.ne")
        ins.append("        if")
        ins.append("          i32.const 0")
        ins.append(f"          local.set {matched}")
        ins.append("          br $brk_rp1i")
        ins.append("        end")
        ins.append(f"        local.get {j}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {j}")
        ins.append("        br $lp_rp1i")
        ins.append("      end")
        ins.append("    end")
        # If matched: count++, i += len_n; else i++
        ins.append(f"    local.get {matched}")
        ins.append("    if")
        ins.append(f"      local.get {count}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {count}")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_n}")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    else")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    end")
        ins.append("    br $lp_rp1")
        ins.append("  end")
        ins.append("end")

        # Compute new_len = len_h - count * len_n + count * len_r
        ins.append(f"local.get {len_h}")
        ins.append(f"local.get {count}")
        ins.append(f"local.get {len_n}")
        ins.append("i32.mul")
        ins.append("i32.sub")
        ins.append(f"local.get {count}")
        ins.append(f"local.get {len_r}")
        ins.append("i32.mul")
        ins.append("i32.add")
        ins.append(f"local.set {new_len}")

        # Allocate result
        ins.append(f"local.get {new_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # ---- Pass 2: copy with replacements ----
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {out_idx}")

        ins.append("block $brk_rp2")
        ins.append("  loop $lp_rp2")
        # i >= len_h → break
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {len_h}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_rp2")

        # Check if needle matches at position i (only if i+len_n <= len_h)
        ins.append("    i32.const 0")
        ins.append(f"    local.set {matched}")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {len_n}")
        ins.append("    i32.add")
        ins.append(f"    local.get {len_h}")
        ins.append("    i32.le_u")
        ins.append("    if")
        ins.append("      i32.const 0")
        ins.append(f"      local.set {j}")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {matched}")
        ins.append("      block $brk_rp2i")
        ins.append("        loop $lp_rp2i")
        ins.append(f"          local.get {j}")
        ins.append(f"          local.get {len_n}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_rp2i")
        ins.append(f"          local.get {ptr_h}")
        ins.append(f"          local.get {i}")
        ins.append("          i32.add")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append(f"          local.get {ptr_n}")
        ins.append(f"          local.get {j}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.ne")
        ins.append("          if")
        ins.append("            i32.const 0")
        ins.append(f"            local.set {matched}")
        ins.append("            br $brk_rp2i")
        ins.append("          end")
        ins.append(f"          local.get {j}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {j}")
        ins.append("          br $lp_rp2i")
        ins.append("        end")
        ins.append("      end")
        ins.append("    end")

        # If matched: copy replacement, advance i by len_n
        ins.append(f"    local.get {matched}")
        ins.append("    if")
        # Copy replacement bytes
        ins.append("      i32.const 0")
        ins.append(f"      local.set {copy_idx}")
        ins.append("      block $brk_rpc")
        ins.append("        loop $lp_rpc")
        ins.append(f"          local.get {copy_idx}")
        ins.append(f"          local.get {len_r}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_rpc")
        ins.append(f"          local.get {dst}")
        ins.append(f"          local.get {out_idx}")
        ins.append("          i32.add")
        ins.append(f"          local.get {ptr_r}")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.store8 offset=0")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {copy_idx}")
        ins.append(f"          local.get {out_idx}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {out_idx}")
        ins.append("          br $lp_rpc")
        ins.append("        end")
        ins.append("      end")
        # Advance i by len_n
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_n}")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    else")
        # Copy one byte from haystack
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {out_idx}")
        ins.append("      i32.add")
        ins.append(f"      local.get {ptr_h}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {out_idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {out_idx}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    end")
        ins.append("    br $lp_rp2")
        ins.append("  end")
        ins.append("end")

        ins.append("end")  # end $rp_main

        # Result: (dst, new_len)
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {new_len}")
        return ins

    def _translate_split(
        self,
        arg_s: ast.Expr,
        arg_d: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate split(string, delimiter) → Array<String> (i32_pair).

        Two-pass algorithm:
        1. Count delimiter occurrences to determine segment count.
        2. Allocate array buffer (seg_count * 8 bytes), then for each
           segment allocate a string buffer and copy bytes.
        Returns (arr_ptr, seg_count).
        """
        s_instrs = self.translate_expr(arg_s, env)
        d_instrs = self.translate_expr(arg_d, env)
        if s_instrs is None or d_instrs is None:
            return None

        self.needs_alloc = True

        ptr_s = self.alloc_local("i32")
        len_s = self.alloc_local("i32")
        ptr_d = self.alloc_local("i32")
        len_d = self.alloc_local("i32")
        count = self.alloc_local("i32")
        seg_count = self.alloc_local("i32")
        arr = self.alloc_local("i32")
        seg_idx = self.alloc_local("i32")
        seg_start = self.alloc_local("i32")
        i = self.alloc_local("i32")
        j = self.alloc_local("i32")
        matched = self.alloc_local("i32")
        seg_len = self.alloc_local("i32")
        seg_ptr = self.alloc_local("i32")
        copy_idx = self.alloc_local("i32")

        ins: list[str] = []

        ins.extend(s_instrs)
        ins.append(f"local.set {len_s}")
        ins.append(f"local.set {ptr_s}")
        ins.extend(d_instrs)
        ins.append(f"local.set {len_d}")
        ins.append(f"local.set {ptr_d}")

        # Wrap main computation in a block so the empty-delimiter edge case
        # can skip it with br instead of return (return would exit the
        # enclosing function, breaking subexpressions like length(split(...))).
        ins.append("block $sp_main")

        # Edge case: empty delimiter → single-element array
        ins.append(f"local.get {len_d}")
        ins.append("i32.eqz")
        ins.append("if")
        # Allocate array of 1 element (8 bytes)
        ins.append("  i32.const 8")
        ins.append("  call $alloc")
        ins.append(f"  local.set {arr}")
        ins.extend(f"  {x}" for x in gc_shadow_push(arr))
        # Allocate copy of the string
        ins.append(f"  local.get {len_s}")
        ins.append("  call $alloc")
        ins.append(f"  local.set {seg_ptr}")
        ins.extend(f"  {x}" for x in gc_shadow_push(seg_ptr))
        # Copy string bytes
        ins.append("  i32.const 0")
        ins.append(f"  local.set {i}")
        ins.append("  block $brk_spe")
        ins.append("    loop $lp_spe")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_s}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_spe")
        ins.append(f"      local.get {seg_ptr}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append(f"      local.get {ptr_s}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("      br $lp_spe")
        ins.append("    end")
        ins.append("  end")
        # Store (seg_ptr, len_s) at arr[0]
        ins.append(f"  local.get {arr}")
        ins.append(f"  local.get {seg_ptr}")
        ins.append("  i32.store offset=0")
        ins.append(f"  local.get {arr}")
        ins.append(f"  local.get {len_s}")
        ins.append("  i32.store offset=4")
        # Set seg_count = 1, skip main computation
        ins.append("  i32.const 1")
        ins.append(f"  local.set {seg_count}")
        ins.append("  br $sp_main")
        ins.append("end")

        # ---- Pass 1: count delimiter occurrences ----
        ins.append("i32.const 0")
        ins.append(f"local.set {count}")
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("block $brk_sp1")
        ins.append("  loop $lp_sp1")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {len_d}")
        ins.append("    i32.add")
        ins.append(f"    local.get {len_s}")
        ins.append("    i32.gt_u")
        ins.append("    br_if $brk_sp1")
        # Inner: compare delimiter
        ins.append("    i32.const 0")
        ins.append(f"    local.set {j}")
        ins.append("    i32.const 1")
        ins.append(f"    local.set {matched}")
        ins.append("    block $brk_sp1i")
        ins.append("      loop $lp_sp1i")
        ins.append(f"        local.get {j}")
        ins.append(f"        local.get {len_d}")
        ins.append("        i32.ge_u")
        ins.append("        br_if $brk_sp1i")
        ins.append(f"        local.get {ptr_s}")
        ins.append(f"        local.get {i}")
        ins.append("        i32.add")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append(f"        local.get {ptr_d}")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append("        i32.ne")
        ins.append("        if")
        ins.append("          i32.const 0")
        ins.append(f"          local.set {matched}")
        ins.append("          br $brk_sp1i")
        ins.append("        end")
        ins.append(f"        local.get {j}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {j}")
        ins.append("        br $lp_sp1i")
        ins.append("      end")
        ins.append("    end")
        ins.append(f"    local.get {matched}")
        ins.append("    if")
        ins.append(f"      local.get {count}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {count}")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_d}")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    else")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    end")
        ins.append("    br $lp_sp1")
        ins.append("  end")
        ins.append("end")

        # seg_count = count + 1
        ins.append(f"local.get {count}")
        ins.append("i32.const 1")
        ins.append("i32.add")
        ins.append(f"local.set {seg_count}")

        # Allocate array: seg_count * 8 bytes
        ins.append(f"local.get {seg_count}")
        ins.append("i32.const 8")
        ins.append("i32.mul")
        ins.append("call $alloc")
        ins.append(f"local.set {arr}")
        ins.extend(gc_shadow_push(arr))

        # ---- Pass 2: fill segments ----
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {seg_idx}")
        ins.append("i32.const 0")
        ins.append(f"local.set {seg_start}")

        ins.append("block $brk_sp2")
        ins.append("  loop $lp_sp2")
        # Check if i + len_d > len_s → break
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {len_d}")
        ins.append("    i32.add")
        ins.append(f"    local.get {len_s}")
        ins.append("    i32.gt_u")
        ins.append("    br_if $brk_sp2")
        # Inner: compare delimiter
        ins.append("    i32.const 0")
        ins.append(f"    local.set {j}")
        ins.append("    i32.const 1")
        ins.append(f"    local.set {matched}")
        ins.append("    block $brk_sp2i")
        ins.append("      loop $lp_sp2i")
        ins.append(f"        local.get {j}")
        ins.append(f"        local.get {len_d}")
        ins.append("        i32.ge_u")
        ins.append("        br_if $brk_sp2i")
        ins.append(f"        local.get {ptr_s}")
        ins.append(f"        local.get {i}")
        ins.append("        i32.add")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append(f"        local.get {ptr_d}")
        ins.append(f"        local.get {j}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append("        i32.ne")
        ins.append("        if")
        ins.append("          i32.const 0")
        ins.append(f"          local.set {matched}")
        ins.append("          br $brk_sp2i")
        ins.append("        end")
        ins.append(f"        local.get {j}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {j}")
        ins.append("        br $lp_sp2i")
        ins.append("      end")
        ins.append("    end")
        ins.append(f"    local.get {matched}")
        ins.append("    if")
        # Found delimiter: emit segment [seg_start, i)
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {seg_start}")
        ins.append("      i32.sub")
        ins.append(f"      local.set {seg_len}")
        # Allocate segment string
        ins.append(f"      local.get {seg_len}")
        ins.append("      call $alloc")
        ins.append(f"      local.set {seg_ptr}")
        ins.extend(f"      {x}" for x in gc_shadow_push(seg_ptr))
        # Copy segment bytes
        ins.append("      i32.const 0")
        ins.append(f"      local.set {copy_idx}")
        ins.append("      block $brk_spc")
        ins.append("        loop $lp_spc")
        ins.append(f"          local.get {copy_idx}")
        ins.append(f"          local.get {seg_len}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_spc")
        ins.append(f"          local.get {seg_ptr}")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.add")
        ins.append(f"          local.get {ptr_s}")
        ins.append(f"          local.get {seg_start}")
        ins.append("          i32.add")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.store8 offset=0")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {copy_idx}")
        ins.append("          br $lp_spc")
        ins.append("        end")
        ins.append("      end")
        # Store (seg_ptr, seg_len) in array
        ins.append(f"      local.get {arr}")
        ins.append(f"      local.get {seg_idx}")
        ins.append("      i32.const 8")
        ins.append("      i32.mul")
        ins.append("      i32.add")
        ins.append(f"      local.get {seg_ptr}")
        ins.append("      i32.store offset=0")
        ins.append(f"      local.get {arr}")
        ins.append(f"      local.get {seg_idx}")
        ins.append("      i32.const 8")
        ins.append("      i32.mul")
        ins.append("      i32.add")
        ins.append(f"      local.get {seg_len}")
        ins.append("      i32.store offset=4")
        # Advance
        ins.append(f"      local.get {seg_idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {seg_idx}")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {len_d}")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.set {seg_start}")
        ins.append("    else")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("    end")
        ins.append("    br $lp_sp2")
        ins.append("  end")
        ins.append("end")

        # Handle last segment: [seg_start, len_s)
        ins.append(f"local.get {len_s}")
        ins.append(f"local.get {seg_start}")
        ins.append("i32.sub")
        ins.append(f"local.set {seg_len}")
        ins.append(f"local.get {seg_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {seg_ptr}")
        ins.extend(gc_shadow_push(seg_ptr))
        # Copy last segment
        ins.append("i32.const 0")
        ins.append(f"local.set {copy_idx}")
        ins.append("block $brk_spl")
        ins.append("  loop $lp_spl")
        ins.append(f"    local.get {copy_idx}")
        ins.append(f"    local.get {seg_len}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_spl")
        ins.append(f"    local.get {seg_ptr}")
        ins.append(f"    local.get {copy_idx}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ptr_s}")
        ins.append(f"    local.get {seg_start}")
        ins.append("    i32.add")
        ins.append(f"    local.get {copy_idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")
        ins.append(f"    local.get {copy_idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {copy_idx}")
        ins.append("    br $lp_spl")
        ins.append("  end")
        ins.append("end")
        # Store last segment in array
        ins.append(f"local.get {arr}")
        ins.append(f"local.get {seg_idx}")
        ins.append("i32.const 8")
        ins.append("i32.mul")
        ins.append("i32.add")
        ins.append(f"local.get {seg_ptr}")
        ins.append("i32.store offset=0")
        ins.append(f"local.get {arr}")
        ins.append(f"local.get {seg_idx}")
        ins.append("i32.const 8")
        ins.append("i32.mul")
        ins.append("i32.add")
        ins.append(f"local.get {seg_len}")
        ins.append("i32.store offset=4")

        ins.append("end")  # end $sp_main

        # Return (arr, seg_count)
        ins.append(f"local.get {arr}")
        ins.append(f"local.get {seg_count}")
        return ins

    def _translate_join(
        self,
        arg_a: ast.Expr,
        arg_s: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate join(array, separator) → String (i32_pair).

        Two-pass algorithm:
        1. Sum all string lengths plus separators.
        2. Allocate result buffer and copy strings with separator
           between them.
        Array<String> is (arr_ptr, count).  Each element is 8 bytes:
        (str_ptr: i32, str_len: i32) at arr_ptr + i*8.
        """
        a_instrs = self.translate_expr(arg_a, env)
        s_instrs = self.translate_expr(arg_s, env)
        if a_instrs is None or s_instrs is None:
            return None

        self.needs_alloc = True

        arr_ptr = self.alloc_local("i32")
        arr_count = self.alloc_local("i32")
        ptr_sep = self.alloc_local("i32")
        len_sep = self.alloc_local("i32")
        total_len = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        i = self.alloc_local("i32")
        out_idx = self.alloc_local("i32")
        str_ptr = self.alloc_local("i32")
        str_len = self.alloc_local("i32")
        copy_idx = self.alloc_local("i32")

        ins: list[str] = []

        # Evaluate array → (ptr, count)
        ins.extend(a_instrs)
        ins.append(f"local.set {arr_count}")
        ins.append(f"local.set {arr_ptr}")
        # Evaluate separator → (ptr, len)
        ins.extend(s_instrs)
        ins.append(f"local.set {len_sep}")
        ins.append(f"local.set {ptr_sep}")

        # ---- Pass 1: compute total length ----
        ins.append("i32.const 0")
        ins.append(f"local.set {total_len}")
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("block $brk_j1")
        ins.append("  loop $lp_j1")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {arr_count}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_j1")
        # Load str_len at arr_ptr + i*8 + 4
        ins.append(f"    local.get {arr_ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 8")
        ins.append("    i32.mul")
        ins.append("    i32.add")
        ins.append("    i32.load offset=4")
        ins.append(f"    local.set {str_len}")
        ins.append(f"    local.get {total_len}")
        ins.append(f"    local.get {str_len}")
        ins.append("    i32.add")
        ins.append(f"    local.set {total_len}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_j1")
        ins.append("  end")
        ins.append("end")

        # Add separator lengths: (count - 1) * len_sep (if count > 0)
        ins.append(f"local.get {arr_count}")
        ins.append("i32.const 1")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {total_len}")
        ins.append(f"  local.get {arr_count}")
        ins.append("  i32.const 1")
        ins.append("  i32.sub")
        ins.append(f"  local.get {len_sep}")
        ins.append("  i32.mul")
        ins.append("  i32.add")
        ins.append(f"  local.set {total_len}")
        ins.append("end")

        # Allocate result
        ins.append(f"local.get {total_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # ---- Pass 2: copy strings with separators ----
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {out_idx}")

        ins.append("block $brk_j2")
        ins.append("  loop $lp_j2")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {arr_count}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_j2")
        # Load (str_ptr, str_len) from array
        ins.append(f"    local.get {arr_ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 8")
        ins.append("    i32.mul")
        ins.append("    i32.add")
        ins.append("    i32.load offset=0")
        ins.append(f"    local.set {str_ptr}")
        ins.append(f"    local.get {arr_ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 8")
        ins.append("    i32.mul")
        ins.append("    i32.add")
        ins.append("    i32.load offset=4")
        ins.append(f"    local.set {str_len}")
        # Copy string bytes
        ins.append("    i32.const 0")
        ins.append(f"    local.set {copy_idx}")
        ins.append("    block $brk_jc")
        ins.append("      loop $lp_jc")
        ins.append(f"        local.get {copy_idx}")
        ins.append(f"        local.get {str_len}")
        ins.append("        i32.ge_u")
        ins.append("        br_if $brk_jc")
        ins.append(f"        local.get {dst}")
        ins.append(f"        local.get {out_idx}")
        ins.append("        i32.add")
        ins.append(f"        local.get {str_ptr}")
        ins.append(f"        local.get {copy_idx}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append("        i32.store8 offset=0")
        ins.append(f"        local.get {out_idx}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {out_idx}")
        ins.append(f"        local.get {copy_idx}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {copy_idx}")
        ins.append("        br $lp_jc")
        ins.append("      end")
        ins.append("    end")
        # If not last element, copy separator
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {arr_count}")
        ins.append("    i32.const 1")
        ins.append("    i32.sub")
        ins.append("    i32.lt_u")
        ins.append("    if")
        ins.append("      i32.const 0")
        ins.append(f"      local.set {copy_idx}")
        ins.append("      block $brk_js")
        ins.append("        loop $lp_js")
        ins.append(f"          local.get {copy_idx}")
        ins.append(f"          local.get {len_sep}")
        ins.append("          i32.ge_u")
        ins.append("          br_if $brk_js")
        ins.append(f"          local.get {dst}")
        ins.append(f"          local.get {out_idx}")
        ins.append("          i32.add")
        ins.append(f"          local.get {ptr_sep}")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.add")
        ins.append("          i32.load8_u offset=0")
        ins.append("          i32.store8 offset=0")
        ins.append(f"          local.get {out_idx}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {out_idx}")
        ins.append(f"          local.get {copy_idx}")
        ins.append("          i32.const 1")
        ins.append("          i32.add")
        ins.append(f"          local.set {copy_idx}")
        ins.append("          br $lp_js")
        ins.append("        end")
        ins.append("      end")
        ins.append("    end")
        # i++
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_j2")
        ins.append("  end")
        ins.append("end")

        # Result: (dst, total_len)
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {total_len}")
        return ins

    # ==================================================================
    # #471 — character classification.  Each classifier loads the first
    # byte of the input string (or returns false for empty) and tests
    # against a small set of ASCII ranges / literals.
    #
    # All six share scaffolding via ``_translate_classifier`` — a
    # helper that emits the empty-check and the byte-load, then takes
    # an inline "body" list that performs the range test on the loaded
    # byte and leaves an i32 (0 or 1) on the stack.
    # ==================================================================

    def _translate_classifier(
        self, arg: ast.Expr, env: WasmSlotEnv, *, body: list[str],
    ) -> list[str] | None:
        """Shared scaffold for ``is_*`` classifiers.

        ``body`` is a list of WAT instructions that assumes the loaded
        first byte is on the stack and must leave an i32 (0 or 1) on
        the stack.  Empty-string convention: returns 0 (false).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        result = self.alloc_local("i32")

        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        ins.append("i32.const 0")
        ins.append(f"local.set {result}")

        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if")
        ins.append("else")
        ins.append(f"  local.get {ptr}")
        ins.append("  i32.load8_u offset=0")
        ins.extend(f"  {line}" for line in body)
        ins.append(f"  local.set {result}")
        ins.append("end")

        ins.append(f"local.get {result}")
        return ins

    def _translate_is_digit(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """is_digit: byte in 48..=57 ('0'..='9').

        Unsigned range trick: (byte - 48) < 10.
        """
        return self._translate_classifier(arg, env, body=[
            "i32.const 48",
            "i32.sub",
            "i32.const 10",
            "i32.lt_u",
        ])

    def _translate_is_alpha(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """is_alpha: byte in 65..=90 OR 97..=122 (A-Z or a-z).

        Optimisation: OR the byte with 0x20 to fold the case, then
        single range check for 97..=122.  Works because the ASCII
        letter ranges differ by exactly bit 5 (0x20).
        """
        return self._translate_classifier(arg, env, body=[
            "i32.const 32",
            "i32.or",
            "i32.const 97",
            "i32.sub",
            "i32.const 26",
            "i32.lt_u",
        ])

    def _translate_is_alphanumeric(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """is_alphanumeric: digit OR alpha.

        Load byte once; save to local; run digit check + alpha check;
        OR results.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        result = self.alloc_local("i32")
        byte = self.alloc_local("i32")

        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")
        ins.append("i32.const 0")
        ins.append(f"local.set {result}")

        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if")
        ins.append("else")
        ins.append(f"  local.get {ptr}")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {byte}")
        # digit check
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 48")
        ins.append("  i32.sub")
        ins.append("  i32.const 10")
        ins.append("  i32.lt_u")
        # alpha check (case-folded)
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 32")
        ins.append("  i32.or")
        ins.append("  i32.const 97")
        ins.append("  i32.sub")
        ins.append("  i32.const 26")
        ins.append("  i32.lt_u")
        ins.append("  i32.or")
        ins.append(f"  local.set {result}")
        ins.append("end")

        ins.append(f"local.get {result}")
        return ins

    def _translate_is_whitespace(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """is_whitespace: byte in {space(32), tab(9), LF(10), CR(13)}."""
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        result = self.alloc_local("i32")
        byte = self.alloc_local("i32")

        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")
        ins.append("i32.const 0")
        ins.append(f"local.set {result}")

        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if")
        ins.append("else")
        ins.append(f"  local.get {ptr}")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {byte}")
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 32")
        ins.append("  i32.eq")
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 9")
        ins.append("  i32.eq")
        ins.append("  i32.or")
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 10")
        ins.append("  i32.eq")
        ins.append("  i32.or")
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 13")
        ins.append("  i32.eq")
        ins.append("  i32.or")
        ins.append(f"  local.set {result}")
        ins.append("end")

        ins.append(f"local.get {result}")
        return ins

    def _translate_is_upper(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """is_upper: byte in 65..=90 ('A'..='Z')."""
        return self._translate_classifier(arg, env, body=[
            "i32.const 65",
            "i32.sub",
            "i32.const 26",
            "i32.lt_u",
        ])

    def _translate_is_lower(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """is_lower: byte in 97..=122 ('a'..='z')."""
        return self._translate_classifier(arg, env, body=[
            "i32.const 97",
            "i32.sub",
            "i32.const 26",
            "i32.lt_u",
        ])

    # ==================================================================
    # #471 — single-character case conversion.  Copy the whole string
    # and flip the case of the first byte if it's an ASCII letter.
    # ==================================================================

    def _translate_char_to_upper(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """char_to_upper(s): if s[0] is a-z, uppercase it; else leave alone."""
        return self._translate_char_case(arg, env, to_upper=True)

    def _translate_char_to_lower(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """char_to_lower(s): if s[0] is A-Z, lowercase it; else leave alone."""
        return self._translate_char_case(arg, env, to_upper=False)

    def _translate_char_case(
        self, arg: ast.Expr, env: WasmSlotEnv, *, to_upper: bool,
    ) -> list[str] | None:
        """Shared scaffold for char_to_upper / char_to_lower.

        Allocates a new buffer the same size as the input, copies
        every byte, then conditionally flips the first byte's case.
        Empty strings pass through unchanged.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        byte = self.alloc_local("i32")

        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")
        ins.extend(gc_shadow_push(ptr))

        ins.append(f"local.get {slen}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # Copy all bytes
        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("block $brk_ccp")
        ins.append("  loop $lp_ccp")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_ccp")
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_ccp")
        ins.append("  end")
        ins.append("end")

        # If slen > 0: conditionally flip first byte's case
        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if")
        ins.append("else")
        ins.append(f"  local.get {dst}")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {byte}")
        if to_upper:
            # if 97 <= byte <= 122: dst[0] = byte - 32
            ins.append(f"  local.get {byte}")
            ins.append("  i32.const 97")
            ins.append("  i32.sub")
            ins.append("  i32.const 26")
            ins.append("  i32.lt_u")
            ins.append("  if")
            ins.append(f"    local.get {dst}")
            ins.append(f"    local.get {byte}")
            ins.append("    i32.const 32")
            ins.append("    i32.sub")
            ins.append("    i32.store8 offset=0")
            ins.append("  end")
        else:
            # if 65 <= byte <= 90: dst[0] = byte + 32
            ins.append(f"  local.get {byte}")
            ins.append("  i32.const 65")
            ins.append("  i32.sub")
            ins.append("  i32.const 26")
            ins.append("  i32.lt_u")
            ins.append("  if")
            ins.append(f"    local.get {dst}")
            ins.append(f"    local.get {byte}")
            ins.append("    i32.const 32")
            ins.append("    i32.add")
            ins.append("    i32.store8 offset=0")
            ins.append("  end")
        ins.append("end")

        ins.append(f"local.get {dst}")
        ins.append(f"local.get {slen}")
        return ins

    # ==================================================================
    # #470 — string_reverse.  Copy bytes in reverse order.  ASCII only
    # (matches the rest of Vera's byte-oriented string library).
    # ==================================================================

    def _translate_string_reverse(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """string_reverse(s): new string with bytes in reverse order."""
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")
        ins.extend(gc_shadow_push(ptr))

        ins.append(f"local.get {slen}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("block $brk_rev")
        ins.append("  loop $lp_rev")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_rev")
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.const 1")
        ins.append("    i32.sub")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.sub")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_rev")
        ins.append("  end")
        ins.append("end")

        ins.append(f"local.get {dst}")
        ins.append(f"local.get {slen}")
        return ins

    # ==================================================================
    # #470 — string_trim_start / string_trim_end.  One-sided variants
    # of string_strip.  ASCII whitespace only.
    # ==================================================================

    def _translate_string_trim_start(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """string_trim_start(s): drop leading whitespace."""
        return self._translate_trim(arg, env, trim_start=True, trim_end=False)

    def _translate_string_trim_end(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """string_trim_end(s): drop trailing whitespace."""
        return self._translate_trim(arg, env, trim_start=False, trim_end=True)

    def _translate_trim(
        self,
        arg: ast.Expr,
        env: WasmSlotEnv,
        *,
        trim_start: bool,
        trim_end: bool,
    ) -> list[str] | None:
        """Shared trim scaffold — adjusts start/end pointers then
        copies the trimmed slice to a fresh buffer.
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

        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        ins.append("i32.const 0")
        ins.append(f"local.set {start}")
        ins.append(f"local.get {slen}")
        ins.append(f"local.set {end}")

        def _is_ws_inline() -> list[str]:
            return [
                f"    local.set {byte}",
                f"    local.get {byte}", "    i32.const 32", "    i32.eq",
                f"    local.get {byte}", "    i32.const 9",  "    i32.eq",
                "    i32.or",
                f"    local.get {byte}", "    i32.const 10", "    i32.eq",
                "    i32.or",
                f"    local.get {byte}", "    i32.const 13", "    i32.eq",
                "    i32.or",
            ]

        if trim_start:
            ins.append("block $brk_ls")
            ins.append("  loop $lp_ls")
            ins.append(f"    local.get {start}")
            ins.append(f"    local.get {end}")
            ins.append("    i32.ge_u")
            ins.append("    br_if $brk_ls")
            ins.append(f"    local.get {ptr}")
            ins.append(f"    local.get {start}")
            ins.append("    i32.add")
            ins.append("    i32.load8_u offset=0")
            ins.extend(_is_ws_inline())
            ins.append("    i32.eqz")
            ins.append("    br_if $brk_ls")
            ins.append(f"    local.get {start}")
            ins.append("    i32.const 1")
            ins.append("    i32.add")
            ins.append(f"    local.set {start}")
            ins.append("    br $lp_ls")
            ins.append("  end")
            ins.append("end")

        if trim_end:
            ins.append("block $brk_le")
            ins.append("  loop $lp_le")
            ins.append(f"    local.get {end}")
            ins.append(f"    local.get {start}")
            ins.append("    i32.le_u")
            ins.append("    br_if $brk_le")
            ins.append(f"    local.get {ptr}")
            ins.append(f"    local.get {end}")
            ins.append("    i32.const 1")
            ins.append("    i32.sub")
            ins.append("    i32.add")
            ins.append("    i32.load8_u offset=0")
            ins.extend(_is_ws_inline())
            ins.append("    i32.eqz")
            ins.append("    br_if $brk_le")
            ins.append(f"    local.get {end}")
            ins.append("    i32.const 1")
            ins.append("    i32.sub")
            ins.append(f"    local.set {end}")
            ins.append("    br $lp_le")
            ins.append("  end")
            ins.append("end")

        ins.append(f"local.get {end}")
        ins.append(f"local.get {start}")
        ins.append("i32.sub")
        ins.append(f"local.set {new_len}")

        ins.append(f"local.get {new_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("block $brk_cp")
        ins.append("  loop $lp_cp")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {new_len}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_cp")
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {start}")
        ins.append("    i32.add")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_cp")
        ins.append("  end")
        ins.append("end")

        ins.append(f"local.get {dst}")
        ins.append(f"local.get {new_len}")
        return ins

    # ==================================================================
    # #470 — string_pad_start / string_pad_end.  Pad the input string
    # to a target length by prepending (start) or appending (end) the
    # fill string.  Fill cycles if the required padding is longer
    # than the fill string (JavaScript padStart/padEnd semantics).
    # Target length less than input length: input returned unchanged.
    # Empty fill string: input returned unchanged (avoids a division-
    # by-zero modulo).
    # ==================================================================

    def _translate_string_pad_start(
        self,
        arg_s: ast.Expr,
        arg_target: ast.Expr,
        arg_fill: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """string_pad_start(s, target_len, fill)."""
        return self._translate_pad(
            arg_s, arg_target, arg_fill, env, pad_start=True,
        )

    def _translate_string_pad_end(
        self,
        arg_s: ast.Expr,
        arg_target: ast.Expr,
        arg_fill: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """string_pad_end(s, target_len, fill)."""
        return self._translate_pad(
            arg_s, arg_target, arg_fill, env, pad_start=False,
        )

    def _translate_pad(
        self,
        arg_s: ast.Expr,
        arg_target: ast.Expr,
        arg_fill: ast.Expr,
        env: WasmSlotEnv,
        *,
        pad_start: bool,
    ) -> list[str] | None:
        """Shared scaffold for pad_start / pad_end.

        Algorithm:
          1. target_i32 = wrap_i64(target_len)
          2. if target_i32 <= slen: allocate slen bytes, copy s, return
          3. if fill_len == 0: allocate slen bytes, copy s, return
          4. pad_len = target_i32 - slen
          5. allocate target_i32 bytes
          6. if pad_start: fill dst[0..pad_len], then copy s into dst[pad_len..]
             if pad_end:   copy s into dst[0..slen], then fill dst[slen..]
          7. return (dst, target_i32)
        """
        s_instrs = self.translate_expr(arg_s, env)
        target_instrs = self.translate_expr(arg_target, env)
        fill_instrs = self.translate_expr(arg_fill, env)
        if s_instrs is None or target_instrs is None or fill_instrs is None:
            return None
        self.needs_alloc = True

        ptr_s = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        target = self.alloc_local("i32")
        ptr_f = self.alloc_local("i32")
        flen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        out_len = self.alloc_local("i32")
        pad_len = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        ins: list[str] = []
        ins.extend(s_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr_s}")
        ins.extend(gc_shadow_push(ptr_s))

        # target = wrap(i64)
        ins.extend(target_instrs)
        ins.append("i32.wrap_i64")
        ins.append(f"local.set {target}")

        ins.extend(fill_instrs)
        ins.append(f"local.set {flen}")
        ins.append(f"local.set {ptr_f}")
        ins.extend(gc_shadow_push(ptr_f))

        # If target <= slen OR flen == 0: no padding — out_len = slen.
        # Otherwise: out_len = target.
        ins.append(f"local.get {target}")
        ins.append(f"local.get {slen}")
        ins.append("i32.le_u")
        ins.append(f"local.get {flen}")
        ins.append("i32.eqz")
        ins.append("i32.or")
        ins.append("if (result i32)")
        ins.append(f"  local.get {slen}")
        ins.append("else")
        ins.append(f"  local.get {target}")
        ins.append("end")
        ins.append(f"local.set {out_len}")

        # pad_len = out_len - slen  (zero in the no-pad case)
        ins.append(f"local.get {out_len}")
        ins.append(f"local.get {slen}")
        ins.append("i32.sub")
        ins.append(f"local.set {pad_len}")

        # dst = $alloc(out_len)
        ins.append(f"local.get {out_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        if pad_start:
            # Fill phase: dst[i] = fill[i % flen] for i in [0, pad_len).
            # Guarded against flen == 0 (pad_len is 0 in that case).
            ins.append("i32.const 0")
            ins.append(f"local.set {idx}")
            ins.append("block $brk_pf")
            ins.append("  loop $lp_pf")
            ins.append(f"    local.get {idx}")
            ins.append(f"    local.get {pad_len}")
            ins.append("    i32.ge_u")
            ins.append("    br_if $brk_pf")
            ins.append(f"    local.get {dst}")
            ins.append(f"    local.get {idx}")
            ins.append("    i32.add")
            ins.append(f"    local.get {ptr_f}")
            ins.append(f"    local.get {idx}")
            ins.append(f"    local.get {flen}")
            ins.append("    i32.rem_u")
            ins.append("    i32.add")
            ins.append("    i32.load8_u offset=0")
            ins.append("    i32.store8 offset=0")
            ins.append(f"    local.get {idx}")
            ins.append("    i32.const 1")
            ins.append("    i32.add")
            ins.append(f"    local.set {idx}")
            ins.append("    br $lp_pf")
            ins.append("  end")
            ins.append("end")

            # Copy s into dst[pad_len..]
            ins.append("i32.const 0")
            ins.append(f"local.set {idx}")
            ins.append("block $brk_ps")
            ins.append("  loop $lp_ps")
            ins.append(f"    local.get {idx}")
            ins.append(f"    local.get {slen}")
            ins.append("    i32.ge_u")
            ins.append("    br_if $brk_ps")
            ins.append(f"    local.get {dst}")
            ins.append(f"    local.get {pad_len}")
            ins.append("    i32.add")
            ins.append(f"    local.get {idx}")
            ins.append("    i32.add")
            ins.append(f"    local.get {ptr_s}")
            ins.append(f"    local.get {idx}")
            ins.append("    i32.add")
            ins.append("    i32.load8_u offset=0")
            ins.append("    i32.store8 offset=0")
            ins.append(f"    local.get {idx}")
            ins.append("    i32.const 1")
            ins.append("    i32.add")
            ins.append(f"    local.set {idx}")
            ins.append("    br $lp_ps")
            ins.append("  end")
            ins.append("end")
        else:
            # pad_end: copy s first, then fill.
            ins.append("i32.const 0")
            ins.append(f"local.set {idx}")
            ins.append("block $brk_ps")
            ins.append("  loop $lp_ps")
            ins.append(f"    local.get {idx}")
            ins.append(f"    local.get {slen}")
            ins.append("    i32.ge_u")
            ins.append("    br_if $brk_ps")
            ins.append(f"    local.get {dst}")
            ins.append(f"    local.get {idx}")
            ins.append("    i32.add")
            ins.append(f"    local.get {ptr_s}")
            ins.append(f"    local.get {idx}")
            ins.append("    i32.add")
            ins.append("    i32.load8_u offset=0")
            ins.append("    i32.store8 offset=0")
            ins.append(f"    local.get {idx}")
            ins.append("    i32.const 1")
            ins.append("    i32.add")
            ins.append(f"    local.set {idx}")
            ins.append("    br $lp_ps")
            ins.append("  end")
            ins.append("end")

            # Fill dst[slen..slen+pad_len]
            ins.append("i32.const 0")
            ins.append(f"local.set {idx}")
            ins.append("block $brk_pf")
            ins.append("  loop $lp_pf")
            ins.append(f"    local.get {idx}")
            ins.append(f"    local.get {pad_len}")
            ins.append("    i32.ge_u")
            ins.append("    br_if $brk_pf")
            ins.append(f"    local.get {dst}")
            ins.append(f"    local.get {slen}")
            ins.append("    i32.add")
            ins.append(f"    local.get {idx}")
            ins.append("    i32.add")
            ins.append(f"    local.get {ptr_f}")
            ins.append(f"    local.get {idx}")
            ins.append(f"    local.get {flen}")
            ins.append("    i32.rem_u")
            ins.append("    i32.add")
            ins.append("    i32.load8_u offset=0")
            ins.append("    i32.store8 offset=0")
            ins.append(f"    local.get {idx}")
            ins.append("    i32.const 1")
            ins.append("    i32.add")
            ins.append(f"    local.set {idx}")
            ins.append("    br $lp_pf")
            ins.append("  end")
            ins.append("end")

        ins.append(f"local.get {dst}")
        ins.append(f"local.get {out_len}")
        return ins

    # ==================================================================
    # #470 — Array<String>-returning splits: string_chars, string_lines,
    # string_words.
    #
    # Shared shape: allocate one "data" buffer (a copy of s), allocate
    # one "outer" buffer of count * 8 bytes, then walk s populating
    # outer[k] = (data_ptr + start_k, end_k - start_k).  All slices
    # share the single data buffer so the memory cost is O(slen) for
    # the data plus O(count) for the outer — not O(slen + count*slen).
    #
    # Each function differs only in: (a) how it counts segments in
    # the first pass, and (b) how it advances through the data in
    # the second pass.  A shared helper would abstract the allocation
    # / outer-write mechanics but the per-function pass bodies are
    # simple enough inlined.
    # ==================================================================

    def _translate_string_chars(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """string_chars(s): Array of one-byte strings, one per byte of s.

        ASCII semantics — multi-byte characters are split per byte.
        Matches Vera's byte-oriented string model (same as
        string_char_code, string_slice etc.).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True

        ptr_s = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        data = self.alloc_local("i32")
        outer = self.alloc_local("i32")
        idx = self.alloc_local("i32")

        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr_s}")
        ins.extend(gc_shadow_push(ptr_s))

        # data = $alloc(slen); copy s -> data
        ins.append(f"local.get {slen}")
        ins.append("call $alloc")
        ins.append(f"local.set {data}")
        ins.extend(gc_shadow_push(data))

        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("block $brk_sc_cp")
        ins.append("  loop $lp_sc_cp")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_sc_cp")
        ins.append(f"    local.get {data}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ptr_s}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_sc_cp")
        ins.append("  end")
        ins.append("end")

        # outer = $alloc(slen * 8)
        ins.append(f"local.get {slen}")
        ins.append("i32.const 8")
        ins.append("i32.mul")
        ins.append("call $alloc")
        ins.append(f"local.set {outer}")
        ins.extend(gc_shadow_push(outer))

        # for idx in [0, slen): outer[idx*8] = (data + idx, 1)
        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("block $brk_sc_fill")
        ins.append("  loop $lp_sc_fill")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_sc_fill")
        # outer[idx*8 + 0] = data + idx
        ins.append(f"    local.get {outer}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 8")
        ins.append("    i32.mul")
        ins.append("    i32.add")
        ins.append(f"    local.get {data}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.store offset=0")
        # outer[idx*8 + 4] = 1
        ins.append(f"    local.get {outer}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 8")
        ins.append("    i32.mul")
        ins.append("    i32.add")
        ins.append("    i32.const 1")
        ins.append("    i32.store offset=4")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_sc_fill")
        ins.append("  end")
        ins.append("end")

        ins.append(f"local.get {outer}")
        ins.append(f"local.get {slen}")
        return ins

    # ==================================================================
    # string_lines — split on \n, \r\n, \r.  Python's splitlines()
    # semantics: trailing newline does NOT produce an empty final
    # element; empty input produces an empty array.
    #
    # Pass 1: count lines by walking the byte stream and counting
    # terminators, treating \r\n as one terminator.
    # Pass 2: walk again emitting (data_ptr + start, end - start) for
    # each line.
    # ==================================================================

    def _translate_string_lines(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """string_lines(s)."""
        return self._translate_structural_split(
            arg, env, mode="lines",
        )

    def _translate_string_words(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """string_words(s)."""
        return self._translate_structural_split(
            arg, env, mode="words",
        )

    def _translate_structural_split(
        self, arg: ast.Expr, env: WasmSlotEnv, *, mode: str,
    ) -> list[str] | None:
        """Shared scaffold for string_lines / string_words.

        Both do a two-pass count-then-emit over a shared data buffer.
        The *predicate* for "this byte is a segment boundary" differs
        (line-terminator set vs any-whitespace set) and the
        *empty-segment handling* differs (lines preserves empty
        segments from consecutive terminators; words discards them),
        but the loop skeleton is identical.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True

        ptr_s = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        data = self.alloc_local("i32")
        outer = self.alloc_local("i32")
        count = self.alloc_local("i32")
        i = self.alloc_local("i32")
        seg_start = self.alloc_local("i32")
        seg_len = self.alloc_local("i32")
        byte = self.alloc_local("i32")
        slot = self.alloc_local("i32")
        write_idx = self.alloc_local("i32")
        in_word = self.alloc_local("i32")

        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr_s}")
        ins.extend(gc_shadow_push(ptr_s))

        # data = $alloc(slen); copy s -> data (shared buffer for slices)
        ins.append(f"local.get {slen}")
        ins.append("call $alloc")
        ins.append(f"local.set {data}")
        ins.extend(gc_shadow_push(data))
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("block $brk_ss_cp")
        ins.append("  loop $lp_ss_cp")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_ss_cp")
        ins.append(f"    local.get {data}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ptr_s}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_ss_cp")
        ins.append("  end")
        ins.append("end")

        # Pass 1: count segments
        ins.append("i32.const 0")
        ins.append(f"local.set {count}")
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")

        if mode == "lines":
            # Count: number of terminator runs (\n, \r\n, or \r).
            # splitlines semantics: trailing terminator does not add
            # an empty final segment.  So count = (sum of terminator
            # events) + (1 if slen > 0 and last byte was not a
            # terminator else 0).  Implemented by checking if final
            # segment has non-zero length at the end.
            #
            # Simpler: walk bytes, every time we hit a terminator
            # increment count; at the end if i != seg_start, count++
            # (for the trailing non-terminator content).
            ins.append("i32.const 0")
            ins.append(f"local.set {seg_start}")
            ins.append("block $brk_ct")
            ins.append("  loop $lp_ct")
            ins.append(f"    local.get {i}")
            ins.append(f"    local.get {slen}")
            ins.append("    i32.ge_u")
            ins.append("    br_if $brk_ct")
            ins.append(f"    local.get {ptr_s}")
            ins.append(f"    local.get {i}")
            ins.append("    i32.add")
            ins.append("    i32.load8_u offset=0")
            ins.append(f"    local.set {byte}")
            # if byte == '\n': count++, seg_start = i+1, i++
            ins.append(f"    local.get {byte}")
            ins.append("    i32.const 10")
            ins.append("    i32.eq")
            ins.append("    if")
            ins.append(f"      local.get {count}")
            ins.append("      i32.const 1")
            ins.append("      i32.add")
            ins.append(f"      local.set {count}")
            ins.append(f"      local.get {i}")
            ins.append("      i32.const 1")
            ins.append("      i32.add")
            ins.append(f"      local.set {seg_start}")
            ins.append(f"      local.get {i}")
            ins.append("      i32.const 1")
            ins.append("      i32.add")
            ins.append(f"      local.set {i}")
            ins.append("      br $lp_ct")
            ins.append("    end")
            # if byte == '\r': count++, seg_start = i+1 (or i+2 if
            # followed by '\n'), advance i accordingly
            ins.append(f"    local.get {byte}")
            ins.append("    i32.const 13")
            ins.append("    i32.eq")
            ins.append("    if")
            ins.append(f"      local.get {count}")
            ins.append("      i32.const 1")
            ins.append("      i32.add")
            ins.append(f"      local.set {count}")
            # Peek next byte if available
            ins.append(f"      local.get {i}")
            ins.append("      i32.const 1")
            ins.append("      i32.add")
            ins.append(f"      local.get {slen}")
            ins.append("      i32.lt_u")
            ins.append("      if (result i32)")
            ins.append(f"        local.get {ptr_s}")
            ins.append(f"        local.get {i}")
            ins.append("        i32.const 1")
            ins.append("        i32.add")
            ins.append("        i32.add")
            ins.append("        i32.load8_u offset=0")
            ins.append("        i32.const 10")
            ins.append("        i32.eq")
            ins.append("      else")
            ins.append("        i32.const 0")
            ins.append("      end")
            ins.append("      if (result i32)")
            ins.append(f"        local.get {i}")
            ins.append("        i32.const 2")
            ins.append("        i32.add")
            ins.append("      else")
            ins.append(f"        local.get {i}")
            ins.append("        i32.const 1")
            ins.append("        i32.add")
            ins.append("      end")
            ins.append(f"      local.set {seg_start}")
            ins.append(f"      local.get {seg_start}")
            ins.append(f"      local.set {i}")
            ins.append("      br $lp_ct")
            ins.append("    end")
            # Regular byte: i++
            ins.append(f"    local.get {i}")
            ins.append("    i32.const 1")
            ins.append("    i32.add")
            ins.append(f"    local.set {i}")
            ins.append("    br $lp_ct")
            ins.append("  end")
            ins.append("end")
            # Trailing non-terminator content? count++ if seg_start < slen
            ins.append(f"local.get {seg_start}")
            ins.append(f"local.get {slen}")
            ins.append("i32.lt_u")
            ins.append("if")
            ins.append(f"  local.get {count}")
            ins.append("  i32.const 1")
            ins.append("  i32.add")
            ins.append(f"  local.set {count}")
            ins.append("end")

        else:
            # words mode: count runs of non-whitespace.  A run begins
            # when we transition from ws to non-ws; at the end, if
            # in_word is true, count it.
            # in_word = 0
            ins.append("i32.const 0")
            ins.append(f"local.set {in_word}")
            ins.append("block $brk_cw")
            ins.append("  loop $lp_cw")
            ins.append(f"    local.get {i}")
            ins.append(f"    local.get {slen}")
            ins.append("    i32.ge_u")
            ins.append("    br_if $brk_cw")
            ins.append(f"    local.get {ptr_s}")
            ins.append(f"    local.get {i}")
            ins.append("    i32.add")
            ins.append("    i32.load8_u offset=0")
            ins.append(f"    local.set {byte}")
            # is_ws(byte) → stack
            ins.extend([
                f"    local.get {byte}", "    i32.const 32", "    i32.eq",
                f"    local.get {byte}", "    i32.const 9",  "    i32.eq",
                "    i32.or",
                f"    local.get {byte}", "    i32.const 10", "    i32.eq",
                "    i32.or",
                f"    local.get {byte}", "    i32.const 13", "    i32.eq",
                "    i32.or",
            ])
            ins.append("    if")  # is ws
            ins.append(f"      local.get {in_word}")
            ins.append("      if")
            # end of a word
            ins.append(f"        local.get {count}")
            ins.append("        i32.const 1")
            ins.append("        i32.add")
            ins.append(f"        local.set {count}")
            ins.append("        i32.const 0")
            ins.append(f"        local.set {in_word}")
            ins.append("      end")
            ins.append("    else")
            # non-ws byte
            ins.append("      i32.const 1")
            ins.append(f"      local.set {in_word}")
            ins.append("    end")
            ins.append(f"    local.get {i}")
            ins.append("    i32.const 1")
            ins.append("    i32.add")
            ins.append(f"    local.set {i}")
            ins.append("    br $lp_cw")
            ins.append("  end")
            ins.append("end")
            # trailing word?
            ins.append(f"local.get {in_word}")
            ins.append("if")
            ins.append(f"  local.get {count}")
            ins.append("  i32.const 1")
            ins.append("  i32.add")
            ins.append(f"  local.set {count}")
            ins.append("end")

        # Allocate outer array buffer (count * 8 bytes)
        ins.append(f"local.get {count}")
        ins.append("i32.const 8")
        ins.append("i32.mul")
        ins.append("call $alloc")
        ins.append(f"local.set {outer}")
        ins.extend(gc_shadow_push(outer))

        # Pass 2: walk again and emit (ptr, len) pairs into outer
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {seg_start}")
        ins.append("i32.const 0")
        ins.append(f"local.set {write_idx}")

        if mode == "lines":
            ins.append("block $brk_et")
            ins.append("  loop $lp_et")
            ins.append(f"    local.get {i}")
            ins.append(f"    local.get {slen}")
            ins.append("    i32.ge_u")
            ins.append("    br_if $brk_et")
            ins.append(f"    local.get {ptr_s}")
            ins.append(f"    local.get {i}")
            ins.append("    i32.add")
            ins.append("    i32.load8_u offset=0")
            ins.append(f"    local.set {byte}")
            # byte == '\n'?
            ins.append(f"    local.get {byte}")
            ins.append("    i32.const 10")
            ins.append("    i32.eq")
            ins.append("    if")
            # emit (data+seg_start, i - seg_start)
            ins.append(f"      local.get {outer}")
            ins.append(f"      local.get {write_idx}")
            ins.append("      i32.const 8")
            ins.append("      i32.mul")
            ins.append("      i32.add")
            ins.append(f"      local.set {slot}")
            ins.append(f"      local.get {slot}")
            ins.append(f"      local.get {data}")
            ins.append(f"      local.get {seg_start}")
            ins.append("      i32.add")
            ins.append("      i32.store offset=0")
            ins.append(f"      local.get {slot}")
            ins.append(f"      local.get {i}")
            ins.append(f"      local.get {seg_start}")
            ins.append("      i32.sub")
            ins.append("      i32.store offset=4")
            ins.append(f"      local.get {write_idx}")
            ins.append("      i32.const 1")
            ins.append("      i32.add")
            ins.append(f"      local.set {write_idx}")
            ins.append(f"      local.get {i}")
            ins.append("      i32.const 1")
            ins.append("      i32.add")
            ins.append(f"      local.set {seg_start}")
            ins.append(f"      local.get {seg_start}")
            ins.append(f"      local.set {i}")
            ins.append("      br $lp_et")
            ins.append("    end")
            # byte == '\r'?
            ins.append(f"    local.get {byte}")
            ins.append("    i32.const 13")
            ins.append("    i32.eq")
            ins.append("    if")
            # emit segment
            ins.append(f"      local.get {outer}")
            ins.append(f"      local.get {write_idx}")
            ins.append("      i32.const 8")
            ins.append("      i32.mul")
            ins.append("      i32.add")
            ins.append(f"      local.set {slot}")
            ins.append(f"      local.get {slot}")
            ins.append(f"      local.get {data}")
            ins.append(f"      local.get {seg_start}")
            ins.append("      i32.add")
            ins.append("      i32.store offset=0")
            ins.append(f"      local.get {slot}")
            ins.append(f"      local.get {i}")
            ins.append(f"      local.get {seg_start}")
            ins.append("      i32.sub")
            ins.append("      i32.store offset=4")
            ins.append(f"      local.get {write_idx}")
            ins.append("      i32.const 1")
            ins.append("      i32.add")
            ins.append(f"      local.set {write_idx}")
            # Determine next seg_start (skip \r\n if applicable)
            ins.append(f"      local.get {i}")
            ins.append("      i32.const 1")
            ins.append("      i32.add")
            ins.append(f"      local.get {slen}")
            ins.append("      i32.lt_u")
            ins.append("      if (result i32)")
            ins.append(f"        local.get {ptr_s}")
            ins.append(f"        local.get {i}")
            ins.append("        i32.const 1")
            ins.append("        i32.add")
            ins.append("        i32.add")
            ins.append("        i32.load8_u offset=0")
            ins.append("        i32.const 10")
            ins.append("        i32.eq")
            ins.append("      else")
            ins.append("        i32.const 0")
            ins.append("      end")
            ins.append("      if (result i32)")
            ins.append(f"        local.get {i}")
            ins.append("        i32.const 2")
            ins.append("        i32.add")
            ins.append("      else")
            ins.append(f"        local.get {i}")
            ins.append("        i32.const 1")
            ins.append("        i32.add")
            ins.append("      end")
            ins.append(f"      local.set {seg_start}")
            ins.append(f"      local.get {seg_start}")
            ins.append(f"      local.set {i}")
            ins.append("      br $lp_et")
            ins.append("    end")
            ins.append(f"    local.get {i}")
            ins.append("    i32.const 1")
            ins.append("    i32.add")
            ins.append(f"    local.set {i}")
            ins.append("    br $lp_et")
            ins.append("  end")
            ins.append("end")
            # Trailing content
            ins.append(f"local.get {seg_start}")
            ins.append(f"local.get {slen}")
            ins.append("i32.lt_u")
            ins.append("if")
            ins.append(f"  local.get {outer}")
            ins.append(f"  local.get {write_idx}")
            ins.append("  i32.const 8")
            ins.append("  i32.mul")
            ins.append("  i32.add")
            ins.append(f"  local.set {slot}")
            ins.append(f"  local.get {slot}")
            ins.append(f"  local.get {data}")
            ins.append(f"  local.get {seg_start}")
            ins.append("  i32.add")
            ins.append("  i32.store offset=0")
            ins.append(f"  local.get {slot}")
            ins.append(f"  local.get {slen}")
            ins.append(f"  local.get {seg_start}")
            ins.append("  i32.sub")
            ins.append("  i32.store offset=4")
            ins.append("end")
        else:
            # words
            ins.append("i32.const 0")
            ins.append(f"local.set {in_word}")
            ins.append("block $brk_ew")
            ins.append("  loop $lp_ew")
            ins.append(f"    local.get {i}")
            ins.append(f"    local.get {slen}")
            ins.append("    i32.ge_u")
            ins.append("    br_if $brk_ew")
            ins.append(f"    local.get {ptr_s}")
            ins.append(f"    local.get {i}")
            ins.append("    i32.add")
            ins.append("    i32.load8_u offset=0")
            ins.append(f"    local.set {byte}")
            # is_ws(byte)
            ins.extend([
                f"    local.get {byte}", "    i32.const 32", "    i32.eq",
                f"    local.get {byte}", "    i32.const 9",  "    i32.eq",
                "    i32.or",
                f"    local.get {byte}", "    i32.const 10", "    i32.eq",
                "    i32.or",
                f"    local.get {byte}", "    i32.const 13", "    i32.eq",
                "    i32.or",
            ])
            ins.append("    if")  # ws
            ins.append(f"      local.get {in_word}")
            ins.append("      if")
            # emit (data + seg_start, i - seg_start)
            ins.append(f"        local.get {outer}")
            ins.append(f"        local.get {write_idx}")
            ins.append("        i32.const 8")
            ins.append("        i32.mul")
            ins.append("        i32.add")
            ins.append(f"        local.set {slot}")
            ins.append(f"        local.get {slot}")
            ins.append(f"        local.get {data}")
            ins.append(f"        local.get {seg_start}")
            ins.append("        i32.add")
            ins.append("        i32.store offset=0")
            ins.append(f"        local.get {slot}")
            ins.append(f"        local.get {i}")
            ins.append(f"        local.get {seg_start}")
            ins.append("        i32.sub")
            ins.append("        i32.store offset=4")
            ins.append(f"        local.get {write_idx}")
            ins.append("        i32.const 1")
            ins.append("        i32.add")
            ins.append(f"        local.set {write_idx}")
            ins.append("        i32.const 0")
            ins.append(f"        local.set {in_word}")
            ins.append("      end")
            ins.append("    else")
            # non-ws
            ins.append(f"      local.get {in_word}")
            ins.append("      i32.eqz")
            ins.append("      if")
            ins.append(f"        local.get {i}")
            ins.append(f"        local.set {seg_start}")
            ins.append("        i32.const 1")
            ins.append(f"        local.set {in_word}")
            ins.append("      end")
            ins.append("    end")
            ins.append(f"    local.get {i}")
            ins.append("    i32.const 1")
            ins.append("    i32.add")
            ins.append(f"    local.set {i}")
            ins.append("    br $lp_ew")
            ins.append("  end")
            ins.append("end")
            # Trailing word?
            ins.append(f"local.get {in_word}")
            ins.append("if")
            ins.append(f"  local.get {outer}")
            ins.append(f"  local.get {write_idx}")
            ins.append("  i32.const 8")
            ins.append("  i32.mul")
            ins.append("  i32.add")
            ins.append(f"  local.set {slot}")
            ins.append(f"  local.get {slot}")
            ins.append(f"  local.get {data}")
            ins.append(f"  local.get {seg_start}")
            ins.append("  i32.add")
            ins.append("  i32.store offset=0")
            ins.append(f"  local.get {slot}")
            ins.append(f"  local.get {slen}")
            ins.append(f"  local.get {seg_start}")
            ins.append("  i32.sub")
            ins.append("  i32.store offset=4")
            ins.append("end")

        ins.append(f"local.get {outer}")
        ins.append(f"local.get {count}")
        return ins
