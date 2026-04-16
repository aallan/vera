"""Parser built-in translation mixin for WasmContext.

Handles: parse_nat, parse_int, parse_bool, parse_float64. Each parser
emits a state-machine loop in WAT and returns a ``Result<T, String>``
ADT, using the heap allocator for error messages via ``string_pool``.
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv, gc_shadow_push


class CallsParsingMixin:
    """Methods for translating parse_* built-in functions."""

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

    def _translate_parse_int(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate parse_int(s) → Result<Int, String> (i32 pointer).

        Like parse_nat but handles optional leading sign (+ or -).

        Returns an ADT heap object:
          Ok(Int):     [tag=0 : i32] [pad 4] [value : i64]   (16 bytes)
          Err(String): [tag=1 : i32] [ptr : i32] [len : i32]  (16 bytes)
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
        is_neg = self.alloc_local("i32")

        # Intern error strings
        empty_off, empty_len = self.string_pool.intern("empty string")
        invalid_off, invalid_len = self.string_pool.intern("invalid digit")

        ins: list[str] = []

        # Evaluate string → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Initialise
        ins.append("i64.const 0")
        ins.append(f"local.set {result}")
        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("i32.const 0")
        ins.append(f"local.set {has_digit}")
        ins.append("i32.const 0")
        ins.append(f"local.set {is_neg}")

        ins.append("block $done_pi")
        ins.append("block $err_pi")

        # -- Skip leading spaces -------------------------------------------
        ins.append("block $brk_sp_pi")
        ins.append("  loop $lp_sp_pi")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_sp_pi")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    br_if $brk_sp_pi")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_sp_pi")
        ins.append("  end")
        ins.append("end")

        # -- Check for sign character (+/-) --------------------------------
        ins.append(f"local.get {idx}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {idx}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {byte}")
        # Check minus (45)
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 45")
        ins.append("  i32.eq")
        ins.append("  if")
        ins.append("    i32.const 1")
        ins.append(f"    local.set {is_neg}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("  else")
        # Check plus (43)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 43")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("    end")
        ins.append("  end")
        ins.append("end")

        # -- Parse digit loop ---------------------------------------------
        ins.append("block $brk_pi")
        ins.append("  loop $lp_pi")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_pi")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {byte}")
        # Skip trailing space (byte 32)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 32")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("      br $lp_pi")
        ins.append("    end")
        # Check byte < '0' (48) → error
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.lt_u")
        ins.append("    br_if $err_pi")
        # Check byte > '9' (57) → error
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 57")
        ins.append("    i32.gt_u")
        ins.append("    br_if $err_pi")
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
        ins.append("    br $lp_pi")
        ins.append("  end")   # loop
        ins.append("end")     # block $brk_pi

        # -- After loop: no digits seen → error
        ins.append(f"local.get {has_digit}")
        ins.append("i32.eqz")
        ins.append("br_if $err_pi")

        # -- Apply sign: if is_neg, negate result
        ins.append(f"local.get {is_neg}")
        ins.append("if")
        ins.append("  i64.const 0")
        ins.append(f"  local.get {result}")
        ins.append("  i64.sub")
        ins.append(f"  local.set {result}")
        ins.append("end")

        # -- Ok path: allocate 16 bytes, tag=0, Int at offset 8 -----------
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")           # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {result}")
        ins.append("i64.store offset=8")  # Int value
        ins.append("br $done_pi")

        ins.append("end")  # block $err_pi

        # -- Err path: allocate 16 bytes, tag=1, String at offsets 4,8 ----
        ins.append(f"local.get {idx}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {invalid_off}")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append(f"local.set {idx}")
        ins.append(f"local.get {idx}")
        ins.append(f"i32.const {invalid_off}")
        ins.append("i32.eq")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {invalid_len}")
        ins.append("else")
        ins.append(f"  i32.const {empty_len}")
        ins.append("end")
        ins.append(f"local.set {byte}")
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

        ins.append("end")  # block $done_pi

        ins.append(f"local.get {out}")
        return ins

    def _translate_parse_bool(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate parse_bool(s) → Result<Bool, String> (i32 pointer).

        Accepts only strict lowercase "true" or "false" (with optional
        leading/trailing whitespace).  Returns Ok(1) for true, Ok(0) for
        false, or Err("expected true or false") otherwise.

        ADT layout (16 bytes):
          Ok(Bool):    [tag=0 : i32] [value : i32] [pad 8]
          Err(String): [tag=1 : i32] [ptr : i32]   [len : i32]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        start = self.alloc_local("i32")
        end = self.alloc_local("i32")
        content_len = self.alloc_local("i32")
        out = self.alloc_local("i32")

        err_off, err_len = self.string_pool.intern("expected true or false")

        ins: list[str] = []

        # Evaluate string → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Skip leading spaces → start
        ins.append("i32.const 0")
        ins.append(f"local.set {start}")
        ins.append("block $brk_ls")
        ins.append("  loop $lp_ls")
        ins.append(f"    local.get {start}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_ls")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {start}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    br_if $brk_ls")
        ins.append(f"    local.get {start}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {start}")
        ins.append("    br $lp_ls")
        ins.append("  end")
        ins.append("end")

        # Skip trailing spaces → end (points past last non-space)
        ins.append(f"local.get {slen}")
        ins.append(f"local.set {end}")
        ins.append("block $brk_ts")
        ins.append("  loop $lp_ts")
        ins.append(f"    local.get {end}")
        ins.append(f"    local.get {start}")
        ins.append("    i32.le_u")
        ins.append("    br_if $brk_ts")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {end}")
        ins.append("    i32.const 1")
        ins.append("    i32.sub")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    br_if $brk_ts")
        ins.append(f"    local.get {end}")
        ins.append("    i32.const 1")
        ins.append("    i32.sub")
        ins.append(f"    local.set {end}")
        ins.append("    br $lp_ts")
        ins.append("  end")
        ins.append("end")

        # content_len = end - start
        ins.append(f"local.get {end}")
        ins.append(f"local.get {start}")
        ins.append("i32.sub")
        ins.append(f"local.set {content_len}")

        ins.append("block $done_pb")
        ins.append("block $err_pb")

        # -- Check length 4 → "true" (bytes: 116, 114, 117, 101) ---------
        ins.append(f"local.get {content_len}")
        ins.append("i32.const 4")
        ins.append("i32.eq")
        ins.append("if")
        # Check byte 0 = 't' (116)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.const 116")
        ins.append("  i32.eq")
        # Check byte 1 = 'r' (114)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=1")
        ins.append("  i32.const 114")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        # Check byte 2 = 'u' (117)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=2")
        ins.append("  i32.const 117")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        # Check byte 3 = 'e' (101)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=3")
        ins.append("  i32.const 101")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        ins.append("  if")
        # Matched "true" → Ok(1)
        ins.append("    i32.const 16")
        ins.append("    call $alloc")
        ins.append(f"    local.tee {out}")
        ins.append("    i32.const 0")
        ins.append("    i32.store")          # tag = 0 (Ok)
        ins.extend(["    " + i for i in gc_shadow_push(out)])
        ins.append(f"    local.get {out}")
        ins.append("    i32.const 1")
        ins.append("    i32.store offset=4") # Bool = true (1)
        ins.append("    br $done_pb")
        ins.append("  end")
        ins.append("end")

        # -- Check length 5 → "false" (bytes: 102, 97, 108, 115, 101) ----
        ins.append(f"local.get {content_len}")
        ins.append("i32.const 5")
        ins.append("i32.eq")
        ins.append("if")
        # Check byte 0 = 'f' (102)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.const 102")
        ins.append("  i32.eq")
        # Check byte 1 = 'a' (97)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=1")
        ins.append("  i32.const 97")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        # Check byte 2 = 'l' (108)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=2")
        ins.append("  i32.const 108")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        # Check byte 3 = 's' (115)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=3")
        ins.append("  i32.const 115")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        # Check byte 4 = 'e' (101)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {start}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=4")
        ins.append("  i32.const 101")
        ins.append("  i32.eq")
        ins.append("  i32.and")
        ins.append("  if")
        # Matched "false" → Ok(0)
        ins.append("    i32.const 16")
        ins.append("    call $alloc")
        ins.append(f"    local.tee {out}")
        ins.append("    i32.const 0")
        ins.append("    i32.store")          # tag = 0 (Ok)
        ins.extend(["    " + i for i in gc_shadow_push(out)])
        ins.append(f"    local.get {out}")
        ins.append("    i32.const 0")
        ins.append("    i32.store offset=4") # Bool = false (0)
        ins.append("    br $done_pb")
        ins.append("  end")
        ins.append("end")

        # -- Fall through to Err ------------------------------------------
        ins.append("br $err_pb")

        ins.append("end")  # block $err_pb

        # -- Err path: allocate 16 bytes, tag=1, String at offsets 4,8 ----
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")           # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_off}")
        ins.append("i32.store offset=4")  # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_len}")
        ins.append("i32.store offset=8")  # string len

        ins.append("end")  # block $done_pb

        ins.append(f"local.get {out}")
        return ins

    def _translate_parse_float64(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate parse_float64(s) → Result<Float64, String> (i32 ptr).

        Parses a decimal string (with optional sign and decimal point)
        to a 64-bit float.  Handles: optional leading spaces, optional
        sign (+/-), integer part, optional fractional part (.digits).
        Returns Ok(Float64) on success, Err(String) on failure.

        ADT layout (16 bytes):
          Ok(Float64): [tag=0 : i32] [pad 4] [value : f64]
          Err(String): [tag=1 : i32] [ptr : i32] [len : i32]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        sign = self.alloc_local("f64")
        int_part = self.alloc_local("f64")
        frac_part = self.alloc_local("f64")
        frac_div = self.alloc_local("f64")
        byte = self.alloc_local("i32")
        has_digit = self.alloc_local("i32")
        out = self.alloc_local("i32")

        # Intern error strings
        empty_off, empty_len = self.string_pool.intern("empty string")
        invalid_off, invalid_len = self.string_pool.intern(
            "invalid character",
        )

        ins: list[str] = []

        # Evaluate string → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Initialize
        ins.append("f64.const 1.0")
        ins.append(f"local.set {sign}")
        ins.append("f64.const 0.0")
        ins.append(f"local.set {int_part}")
        ins.append("f64.const 0.0")
        ins.append(f"local.set {frac_part}")
        ins.append("f64.const 1.0")
        ins.append(f"local.set {frac_div}")
        ins.append("i32.const 0")
        ins.append(f"local.set {idx}")
        ins.append("i32.const 0")
        ins.append(f"local.set {has_digit}")

        ins.append("block $done_pf")
        ins.append("block $err_pf")

        # -- Skip leading spaces -------------------------------------------
        ins.append("block $brk_sp")
        ins.append("  loop $lp_sp")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_sp")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    br_if $brk_sp")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_sp")
        ins.append("  end")
        ins.append("end")

        # -- Check for sign character (+/-) --------------------------------
        ins.append(f"local.get {idx}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {idx}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {byte}")
        # Check minus (45)
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 45")
        ins.append("  i32.eq")
        ins.append("  if")
        ins.append("    f64.const -1.0")
        ins.append(f"    local.set {sign}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("  else")
        # Check plus (43)
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 43")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("    end")
        ins.append("  end")
        ins.append("end")

        # -- Parse integer part (digits before decimal point) --------------
        ins.append("block $brk_int")
        ins.append("  loop $lp_int")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_int")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {byte}")
        # Break if not a digit (byte < 48 || byte > 57) — catches '.'
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.lt_u")
        ins.append("    br_if $brk_int")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 57")
        ins.append("    i32.gt_u")
        ins.append("    br_if $brk_int")
        # int_part = int_part * 10 + (byte - 48)
        ins.append(f"    local.get {int_part}")
        ins.append("    f64.const 10.0")
        ins.append("    f64.mul")
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 48")
        ins.append("    i32.sub")
        ins.append("    f64.convert_i32_u")
        ins.append("    f64.add")
        ins.append(f"    local.set {int_part}")
        # Mark that we saw a digit
        ins.append("    i32.const 1")
        ins.append(f"    local.set {has_digit}")
        # idx++
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_int")
        ins.append("  end")
        ins.append("end")

        # -- Check for decimal point (46) ----------------------------------
        ins.append(f"local.get {idx}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {idx}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {byte}")
        ins.append(f"  local.get {byte}")
        ins.append("  i32.const 46")
        ins.append("  i32.eq")
        ins.append("  if")
        # Skip the '.'
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        # Parse fractional digits
        ins.append("    block $brk_frac")
        ins.append("    loop $lp_frac")
        ins.append(f"      local.get {idx}")
        ins.append(f"      local.get {slen}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $brk_frac")
        ins.append(f"      local.get {ptr}")
        ins.append(f"      local.get {idx}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append(f"      local.set {byte}")
        # Space → break (trailing space)
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 32")
        ins.append("      i32.eq")
        ins.append("      br_if $brk_frac")
        # Not a digit → error (set has_digit=1 so error path
        # picks "invalid character" not "empty string")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 48")
        ins.append("      i32.lt_u")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 57")
        ins.append("      i32.gt_u")
        ins.append("      i32.or")
        ins.append("      if")
        ins.append(f"        i32.const 1")
        ins.append(f"        local.set {has_digit}")
        ins.append("        br $err_pf")
        ins.append("      end")
        # frac_div *= 10, frac_part = frac_part * 10 + (byte - 48)
        ins.append(f"      local.get {frac_div}")
        ins.append("      f64.const 10.0")
        ins.append("      f64.mul")
        ins.append(f"      local.set {frac_div}")
        ins.append(f"      local.get {frac_part}")
        ins.append("      f64.const 10.0")
        ins.append("      f64.mul")
        ins.append(f"      local.get {byte}")
        ins.append("      i32.const 48")
        ins.append("      i32.sub")
        ins.append("      f64.convert_i32_u")
        ins.append("      f64.add")
        ins.append(f"      local.set {frac_part}")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {has_digit}")
        # idx++
        ins.append(f"      local.get {idx}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {idx}")
        ins.append("      br $lp_frac")
        ins.append("    end")
        ins.append("    end")
        ins.append("  else")
        # Non-digit, non-dot after integer part → check if it's space
        ins.append(f"    local.get {byte}")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    if")
        ins.append(f"      i32.const 1")
        ins.append(f"      local.set {has_digit}")
        ins.append("      br $err_pf")
        ins.append("    end")
        ins.append("  end")
        ins.append("end")

        # -- Skip trailing spaces ------------------------------------------
        ins.append("block $brk_ts")
        ins.append("  loop $lp_ts")
        ins.append(f"    local.get {idx}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_ts")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 32")
        ins.append("    i32.ne")
        ins.append("    if")
        ins.append(f"      i32.const 1")
        ins.append(f"      local.set {has_digit}")
        ins.append("      br $err_pf")
        ins.append("    end")
        ins.append(f"    local.get {idx}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {idx}")
        ins.append("    br $lp_ts")
        ins.append("  end")
        ins.append("end")

        # -- After parsing: no digits seen → error
        ins.append(f"local.get {has_digit}")
        ins.append("i32.eqz")
        ins.append("br_if $err_pf")

        # -- Ok path: allocate 16 bytes, tag=0, f64 at offset 8 -----------
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")             # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        # Compute: sign * (int_part + frac_part / frac_div)
        ins.append(f"local.get {sign}")
        ins.append(f"local.get {int_part}")
        ins.append(f"local.get {frac_part}")
        ins.append(f"local.get {frac_div}")
        ins.append("f64.div")
        ins.append("f64.add")
        ins.append("f64.mul")
        ins.append("f64.store offset=8")    # Float64 value
        ins.append("br $done_pf")

        ins.append("end")  # block $err_pf

        # -- Err path: allocate 16 bytes, tag=1, String at offsets 4,8 ----
        ins.append(f"local.get {has_digit}")
        ins.append("i32.eqz")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {empty_off}")
        ins.append("else")
        ins.append(f"  i32.const {invalid_off}")
        ins.append("end")
        ins.append(f"local.set {idx}")   # reuse idx for err ptr
        ins.append(f"local.get {has_digit}")
        ins.append("i32.eqz")
        ins.append("if (result i32)")
        ins.append(f"  i32.const {empty_len}")
        ins.append("else")
        ins.append(f"  i32.const {invalid_len}")
        ins.append("end")
        ins.append(f"local.set {byte}")  # reuse byte for err len
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")             # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {idx}")
        ins.append("i32.store offset=4")    # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"local.get {byte}")
        ins.append("i32.store offset=8")    # string len

        ins.append("end")  # block $done_pf

        ins.append(f"local.get {out}")
        return ins
