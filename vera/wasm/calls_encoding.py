"""Encoding and URL built-in translation mixin for WasmContext.

Handles: base64_encode, base64_decode, url_encode, url_decode,
url_parse, url_join. All emit heap-allocating state machines in WAT.
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv, gc_shadow_push


class CallsEncodingMixin:
    """Methods for translating base64 and URL built-in functions."""

    # -----------------------------------------------------------------
    # Base64 encoding / decoding (RFC 4648)
    # -----------------------------------------------------------------

    def _translate_base64_encode(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate base64_encode(s) → String (i32_pair).

        Every 3 input bytes produce 4 output chars from the standard
        Base64 alphabet.  Remaining 1 or 2 bytes are padded with '='.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        # Intern the Base64 alphabet in the string pool so we can
        # look up output characters by 6-bit index.
        alpha_off, _ = self.string_pool.intern(
            "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
        )
        empty_off, empty_len = self.string_pool.intern("")

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        out_len = self.alloc_local("i32")
        i = self.alloc_local("i32")   # input index
        j = self.alloc_local("i32")   # output index
        b0 = self.alloc_local("i32")
        b1 = self.alloc_local("i32")
        b2 = self.alloc_local("i32")
        rem = self.alloc_local("i32")
        full = self.alloc_local("i32")  # slen - remainder

        ins: list[str] = []

        # Evaluate string arg → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Empty input → empty output
        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if (result i32 i32)")
        ins.append(f"  i32.const {empty_off}")
        ins.append(f"  i32.const {empty_len}")
        ins.append("else")

        # out_len = ((slen + 2) / 3) * 4
        ins.append(f"local.get {slen}")
        ins.append("i32.const 2")
        ins.append("i32.add")
        ins.append("i32.const 3")
        ins.append("i32.div_u")
        ins.append("i32.const 4")
        ins.append("i32.mul")
        ins.append(f"local.set {out_len}")

        # Allocate output buffer
        ins.append(f"local.get {out_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # rem = slen % 3; full = slen - rem
        ins.append(f"local.get {slen}")
        ins.append("i32.const 3")
        ins.append("i32.rem_u")
        ins.append(f"local.set {rem}")
        ins.append(f"local.get {slen}")
        ins.append(f"local.get {rem}")
        ins.append("i32.sub")
        ins.append(f"local.set {full}")

        # --- Main loop: process complete 3-byte groups ----------------
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {j}")
        ins.append("block $brk_e3")
        ins.append("  loop $lp_e3")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {full}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_e3")

        # Load b0, b1, b2
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {b0}")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=1")
        ins.append(f"    local.set {b1}")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=2")
        ins.append(f"    local.set {b2}")

        # Output char 0: alphabet[b0 >> 2]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {alpha_off}")
        ins.append(f"    local.get {b0}")
        ins.append("    i32.const 2")
        ins.append("    i32.shr_u")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=0")

        # Output char 1: alphabet[((b0 & 3) << 4) | (b1 >> 4)]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {alpha_off}")
        ins.append(f"    local.get {b0}")
        ins.append("    i32.const 3")
        ins.append("    i32.and")
        ins.append("    i32.const 4")
        ins.append("    i32.shl")
        ins.append(f"    local.get {b1}")
        ins.append("    i32.const 4")
        ins.append("    i32.shr_u")
        ins.append("    i32.or")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=1")

        # Output char 2: alphabet[((b1 & 0xF) << 2) | (b2 >> 6)]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {alpha_off}")
        ins.append(f"    local.get {b1}")
        ins.append("    i32.const 15")
        ins.append("    i32.and")
        ins.append("    i32.const 2")
        ins.append("    i32.shl")
        ins.append(f"    local.get {b2}")
        ins.append("    i32.const 6")
        ins.append("    i32.shr_u")
        ins.append("    i32.or")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=2")

        # Output char 3: alphabet[b2 & 0x3F]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {alpha_off}")
        ins.append(f"    local.get {b2}")
        ins.append("    i32.const 63")
        ins.append("    i32.and")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=3")

        # i += 3; j += 4
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 3")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.const 4")
        ins.append("    i32.add")
        ins.append(f"    local.set {j}")
        ins.append("    br $lp_e3")
        ins.append("  end")
        ins.append("end")

        # --- Handle remainder (1 or 2 bytes) --------------------------
        # rem == 1: 2 base64 chars + "=="
        ins.append(f"local.get {rem}")
        ins.append("i32.const 1")
        ins.append("i32.eq")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {i}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {b0}")
        # char 0: alphabet[b0 >> 2]
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {alpha_off}")
        ins.append(f"  local.get {b0}")
        ins.append("  i32.const 2")
        ins.append("  i32.shr_u")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.store8 offset=0")
        # char 1: alphabet[(b0 & 3) << 4]
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {alpha_off}")
        ins.append(f"  local.get {b0}")
        ins.append("  i32.const 3")
        ins.append("  i32.and")
        ins.append("  i32.const 4")
        ins.append("  i32.shl")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.store8 offset=1")
        # char 2-3: '=' (61)
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append("  i32.const 61")
        ins.append("  i32.store8 offset=2")
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append("  i32.const 61")
        ins.append("  i32.store8 offset=3")
        ins.append("end")

        # rem == 2: 3 base64 chars + "="
        ins.append(f"local.get {rem}")
        ins.append("i32.const 2")
        ins.append("i32.eq")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {i}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append(f"  local.set {b0}")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {i}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=1")
        ins.append(f"  local.set {b1}")
        # char 0: alphabet[b0 >> 2]
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {alpha_off}")
        ins.append(f"  local.get {b0}")
        ins.append("  i32.const 2")
        ins.append("  i32.shr_u")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.store8 offset=0")
        # char 1: alphabet[((b0 & 3) << 4) | (b1 >> 4)]
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {alpha_off}")
        ins.append(f"  local.get {b0}")
        ins.append("  i32.const 3")
        ins.append("  i32.and")
        ins.append("  i32.const 4")
        ins.append("  i32.shl")
        ins.append(f"  local.get {b1}")
        ins.append("  i32.const 4")
        ins.append("  i32.shr_u")
        ins.append("  i32.or")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.store8 offset=1")
        # char 2: alphabet[(b1 & 0xF) << 2]
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {alpha_off}")
        ins.append(f"  local.get {b1}")
        ins.append("  i32.const 15")
        ins.append("  i32.and")
        ins.append("  i32.const 2")
        ins.append("  i32.shl")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.store8 offset=2")
        # char 3: '='
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {j}")
        ins.append("  i32.add")
        ins.append("  i32.const 61")
        ins.append("  i32.store8 offset=3")
        ins.append("end")

        # Leave (dst, out_len) on the stack
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {out_len}")

        ins.append("end")  # else branch of empty check

        return ins

    def _translate_base64_decode(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate base64_decode(s) → Result<String, String> (i32 ptr).

        Decodes a standard Base64 string (RFC 4648).  Returns Err on
        invalid length (not a multiple of 4) or invalid characters.

        ADT layout (16 bytes):
          Ok(String):  [tag=0 : i32] [ptr : i32] [len : i32] [pad 4]
          Err(String): [tag=1 : i32] [ptr : i32] [len : i32] [pad 4]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        err_len_off, err_len_ln = self.string_pool.intern(
            "invalid base64 length"
        )
        err_chr_off, err_chr_ln = self.string_pool.intern("invalid base64")
        empty_off, empty_len = self.string_pool.intern("")

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        out = self.alloc_local("i32")    # Result ADT pointer
        dst = self.alloc_local("i32")    # decoded bytes pointer
        out_len = self.alloc_local("i32")
        pad = self.alloc_local("i32")    # padding count (0-2)
        i = self.alloc_local("i32")      # input index
        k = self.alloc_local("i32")      # output index
        ch = self.alloc_local("i32")     # current input byte
        val = self.alloc_local("i32")    # decoded 6-bit value
        acc = self.alloc_local("i32")    # accumulated 24-bit value
        gi = self.alloc_local("i32")     # group-internal index (0-3)

        ins: list[str] = []

        # Evaluate string arg → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        ins.append("block $done_bd")
        ins.append("block $err_chr_bd")
        ins.append("block $err_len_bd")

        # Validate: slen % 4 must be 0
        ins.append(f"local.get {slen}")
        ins.append("i32.const 3")
        ins.append("i32.and")        # slen & 3 (faster than rem_u)
        ins.append("i32.const 0")
        ins.append("i32.ne")
        ins.append("br_if $err_len_bd")

        # Empty input → Ok("")
        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if")
        ins.append("  i32.const 16")
        ins.append("  call $alloc")
        ins.append(f"  local.tee {out}")
        ins.append("  i32.const 0")
        ins.append("  i32.store")          # tag = 0 (Ok)
        ins.extend(["  " + x for x in gc_shadow_push(out)])
        ins.append(f"  local.get {out}")
        ins.append(f"  i32.const {empty_off}")
        ins.append("  i32.store offset=4") # ptr
        ins.append(f"  local.get {out}")
        ins.append(f"  i32.const {empty_len}")
        ins.append("  i32.store offset=8") # len
        ins.append("  br $done_bd")
        ins.append("end")

        # Count trailing '=' padding
        ins.append("i32.const 0")
        ins.append(f"local.set {pad}")
        # Check last byte: ptr + slen - 1
        ins.append(f"local.get {ptr}")
        ins.append(f"local.get {slen}")
        ins.append("i32.add")
        ins.append("i32.const 1")
        ins.append("i32.sub")
        ins.append("i32.load8_u offset=0")
        ins.append("i32.const 61")         # '='
        ins.append("i32.eq")
        ins.append("if")
        ins.append(f"  local.get {pad}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {pad}")
        # Check second-to-last byte: ptr + slen - 2
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {slen}")
        ins.append("  i32.add")
        ins.append("  i32.const 2")
        ins.append("  i32.sub")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.const 61")
        ins.append("  i32.eq")
        ins.append("  if")
        ins.append(f"    local.get {pad}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {pad}")
        ins.append("  end")
        ins.append("end")

        # out_len = (slen / 4) * 3 - pad
        ins.append(f"local.get {slen}")
        ins.append("i32.const 2")
        ins.append("i32.shr_u")           # slen / 4
        ins.append("i32.const 3")
        ins.append("i32.mul")
        ins.append(f"local.get {pad}")
        ins.append("i32.sub")
        ins.append(f"local.set {out_len}")

        # Allocate decoded buffer
        ins.append(f"local.get {out_len}")
        ins.append("i32.const 1")
        ins.append("i32.or")              # at least 1 byte for alloc
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # --- Decode loop: 4 input chars → 3 output bytes -------------
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {k}")

        ins.append("block $brk_dl")
        ins.append("  loop $lp_dl")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_dl")

        # Decode 4 chars into acc (24 bits)
        ins.append("    i32.const 0")
        ins.append(f"    local.set {acc}")
        ins.append("    i32.const 0")
        ins.append(f"    local.set {gi}")
        ins.append("    block $brk_g")
        ins.append("      loop $lp_g")
        ins.append(f"        local.get {gi}")
        ins.append("        i32.const 4")
        ins.append("        i32.ge_u")
        ins.append("        br_if $brk_g")

        # Load input char
        ins.append(f"        local.get {ptr}")
        ins.append(f"        local.get {i}")
        ins.append(f"        local.get {gi}")
        ins.append("        i32.add")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append(f"        local.set {ch}")

        # Decode char → 6-bit value via branching
        ins.append("        block $valid_d")
        ins.append("        block $invalid_d")

        # A-Z (65-90) → 0-25
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 65")
        ins.append("        i32.ge_u")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 90")
        ins.append("        i32.le_u")
        ins.append("        i32.and")
        ins.append("        if")
        ins.append(f"          local.get {ch}")
        ins.append("          i32.const 65")
        ins.append("          i32.sub")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # a-z (97-122) → 26-51
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 97")
        ins.append("        i32.ge_u")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 122")
        ins.append("        i32.le_u")
        ins.append("        i32.and")
        ins.append("        if")
        ins.append(f"          local.get {ch}")
        ins.append("          i32.const 97")
        ins.append("          i32.sub")
        ins.append("          i32.const 26")
        ins.append("          i32.add")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # 0-9 (48-57) → 52-61
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 48")
        ins.append("        i32.ge_u")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 57")
        ins.append("        i32.le_u")
        ins.append("        i32.and")
        ins.append("        if")
        ins.append(f"          local.get {ch}")
        ins.append("          i32.const 48")
        ins.append("          i32.sub")
        ins.append("          i32.const 52")
        ins.append("          i32.add")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # '+' (43) → 62
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 43")
        ins.append("        i32.eq")
        ins.append("        if")
        ins.append("          i32.const 62")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # '/' (47) → 63
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 47")
        ins.append("        i32.eq")
        ins.append("        if")
        ins.append("          i32.const 63")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # '=' (61) → 0 (padding)
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 61")
        ins.append("        i32.eq")
        ins.append("        if")
        ins.append("          i32.const 0")
        ins.append(f"          local.set {val}")
        ins.append("          br $valid_d")
        ins.append("        end")

        # Invalid character
        ins.append("        br $invalid_d")
        ins.append("        end")  # block $invalid_d
        ins.append("        br $err_chr_bd")

        ins.append("        end")  # block $valid_d

        # acc = (acc << 6) | val
        ins.append(f"        local.get {acc}")
        ins.append("        i32.const 6")
        ins.append("        i32.shl")
        ins.append(f"        local.get {val}")
        ins.append("        i32.or")
        ins.append(f"        local.set {acc}")

        # gi++
        ins.append(f"        local.get {gi}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {gi}")
        ins.append("        br $lp_g")
        ins.append("      end")  # loop $lp_g
        ins.append("    end")    # block $brk_g

        # Extract up to 3 bytes from acc and store if within out_len
        # Byte 0: (acc >> 16) & 0xFF
        ins.append(f"    local.get {k}")
        ins.append(f"    local.get {out_len}")
        ins.append("    i32.lt_u")
        ins.append("    if")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {k}")
        ins.append("      i32.add")
        ins.append(f"      local.get {acc}")
        ins.append("      i32.const 16")
        ins.append("      i32.shr_u")
        ins.append("      i32.const 255")
        ins.append("      i32.and")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {k}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {k}")
        ins.append("    end")

        # Byte 1: (acc >> 8) & 0xFF
        ins.append(f"    local.get {k}")
        ins.append(f"    local.get {out_len}")
        ins.append("    i32.lt_u")
        ins.append("    if")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {k}")
        ins.append("      i32.add")
        ins.append(f"      local.get {acc}")
        ins.append("      i32.const 8")
        ins.append("      i32.shr_u")
        ins.append("      i32.const 255")
        ins.append("      i32.and")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {k}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {k}")
        ins.append("    end")

        # Byte 2: acc & 0xFF
        ins.append(f"    local.get {k}")
        ins.append(f"    local.get {out_len}")
        ins.append("    i32.lt_u")
        ins.append("    if")
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {k}")
        ins.append("      i32.add")
        ins.append(f"      local.get {acc}")
        ins.append("      i32.const 255")
        ins.append("      i32.and")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {k}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {k}")
        ins.append("    end")

        # i += 4
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 4")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_dl")
        ins.append("  end")  # loop $lp_dl
        ins.append("end")    # block $brk_dl

        # --- Ok path: wrap (dst, out_len) in Result -------------------
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")            # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {dst}")
        ins.append("i32.store offset=4")   # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"local.get {out_len}")
        ins.append("i32.store offset=8")   # string len
        ins.append("br $done_bd")

        # --- Err path: invalid length ---------------------------------
        ins.append("end")  # block $err_len_bd
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")            # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_len_off}")
        ins.append("i32.store offset=4")
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_len_ln}")
        ins.append("i32.store offset=8")
        ins.append("br $done_bd")

        # --- Err path: invalid character ------------------------------
        ins.append("end")  # block $err_chr_bd
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")            # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_chr_off}")
        ins.append("i32.store offset=4")
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_chr_ln}")
        ins.append("i32.store offset=8")

        ins.append("end")  # block $done_bd

        ins.append(f"local.get {out}")
        return ins

    def _translate_url_encode(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate url_encode(s) → String (i32_pair).

        Percent-encodes all bytes except RFC 3986 unreserved characters:
        A-Z, a-z, 0-9, '-', '_', '.', '~'.
        Each reserved byte becomes %XX (uppercase hex).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        # Intern the hex digit alphabet for fast lookup
        hex_off, _ = self.string_pool.intern("0123456789ABCDEF")
        empty_off, empty_len = self.string_pool.intern("")

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        out_len = self.alloc_local("i32")
        i = self.alloc_local("i32")    # input index
        j = self.alloc_local("i32")    # output index
        ch = self.alloc_local("i32")   # current byte

        ins: list[str] = []

        # Evaluate string arg → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        # Empty input → empty output
        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if (result i32 i32)")
        ins.append(f"  i32.const {empty_off}")
        ins.append(f"  i32.const {empty_len}")
        ins.append("else")

        # First pass: count output length
        # Each byte is either 1 (unreserved) or 3 (%XX)
        ins.append("i32.const 0")
        ins.append(f"local.set {out_len}")
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("block $brk_cnt")
        ins.append("  loop $lp_cnt")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_cnt")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {ch}")

        # Check if unreserved: A-Z || a-z || 0-9 || '-' || '_' || '.' || '~'
        ins.append("    block $unreserved_c")
        # A-Z (65-90)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 65")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 90")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_c")
        # a-z (97-122)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 97")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 122")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_c")
        # 0-9 (48-57)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 48")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 57")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_c")
        # '-' (45)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 45")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_c")
        # '_' (95)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 95")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_c")
        # '.' (46)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 46")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_c")
        # '~' (126)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 126")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_c")

        # Reserved: out_len += 3
        ins.append(f"    local.get {out_len}")
        ins.append("    i32.const 3")
        ins.append("    i32.add")
        ins.append(f"    local.set {out_len}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_cnt")
        ins.append("    end")  # block $unreserved_c

        # Unreserved: out_len += 1
        ins.append(f"    local.get {out_len}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {out_len}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_cnt")
        ins.append("  end")  # loop
        ins.append("end")    # block $brk_cnt

        # Allocate output buffer
        ins.append(f"local.get {out_len}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # Second pass: write encoded output
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {j}")
        ins.append("block $brk_enc")
        ins.append("  loop $lp_enc")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_enc")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {ch}")

        # Check if unreserved (same logic as counting pass)
        ins.append("    block $unreserved_e")
        # A-Z
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 65")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 90")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_e")
        # a-z
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 97")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 122")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_e")
        # 0-9
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 48")
        ins.append("    i32.ge_u")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 57")
        ins.append("    i32.le_u")
        ins.append("    i32.and")
        ins.append("    br_if $unreserved_e")
        # '-'
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 45")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_e")
        # '_'
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 95")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_e")
        # '.'
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 46")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_e")
        # '~'
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 126")
        ins.append("    i32.eq")
        ins.append("    br_if $unreserved_e")

        # Reserved: write '%', hex_hi, hex_lo
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append("    i32.const 37")         # '%'
        ins.append("    i32.store8 offset=0")
        # High nibble: hex[ch >> 4]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {hex_off}")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 4")
        ins.append("    i32.shr_u")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=1")
        # Low nibble: hex[ch & 0xF]
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    i32.const {hex_off}")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 15")
        ins.append("    i32.and")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.store8 offset=2")
        # j += 3
        ins.append(f"    local.get {j}")
        ins.append("    i32.const 3")
        ins.append("    i32.add")
        ins.append(f"    local.set {j}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_enc")
        ins.append("    end")  # block $unreserved_e

        # Unreserved: copy byte directly
        ins.append(f"    local.get {dst}")
        ins.append(f"    local.get {j}")
        ins.append("    i32.add")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.store8 offset=0")
        # j += 1
        ins.append(f"    local.get {j}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {j}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $lp_enc")
        ins.append("  end")  # loop
        ins.append("end")    # block $brk_enc

        # Leave (dst, out_len) on the stack
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {out_len}")

        ins.append("end")  # else branch of empty check

        return ins

    def _translate_url_decode(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate url_decode(s) → Result<String, String> (i32 ptr).

        Decodes percent-encoded strings (RFC 3986).  Each %XX sequence
        is converted to the byte with that hex value.  Returns Err on
        invalid sequences (truncated %, invalid hex digits).

        ADT layout (16 bytes):
          Ok(String):  [tag=0 : i32] [ptr : i32] [len : i32] [pad 4]
          Err(String): [tag=1 : i32] [ptr : i32] [len : i32] [pad 4]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        err_off, err_ln = self.string_pool.intern("invalid percent-encoding")
        empty_off, empty_len = self.string_pool.intern("")

        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        out = self.alloc_local("i32")    # Result ADT pointer
        dst = self.alloc_local("i32")    # decoded bytes pointer
        out_len = self.alloc_local("i32")
        i = self.alloc_local("i32")      # input index
        k = self.alloc_local("i32")      # output index
        ch = self.alloc_local("i32")     # current byte
        hi = self.alloc_local("i32")     # high hex nibble value
        lo = self.alloc_local("i32")     # low hex nibble value

        ins: list[str] = []

        # Evaluate string arg → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        ins.append("block $done_ud")
        ins.append("block $err_ud")

        # Empty input → Ok("")
        ins.append(f"local.get {slen}")
        ins.append("i32.eqz")
        ins.append("if")
        ins.append("  i32.const 16")
        ins.append("  call $alloc")
        ins.append(f"  local.tee {out}")
        ins.append("  i32.const 0")
        ins.append("  i32.store")              # tag = 0 (Ok)
        ins.extend(["  " + x for x in gc_shadow_push(out)])
        ins.append(f"  local.get {out}")
        ins.append(f"  i32.const {empty_off}")
        ins.append("  i32.store offset=4")
        ins.append(f"  local.get {out}")
        ins.append(f"  i32.const {empty_len}")
        ins.append("  i32.store offset=8")
        ins.append("  br $done_ud")
        ins.append("end")

        # Allocate output buffer (at most slen bytes — decoding shrinks)
        ins.append(f"local.get {slen}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        # Decode loop
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const 0")
        ins.append(f"local.set {k}")

        ins.append("block $brk_dl")
        ins.append("  loop $lp_dl")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    br_if $brk_dl")

        # Load current byte
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {ch}")

        # Check if '%' (37)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 37")
        ins.append("    i32.eq")
        ins.append("    if")

        # Need at least 2 more bytes
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 2")
        ins.append("      i32.add")
        ins.append(f"      local.get {slen}")
        ins.append("      i32.ge_u")
        ins.append("      br_if $err_ud")

        # Decode high nibble (i+1)
        ins.append(f"      local.get {ptr}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=1")
        ins.append(f"      local.set {ch}")

        # Convert hex char to value (hi)
        ins.append("      block $hi_ok")
        ins.append("      block $hi_bad")
        # 0-9 (48-57) → 0-9
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 48")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 57")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 48")
        ins.append("        i32.sub")
        ins.append(f"        local.set {hi}")
        ins.append("        br $hi_ok")
        ins.append("      end")
        # A-F (65-70) → 10-15
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 65")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 70")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 55")
        ins.append("        i32.sub")
        ins.append(f"        local.set {hi}")
        ins.append("        br $hi_ok")
        ins.append("      end")
        # a-f (97-102) → 10-15
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 97")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 102")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 87")
        ins.append("        i32.sub")
        ins.append(f"        local.set {hi}")
        ins.append("        br $hi_ok")
        ins.append("      end")
        ins.append("      br $hi_bad")
        ins.append("      end")  # block $hi_bad
        ins.append("      br $err_ud")
        ins.append("      end")  # block $hi_ok

        # Decode low nibble (i+2)
        ins.append(f"      local.get {ptr}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=2")
        ins.append(f"      local.set {ch}")

        # Convert hex char to value (lo)
        ins.append("      block $lo_ok")
        ins.append("      block $lo_bad")
        # 0-9
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 48")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 57")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 48")
        ins.append("        i32.sub")
        ins.append(f"        local.set {lo}")
        ins.append("        br $lo_ok")
        ins.append("      end")
        # A-F
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 65")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 70")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 55")
        ins.append("        i32.sub")
        ins.append(f"        local.set {lo}")
        ins.append("        br $lo_ok")
        ins.append("      end")
        # a-f
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 97")
        ins.append("      i32.ge_u")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 102")
        ins.append("      i32.le_u")
        ins.append("      i32.and")
        ins.append("      if")
        ins.append(f"        local.get {ch}")
        ins.append("        i32.const 87")
        ins.append("        i32.sub")
        ins.append(f"        local.set {lo}")
        ins.append("        br $lo_ok")
        ins.append("      end")
        ins.append("      br $lo_bad")
        ins.append("      end")  # block $lo_bad
        ins.append("      br $err_ud")
        ins.append("      end")  # block $lo_ok

        # Store decoded byte: (hi << 4) | lo
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {k}")
        ins.append("      i32.add")
        ins.append(f"      local.get {hi}")
        ins.append("      i32.const 4")
        ins.append("      i32.shl")
        ins.append(f"      local.get {lo}")
        ins.append("      i32.or")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {k}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {k}")
        # i += 3
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 3")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")

        ins.append("    else")

        # Not '%': copy byte directly
        ins.append(f"      local.get {dst}")
        ins.append(f"      local.get {k}")
        ins.append("      i32.add")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.store8 offset=0")
        ins.append(f"      local.get {k}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {k}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")

        ins.append("    end")  # if '%'

        ins.append("    br $lp_dl")
        ins.append("  end")  # loop
        ins.append("end")    # block $brk_dl

        # --- Ok path ---
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")                # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {dst}")
        ins.append("i32.store offset=4")       # string ptr
        ins.append(f"local.get {out}")
        ins.append(f"local.get {k}")
        ins.append("i32.store offset=8")       # string len
        ins.append("br $done_ud")

        # --- Err path ---
        ins.append("end")  # block $err_ud
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")                # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_off}")
        ins.append("i32.store offset=4")
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_ln}")
        ins.append("i32.store offset=8")

        ins.append("end")  # block $done_ud

        ins.append(f"local.get {out}")
        return ins

    def _translate_url_parse(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate url_parse(s) → Result<UrlParts, String> (i32 ptr).

        RFC 3986 simplified URL decomposition.  Scans the input for
        delimiters (:, ://, /, ?, #) and records each component as a
        substring of the original input (no copies needed for scheme,
        authority, path, query, fragment).

        UrlParts layout (48 bytes):
          [tag=0     : i32 @ 0 ]
          [scheme_ptr: i32 @ 4 ] [scheme_len: i32 @ 8 ]
          [auth_ptr  : i32 @ 12] [auth_len  : i32 @ 16]
          [path_ptr  : i32 @ 20] [path_len  : i32 @ 24]
          [query_ptr : i32 @ 28] [query_len : i32 @ 32]
          [frag_ptr  : i32 @ 36] [frag_len  : i32 @ 40]
          [pad 4     @ 44]

        Result layout (16 bytes):
          Ok(UrlParts):  [tag=0 : i32] [urlparts_ptr : i32] [pad 8]
          Err(String):   [tag=1 : i32] [ptr : i32] [len : i32] [pad 4]
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        err_off, err_ln = self.string_pool.intern("missing scheme")
        empty_off, empty_len = self.string_pool.intern("")

        # Input string
        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        # Scanning index
        i = self.alloc_local("i32")
        ch = self.alloc_local("i32")
        # Component boundaries (offsets relative to ptr)
        colon_pos = self.alloc_local("i32")   # position of first ':'
        auth_start = self.alloc_local("i32")  # start of authority
        auth_end = self.alloc_local("i32")    # end of authority
        path_start = self.alloc_local("i32")  # start of path
        path_end = self.alloc_local("i32")    # end of path
        query_start = self.alloc_local("i32")  # start of query (after '?')
        query_end = self.alloc_local("i32")    # end of query
        frag_start = self.alloc_local("i32")   # start of fragment (after '#')
        has_auth = self.alloc_local("i32")     # bool: found ://
        has_query = self.alloc_local("i32")    # bool: found ?
        has_frag = self.alloc_local("i32")     # bool: found #
        # Output pointers
        up = self.alloc_local("i32")   # UrlParts heap pointer
        out = self.alloc_local("i32")  # Result heap pointer

        ins: list[str] = []

        # Evaluate string arg → (ptr, len)
        ins.extend(arg_instrs)
        ins.append(f"local.set {slen}")
        ins.append(f"local.set {ptr}")

        ins.append("block $done_up")
        ins.append("block $err_up")

        # ---- Step 1: Find colon (scheme delimiter) ----
        # Scan for first ':'
        ins.append("i32.const 0")
        ins.append(f"local.set {i}")
        ins.append("i32.const -1")
        ins.append(f"local.set {colon_pos}")

        ins.append("block $found_colon")
        ins.append("  loop $scan_colon")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    if")
        # No colon found → Err
        ins.append("      br $err_up")
        ins.append("    end")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {ch}")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 58")   # ':'
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.set {colon_pos}")
        ins.append("      br $found_colon")
        ins.append("    end")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $scan_colon")
        ins.append("  end")  # loop
        ins.append("end")    # block $found_colon

        # scheme is input[0..colon_pos]
        # Now check if :// follows the colon

        # ---- Step 2: Check for :// (authority indicator) ----
        ins.append("i32.const 0")
        ins.append(f"local.set {has_auth}")

        # Need colon_pos + 3 <= slen  and  input[colon_pos+1] == '/'
        # and input[colon_pos+2] == '/'
        ins.append(f"local.get {colon_pos}")
        ins.append("i32.const 3")
        ins.append("i32.add")
        ins.append(f"local.get {slen}")
        ins.append("i32.le_u")
        ins.append("if")
        # Check input[colon_pos+1] == '/' (47)
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {colon_pos}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=1")
        ins.append("  i32.const 47")
        ins.append("  i32.eq")
        ins.append("  if")
        # Check input[colon_pos+2] == '/' (47)
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {colon_pos}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=2")
        ins.append("    i32.const 47")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {has_auth}")
        ins.append("    end")
        ins.append("  end")
        ins.append("end")

        # ---- Step 3: Determine authority, path, query, fragment ----
        # Set cursor position after scheme
        ins.append("i32.const 0")
        ins.append(f"local.set {has_query}")
        ins.append("i32.const 0")
        ins.append(f"local.set {has_frag}")

        # If has_auth: cursor = colon_pos + 3 (after ://)
        # Else: cursor = colon_pos + 1 (after :)
        ins.append(f"local.get {has_auth}")
        ins.append("if")
        ins.append(f"  local.get {colon_pos}")
        ins.append("  i32.const 3")
        ins.append("  i32.add")
        ins.append(f"  local.set {auth_start}")
        ins.append("else")
        # No authority — set auth to empty
        ins.append(f"  local.get {colon_pos}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {auth_start}")
        ins.append("end")

        # auth_end = auth_start initially (will scan to find end)
        ins.append(f"local.get {auth_start}")
        ins.append(f"local.set {auth_end}")

        # If has_auth: scan authority until /, ?, #, or end
        ins.append(f"local.get {has_auth}")
        ins.append("if")
        ins.append(f"  local.get {auth_start}")
        ins.append(f"  local.set {i}")
        ins.append("  block $auth_done")
        ins.append("    loop $scan_auth")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.get {slen}")
        ins.append("      i32.ge_u")
        ins.append("      if")
        ins.append(f"        local.get {i}")
        ins.append(f"        local.set {auth_end}")
        ins.append("        br $auth_done")
        ins.append("      end")
        ins.append(f"      local.get {ptr}")
        ins.append(f"      local.get {i}")
        ins.append("      i32.add")
        ins.append("      i32.load8_u offset=0")
        ins.append(f"      local.set {ch}")
        # Check for / (47), ? (63), # (35)
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 47")
        ins.append("      i32.eq")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 63")
        ins.append("      i32.eq")
        ins.append("      i32.or")
        ins.append(f"      local.get {ch}")
        ins.append("      i32.const 35")
        ins.append("      i32.eq")
        ins.append("      i32.or")
        ins.append("      if")
        ins.append(f"        local.get {i}")
        ins.append(f"        local.set {auth_end}")
        ins.append("        br $auth_done")
        ins.append("      end")
        ins.append(f"      local.get {i}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {i}")
        ins.append("      br $scan_auth")
        ins.append("    end")  # loop
        ins.append("  end")    # block $auth_done
        ins.append("else")
        # No authority: auth_end = auth_start (empty)
        ins.append(f"  local.get {auth_start}")
        ins.append(f"  local.set {auth_end}")
        ins.append("end")

        # ---- Path: from auth_end until ? or # or end ----
        ins.append(f"local.get {auth_end}")
        ins.append(f"local.set {path_start}")
        ins.append(f"local.get {auth_end}")
        ins.append(f"local.set {i}")

        ins.append("block $path_done")
        ins.append("  loop $scan_path")
        ins.append(f"    local.get {i}")
        ins.append(f"    local.get {slen}")
        ins.append("    i32.ge_u")
        ins.append("    if")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.set {path_end}")
        ins.append("      br $path_done")
        ins.append("    end")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {i}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append(f"    local.set {ch}")
        # Check for ? (63) or # (35)
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 63")
        ins.append("    i32.eq")
        ins.append(f"    local.get {ch}")
        ins.append("    i32.const 35")
        ins.append("    i32.eq")
        ins.append("    i32.or")
        ins.append("    if")
        ins.append(f"      local.get {i}")
        ins.append(f"      local.set {path_end}")
        ins.append("      br $path_done")
        ins.append("    end")
        ins.append(f"    local.get {i}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {i}")
        ins.append("    br $scan_path")
        ins.append("  end")  # loop
        ins.append("end")    # block $path_done

        # ---- Query: if input[path_end] == '?', scan until # or end ----
        ins.append(f"local.get {path_end}")
        ins.append(f"local.get {slen}")
        ins.append("i32.lt_u")
        ins.append("if")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {path_end}")
        ins.append("  i32.add")
        ins.append("  i32.load8_u offset=0")
        ins.append("  i32.const 63")   # '?'
        ins.append("  i32.eq")
        ins.append("  if")
        ins.append("    i32.const 1")
        ins.append(f"    local.set {has_query}")
        ins.append(f"    local.get {path_end}")
        ins.append("    i32.const 1")
        ins.append("    i32.add")
        ins.append(f"    local.set {query_start}")
        # Scan query until # or end
        ins.append(f"    local.get {query_start}")
        ins.append(f"    local.set {i}")
        ins.append("    block $query_done")
        ins.append("      loop $scan_query")
        ins.append(f"        local.get {i}")
        ins.append(f"        local.get {slen}")
        ins.append("        i32.ge_u")
        ins.append("        if")
        ins.append(f"          local.get {i}")
        ins.append(f"          local.set {query_end}")
        ins.append("          br $query_done")
        ins.append("        end")
        ins.append(f"        local.get {ptr}")
        ins.append(f"        local.get {i}")
        ins.append("        i32.add")
        ins.append("        i32.load8_u offset=0")
        ins.append("        i32.const 35")   # '#'
        ins.append("        i32.eq")
        ins.append("        if")
        ins.append(f"          local.get {i}")
        ins.append(f"          local.set {query_end}")
        ins.append("          br $query_done")
        ins.append("        end")
        ins.append(f"        local.get {i}")
        ins.append("        i32.const 1")
        ins.append("        i32.add")
        ins.append(f"        local.set {i}")
        ins.append("        br $scan_query")
        ins.append("      end")  # loop
        ins.append("    end")    # block $query_done
        ins.append("  end")  # if '?'
        ins.append("end")   # if path_end < slen

        # ---- Fragment: check after query (or after path if no query) ----
        # The fragment start is wherever we stopped + 1 if we see '#'
        # We need to check: if has_query, check at query_end; else at path_end
        ins.append(f"local.get {has_query}")
        ins.append("if")
        # Check if query_end < slen and input[query_end] == '#'
        ins.append(f"  local.get {query_end}")
        ins.append(f"  local.get {slen}")
        ins.append("  i32.lt_u")
        ins.append("  if")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {query_end}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 35")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {has_frag}")
        ins.append(f"      local.get {query_end}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {frag_start}")
        ins.append("    end")
        ins.append("  end")
        ins.append("else")
        # No query — check at path_end for '#'
        ins.append(f"  local.get {path_end}")
        ins.append(f"  local.get {slen}")
        ins.append("  i32.lt_u")
        ins.append("  if")
        ins.append(f"    local.get {ptr}")
        ins.append(f"    local.get {path_end}")
        ins.append("    i32.add")
        ins.append("    i32.load8_u offset=0")
        ins.append("    i32.const 35")
        ins.append("    i32.eq")
        ins.append("    if")
        ins.append("      i32.const 1")
        ins.append(f"      local.set {has_frag}")
        ins.append(f"      local.get {path_end}")
        ins.append("      i32.const 1")
        ins.append("      i32.add")
        ins.append(f"      local.set {frag_start}")
        ins.append("    end")
        ins.append("  end")
        ins.append("end")

        # ---- Step 4: Allocate UrlParts (48 bytes) ----
        ins.append("i32.const 48")
        ins.append("call $alloc")
        ins.append(f"local.tee {up}")
        ins.append("i32.const 0")
        ins.append("i32.store")              # tag = 0 (UrlParts constructor)
        ins.extend(gc_shadow_push(up))

        # Scheme: input[0..colon_pos]
        ins.append(f"local.get {up}")
        ins.append(f"local.get {ptr}")
        ins.append("i32.store offset=4")     # scheme_ptr
        ins.append(f"local.get {up}")
        ins.append(f"local.get {colon_pos}")
        ins.append("i32.store offset=8")     # scheme_len

        # Authority: input[auth_start..auth_end]  (empty if no ://)
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_auth}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {auth_start}")
        ins.append("  i32.add")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append("i32.store offset=12")    # auth_ptr
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_auth}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {auth_end}")
        ins.append(f"  local.get {auth_start}")
        ins.append("  i32.sub")
        ins.append("else")
        ins.append(f"  i32.const {empty_len}")
        ins.append("end")
        ins.append("i32.store offset=16")    # auth_len

        # Path: input[path_start..path_end]
        ins.append(f"local.get {up}")
        ins.append(f"local.get {path_start}")
        ins.append(f"local.get {path_end}")
        ins.append("i32.lt_u")
        ins.append("if (result i32)")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {path_start}")
        ins.append("  i32.add")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append("i32.store offset=20")    # path_ptr
        ins.append(f"local.get {up}")
        ins.append(f"local.get {path_end}")
        ins.append(f"local.get {path_start}")
        ins.append("i32.sub")
        ins.append("i32.store offset=24")    # path_len

        # Query: input[query_start..query_end]  (empty if no ?)
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_query}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {query_start}")
        ins.append("  i32.add")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append("i32.store offset=28")    # query_ptr
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_query}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {query_end}")
        ins.append(f"  local.get {query_start}")
        ins.append("  i32.sub")
        ins.append("else")
        ins.append(f"  i32.const {empty_len}")
        ins.append("end")
        ins.append("i32.store offset=32")    # query_len

        # Fragment: input[frag_start..slen]  (empty if no #)
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_frag}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {ptr}")
        ins.append(f"  local.get {frag_start}")
        ins.append("  i32.add")
        ins.append("else")
        ins.append(f"  i32.const {empty_off}")
        ins.append("end")
        ins.append("i32.store offset=36")    # frag_ptr
        ins.append(f"local.get {up}")
        ins.append(f"local.get {has_frag}")
        ins.append("if (result i32)")
        ins.append(f"  local.get {slen}")
        ins.append(f"  local.get {frag_start}")
        ins.append("  i32.sub")
        ins.append("else")
        ins.append(f"  i32.const {empty_len}")
        ins.append("end")
        ins.append("i32.store offset=40")    # frag_len

        # ---- Step 5: Allocate Result (16 bytes), Ok(UrlParts) ----
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 0")
        ins.append("i32.store")              # tag = 0 (Ok)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"local.get {up}")
        ins.append("i32.store offset=4")     # UrlParts ptr
        ins.append("br $done_up")

        # ---- Err path ----
        ins.append("end")  # block $err_up
        ins.append("i32.const 16")
        ins.append("call $alloc")
        ins.append(f"local.tee {out}")
        ins.append("i32.const 1")
        ins.append("i32.store")              # tag = 1 (Err)
        ins.extend(gc_shadow_push(out))
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_off}")
        ins.append("i32.store offset=4")
        ins.append(f"local.get {out}")
        ins.append(f"i32.const {err_ln}")
        ins.append("i32.store offset=8")

        ins.append("end")  # block $done_up

        ins.append(f"local.get {out}")
        return ins

    def _translate_url_join(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate url_join(parts) → String (i32_pair).

        Takes a UrlParts heap pointer and reassembles a URL string.
        Components: scheme://authority/path?query#fragment
        Empty components are omitted (including their delimiters).

        The argument is an i32 (heap pointer to UrlParts struct).
        Returns i32_pair (ptr, len) on the stack.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        self.needs_alloc = True

        # Intern "://" for the scheme separator
        sep_off, sep_len = self.string_pool.intern("://")
        q_off, _ = self.string_pool.intern("?")
        h_off, _ = self.string_pool.intern("#")

        # UrlParts pointer
        up = self.alloc_local("i32")
        # Component locals (5 pairs: ptr, len)
        s_ptr = self.alloc_local("i32")    # scheme
        s_len = self.alloc_local("i32")
        a_ptr = self.alloc_local("i32")    # authority
        a_len = self.alloc_local("i32")
        p_ptr = self.alloc_local("i32")    # path
        p_len = self.alloc_local("i32")
        q_ptr = self.alloc_local("i32")    # query
        q_len = self.alloc_local("i32")
        f_ptr = self.alloc_local("i32")    # fragment
        f_len = self.alloc_local("i32")
        # Output
        total = self.alloc_local("i32")
        dst = self.alloc_local("i32")
        k = self.alloc_local("i32")        # write cursor

        ins: list[str] = []

        # Evaluate arg → i32 (UrlParts heap pointer)
        ins.extend(arg_instrs)
        ins.append(f"local.set {up}")

        # Load all 5 String fields (each is ptr + len at known offsets)
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=4")
        ins.append(f"local.set {s_ptr}")
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=8")
        ins.append(f"local.set {s_len}")

        ins.append(f"local.get {up}")
        ins.append("i32.load offset=12")
        ins.append(f"local.set {a_ptr}")
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=16")
        ins.append(f"local.set {a_len}")

        ins.append(f"local.get {up}")
        ins.append("i32.load offset=20")
        ins.append(f"local.set {p_ptr}")
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=24")
        ins.append(f"local.set {p_len}")

        ins.append(f"local.get {up}")
        ins.append("i32.load offset=28")
        ins.append(f"local.set {q_ptr}")
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=32")
        ins.append(f"local.set {q_len}")

        ins.append(f"local.get {up}")
        ins.append("i32.load offset=36")
        ins.append(f"local.set {f_ptr}")
        ins.append(f"local.get {up}")
        ins.append("i32.load offset=40")
        ins.append(f"local.set {f_len}")

        # ---- Pass 1: compute total output length ----
        # total = scheme_len + path_len
        ins.append(f"local.get {s_len}")
        ins.append(f"local.get {p_len}")
        ins.append("i32.add")
        ins.append(f"local.set {total}")
        # If scheme_len > 0: total += 3 (for "://")
        ins.append(f"local.get {s_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {total}")
        ins.append("  i32.const 3")
        ins.append("  i32.add")
        ins.append(f"  local.set {total}")
        ins.append("end")
        # total += auth_len
        ins.append(f"local.get {total}")
        ins.append(f"local.get {a_len}")
        ins.append("i32.add")
        ins.append(f"local.set {total}")
        # If query_len > 0: total += 1 + query_len
        ins.append(f"local.get {q_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {total}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.get {q_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {total}")
        ins.append("end")
        # If frag_len > 0: total += 1 + frag_len
        ins.append(f"local.get {f_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {total}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.get {f_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {total}")
        ins.append("end")

        # If total == 0: skip allocation, use empty string
        empty_off2, empty_len2 = self.string_pool.intern("")
        ins.append(f"local.get {total}")
        ins.append("i32.eqz")
        ins.append("if")
        ins.append(f"  i32.const {empty_off2}")
        ins.append(f"  local.set {dst}")
        ins.append("end")

        ins.append("block $uj_done")
        ins.append(f"local.get {total}")
        ins.append("i32.eqz")
        ins.append("br_if $uj_done")

        # ---- Pass 2: allocate and write ----
        ins.append(f"local.get {total}")
        ins.append("call $alloc")
        ins.append(f"local.set {dst}")
        ins.extend(gc_shadow_push(dst))

        ins.append("i32.const 0")
        ins.append(f"local.set {k}")

        # If scheme non-empty: copy scheme, write "://"
        ins.append(f"local.get {s_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        # memory.copy(dst+k, s_ptr, s_len)
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  local.get {s_ptr}")
        ins.append(f"  local.get {s_len}")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append(f"  local.get {s_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        # Write "://" (3 bytes from string pool)
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  i32.const {sep_off}")
        ins.append("  i32.const 3")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append("  i32.const 3")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        ins.append("end")

        # Copy authority (even if empty — zero-length copy is a no-op)
        ins.append(f"local.get {a_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  local.get {a_ptr}")
        ins.append(f"  local.get {a_len}")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append(f"  local.get {a_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        ins.append("end")

        # Copy path
        ins.append(f"local.get {p_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  local.get {p_ptr}")
        ins.append(f"  local.get {p_len}")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append(f"  local.get {p_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        ins.append("end")

        # If query non-empty: write "?" + query
        ins.append(f"local.get {q_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        # Write '?' (1 byte)
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append("  i32.const 63")   # '?'
        ins.append("  i32.store8 offset=0")
        ins.append(f"  local.get {k}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        # Copy query
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  local.get {q_ptr}")
        ins.append(f"  local.get {q_len}")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append(f"  local.get {q_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        ins.append("end")

        # If fragment non-empty: write "#" + fragment
        ins.append(f"local.get {f_len}")
        ins.append("i32.const 0")
        ins.append("i32.gt_u")
        ins.append("if")
        # Write '#' (1 byte)
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append("  i32.const 35")   # '#'
        ins.append("  i32.store8 offset=0")
        ins.append(f"  local.get {k}")
        ins.append("  i32.const 1")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        # Copy fragment
        ins.append(f"  local.get {dst}")
        ins.append(f"  local.get {k}")
        ins.append("  i32.add")
        ins.append(f"  local.get {f_ptr}")
        ins.append(f"  local.get {f_len}")
        ins.append("  memory.copy")
        ins.append(f"  local.get {k}")
        ins.append(f"  local.get {f_len}")
        ins.append("  i32.add")
        ins.append(f"  local.set {k}")
        ins.append("end")

        ins.append("end")  # block $uj_done

        # Return (dst, total) as i32_pair
        ins.append(f"local.get {dst}")
        ins.append(f"local.get {total}")
        return ins
