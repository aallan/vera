"""Container type translation mixin for WasmContext.

Handles the three opaque-handle types: Map<K,V>, Set<E>, and Decimal.
All three use the host-import pattern with lazy registration of
type-specialised imports (e.g. ``map_insert$ks_vi`` for String key /
Int value).

#573 (phase 1 — Map only): Map host functions return raw i32 handles
(indices into ``_map_store`` in ``vera/codegen/api.py``).  Each
Map-returning call-site now wraps that handle in an 8-byte ADT on
the GC heap (tag at offset 0, handle at offset 4) and registers the
wrapper with ``$register_wrapper`` so Phase 2c of ``$gc_collect``
can fire ``host_decref_handle`` when the wrapper becomes
unreachable.  Map-consuming call-sites unwrap by loading the handle
back via ``i32.load offset=4`` before the host call.  Set and
Decimal still use the raw-handle scheme; they migrate in their own
follow-ups so each domain's wrapping decisions can be reviewed
independently.
"""

from __future__ import annotations

from vera import ast
from vera.skip import CodegenSkip
from vera.wasm.helpers import WasmSlotEnv, gc_shadow_push

# #573: kind discriminators passed to ``host_decref_handle`` and
# stored in the wrap-table side index.  Must stay in sync with the
# Python dispatcher in ``vera/codegen/api.py`` and the JS dispatcher
# in ``vera/browser/runtime.mjs``.
_WRAP_KIND_MAP = 1
_WRAP_KIND_SET = 2
_WRAP_KIND_DECIMAL = 3

# #573: wrapper-ADT tag values stored at wrapper body offset 0.  Not
# strictly required for correctness — the side table is the source
# of truth for "is this object a wrapper" — but stored anyway as a
# debugging aid (a heap dump will show e.g. MAP_HANDLE_TAG at the
# body's first word).  Chosen well outside the user-ADT tag range
# (which starts at 0 and increments per constructor).
_MAP_HANDLE_TAG = 0xFEEDC001
_SET_HANDLE_TAG = 0xFEEDC002
_DECIMAL_HANDLE_TAG = 0xFEEDC003

_KIND_TO_TAG: dict[int, int] = {
    _WRAP_KIND_MAP: _MAP_HANDLE_TAG,
    _WRAP_KIND_SET: _SET_HANDLE_TAG,
    _WRAP_KIND_DECIMAL: _DECIMAL_HANDLE_TAG,
}

# #573 / #695 / #705: wrapper ADT body size.  Layout:
#   +0  tag (i32)                                     [#573]
#   +4  handle | 0x80000000 (i32, bit-31 tagged)      [#578]
#   +8  bucket_ptr (i32, heap pointer or 0)           [#695/#705]
#
# ``bucket_ptr`` is non-zero for Map / Set wrappers whose host-side
# stores hold heap-pointer values; it points to a WASM-resident
# bucket array making those values reachable to the conservative
# scan.  Decimal wrappers and empty Map / Set wrappers leave it 0.
# Must agree with ``_WRAPPER_BODY_SIZE`` in ``vera/codegen/api.py``.
_WRAPPER_BODY_SIZE = 12


class CallsContainersMixin:
    """Methods for translating Map, Set, and Decimal built-in functions."""

    # -----------------------------------------------------------------
    # #573: handle wrap / unwrap helpers (Map only — phase 1)
    # -----------------------------------------------------------------

    def _emit_wrap_handle(
        self, kind: int, handle_temp: int, wrapper_temp: int,
    ) -> list[str]:
        """Emit WAT to wrap a host-handle i32 into a heap ADT wrapper.

        Pre-condition: ``handle_temp`` holds the raw i32 handle
        returned by a host helper.

        Post-condition: ``wrapper_temp`` holds the wrapper-ADT
        pointer (a GC-managed i32 heap pointer).  The wrapper has
        been registered with the wrap table so Phase 2c of
        ``$gc_collect`` will fire ``host_decref_handle(kind,
        handle)`` when the wrapper becomes unreachable.

        ``kind`` is one of the ``_WRAP_KIND_*`` constants.
        Wrapper body layout:

        ::

            offset 0: tag (i32) — magic value (debugging aid)
            offset 4: handle (i32) — host-handle index

        Caller is responsible for leaving ``wrapper_temp`` (or a
        ``local.get`` of it) on the operand stack as the call's
        result, so the slot env / let-binding sees the wrapper
        pointer rather than the raw handle.
        """
        tag_value = _KIND_TO_TAG.get(kind)
        if tag_value is None:  # pragma: no cover
            raise NotImplementedError(
                f"#573: unknown wrap kind {kind}",
            )
        # Allocate 8-byte body.  $alloc returns the body pointer
        # (header lives at body_ptr - 4).
        seq = [
            f"i32.const {_WRAPPER_BODY_SIZE}",
            "call $alloc",
            f"local.tee {wrapper_temp}",
            # Store tag at body[0].
            f"i32.const {tag_value}",
            "i32.store offset=0",
            # Store TAGGED handle at body[4].  #578: OR with
            # 0x80000000 so the in-heap field cannot be mistaken
            # for a heap pointer by the conservative GC scan.
            # The heap-ceiling guard in $alloc enforces
            # heap_ptr < 0x80000000, so a value with bit 31 set
            # is guaranteed outside the heap-range check.  The
            # raw handle is recovered by ANDing with 0x7FFFFFFF
            # at the unwrap site.  Note: ``$register_wrapper``
            # below still receives the RAW handle — the wrap
            # table needs it for ``host_decref_handle`` calls
            # during Phase 2c.
            f"local.get {wrapper_temp}",
            f"local.get {handle_temp}",
            "i32.const 0x80000000",
            "i32.or",
            "i32.store offset=4",
            # #695/#705: write 0 at +8 (default bucket_ptr).  Map/Set
            # wrappers get this overwritten by attach_bucket_to_wrapper
            # below; Decimal wrappers keep it at 0.
            f"local.get {wrapper_temp}",
            "i32.const 0",
            "i32.store offset=8",
            # Register with wrap table: $register_wrapper(ptr, kind, handle).
            f"local.get {wrapper_temp}",
            f"i32.const {kind}",
            f"local.get {handle_temp}",
            "call $register_wrapper",
        ]
        # #573: shadow-push the wrapper so any subsequent
        # allocation within the same function frame can't sweep
        # it.  Without this, code like
        # ``decimal_add(decimal_from_int(a), decimal_from_int(b))``
        # is unsafe — the inner ``decimal_from_int`` returns a
        # wrapper which sits on the operand stack while the
        # second ``decimal_from_int`` invokes ``$alloc``; if GC
        # fires there, the first wrapper is unmarked (it's on
        # the operand stack and in a WASM local but neither is
        # GC-visible) and Phase 2c evicts its host-store entry.
        # The function epilogue's ``gc_sp`` restore clears
        # these per-call pushes, so the shadow stack doesn't
        # grow unbounded across iterations of an enclosing
        # ``array_fold``.
        seq.extend(gc_shadow_push(wrapper_temp))
        # #695/#705: populate the wrapper's bucket_ptr field (+8) by
        # mirroring the host-store contents into a WASM-resident
        # bucket array.  Must come AFTER the shadow-push above so
        # the wrapper itself stays rooted during the bucket
        # allocation's possible sub-GCs.  No-op for Decimal
        # wrappers (kind=3).
        seq.extend([
            f"local.get {wrapper_temp}",
            f"i32.const {kind}",
            f"local.get {handle_temp}",
            "call $vera.attach_bucket_to_wrapper",
        ])
        # Leave the wrapper pointer on the stack as the call result.
        seq.append(f"local.get {wrapper_temp}")
        return seq

    def _emit_unwrap_handle(self) -> list[str]:
        """Emit WAT to unwrap a wrapper-ADT pointer to its raw handle.

        Consumes one i32 from the operand stack (the wrapper
        pointer) and produces one i32 (the raw handle stored at
        body offset 4).

        #578: the in-heap field stores the handle ORed with
        0x80000000 so the conservative GC scan can never mistake
        it for a heap pointer.  AND with 0x7FFFFFFF here to
        recover the raw handle.
        """
        return [
            "i32.load offset=4",
            "i32.const 0x7FFFFFFF",
            "i32.and",
        ]

    # -----------------------------------------------------------------
    # Decimal built-in operations (§9.7.2)
    # -----------------------------------------------------------------

    def _register_decimal_import(
        self, op: str, params: list[str], results: list[str],
    ) -> str:
        """Register a Decimal host import and return the WASM call name."""
        wasm_name = f"$vera.{op}"
        param_str = " ".join(f"(param {p})" for p in params)
        result_str = " ".join(f"(result {r})" for r in results)
        sig = f"(func {wasm_name} {param_str} {result_str})"
        self._decimal_imports.add(f'  (import "vera" "{op}" {sig})')
        self._decimal_ops_used.add(op)
        return wasm_name

    def _emit_wrap_decimal_result(self) -> list[str]:
        """Wrap a Decimal raw handle on the operand stack into a
        wrapper-ADT pointer (#573 phase 3).

        Convenience for Decimal-returning ops; allocates the
        ``handle_tmp`` and ``wrapper_tmp`` locals and emits the
        wrap sequence.  Caller must have just left the raw handle
        on the operand stack (e.g. from a host-import call).
        """
        self.needs_alloc = True
        handle_tmp = self.alloc_local("i32")
        wrapper_tmp = self.alloc_local("i32")
        ins: list[str] = [f"local.set {handle_tmp}"]
        ins.extend(
            self._emit_wrap_handle(
                _WRAP_KIND_DECIMAL, handle_tmp, wrapper_tmp,
            )
        )
        return ins

    def _translate_decimal_unary(
        self, call: "ast.FnCall", env: WasmSlotEnv,
        op: str, param_type: str, result_type: str,
    ) -> list[str] | None:
        """Translate a unary Decimal operation (#573 phase 3).

        Three flavours by ``param_type`` / ``result_type``:

        * ``decimal_from_int``/``decimal_from_float`` — input is a
          primitive (i64/f64), output is Decimal.  WRAP result.
        * ``decimal_neg`` — input and output are both Decimal.
          UNWRAP input, WRAP result.
        * ``decimal_to_float`` — input Decimal, output f64.
          UNWRAP input only.
        """
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            op, [param_type], [result_type])
        ins: list[str] = list(arg_instrs)
        # Input: unwrap if Decimal (i32 with handle semantics).
        if param_type == "i32":
            ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        # Result: wrap if Decimal.  ``decimal_to_float`` produces
        # f64 (not Decimal) and is the only i32-input / non-i32-
        # output op; ``decimal_from_int`` and ``decimal_from_float``
        # have non-i32 input and i32 (Decimal) output.
        if result_type == "i32":
            ins.extend(self._emit_wrap_decimal_result())
        return ins

    def _translate_decimal_binary(
        self, call: "ast.FnCall", env: WasmSlotEnv,
        op: str,
    ) -> list[str] | None:
        """Translate a binary Decimal op (Decimal, Decimal → Decimal).

        Both inputs and the output are Decimal: UNWRAP both,
        WRAP result.  Used for ``decimal_add`` / ``decimal_sub``
        / ``decimal_mul``.
        """
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            op, ["i32", "i32"], ["i32"])
        ins: list[str] = list(a_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.extend(b_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        ins.extend(self._emit_wrap_decimal_result())
        return ins

    def _translate_decimal_from_string(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_from_string(s) → Option<Decimal> (i32 heap ptr).

        Input is a String (i32_pair) — no unwrap needed.  Result
        is an Option ADT whose Some payload is wrapped *host-
        side* (see ``host_decimal_from_string`` in
        ``vera/codegen/api.py``), so no further wrapping here.
        """
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_from_string", ["i32", "i32"], ["i32"])
        self.needs_alloc = True
        return arg_instrs + [f"call {wasm_name}"]

    def _translate_decimal_to_string(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_to_string(d) → String (#573: unwrap input only)."""
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_to_string", ["i32"], ["i32", "i32"])
        self.needs_alloc = True
        ins: list[str] = list(arg_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_decimal_div(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_div(a, b) → Option<Decimal> (#573: unwrap inputs).

        Result wrapping happens host-side (see ``host_decimal_div``
        in ``vera/codegen/api.py``); the Some payload is a
        wrapper pointer when present.
        """
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_div", ["i32", "i32"], ["i32"])
        self.needs_alloc = True
        ins: list[str] = list(a_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.extend(b_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_decimal_compare(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_compare(a, b) → Ordering (#573: unwrap inputs)."""
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_compare", ["i32", "i32"], ["i32"])
        self.needs_alloc = True
        ins: list[str] = list(a_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.extend(b_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_decimal_eq(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_eq(a, b) → Bool (#573: unwrap inputs)."""
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_eq", ["i32", "i32"], ["i32"])
        ins: list[str] = list(a_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.extend(b_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_decimal_round(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_round(d, places) → Decimal (#573: unwrap d, wrap result)."""
        d_instrs = self.translate_expr(call.args[0], env)
        p_instrs = self.translate_expr(call.args[1], env)
        if d_instrs is None or p_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_round", ["i32", "i64"], ["i32"])
        ins: list[str] = list(d_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.extend(p_instrs)
        ins.append(f"call {wasm_name}")
        ins.extend(self._emit_wrap_decimal_result())
        return ins

    # ── Map<K, V> host-import builtins ──────────────────────────────

    @staticmethod
    def _map_wasm_tag(vera_type: str | None) -> str | None:
        """Map a Vera type name to a single-char WASM type tag.

        Used to build monomorphized host import names like
        ``map_insert$ki_vi`` (key=i64, value=i64).

        Returns ``None`` for ``Array<T>`` values: arrays lower to
        ``i32_pair`` (ptr + len), but pre-#475 the fallback routed
        every non-primitive / non-String type to ``"b"`` (single
        i32), which produced a host-import signature with one i32
        slot where two were needed — silently mis-tagging
        ``Map<K, Array<T>>`` insertions and breaking ``map_values``
        round-trips.  Callers must check for ``None`` and return
        ``None`` themselves, propagating the "skip this function"
        signal through the translator (the standard compile-failure
        convention).  When direct ``Map<K, Array<T>>`` support is
        added later it would belong here as a new tag (e.g. ``"a"``)
        with matching ``_map_wasm_types`` entry.
        """
        if vera_type in ("Int", "Nat"):
            return "i"   # i64
        if vera_type == "Float64":
            return "f"   # f64
        if vera_type == "String":
            return "s"   # i32_pair
        # Array<T> values lower to i32_pair too, but no Map host
        # import currently handles that shape.  Reject so the caller
        # bails to "function skipped" rather than emitting a
        # signature-mismatched import.  The None-guard is required
        # because `vera_type` is `Optional` per the type hint above —
        # we explicitly reject Array shapes, but a `None` (uninferred
        # element type from an empty collection like `set_new()` or
        # `map_keys(map_new())`) is allowed to fall through to ``"b"``
        # so empty-collection round-trips still compile.
        if vera_type is not None and vera_type.startswith("Array"):
            return None
        # Bool, Byte, ADTs, Map handles, and uninferred (None) element
        # types from empty collections → i32.  This is the historical
        # fall-through; CodeRabbit on PR #567 flagged it as a possible
        # re-introduction of the pre-#475 hole, but the empty-collection
        # tests (`test_set_empty_to_array`, `test_map_keys_in_if_expr`,
        # `test_set_to_array_in_if_expr`) depend on this path: the
        # element type is genuinely unknown but the host import works
        # because no element value flows through it.  Mis-tagging is
        # only possible when a real (non-None) type fails inference,
        # and that's caught by the Array branch above and the
        # primitive branches.
        return "b"

    @staticmethod
    def _map_wasm_types(tag: str) -> list[str]:
        """Return WAT param types for a type tag."""
        if tag == "i":
            return ["i64"]
        if tag == "f":
            return ["f64"]
        if tag == "s":
            return ["i32", "i32"]
        return ["i32"]

    def _map_import_name(self, op: str, key_tag: str | None = None,
                         val_tag: str | None = None) -> str:
        """Build a mangled Map host import name and register it."""
        if key_tag is not None and val_tag is not None:
            suffix = f"$k{key_tag}_v{val_tag}"
        elif key_tag is not None:
            suffix = f"$k{key_tag}"
        elif val_tag is not None:
            suffix = f"$v{val_tag}"
        else:
            suffix = ""
        name = f"{op}{suffix}"
        self._map_ops_used.add(name)
        return name

    def _register_map_import(
        self, op: str, key_tag: str | None = None,
        val_tag: str | None = None,
        extra_params: list[str] | None = None,
        results: list[str] | None = None,
    ) -> str:
        """Register a Map host import and return the WASM call name."""
        name = self._map_import_name(op, key_tag, val_tag)
        wasm_name = f"$vera.{name}"
        params: list[str] = []
        if extra_params:
            params.extend(extra_params)
        param_str = " ".join(f"(param {p})" for p in params)
        result_str = ""
        if results:
            result_str = " ".join(f"(result {r})" for r in results)
        sig = f"(func {wasm_name} {param_str} {result_str})".rstrip()
        import_line = f'  (import "vera" "{name}" {sig})'
        self._map_imports.add(import_line)
        return wasm_name

    def _infer_map_key_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Map's key from the call arguments."""
        # For map_insert(m, k, v): key is arg[1]
        # For map_get/contains/remove(m, k): key is arg[1]
        # For map_new(): no key arg, infer from type context
        if call.name == "map_new":
            return None
        if len(call.args) >= 2:
            return self._infer_vera_type(call.args[1])
        return None

    def _infer_map_val_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Map's value from the call arguments."""
        # For map_insert(m, k, v): value is arg[2]
        if call.name == "map_insert" and len(call.args) >= 3:
            return self._infer_vera_type(call.args[2])
        return None

    def _translate_map_new(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_new() → wrapped Map handle via host import (#573).

        Allocates a fresh empty map on the host side, then wraps the
        raw handle in an 8-byte ADT on the GC heap so the existing
        mark-sweep collector can reclaim it.  Phase 2c of
        ``$gc_collect`` fires ``host_decref_handle(MAP, handle)``
        when the wrapper becomes unreachable, evicting the dead
        entry from ``_map_store``.
        """
        wasm_name = "$vera.map_new"
        sig = "(func $vera.map_new (result i32))"
        self._map_imports.add(f'  (import "vera" "map_new" {sig})')
        self._map_ops_used.add("map_new")
        self.needs_alloc = True
        ins: list[str] = [f"call {wasm_name}"]
        handle_tmp = self.alloc_local("i32")
        wrapper_tmp = self.alloc_local("i32")
        ins.append(f"local.set {handle_tmp}")
        ins.extend(
            self._emit_wrap_handle(
                _WRAP_KIND_MAP, handle_tmp, wrapper_tmp,
            )
        )
        return ins

    def _translate_map_insert(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_insert(m, k, v) → wrapped Map handle via host import.

        Emits a type-specific host import based on the key and value
        types.  Per #573, the input ``m`` is a wrapper-ADT pointer
        and we must unwrap it (``i32.load offset=4``) to get the
        raw host handle before calling the host helper; the result
        is a fresh raw handle that we re-wrap before returning.
        """
        key_type = self._infer_vera_type(call.args[1])
        val_type = self._infer_vera_type(call.args[2])
        kt = self._map_wasm_tag(key_type)
        vt = self._map_wasm_tag(val_type)

        if kt is None or vt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        params.extend(self._map_wasm_types(vt))  # value
        wasm_name = self._register_map_import(
            "map_insert", kt, vt,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        # Eval `m` (wrapper ptr) and unwrap to raw handle.
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        ins.extend(self._emit_unwrap_handle())
        # Eval remaining args.
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        # Wrap result.
        self.needs_alloc = True
        handle_tmp = self.alloc_local("i32")
        wrapper_tmp = self.alloc_local("i32")
        ins.append(f"local.set {handle_tmp}")
        ins.extend(
            self._emit_wrap_handle(
                _WRAP_KIND_MAP, handle_tmp, wrapper_tmp,
            )
        )
        return ins

    def _translate_map_get(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_get(m, k) → i32 (Option<V> heap pointer) via host import.

        The host reads the value from its internal dict, constructs an
        Option ADT (Some/None) in WASM memory, and returns the pointer.
        """
        key_type = self._infer_vera_type(call.args[1])
        kt = self._map_wasm_tag(key_type)

        if kt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )
        # We need the value tag too, so the host knows how to build Option<V>.
        # Infer from the map's type — look at the slot ref for arg[0].
        val_type = self._infer_map_value_from_map_arg(call.args[0])
        vt = self._map_wasm_tag(val_type)

        if vt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        wasm_name = self._register_map_import(
            "map_get", kt, vt,
            extra_params=params, results=["i32"],
        )
        self.needs_alloc = True
        ins: list[str] = []
        # Unwrap the Map argument (#573).  Result is an Option ADT
        # heap pointer built by the host helper, so no re-wrap.
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        ins.extend(self._emit_unwrap_handle())
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _infer_map_value_from_map_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the value type V from a Map<K, V> expression."""
        # If the map arg is a slot ref like @Map<String, Int>.0,
        # extract V from the type_args (not the type_name string).
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Map" and expr.type_args:
                if len(expr.type_args) == 2:
                    val_te = expr.type_args[1]
                    if isinstance(val_te, ast.NamedType):
                        return val_te.name
            # Fallback: parse from composite type_name string
            # Uses depth-aware split to handle nested generics
            # like Map<Result<Int, Bool>, String>
            name = expr.type_name
            if name.startswith("Map<") and name.endswith(">"):
                v = self._split_map_type_args(name)
                if v is not None:
                    return v[1]
        # If it's a function call that returns Map, try to infer
        if isinstance(expr, ast.FnCall):
            if expr.name in ("map_new", "map_insert", "map_remove"):
                if expr.name == "map_insert" and len(expr.args) >= 3:
                    return self._infer_vera_type(expr.args[2])
                # Recurse into the map argument
                if expr.args:
                    return self._infer_map_value_from_map_arg(expr.args[0])
        return None

    def _translate_map_contains(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_contains(m, k) → i32 (Bool) via host import."""
        key_type = self._infer_vera_type(call.args[1])
        kt = self._map_wasm_tag(key_type)

        if kt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        wasm_name = self._register_map_import(
            "map_contains", kt, None,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        # Unwrap the Map argument (#573).  Result is Bool — no wrap.
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        ins.extend(self._emit_unwrap_handle())
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_remove(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_remove(m, k) → i32 (new handle) via host import."""
        key_type = self._infer_vera_type(call.args[1])
        kt = self._map_wasm_tag(key_type)

        if kt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        wasm_name = self._register_map_import(
            "map_remove", kt, None,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        # Unwrap the Map argument (#573); re-wrap the new handle.
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        ins.extend(self._emit_unwrap_handle())
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        self.needs_alloc = True
        handle_tmp = self.alloc_local("i32")
        wrapper_tmp = self.alloc_local("i32")
        ins.append(f"local.set {handle_tmp}")
        ins.extend(
            self._emit_wrap_handle(
                _WRAP_KIND_MAP, handle_tmp, wrapper_tmp,
            )
        )
        return ins

    def _translate_map_size(
        self, arg: "ast.Expr", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_size(m) → i64 (Int) via host import.

        Per #573 the Map argument is a wrapper-ADT pointer; unwrap
        before calling the host.  The result is i64, no re-wrap.
        """
        wasm_name = "$vera.map_size"
        sig = "(func $vera.map_size (param i32) (result i64))"
        self._map_imports.add(f'  (import "vera" "map_size" {sig})')
        self._map_ops_used.add("map_size")
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_keys(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_keys(m) → (i32, i32) Array<K> via host import."""
        # Infer key type from the map argument
        key_type = self._infer_map_key_from_map_arg(call.args[0])
        kt = self._map_wasm_tag(key_type)

        if kt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )

        wasm_name = self._register_map_import(
            "map_keys", kt, None,
            extra_params=["i32"], results=["i32", "i32"],
        )
        self.needs_alloc = True
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_values(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_values(m) → (i32, i32) Array<V> via host import."""
        val_type = self._infer_map_value_from_map_arg(call.args[0])
        vt = self._map_wasm_tag(val_type)

        if vt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )

        wasm_name = self._register_map_import(
            "map_values", val_tag=vt,
            extra_params=["i32"], results=["i32", "i32"],
        )
        self.needs_alloc = True
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        return ins

    @staticmethod
    def _split_map_type_args(name: str) -> tuple[str, str] | None:
        """Split 'Map<K, V>' into (K, V) with nesting-aware comma split.

        Handles nested generics like Map<Result<Int, Bool>, String>
        by tracking angle-bracket depth.
        """
        inner = name[4:-1]  # strip "Map<" and ">"
        depth = 0
        for i, ch in enumerate(inner):
            if ch == "<":
                depth += 1
            elif ch == ">":
                depth -= 1
            elif ch == "," and depth == 0:
                k = inner[:i].strip()
                v = inner[i + 1:].strip()
                if k and v:
                    return (k, v)
        return None

    def _infer_map_key_from_map_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the key type K from a Map<K, V> expression."""
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Map" and expr.type_args:
                if len(expr.type_args) >= 1:
                    key_te = expr.type_args[0]
                    if isinstance(key_te, ast.NamedType):
                        return key_te.name
            name = expr.type_name
            if name.startswith("Map<") and name.endswith(">"):
                v = self._split_map_type_args(name)
                if v is not None:
                    return v[0]
        if isinstance(expr, ast.FnCall):
            if expr.name == "map_insert" and len(expr.args) >= 2:
                return self._infer_vera_type(expr.args[1])
            if expr.args:
                return self._infer_map_key_from_map_arg(expr.args[0])
        return None

    # ── Set<T> host-import builtins ──────────────────────────────

    def _set_import_name(self, op: str, elem_tag: str | None = None) -> str:
        """Build a mangled Set host import name."""
        suffix = f"$e{elem_tag}" if elem_tag is not None else ""
        name = f"{op}{suffix}"
        self._set_ops_used.add(name)
        return name

    def _register_set_import(
        self, op: str, elem_tag: str | None = None,
        extra_params: list[str] | None = None,
        results: list[str] | None = None,
    ) -> str:
        """Register a Set host import and return the WASM call name."""
        name = self._set_import_name(op, elem_tag)
        wasm_name = f"$vera.{name}"
        params: list[str] = []
        if extra_params:
            params.extend(extra_params)
        param_str = " ".join(f"(param {p})" for p in params)
        result_str = ""
        if results:
            result_str = " ".join(f"(result {r})" for r in results)
        sig = f"(func {wasm_name} {param_str} {result_str})".rstrip()
        import_line = f'  (import "vera" "{name}" {sig})'
        self._set_imports.add(import_line)
        return wasm_name

    def _infer_set_elem_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Set's element from call arguments."""
        if call.name == "set_new":
            return None
        if len(call.args) >= 2:
            return self._infer_vera_type(call.args[1])
        return None

    def _infer_set_elem_from_set_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the element type T from a Set<T> expression."""
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Set" and expr.type_args:
                if len(expr.type_args) >= 1:
                    elem_te = expr.type_args[0]
                    if isinstance(elem_te, ast.NamedType):
                        return elem_te.name
            name = expr.type_name
            if name.startswith("Set<") and name.endswith(">"):
                return name[4:-1]
        if isinstance(expr, ast.FnCall):
            if expr.name == "set_add" and len(expr.args) >= 2:
                return self._infer_vera_type(expr.args[1])
            # Only recurse into set-returning functions
            if expr.name in ("set_new", "set_add", "set_remove"):
                if expr.args:
                    return self._infer_set_elem_from_set_arg(expr.args[0])
        return None

    def _translate_set_new(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_new() → wrapped Set handle via host import (#573 phase 2).

        Mirror of ``_translate_map_new``; see there for design.
        """
        wasm_name = "$vera.set_new"
        sig = "(func $vera.set_new (result i32))"
        self._set_imports.add(f'  (import "vera" "set_new" {sig})')
        self._set_ops_used.add("set_new")
        self.needs_alloc = True
        ins: list[str] = [f"call {wasm_name}"]
        handle_tmp = self.alloc_local("i32")
        wrapper_tmp = self.alloc_local("i32")
        ins.append(f"local.set {handle_tmp}")
        ins.extend(
            self._emit_wrap_handle(
                _WRAP_KIND_SET, handle_tmp, wrapper_tmp,
            )
        )
        return ins

    def _translate_set_add(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_add(s, elem) → wrapped Set handle (#573).

        Unwrap ``s``, call host, re-wrap result.
        """
        elem_type = self._infer_vera_type(call.args[1])
        et = self._map_wasm_tag(elem_type)

        if et is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )

        params = ["i32"]  # set handle
        params.extend(self._map_wasm_types(et))  # element
        wasm_name = self._register_set_import(
            "set_add", et,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        ins.extend(self._emit_unwrap_handle())
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        self.needs_alloc = True
        handle_tmp = self.alloc_local("i32")
        wrapper_tmp = self.alloc_local("i32")
        ins.append(f"local.set {handle_tmp}")
        ins.extend(
            self._emit_wrap_handle(
                _WRAP_KIND_SET, handle_tmp, wrapper_tmp,
            )
        )
        return ins

    def _translate_set_contains(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_contains(s, elem) → Bool (#573: unwrap input only)."""
        elem_type = self._infer_vera_type(call.args[1])
        et = self._map_wasm_tag(elem_type)

        if et is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )

        params = ["i32"]  # set handle
        params.extend(self._map_wasm_types(et))  # element
        wasm_name = self._register_set_import(
            "set_contains", et,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        ins.extend(self._emit_unwrap_handle())
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_remove(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_remove(s, elem) → wrapped Set handle (#573)."""
        elem_type = self._infer_vera_type(call.args[1])
        et = self._map_wasm_tag(elem_type)

        if et is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )

        params = ["i32"]  # set handle
        params.extend(self._map_wasm_types(et))  # element
        wasm_name = self._register_set_import(
            "set_remove", et,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        ins.extend(self._emit_unwrap_handle())
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        self.needs_alloc = True
        handle_tmp = self.alloc_local("i32")
        wrapper_tmp = self.alloc_local("i32")
        ins.append(f"local.set {handle_tmp}")
        ins.extend(
            self._emit_wrap_handle(
                _WRAP_KIND_SET, handle_tmp, wrapper_tmp,
            )
        )
        return ins

    def _translate_set_size(
        self, arg: "ast.Expr", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_size(s) → i64 (#573: unwrap input only)."""
        wasm_name = "$vera.set_size"
        sig = "(func $vera.set_size (param i32) (result i64))"
        self._set_imports.add(f'  (import "vera" "set_size" {sig})')
        self._set_ops_used.add("set_size")
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_to_array(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_to_array(s) → Array<T> (#573: unwrap input only)."""
        elem_type = self._infer_set_elem_from_set_arg(call.args[0])
        et = self._map_wasm_tag(elem_type)

        if et is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a host-import shape yet.
            raise CodegenSkip(
                call,
                "Map/Set with Array-typed key, value, or element is not supported",
            )

        wasm_name = self._register_set_import(
            "set_to_array", et,
            extra_params=["i32"], results=["i32", "i32"],
        )
        self.needs_alloc = True
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.append(f"call {wasm_name}")
        return ins
