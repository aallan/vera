"""Container type translation mixin for WasmContext.

Handles Map<K,V> and Set<E>, persistent hash tries in the module's own
code (#1676), and the opaque-handle Decimal type, a host import.

A Map or Set operation lowers to a call of the function ``vera.wasm.hamt``
generates for it at its key, value or element representation, named as its
instance (``map_insert$ks_vi`` for a String key and an Int value) and
emitted once per module on demand.  An update returns a new header, rooted
where it LANDS by the call-result rule in ``WasmContext._root_landed_value``
(#1379), as every call result is.  Decimal keeps the value-typed host store
and the #573 wrap/unwrap scheme: its call-sites wrap a raw handle in an ADT
(tag at offset 0, handle at offset 4), register it with
``$register_wrapper``, and unwrap via ``i32.load offset=4`` before the host
call.
"""

from __future__ import annotations

from vera import ast
from vera.skip import CodegenSkip
from vera.wasm import hamt
from vera.wasm.helpers import WasmSlotEnv, gc_shadow_push

# #573: kind discriminators passed to ``host_decref_handle`` and
# stored in the wrap-table side index.  Must stay in sync with the
# Python dispatcher in ``vera/codegen/api.py`` and the JS dispatcher
# in ``vera/browser/runtime.mjs``.  Kinds 1 and 2 were Map's and Set's,
# which are plain heap blocks (#706, #1676); the numbers stay retired.
_WRAP_KIND_DECIMAL = 3
_WRAP_KIND_FUTURE = 4  # #841: fused-async pending future

# #573: wrapper-ADT tag values stored at wrapper body offset 0.  Not
# strictly required for correctness — the side table is the source
# of truth for "is this object a wrapper" — but stored anyway as a
# debugging aid (a heap dump will show e.g. MAP_HANDLE_TAG at the
# body's first word).  Chosen well outside the user-ADT tag range
# (which starts at 0 and increments per constructor).
_DECIMAL_HANDLE_TAG = 0xFEEDC003
# #841: unlike the other tags, the Future tag is also load-bearing for
# discrimination — the await lowering in ``calls_markup.py`` probes a
# Future<Result<String, String>> value's first word against this tag to
# distinguish a fused handle wrapper from an eagerly-evaluated Result
# pointer (whose first word is a small constructor tag).
_FUTURE_HANDLE_TAG = 0xFEEDC004

_KIND_TO_TAG: dict[int, int] = {
    _WRAP_KIND_DECIMAL: _DECIMAL_HANDLE_TAG,
    _WRAP_KIND_FUTURE: _FUTURE_HANDLE_TAG,
}

# Wrapper ADT body size:
#   +0  tag (i32)                                     [#573]
#   +4  handle | 0x80000000 (bit-31 tagged)           [#578]
#   +8  0, the field Map's and Set's buckets once held [#695/#706]
#
# Must agree with ``_WRAPPER_BODY_SIZE`` in ``vera/runtime/heap.py``.
_WRAPPER_BODY_SIZE = 12


class CallsContainersMixin:
    """Methods for translating Map, Set, and Decimal built-in functions."""

    # -----------------------------------------------------------------
    # Decimal handle wrap / unwrap helpers (#573).
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
            # Write 0 at +8 (bucket_ptr).  No wrap kind uses a bucket
            # here: Decimal is value-typed and the #841 Future handle
            # indexes a host-side store — nothing for the GC scan to
            # anchor.
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
        # `needs_alloc` beside the push (#1376/#1379): the flag is what
        # declares `$gc_sp`, so a push without it emits a reference to
        # an undeclared global whenever nothing else in the module
        # allocates — and `_scope_shadow_roots` refuses it outright.
        self.needs_alloc = True
        seq.extend(gc_shadow_push(wrapper_temp))
        # #706: no wrap kind needs a bucket (``PyDecimal`` is value-typed;
        # #841 Future handles index a host-side future store).  The
        # ``attach_bucket_to_wrapper`` call is retained as a tripwire: its
        # host-side dispatcher asserts kind=3, so a wrapper of any other
        # kind routed through this path fails loudly.  #841 Future
        # wrappers skip the call by design (they were never part of the
        # #695 bucket scheme, and emitting it would trip the assert).
        if kind != _WRAP_KIND_FUTURE:
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

    def _register_decimal_import(self, op: str) -> str:
        """Register a Decimal host import and return the WASM call name.

        The declaration is the registry's row for *op* (`vera.builtins`).
        """
        self._host_imports_used.add(op)
        return f"$vera.{op}"

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
        wasm_name = self._register_decimal_import(op)
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
        wasm_name = self._register_decimal_import(op)
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
        wasm_name = self._register_decimal_import("decimal_from_string")
        self.needs_alloc = True
        return arg_instrs + [f"call {wasm_name}"]

    def _translate_decimal_to_string(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_to_string(d) → String (#573: unwrap input only)."""
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        wasm_name = self._register_decimal_import("decimal_to_string")
        self.needs_alloc = True
        # Decimal keeps the wrapper/handle scheme: unwrap the wrapper to
        # the raw decimal-store handle before the host call.
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
        wasm_name = self._register_decimal_import("decimal_div")
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
        wasm_name = self._register_decimal_import("decimal_compare")
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
        wasm_name = self._register_decimal_import("decimal_eq")
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
        wasm_name = self._register_decimal_import("decimal_round")
        ins: list[str] = list(d_instrs)
        ins.extend(self._emit_unwrap_handle())
        ins.extend(p_instrs)
        ins.append(f"call {wasm_name}")
        ins.extend(self._emit_wrap_decimal_result())
        return ins

    # ── Map<K, V> and Set<T>: generated functions (#1676) ─────────

    def _collection_fn(self, op: str, **tags: str | None) -> str:
        """The function *op* lowers to at the representations *tags* names
        (``$map_insert$ks_vi``), requested with every helper it calls.

        The functions are ``vera.wasm.hamt``'s, emitted once per module
        (``_collection_helpers``, merged like the structural-Eq helpers);
        ``$eq_String`` is the one a String key's equality shares with ``==``.
        """
        name = hamt.helper_name(op, **tags)
        hamt.register(name, self._collection_helpers, self._request_string_eq_helper)
        self.needs_alloc = True
        return f"${name}"

    def _export_host_maps(self, value_tag: str) -> None:
        """Export the functions a host builds and reads a ``Map<String, V>``
        of *value_tag* through (``hamt.HOST_MAPS``): the JSON host's object
        members, the HTML host's attributes."""
        for name in hamt.HOST_MAPS[value_tag]:
            op, _, _ = name.partition("$")
            self._collection_fn(op, **hamt.tags_of(name))
            self._collection_exports.add(name)


    def _map_wasm_tag(self, vera_type: str | None) -> str | None:
        """Map a Vera type name to its representation tag (``vera.wasm.hamt``).

        Names the generated function of an operation at that representation,
        like ``map_insert$ki_vi`` (key=i64, value=i64): ``i`` Int and Nat,
        ``f`` Float64, ``s`` String, ``y`` Bool and Byte (an i32 that takes
        one byte in an array), and ``b`` every other value, a heap pointer.

        A representation-transparent ``Future<…>`` wrapper is stripped to
        its payload first (#1097, #841): a ``Future<Int>`` IS an i64, a
        ``Future<String>`` IS an i32_pair, so the tag must classify the
        payload, not the opaque head.  An alias name is canonicalized to
        its target's full compound spelling before stripping (``type FI =
        Future<Int>``), re-canonicalized per wrapper hop so alias-of-Future
        chains resolve.  Pre-strip, a ``Future<Int>`` value fell through to
        the ``"b"`` (single-i32) tag while the value expression pushed an
        i64 — the registered operation disagreed with the stack and a
        check+verify-green program compiled exit-0 to an INVALID module
        ("type mismatch: expected i32, found i64", or "values remaining on
        stack" for the i32_pair payload).  Stripping happens BEFORE the
        chain, so the zero-size erasure arm still fires on the payload
        (``Future<Unit>`` -> ``Unit`` -> the ``None`` rejection) and an
        ``Array<T>`` payload (``Future<Array<Int>>`` -> ``Array<Int>``)
        reaches the existing Array-reject ``None`` path — a loud skip, not
        an invalid module.

        Returns ``None`` for ``Array<T>`` values: arrays lower to
        ``i32_pair`` (ptr + len), but pre-#475 the fallback routed
        every non-primitive / non-String type to ``"b"`` (single
        i32), which produced a signature with one i32 slot where two
        were needed — silently mis-tagging ``Map<K, Array<T>>``
        insertions and breaking ``map_values`` round-trips.  Also returns ``None`` for any name that ERASES
        to zero size (#1075 — an instance method for this reason: the
        recursive `_slot_name_erases_to_unit` oracle needs the alias
        tables): it pushes no operand at all, so a ``"b"`` tag emits
        invalid WASM.  Callers must check for ``None`` and return
        ``None`` themselves, propagating the "skip this function"
        signal through the translator (the standard compile-failure
        convention).  When direct ``Map<K, Array<T>>`` support is
        added later it would belong here as a new tag (e.g. ``"a"``)
        with its WAT types in ``vera.wasm.hamt.PARAMS``.
        """
        # #1097: canonicalize an alias name, then peel transparent
        # ``Future<…>`` wrappers to the payload BEFORE the tag chain below
        # classifies it.  ONE canonicalize suffices: it resolves alias
        # payloads at every depth (``type FI = Future<Int>`` and nested
        # ``Future<FI2>`` chains both come back fully spelled), so the
        # strip is a plain textual peel — matching ``_strip_future`` — and
        # a cyclic alias (already E132 at check) cannot spin it: the
        # canonicalizer's ``_seen`` guard runs once, never per hop.
        if vera_type is not None:
            vera_type, _ = self._canonicalize_alias_slot_name(vera_type)
            while vera_type.startswith("Future<") and vera_type.endswith(">"):
                vera_type = vera_type[len("Future<"):-1]
        if vera_type in ("Int", "Nat"):
            return "i"   # i64
        if vera_type == "Float64":
            return "f"   # f64
        if vera_type == "String":
            return "s"   # i32_pair
        if vera_type in ("Bool", "Byte"):
            return "y"   # i32, one byte in an array (#1729)
        # Array<T> values lower to i32_pair too, but no generated
        # operation handles that shape.  Reject so the caller
        # bails to "function skipped" rather than emitting a
        # signature-mismatched import.  The None-guard is required
        # because `vera_type` is `Optional` per the type hint above —
        # we explicitly reject Array shapes, but a `None` (uninferred
        # element type from an empty collection like `set_new()` or
        # `map_keys(map_new())`) is allowed to fall through to ``"b"``
        # so empty-collection round-trips still compile.
        if vera_type is not None and vera_type.startswith("Array"):
            return None
        # #1075: a ZERO-SIZE key/value/element pushes nothing onto the
        # stack, so tagging it "b" emits an operation expecting an i32
        # operand that was never produced — invalid WASM behind an exit-0
        # compile.  The annotated spellings (`@Map<String, Unit>`, aliases)
        # are rejected at check (E135, the Map/Set siblings of the Array
        # gate); this backstop covers the annotation-free spellings, whose
        # types exist only through inference and never pass type
        # resolution — the caller's None-branch turns them into a loud
        # skip.  The test is the same RECURSIVE erasure oracle the checker
        # gate and the zero-size declaration guards key on
        # (`_slot_name_erases_to_unit`: alias chains canonicalized,
        # `Future<...>` payloads recursed) — a literal name comparison
        # here was defeated by any indirection (`async(async(()))` infers
        # `Future<Future<Unit>>`; a user fn returning `@FU` with
        # `type FU = Future<Unit>` infers the alias name; both previously
        # fell through to "b" and emitted invalid modules — PR #1083
        # adversarial review).
        if vera_type is not None and self._slot_name_erases_to_unit(vera_type):
            return None
        # ADTs, Map and Set headers, and uninferred (None) element types
        # from empty collections → i32.  This is the historical
        # fall-through; CodeRabbit on PR #567 flagged it as a possible
        # re-introduction of the pre-#475 hole, but the empty-collection
        # tests (`test_set_empty_to_array`, `test_map_keys_in_if_expr`,
        # `test_set_to_array_in_if_expr`) depend on this path: the
        # element type is genuinely unknown but the operation works
        # because no element value flows through it.  Mis-tagging happens
        # whenever a REAL (non-None) element type fails inference and a
        # value flows through the import.  The #1053 container extension
        # closed the known such failures — alias-spelled slots, registered
        # user-fn returns (parameterized, bare-alias, generic-alias), and
        # Block-wrapped arguments now resolve via
        # `_container_arg_elem_name` — but argument shapes none of the
        # resolvers type (see that helper's docstring for the list) still
        # reach this fall-through with real elements and would mis-tag;
        # they are exactly the shapes with no inference arm today.
        return "b"

    def _infer_map_key_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Map's key from the call arguments."""
        # For map_insert(m, k, v): key is arg[1]
        # For map_get/contains/remove(m, k): key is arg[1]
        # For map_new(): no key arg, infer from type context
        if call.name == "map_new":
            return None
        if len(call.args) >= 2:
            return self._container_entry_type_name(call.args[1])
        return None

    def _infer_map_val_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Map's value from the call arguments."""
        # For map_insert(m, k, v): value is arg[2]
        if call.name == "map_insert" and len(call.args) >= 3:
            return self._container_entry_type_name(call.args[2])
        return None

    def _translate_map_new(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_new() → the header of an empty Map, rooted where it lands
        (#1379) and reclaimed by ordinary mark-sweep."""
        return [f"call {self._collection_fn('map_new')}"]

    def _translate_map_insert(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_insert(m, k, v) → a new Map header (#1676).

        Calls the operation generated for the key and value
        representations; ``m`` is left as it was, and the header returned
        is rooted where it lands by ``_root_landed_value`` (#1379).
        """
        key_type = self._container_entry_type_name(call.args[1])
        val_type = self._container_entry_type_name(call.args[2])
        kt = self._map_wasm_tag(key_type)
        vt = self._map_wasm_tag(val_type)

        if kt is None or vt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )

        wasm_name = self._collection_fn("map_insert", k=kt, v=vt)
        ins: list[str] = []
        # #1426: the §2.6.5 predicate on the VALUE going into the map.  The
        # value argument's own recorded target is the ERASED base — generic
        # unification resolves `V` against the `map_new()` receiver — so the
        # refinement is read from the CALL's target instead, which carries
        # `Map<K, {refined}>` whole.  Same asymmetry the verifier hit
        # obligating this site, answered from the same place.  R-1412 F3: a
        # `map_insert` NESTED in a container position has no recorded target
        # of its own, so the one its position handed down stands in for it.
        map_target = self._container_target_refined(call)
        value_component = self._adt_arg_type(map_target, 1)
        # A chained insert builds the same map, so the receiver is handed
        # the map's own type, as the verifier's descent obligates it
        # (R-1412 F3).
        with self._handing_down(call.args[0], map_target):
            arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        # Eval remaining args.
        for pos, arg in enumerate(call.args[1:], start=1):
            with self._handing_down(
                    arg, value_component if pos == 2 else None):
                arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            if pos == 2:
                arg_instrs = self._emit_construction_refine_guard(
                    arg_instrs, arg, "map value", "map value insert", env,
                    component_ty=value_component,
                )
                # #1440: the SIGN obligation at the same insert.
                arg_instrs = self._emit_construction_nat_guard(
                    arg_instrs, arg, value_component)
            else:
                # The key is `K`'s argument: checked where `K` is `Nat`.
                arg_instrs = self._guard_nat_instantiated_arg(arg, arg_instrs)
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_get(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_get(m, k) → i32, the `Option<V>` the generated operation
        builds: `Some` of the key's value, or `None`."""
        key_type = self._container_entry_type_name(call.args[1])
        kt = self._map_wasm_tag(key_type)

        if kt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )
        # The value tag too: it lays out the Option<V> the operation builds.
        # Infer from the map's type — look at the slot ref for arg[0].
        val_type = self._infer_map_value_from_map_arg(call.args[0])
        vt = self._map_wasm_tag(val_type)

        if vt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )

        wasm_name = self._collection_fn("map_get", k=kt, v=vt)
        self.needs_alloc = True
        ins: list[str] = []
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            # The key is `K`'s argument: checked where `K` is `Nat`.
            ins.extend(self._guard_nat_instantiated_arg(arg, arg_instrs))
        ins.append(f"call {wasm_name}")
        return ins

    def _container_arg_elem_name(
        self, expr: "ast.Expr", container: str, idx: int,
    ) -> str | None:
        """Type-arg ``idx`` of a ``container``-typed argument expression,
        resolved through the shared rebuilder (#1053 container extension).

        ``_named_type_from_arg_info`` resolves the argument shapes the
        local arms in ``_infer_map_key/value_from_map_arg`` and
        ``_infer_set_elem_from_set_arg`` below don't: an alias-spelled slot
        (``@M.0`` via `type M = Map<String, Int>;` — #1055), a registered
        non-generic user fn's declared return — parameterized (#1053),
        bare-alias (`fn mkm(-> @M)` — #1071), or generic-alias
        (`-> @MyMap<Int>` via `type MyMap<V> = Map<String, V>`,
        substituted through the target — #1068) — and a Block-wrapped
        argument via its tail expression (#1071).  Pre-fix those shapes
        returned None here and ``_map_wasm_tag(None)`` fell through to the
        ``"b"`` (i32) tag, so the mis-tagged operation silently truncated
        i64 values and garbled String keys (a wrong VALUE, not even an
        [E602] drop).

        Shapes that still return ``None`` and ride the permissive ``"b"``
        fall-through: genuinely element-type-free arguments (an empty
        ``map_new()`` / ``set_new()``, where no element value flows through
        the import), builtin container chains the local arms resolve
        instead, and argument expressions none of the resolvers type (an
        effect-op call, a match/if expression, a chained generic alias
        whose free type params survive substitution).
        """
        nt = self._named_type_from_arg_info(expr)
        if (nt is not None and nt.name == container and nt.type_args
                and len(nt.type_args) > idx):
            ta = nt.type_args[idx]
            if isinstance(ta, ast.NamedType):
                return self._format_named_type(ta)
        return None

    def _container_entry_type_name(self, expr: "ast.Expr") -> str | None:
        """Full Vera type name of a Map/Set ENTRY expression (a key, value,
        or element argument) for host-tag classification.

        Rebuilder-first (#1075, PR #1083 adversarial review):
        ``_named_type_from_arg_info`` recovers a registered user fn's
        declared return with FULL nesting (``Future<Unit>``, ``Array<String>``
        — including bare-alias and generic-alias returns, #1071/#1068),
        where ``_infer_vera_type``'s non-generic arm deliberately collapses
        a parameterized return to its bare head (``"Future"``, the #911
        convention) — a name the zero-size erasure oracle and the
        Array-reject branch in :py:meth:`_map_wasm_tag` cannot decide, so a
        ``fn(-> @Future<Unit>)`` map value fell through to the ``"b"`` tag
        and emitted invalid WASM.  Falls back to ``_infer_vera_type`` for
        every shape the rebuilder does not type (literals, effect ops,
        builtin calls like ``async(...)`` whose inference arm already
        renders the full spelling), so tags for previously-working entries
        are unchanged.
        """
        nt = self._named_type_from_arg_info(expr)
        if nt is not None:
            return self._format_named_type(nt)
        return self._infer_vera_type(expr)

    def _infer_map_value_from_map_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the value type V from a Map<K, V> expression.

        The shared-rebuilder consult handles alias-spelled and user-fn
        arguments first (#1053 container extension); it resolves the direct
        ``@Map<K, V>`` slot to the same answer as the arms below, so
        ordering is behavior-preserving for the previously-working shapes.
        """
        t = self._container_arg_elem_name(expr, "Map", 1)
        if t is not None:
            return t
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
                    return self._container_entry_type_name(expr.args[2])
                # Recurse into the map argument
                if expr.args:
                    return self._infer_map_value_from_map_arg(expr.args[0])
        return None

    def _translate_map_contains(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_contains(m, k) → i32 (Bool)."""
        key_type = self._container_entry_type_name(call.args[1])
        kt = self._map_wasm_tag(key_type)

        if kt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )

        wasm_name = self._collection_fn("map_contains", k=kt)
        ins: list[str] = []
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            # The key is `K`'s argument: checked where `K` is `Nat`.
            ins.extend(self._guard_nat_instantiated_arg(arg, arg_instrs))
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_remove(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_remove(m, k) → i32, a Map header without the key (``m``
        itself when the key is absent)."""
        key_type = self._container_entry_type_name(call.args[1])
        kt = self._map_wasm_tag(key_type)

        if kt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )

        wasm_name = self._collection_fn("map_remove", k=kt)
        ins: list[str] = []
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            # The key is `K`'s argument: checked where `K` is `Nat`.
            ins.extend(self._guard_nat_instantiated_arg(arg, arg_instrs))
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_size(
        self, arg: "ast.Expr", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_size(m) → i64 (Int): the count the header holds."""
        wasm_name = self._collection_fn("map_size")
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_keys(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_keys(m) → (i32, i32) Array<K>, in insertion order."""
        # Infer key type from the map argument
        key_type = self._infer_map_key_from_map_arg(call.args[0])
        kt = self._map_wasm_tag(key_type)

        if kt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )

        wasm_name = self._collection_fn("map_keys", k=kt)
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_values(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_values(m) → (i32, i32) Array<V>, in insertion order."""
        val_type = self._infer_map_value_from_map_arg(call.args[0])
        vt = self._map_wasm_tag(val_type)

        if vt is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )

        wasm_name = self._collection_fn("map_values", v=vt)
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
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
        """Infer the key type K from a Map<K, V> expression.

        Shared-rebuilder consult first (#1053 container extension) — see
        :py:meth:`_container_arg_elem_name`.  For a user-fn argument this
        also pre-empts the blind ``args[0]`` recursion below, so the
        DECLARED return type wins over a coincidental map-shaped first
        argument.
        """
        t = self._container_arg_elem_name(expr, "Map", 0)
        if t is not None:
            return t
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
                return self._container_entry_type_name(expr.args[1])
            if expr.args:
                return self._infer_map_key_from_map_arg(expr.args[0])
        return None

    # ── Set<T> ─────────────────────────────────────────────────────

    def _infer_set_elem_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Set's element from call arguments."""
        if call.name == "set_new":
            return None
        if len(call.args) >= 2:
            return self._container_entry_type_name(call.args[1])
        return None

    def _infer_set_elem_from_set_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the element type T from a Set<T> expression.

        Shared-rebuilder consult first (#1053 container extension) — see
        :py:meth:`_container_arg_elem_name`.
        """
        t = self._container_arg_elem_name(expr, "Set", 0)
        if t is not None:
            return t
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
                return self._container_entry_type_name(expr.args[1])
            # Only recurse into set-returning functions
            if expr.name in ("set_new", "set_add", "set_remove"):
                if expr.args:
                    return self._infer_set_elem_from_set_arg(expr.args[0])
        return None

    def _translate_set_new(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_new() → the header of an empty Set; see ``_translate_map_new``."""
        return [f"call {self._collection_fn('set_new')}"]

    def _translate_set_add(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_add(s, elem) → i32, a Set header with the element (``s``
        itself when the element is present)."""
        elem_type = self._container_entry_type_name(call.args[1])
        et = self._map_wasm_tag(elem_type)

        if et is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )

        wasm_name = self._collection_fn("set_add", e=et)
        ins: list[str] = []
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            # The element is `T`'s argument: checked where `T` is `Nat`.
            ins.extend(self._guard_nat_instantiated_arg(arg, arg_instrs))
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_contains(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_contains(s, elem) → Bool."""
        elem_type = self._container_entry_type_name(call.args[1])
        et = self._map_wasm_tag(elem_type)

        if et is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )

        wasm_name = self._collection_fn("set_contains", e=et)
        ins: list[str] = []
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            # The element is `T`'s argument: checked where `T` is `Nat`.
            ins.extend(self._guard_nat_instantiated_arg(arg, arg_instrs))
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_remove(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_remove(s, elem) → i32, a Set header without the element
        (``s`` itself when the element is absent)."""
        elem_type = self._container_entry_type_name(call.args[1])
        et = self._map_wasm_tag(elem_type)

        if et is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )

        wasm_name = self._collection_fn("set_remove", e=et)
        ins: list[str] = []
        arg0 = self.translate_expr(call.args[0], env)
        if arg0 is None:
            return None
        ins.extend(arg0)
        for arg in call.args[1:]:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            # The element is `T`'s argument: checked where `T` is `Nat`.
            ins.extend(self._guard_nat_instantiated_arg(arg, arg_instrs))
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_size(
        self, arg: "ast.Expr", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_size(s) → i64 (Int): the count the header holds."""
        wasm_name = self._collection_fn("set_size")
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_to_array(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_to_array(s) → Array<T>, in insertion order."""
        elem_type = self._infer_set_elem_from_set_arg(call.args[0])
        et = self._map_wasm_tag(elem_type)

        if et is None:
            # #475 finding 5 — Map<K, V> / Set<T> with Array-typed
            # K, V, or element doesn't have a generated operation yet;
            # #1075 — a zero-size (Unit-erasing) K, V, or element has
            # no value to pass through one (annotated spellings are
            # E135 at check; this is the inference-only backstop).
            raise CodegenSkip(
                call,
                "Map/Set with an Array-typed or zero-size key, value, or element is not supported",
            )

        wasm_name = self._collection_fn("set_to_array", e=et)
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins
