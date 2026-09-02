"""Constructor, match, and array translation mixin for WasmContext."""

from __future__ import annotations

from typing import TYPE_CHECKING

from vera import ast
from vera.skip import CodegenSkip
from vera.wasm.helpers import (
    _INLINE_I32_TYPES,
    WasmSlotEnv,
    _element_mem_size,
    _element_load_op,
    _element_store_op,
    _is_pair_element_type,
    contains_shadow_push,
    gc_shadow_push,
    is_gc_pointer_base,
)

if TYPE_CHECKING:
    from vera.codegen import ConstructorLayout


class DataMixin:
    """Methods for translating constructors, match expressions, and arrays."""

    # -----------------------------------------------------------------
    # Constructors
    # -----------------------------------------------------------------

    def _translate_nullary_constructor(
        self, expr: ast.NullaryConstructor
    ) -> list[str] | None:
        """Translate a nullary constructor (e.g., None, Red) to WAT.

        Emits: alloc → store tag → return pointer.
        """
        layout = self._ctor_layouts.get(expr.name)
        if layout is None:
            raise CodegenSkip(
                expr, f"unknown nullary constructor {expr.name!r}"
            )

        self.needs_alloc = True
        tmp = self.alloc_local("i32")
        return [
            f"i32.const {layout.total_size}",
            "call $alloc",
            f"local.tee {tmp}",
            f"i32.const {layout.tag}",
            "i32.store",
            *gc_shadow_push(tmp),
            f"local.get {tmp}",
        ]

    def _translate_constructor_call(
        self, expr: ast.ConstructorCall, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a constructor call (e.g., Some(42)) to WAT.

        Emits: alloc → store tag → store each field → return pointer.
        Field offsets are computed from the concrete argument types so that
        generic constructors (e.g. Some(T) instantiated as Some(Int))
        use the correct WASM types and alignment.
        """
        layout = self._ctor_layouts.get(expr.name)
        if layout is None:
            raise CodegenSkip(
                expr, f"unknown constructor {expr.name!r}"
            )

        # Translate all arguments and infer their concrete WASM types.
        # A `Unit` field is zero-size (spec §2.2 / §11.2.2: `Unit` is 0 bytes
        # with no WASM representation), so it carries the `"unit"` sentinel
        # rather than a real WAT type: its instructions are still emitted (for
        # any side effect — a `()` literal produces nothing, but a
        # `Unit`-returning call does have effects), but it occupies no bytes
        # in the layout and stores nothing.  This mirrors the existing
        # Unit-skip in `_translate_let_destruct` and closes #902 — a
        # `Tuple<Unit, …>` (or any constructor with a `Unit` field) must
        # compile, not silently skip the function and dangle its call.
        arg_instrs_list: list[list[str]] = []
        arg_wasm_types: list[str] = []
        for i, arg in enumerate(expr.args):
            # #1092/#1212: an int literal the checker coerced into a GENERIC
            # field instantiated at @Byte is marked BEFORE translation, so
            # both its lowering and the `arg_wt` inference below see the
            # field's i32 width — including a literal inside an `if` /
            # `match` argument, through the ONE branch descent.  See the
            # #1092 note on `_ctor_field_targets_byte` for why the literal
            # alone cannot decide this.
            if self._ctor_field_targets_byte(expr, i):
                self._mark_byte_write_value(arg, "Byte")
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            arg_wt = self._infer_expr_wasm_type(arg)
            if arg_wt is None:
                # Distinguish a genuine zero-size field (handled) from a true
                # inability to infer the WASM type (still a skip).  `_is_void_expr`
                # — the canonical "produces no stack value" check — catches a
                # *Unit-returning call* in field position (`IO.print("x")`, a
                # user `@Unit` fn, a void effect op, a `ModuleCall` to a `@Unit`
                # fn), laid out zero-size instead of skipping (#902 completeness:
                # `_infer_vera_type` returns None for Qualified/Module calls).
                # #1031: a *transparent* `Future<Unit>` field (`async(())`)
                # produces no stack value either — `_infer_expr_wasm_type` already
                # returned None by recursing through the Future to its zero-size
                # Unit payload — but it is not structurally void, so also lay it
                # out zero-size when its inferred Vera type erases to Unit.  This
                # gates reachability: without it the constructor skips and the
                # destructure/match declaration guards below are never reached.
                arg_vera = self._infer_vera_type(arg)
                if self._is_void_expr(arg) or (
                    arg_vera is not None
                    and self._slot_name_erases_to_unit(arg_vera)
                ):
                    arg_wt = "unit"
                else:
                    raise CodegenSkip(
                        arg,
                        "could not infer constructor argument WASM type",
                    )
            # #1092: an in-range int literal the checker coerced into a
            # GENERIC field instantiated at @Byte (`let @Box<Byte> = MkB(0);`
            # — the only literal-at-Byte-field spelling check admits: a
            # DECLARED `Byte` field is E213, out-of-range / negative /
            # non-literal @Int arguments are E170) translated at the
            # literal's own i64 width and was stored at the i64 slot, while
            # every READER — field extraction, the structural-`$eq` helper,
            # show/hash — sizes the field from the instantiated type (Byte
            # -> i32 at the i32 offset): extraction read 0 for a stored 255
            # and `MkB(0) == MkB(255)` compared EQUAL, silently, on a
            # check-green program.  The marking above stores the coerced
            # literal at the field's i32 Byte width, exactly as the
            # (always-correct) `@Byte`-slot passthrough argument does; a
            # literal outside 0..255 is E170 at check, so nothing narrower
            # than the marking's own range test is needed here.  The target
            # instantiation comes from the checker-recorded target type (the
            # #820 table); an unthreaded transform->compile keeps the
            # documented #798/#820 degraded-path caveat.
            arg_instrs_list.append(arg_instrs)
            arg_wasm_types.append(arg_wt)

        # Compute field offsets from concrete argument types.  A `"unit"`
        # field is zero-size: it neither aligns nor advances the offset.
        _sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8, "unit": 0}
        _aligns = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4, "unit": 1}
        offset = 4  # after tag (i32, 4 bytes)
        field_offsets: list[tuple[int, str]] = []
        for wt in arg_wasm_types:
            align = _aligns.get(wt, 8)
            offset = (offset + align - 1) & ~(align - 1)  # align up
            field_offsets.append((offset, wt))
            offset += _sizes.get(wt, 8)
        total_size = ((offset + 7) & ~7) if offset > 0 else 8  # 8-byte aligned

        self.needs_alloc = True
        tmp = self.alloc_local("i32")
        instructions: list[str] = [
            f"i32.const {total_size}",
            "call $alloc",
            f"local.tee {tmp}",
            f"i32.const {layout.tag}",
            "i32.store",
            *gc_shadow_push(tmp),
        ]

        # #820: the BUILTIN `Tuple` carrier is variadic — its registered layout
        # has no per-field metadata (`field_offsets` / `int_fields` are `()`, the
        # real layout being recomputed per call).  Recover the construction's
        # target component types (`Tuple<Int, Int>`) from the threaded target-type
        # table so a @Nat component widening into an @Int tuple slot is guarded AT
        # CONSTRUCTION (the #813-disclosed widening residual the enabler
        # unlocks — the widening dual of #758's tuple-component narrowing).  A
        # generic ADT field (`Some(@Nat.0)` -> `Option<Int>`) is NOT this path —
        # it goes through `layout.int_fields` (empty for a generic field, so it
        # stays E531-disclosed, #757).
        #
        # FIX-3: a USER `data Tuple<A, B>` also matches `expr.name == "Tuple"`,
        # but its layout is a FIXED user ADT (non-empty `field_offsets`, built
        # parallel to its declared fields) — the verifier routes such a
        # construction through the generic-ctor-field path and emits NO coerce
        # obligation, so taking the tuple-target path here would emit a widen
        # guard the verifier never obligated (an opposite-direction desync that
        # trapped a legal @Nat).  Discriminate the builtin variadic carrier
        # (empty `field_offsets`) from the user ADT, so only the builtin carrier
        # uses the target table; the user Tuple's generic fields stay unguarded
        # via the (empty) `int_fields` path, exactly like any other generic ADT.
        tuple_target = (
            self._target_codegen_type_full(expr)
            if (expr.name == "Tuple" and not layout.field_offsets)
            else None
        )

        # Store each field at its computed offset
        for i, (fo, wt) in enumerate(field_offsets):
            if wt == "unit":
                # Zero-size Unit field: emit the argument for its side effects
                # (a `()` literal is empty; a Unit-returning call still runs),
                # but there is nothing on the stack to store and no bytes to
                # occupy — no `local.get`, no store.
                instructions.extend(arg_instrs_list[i])
            elif wt == "i32_pair":
                # Pair type (String, Array<T>): store (ptr, len) as two i32s
                tmp_val_ptr = self.alloc_local("i32")
                tmp_val_len = self.alloc_local("i32")
                instructions.extend(arg_instrs_list[i])
                instructions.append(f"local.set {tmp_val_len}")
                instructions.append(f"local.set {tmp_val_ptr}")
                instructions.append(f"local.get {tmp}")
                instructions.append(f"local.get {tmp_val_ptr}")
                instructions.append(f"i32.store offset={fo}")
                instructions.append(f"local.get {tmp}")
                instructions.append(f"local.get {tmp_val_len}")
                instructions.append(f"i32.store offset={fo + 4}")
            else:
                instructions.append(f"local.get {tmp}")
                field_val = arg_instrs_list[i]
                # #747: runtime-guard an @Int -> @Nat narrowing into a
                # concrete @Nat constructor field (`WrapN(@Int.0)` where
                # `WrapN(Nat)`).  Generic fields instantiated to @Nat erase
                # to i64 here (no `nat_fields` flag), so they stay
                # statically-only — the verifier obligates them.
                if (i < len(layout.nat_fields) and layout.nat_fields[i]
                        and self._narrows_into_nat(expr.args[i])):
                    field_val = self._emit_nat_bind_guard(field_val)
                # #813: dual — runtime-guard a @Nat -> @Int widening into a
                # concrete @Int constructor field (`WrapI(@Nat.0)` where
                # `WrapI(Int)`); a @Nat above i64.MAX would otherwise be stored
                # and later extracted as a reinterpreted negative @Int.  #820
                # extends this to a `Tuple<..., Int, ...>` component, whose @Int
                # target comes from `tuple_target` rather than `int_fields`.
                elif (((i < len(layout.int_fields) and layout.int_fields[i])
                        or self._adt_arg_is_int(tuple_target, i))
                        and self._result_is_nat(expr.args[i])):
                    field_val = self._emit_int_widen_guard(field_val)
                instructions.extend(field_val)
                instructions.append(f"{wt}.store offset={fo}")

        # Leave pointer as result
        instructions.append(f"local.get {tmp}")
        return instructions

    def _ctor_field_targets_byte(
        self, expr: ast.ConstructorCall, field_i: int,
    ) -> bool:
        """Whether constructor field ``field_i`` is a type-parameter field
        instantiated at ``@Byte`` by the construction's TARGET type (#1092).

        Decides the literal-width coercion in
        :py:meth:`_translate_constructor_call`: the literal alone cannot —
        ``MkB(0)`` is equally legal as ``Box<Int>`` (i64 field) and as
        ``Box<Byte>`` (i32 field); only the checker-recorded target type
        (``_target_codegen_type_full``, the #820 side-table) knows which.
        The target's argument name is grounded through the shared
        canonicalizer so an alias spelling (``Box<MB>``, ``type MB =
        Byte;``) instantiates like the literal ``Byte``.  Conservative
        ``False`` when the field is not a bare type parameter, the table is
        unthreaded, or the target carries no matching argument — the
        literal then keeps its i64 translation (the pre-#1092 behaviour).
        """
        tp_idx = self._ctor_adt_tp_indices.get(expr.name)
        if not tp_idx or field_i >= len(tp_idx):
            return False
        pos = tp_idx[field_i]
        if pos is None:
            return False  # concrete declared field (a literal there is E213)
        target = self._target_codegen_type_full(expr)
        args = getattr(target, "type_args", None)
        if not args or pos >= len(args):
            return False
        arg_ty = args[pos]
        base = getattr(arg_ty, "base", arg_ty)  # unwrap a refinement
        name = getattr(base, "name", None)
        if name is None:
            return False
        return self._canonical_field_type(name) == "Byte"

    # -----------------------------------------------------------------
    # Let destructuring
    # -----------------------------------------------------------------

    def _translate_let_destruct(
        self, stmt: ast.LetDestruct, env: WasmSlotEnv
    ) -> tuple[list[str], WasmSlotEnv] | None:
        """Translate ``let Ctor<@T1, @T2> = expr;`` into field extractions.

        Works for any single-constructor ADT (Tuple, UrlParts, user-defined).
        The algorithm mirrors ``_extract_constructor_fields`` but iterates
        over ``stmt.type_bindings`` (TypeExpr items) instead of match
        sub-patterns.
        """
        # Translate the value expression — should produce a heap pointer (i32)
        val_instrs = self.translate_expr(stmt.value, env)
        if val_instrs is None:
            return None

        # Save to a local
        scr_local = self.alloc_local("i32")
        instrs: list[str] = list(val_instrs)
        instrs.append(f"local.set {scr_local}")

        # #820: a @Nat component destructured into an @Int binding
        # (`let Tuple<@Int> = Tuple(@Nat.0)`) widens it — the tuple-component
        # dual of construction.  The widening reinterprets its bit pattern above
        # i64.MAX (u64.MAX -> -1) at the read into the @Int slot.  Mirror the
        # verifier's literal-source tuple-destructure path EXACTLY (a literal
        # ``Tuple(...)`` whose i-th arg `_result_is_nat` and whose i-th binding
        # is @Int): guard the field load.  A non-literal source is NOT obligated
        # by the verifier here, so codegen leaves it unguarded (no mismatch).
        destr_lit_args: tuple[ast.Expr, ...] = (
            stmt.value.args
            if isinstance(stmt.value, ast.ConstructorCall)
            and stmt.value.name == stmt.constructor
            else ()
        )

        # Extract each field using the same offset algorithm as constructors
        _sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8}
        _aligns = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4}
        offset = 4  # skip past tag (i32, 4 bytes)
        new_env = env

        for idx, te in enumerate(stmt.type_bindings):
            type_name = self._type_expr_to_slot_name(te)
            if type_name is None:
                raise CodegenSkip(
                    stmt, "let-destruct binding type has no slot name"
                )
            # Zero-size bindings (Unit, transparent Future<Unit>, …): no WASM
            # representation — bind nothing and advance no offset, exactly like
            # a zero-size constructor field.  Keyed on erasure, not the bare
            # string "Unit" (#1031), so Future<Unit> erases like Unit instead of
            # skipping the whole function.
            if self._slot_name_erases_to_unit(type_name):
                continue
            # Pair types (String, Array<T>): two consecutive i32 locals
            if self._is_pair_type_name(type_name):
                align = _aligns["i32"]
                offset = (offset + align - 1) & ~(align - 1)
                ptr_local = self.alloc_local("i32")
                len_local = self.alloc_local("i32")
                instrs.append(f"local.get {scr_local}")
                instrs.append(f"i32.load offset={offset}")
                instrs.append(f"local.set {ptr_local}")
                instrs.append(f"local.get {scr_local}")
                instrs.append(f"i32.load offset={offset + 4}")
                instrs.append(f"local.set {len_local}")
                # PR #707 review: same pair-type rooting
                # gap as ``_extract_constructor_fields`` — String
                # buffer / Array<T> backing ptr needs shadow-push.
                # ``let MyAdt(@String, ...) = ...;`` was missed by
                # the original #705 fix (which only covered the
                # ``wt == "i32"`` non-inline branch).
                self.needs_alloc = True
                instrs.extend(gc_shadow_push(ptr_local))
                new_env = new_env.push(type_name, ptr_local)
                offset += 8
                continue
            wt = self._slot_name_to_wasm_type(type_name)
            if wt is None:
                raise CodegenSkip(
                    stmt,
                    f"let-destruct type {type_name!r} has no WASM representation",
                )
            align = _aligns.get(wt, 8)
            offset = (offset + align - 1) & ~(align - 1)
            local_idx = self.alloc_local(wt)
            load = [
                f"local.get {scr_local}",
                f"{wt}.load offset={offset}",
            ]
            # #747: runtime-guard an @Int -> @Nat destructure component the
            # verifier could not discharge `>= 0` statically (Tier 3), or
            # when codegen runs without `vera verify`.  Conservative — every
            # @Nat target slot is guarded, since the *source* component type
            # is not threaded into codegen — but it only ever traps on a
            # genuinely negative i64, never on a valid @Nat in [0, 2^63).
            # `_resolve_base_type_name` so a `type Age = Nat` alias / refined
            # @Nat target is guarded too (CR #756), matching the alias-aware
            # call-arg / ctor-field metadata.
            if self._resolve_base_type_name(type_name) == "Nat":
                load = self._emit_nat_bind_guard(load)
            # #820: a @Nat component destructured into an @Int slot
            # (`let Tuple<@Int> = Tuple(@Nat.0)`) is a tuple-component widening —
            # guard the field load when the target binding is @Int and the
            # literal source arg is provably @Nat, mirroring the verifier's
            # literal-source tuple-destructure obligation (was E531-disclosed).
            elif (self._resolve_base_type_name(type_name) == "Int"
                    and idx < len(destr_lit_args)
                    and self._result_is_nat(destr_lit_args[idx])):
                load = self._emit_int_widen_guard(load)
            instrs.extend(load)
            instrs.append(f"local.set {local_idx}")
            # PR #707 review: same heap-pointer rooting
            # discipline as ``_extract_constructor_fields`` (line ~515)
            # and the ``BindingPattern`` branch (line ~408).
            # ``let MyAdt(@Json) = makeThing();`` extracts an i32 field
            # into a fresh local that's invisible to the conservative
            # scan until shadow-pushed.  Without this, a subsequent
            # allocation can reclaim the bound heap pointer.  This was
            # missed by the original #705 fix — match-arm paths were
            # rooted but the parallel let-destruct path was not.
            if wt == "i32" and type_name not in _INLINE_I32_TYPES:
                self.needs_alloc = True
                instrs.extend(gc_shadow_push(local_idx))
            new_env = new_env.push(type_name, local_idx)
            offset += _sizes.get(wt, 8)

        return (instrs, new_env)

    # -----------------------------------------------------------------
    # Match expressions
    # -----------------------------------------------------------------

    def _translate_match(
        self, expr: ast.MatchExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a match expression to WAT.

        Evaluates the scrutinee once, saves to a local, then emits a
        chained if-else cascade for each arm.

        A PAIR-represented scrutinee (``String`` / ``Array<T>``, #1305) takes
        TWO consecutive i32 locals — the same (ptr, len) convention parameters
        and constructor fields already use, with the env holding the pointer
        half and the length at ``ptr + 1``.  ``alloc_local("i32_pair")`` would
        otherwise write the internal pseudo-type verbatim into the locals
        declaration (``(local $l1 i32_pair)``), which is not a WAT value type,
        so the whole module failed to assemble — on programs as ordinary as
        ``match @String.0 { @String -> string_length(@String.0) }``.
        """
        # Translate scrutinee
        scr_instrs = self.translate_expr(expr.scrutinee, env)
        if scr_instrs is None:
            return None

        scr_wasm_type = self._infer_expr_wasm_type(expr.scrutinee)
        if scr_wasm_type is None:
            raise CodegenSkip(
                expr.scrutinee,
                "could not infer match scrutinee WASM type",
            )

        # Type-check rejects empty match expressions, but a cross-module
        # import could still hand us one (#626 audit borderline).  Raise
        # CodegenSkip with the MatchExpr's span rather than the legacy
        # silent-bail-through-_compile_match_arms.
        if not expr.arms:
            raise CodegenSkip(expr, "match expression has no arms")

        # Save scrutinee to a local
        instructions: list[str] = list(scr_instrs)
        if scr_wasm_type == "i32_pair":
            # A WHITELIST, deliberately: exactly two pattern kinds have a
            # lowering over a pair, and every other kind must be refused
            # here rather than reach an emitter that will read one of the
            # two words as something it is not.  A blacklist naming the
            # constructor kinds was the first cut of this guard and was
            # strictly worse than the bug it was added beside — a pair has
            # no comparable scalar word either, so `true ->` and `1 ->`
            # fell through into the arm-condition emitter and compiled the
            # scrutinee's heap POINTER as the condition: `match @String.0 {
            # true -> 100, _ -> 200 }` went from a loud WAT failure to a
            # check-green program that exits 0 and prints 100, and the
            # integer twin shipped a `.wasm` that died at instantiation
            # with no diagnostic at all.  Enumerating what IS lowerable
            # cannot fail that way when a pattern kind is added.
            for arm in expr.arms:
                if not isinstance(
                    arm.pattern,
                    (ast.WildcardPattern, ast.BindingPattern),
                ):
                    raise CodegenSkip(
                        arm.pattern,
                        "pattern over a scrutinee whose representation is a "
                        "(ptr, len) pair — only a wildcard or a binding "
                        "pattern lowers over one, since a pair carries "
                        "neither a constructor tag nor a comparable scalar "
                        "word",
                    )
            ptr_local = self.alloc_local("i32")
            len_local = self.alloc_local("i32")  # consecutive: ptr + 1
            instructions.append(f"local.set {len_local}")
            instructions.append(f"local.set {ptr_local}")
            # NOT rooted (#1322).  ``ptr_local`` is a COPY of the address the
            # scrutinee expression just produced, and every producer of a heap
            # pointer already roots it: a parameter in the function prologue,
            # an allocation at its ``$alloc`` site, a call's result in the
            # callee's epilogue, a ``let`` at its binding.  The shadow stack
            # roots ADDRESSES, not locals, so a second push of the same
            # address buys the mark phase nothing — while costing a slot for
            # the whole frame.  Two pushes of one address is what took a
            # ``String``-scrutinee recursion to three roots per frame and a
            # bare `unreachable` at depth 1 364.
            #
            # The rooting these replaced was already documented as defensive
            # rather than load-bearing: "with both pushes deleted the whole
            # suite, the GC rooting and reclamation suites, and four
            # allocate-inside-the-arm probes under VERA_EAGER_GC=1 all stay
            # green".  What makes deleting them SAFE rather than merely
            # untested is the producer's root staying live across the arm,
            # which ``_scope_match_shadow_roots`` now guarantees: its
            # ``$gc_sp`` snapshot is taken BEFORE the scrutinee, so anything
            # the scrutinee rooted is reclaimed only once the arm is done.
            #
            # The non-pair bindings below are a different case and keep their
            # pushes: a constructor FIELD load produces an address that lives
            # in no other local, so #705/#707 are load-bearing there.
            scr_local = ptr_local
        else:
            scr_local = self.alloc_local(scr_wasm_type)
            instructions.append(f"local.set {scr_local}")

        # Infer result type of the match
        result_type = self._infer_match_result_type(expr)

        # #820: a HETEROGENEOUS @Int-join match (a @Nat arm body alongside a
        # genuine @Int-slot arm body) widens each @Nat arm into the @Int join.
        # The whole-match boundary guard cannot fire (it would false-trap the
        # @Int arm), so guard the @Nat arm(s) PER-ARM.  `_is_hetero_int_widen_join`
        # is the shared gate: i64 join, NOT wholly @Nat (`_result_is_nat`), AND
        # TARGET @Int (FIX-4 — without the target check this false-trapped a
        # legal @Nat arm of a hetero join in a @Nat-RETURNING context).  The same
        # gate drives the FIX-1 tail-call collector, so the two stay in lockstep.
        guard_widen_arms = self._is_hetero_int_widen_join(expr)

        # #1060: the scrutinee's CONCRETE Vera type (e.g. "Box<Unit>") drives the
        # instantiation-aware width of a WILDCARD over a bare type-parameter
        # field — that field registers generically as i32 but is laid out per
        # the concrete type arg at construction (Unit → 0 bytes).  #1065: a
        # DIRECT-CALL scrutinee recovers its full instantiation from the callee's
        # declared return type (`_infer_vera_type` alone drops the type args and
        # a type-parameter wildcard then LOUD-skipped a check-green program);
        # None only when the type is genuinely unrecoverable, and a
        # type-parameter wildcard still LOUD-skips rather than reading a shifted
        # offset.
        scrutinee_type = self._match_scrutinee_vera_type(expr.scrutinee)

        # Compile arms as chained if-else
        arm_instrs = self._compile_match_arms(
            expr.arms, scr_local, scr_wasm_type, result_type, env,
            expr.scrutinee, guard_widen_arms=guard_widen_arms,
            scrutinee_type=scrutinee_type,
        )
        if arm_instrs is None:
            return None

        instructions.extend(arm_instrs)
        return self._scope_match_shadow_roots(expr, instructions, result_type)

    def _scope_match_shadow_roots(
        self,
        expr: ast.MatchExpr,
        instructions: list[str],
        result_type: str | None,
    ) -> list[str]:
        """Give a match's GC shadow roots ARM lifetime instead of FRAME
        lifetime (#1322).

        Every root this match pushes — the pair scrutinee's pointer half, each
        arm's pattern bindings, every allocation an arm body makes — is dead
        once the arm has produced its value.  Nothing popped them: the only
        reclamation was the function epilogue's ``$gc_sp`` restore, which runs
        once, at frame exit.  A ``let``'s frame lifetime is correct (the
        binding is live to the end of its block); a match arm's is not, so a
        frame holding K sequential matches held 3K roots of which at most
        three were live, and a recursion multiplied that by its depth.  With
        the shadow stack at 4 096 roots the ceiling moved with K — measured
        over a ``String`` scrutinee: 1 023 levels at K=1, 584 at K=2, 314 at
        K=4 — and overflow is a bare ``unreachable`` from
        :func:`gc_shadow_push`'s bound check: no diagnostic, no location, on a
        program ``check`` and ``verify`` both pass.

        The discipline is the function epilogue's, verbatim (``gc_prologue`` /
        ``gc_epilogue`` in ``vera/codegen/functions.py``): snapshot ``$gc_sp``
        before the scrutinee, restore it after the arm cascade, and re-root
        the arm's result when the result is a heap pointer.  What survives the
        match is then exactly the one value the match produced — and anything
        that value reaches, which the conservative mark phase finds from it.

        Emitted ONLY when this match actually pushed
        (:func:`contains_shadow_push`).  That is not an optimization: a
        function whose lowering never sets ``needs_alloc`` gets no ``$gc_sp``
        global at all, so an unconditional wrapper would emit a
        ``global.get $gc_sp`` with nothing to read.  It also keeps the emitted
        WAT of every non-rooting match byte-identical.

        The save is placed before the SCRUTINEE, not after it: a scrutinee
        that allocates (``match json_keys(j) { … }``) roots its own result,
        and that root dies with the match too.  Roots pushed by anything
        lowered EARLIER — a preceding call argument, an enclosing ``let`` —
        sit below the snapshot and are untouched.
        """
        if not contains_shadow_push(instructions):
            return instructions
        save_local = self.alloc_local("i32")
        scoped = ["global.get $gc_sp", f"local.set {save_local}"]
        scoped.extend(instructions)
        restore = [f"local.get {save_local}", "global.set $gc_sp"]
        if result_type == "i32_pair":
            # A (ptr, len) result: the pointer half is a heap pointer by
            # construction (the pair convention has no non-pointer form).
            ret_ptr = self.alloc_local("i32")
            ret_len = self.alloc_local("i32")
            scoped.append(f"local.set {ret_len}")
            scoped.append(f"local.set {ret_ptr}")
            scoped.extend(restore)
            scoped.extend(gc_shadow_push(ret_ptr))
            scoped.append(f"local.get {ret_ptr}")
            scoped.append(f"local.get {ret_len}")
        elif result_type is not None:
            ret_local = self.alloc_local(result_type)
            scoped.append(f"local.set {ret_local}")
            scoped.extend(restore)
            if result_type == "i32" and self._match_result_is_pointer(expr):
                scoped.extend(gc_shadow_push(ret_local))
            scoped.append(f"local.get {ret_local}")
        else:
            # Void match — the cascade carries no result annotation and
            # leaves nothing on the operand stack.
            scoped.extend(restore)
        return scoped

    def _match_result_is_pointer(self, expr: ast.MatchExpr) -> bool:
        """Whether an ``i32``-lowered match result must be re-rooted (#1322).

        Decided by :func:`is_gc_pointer_base` over the REPRESENTATION base of
        the match's Vera type — the same rule, from the same function, that
        the function and closure epilogues use for their return values, so
        the three cannot drift.

        Defaults to ``True`` when the Vera type is unrecoverable.  The two
        errors are not symmetric: re-rooting a non-pointer costs one shadow
        slot and one candidate the mark phase's heap-range guard rejects,
        while failing to re-root a pointer hands the arm's result to the next
        collection.  An unknown type takes the inert error.
        """
        vera_type = self._infer_vera_type(expr)
        if vera_type is None:
            return True
        head = vera_type.split("<", 1)[0]
        return is_gc_pointer_base(self._resolve_base_type_name(head))

    def _match_scrutinee_vera_type(self, scrutinee: ast.Expr) -> str | None:
        """Concrete Vera type of a match scrutinee for the #1060 wildcard walks.

        A ``SlotRef`` scrutinee (``@Box<Unit>.0``) already carries its concrete
        type args, which ``_infer_vera_type`` renders in full.  A DIRECT-CALL
        scrutinee (``mk()``) does NOT: ``_infer_fncall_vera_type`` returns the
        bare base head (``"Box"``) for a parameterized i32-pointer return (#911),
        dropping the ``<Unit>`` a type-parameter WILDCARD needs to recompute its
        erased width — so the #1060 walk LOUD-skipped (E602) a check-green
        program on a shape the slot form compiled correctly (#1065).

        For a NON-generic direct-call scrutinee the callee's DECLARED return type
        IS the concrete instantiation — a non-generic signature mentions no type
        variables, so ``mk() -> @Box<Unit>`` declares exactly ``Box<Unit>``.
        Recover it from ``_fn_ret_type_exprs`` (the same #614/#878 declared-return
        registry other consultors read, populated by ``_register_fn`` in both the
        CLI and the ``transform -> compile`` test-harness path) and render it in
        full, matching the SlotRef form so the wildcard walks receive an
        identical concrete type.  A non-parameterized return (``ret_te.type_args``
        empty) needs no recovery and falls through unchanged.

        A GENERIC callee's declared return carries type variables
        (``forall<T> fn wrap(@T -> @P2<T, Unit>)``) — #1072 resolves them from
        the call site via the same ``_unify_param_arg_wasm`` unification the
        generic call-rewrite performs, then renders the substituted return in
        full (``P2<Int, Unit>``).  On main this family read shifted offsets
        SILENTLY (the pre-#1060 walk); the #1049 stack made it a sound
        LOUD-skip; now it compiles like the slot form.  An unresolved variable
        falls through to ``_infer_vera_type`` — whose bare base head keeps the
        wildcard walk's LOUD-skip (sound) — though no check-green shape reaches
        it (var-at-Unit is E206-rejected, a phantom-var callee is E121-rejected).

        A MODULE-qualified callee (``boxlib::mk()``, #1073) resolves through
        the single shared target resolver (``_resolve_module_call_wasm_name``,
        the #774-reviewed source of truth that CONSUMES ``path`` — no wrong
        same-name-local lookup, mirroring ``_infer_vera_type``'s ModuleCall
        arm) and recurses with the resolved-name ``FnCall``: the bare or
        ``mod$…`` name of a non-generic import is in ``_fn_ret_type_exprs``,
        a shadowed generic resolves to its per-instantiation clone whose
        registered declared return is already substituted, and anything
        unregistered falls through to the sound LOUD-skip.
        """
        if isinstance(scrutinee, ast.ModuleCall):
            target = self._resolve_module_call_wasm_name(scrutinee)
            return self._match_scrutinee_vera_type(ast.FnCall(
                name=target, args=scrutinee.args, span=scrutinee.span))
        if isinstance(scrutinee, ast.FnCall):
            if scrutinee.name in self._generic_fn_info:
                rendered = self._generic_call_ret_vera_type(scrutinee)
                if rendered is not None:
                    return rendered
            elif scrutinee.name in self._fn_ret_type_exprs:
                ret_te = self._fn_ret_type_exprs[scrutinee.name]
                if isinstance(ret_te, ast.RefinementType):
                    ret_te = ret_te.base_type
                if isinstance(ret_te, ast.NamedType) and ret_te.type_args:
                    return self._format_named_type(ret_te)
        return self._infer_vera_type(scrutinee)

    def _generic_call_ret_vera_type(self, call: ast.FnCall) -> str | None:
        """Render a GENERIC call's declared return with its type variables
        resolved from the call site (#1072) — ``wrap(5)`` against
        ``forall<T> fn wrap(@T -> @P2<T, Unit>)`` yields ``"P2<Int, Unit>"``.

        Unifies each parameter TypeExpr against its argument exactly as the
        generic call-rewrite does (``_unify_param_arg_wasm``), substitutes the
        bound variables into the declared return, and renders the full name.
        Returns ``None`` — caller falls back to ``_infer_vera_type`` — when the
        return is not a parameterized ``NamedType`` (nothing to recover) or any
        variable in it stays unbound (the render must never guess: a wrong
        concrete type would put the wildcard walk back on a shifted offset,
        whereas the bare-head fallback keeps the sound LOUD-skip).
        """
        ret_te: ast.TypeExpr | None = self._fn_ret_type_exprs.get(call.name)
        if isinstance(ret_te, ast.RefinementType):
            ret_te = ret_te.base_type
        if not (isinstance(ret_te, ast.NamedType) and ret_te.type_args):
            return None
        forall_vars, param_types = self._generic_fn_info[call.name]
        constrained_vars = self._generic_constrained_vars.get(
            call.name, frozenset())
        mapping: dict[str, str] = {}
        for pt, arg in zip(param_types, call.args):
            self._unify_param_arg_wasm(
                pt, arg, forall_vars, mapping, constrained_vars)
        return self._render_type_substituted(ret_te, forall_vars, mapping)

    def _render_type_substituted(
        self,
        te: ast.TypeExpr,
        forall_vars: tuple[str, ...],
        mapping: dict[str, str],
    ) -> str | None:
        """Render *te* as a full Vera type name with every forall variable
        replaced by its call-site binding (#1072) — the substituting sibling of
        ``_format_named_type``, which renders names verbatim.

        A leaf that is a forall variable renders its ``mapping`` binding —
        ``None`` (propagated to the caller) when unbound, so an unresolved
        instantiation is never guessed.  Concrete leaves render verbatim;
        parameterized nodes recurse into their type args.  A non-``NamedType``
        node (after refinement unwrap) is unrenderable → ``None``.
        """
        if isinstance(te, ast.RefinementType):
            te = te.base_type
        if not isinstance(te, ast.NamedType):
            return None
        if not te.type_args:
            if te.name in forall_vars:
                return mapping.get(te.name)
            return te.name
        if te.name in forall_vars:
            # A parameterized node whose HEAD is a type variable — Vera type
            # vars are not higher-kinded, so this cannot arise from a checked
            # program; refuse to render rather than emit a var-headed name.
            return None
        parts = []
        for ta in te.type_args:
            rendered = self._render_type_substituted(ta, forall_vars, mapping)
            if rendered is None:
                return None
            parts.append(rendered)
        return f"{te.name}<{', '.join(parts)}>"

    def _infer_match_result_type(
        self, expr: ast.MatchExpr
    ) -> str | None:
        """Infer the WASM result type from the first arm body."""
        for arm in expr.arms:
            wt = self._infer_expr_wasm_type(arm.body)
            if wt is not None:
                return wt
        return None

    def _compile_match_arms(
        self,
        arms: tuple[ast.MatchArm, ...],
        scr_local: int,
        scr_wasm_type: str,
        result_type: str | None,
        env: WasmSlotEnv,
        scrutinee: ast.Expr | None = None,
        *,
        guard_widen_arms: bool = False,
        scrutinee_type: str | None = None,
    ) -> list[str] | None:
        """Compile match arms as a chained if-else cascade.

        *scrutinee* is the match scrutinee expression (#813): threaded so a
        top-level binding pattern can tell whether the bound value is @Nat
        (`_result_is_nat`) and thus needs the @Nat -> @Int widening guard.

        *scrutinee_type* (#1060) is that scrutinee's concrete Vera type name
        (e.g. "Box<Unit>"), threaded so a WILDCARD over a bare type-parameter
        field advances by the concrete (instantiation-aware) width, not the
        generic i32 placeholder.

        *guard_widen_arms* (#820) is True for a heterogeneous @Int-join match:
        each arm body that is intrinsically @Nat (`_result_is_nat`) widens into
        the @Int join and is wrapped with the boundary guard PER-ARM.
        """
        if not arms:
            return None

        arm = arms[0]
        remaining = arms[1:]

        # Check if this arm needs a condition
        cond = self._translate_match_condition(
            arm.pattern, scr_local, scr_wasm_type, scrutinee_type,
        )

        if cond is None or not remaining:
            # Unconditional arm (catch-all) or last arm — emit directly
            setup = self._setup_match_arm_env(
                arm.pattern, scr_local, scr_wasm_type, env, scrutinee,
                scrutinee_type,
            )
            if setup is None:
                return None
            setup_instrs, arm_env = setup
            body = self.translate_expr(arm.body, arm_env)
            if body is None:
                return None
            # #758/#983 — guard a narrowing @Nat-return leaf inline (a bare-expr
            # arm body IS the leaf; a Block arm body's leaf is its trailing expr,
            # guarded in `translate_block`, so this no-ops on that id).
            body = self._guard_nat_return_leaf(arm.body, body)
            if guard_widen_arms and self._result_is_nat(arm.body):
                body = self._emit_int_widen_guard(body)
            return setup_instrs + body

        # Conditional arm with more arms following
        setup = self._setup_match_arm_env(
            arm.pattern, scr_local, scr_wasm_type, env, scrutinee,
            scrutinee_type,
        )
        if setup is None:
            return None
        setup_instrs, arm_env = setup
        body = self.translate_expr(arm.body, arm_env)
        if body is None:
            return None
        # #758/#983 — per-leaf narrowing @Nat-return guard (see the catch-all
        # arm above); no-ops unless this arm body is a collected narrowing leaf.
        body = self._guard_nat_return_leaf(arm.body, body)
        if guard_widen_arms and self._result_is_nat(arm.body):
            body = self._emit_int_widen_guard(body)

        # Compile remaining arms (else branch)
        else_instrs = self._compile_match_arms(
            remaining, scr_local, scr_wasm_type, result_type, env, scrutinee,
            guard_widen_arms=guard_widen_arms, scrutinee_type=scrutinee_type,
        )
        if else_instrs is None:
            return None

        # Build if-else block
        if result_type == "i32_pair":
            result_annot = " (result i32 i32)"
        elif result_type:
            result_annot = f" (result {result_type})"
        else:
            result_annot = ""
        instrs: list[str] = list(cond)
        instrs.append(f"if{result_annot}")
        for i in setup_instrs:
            instrs.append(f"  {i}")
        for i in body:
            instrs.append(f"  {i}")
        instrs.append("else")
        for i in else_instrs:
            instrs.append(f"  {i}")
        instrs.append("end")
        return instrs

    def _translate_match_condition(
        self,
        pattern: ast.Pattern,
        scr_local: int,
        scr_wasm_type: str,
        scrutinee_type: str | None = None,
    ) -> list[str] | None:
        """Emit i32 condition for a pattern check.

        Returns None for unconditional patterns (wildcard/binding).

        *scrutinee_type* (#1060) is the scrutinee's concrete Vera type name,
        threaded into the nested tag-check walk so a WILDCARD over a bare
        type-parameter field before a nested constructor sub-pattern advances
        the offset by the concrete width (Unit → 0 bytes), keeping the nested
        tag load on the right address.
        """
        if isinstance(pattern, (ast.NullaryPattern, ast.ConstructorPattern)):
            name = pattern.name
            layout = self._ctor_layouts.get(name)
            if layout is None:
                raise CodegenSkip(
                    pattern,
                    f"unknown constructor {name!r} in match pattern",
                )
            instrs = [
                f"local.get {scr_local}",
                "i32.load",
                f"i32.const {layout.tag}",
                "i32.eq",
            ]
            # AND-chain nested tag checks for constructor sub-patterns
            if isinstance(pattern, ast.ConstructorPattern):
                nested = self._collect_nested_tag_checks(
                    pattern, scr_local, layout, scrutinee_type,
                )
                if nested is None:
                    return None
                for check in nested:
                    instrs.extend(check)
                    instrs.append("i32.and")
            return instrs

        if isinstance(pattern, ast.BoolPattern):
            if pattern.value:
                return [f"local.get {scr_local}"]
            else:
                return [f"local.get {scr_local}", "i32.eqz"]

        if isinstance(pattern, ast.IntPattern):
            return [
                f"local.get {scr_local}",
                f"i64.const {pattern.value}",
                "i64.eq",
            ]

        # WildcardPattern, BindingPattern — unconditional
        return None

    def _setup_match_arm_env(
        self,
        pattern: ast.Pattern,
        scr_local: int,
        scr_wasm_type: str,
        env: WasmSlotEnv,
        scrutinee: ast.Expr | None = None,
        scrutinee_type: str | None = None,
    ) -> tuple[list[str], WasmSlotEnv] | None:
        """Extract fields and set up environment bindings for a match arm.

        Returns (instructions, new_env) or None on failure.

        *scrutinee_type* (#1060) is the scrutinee's concrete Vera type name,
        forwarded to the field-extraction walk so a WILDCARD over a bare
        type-parameter field advances the offset by the instantiation-aware
        width instead of the generic i32 placeholder.
        """
        if isinstance(pattern, (ast.WildcardPattern, ast.NullaryPattern,
                                ast.BoolPattern, ast.IntPattern)):
            return ([], env)

        if isinstance(pattern, ast.BindingPattern):
            # Bind the scrutinee itself to a new local
            type_name = self._type_expr_to_slot_name(pattern.type_expr)
            if type_name is None:
                raise CodegenSkip(
                    pattern,
                    "binding pattern type has no slot name",
                )
            if scr_wasm_type == "i32_pair":
                # #1305: a pair scrutinee lives in two consecutive locals
                # (``scr_local`` = ptr, ``scr_local + 1`` = len), so the
                # binding takes two of its own.  Copying only the pointer
                # would bind a length-free String and read garbage.
                ptr_local = self.alloc_local("i32")
                len_local = self.alloc_local("i32")  # consecutive: ptr + 1
                instrs = [
                    f"local.get {scr_local}",
                    f"local.set {ptr_local}",
                    f"local.get {scr_local + 1}",
                    f"local.set {len_local}",
                ]
                # NOT rooted (#1322), for the same reason the scrutinee copy
                # in ``_translate_match`` is not: this local receives the
                # scrutinee's address verbatim, and the shadow stack roots
                # addresses.  See the note there.
                return (instrs, env.push(type_name, ptr_local))
            local_idx = self.alloc_local(scr_wasm_type)
            bind_val = [f"local.get {scr_local}"]
            # #747: runtime-guard a top-level `match <Int> { @Nat -> ... }`
            # narrowing — the scrutinee binds as @Nat, so trap if it is a
            # negative i64 (Tier-3 backstop; never trips on a valid @Nat).
            # Alias-aware (`type Age = Nat`) via `_resolve_base_type_name`
            # (CR #756).
            if (self._resolve_base_type_name(type_name) == "Nat"
                    and scr_wasm_type == "i64"):
                bind_val = self._emit_nat_bind_guard(bind_val)
            # #813: dual — `match @Nat.0 { @Int -> … }` binds a @Nat scrutinee
            # into an @Int slot, widening it.  Guard only when the scrutinee is
            # provably @Nat (`_result_is_nat`), never a genuine @Int scrutinee
            # (which can be legitimately negative).
            elif (self._resolve_base_type_name(type_name) == "Int"
                    and scr_wasm_type == "i64"
                    and scrutinee is not None
                    and self._result_is_nat(scrutinee)):
                bind_val = self._emit_int_widen_guard(bind_val)
            instrs = [
                *bind_val,
                f"local.set {local_idx}",
            ]
            # PR #707 review: same heap-pointer rooting
            # discipline as ``_extract_constructor_fields`` (below) —
            # ``match @Json.0 { @Json -> set_add(set_new(), @Json.0) }``
            # binds the scrutinee to a fresh local that's invisible
            # to the conservative scan until shadow-pushed.  Without
            # this, the inner ``set_new()`` allocation can reclaim
            # the bound Json block.
            if (
                scr_wasm_type == "i32"
                and type_name not in _INLINE_I32_TYPES
            ):
                self.needs_alloc = True
                instrs.extend(gc_shadow_push(local_idx))
            new_env = env.push(type_name, local_idx)
            return (instrs, new_env)

        if isinstance(pattern, ast.ConstructorPattern):
            layout = self._ctor_layouts.get(pattern.name)
            if layout is None:
                raise CodegenSkip(
                    pattern,
                    f"unknown constructor {pattern.name!r} in match arm pattern",
                )
            return self._extract_constructor_fields(
                pattern, scr_local, layout, env, scrutinee_type,
            )

        raise CodegenSkip(
            pattern,
            f"unsupported match pattern type {type(pattern).__name__}",
        )

    def _extract_constructor_fields(
        self,
        pattern: ast.ConstructorPattern,
        scr_local: int,
        layout: ConstructorLayout,
        env: WasmSlotEnv,
        scrutinee_type: str | None = None,
    ) -> tuple[list[str], WasmSlotEnv] | None:
        """Extract fields from a constructor match into locals.

        Computes field offsets from concrete binding types (same
        monomorphization approach as _translate_constructor_call).

        *scrutinee_type* (#1060) is the concrete Vera type name of the value at
        *scr_local* (e.g. "Box<Unit>").  A WILDCARD over a bare type-parameter
        field consults it to recover the field's instantiation-aware width; a
        nested constructor sub-pattern recurses with the field's own resolved
        concrete type so deeper type-parameter wildcards stay correct too.
        """
        # #1043: `"unit"` (a zero-size erases-to-Unit field) is size 0 / align 1
        # — a WILDCARD over such a field reads `"unit"` from the (now
        # erasure-aware) registered `field_offsets` and must advance the offset
        # by nothing, matching construction.  A `"unit"` BINDING is handled by
        # the `type_name == "Unit"` skip above and never reaches these maps.
        _sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8, "unit": 0}
        _aligns = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4, "unit": 1}
        offset = 4  # after tag (i32, 4 bytes)
        instrs: list[str] = []
        new_env = env

        for i, sub_pat in enumerate(pattern.sub_patterns):
            if isinstance(sub_pat, ast.BindingPattern):
                # Resolve concrete WASM type from the binding's type_expr
                type_name = self._type_expr_to_slot_name(sub_pat.type_expr)
                if type_name is None:
                    raise CodegenSkip(
                        sub_pat,
                        "constructor field binding has no slot name",
                    )
                # Zero-size bindings (Unit, transparent Future<Unit>, …): no
                # WASM representation — skip extraction, advance no offset.
                # Keyed on erasure, not the bare string "Unit" (#1031).
                if self._slot_name_erases_to_unit(type_name):
                    continue
                # Pair types (String, Array<T>): two consecutive i32 locals
                if self._is_pair_type_name(type_name):
                    align = _aligns.get("i32", 4)
                    offset = (offset + align - 1) & ~(align - 1)
                    ptr_local = self.alloc_local("i32")
                    len_local = self.alloc_local("i32")
                    instrs.append(f"local.get {scr_local}")
                    instrs.append(f"i32.load offset={offset}")
                    instrs.append(f"local.set {ptr_local}")
                    instrs.append(f"local.get {scr_local}")
                    instrs.append(f"i32.load offset={offset + 4}")
                    instrs.append(f"local.set {len_local}")
                    # PR #707 review: pair-type field
                    # extraction in match arms — the ``ptr_local``
                    # holds a heap pointer (the String buffer or the
                    # Array<T> backing) which is invisible to the
                    # conservative scan from a WASM local.  Same #705
                    # bug class as the ``wt == "i32"`` non-inline
                    # branch below; the original fix missed the
                    # pair-type branch because pair-types lower as
                    # two i32s and only the ptr half needs rooting.
                    # ``len_local`` is a length, not a pointer — no
                    # rooting needed.
                    self.needs_alloc = True
                    instrs.extend(gc_shadow_push(ptr_local))
                    new_env = new_env.push(type_name, ptr_local)
                    offset += 8  # two i32s
                    continue
                wt = self._slot_name_to_wasm_type(type_name)
                if wt is None:
                    raise CodegenSkip(
                        sub_pat,
                        f"constructor field type {type_name!r} has no WASM type",
                    )
                # Compute aligned offset for this field
                align = _aligns.get(wt, 8)
                offset = (offset + align - 1) & ~(align - 1)
                # Load field from scrutinee pointer
                local_idx = self.alloc_local(wt)
                load = [
                    f"local.get {scr_local}",
                    f"{wt}.load offset={offset}",
                ]
                # #747: runtime-guard an @Int -> @Nat ADT sub-pattern bind
                # (`match opt { Some(@Nat.0) -> }` on `Option<Int>`).  The
                # field loads as @Nat; trap if it is a negative i64 (Tier-3
                # backstop; never trips on a valid @Nat in [0, 2^63)).
                # Alias-aware (`type Age = Nat`) via `_resolve_base_type_name`
                # (CR #756).
                if self._resolve_base_type_name(type_name) == "Nat":
                    load = self._emit_nat_bind_guard(load)
                # #813: dual — extracting a concrete @Nat *field* into an @Int
                # sub-pattern slot (`match @Box.0 { Box(@Int) -> }` on a
                # `Box(Nat)`) widens it; a @Nat field above i64.MAX would
                # reinterpret to a negative @Int.  The widen guard must fire
                # only when the SOURCE field is @Nat (``layout.nat_fields[i]``),
                # never on a genuine @Int field — unlike the narrowing guard it
                # would otherwise wrongly trap a legitimately-negative @Int.
                elif (self._resolve_base_type_name(type_name) == "Int"
                        and i < len(layout.nat_fields)
                        and layout.nat_fields[i]):
                    load = self._emit_int_widen_guard(load)
                instrs.extend(load)
                instrs.append(f"local.set {local_idx}")
                # #705: shadow-push heap-pointer match bindings so
                # subsequent allocations (e.g. ``set_new()`` inside
                # ``set_add(set_new(), @Json.0)``) can't reclaim
                # them during the gap between binding and use.
                # ``i32`` slot with a non-scalar Vera type is the
                # signature of a heap-pointer ADT field; Bool / Byte
                # / Unit are inline i32s that don't need rooting.
                # The function epilogue's ``$gc_sp`` restore pops
                # these on exit so the shadow stack stays bounded.
                # PR #707 review: ``gc_shadow_push``
                # references ``$gc_sp`` / ``$gc_stack_limit`` which
                # are only exported when ``needs_alloc`` is set on
                # the surrounding context.  Without flipping it,
                # a function that has a heap-pointer match binding
                # but no other allocation would emit WAT referencing
                # undefined globals.
                if wt == "i32" and type_name not in _INLINE_I32_TYPES:
                    self.needs_alloc = True
                    instrs.extend(gc_shadow_push(local_idx))
                new_env = new_env.push(type_name, local_idx)
                offset += _sizes.get(wt, 8)

            elif isinstance(sub_pat, ast.WildcardPattern):
                # Skip this field but advance the offset by its width.  #1060:
                # a bare type-PARAMETER field registers generically as i32, but
                # construction laid it out per the concrete instantiation
                # (Unit → 0 bytes) — recompute the width from the scrutinee's
                # type args, mirroring the eq/show recomputation, so every later
                # field reads the address construction actually wrote.  A
                # concrete field keeps its registered (#1043-erasure-aware)
                # width; an unrecoverable type-parameter instantiation LOUD-skips.
                if i < len(layout.field_offsets):
                    _, generic_wt = layout.field_offsets[i]
                    wt = self._wildcard_field_wasm_type(
                        pattern.name, i, generic_wt, scrutinee_type, sub_pat,
                        self._later_sub_pattern_reads(pattern.sub_patterns, i),
                    )
                    align = _aligns.get(wt, 8)
                    offset = (offset + align - 1) & ~(align - 1)
                    offset += _sizes.get(wt, 8)

            elif isinstance(sub_pat, ast.ConstructorPattern):
                # Nested constructor: load the field pointer (i32),
                # look up its layout, and recurse to extract its fields.
                align = _aligns.get("i32", 4)
                offset = (offset + align - 1) & ~(align - 1)
                sub_layout = self._ctor_layouts.get(sub_pat.name)
                if sub_layout is None:
                    raise CodegenSkip(
                        sub_pat,
                        f"unknown nested constructor {sub_pat.name!r} in pattern",
                    )
                sub_local = self.alloc_local("i32")
                instrs.append(f"local.get {scr_local}")
                instrs.append(f"i32.load offset={offset}")
                instrs.append(f"local.set {sub_local}")
                # Recurse into the nested constructor's sub-patterns, resolving
                # this field's concrete type against the outer instantiation
                # (#1060) so a type-parameter wildcard deeper in the nest
                # recomputes its width too.
                nested = self._extract_constructor_fields(
                    sub_pat, sub_local, sub_layout, new_env,
                    self._resolve_nested_scrutinee_type(
                        pattern.name, i, scrutinee_type,
                    ),
                )
                if nested is None:
                    return None
                nested_instrs, new_env = nested
                instrs.extend(nested_instrs)
                offset += _sizes.get("i32", 4)

            elif isinstance(sub_pat, ast.NullaryPattern):
                # Nullary: tag was already checked in the condition phase.
                # Just advance offset by i32 size (ADT pointer).
                align = _aligns.get("i32", 4)
                offset = (offset + align - 1) & ~(align - 1)
                offset += _sizes.get("i32", 4)

            else:
                # Unknown sub-pattern type
                raise CodegenSkip(
                    sub_pat,
                    f"unsupported nested pattern type {type(sub_pat).__name__}",
                )

        return (instrs, new_env)

    # -----------------------------------------------------------------
    # Nested pattern helpers
    # -----------------------------------------------------------------

    def _later_sub_pattern_reads(
        self, sub_patterns: tuple[ast.Pattern, ...], index: int,
    ) -> bool:
        """True if any sub-pattern after *index* reads a field.  #1060: a
        wildcard's mis-computed width only corrupts the offsets of LATER
        reads; a trailing wildcard — or one followed only by other wildcards —
        is harmless, so an unrecoverable type-parameter wildcard there need
        not LOUD-skip a compilable function.

        A zero-size BINDING (``@Unit``, ``@Future<Unit>``, aliases) is also
        not a read (#1070 rider): both walks bind nothing and load nothing
        for it (the extraction walk ``continue``s on erased bindings), so a
        trailing erased binding after an unrecoverable wildcard stays
        compilable too.  An un-nameable binding stays conservative (a read).
        """
        for sp in sub_patterns[index + 1:]:
            if isinstance(sp, ast.WildcardPattern):
                continue
            if isinstance(sp, ast.BindingPattern):
                type_name = self._type_expr_to_slot_name(sp.type_expr)
                if (type_name is not None
                        and self._slot_name_erases_to_unit(type_name)):
                    continue
            return True
        return False

    def _sub_pattern_wasm_type(
        self,
        sub_pat: ast.Pattern,
        field_index: int,
        layout: ConstructorLayout,
        ctor_name: str = "",
        scrutinee_type: str | None = None,
        later_read: bool = False,
    ) -> str | None:
        """Return the WASM type for a sub-pattern's field.

        Used for offset computation when walking nested patterns.  *ctor_name*,
        *scrutinee_type*, and *later_read* (#1060) let a WILDCARD over a bare
        type-parameter field resolve its instantiation-aware width instead of
        the generic i32 placeholder the registered layout records for a type
        parameter (LOUD-skipping only when the width is unrecoverable AND a
        later field is read).
        """
        if isinstance(sub_pat, ast.BindingPattern):
            type_name = self._type_expr_to_slot_name(sub_pat.type_expr)
            if type_name is None:
                raise CodegenSkip(
                    sub_pat,
                    "sub-pattern binding has no slot name",
                )
            # Zero-size bindings (Unit, transparent Future<Unit>, …): no WASM
            # representation — construction stores NOTHING for them, so the
            # offset walk must give them zero width (#1042).  Consulting the
            # registered layout here is wrong twice over: the builtin Tuple's
            # layout is empty (its per-call layout is recomputed erasure-aware),
            # and the registered user-ADT layout gives zero-size fields 4 bytes
            # (#1043) — either way the walk would advance past bytes that were
            # never stored and every later nested tag check would read garbage.
            # Keyed on erasure, not the bare string "Unit" (#1031), so
            # Future<Unit> behaves identically to Unit.
            if self._slot_name_erases_to_unit(type_name):
                return "unit"
            # Pair types (String, Array<T>) use i32_pair representation
            if self._is_pair_type_name(type_name):
                return "i32_pair"
            return self._slot_name_to_wasm_type(type_name)
        if isinstance(sub_pat, ast.WildcardPattern):
            if field_index < len(layout.field_offsets):
                _, generic_wt = layout.field_offsets[field_index]
                # #1060: instantiation-aware for a bare type-parameter field —
                # its registered width is the generic i32 placeholder, wrong for
                # any instantiation whose concrete width differs (Unit → 0).
                return self._wildcard_field_wasm_type(
                    ctor_name, field_index, generic_wt, scrutinee_type,
                    sub_pat, later_read,
                )
            return None
        if isinstance(sub_pat, (ast.ConstructorPattern, ast.NullaryPattern)):
            return "i32"  # ADT = heap pointer
        return None

    def _wildcard_field_wasm_type(
        self,
        ctor_name: str,
        field_index: int,
        generic_wt: str,
        scrutinee_type: str | None,
        sub_pat: ast.Pattern,
        later_read: bool,
    ) -> str:
        """WASM width of a WILDCARD sub-pattern's field, instantiation-aware.

        #1060: a bare type-PARAMETER field (``Box<T>`` field ``T``) registers
        generically as a 4-byte i32, but construction lays it out per the
        concrete instantiation — ``Box<Unit>`` erases it to 0 bytes,
        ``Box<String>`` to an i32_pair, ``Box<Int>`` to an i64.  A wildcard over
        such a field must advance the offset by the CONCRETE width, recovered
        from the scrutinee's type args exactly as the eq/show recomputation does
        (``_resolve_field_type_for_eq`` + ``_eq_field_wasm_type``); otherwise
        every later field reads a shifted, wrong address on a check-green
        program.  A concrete (non-type-parameter) field keeps its registered
        width, which #1043 already made erasure-aware.

        When the field IS a type parameter but the concrete instantiation cannot
        be recovered from *scrutinee_type* (e.g. a direct-call scrutinee whose
        inferred type dropped its type args), the width is unknown.  It only
        MATTERS if a later field is read at an offset that depends on it, so:

        * *later_read* True (a subsequent sub-pattern reads a field) → raise
          ``CodegenSkip``, a LOUD skip (E602 disclosure), never a wrong read;
        * *later_read* False (this wildcard is trailing, or only wildcards
          follow) → the unknown width is never consumed, so fall back to the
          generic placeholder rather than skip a compilable function
          (``match parse_bool(s) { Ok(_) -> …, Err(_) -> … }``).
        """
        tp_idx = self._ctor_adt_tp_indices.get(ctor_name)
        pos = (
            tp_idx[field_index]
            if tp_idx is not None and field_index < len(tp_idx)
            else None
        )
        if pos is None:
            # Not a bare type parameter — the registered width is correct.
            return generic_wt
        _base, type_args = self._split_param_type(scrutinee_type or "")
        if pos < len(type_args):
            return self._eq_field_wasm_type(type_args[pos])
        # Unrecoverable instantiation for a type-parameter field.
        if later_read:
            raise CodegenSkip(
                sub_pat,
                f"wildcard over type-parameter field {field_index} of "
                f"{ctor_name!r}: concrete instantiation unrecoverable from "
                f"scrutinee type {scrutinee_type!r}, and a later field is read "
                f"at an offset that depends on this field's erased width",
            )
        return generic_wt

    def _resolve_nested_scrutinee_type(
        self,
        ctor_name: str,
        field_index: int,
        scrutinee_type: str | None,
    ) -> str | None:
        """Concrete Vera type of a field — the scrutinee type for a nested
        constructor pattern on it.

        #1060: substitutes the outer instantiation's type args into the field's
        declared type (``Outer<Unit>`` field ``Inner<T>`` → ``Inner<Unit>``), so
        a wildcard over a type-parameter field deeper in the nest recomputes its
        width correctly.  Returns ``None`` when the field type is unknown or the
        outer instantiation is missing; the nested walk then LOUD-skips any
        type-parameter wildcard rather than reading a wrong offset.
        """
        layout = self._ctor_layouts.get(ctor_name)
        if layout is None or field_index >= len(layout.field_types):
            return None
        raw = layout.field_types[field_index]
        base, type_args = self._split_param_type(scrutinee_type or "")
        tp_names = self._adt_tp_param_names.get(base, ())
        tp_mapping = dict(zip(tp_names, type_args))
        tp_idx = self._ctor_adt_tp_indices.get(ctor_name)
        return self._resolve_field_type_for_eq(
            raw, field_index, tp_idx, type_args, tp_mapping,
        )

    def _collect_nested_tag_checks(
        self,
        pattern: ast.ConstructorPattern,
        scr_local: int,
        layout: ConstructorLayout,
        scrutinee_type: str | None = None,
    ) -> list[list[str]] | None:
        """Collect tag checks for nested constructor/nullary sub-patterns.

        Walks *pattern.sub_patterns* and for each that is a
        ``ConstructorPattern`` or ``NullaryPattern``, emits a sequence of
        WASM instructions that (a) loads the field pointer from the parent,
        (b) loads the tag from that pointer, (c) compares to the expected
        tag.  For ``ConstructorPattern`` it recurses to collect deeper
        checks.

        *scrutinee_type* (#1060) is the concrete Vera type name of the value at
        *scr_local*; it lets a WILDCARD over a bare type-parameter field before
        a nested constructor advance by the instantiation-aware width so the
        nested tag load lands on the address construction actually wrote.

        Returns a list of instruction-lists, each producing an ``i32``
        boolean on the stack.  Returns ``None`` on layout lookup failure.
        """
        # "unit" is a zero-size binding (Unit, transparent Future<Unit>):
        # construction stores nothing for it, so the walk gives it zero width
        # and no alignment — the extraction walks reach the same result by
        # `continue`-ing on erased components before their map lookups (#1042).
        # A WILDCARD over such a field also resolves to `"unit"`: for a DECLARED
        # Unit field via the erasure-aware registered `field_offsets` (#1043),
        # and for a type-PARAMETER field instantiated to Unit via the
        # scrutinee-threaded recomputation (#1060) — so the zero-width rule
        # covers both sub-pattern arms.
        _sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8, "unit": 0}
        _aligns = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4, "unit": 1}
        offset = 4  # after tag

        checks: list[list[str]] = []

        for i, sub_pat in enumerate(pattern.sub_patterns):
            wt = self._sub_pattern_wasm_type(
                sub_pat, i, layout, pattern.name, scrutinee_type,
                self._later_sub_pattern_reads(pattern.sub_patterns, i),
            )
            if wt is None:
                raise CodegenSkip(
                    sub_pat,
                    "nested pattern field has no WASM type",
                )
            align = _aligns.get(wt, 8)
            offset = (offset + align - 1) & ~(align - 1)

            if isinstance(sub_pat, (ast.ConstructorPattern, ast.NullaryPattern)):
                name = sub_pat.name
                sub_layout = self._ctor_layouts.get(name)
                if sub_layout is None:
                    raise CodegenSkip(
                        sub_pat,
                        f"unknown nested constructor {name!r} in pattern",
                    )
                # Load the nested ADT pointer, stash in a temp,
                # then load the tag and compare.
                tmp = self.alloc_local("i32")
                check: list[str] = [
                    f"local.get {scr_local}",
                    f"i32.load offset={offset}",
                    f"local.tee {tmp}",
                    "i32.load",
                    f"i32.const {sub_layout.tag}",
                    "i32.eq",
                ]
                checks.append(check)

                # Recurse for deeper nesting, resolving this field's concrete
                # type against the outer instantiation (#1060) so a
                # type-parameter wildcard deeper in the nest recomputes its
                # width too.
                if isinstance(sub_pat, ast.ConstructorPattern):
                    deeper = self._collect_nested_tag_checks(
                        sub_pat, tmp, sub_layout,
                        self._resolve_nested_scrutinee_type(
                            pattern.name, i, scrutinee_type,
                        ),
                    )
                    if deeper is None:
                        return None
                    checks.extend(deeper)

            offset += _sizes.get(wt, 8)

        return checks

    # -----------------------------------------------------------------
    # Array literals
    # -----------------------------------------------------------------

    def _translate_array_lit(
        self, expr: ast.ArrayLit, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate an array literal to (ptr, len) on the stack.

        Allocates heap memory via $alloc, stores each element, then
        pushes (ptr, len) as an i32 pair.  Empty arrays push (0, 0).
        """
        n = len(expr.elements)
        if n == 0:
            return ["i32.const 0", "i32.const 0"]

        elem_type = self._infer_array_element_type(expr)
        if elem_type is None:
            raise CodegenSkip(
                expr,
                "could not infer array literal element type",
            )
        # Resolve type aliases — `type Row = Array<Bool>` makes the
        # inferred element name "Row", but the element-layout helpers
        # below match on bare "Array" / "Array<...>".  Without this,
        # an alias-typed element falls through to the 4-byte i32 path
        # and the literal emits a malformed WAT (#583).
        #
        # Canonicalize to the target's FULL compound spelling first
        # (#1058): the name-only `_resolve_base_type_name` hop drops type
        # arguments, so `type FI = Future<Int>` resolved to bare "Future".
        # A `Future<T>` element is representation-transparent (#841) —
        # its width is its payload T's — but the bare head collapses to
        # the i32 default, storing an i64 payload with `i32.store` (a
        # "expected i32, found i64" validation trap) on a check-green
        # program.  Mirrors the `_is_pair_type_name` canonicalize-then-
        # resolve order (#1046).
        elem_type, _ = self._canonicalize_alias_slot_name(elem_type)
        elem_type = self._resolve_base_type_name(elem_type)
        elem_size = _element_mem_size(elem_type)
        if elem_size is None:
            raise CodegenSkip(
                expr,
                f"unsupported array literal element type {elem_type!r}",
            )
        is_pair = _is_pair_element_type(elem_type)
        store_op = _element_store_op(elem_type)
        # store_op is None only for pair types — handled below
        if store_op is None and not is_pair:
            raise CodegenSkip(
                expr,
                f"no store op for array literal element type {elem_type!r}",
            )

        self.needs_alloc = True
        total_bytes = n * elem_size
        tmp_ptr = self.alloc_local("i32")

        # #820: a @Nat element widening into an @Array<Int> literal reinterprets
        # its bit pattern above i64.MAX (u64.MAX -> -1).  The literal is typed by
        # its element *values* (source), so recover the *target* element type
        # (`Array<Int>`) from the threaded target-type table (the enabler) to
        # decide the widening guard — the dual of the concrete @Int constructor
        # field.  Guard only when the target element is genuinely @Int, never a
        # @Nat / generic element (which must not be range-trapped).
        target_elem_is_int = self._adt_arg_is_int(
            self._target_codegen_type_full(expr), 0)

        instructions: list[str] = []
        # Allocate
        instructions.append(f"i32.const {total_bytes}")
        instructions.append("call $alloc")
        instructions.append(f"local.set {tmp_ptr}")
        instructions.extend(gc_shadow_push(tmp_ptr))

        # Store each element
        for i, elem in enumerate(expr.elements):
            elem_instrs = self.translate_expr(elem, env)
            if elem_instrs is None:
                return None
            if target_elem_is_int and self._result_is_nat(elem):
                elem_instrs = self._emit_int_widen_guard(elem_instrs)
            offset = i * elem_size
            if is_pair:
                # Pair type (String, Array<T>): element pushes (ptr, len)
                # Store into two consecutive i32 slots
                tmp_val_ptr = self.alloc_local("i32")
                tmp_val_len = self.alloc_local("i32")
                instructions.extend(elem_instrs)
                instructions.append(f"local.set {tmp_val_len}")
                instructions.append(f"local.set {tmp_val_ptr}")
                # Store ptr at offset
                instructions.append(f"local.get {tmp_ptr}")
                instructions.append(f"local.get {tmp_val_ptr}")
                instructions.append(f"i32.store offset={offset}")
                # Store len at offset+4
                instructions.append(f"local.get {tmp_ptr}")
                instructions.append(f"local.get {tmp_val_len}")
                instructions.append(f"i32.store offset={offset + 4}")
            else:
                instructions.append(f"local.get {tmp_ptr}")
                instructions.extend(elem_instrs)
                instructions.append(f"{store_op} offset={offset}")

        # Push (ptr, len)
        instructions.append(f"local.get {tmp_ptr}")
        instructions.append(f"i32.const {n}")
        return instructions

    def _translate_index_expr(
        self, expr: ast.IndexExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array indexing with bounds check.

        Evaluates collection → (ptr, len), evaluates index,
        performs bounds check (trap on OOB), then loads the element.
        """
        elem_type = self._infer_index_element_type(expr)
        if elem_type is None:
            raise CodegenSkip(
                expr,
                "could not infer index expression element type",
            )
        elem_size = _element_mem_size(elem_type)
        if elem_size is None:
            raise CodegenSkip(
                expr,
                f"unsupported index expression element type {elem_type!r}",
            )
        is_pair = _is_pair_element_type(elem_type)
        load_op = _element_load_op(elem_type)
        # load_op is None only for pair types — handled below
        if load_op is None and not is_pair:
            raise CodegenSkip(
                expr,
                f"no load op for index expression element type {elem_type!r}",
            )

        # Evaluate collection → (ptr, len) on stack
        coll_instrs = self.translate_expr(expr.collection, env)
        if coll_instrs is None:
            return None

        # Evaluate index (Int → i64)
        idx_instrs = self.translate_expr(expr.index, env)
        if idx_instrs is None:
            return None

        # Temp locals for ptr, len, index
        tmp_ptr = self.alloc_local("i32")
        tmp_len = self.alloc_local("i32")
        tmp_idx = self.alloc_local("i32")

        instructions: list[str] = []
        # Save (ptr, len)
        instructions.extend(coll_instrs)
        instructions.append(f"local.set {tmp_len}")
        instructions.append(f"local.set {tmp_ptr}")
        # Evaluate and wrap index from i64 to i32
        instructions.extend(idx_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {tmp_idx}")
        # Bounds check: if (u32)idx >= (u32)len then trap
        instructions.append(f"local.get {tmp_idx}")
        instructions.append(f"local.get {tmp_len}")
        instructions.append("i32.ge_u")
        instructions.append("if")
        instructions.append("  unreachable")
        instructions.append("end")
        # Compute address: ptr + idx * elem_size
        instructions.append(f"local.get {tmp_ptr}")
        if elem_size == 1:
            instructions.append(f"local.get {tmp_idx}")
            instructions.append("i32.add")
        else:
            instructions.append(f"local.get {tmp_idx}")
            instructions.append(f"i32.const {elem_size}")
            instructions.append("i32.mul")
            instructions.append("i32.add")
        # Load element
        if is_pair:
            # Pair type (String, Array<T>): load (ptr, len) from two
            # consecutive i32 slots.  Save computed address first.
            tmp_addr = self.alloc_local("i32")
            instructions.append(f"local.set {tmp_addr}")
            instructions.append(f"local.get {tmp_addr}")
            instructions.append("i32.load offset=0")
            instructions.append(f"local.get {tmp_addr}")
            instructions.append("i32.load offset=4")
        else:
            instructions.append(load_op)  # type: ignore[arg-type]
        return instructions
