"""Operator and simple expression translation mixin for WasmContext."""

from __future__ import annotations

from collections.abc import Callable
from typing import ClassVar

from vera import ast, narrowing, naming
from vera.monomorphize import pipe_desugared_call, resolve_type_alias
from vera.types import TO_STRING_BUILTINS
from vera.skip import AdtEqNotDerivableError, CodegenInvariantError
from vera.wasm.helpers import WasmSlotEnv, field_layout, state_type_arg


class OperatorsMixin:
    """Mixin providing operator and simple expression translation methods.

    Methods here translate slot references, binary/unary operators,
    control flow, string literals, assert/assume, quantifiers, and
    old/new state expressions into WAT instructions.  They rely on
    attributes and methods provided by the main WasmContext class
    through mixin composition.
    """

    # -----------------------------------------------------------------
    # Slot references
    # -----------------------------------------------------------------

    def _translate_slot_ref(
        self, ref: ast.SlotRef, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate @Type.n to local.get."""
        # #1208: the reference resolves by the CHECKER's rendering — the
        # single `vera.naming` renderer, against this context's alias
        # environment — and so does every binding key in `env`.  The two
        # sides of the lookup are one function of one environment, which is
        # what makes a hit the checker's own binding rather than whichever
        # member of its equivalence class happened to be spelled the way
        # this reference was.  Nested composite type arguments stay fully
        # qualified (#914 finding 2).
        type_name = naming.slot_ref_key(ref, self._alias_env)
        local_idx = env.resolve(type_name, ref.index)
        if local_idx is None:
            # Defensive invariant: a check-green slot reference must map to a
            # local.  The two source routes that used to reach here — reading
            # handler state as a slot in a handled body (#973) and a
            # where-helper body reading the OUTER function's parameter slot
            # (#969) — are both now rejected at check with E130, so no known
            # valid-source program trips this.  It stays as a soundness net for
            # any future checker/backend scope desync (never delete the guard).
            raise CodegenInvariantError(  # pragma: no cover
                "slot reference resolved to no local (dangling @T.n)", ref)
        # Pair types (String, Array<T>) push (ptr, len) — two locals
        if self._is_pair_type_name(type_name):
            return [f"local.get {local_idx}", f"local.get {local_idx + 1}"]
        return [f"local.get {local_idx}"]

    # -----------------------------------------------------------------
    # Binary operators
    # -----------------------------------------------------------------

    def _translate_widening_binary(
        self, expr: ast.BinaryExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a binary operator to WAT, its widened `@Nat` operands
        arranged first (:py:meth:`_translate_binary` does the rest)."""
        # Pipe: a |> f(x, y) → f(a, x, y), through the ONE shared desugar
        # (`vera.monomorphize.pipe_desugared_call`) the checker, discovery and
        # both type namers use.  #1357: the desugared call keeps the right
        # operand's own node type, so `a |> m::g()` stays a `ModuleCall` and
        # its `path` still routes to the declaring module's clone.  Rebuilding
        # it as a bare-name `FnCall` discarded that path, and the call landed
        # on a name the importer's flat namespace does not have — a
        # check-green, verify-clean program whose caller was dropped at
        # [E602] while the DIRECT spelling of the same call compiled.
        if expr.op == ast.BinOp.PIPE:
            desugared = pipe_desugared_call(expr)
            if desugared is None:
                raise CodegenInvariantError(  # pragma: no cover
                    "pipe RHS is neither FnCall nor ModuleCall", expr)
            # Through `translate_expr`, so each shape takes its OWN arm: a
            # `ModuleCall` reaches the qualified-target resolver that consumes
            # its `path`, exactly as the direct spelling of the same call does.
            return self.translate_expr(desugared, env)

        # PR #1583 review, #1588: a `@Nat` value an `@Int` operation widens
        # — an operand, or an arm of a join operand that supplies one —
        # traps above `i64.MAX` as it is evaluated, at the sites the
        # verifier's `nat_to_int_coerce` obligation reads from the same
        # classifier.  Arranged before either operand is translated, since
        # the `@Nat` subtraction translates them on its own path.
        widened = [
            id(value) for value in narrowing.widened_nat_operands(
                expr, self._overflow_codegen_type,
                self._is_guarded_nat_subtraction)
            if id(value) not in self._widened_operands]
        self._widened_operands.update(widened)
        try:
            return self._translate_binary(expr, env)
        finally:
            self._widened_operands.difference_update(widened)

    def _translate_binary(
        self, expr: ast.BinaryExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate binary operators to WAT, once
        :py:meth:`_translate_widening_binary` has arranged the widened
        operands."""
        # @Nat subtraction underflow guard (#520) — mirrors the static
        # obligation emitted in vera/verifier.py.  When the result is
        # statically @Nat and at least one operand has @Nat origin, emit a
        # runtime check that traps on underflow.  Programs that ran `vera
        # verify` first will have caught the violation statically; this
        # guard is the safety net for `vera compile` / `vera run` paths that
        # skipped verification.  Decided BEFORE the operands are translated:
        # an operand whose sign its bits do not carry records it as it is
        # evaluated (#1503), and that has to be arranged first.  (The static
        # rule reads no f64 or `@Byte` operand as a `@Nat`, so neither lowering
        # below is passed over.)
        if expr.op == ast.BinOp.SUB and self._is_nat_subtraction(expr):
            return self._translate_nat_subtraction(expr, env)

        left = self.translate_expr(expr.left, env)
        right = self.translate_expr(expr.right, env)
        # #657 / #630 [E615]: keep as `return None` — do NOT "clean up" to
        # assert/raise.  translate_expr returns None *reachably* when an operand
        # is a string interpolation whose inference failed (e.g. `x == "\(bad)"`):
        # it records to _interp_inference_failures and the [E615] function-drop
        # propagates through this forward.  Load-bearing PROPAGATE, not dead.
        # See vera/skip.py, "Reachable None via the [E615] channel".
        if left is None or right is None:
            return None  # pragma: no cover

        op = expr.op
        ltype = self._infer_expr_wasm_type(expr.left)

        # #766: a binary op over a `@Byte` operand must lower entirely at i32.
        # `@Byte` is represented as i32 (spec §11 — Byte uses i32 unsigned
        # comparison ops), but int literals emit `i64.const` and the default
        # arithmetic/comparison tables emit i64 ops, so a Byte slot compared or
        # combined with an int literal (which only occurs inside a refinement
        # predicate — ordinary code rejects `@Byte < 10` at the checker) yields
        # an i32-value/i64-op mismatch wasmtime rejects at instantiation.
        # Detected before the i64 arithmetic/comparison branches and re-lowered
        # at i32 (unsigned for comparison and division/mod, matching Byte's
        # 0..255 semantics).
        if (op in self._ARITH_OPS or op in self._CMP_OPS) and (
                self._is_byte_expr(expr.left)
                or self._is_byte_expr(expr.right)):
            byte_result = self._translate_byte_binop(expr, env)
            if byte_result is not None:
                return byte_result

        # Arithmetic
        if op in self._ARITH_OPS:
            if ltype == "f64":
                if op == ast.BinOp.MOD:
                    return self._translate_f64_mod(left, right)
                if op not in self._ARITH_OPS_F64:  # pragma: no cover
                    raise CodegenInvariantError(  # pragma: no cover
                        "unsupported f64 arithmetic operator", expr)
                return left + right + [self._ARITH_OPS_F64[op]]
            # A @Nat subtraction took its guarded path above, before its
            # operands were translated (#520, #1503).
            # #798: @Int/@Nat add/sub/mul wrap at the i64/u64 boundary; emit a
            # runtime overflow guard mirroring the verifier's `int_overflow`
            # obligation (vera/verifier.py:_check_overflow_obligation).  The
            # classifier consults the checker's resolved-type table so it
            # guards exactly the sites — at the exact signed/unsigned range —
            # the verifier obligates.  @Nat subtraction is `nat_sub` underflow
            # (handled above), not high-overflow, so it is excluded here, in
            # lockstep with the verifier's `expr.op == SUB and ovf == "Nat"`
            # exclusion.  Programs that ran `vera verify` first caught any
            # provable overflow statically (loud E528); this guard is the
            # safety net for the `vera compile` / `vera run` paths.
            # `_overflow_arith_codegen_type` classifies on the operands' COMMON
            # (coerced) type — the width the i64/u64 op runs at — so a
            # literal-left @Int add and an @Int add narrowed into a @Nat slot
            # are both i64, in lockstep with the verifier (#798).
            #
            # #1417: an UNCLASSIFIED operand pair fails CLOSED.  The
            # classifier answers `None` when the threaded type table has no
            # entry for an operand, and skipping the guard on that answer
            # meant the arithmetic wrapped in silence while the verifier's
            # `int_overflow` obligation went on claiming a runtime check —
            # a false guarantee reachable, in principle, by any path that
            # loses an entry.  An unknown width is treated as `Int`, which
            # is the safe reading of the pair: `Int` is the wider signed
            # interpretation, its guard fires on exactly the values that
            # would wrap, and a `@Nat` pair mistakenly guarded as `Int`
            # traps only on values that had already left the range its own
            # obligation covers.  The classifier itself keeps saying `None`
            # — "I do not know" is a real answer and collapsing it into a
            # type would put the guess where the verifier's mirror reads.
            ovf = self._overflow_arith_codegen_type(expr) or "Int"
            if (op in (ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL)
                    and not (op == ast.BinOp.SUB and ovf == "Nat")):
                return self._emit_overflow_guard(
                    left, right, op, ovf, at=expr)
            if op in (ast.BinOp.DIV, ast.BinOp.MOD):
                # `i64.div_s` / `i64.rem_s` trap by themselves on a zero
                # divisor, so the instruction IS the check, and carries its
                # record entry's marker (#1479).  A signed division also
                # traps on `INT_MIN / -1`, so it carries that condition's
                # marker too — keyed on the instruction emitted, not on the
                # operands' type: a `@Nat` division is `i64.div_s` today as
                # well, and reads 2^63 and 2^64 - 1 as those two (#1504).
                instruction = self._ARITH_OPS[op]
                markers = self._record_check(
                    "wasm/operators.py:_translate_binary", expr)
                if instruction.endswith(".div_s"):
                    markers += self._note_quotient_overflow(expr)
                return left + right + [instruction + markers]
            return left + right + [self._ARITH_OPS[op]]

        # Comparison — choose i32/i64/f64 based on operand types
        if op in self._CMP_OPS:
            rtype = self._infer_expr_wasm_type(expr.right)
            if ltype == "f64" or rtype == "f64":
                return left + right + [self._CMP_OPS_F64[op]]
            # String equality — byte-by-byte comparison
            if (ltype == "i32_pair" and rtype == "i32_pair"
                    and op in (ast.BinOp.EQ, ast.BinOp.NEQ)):
                result = self._translate_string_eq(left, right)
                if op == ast.BinOp.NEQ:
                    result.append("i32.eqz")
                return result
            # #927: String ORDERING (`<`/`>`/`<=`/`>=`).  A String is an
            # (i32 ptr, i32 len) pair, not a scalar — falling through to the
            # i64 comparison table below emitted `i64.lt_s` on the pointer
            # word (both a wrong-order result AND an i32/i64 type mismatch that
            # crashed WASM translation).  `String` IS orderable (spec §4.5,
            # lexicographic), so lower to a three-way `$cmp_String` helper
            # (byte-wise, proper-prefix-is-less — matching Z3's `StringSort`
            # ordering the verifier already uses, so verify ↔ run agree) and
            # test its {-1,0,1} result against zero with the scalar i32 op.
            # `compare(a, b)` on strings reaches here too: Pass 1.6 rewrites it
            # to `a < b ? Less : (a == b ? Equal : Greater)` (#874).
            if (ltype == "i32_pair" and rtype == "i32_pair"
                    and op in (ast.BinOp.LT, ast.BinOp.GT,
                               ast.BinOp.LE, ast.BinOp.GE)):
                self._request_string_cmp_helper()
                zero_cmp = self._CMP_OPS[op].replace("i64.", "i32.")
                return left + right + [
                    "call $cmp_String", "i32.const 0", zero_cmp,
                ]
            if ltype == "i32" and rtype == "i32":
                # Byte operands use unsigned i32 comparison
                lv = self._infer_vera_type(expr.left)
                rv = self._infer_vera_type(expr.right)
                if lv == "Byte" or rv == "Byte":
                    i32_op = self._CMP_OPS[op].replace("i64.", "i32.")
                    i32_op = i32_op.replace("_s", "_u")
                    return left + right + [i32_op]
                # ADT structural equality (§9.8 auto-derivation).  `lv` may be
                # parameterized (`Box<String>`); dispatch on the base name but
                # pass the full name so the generated helper resolves the
                # concrete field types of *this* instantiation (#773).  Recover
                # the left operand's fully-qualified name via the shared chain:
                # `_parameterize_ctor_operand` (a `Some(1)` operand → `Option<Int>`,
                # #772), `_recover_lost_type_arg` (a bare generic-ADT slot →
                # `Box<Int>` from its sibling, #912) and the `_eq_full_type_names`
                # map (a truncated `List<List>` clone → `List<List<Int>>`, #932).
                lv = self._eq_operand_full_name(expr.left, expr.right, lv)
                # #994 F2: a payload-less nested constructor (`Some(None)` →
                # `Option<Option>`, inner argument erased) or a dead base generic
                # clone's slot (`Option<Option<T>>`, nested free `T`) leaves `lv`
                # only PARTIALLY resolved — the structural-Eq derivation cannot
                # lower it and raised a spurious E613.  Both operands share a type
                # (checker E142 otherwise), and a monomorphized *reachable* clone
                # substitutes the sibling slot to a fully concrete name, so
                # recover the concrete name from the OTHER operand when this one
                # is under-resolved.  When NEITHER resolves (the dead base clone),
                # `lv` stays partial and the concreteness gate below routes it to
                # the harmless scalar (dead-code) lowering, exactly as the #912
                # lost-type-arg clone does.
                if lv is not None and not self._eq_type_name_fully_concrete(lv):
                    rv_full = self._eq_operand_full_name(expr.right, expr.left, rv)
                    if (rv_full is not None
                            and self._eq_type_name_fully_concrete(rv_full)):
                        lv = rv_full
                # #1085: ground the operand's OWN spelling.  An alias of a WHOLE
                # ADT (`type MyBox = Box<Int>;`) reaches the dispatch as the bare
                # alias name `MyBox`, absent from `_adt_type_names`, so the
                # structural branch below was skipped and `==` fell to the scalar
                # POINTER compare — two structurally equal, distinct-pointer
                # values compared unequal (0) on a check-green program.  #1076
                # grounded type ARGUMENTS (`Box<MyInt>`); this grounds the whole
                # operand.  `_canonical_field_type` resolves alias chains and
                # peels a transparent `Future<...>` wrapper; a registered ADT or a
                # genuine free `T` is returned unchanged, so the lost-arg and
                # free-var controls still route to the scalar fallback.
                if lv is not None:
                    lv = self._canonical_field_type(lv)
                lv_base = lv.split("<", 1)[0] if lv is not None else None
                if (op in (ast.BinOp.EQ, ast.BinOp.NEQ)
                        and lv is not None
                        and lv_base not in ("Bool", "Byte")
                        and self._value_adt_key(lv) is not None
                        and not self._is_lost_type_arg_clone(lv, lv_base)
                        and self._eq_type_name_fully_concrete(lv)):
                    adt_eq = self._translate_adt_eq(left, right, lv, expr)
                    if adt_eq is not None:
                        if op == ast.BinOp.NEQ:
                            adt_eq.append("i32.eqz")
                        return adt_eq
                # Bool operands — use i32 comparison (signed)
                i32_op = self._CMP_OPS[op].replace("i64.", "i32.")
                return left + right + [i32_op]
            return left + right + [self._CMP_OPS[op]]

        # Boolean
        if op == ast.BinOp.AND:
            return left + right + ["i32.and"]
        if op == ast.BinOp.OR:
            return left + right + ["i32.or"]

        # IMPLIES: a ==> b  ≡  (not a) or b
        if op == ast.BinOp.IMPLIES:
            return left + ["i32.eqz"] + right + ["i32.or"]

        raise CodegenInvariantError(  # pragma: no cover
            "binary operator dispatch fell through", expr)

    # -----------------------------------------------------------------
    # Byte binary operators (#766)
    # -----------------------------------------------------------------

    # Arithmetic over Byte (i32): division / remainder are UNSIGNED (0..255).
    _ARITH_OPS_I32_BYTE: ClassVar[dict[ast.BinOp, str]] = {
        ast.BinOp.ADD: "i32.add",
        ast.BinOp.SUB: "i32.sub",
        ast.BinOp.MUL: "i32.mul",
        ast.BinOp.DIV: "i32.div_u",
        ast.BinOp.MOD: "i32.rem_u",
    }

    def _is_byte_expr(self, expr: ast.Expr) -> bool:
        """Whether *expr* is a `@Byte` value at runtime (an i32 in 0..255).

        True for a Byte-typed slot ref (directly or through an alias, e.g.
        `type SmallByte = { @Byte | ... }`), for arithmetic over Byte
        operands (`@Byte.0 + 1`), whose i32 result stays a Byte, and for a
        call to a user fn whose DECLARED return type resolves to `@Byte`
        (`ident(@Byte.0)` in a refinement predicate; #766 review follow-up).
        An int *literal* alone is NOT a Byte — it is width-coerced to the
        companion Byte operand by :py:meth:`_translate_byte_operand` — so
        `10 < 20` without a Byte operand is unaffected (#766)."""
        if isinstance(expr, ast.SlotRef):
            return self._resolve_base_type_name(expr.type_name) == "Byte"
        if isinstance(expr, ast.ResultRef):
            return expr.type_name == "Byte"
        if isinstance(expr, ast.BinaryExpr) and expr.op in self._ARITH_OPS:
            return (self._is_byte_expr(expr.left)
                    or self._is_byte_expr(expr.right))
        if isinstance(expr, ast.UnaryExpr) and expr.op == ast.UnaryOp.NEG:
            return self._is_byte_expr(expr.operand)
        if isinstance(expr, ast.FnCall):
            # Byte-ness of a call operand comes from the callee's DECLARED
            # Vera return type, NOT its WASM return width: `Byte` and `Bool`
            # are both i32, and the `_infer_vera_type` fallback below maps an
            # i32 return to "Bool" unconditionally — collapsing the two and
            # leaving a `@Byte`-returning call's result compared at i64 (the
            # same #766 width mismatch in a different operand shape).  The
            # `_fn_ret_type_exprs` registry holds the un-canonical declared
            # TypeExpr per user fn; `_canonical_named_type` resolves alias
            # chains and refinement wrappers (`-> @MyByte` where `type MyByte
            # = Byte`).  No builtin returns a bare `@Byte` (`byte_to_int` →
            # Int, `int_to_byte` → Option<Byte>), so a registry miss is
            # correctly non-Byte.
            ret_te = self._fn_ret_type_exprs.get(expr.name)
            if ret_te is not None:
                canonical = self._canonical_named_type(ret_te)
                return canonical is not None and canonical.name == "Byte"
            return False
        return self._resolve_base_type_name(
            self._infer_vera_type(expr) or "") == "Byte"

    def _translate_byte_operand(
        self, expr: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate *expr* as an i32 operand of a Byte binary op (#766).

        An int literal emits `i32.const` (not the default `i64.const`) so it
        matches the i32 Byte value it is compared with / combined into; a nested
        Byte arithmetic sub-expression recurses through
        :py:meth:`_translate_byte_binop`; everything else (a Byte slot ref) is
        translated normally, already yielding an i32."""
        if isinstance(expr, ast.IntLit):
            return [f"i32.const {expr.value}"]
        if isinstance(expr, ast.BinaryExpr) and expr.op in self._ARITH_OPS:
            return self._translate_byte_binop(expr, env)
        return self.translate_expr(expr, env)

    def _translate_byte_binop(
        self, expr: ast.BinaryExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Lower a Byte arithmetic / comparison binary op entirely at i32 (#766).

        Both operands are lowered to i32 via :py:meth:`_translate_byte_operand`
        (int literals coerced to `i32.const`), and the op is emitted as its i32
        form — unsigned for comparison and for division / remainder, matching
        Byte's unsigned 0..255 semantics (spec §11).  Returns None only if an
        operand fails to translate (propagating the reachable [E615] None)."""
        left = self._translate_byte_operand(expr.left, env)
        right = self._translate_byte_operand(expr.right, env)
        if left is None or right is None:
            return None  # pragma: no cover
        op = expr.op
        if op in self._ARITH_OPS:
            return left + right + [self._ARITH_OPS_I32_BYTE[op]]
        # Comparison: i64 signed table → i32 unsigned.
        i32_op = self._CMP_OPS[op].replace("i64.", "i32.").replace("_s", "_u")
        return left + right + [i32_op]

    # -----------------------------------------------------------------
    # ADT structural equality (#773)
    # -----------------------------------------------------------------
    #
    # Structural `Eq` auto-derivation (§9.8).  A comparison site emits a `call`
    # to a generated per-instantiation `$eq_<type>` helper; the helpers compare
    # two heap pointers structurally, dispatching each field by its *Vera* type
    # — scalar `.eq`, String content comparison, or recursion into a nested
    # ADT's own `$eq_` helper.  Generating real functions (rather than inline
    # expansion) is what lets a recursive ADT (e.g. `List<T>`) derive equality:
    # the nested-field call is a plain `call`, not an unbounded expansion.
    #
    # A field type with no `Eq` semantics (Array / Map / host handle / a
    # closure) is not derivable.  BOTH comparison paths consult the same E613
    # gate (`_adt_satisfies_eq`, in `vera/codegen/monomorphize.py`): the
    # GENERIC constraint path checks it before codegen, and the DIRECT `==`
    # path checks it here in `_translate_adt_eq` (via the injected
    # `_adt_eq_derivable` oracle) and raises `AdtEqNotDerivableError` —
    # converted to a clean E613 by the function/closure compile drivers — so a
    # non-derivable ADT never silently mis-compares by pointer and never trips
    # the helper generator's E699 field-dispatch invariant (PR #870 review;
    # closes the #872 hole).

    def _parameterize_ctor_operand(
        self, operand: ast.Expr, bare: str | None,
    ) -> str | None:
        """Recover an `==` operand's parameterized ADT type name (#772, #923).

        `_infer_vera_type` resolves a `ConstructorCall` to the BARE ADT name
        (`Option`, dropping `<Int>`).  For the direct structural-`==` derivation
        the type argument is load-bearing — the generated `$eq_<type>` helper
        must resolve the concrete field type — so recover it from the
        constructor's arguments, RECURSIVELY (#923): a nested-generic operand
        (`Cons(Cons(1, Nil), Nil)`) reconstructs the FULLY-qualified
        `List<List<Int>>` rather than the one-level `List<List>` the pre-#923
        flat recovery produced (which then spuriously E613'd on the derivable
        nested type).  When that recursion bottoms out at a bare head because no
        field IS a bare type parameter — a GENERIC mutually-recursive ADT whose
        argument is buried in a NESTED generic field (`Grove(Rose<T>,
        Forest<T>)`) — fall back to `_recover_ctor_ptype`, which descends into
        the nested field's own argument to dig the parameter out (#934; without
        the recovered `<Int>` the composite `==` silently lowered to a
        bare-pointer `i32.eq` → a wrong `0`).  Falls back to ``bare`` when the
        operand is not a `ConstructorCall` or a needed type argument cannot be
        inferred — the established lost-type-arg shape the derivability path
        already routes to the scalar lowering.
        """
        if bare is None:
            return bare
        # #923: recover the FULLY-qualified nested-generic name (List<List<Int>>)
        # for the direct-`==` path.  #934: when that recursion bottoms out at a
        # bare head — a GENERIC mutually-recursive ADT (`Grove(Rose<T>,
        # Forest<T>)`) with no bare-`T` field — fall back to the nested-descent
        # recovery that digs the parameter out of a nested generic field.  Trying
        # `_full_ctor_type_name` first (any `<…>` result wins) means the two
        # recoveries never disagree on a shape the direct path already handles.
        full = self._full_ctor_type_name(operand)
        if full is not None and "<" in full:
            return full
        # #934 fallback applies only to a `ConstructorCall` — `_recover_ctor_ptype`
        # reads `.name`/args (a `SlotRef` has neither) and returns None for a
        # non-generic ADT, so a non-descendable or non-generic operand keeps the
        # bare name `_full_ctor_type_name` already produced (the release path).
        if isinstance(operand, ast.ConstructorCall):
            recovered = self._recover_ctor_ptype(operand, bare)
            if recovered is not None and recovered != bare:
                return recovered
        return full or bare

    def _full_ctor_type_name(self, operand: ast.Expr) -> str | None:
        """Fully-qualified Vera type name of a constructor operand (#923).

        Recurses through nested `ConstructorCall` fields so every level's type
        argument is recovered: for each field that maps to an ADT type parameter
        (`_ctor_adt_tp_indices`), the field's own full name is reconstructed by
        recursing on the field expression.  A non-`ConstructorCall` expression
        yields its bare `_infer_vera_type` name (a nested `List<Int>` bottoms out
        at the `Int` leaf, a nullary `Nil` at the bare `List`).  Returns ``None``
        only when the base ADT name itself cannot be resolved; a field whose type
        argument cannot be inferred leaves that position bare (the base ADT name
        with no `<…>`), matching the lost-type-arg shape codegen already handles.
        """
        if not isinstance(operand, ast.ConstructorCall):
            return self._infer_vera_type(operand)
        base = self._ctor_to_adt_name(operand.name)
        if base is None:
            return None
        # ctor-owner-exempt: resolved in the compiling namespace's scoped
        # projection (#1436)
        tp_indices = self._ctor_adt_tp_indices.get(operand.name)
        tp_count = self._adt_tp_counts.get(base, 0)
        if not tp_indices or tp_count == 0:
            return base
        slots: list[str | None] = [None] * tp_count
        for field_i, tp_idx in enumerate(tp_indices):
            if tp_idx is not None and field_i < len(operand.args):
                slots[tp_idx] = self._full_ctor_type_name(operand.args[field_i])
        if all(s is not None for s in slots):
            return f"{base}<{', '.join(s for s in slots if s is not None)}>"
        return base

    def _recover_lost_type_arg(
        self, lv: str | None, other: ast.Expr,
    ) -> str | None:
        """Recover a bare generic-ADT operand's type argument from its sibling.

        A `ResultRef`/`SlotRef` operand of a composite `==` carries no arguments
        of its own to recover a dropped type parameter from (unlike a
        `ConstructorCall`, handled by `_parameterize_ctor_operand`).  When `lv`
        is a bare generic-ADT name (its base declares type parameters but `lv`
        has no `<…>`) — the #772 monomorphization residue where `@T.result`
        became `@Box.result`, dropping `<Int>` — try the OTHER `==` operand: a
        `ConstructorCall` sibling (`@Box.result == MkBox(7)`) still carries the
        concrete argument, so `_parameterize_ctor_operand` recovers `Box<Int>`.
        Returns the parameterized name on success, else `lv` unchanged (the
        caller then treats the still-bare name as a lost-arg clone).
        """
        if lv is None or "<" in lv:
            return lv
        base = lv
        if not self._adt_tp_param_names.get(base):
            return lv  # not a generic ADT — nothing to recover
        recovered = self._parameterize_ctor_operand(other, base)
        return recovered if recovered is not None else lv

    # Non-ADT type-name bases that are nonetheless CONCRETE (primitives +
    # built-in containers).  A single-segment type-argument base that is none
    # of these AND is not a registered ADT is an unresolved type VARIABLE
    # (`T`), the #912 round-2 signal.
    _CONCRETE_NON_ADT_BASES = frozenset(
        {
            "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit", "Never",
            "Array", "Map", "Set", "Tuple", "Decimal", "Json",
        }
    )

    def _type_arg_is_free_var(self, arg: str) -> bool:
        """Whether a type-argument name is an unresolved type VARIABLE (#912).

        `arg` is a rendered type-name string (`"Int"`, `"Box<Int>"`, `"T"`).
        Its base is a free type variable when it is neither a known concrete
        base (primitive or built-in container, `_CONCRETE_NON_ADT_BASES`) nor a
        registered ADT (`_adt_type_names`) — i.e. a bare `T` left un-substituted
        in a generic function's `@Box<T>` operand that the monomorphizer did not
        specialize to a concrete clone.

        #1070/#1076: an ALIAS or transparent-`Future` spelling (`U` via
        `type U = Unit;`, `MyInt` via `type MyInt = Int;`, `Future<Int>`,
        `FU`, chains) is NOT a free variable — it names a concrete type.
        Classify on the GROUND spelling: without this, `Box<U>` / `Box<MyInt>`
        were classified as dead base-generic clones and their `==` fell back
        to the scalar POINTER compare — structurally equal values compared
        unequal, silently, on a check-green program.  A genuinely unregistered
        name (`T`) grounds to itself and still classifies free.
        """
        arg = self._canonical_field_type(arg.strip())
        base = arg.split("<", 1)[0]
        return (
            base not in self._CONCRETE_NON_ADT_BASES
            and self._value_adt_key(arg) is None
        )

    def _has_free_type_var_arg(self, lv: str) -> bool:
        """Whether `lv` carries a type argument that is an unresolved type var.

        Parses the top-level type arguments out of a rendered name
        (`"Box<T>"` → `["T"]`, `"Map<K, V>"` → `["K", "V"]`, respecting nesting)
        and returns True if any is a free type variable (`_type_arg_is_free_var`).
        Such a name (`Box<T>`) cannot dispatch to a concrete `$eq_<type>` helper,
        so the composite `==` falls back to the scalar lowering rather than
        crashing the derivability gate.
        """
        lt = lv.find("<")
        if lt == -1:
            return False
        inner = lv[lt + 1 : lv.rfind(">")]
        args: list[str] = []
        depth = 0
        start = 0
        for i, ch in enumerate(inner):
            if ch == "<":
                depth += 1
            elif ch == ">":
                depth -= 1
            elif ch == "," and depth == 0:
                args.append(inner[start:i])
                start = i + 1
        args.append(inner[start:])
        return any(self._type_arg_is_free_var(a) for a in args if a.strip())

    def _is_lost_type_arg_clone(self, lv: str, lv_base: str | None) -> bool:
        """Whether `lv` is a generic-ADT name that lost its type argument (#912).

        Two lost-argument shapes route the composite `==` to the scalar
        (pointer) lowering it used before #912 — rather than raising a spurious
        E613 (or crashing the derivability gate) on an otherwise-valid program:

        1. **Bare** generic-ADT name (round 1): the base ADT declares type
           parameters yet `lv` carries no `<…>` argument — the #772
           monomorphization residue where `@T.result` became `@Box.result` for
           a `Box<T>` clone, dropping `<Int>`.

        2. **Free-type-variable** argument (round 2, #912): `lv` carries a `<…>`
           whose argument is an unresolved type variable (`Box<T>`) — the BASE
           generic clone of a function generic over the parameterized ADT
           itself, whose `@Box<T>` operands the monomorphizer left as a free
           `T`.  Routing this to the scalar lowering is SOUND — and the scalar
           compare NEVER runs — because the base generic clone is DEAD CODE:
           `$id2` (the `Box<T>` clone) is emitted but is never a call target and
           never exported (higher-order escape of a bare generic fn is a parse
           error, E005, so it cannot be routed into a `call_indirect`/table).
           Every *reachable* call dispatches to a monomorphized clone
           (`$id2$Int`) whose `@Box<Int>.result == @Box<Int>.0` is lowered
           STRUCTURALLY (`call $eq_Box_LInt_R`) — `Box<Int>` is concrete, so it
           is NOT matched here — correctly discharging the composite `==` at its
           Tier-1 proof.  (The `ensures` obligation IS proved at Tier 1, the
           verifier substituting `T:=Int`; that is exactly why the reachable
           path must be — and is — structural.)  This is verified by
           `rebox`-style tests where the result is a FRESHLY-constructed,
           structurally-equal, DIFFERENT-pointer box: Tier-1-verified AND runs
           correctly (via the structural mono clone), where a reachable scalar
           pointer compare would have trapped.  The scalar fallback here merely
           lets the dead base clone COMPILE (as harmless dead `i32.eq`) instead
           of E613-erroring and being dropped, which failed the whole compile.

        A genuinely non-derivable operand — a `Map`/`Array`-field ADT (a
        concrete non-Eq field, and the ADT itself has NO type parameters),
        `Tuple` (variadic placeholder), an `Md*` builtin, or a generic ADT with
        a present CONCRETE non-Eq argument (`Box<Array<Int>>`, whose argument is
        a known concrete type, NOT a free variable) — is NOT a lost-arg clone,
        so it still routes to `_translate_adt_eq` and raises the correct E613,
        keeping the checker↔codegen lockstep the #732 differential pins.  Relies
        on imported generic ADTs' type-parameter metadata being propagated
        (`modules.py`, #912) so `_adt_tp_param_names` answers for cross-module
        `Box<T>` too, not just local ADTs.
        """
        if "<" in lv:
            return self._has_free_type_var_arg(lv)
        return bool(self._adt_tp_param_names.get(lv_base or ""))

    @staticmethod
    def _split_type_name(name: str) -> tuple[str, list[str]]:
        """Split a rendered type name into ``(base, top-level args)`` (#994 F2).

        ``"Option<Option<Int>>"`` → ``("Option", ["Option<Int>"])`` (respecting
        nesting depth so a comma inside a nested ``<…>`` does not split).  A bare
        name yields ``(name, [])``.
        """
        lt = name.find("<")
        if lt == -1:
            return name.strip(), []
        base = name[:lt].strip()
        inner = name[lt + 1 : name.rfind(">")]
        args: list[str] = []
        depth = 0
        start = 0
        for i, ch in enumerate(inner):
            if ch == "<":
                depth += 1
            elif ch == ">":
                depth -= 1
            elif ch == "," and depth == 0:
                args.append(inner[start:i].strip())
                start = i + 1
        tail = inner[start:].strip()
        if tail:
            args.append(tail)
        return base, args

    def _eq_type_name_fully_concrete(self, name: str) -> bool:
        """Whether a rendered ADT type name is fully instantiated (#994 F2).

        Fully concrete = no free type variable and no under-parameterized ADT
        at ANY nesting level: every registered-ADT segment carries EXACTLY its
        declared type-parameter count and every argument is itself fully
        concrete.  This rejects the two shapes the structural-Eq derivation
        cannot lower on a check-green ``forall<T>`` program:

        * a payload-less nested constructor operand — ``Some(None)`` recovers as
          the erased ``Option<Option>`` (inner ``Option`` missing its argument,
          since a bare ``None`` carries none to recover ``<Int>`` from); and
        * a dead base generic clone's slot operand — ``Option<Option<T>>``, whose
          nested free ``T`` the top-level-only ``_has_free_type_var_arg`` misses.

        A GENUINELY concrete-but-non-Eq name (``Box<Array<Int>>`` — ``Array`` is
        not Eq, but the argument is a known concrete type; or ``Tuple<Int, Int>``
        — variadic, never Eq) is fully concrete, so it still routes to
        ``_translate_adt_eq`` and raises the CORRECT E613, keeping the
        checker↔codegen lockstep the #732 differential pins.
        """
        base, args = self._split_type_name(name)
        if base in self._CONCRETE_NON_ADT_BASES:
            # Primitive / built-in container (``Int``, ``Array<T>``, ``Tuple<…>``):
            # concrete iff every argument is (``Array<Int>`` yes, ``Array<T>`` no,
            # bare ``Int`` yes).  Checked BEFORE the ADT branch because a variadic
            # container (``Tuple``) is registered as a 0-type-parameter ADT yet
            # renders WITH arguments, which the exact tp-count check below would
            # wrongly flag as under-parameterized — silently dropping the loud
            # E613 that a non-Eq ``Tuple`` comparison must raise.
            return all(self._eq_type_name_fully_concrete(a) for a in args)
        if self._value_adt_key(base) is not None:
            if len(args) != self._adt_tp_counts.get(base, 0):
                return False  # under-parameterized: an argument was erased
            return all(self._eq_type_name_fully_concrete(a) for a in args)
        # #1070/#1076: an ALIAS or transparent-`Future` spelling (`U`,
        # `MyInt`, `FU`, `Future<Int>`, chains) is NOT a free type variable —
        # ground it and re-judge (`U` → `Unit`, `MyInt` → `Int`, `Future<Int>`
        # → `Int`).  Without this, `Box<U>` / `Box<MyInt>` failed the
        # concreteness gate and the `==` dispatch fell back to the scalar i32
        # POINTER compare: two structurally equal values compared unequal,
        # silently, on a check-green program (the checker resolves the alias
        # and accepts the Eq).  A genuine `T` grounds to itself: no recursion.
        canonical = self._canonical_field_type(name)
        if canonical != name:
            return self._eq_type_name_fully_concrete(canonical)
        # A single-segment name that is neither a registered ADT nor a known
        # concrete base is an unresolved type VARIABLE (``T``).
        return False

    def _eq_operand_full_name(
        self, operand: ast.Expr, other: ast.Expr, bare: str | None,
    ) -> str | None:
        """Fully-recover an ``==`` operand's ADT type name (#994 F2).

        Factors the established recovery chain (used for the left operand since
        #772/#912/#932) so it can be applied to EITHER operand symmetrically:

        * ``_parameterize_ctor_operand`` — recover a ``ConstructorCall``'s dropped
          type argument from its own arguments (``Some(1)`` → ``Option<Int>``);
        * ``_recover_lost_type_arg`` — recover a bare generic-ADT slot operand's
          argument from the *other* operand (``@Box.result == MkBox(7)`` →
          ``Box<Int>``);
        * the ``_eq_full_type_names`` map — expand a truncated one-level clone
          name to its fully-nested form (#932).

        ``bare`` is *operand*'s already-computed ``_infer_vera_type`` name.

        #1078: an ``IndexExpr`` operand (an array ELEMENT) arrives as the
        element type's bare head — ``_infer_index_element_type`` computes the
        full element ``NamedType`` and then returns only ``.name`` (``Box<Int>``
        → ``"Box"``) — so a parameterized element was classified as a
        lost-type-argument clone and ``==`` silently fell back to the scalar
        POINTER compare.  The indexed collection carries its complete type
        arguments, so re-derive the full element spelling from it.
        """
        name = self._parameterize_ctor_operand(operand, bare)
        if (isinstance(operand, ast.IndexExpr)
                and name is not None
                and "<" not in name):
            te = self._infer_index_element_type_expr(operand)
            if te is not None and te.type_args and te.name == name:
                name = self._format_named_type(te)
        name = self._recover_lost_type_arg(name, other)
        if name is not None:
            name = self._eq_full_type_names.get(name, name)
        return name

    def _translate_adt_eq(
        self,
        left: list[str],
        right: list[str],
        adt_name: str,
        node: ast.Expr | None = None,
    ) -> list[str] | None:
        """Emit a structural-equality comparison of two ADT values.

        ``adt_name`` is the comparison site's Vera type name — bare
        (``"Outer"``) for a concrete ADT or parameterized (``"Box<String>"``)
        for a generic instantiation.  Checks structural derivability (the same
        E613 gate the generic constraint path uses; see the section comment),
        then requests the matching ``$eq_<type>`` helper (generating it, and
        any nested-ADT helpers, on demand) and returns
        ``left ++ right ++ [call $eq_<type>]``.

        ``node`` is the comparison's AST node, for the E613 diagnostic span
        when the operand type is not derivable.
        """
        if (self._adt_eq_derivable is not None
                and not self._adt_eq_derivable(adt_name)):
            raise AdtEqNotDerivableError(adt_name, node)
        fn_name = self._request_adt_eq_helper(adt_name)
        if fn_name is None:
            return None
        return left + right + [f"call {fn_name}"]

    def _adt_eq_fn_name(self, type_name: str) -> str:
        """Mangle a Vera type name into its ``$eq_<type>`` helper name.

        Injective over the type-name grammar: ``<`` / ``>`` / ``,`` / space are
        distinct escapes so ``Box<Int>`` and a bare ADT literally named
        ``Box_Int`` cannot collide.  Delegates to the shared
        :func:`vera.monomorphize.mangle_type_name` escape (#775) — the same
        convention mono-clone symbols use, so the two naming families stay
        in lockstep.
        """
        from vera.monomorphize import mangle_type_name

        return f"$eq_{mangle_type_name(type_name)}"

    def _request_adt_eq_helper(self, type_name: str) -> str | None:
        """Ensure a ``$eq_<type>`` helper exists; return its function name.

        Deduped by name and guarded against recursion via ``_adt_eq_pending``
        so a self-referential ADT emits exactly one helper.
        """
        from vera.monomorphize import Monomorphizer

        parsed = Monomorphizer._parse_type_name(type_name)
        base = parsed.name
        if self._value_adt_key(type_name) is None:
            return None
        fn_name = self._adt_eq_fn_name(type_name)
        if fn_name in self._adt_eq_helpers or fn_name in self._adt_eq_pending:
            return fn_name
        self._adt_eq_pending.add(fn_name)
        body = self._generate_adt_eq_fn(fn_name, base, parsed)
        if body is None:
            self._adt_eq_pending.discard(fn_name)
            return None
        self._adt_eq_helpers[fn_name] = body
        return fn_name

    def _generate_adt_eq_fn(
        self, fn_name: str, base: str, parsed: ast.NamedType,
    ) -> str | None:
        """Generate the full WAT text of a ``$eq_<type>`` helper function.

        Signature ``(param $l i32) (param $r i32) (result i32)`` → 1 if the two
        pointers are structurally equal, else 0.  Field dispatch is by Vera
        type (see the section comment above).  Nested-ADT fields recurse by
        requesting (and thereby generating) that ADT's own helper first.

        Bounded against POLYMORPHIC recursion (#933): a non-uniform ADT
        (`Box<T>` field `Box<Box<T>>`) mints a strictly deeper type at each
        nested-helper request, so the `_adt_eq_pending` guard never routes back
        to a self-call and this generation recurs unboundedly.  The
        derivability gate (`_adt_satisfies_eq`) normally rejects such a type as
        a clean E613 *before* generation begins; this cap is the belt-and-
        suspenders backstop on the SAME shared depth so a program that reaches
        the generator still degrades to a skip rather than a traceback.
        """
        if self._derived_helper_depth >= self._derived_helper_depth_cap:
            return None
        self._derived_helper_depth += 1
        try:
            return self._generate_adt_eq_fn_body(fn_name, base, parsed)
        finally:
            self._derived_helper_depth -= 1

    def _generate_adt_eq_fn_body(
        self, fn_name: str, base: str, parsed: ast.NamedType,
    ) -> str | None:
        """Body of :meth:`_generate_adt_eq_fn` (depth-bound wrapper above)."""
        from vera.monomorphize import Monomorphizer

        # Concrete type args for this instantiation, mapped onto the ADT's
        # type parameters, so a field typed by a type parameter resolves to the
        # concrete type argument (`Box<String>` → field "T" ↦ "String").
        type_args = [
            Monomorphizer._format_type_name(a)
            for a in (parsed.type_args or ())
            if isinstance(a, ast.NamedType)
        ]
        # Param-NAME → concrete-arg mapping, for params nested inside a
        # parameterized field type (the recursive tail `Cons(T, List<T>)`
        # under `List<Int>` needs `List<T>` → `List<Int>`).
        tp_names = self._adt_tp_param_names.get(base, ())
        tp_mapping = dict(zip(tp_names, type_args))

        # #1414: enumerate the constructors of the ADT being compared out
        # of ITS OWN table.  Both maps here are keyed by bare constructor
        # name across every ADT, so a user declaration sharing one of this
        # type's constructor names displaces the layout AND the ownership
        # entry.  LATENT under current coverage, and measured to be:
        # forcing this branch back to the flat map leaves the whole
        # tag-index battery green, because the writer fix in
        # `data.py` already gives the value the right tag and this
        # enumeration is only reached for types the collision does not
        # reorder.  Converted anyway, on the same rule as the other
        # owner-qualified reads — a site holding the owner must not ask a
        # table that cannot represent one (PR #1419 review).
        own = self._adt_ctor_layouts.get(base)
        # Same measured-dead fallback as `_composite_ctor_plans`, removed on
        # the same evidence.
        adt_ctors = sorted((own or {}).items(), key=lambda x: x[1].tag)
        if not adt_ctors:
            raise CodegenInvariantError(  # pragma: no cover
                "ADT equality on a type with no constructors")

        # A "field plan" per constructor: the concrete (offset, field_type)
        # per field, with type parameters substituted.  Offsets are recomputed
        # from the concrete field WASM types — the bare layout stores each
        # generic field as an i32 pointer, but a String instantiation lays the
        # field out as an i32_pair, exactly as the construction site does.
        body: list[str] = []
        # tag mismatch → 0
        body.append("    local.get 0")
        body.append("    i32.load")
        body.append("    local.set $tag")
        body.append("    local.get $tag")
        body.append("    local.get 1")
        body.append("    i32.load")
        body.append("    i32.eq")
        body.append("    if (result i32)")

        ctors_with_fields = [
            (name, lay) for name, lay in adt_ctors if lay.field_offsets
        ]
        if not ctors_with_fields:
            body.append("      i32.const 1")
        else:
            for depth, (cname, layout) in enumerate(ctors_with_fields):
                pad = "  " * (depth + 3)
                body.append(f"{pad}local.get $tag")
                body.append(f"{pad}i32.const {layout.tag}")
                body.append(f"{pad}i32.eq")
                body.append(f"{pad}if (result i32)")
                fpad = pad + "  "
                # Resolve concrete field types (substitute type params).  A
                # field that is a type PARAMETER (per `_ctor_adt_tp_indices`)
                # resolves positionally to the matching concrete type argument;
                # any other field deep-substitutes param NAMES nested inside a
                # parameterized declared type (`List<T>` → `List<Int>`).
                # ctor-owner-exempt: owner-qualified above; parsed-name path
                tp_idx = self._ctor_adt_tp_indices.get(cname)
                raw_types = (
                    layout.field_types
                    if layout.field_types
                    else ("<opaque>",) * len(layout.field_offsets)
                )
                field_type_names = [
                    self._resolve_field_type_for_eq(
                        raw, i, tp_idx, type_args, tp_mapping,
                    )
                    for i, raw in enumerate(raw_types)
                ]
                # Concrete offsets from concrete WASM types.
                concrete = self._concrete_field_layout(field_type_names)
                # #1043: a zero-size Unit field ("unit" wt) is equal by
                # definition — emit NO comparison for it (and don't advance the
                # `i32.and` chain, which would underflow the stack).  If a
                # constructor's fields are ALL zero-size, its two values are
                # equal once the tags match: the then-branch of this
                # `if (result i32)` must still leave an i32, so emit a constant
                # `1` (mirrors the no-field-constructors `i32.const 1` above).
                comparable = [
                    (offset, ftype)
                    for (offset, wt), ftype in zip(concrete, field_type_names)
                    if wt != "unit"
                ]
                if not comparable:
                    body.append(f"{fpad}i32.const 1")
                else:
                    first = True
                    for offset, ftype in comparable:
                        cmp_instrs = self._emit_field_eq(offset, ftype)
                        if cmp_instrs is None:
                            raise CodegenInvariantError(  # pragma: no cover
                                f"ADT field type {ftype!r} of {cname!r} has no Eq "
                                f"comparison; the E613 gate should have rejected it")
                        body.extend(fpad + ln for ln in cmp_instrs)
                        if not first:
                            body.append(f"{fpad}i32.and")
                        first = False
                body.append(f"{pad}else")
            inner_pad = "  " * (len(ctors_with_fields) + 3)
            body.append(f"{inner_pad}i32.const 1")
            for depth in range(len(ctors_with_fields) - 1, -1, -1):
                pad = "  " * (depth + 3)
                body.append(f"{pad}end")

        body.append("    else")
        body.append("      i32.const 0")
        body.append("    end")

        header = (
            f"  (func {fn_name} (param $l i32) (param $r i32) (result i32)\n"
            f"    (local $tag i32)\n"
        )
        return header + "\n".join(body) + "\n  )"

    def _resolve_field_type_for_eq(
        self,
        raw: str,
        field_index: int,
        tp_idx: tuple[int | None, ...] | None,
        type_args: list[str],
        tp_mapping: dict[str, str],
    ) -> str:
        """Resolve a declared field type against the instantiation's type args.

        ``raw`` is the DECLARED field type (``"T"``, ``"String"``,
        ``"Inner"``, ``"List<T>"``).  If field ``field_index`` is a bare type
        PARAMETER — per the per-constructor ``_ctor_adt_tp_indices`` table —
        its position maps into ``type_args`` (``Box<String>`` field-0 ↦
        ``"String"``).  Otherwise param NAMES nested inside a parameterized
        declared type are deep-substituted (``List<T>`` ↦ ``List<Int>`` under
        a ``List<Int>`` comparison); a fully concrete type passes through
        unchanged.

        #1070/#1076: the resolution is GROUNDED — alias chains resolved,
        transparent ``Future<...>`` peeled (``"U"`` → ``"Unit"``, ``"MyStr"``
        → ``"String"``, ``"FI"`` → ``"Int"``).  Registration already grounds
        a DECLARED field type (#773/#1043), but a type argument keeps its
        use-site spelling, and the show/hash/`$eq` field dispatches key on
        this NAME: ungrounded they treated the alias as an unknown type and
        loud-skipped (show/hash) or mis-sized and mis-compared it (`$eq`).
        """
        if tp_idx is not None and field_index < len(tp_idx):
            pos = tp_idx[field_index]
            if pos is not None and pos < len(type_args):
                return self._canonical_field_type(type_args[pos])
        from vera.monomorphize import substitute_type_param_names

        return self._canonical_field_type(
            substitute_type_param_names(raw, tp_mapping)
        )

    def _canonical_field_type(self, name: str) -> str:
        """Ground spelling of a field / type-argument name (#1070, #1076).

        Resolves alias chains to their target's compound spelling (the shared
        `_canonicalize_alias_slot_name` walk) and peels transparent
        ``Future<...>`` wrappers to their payload (representation-identical,
        #841), repeating until stable: ``U`` → ``"Unit"``, ``FU`` /
        ``Future<Unit>`` → ``"Unit"``, ``MyInt`` → ``"Int"``, ``FI`` /
        ``Future<Int>`` → ``"Int"``.  A non-alias, non-Future name — a
        concrete type or a genuine free type variable ``T`` — returns
        unchanged; alias arguments NESTED inside a compound (``Box<U>``) are
        not touched here (each consumer canonicalises per nesting level).

        The resolved-field-type consumers (`_eq_field_wasm_type`,
        `_show_value`, `_hash_value`, `_emit_field_eq`) dispatch on the Vera
        type NAME, and the `==` dispatch gates classify it — the ground
        spelling is the one they all understand.  Mirrors
        ``RegistrationMixin._field_vera_type_name``, which grounds DECLARED
        field types the same way at registration (#773/#1043); a type
        ARGUMENT arrives spelled as at the use site and is grounded here.
        """
        seen: frozenset[str] = frozenset()
        while True:
            name, seen = self._canonicalize_alias_slot_name(name, seen)
            if name.startswith("Future<") and name.endswith(">"):
                name = name[7:-1]
                continue
            return name

    def _concrete_field_layout(
        self, field_type_names: list[str],
    ) -> list[tuple[int, str]]:
        """Recompute (offset, wasm_type) per field from concrete Vera types.

        Mirrors the construction site (``_translate_constructor_call``): tag at
        offset 0 (4 bytes), then each field aligned to its natural alignment.
        """
        # Through `helpers.field_layout`, the ONE rule construction lays an
        # object out by, rather than a copy of its widths: `"unit"` (a
        # zero-size Unit field) is size 0 / align 1 there, so it neither
        # aligns nor advances the offset, which is the convention
        # `_translate_constructor_call` uses (#1043).
        offset = 4
        out: list[tuple[int, str]] = []
        for ftype in field_type_names:
            wt = self._eq_field_wasm_type(ftype)
            field_off, offset = field_layout(offset, wt)
            out.append((field_off, wt))
        return out

    def _eq_field_wasm_type(self, ftype: str) -> str:
        """WASM rep of a concrete field type for structural-eq layout."""
        # #1070/#1076: ground the spelling first — a type ARGUMENT arrives as
        # spelled at the use site (`Box<U>`, `Box<MyInt>`, `Box<Future<Int>>`,
        # alias chains), and the raw-name dispatch mis-sized every such
        # spelling (an alias fell to the 4-byte ADT-pointer default; a
        # transparent Future missed its payload's width): the wildcard width
        # recomputation (#1060) then shifted every later field's read on a
        # check-green program.  Grounding makes each spelling behave exactly
        # like its target written literally.
        ftype = self._canonical_field_type(ftype)
        # #1043: a zero-size field is the `"unit"` sentinel, which makes
        # `_concrete_field_layout` advance the offset by nothing (matching
        # construction) and lets the `$eq` emitter skip the (equal-by-
        # definition) comparison.  Post-grounding, every erases-to-Unit
        # spelling IS the literal name.
        if ftype == "Unit":
            return "unit"
        base = ftype.split("<", 1)[0]
        if base in ("Int", "Nat"):
            return "i64"
        if base == "Float64":
            return "f64"
        if base in ("Bool", "Byte"):
            return "i32"
        # #1331/#1539: a data type's value is a pointer, a `data Array`'s
        # among them, which the container arm below would measure as a pair.
        if self._value_adt_key(ftype) is not None:
            return "i32"
        if base in ("String", "Array"):
            return "i32_pair"
        # ADT pointer (or opaque) → i32
        return "i32"

    def _emit_field_eq(
        self, offset: int, ftype: str,
    ) -> list[str] | None:
        """Emit the per-field comparison for a helper, leaving i32 on the stack.

        ``$l`` / ``$r`` (locals 0 / 1) are the two struct pointers.  Returns
        None if the field type has no Eq comparison (should be unreachable —
        the E613 gate rejects such ADTs).
        """
        base = ftype.split("<", 1)[0]
        # Scalar Eq primitive.
        if base in ("Int", "Nat"):
            return [
                "local.get 0", f"i64.load offset={offset}",
                "local.get 1", f"i64.load offset={offset}",
                "i64.eq",
            ]
        if base == "Float64":
            return [
                "local.get 0", f"f64.load offset={offset}",
                "local.get 1", f"f64.load offset={offset}",
                "f64.eq",
            ]
        if base in ("Bool", "Byte", "Unit"):
            return [
                "local.get 0", f"i32.load offset={offset}",
                "local.get 1", f"i32.load offset={offset}",
                "i32.eq",
            ]
        # String: content comparison via the $eq_String helper.
        if base == "String":
            self._request_string_eq_helper()
            return [
                "local.get 0", f"i32.load offset={offset}",
                "local.get 0", f"i32.load offset={offset + 4}",
                "local.get 1", f"i32.load offset={offset}",
                "local.get 1", f"i32.load offset={offset + 4}",
                "call $eq_String",
            ]
        # Nested ADT: recurse into its own helper.
        if self._value_adt_key(ftype) is not None:
            nested_fn = self._request_adt_eq_helper(ftype)
            if nested_fn is None:
                return None
            return [
                "local.get 0", f"i32.load offset={offset}",
                "local.get 1", f"i32.load offset={offset}",
                f"call {nested_fn}",
            ]
        return None

    def _request_string_eq_helper(self) -> None:
        """Ensure the standalone ``$eq_String`` content-comparison helper."""
        fn_name = "$eq_String"
        if fn_name in self._adt_eq_helpers:
            return
        self._adt_eq_helpers[fn_name] = self._emit_string_eq_fn()

    def _request_string_cmp_helper(self) -> None:
        """Ensure the standalone ``$cmp_String`` three-way ordering helper (#927)."""
        fn_name = "$cmp_String"
        if fn_name in self._adt_eq_helpers:
            return
        self._adt_eq_helpers[fn_name] = self._emit_string_cmp_fn()

    @staticmethod
    def _emit_string_cmp_fn() -> str:
        """Standalone String three-way lexicographic-ordering helper (#927).

        ``(param $p1 i32)(param $l1 i32)(param $p2 i32)(param $l2 i32)`` →
        i32 in {-1, 0, 1}: ``-1`` if s1 < s2, ``0`` if equal, ``1`` if s1 > s2.

        Byte-wise comparison over ``min(l1, l2)`` bytes (UTF-8 preserves
        code-point order under unsigned byte comparison); on the first
        differing byte the smaller byte's string is less.  If one string is a
        proper prefix of the other, the shorter is less.  This matches Z3's
        ``StringSort`` ordering (proper-prefix-is-less, byte order), which the
        verifier already uses for String ``<`` — so ``vera verify`` and
        ``vera run`` agree on String ordering.
        """
        return (
            "  (func $cmp_String "
            "(param $p1 i32) (param $l1 i32) (param $p2 i32) (param $l2 i32) "
            "(result i32)\n"
            "    (local $idx i32)\n"
            "    (local $min i32)\n"
            "    (local $b1 i32)\n"
            "    (local $b2 i32)\n"
            # min = l1 < l2 ? l1 : l2
            "    local.get $l1\n"
            "    local.get $l2\n"
            "    i32.lt_u\n"
            "    if (result i32)\n"
            "      local.get $l1\n"
            "    else\n"
            "      local.get $l2\n"
            "    end\n"
            "    local.set $min\n"
            "    i32.const 0\n"
            "    local.set $idx\n"
            "    block $done (result i32)\n"
            "      loop $lp\n"
            # if idx >= min, exit the byte loop → compare lengths
            "        local.get $idx\n"
            "        local.get $min\n"
            "        i32.ge_u\n"
            "        if\n"
            # lengths: l1 < l2 → -1 ; l1 > l2 → 1 ; equal → 0
            "          local.get $l1\n"
            "          local.get $l2\n"
            "          i32.lt_u\n"
            "          if\n"
            "            i32.const -1\n"
            "            br $done\n"
            "          end\n"
            "          local.get $l1\n"
            "          local.get $l2\n"
            "          i32.gt_u\n"
            "          if\n"
            "            i32.const 1\n"
            "            br $done\n"
            "          end\n"
            "          i32.const 0\n"
            "          br $done\n"
            "        end\n"
            # b1 = p1[idx], b2 = p2[idx]
            "        local.get $p1\n"
            "        local.get $idx\n"
            "        i32.add\n"
            "        i32.load8_u\n"
            "        local.set $b1\n"
            "        local.get $p2\n"
            "        local.get $idx\n"
            "        i32.add\n"
            "        i32.load8_u\n"
            "        local.set $b2\n"
            # if b1 < b2 → -1
            "        local.get $b1\n"
            "        local.get $b2\n"
            "        i32.lt_u\n"
            "        if\n"
            "          i32.const -1\n"
            "          br $done\n"
            "        end\n"
            # if b1 > b2 → 1
            "        local.get $b1\n"
            "        local.get $b2\n"
            "        i32.gt_u\n"
            "        if\n"
            "          i32.const 1\n"
            "          br $done\n"
            "        end\n"
            # bytes equal → advance
            "        local.get $idx\n"
            "        i32.const 1\n"
            "        i32.add\n"
            "        local.set $idx\n"
            "        br $lp\n"
            "      end\n"
            "      i32.const 0\n"
            "    end\n"
            "  )"
        )

    @staticmethod
    def _emit_string_eq_fn() -> str:
        """Standalone String content-equality helper.

        ``(param $p1 i32)(param $l1 i32)(param $p2 i32)(param $l2 i32)`` → i32.
        Length check, then a byte-by-byte loop — the same algorithm as the
        inline ``_translate_string_eq``, hoisted into a reusable function so a
        String ADT field compares by content, not pointer.
        """
        return (
            "  (func $eq_String "
            "(param $p1 i32) (param $l1 i32) (param $p2 i32) (param $l2 i32) "
            "(result i32)\n"
            "    (local $idx i32)\n"
            "    local.get $l1\n"
            "    local.get $l2\n"
            "    i32.ne\n"
            "    if (result i32)\n"
            "      i32.const 0\n"
            "    else\n"
            "      i32.const 0\n"
            "      local.set $idx\n"
            "      block $done (result i32)\n"
            "        loop $lp\n"
            "          local.get $idx\n"
            "          local.get $l1\n"
            "          i32.ge_u\n"
            "          if\n"
            "            i32.const 1\n"
            "            br $done\n"
            "          end\n"
            "          local.get $p1\n"
            "          local.get $idx\n"
            "          i32.add\n"
            "          i32.load8_u\n"
            "          local.get $p2\n"
            "          local.get $idx\n"
            "          i32.add\n"
            "          i32.load8_u\n"
            "          i32.ne\n"
            "          if\n"
            "            i32.const 0\n"
            "            br $done\n"
            "          end\n"
            "          local.get $idx\n"
            "          i32.const 1\n"
            "          i32.add\n"
            "          local.set $idx\n"
            "          br $lp\n"
            "        end\n"
            "        i32.const 1\n"
            "      end\n"
            "    end\n"
            "  )"
        )

    # -----------------------------------------------------------------
    # String equality
    # -----------------------------------------------------------------

    def _translate_string_eq(
        self, left: list[str], right: list[str],
    ) -> list[str]:
        """Generate WASM for string equality (byte-by-byte).

        Compares two (ptr, len) pairs:
        1. Quick length check — if lengths differ, false
        2. Same pointer shortcut — if ptrs match, true
        3. Byte-by-byte comparison loop
        """
        ptr1 = self.alloc_local("i32")
        len1 = self.alloc_local("i32")
        ptr2 = self.alloc_local("i32")
        len2 = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        result = self.alloc_local("i32")

        instrs: list[str] = []
        # Store both strings
        instrs += left + [f"local.set {len1}", f"local.set {ptr1}"]
        instrs += right + [f"local.set {len2}", f"local.set {ptr2}"]

        # Default: equal (1)
        instrs += ["i32.const 1", f"local.set {result}"]

        # Length check
        instrs += [
            f"local.get {len1}", f"local.get {len2}", "i32.ne",
            "if",
            "  i32.const 0", f"  local.set {result}",
            "else",
        ]

        # Pointer check (fast path for interned strings)
        instrs += [
            f"  local.get {ptr1}", f"  local.get {ptr2}", "  i32.ne",
            "  if",
        ]

        # Byte-by-byte comparison loop
        instrs += [
            "    i32.const 0", f"    local.set {idx}",
            "    block $seq_break",
            "      loop $seq_loop",
            f"        local.get {idx}",
            f"        local.get {len1}",
            "        i32.ge_u",
            "        br_if $seq_break",
            # Compare bytes at idx
            f"        local.get {ptr1}",
            f"        local.get {idx}",
            "        i32.add",
            "        i32.load8_u",
            f"        local.get {ptr2}",
            f"        local.get {idx}",
            "        i32.add",
            "        i32.load8_u",
            "        i32.ne",
            "        if",
            "          i32.const 0",
            f"          local.set {result}",
            "          br $seq_break",
            "        end",
            # Increment idx
            f"        local.get {idx}",
            "        i32.const 1",
            "        i32.add",
            f"        local.set {idx}",
            "        br $seq_loop",
            "      end",  # loop
            "    end",    # block
        ]

        # Close pointer-check if and length-check if
        instrs += ["  end", "end"]
        instrs += [f"local.get {result}"]
        return instrs

    def _translate_f64_mod(
        self, left: list[str], right: list[str]
    ) -> list[str]:
        """Translate f64 modulo: a % b = a - trunc(a / b) * b.

        WASM has no f64.rem instruction, so we decompose using
        f64.trunc (truncation toward zero).  This is the naive truncated
        remainder (not bit-exact C fmod for large a / b), consistent with
        i64.rem_s for integer modulo.  The verifier models the same formula
        (#797), so Tier 1 matches this output exactly.
        """
        tmp_a = self.alloc_local("f64")
        tmp_b = self.alloc_local("f64")
        return [
            *left,
            f"local.set {tmp_a}",
            *right,
            f"local.set {tmp_b}",
            f"local.get {tmp_a}",          # a
            f"local.get {tmp_a}",          # a  (for a / b)
            f"local.get {tmp_b}",          # b  (for a / b)
            "f64.div",                      # a / b
            "f64.trunc",                    # trunc(a / b)
            f"local.get {tmp_b}",          # b  (for * b)
            "f64.mul",                      # trunc(a / b) * b
            "f64.sub",                      # a - trunc(a / b) * b
        ]

    # -----------------------------------------------------------------
    # Unary operators
    # -----------------------------------------------------------------

    def _translate_unary(
        self, expr: ast.UnaryExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate unary operators to WAT."""
        operand = self.translate_expr(expr.operand, env)
        # #657 / #630 [E615]: keep as `return None` — translate_expr returns
        # None reachably for a failed string interpolation (#630); this forward
        # propagates the [E615] drop.  Do NOT convert to assert/raise.
        # See vera/skip.py, "Reachable None via the [E615] channel".
        if operand is None:
            return None  # pragma: no cover

        if expr.op == ast.UnaryOp.NOT:
            return operand + ["i32.eqz"]
        if expr.op == ast.UnaryOp.NEG:
            if self._infer_expr_wasm_type(expr.operand) == "f64":
                return operand + ["f64.neg"]
            return ["i64.const 0"] + operand + ["i64.sub"]
        raise CodegenInvariantError(  # pragma: no cover
            "unary operator dispatch fell through", expr)

    # -----------------------------------------------------------------
    # Control flow
    # -----------------------------------------------------------------

    def _translate_if(
        self, expr: ast.IfExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate if-then-else to WASM if/else."""
        cond = self.translate_expr(expr.condition, env)
        then = self.translate_block(expr.then_branch, env)
        else_ = self.translate_block(expr.else_branch, env)
        if cond is None or then is None or else_ is None:
            return None

        # Determine result type from branches — try then first, fall back
        # to else (handles cases where one branch ends with throw/unreachable)
        result_type = self._infer_block_result_type(expr.then_branch)
        if result_type is None and expr.else_branch is not None:
            result_type = self._infer_block_result_type(expr.else_branch)
        if result_type is None:
            # Unit result — no (result) annotation
            return (
                cond
                + ["if"]
                + ["  " + i for i in then]
                + ["else"]
                + ["  " + i for i in else_]
                + ["end"]
            )

        # #820: a HETEROGENEOUS @Int-join if (one @Nat arm, one genuine @Int
        # arm) widens the @Nat arm into the @Int join.  The whole-if boundary
        # guard cannot fire (it would false-trap the legitimately-negative @Int
        # arm), so guard the @Nat arm PER-ARM here.  `_is_hetero_int_widen_join`
        # is the shared gate: i64 join, NOT wholly @Nat (`_result_is_nat`), AND
        # TARGET @Int (FIX-4 — without the target check this false-trapped a
        # legal @Nat arm of a hetero join in a @Nat-RETURNING context).  The same
        # gate drives the FIX-1 tail-call collector, so the two stay in lockstep.
        if self._is_hetero_int_widen_join(expr):
            if self._result_is_nat(expr.then_branch):
                then = self._emit_int_widen_guard(
                    then, at=expr.then_branch)
            if (expr.else_branch is not None
                    and self._result_is_nat(expr.else_branch)):
                else_ = self._emit_int_widen_guard(
                    else_, at=expr.else_branch)

        # i32_pair → two i32 results (ptr, len)
        if result_type == "i32_pair":
            result_annot = "if (result i32 i32)"
        else:
            result_annot = f"if (result {result_type})"

        return (
            cond
            + [result_annot]
            + ["  " + i for i in then]
            + ["else"]
            + ["  " + i for i in else_]
            + ["end"]
        )

    # -----------------------------------------------------------------
    # String literals
    # -----------------------------------------------------------------

    def _translate_string_lit(self, expr: ast.StringLit) -> list[str]:
        """Translate a string literal to (ptr, len) on the stack."""
        offset, length = self.string_pool.intern(expr.value)
        return [f"i32.const {offset}", f"i32.const {length}"]

    # -----------------------------------------------------------------
    # String interpolation
    # -----------------------------------------------------------------

    def _interp_resolved_type_name(self, name: str | None) -> str | None:
        """Resolve an inferred type NAME to the shape that renders it.

        Interpolation is a representation-level question — "which
        `*_to_string` builtin takes this value?" — so it uses the walker
        every representation-level classifier shares
        (:func:`vera.monomorphize.resolve_type_alias`): refinement layers
        unwrap, alias chains follow, and a name that is neither is
        returned unchanged.  Returns *name* untouched when there is no
        alias environment to resolve against or the chain is cyclic
        (E132 rejects that upstream), so the dispatch falls to its loud
        skip rather than guessing.

        The name arrives RENDERED, so a parameterised spelling
        (``Identity<Int>`` for ``type Identity<T> = T``) does not match
        the alias table and is returned unchanged — deliberately, rather
        than re-parsing a rendered name.  Nothing is lost: a value of a
        generic-alias type has no WASM representation at all, so codegen
        refuses such a program at its ``let`` (measured at this revision
        and at the merge base, with and without an interpolation in the
        body).  Should that gap close, this is the seam to thread the
        type arguments through.
        """
        if name is None:
            return None
        env = getattr(self, "_alias_env", None)
        if env is None:
            return name
        resolved = resolve_type_alias(
            ast.NamedType(name=name, type_args=None),
            env.aliases, env.alias_params,
        )
        if isinstance(resolved, ast.NamedType):
            return resolved.name
        return name

    # Type -> to_string builtin dispatch: the checker's table itself
    # (#1347), not a copy that has to be kept matching it by comment.
    _INTERP_TO_STRING: ClassVar[dict[str, str]] = TO_STRING_BUILTINS

    def _translate_interpolated_string(
        self, expr: ast.InterpolatedString, env: "WasmSlotEnv",
    ) -> list[str] | None:
        """Translate an interpolated string to a chain of string_concat calls.

        Desugars at the WASM level: ``"a\\(x)b"`` becomes
        ``string_concat(string_concat("a", to_string(x)), "b")``.
        Each part is translated to ``(ptr, len)`` on the stack, then
        folded left with ``string_concat``.
        """
        # Collect non-empty parts as AST nodes ready for translation.
        # Continue iterating even after the first inference failure so
        # that every offending segment in a single interpolation surfaces
        # as its own [E615] diagnostic — N reports per N failures, not
        # one report per recompile.  `had_failure` tracks whether any
        # segment hit the silent-amplifier-now-loud path so we still
        # return None at the end (the function is dropped via [E602]).
        parts: list[ast.Expr] = []
        had_failure = False
        for p in expr.parts:
            if isinstance(p, str):
                if p:  # skip empty string fragments
                    parts.append(ast.StringLit(value=p, span=expr.span))
            else:
                # Determine Vera type for auto-conversion, on its
                # RESOLVED form (#1347).  `_infer_vera_type` answers with
                # the type's SPELLING — `Celsius` for a `type Celsius =
                # Float64` slot — and this dispatch used to look that up
                # directly, so every alias and every refinement missed
                # the table and fell into the loud-skip branch below: a
                # check-green program dropped with "Cannot interpolate
                # value of unknown type".  The walker unwraps refinements
                # and follows alias chains to the terminal shape, which
                # is what actually decides how the value renders.
                vera_type = self._interp_resolved_type_name(
                    self._infer_vera_type(p),
                )
                if vera_type == "String":
                    parts.append(p)
                elif vera_type in self._INTERP_TO_STRING:
                    # Wrap with the appropriate to_string call
                    fn_name = self._INTERP_TO_STRING[vera_type]
                    parts.append(ast.FnCall(
                        name=fn_name, args=(p,), span=expr.span,
                    ))
                else:
                    # #630 Tier 2 — record every inference failure and
                    # bail at the end.  Pre-#630 this branch silently
                    # wrapped `p` in `to_string(...)`, which reads its
                    # arg as `i64`.  When `_infer_vera_type(p)` returns
                    # None or a non-recognised name (e.g. an `i32_pair`
                    # String/Array value the canonicaliser couldn't
                    # walk), the `to_string` wrapper produced invalid
                    # WASM — `expected i64, found i32` at validation.
                    # That silent fallthrough was the amplifier that
                    # turned every canonicalisation gap (the ten
                    # triggers of the #602 bug class accumulated
                    # across PRs #627 + #629) into invalid emission
                    # rather than a clean compile-time skip.
                    #
                    # Post-#630: append the failing segment to the
                    # WasmContext failure list so the codegen base's
                    # `_harvest_interp_inference_failures` (called from
                    # `_compile_fn` and `_compile_lifted_closure`) can
                    # emit one [E615] diagnostic per offending segment,
                    # then fall through to the existing [E602] /
                    # closure-drop mechanism — same loud-skip behaviour
                    # that any other unsupported expression triggers,
                    # but now with a specific E-code pointing at the
                    # actual inference gap rather than a generic
                    # "unsupported expressions".  No more silent
                    # miscompilation.
                    self._interp_inference_failures.append(p)
                    had_failure = True
        # #630 [E615] / #657: THIS is the canonical reachable `return None` in
        # codegen.  It is NOT a silent skip — the failing segments were recorded
        # above and are surfaced as [E615] at the _compile_fn boundary.  Every
        # enclosing translator that forwards a translate_expr / translate_block
        # result relies on this None propagating up (see vera/skip.py,
        # "Reachable None via the [E615] channel").  Do NOT convert forwards of
        # it to assert/raise — that would crash instead of dropping via [E615].
        if had_failure:
            return None

        if not parts:  # pragma: no cover
            # All fragments were empty -> empty string
            offset, length = self.string_pool.intern("")
            return [f"i32.const {offset}", f"i32.const {length}"]

        if len(parts) == 1:
            # Single part -- translate directly
            return self.translate_expr(parts[0], env)

        # Left-fold with string_concat: concat(concat(a, b), c) ...
        result = ast.FnCall(
            name="string_concat",
            args=(parts[0], parts[1]),
            span=expr.span,
        )
        for part in parts[2:]:
            result = ast.FnCall(
                name="string_concat",
                args=(result, part),
                span=expr.span,
            )
        return self.translate_expr(result, env)

    # -----------------------------------------------------------------
    # Result references (postconditions)
    # -----------------------------------------------------------------

    def _translate_result_ref(self) -> list[str] | None:
        """Translate @T.result to local.get of the result temp."""
        if self._result_local is not None:
            return [f"local.get {self._result_local}"]
        raise CodegenInvariantError(  # pragma: no cover
            "@T.result reference with no result local bound")

    # -----------------------------------------------------------------
    # Assert and assume
    # -----------------------------------------------------------------

    def _translate_assert(
        self, expr: ast.AssertExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate assert(expr) → trap if false.

        Evaluates the condition; if it's false (i32.eqz), signals
        ``assertion_failed`` with the assertion's own text and traps
        (#1479).  Returns no value (Unit).
        """
        cond = self.translate_expr(expr.expr, env)
        # #657 / #630 [E615]: keep as `return None` — translate_expr returns
        # None reachably for a failed string interpolation (#630); this forward
        # propagates the [E615] drop.  Do NOT convert to assert/raise.
        # See vera/skip.py, "Reachable None via the [E615] channel".
        if cond is None:
            return None  # pragma: no cover
        trap = self._emit_trap(
            "wasm/operators.py:_translate_assert", at=expr,
            message=(
                f"Assertion failed{self._at_line(expr)}: "
                f"assert({ast.format_expr(expr.expr)})"
            ))
        return cond + ["i32.eqz", "if", *(f"  {i}" for i in trap), "end"]

    def _translate_assume(self) -> list[str]:
        """Translate assume(expr) → no-op at runtime.

        The verifier uses assume as an axiom; at runtime it has no
        effect.  Returns empty instructions (Unit).
        """
        return []

    # -----------------------------------------------------------------
    # Quantifiers — forall/exists as runtime loops
    # -----------------------------------------------------------------

    def _translate_forall(
        self, expr: ast.ForallExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate forall(@T, domain, predicate) → loop returning Bool.

        Iterates counter from 0 to domain-1, inlining the predicate
        body with counter as the @T binding.  Short-circuits on the
        first false result.
        """
        return self._translate_quantifier(expr, env, is_forall=True)

    def _translate_exists(
        self, expr: ast.ExistsExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate exists(@T, domain, predicate) → loop returning Bool.

        Iterates counter from 0 to domain-1, inlining the predicate
        body with counter as the @T binding.  Short-circuits on the
        first true result.
        """
        return self._translate_quantifier(expr, env, is_forall=False)

    def _index_refinement_layers(
        self, te: ast.TypeExpr,
    ) -> list[naming.RefinementBinder]:
        """Each refinement a quantifier's index type carries, outermost
        first, following aliases — ``[]`` for a plain ``Int`` or ``Nat``."""
        layers: list[naming.RefinementBinder] = []
        node: ast.TypeExpr | None = te
        while node is not None:
            parts = naming.refinement_binder_parts(node, self._alias_env)
            if parts is None:
                break
            layers.append(parts)
            node = parts.base if parts.base_is_refinement else None
        return layers

    def _translate_quantifier(
        self,
        expr: ast.ForallExpr | ast.ExistsExpr,
        env: WasmSlotEnv,
        *,
        is_forall: bool,
    ) -> list[str] | None:
        """Shared implementation for forall/exists compilation.

        Layout:
          counter (i64) = 0
          limit   (i64) = domain
          result  (i32) = 1 (forall) or 0 (exists)
          block $qbreak_N
            loop $qloop_N
              if counter >= limit → br $qbreak_N
              if the index type's refinement holds of counter:
                push counter as @T binding
                evaluate predicate body → i32
                forall: if false → result=0, br $qbreak_N
                exists: if true  → result=1, br $qbreak_N
              counter++
              br $qloop_N
            end
          end
          local.get result

        The index type's refinement is HONOURED (#1506 review): the
        quantifier ranges over the values below the bound that satisfy it,
        so ``forall`` means ``P(i) ==> body(i)`` for each index and
        ``exists`` means ``P(i) && body(i)`` for some.  It was never read —
        the runtime check of ``forall(@{ @Nat | @Nat.0 < 2 }, 5, ...)``
        tested every index below 5, and an ``exists`` over a refinement
        nothing satisfies still answered the body's value.
        """
        # Evaluate domain
        domain_instrs = self.translate_expr(expr.domain, env)
        # #657 / #630 [E615]: keep as `return None` — translate_expr returns
        # None reachably for a failed string interpolation (#630); this forward
        # propagates the [E615] drop.  Do NOT convert to assert/raise.
        # See vera/skip.py, "Reachable None via the [E615] channel".
        if domain_instrs is None:
            return None  # pragma: no cover

        # Translate predicate body with counter as binding
        pred = expr.predicate
        if len(pred.params) != 1:
            raise CodegenInvariantError(  # pragma: no cover
                "quantifier predicate must have exactly one parameter", expr)
        param_te = pred.params[0]
        if not isinstance(param_te, ast.NamedType):
            raise CodegenInvariantError(  # pragma: no cover
                "quantifier predicate parameter is not a NamedType", expr)
        param_type_name = param_te.name
        counter_local = self.alloc_local("i64")
        limit_local = self.alloc_local("i64")
        result_local = self.alloc_local("i32")
        inner_env = env.push(param_type_name, counter_local)

        body_instrs = self.translate_block(pred.body, inner_env)
        # #657 / #630 [E615]: keep as `return None` — translate_block returns
        # None reachably when the predicate body ends in a failed string
        # interpolation (#630); this forward propagates the [E615] drop.  Do NOT
        # convert to assert/raise.  See vera/skip.py, "Reachable None via [E615]".
        if body_instrs is None:
            return None  # pragma: no cover

        # The index type's refinement, each layer of it: `P(counter)` as an
        # i32, outermost first.
        layer_conds: list[list[str]] = []
        for layer in self._index_refinement_layers(expr.binding_type):
            cond = self.translate_expr(
                layer.predicate, env.push(layer.binder_name, counter_local))
            if cond is None:
                return None  # pragma: no cover — the [E615] channel above
            layer_conds.append(cond)

        # Unique labels
        qid = self._next_quant_id
        self._next_quant_id += 1
        brk = f"$qbreak_{qid}"
        lp = f"$qloop_{qid}"

        init_val = "1" if is_forall else "0"
        instructions: list[str] = []

        # Initialize
        instructions.extend(domain_instrs)
        instructions.append(f"local.set {limit_local}")
        instructions.append("i64.const 0")
        instructions.append(f"local.set {counter_local}")
        instructions.append(f"i32.const {init_val}")
        instructions.append(f"local.set {result_local}")

        # Loop structure
        instructions.append(f"block {brk}")
        instructions.append(f"  loop {lp}")

        # Termination check: counter >= limit → break
        instructions.append(f"    local.get {counter_local}")
        instructions.append(f"    local.get {limit_local}")
        instructions.append("    i64.ge_s")
        instructions.append(f"    br_if {brk}")

        # Evaluate predicate body (counter is in env as @T), and
        # short-circuit: forall on a false predicate → result=0, break;
        # exists on a true one → result=1, break.
        step: list[str] = list(body_instrs)
        if is_forall:
            step += ["i32.eqz", "if", "  i32.const 0",
                     f"  local.set {result_local}", f"  br {brk}", "end"]
        else:
            step += ["if", "  i32.const 1",
                     f"  local.set {result_local}", f"  br {brk}", "end"]
        # An index outside the refinement is not in the range.  Each layer
        # guards the step, wrapped outermost first so the INNERMOST is
        # tested first and each outer layer only where the ones inside it
        # hold: an outer predicate may be defined only there (`12 / @Pos.0`
        # over a `Pos` that excludes 0), which an eager `i32.and` of the
        # layers would evaluate at every index (PR #1508 review).
        for cond in layer_conds:
            step = [*cond, "if", *(f"  {i}" for i in step), "end"]
        for instr in step:
            instructions.append(f"    {instr}")

        # Increment counter
        instructions.append(f"    local.get {counter_local}")
        instructions.append("    i64.const 1")
        instructions.append("    i64.add")
        instructions.append(f"    local.set {counter_local}")
        instructions.append(f"    br {lp}")

        instructions.append("  end")  # loop
        instructions.append("end")    # block

        # Push result
        instructions.append(f"local.get {result_local}")

        return instructions

    # -----------------------------------------------------------------
    # old/new state expressions (postconditions)
    # -----------------------------------------------------------------

    def _translate_old_expr(self, expr: ast.OldExpr) -> list[str] | None:
        """Translate old(State<T>) → local.get of saved pre-execution state."""
        # The snapshot map is keyed by the cell FAMILY (see
        # `_collect_old_types`), so `old(State<Count>)` reads the `Nat`
        # snapshot (#1205) and `old(State<MaybeInt>)` the `Option<Int>` one
        # (#1209) — one derivation, `_state_effect_family`, on both sides.
        local_idx = self.get_old_state_local(
            self._state_effect_family(expr.effect_ref))
        if local_idx is None:
            # Reachable, and pinned: the checker accepts a contract naming a
            # `State<T>` the function's effect row does not declare, so there
            # is no snapshot to read.  E699 says exactly that ("the type
            # checker should have rejected the input"), which is the honest
            # report until it does — tracked as #1298.
            raise CodegenInvariantError(
                "old(State<T>) has no saved pre-execution state local", expr)
        return [f"local.get {local_idx}"]

    def _translate_new_expr(self, expr: ast.NewExpr) -> list[str] | None:
        """Translate new(State<T>) → call state_get to read current value."""
        state_type_arg(expr.effect_ref)  # shape validation; raises otherwise
        # Keyed by the cell FAMILY, exactly as `_translate_old_expr` above
        # keys the snapshot map — one derivation, `_state_effect_family`, on
        # both sides of the same `ensures` clause (#1285).  This used to read
        # the name-keyed `_effect_ops["get"]`, which holds whichever family
        # the ROW registered first: under `effects(<State<Int>, State<Bool>>)`
        # a `new(State<Bool>)` took `state_get_Int`, feeding an i64 into the
        # Bool comparison's `i32.eq` — check-green, verify-green, and dead at
        # load with wasmtime's raw type mismatch.  A bare `get(())` names no
        # family and so is right to read the name-keyed registry; a contract
        # names one and must not.
        family = self._state_effect_family(expr.effect_ref)
        call_target = self._state_getters.get(family)
        if call_target is None:
            # The `old()` twin above, reached the same way and pinned beside
            # it: a contract naming a family the row does not declare has no
            # cell to read.  Pre-#1285 this branch could not fire, because
            # the name-keyed lookup found SOME getter and read the wrong
            # cell — the defect, in its purest form.
            raise CodegenInvariantError(
                f"new(State<{family}>) has no registered state getter", expr)
        return [f"call {call_target}"]

    # -----------------------------------------------------------------
    # @Nat subtraction underflow guard (#520)
    # -----------------------------------------------------------------

    def _is_nat_subtraction(self, expr: ast.BinaryExpr) -> bool:
        """Return True iff *expr* is a `@Nat - @Nat` site that needs guarding.

        Mirrors :py:meth:`ContractVerifier._is_nat_typed` AND
        :py:meth:`ContractVerifier._has_nat_origin` from the verifier
        (vera/verifier.py): the result must be statically @Nat (both
        operands @Nat-typed per checker subtyping rule) AND at least
        one operand must have @Nat *provenance* (slot ref or
        function return), distinguishing real @Nat-flowed
        subtractions from pure-literal idioms like ``0 - 1`` (the
        common "I want -1 as a literal" pattern used in
        ``Err(_) -> 0 - 1`` and similar positions).

        The two conditions must agree exactly with the verifier so
        that programs verified clean at Tier 1 don't pay an unguarded
        underflow risk and so the runtime guard never fires on a site
        the verifier considered exempt.

        Pure-literal underflow into a @Nat binding (e.g.
        ``let @Nat = 0 - 1``) is intentionally *not* caught here —
        that's Path B (#552) territory, which generalises the
        verifier check to every binding-site narrowing.
        """
        # The one rule the verifier reads (PR #1583 review): a literal-only
        # operand by its value, any other by the checker's resolved type
        # first.  Read from the syntax alone, `0 - 3` is two non-negative
        # literals, so `(0 - 3) - @Nat.0` — an `@Int` subtraction the
        # verifier records no `nat_sub` for — was guarded as one, and the
        # guard trapped the -8 of a program `vera verify` passed.
        return narrowing.is_guarded_nat_subtraction(
            expr, lambda e: self._overflow_codegen_type(e) == "Nat",
            self._has_nat_origin_codegen)

    def _is_static_nat_typed(self, expr: ast.Expr) -> bool:
        """Return True iff *expr* has static type @Nat.

        Delegates to :func:`vera.narrowing.is_static_nat_typed` — the rule now
        lives in one place and both this and the verifier's classification read
        it, so they cannot drift (#1205 parity, re-keyed in #1362).  What stays
        here is the ORACLE: codegen infers a call's return type from its own
        tables.
        """
        return narrowing.is_static_nat_typed(
            expr, self._infer_fncall_vera_type_for_narrowing)

    def _infer_fncall_vera_type_for_narrowing(self, call: ast.Expr) -> str | None:
        """Codegen's return-type oracle for the shared narrowing rule.

        A `ModuleCall` is desugared to a `FnCall` before translation, so the
        same lookup answers both once the flattened shape is synthesised.
        """
        if isinstance(call, ast.ModuleCall):
            return self._infer_fncall_vera_type(
                ast.FnCall(name=call.name, args=call.args, span=call.span))
        if isinstance(call, ast.FnCall):
            return self._infer_fncall_vera_type(call)
        return None

    def _result_is_nat(self, expr: ast.Expr) -> bool:
        """Whether *expr*'s VALUE is a genuine @Nat — the #813 widening
        question, answered by THE rule every guard and every obligation reads
        (:func:`vera.narrowing.result_is_nat`, #1503).

        Codegen's guard fires at exactly the sites the verifier obligates only
        if the two ask one rule, so the rule is not written here; this side
        supplies the declaration leaf (:py:meth:`_declared_result_is_nat`) and
        nothing else.  A non-negative literal is not a genuine @Nat (it is
        range-checked against its target, #812) unless it exceeds `i64.MAX`,
        and arithmetic is @Nat only when both operands are.
        """
        return narrowing.result_is_nat(expr, self._declared_result_is_nat)

    def _declared_result_is_nat(self, expr: ast.Expr) -> bool:
        """The declaration leaf of the shared widening rule, codegen's
        reading: whether the value of a form the rule does not decompose — a
        slot, a call, an index into an opaque array, an effect operation —
        is a genuine @Nat (#1503).

        Consults the checker's resolved-type side-table first — the answer
        the verifier's leaf reads, so a verified build matches it
        site-for-site.  A call's @Nat return cannot come from
        `_infer_fncall_vera_type` alone: it maps the i64 WASM return back to
        "Int" (both @Nat and @Int lower to i64) and so NEVER yields "Nat",
        which left every @Nat-returning call result unguarded while the
        verifier obligated it `tier3` (#813 review).

        Caveat (no-side-table fallback): an unverified `transform -> compile`
        has no table, so a user callee's DECLARED @Nat return is recovered
        from `_fn_ret_type_exprs`, mirroring the verifier's
        `env.lookup_function().return_type` path — `_infer_fncall_vera_type`
        would make a genuine @Nat -> @Nat tail call (`count_down(@Nat.0 - 1)`)
        look like a narrowing and break its return_call TCO (#758).
        Over-classifying a call result as @Nat here only ever suppresses a
        (dead) guard on a provably-@Nat value — never a wrong runtime verdict.
        """
        resolved = self._resolved_codegen_type(expr)
        if resolved is not None:
            return resolved == "Nat"
        if not isinstance(expr, (ast.FnCall, ast.ModuleCall)):
            return False
        decl_ret = self._fn_ret_type_exprs.get(expr.name)
        if isinstance(decl_ret, ast.RefinementType):
            decl_ret = decl_ret.base_type
        if (isinstance(decl_ret, ast.NamedType)
                and not decl_ret.type_args
                and self._resolve_base_type_name(decl_ret.name) == "Nat"):
            return True
        call = (
            expr if isinstance(expr, ast.FnCall)
            else ast.FnCall(name=expr.name, args=expr.args, span=expr.span)
        )
        return self._infer_fncall_vera_type(call) == "Nat"

    def _arm_nat_compatible(self, expr: ast.Expr) -> bool:
        """Codegen's reading of :func:`vera.narrowing.arm_nat_compatible` —
        an if/match arm is @Nat-compatible if intrinsically @Nat or a
        non-negative literal (#813 site 2a)."""
        return narrowing.arm_nat_compatible(expr, self._declared_result_is_nat)

    @staticmethod
    def _is_nonneg_int_literal(expr: ast.Expr) -> bool:
        """(A block trailing into) a non-negative int literal — the shared
        rule, :func:`vera.narrowing.is_nonneg_int_literal`."""
        return narrowing.is_nonneg_int_literal(expr)

    def _is_hetero_int_widen_join(self, expr: ast.Expr) -> bool:
        """Codegen mirror of ``ContractVerifier._is_hetero_int_widen_join``
        (#820) — the single source of truth for the heterogeneous @Nat -> @Int
        per-arm widen gate, shared by both emitters (``_translate_if`` /
        ``_translate_match``) and the FIX-1 tail-call collector so collection
        and emission cannot desync.

        True iff *expr* is an ``if`` / ``match`` whose i64 result is a
        HETEROGENEOUS @Int join — at least one genuine @Int-*slot* arm makes the
        join genuinely @Int (``not _result_is_nat``), so the whole-expression
        boundary guard cannot fire without false-trapping that arm — AND whose
        TARGET type is @Int, recovered from the threaded target-type table.  Each
        intrinsically-@Nat arm then widens into that @Int join and is guarded
        PER-ARM.

        The target-@Int requirement mirrors the verifier's
        ``_is_int_type(_target_type_of(expr))`` and is the FIX-4 correction: the
        pre-existing ``result_type == "i64" and not _result_is_nat`` gate was
        TARGET-BLIND, so a hetero i64 join in a @Nat-RETURNING context (where the
        @Int arm narrows into the @Nat return via the #983 nat_bind machinery,
        and the @Nat arm is a LEGAL @Nat) had its @Nat arm falsely wrapped in the
        widen guard — trapping a verify-clean Tier-1 program on a value like
        2^63.  When the target-type table carries no entry for the join (an
        unverified ``transform -> compile``), there is no widen claim to honour,
        so we do NOT guard — matching the verifier, which likewise emits no
        per-arm obligation without the table.  ``_resolve_base_type_name`` makes
        the target check alias-aware, as the sibling widen gates are.
        """
        if isinstance(expr, ast.IfExpr):
            result_type = self._infer_block_result_type(expr.then_branch)
            if result_type is None and expr.else_branch is not None:
                result_type = self._infer_block_result_type(expr.else_branch)
        elif isinstance(expr, ast.MatchExpr):
            result_type = self._infer_match_result_type(expr)
        else:
            return False
        if result_type != "i64" or self._result_is_nat(expr):
            return False
        target = self._target_codegen_type_full(expr)
        if target is None:
            return False
        name = getattr(target, "name", None)
        return name is not None and self._resolve_base_type_name(name) == "Int"

    def _has_nat_origin_codegen(self, expr: ast.Expr) -> bool:
        """Return True iff *expr* derives from a definitely-@Nat source.

        Mirrors :py:meth:`ContractVerifier._has_nat_origin`.  Distinct
        from :py:meth:`_is_static_nat_typed`: that classifies the
        type, this asks whether the value has @Nat *provenance* — a
        parameter, let-binding, or function call carrying the @Nat
        invariant forward, vs. a pure-literal computation.

        Used to scope #520's runtime guard so it doesn't fire on
        pure-literal subtractions (those are #552 territory).
        """
        if isinstance(expr, ast.SlotRef):
            return expr.type_name == "Nat"
        if isinstance(expr, ast.FnCall):
            return self._infer_fncall_vera_type(expr) == "Nat"
        if isinstance(expr, ast.ModuleCall):
            return self._infer_fncall_vera_type(
                ast.FnCall(name=expr.name, args=expr.args, span=expr.span),
            ) == "Nat"
        if isinstance(expr, ast.BinaryExpr):
            return (self._has_nat_origin_codegen(expr.left)
                    or self._has_nat_origin_codegen(expr.right))
        if isinstance(expr, ast.UnaryExpr):
            return self._has_nat_origin_codegen(expr.operand)
        if isinstance(expr, ast.IfExpr):
            if expr.else_branch is None:
                return False
            return (self._has_nat_origin_codegen(expr.then_branch)
                    or self._has_nat_origin_codegen(expr.else_branch))
        if isinstance(expr, ast.Block):
            return self._has_nat_origin_codegen(expr.expr)
        if isinstance(expr, ast.MatchExpr):
            if not expr.arms:
                return False
            return any(
                self._has_nat_origin_codegen(arm.body)
                for arm in expr.arms
            )
        return False

    def _is_guarded_nat_subtraction(self, expr: ast.Expr) -> bool:
        """Whether *expr* is a `@Nat` subtraction this guard checks — so its
        value, when it has one, is never negative."""
        return (isinstance(expr, ast.BinaryExpr)
                and expr.op == ast.BinOp.SUB
                and self._is_nat_subtraction(expr))

    def _runs_unsigned(self, expr: ast.BinaryExpr) -> bool:
        """Whether an addition or a multiplication is compiled at the
        unsigned (`@Nat`) width — the width `_translate_binary` gives its
        overflow guard, read the same way."""
        return (self._overflow_arith_codegen_type(expr) or "Int") == "Nat"

    def _translate_nat_subtraction(
        self, expr: ast.BinaryExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """A `@Nat` subtraction, guarded to trap where the left operand's
        value is below the right's (#520).

        Where both operands can hold only non-negative values their bits are
        their u64s, and the guard compares those (:py:meth:`_emit_nat_sub_guard`).
        Where either can hold a negative value — a literal-only part, which
        the static rule calls `@Nat` (`0 - 3` is two non-negative literals) —
        the bits no longer say which value they are, so each operand's sign
        is computed from how it is made
        (:func:`vera.narrowing.subtraction_operand_sign`) and the guard
        compares the two values:
        where exactly one is negative it traps iff that one is the left, and
        otherwise it compares their u64s (#1503).  A sign that only the arm
        which produced the value knows, or that needs a sub-value the
        operand consumes, is recorded while the operand is evaluated, by
        instructions ``translate_expr`` appends to those nodes — so they are
        arranged before either operand is translated, and withdrawn after.
        """
        signs = tuple(
            narrowing.subtraction_operand_sign(
                operand, self._is_guarded_nat_subtraction, self._runs_unsigned)
            for operand in (expr.left, expr.right)
        )
        if signs == (narrowing.KnownSign(False), narrowing.KnownSign(False)):
            left = self.translate_expr(expr.left, env)
            right = self.translate_expr(expr.right, env)
            if left is None or right is None:
                return None  # pragma: no cover — the [E615] channel
            return self._emit_nat_sub_guard(left, right, at=expr)
        lhs_tmp = self.alloc_local("i64")
        rhs_tmp = self.alloc_local("i64")
        hooks: dict[int, list[str]] = {}
        captures: dict[int, int] = {}
        lhs = [f"local.get {lhs_tmp}"]
        rhs = [f"local.get {rhs_tmp}"]
        left_neg = self._nat_sub_sign_code(
            signs[0], lambda: lhs, hooks, captures)
        right_neg = self._nat_sub_sign_code(
            signs[1], lambda: rhs, hooks, captures)
        below = self._nat_sub_below(
            left_neg, right_neg, lambda: lhs, lambda: rhs)
        if hooks.keys() & self._nat_sub_hooks.keys():
            raise CodegenInvariantError(  # pragma: no cover — a tree
                "a @Nat subtraction's operand node is recorded twice", expr)
        self._nat_sub_hooks.update(hooks)
        try:
            left = self.translate_expr(expr.left, env)
            right = self.translate_expr(expr.right, env)
        finally:
            for key in hooks:
                del self._nat_sub_hooks[key]
        if left is None or right is None:
            return None  # pragma: no cover — the [E615] channel
        return self._emit_nat_sub_guard(
            left, right, at=expr, below=below, operands=(lhs_tmp, rhs_tmp))

    def _nat_sub_sign_code(
        self,
        sign: narrowing.OperandSign,
        value: Callable[[], list[str]],
        hooks: dict[int, list[str]],
        captures: dict[int, int],
    ) -> list[str]:
        """Instructions that push i32 1 iff the value *sign* describes is
        negative, once that value has been computed; *value* pushes it.

        The instructions run at the guard, after both operands; what they
        need from inside an operand — a join's arm, a sub-value an operation
        consumes — is recorded there through *hooks*, keyed by node."""
        if isinstance(sign, narrowing.KnownSign):
            return [f"i32.const {int(sign.negative)}"]
        if isinstance(sign, narrowing.SignBit):
            return [*value(), "i64.const 0", "i64.lt_s"]
        if isinstance(sign, narrowing.ArmSign):
            flag = self.alloc_local("i32")
            for leaf, arm_sign in sign.arms:
                code = self._nat_sub_sign_code(
                    arm_sign, self._nat_sub_capture(leaf, hooks, captures),
                    hooks, captures)
                hooks.setdefault(id(leaf), []).extend(
                    [*code, f"local.set {flag}"])
            return [f"local.get {flag}"]
        if isinstance(sign, narrowing.RemainderSign):
            dividend = self._nat_sub_sign_code(
                sign.dividend,
                self._nat_sub_capture(sign.expr.left, hooks, captures),
                hooks, captures)
            return [*dividend, *value(), "i64.const 0", "i64.ne", "i32.and"]
        left_value = self._nat_sub_capture(sign.expr.left, hooks, captures)
        right_value = self._nat_sub_capture(sign.expr.right, hooks, captures)
        left = self._nat_sub_sign_code(sign.left, left_value, hooks, captures)
        right = self._nat_sub_sign_code(
            sign.right, right_value, hooks, captures)
        if isinstance(sign, narrowing.DifferenceSign):
            return self._nat_sub_below(left, right, left_value, right_value)
        if isinstance(sign, narrowing.QuotientSign):
            return self._quotient_sign_code(
                sign, left, right, value, left_value, right_value)
        code = [*left, *right, "i32.xor"]
        if sign.expr.op == ast.BinOp.MUL:
            code += [*value(), "i64.const 0", "i64.lt_s", "i32.and"]
        return code

    def _quotient_sign_code(
        self,
        sign: narrowing.QuotientSign,
        left: list[str],
        right: list[str],
        value: Callable[[], list[str]],
        left_value: Callable[[], list[str]],
        right_value: Callable[[], list[str]],
    ) -> list[str]:
        """The sign code of a quotient: negative exactly when one operand is
        and it is not zero — where `i64.div_s` computes the quotient.

        It does not where an operand is a `@Nat` above `i64.MAX`, which it
        divides as the negative i64 its bits are (#1504): `(2^63 + 10) / -2`
        comes back as the positive `2^62 - 5`.  There the operand signs say
        nothing about the value computed, so it is read as the u64 it is, the
        comparison the guard makes of two genuine operands.  A division by -1
        is the exception: it negates exactly at the u64 width, so its sign is
        still its operands'.  An operand above `i64.MAX` is one read as not
        negative whose sign bit is set."""
        left_flag = self.alloc_local("i32")
        right_flag = self.alloc_local("i32")

        def above_i64_max(
            flag: int, operand: Callable[[], list[str]],
        ) -> list[str]:
            return [*operand(), "i64.const 0", "i64.lt_s",
                    f"local.get {flag}", "i32.eqz", "i32.and"]

        return [
            *left, f"local.tee {left_flag}",
            *right, f"local.tee {right_flag}",
            "i32.xor",
            *value(), "i64.const 0", "i64.ne", "i32.and",
            *above_i64_max(left_flag, left_value),
            *right_value(), "i64.const -1", "i64.ne", "i32.and",
            *above_i64_max(right_flag, right_value),
            "i32.or",
            "i32.eqz", "i32.and",
        ]

    def _nat_sub_capture(
        self, node: ast.Expr, hooks: dict[int, list[str]],
        captures: dict[int, int],
    ) -> Callable[[], list[str]]:
        """A pusher of *node*'s value, for sign code that runs after *node*
        is evaluated: the first use tees the value into a local as *node*
        produces it, ahead of anything else recorded there."""
        def push() -> list[str]:
            local = captures.get(id(node))
            if local is None:
                local = self.alloc_local("i64")
                captures[id(node)] = local
                hooks.setdefault(id(node), []).insert(0, f"local.tee {local}")
            return [f"local.get {local}"]
        return push

    def _nat_sub_below(
        self,
        left_neg: list[str],
        right_neg: list[str],
        left: Callable[[], list[str]],
        right: Callable[[], list[str]],
    ) -> list[str]:
        """Instructions that push i32 1 iff the left value is below the right,
        given each one's sign: where exactly one is negative, iff that one is
        the left; otherwise by their u64s — two non-negative values are their
        u64s, and two negative i64s order the same way unsigned."""
        u64_below = [*left(), *right(), "i64.lt_u"]
        constant = {"i32.const 0": 0, "i32.const 1": 1}
        if (len(left_neg) == 1 and len(right_neg) == 1
                and left_neg[0] in constant and right_neg[0] in constant):
            if left_neg == right_neg:
                return u64_below
            return list(left_neg)
        left_flag = self.alloc_local("i32")
        right_flag = self.alloc_local("i32")
        return [
            *left_neg, f"local.set {left_flag}",
            *right_neg, f"local.set {right_flag}",
            f"local.get {left_flag}",
            *u64_below,
            f"local.get {left_flag}", f"local.get {right_flag}", "i32.ne",
            "select",
        ]

    def _emit_nat_sub_guard(
        self, left: list[str], right: list[str], *, at: ast.Node | None,
        below: list[str] | None = None,
        operands: tuple[int, int] | None = None,
    ) -> list[str]:
        """Emit a guarded `i64.sub` that traps on underflow.

        Pattern:

            [left] [right]
            local.set $rhs_tmp     ;; pop rhs into temp
            local.tee $lhs_tmp     ;; pop lhs into temp, leave on stack
            local.get $rhs_tmp     ;; push rhs back (stack: [lhs, rhs])
            i64.lt_u               ;; lhs < rhs, as the u64s @Nat is?
            if
              <vera.trap nat_underflow> unreachable
            end
            local.get $lhs_tmp
            local.get $rhs_tmp
            i64.sub

        The trap names itself (#1479): it signals ``nat_underflow`` with a
        message quoting the two operands and the ``requires(lhs >= rhs)``
        that discharges the site's ``nat_sub`` obligation, so a reader is
        handed the clause to add rather than a bare ``unreachable``.  The
        comparison is unsigned, as the ``@Nat`` overflow guards are: a
        ``@Nat`` is a u64 (spec §2.2.1), and a signed compare read one above
        i64.MAX as negative — trapping ``2^63 - 1`` with a message saying its
        right operand was the larger, and passing ``1 - 2^63``.

        An operand that can hold a negative value is compared by *below*
        instead (:py:meth:`_translate_nat_subtraction`), over the locals
        *operands* names, which it reads after both are set (#1503).
        """
        if below is None or operands is None:
            lhs_tmp = self.alloc_local("i64")
            rhs_tmp = self.alloc_local("i64")
            check = [
                f"local.set {rhs_tmp}",
                f"local.tee {lhs_tmp}",
                f"local.get {rhs_tmp}",
                "i64.lt_u",
            ]
        else:
            lhs_tmp, rhs_tmp = operands
            check = [f"local.set {rhs_tmp}", f"local.set {lhs_tmp}", *below]
        trap = self._emit_trap(
            "wasm/operators.py:_emit_nat_sub_guard", at=at,
            message=self._nat_sub_message(at))
        return [
            *left,
            *right,
            *check,
            "if",
            *(f"  {i}" for i in trap),
            "end",
            f"local.get {lhs_tmp}",
            f"local.get {rhs_tmp}",
            "i64.sub",
        ]

    def _note_quotient_overflow(self, expr: ast.BinaryExpr) -> str:
        """The record entry for a signed division's second trap condition,
        ``INT_MIN / -1``, whose quotient leaves the i64 range (#1479); its
        marker goes on the same ``i64.div_s``.  Returns ``""`` for a literal
        divisor whose i64 bits are not -1's — -1 itself, or the `@Nat`
        literal 2^64 - 1, can meet it; any other literal cannot."""
        divisor = expr.right
        minus_one = (1 << 64) - 1
        if (isinstance(divisor, ast.IntLit)
                and divisor.value % (1 << 64) != minus_one):
            return ""
        if (isinstance(divisor, ast.UnaryExpr)
                and divisor.op == ast.UnaryOp.NEG
                and isinstance(divisor.operand, ast.IntLit)
                and divisor.operand.value % (1 << 64) != 1):
            return ""
        return self._record_check(
            "wasm/operators.py:_note_quotient_overflow", expr)

    @staticmethod
    def _at_line(at: ast.Node | None) -> str:
        """`` (line N)`` for a trap message, or nothing for an unspanned
        node — the backtrace names the function, and this names the line."""
        if at is None or at.span is None:
            return ""
        return f" (line {at.span.line})"

    def _nat_sub_message(self, at: ast.Node | None) -> str:
        """The `nat_underflow` message: the two operands, and the clause that
        discharges the subtraction."""
        if isinstance(at, ast.BinaryExpr):
            lhs, rhs = ast.format_expr(at.left), ast.format_expr(at.right)
        else:  # pragma: no cover — every caller passes the subtraction
            lhs, rhs = "lhs", "rhs"
        return (
            f"@Nat subtraction `{lhs} - {rhs}` would be negative"
            f"{self._at_line(at)}: its right operand is larger than its "
            f"left.  Add `requires({lhs} >= {rhs})` to the enclosing "
            "function, or compute in @Int."
        )

    def _emit_nat_bind_guard(
        self, value: list[str], *, at: ast.Node | None,
    ) -> list[str]:
        """Emit a guarded value that traps if it is a negative i64.

        The binding-site analogue of :py:meth:`_emit_nat_sub_guard`
        (#552): a runtime safety net for an @Int -> @Nat narrowing the
        verifier could not discharge statically (Tier 3), or that reaches
        codegen without ``vera verify`` having run.  Emitted at the @Nat
        binding sites — ``let @Nat = <Int>``, tuple destructure, top-level
        match bind, ADT sub-pattern bind, concrete constructor field, and
        call argument (#747).  Pattern:

            [value]
            local.tee $tmp     ;; leave value on stack, copy to temp
            i64.const 0
            i64.lt_s           ;; value < 0?
            if
              <vera.trap nat_guard> unreachable
            end
            local.get $tmp     ;; restore the (now-checked) value

        The trap carries its OWN kind (#754): the guard signals
        ``nat_guard`` through ``vera.trap`` immediately before the
        ``unreachable``, so the runtime reports it with a Fix naming the
        `requires(... >= 0)` that would discharge it rather than the generic
        ``unreachable`` paragraph.  The guard never fires on a value the
        verifier proved non-negative, so a Tier-1-clean program pays only
        dead instructions, never a trap.
        """
        # `_emit_trap` raises the import's flag beside the emission, not at
        # module assembly — a guard emitted without it would reference an
        # undeclared `$vera.trap` (the #808 / #1376 discipline).
        trap = self._emit_trap("wasm/operators.py:_emit_nat_bind_guard", at=at)
        return self._emit_negative_i64_guard(value, trap=trap)

    def _emit_int_widen_guard(
        self, value: list[str], *, at: ast.Node | None,
    ) -> list[str]:
        """Emit a guarded value that traps if a @Nat exceeds i64.MAX (#813).

        The @Nat -> @Int widening dual of :py:meth:`_emit_nat_bind_guard`: a
        runtime safety net for the ``nat_to_int_coerce`` obligation (E530) the
        verifier could not discharge statically (Tier 3), or that reaches codegen
        without ``vera verify`` having run.  A @Nat is stored as an i64; its
        unsigned value exceeds i64.MAX exactly when the sign bit is set — i.e.
        when the i64 reads as negative — so the guard traps on ``value < 0``
        (the same negative-i64 mechanism as the nat-bind guard).  Emitted at the
        @Nat -> @Int coercion sites the verifier obligates (return, call
        argument, let).  It signals ``widen_guard`` through ``vera.trap``
        immediately before the ``unreachable``, so the runtime names the
        ``requires(... <= i64.MAX)`` that discharges it (#1438); the guard
        never fires on a value the verifier proved ``<= i64.MAX``, so a
        Tier-1-clean program pays only dead instructions.
        """
        trap = self._emit_trap(
            "wasm/operators.py:_emit_int_widen_guard", at=at)
        return self._emit_negative_i64_guard(value, trap=trap)

    def _emit_negative_i64_guard(
        self, value: list[str], *, trap: list[str],
    ) -> list[str]:
        """Shared mechanism behind the @Int->@Nat narrowing guard (#552) and
        the @Nat->@Int widening guard (#813): leave *value* on the stack, but
        trap when it reads as a negative i64.  Both callers reduce to this
        same sign-bit check; they stay distinct entry points because they
        are distinct BOUNDARIES with distinct remedies, which is what *trap*
        carries: the caller's own signal from ``_emit_trap``, naming its kind
        (``nat_guard`` or ``widen_guard``) so the runtime reports the
        boundary that failed rather than the instruction the two share.

            [value]
            local.tee $tmp     ;; leave value on stack, copy to temp
            i64.const 0
            i64.lt_s           ;; value < 0?
            if <trap> end
            local.get $tmp     ;; restore the (now-checked) value
        """
        tmp = self.alloc_local("i64")
        return [
            *value,
            f"local.tee {tmp}",
            "i64.const 0",
            "i64.lt_s",
            "if",
            *(f"  {i}" for i in trap),
            "end",
            f"local.get {tmp}",
        ]

    def _narrows_into_nat(self, value: ast.Expr) -> bool:
        """Codegen mirror of ``ContractVerifier._narrows_into_nat`` (#552).

        True iff binding *value* into a @Nat slot needs a runtime
        ``value >= 0`` guard — a genuine @Int narrowing, or a value whose
        tree contains a pure-literal subtraction (``0 - 1``) that
        ``_is_static_nat_typed`` calls @Nat but which can underflow
        negative.  Should agree with the verifier so a Tier-1-clean
        program never *traps*.  (Codegen sees a user function's i64
        return type, not its @Nat Vera type, so it may emit a dead guard
        on ``let @Nat = <user-fn returning @Nat>`` — harmless, since the
        value is provably >= 0 and never trips the trap; recovering @Nat
        user-fn returns is a precision follow-up.)
        """
        if not self._is_static_nat_typed(value):
            return True
        return self._has_underflow_leaf(value)

    def _collect_narrowing_return_leaves(self, body: ast.Expr) -> set[int]:
        """The ``id()`` of every tail-position return leaf that narrows into a
        @Nat return — the codegen mirror of the verifier's
        ``_return_narrows_into_nat`` leaf descent (#758), but collecting leaf
        identities so ``CodeGenerator._compile_fn`` can guard EACH narrowing
        leaf inline instead of wrapping the whole body (#983 review).

        The whole-body ``_emit_nat_bind_guard(body_instrs)`` wrap appended the
        sign check after the entire body, which forced EVERY ``return_call`` to
        revert to ``call`` — losing TCO for a non-narrowing @Nat->@Nat recursive
        tail call (`drain(@Int.0 - 1)`, itself @Nat->@Nat) that then
        stack-exhausted at depth.  Descending to each leaf and guarding only the
        genuine narrowings (`@Int.0`, `0 - x`, an @Int-returning tail call)
        leaves the non-narrowing recursive tail call structurally untouched, so
        its ``return_call`` survives and the chain runs constant-stack.

        A leaf narrows exactly when ``_narrows_into_nat`` says binding it into a
        @Nat slot needs a ``>= 0`` guard AND it is not intrinsically @Nat
        (the shared rule read through
        :data:`vera.narrowing.NARROWING_EXEMPTION_READING` — a genuine
        @Nat->@Nat tail call resolves its callee's @Nat return there and so is
        NOT collected), the per-leaf form of the whole-body ``narrow_guarded``
        gate.  Descends ``Block`` / ``IfExpr`` / ``MatchExpr`` joins exactly as
        the verifier does.
        """
        leaves: set[int] = set()
        self._collect_narrowing_return_leaves_into(body, leaves)
        return leaves

    def _collect_narrowing_return_leaves_into(
        self, expr: ast.Expr, leaves: set[int],
    ) -> None:
        """Recursive worker for :py:meth:`_collect_narrowing_return_leaves`."""
        if isinstance(expr, ast.Block):
            self._collect_narrowing_return_leaves_into(expr.expr, leaves)
            return
        if isinstance(expr, ast.IfExpr):
            if expr.else_branch is None:
                return
            self._collect_narrowing_return_leaves_into(expr.then_branch, leaves)
            self._collect_narrowing_return_leaves_into(expr.else_branch, leaves)
            return
        if isinstance(expr, ast.MatchExpr):
            for arm in expr.arms:
                self._collect_narrowing_return_leaves_into(arm.body, leaves)
            return
        if self._narrows_into_nat(expr) and not narrowing.result_is_nat(
                expr, self._declared_result_is_nat,
                narrowing.NARROWING_EXEMPTION_READING):
            leaves.add(id(expr))

    def _guard_nat_return_leaf(
        self, expr: ast.Expr, instrs: list[str],
    ) -> list[str]:
        """Wrap a tail-position leaf's WAT with the #758 @Int->@Nat narrowing
        guard when *expr* is a designated narrowing return leaf (per-leaf
        emission — #983 review; replaces the whole-body wrap that broke TCO).

        A no-op unless ``id(expr)`` was collected into ``_nat_return_leaf_ids``
        for the function currently being compiled, so only the genuine
        narrowing leaves pay the guard; a non-narrowing @Nat->@Nat recursive
        tail leaf keeps its ``return_call`` untouched.
        """
        if id(expr) in self._nat_return_leaf_ids:
            return self._emit_nat_bind_guard(instrs, at=expr)
        return instrs

    def _collect_hetero_widen_arm_calls(self, body: ast.Expr) -> set[int]:
        """The ``id()`` of every ``FnCall`` / ``ModuleCall`` that sits inside a
        heterogeneous @Nat->@Int per-arm widen guard (#820, FIX-1) — collected
        so ``CodeGenerator._compile_fn`` can subtract them from ``tail_sites``,
        forcing those calls to lower to a plain ``call`` instead of
        ``return_call``.

        The per-arm widen guard (``_emit_int_widen_guard``) is appended AFTER the
        arm body's WAT, so a ``return_call`` inside that arm would return before
        the guard runs — the guard would be DEAD and a @Nat above i64.MAX would
        silently reinterpret to a negative @Int (the same hazard the #983
        narrowing-leaf collector defends against at the return position).  This
        collector descends ``Block`` trailing exprs / ``IfExpr`` branches /
        ``MatchExpr`` arms and, at each join for which
        :py:meth:`_is_hetero_int_widen_join` holds — THE EXACT gate both emitters
        use, so collection and emission stay in lockstep — collects EVERY call
        under each arm that ``_result_is_nat`` marks (i.e. the arms that ARE
        widen-guarded).  Over-collection is safe: subtraction only affects
        ``tail_sites`` members, and any call inside a guarded arm must not be a
        ``return_call`` (the guard is appended after the arm).  Non-@Nat arms are
        recursed into, so a nested join is still covered.
        """
        ids: set[int] = set()
        self._collect_hetero_widen_arm_calls_into(body, ids)
        return ids

    def _collect_hetero_widen_arm_calls_into(
        self, expr: ast.Expr, ids: set[int],
    ) -> None:
        """Recursive worker for :py:meth:`_collect_hetero_widen_arm_calls`."""
        if isinstance(expr, ast.Block):
            self._collect_hetero_widen_arm_calls_into(expr.expr, ids)
            return
        if isinstance(expr, ast.IfExpr):
            hetero = self._is_hetero_int_widen_join(expr)
            branches = [expr.then_branch]
            if expr.else_branch is not None:
                branches.append(expr.else_branch)
            for branch in branches:
                if hetero and self._result_is_nat(branch):
                    self._collect_all_call_ids(branch, ids)
                else:
                    self._collect_hetero_widen_arm_calls_into(branch, ids)
            return
        if isinstance(expr, ast.MatchExpr):
            hetero = self._is_hetero_int_widen_join(expr)
            for arm in expr.arms:
                if hetero and self._result_is_nat(arm.body):
                    self._collect_all_call_ids(arm.body, ids)
                else:
                    self._collect_hetero_widen_arm_calls_into(arm.body, ids)
            return
        # A leaf (or a non-tail-transparent construct): nothing to descend.

    @staticmethod
    def _collect_all_call_ids(expr: ast.Expr, ids: set[int]) -> None:
        """Add ``id()`` of every ``FnCall`` / ``ModuleCall`` anywhere under
        *expr* (a widen-guarded arm) — the whole arm body's WAT is wrapped, so
        any call in it (not only its tail leaf) must not be a ``return_call``.
        Generic dataclass-field walk (via :func:`walk_nodes`) so new AST call
        shapes are covered structurally."""
        from vera.obligations.cache import walk_nodes
        for node in walk_nodes(expr):
            if isinstance(node, (ast.FnCall, ast.ModuleCall)):
                ids.add(id(node))

    def _has_underflow_leaf(self, value: ast.Expr) -> bool:
        """Codegen mirror of the shared underflow-leaf rule (#552).

        Delegates to :func:`vera.narrowing.has_underflow_leaf`; the @Nat-origin
        oracle stays here because it reads codegen's own tables.
        """
        return narrowing.has_underflow_leaf(
            value, self._has_nat_origin_codegen)

    # -----------------------------------------------------------------
    # @Int / @Nat integer-overflow runtime guard (#798)
    # -----------------------------------------------------------------

    # WASM literal forms for the two's-complement i64 bounds.  ``i64.const``
    # accepts the value ``-9223372036854775808`` directly (the lexer reads a
    # negative literal, not ``-(9223372036854775808)`` whose magnitude is out
    # of the signed range), so emitting ``str(_I64_MIN_CODEGEN)`` is correct.
    _I64_MIN_CODEGEN = -(2**63)

    def _overflow_codegen_type(self, expr: ast.Expr) -> str | None:
        """Return ``"Int"`` / ``"Nat"`` if *expr* (the whole arithmetic
        expression) is a machine integer subject to the #798 overflow guard,
        else ``None``.

        This is the codegen mirror of
        :py:meth:`ContractVerifier._overflow_int_type`, classifying on the
        binary expression's resolved type.  Classifying on the expression (not
        the left operand) handles a literal correctly: a non-negative literal
        carries its own narrow ``@Nat`` type, so ``5 + @Int.0`` is an ``@Int``
        (i64) add even though ``5`` is ``@Nat`` — reading the operand's type
        would mis-range it to u64.

        The verifier classifies on the *checker's resolved type*
        (``_resolved_type_of``).  Codegen does the same FIRST — consulting the
        threaded ``_expr_semantic_types`` side-table — so a bare-literal
        operand whose resolved type is context-dependent (``5 + @Int.0`` is
        Int, ``5 + @Nat.0`` is Nat) is classified identically to the verifier.
        Without this, the AST-only fallback would call any non-negative
        ``IntLit`` ``@Nat`` (the ``_is_static_nat_typed`` rule), mis-ranging a
        literal-left @Int site to u64 and silently dropping an @Int overflow at
        ``[I64_MAX+1, U64_MAX]`` — a verifier/codegen desync (#798 RISK 6).

        The AST-only fallback (``_is_static_nat_typed`` / ``_is_static_int_typed``)
        runs only when the side-table is absent or has no entry for this span
        — e.g. a ``transform -> compile`` caller that skipped typecheck.  It is
        sound for slot-/call-typed operands; the literal ambiguity it cannot
        resolve is the documented precision gap such callers accept.
        """
        resolved = self._resolved_codegen_type(expr)
        if resolved is not None:
            return resolved
        if self._is_static_nat_typed(expr):
            return "Nat"
        if self._is_static_int_typed(expr):
            return "Int"
        return None

    def _overflow_arith_codegen_type(self, expr: ast.BinaryExpr) -> str | None:
        """The codegen mirror of
        :py:meth:`ContractVerifier._overflow_arith_type` — the operation's
        signed/unsigned width = the operands' common (coerced) type (``Int`` if
        either operand is ``@Int``, else ``@Nat``), NOT the narrowed result
        type.  Keeps the runtime guard in lockstep with the verifier's
        obligation at every ``+``/``-``/``*`` site (#798)."""
        # #1503: two literal-only operands take their width from their
        # values, the rule the verifier's width reads first too.
        return narrowing.operation_width(expr, self._overflow_codegen_type)

    def _checker_resolved_type(self, expr: ast.Expr) -> object | None:
        """*expr*'s checker-resolved type from the threaded side-table, raw.

        The same lookup :py:meth:`_resolved_codegen_type` performs, without
        the Int/Nat narrowing of the answer — for a consumer whose rule lives
        in :mod:`vera.narrowing` and is shared with the verifier, which reads
        the identical table through ``_resolved_type_of``.  ``None`` when the
        table was not threaded or carries no entry for this span, which is a
        distinct answer from any type and must not be collapsed into one.
        """
        table = self._expr_semantic_types
        if table is None:
            return None
        key = ast.span_key(expr)
        if key is None:
            return None
        return table.get(key)

    def _resolved_codegen_type(self, expr: ast.Expr) -> str | None:
        """Look up *expr*'s checker-resolved type as ``"Int"`` / ``"Nat"``,
        else ``None`` (no table, no entry, or a non-Int/Nat type).

        Mirrors :py:meth:`ContractVerifier._overflow_int_type` over
        ``_resolved_type_of``: it dispatches on the resolved type's base so a
        ``@Nat`` reached through a refinement/alias still classifies as Nat.
        """
        table = self._expr_semantic_types
        if table is None:
            return None
        key = ast.span_key(expr)
        if key is None:
            return None
        ty = table.get(key)
        if ty is None:
            return None
        # Avoid importing the type module at call time on every arithmetic
        # site: dispatch on the resolved type's *base name*.  ``PrimitiveType``
        # has a ``name``; ``RefinedType`` has a ``base`` carrying it.
        base = getattr(ty, "base", ty)
        name = getattr(base, "name", None)
        if name == "Nat":
            return "Nat"
        if name == "Int":
            return "Int"
        return None

    def _target_codegen_type_full(self, expr: ast.Expr) -> object | None:
        """The checker-recorded *target* type of *expr* (the ``expected`` it was
        checked against), unwrapping any refinement to its base — the codegen
        dual of ``ContractVerifier._target_type_of`` (#820).

        Returns the raw ``Type`` so callers can inspect an ``AdtType``'s
        ``type_args`` (a ``Tuple<Int, Int>`` component target, an ``Array<Int>``
        element target).  ``None`` when the target-type table was not threaded
        (an unverified ``transform -> compile``) or the span carries no target,
        so those component sites stay E531-disclosed rather than falsely guarded.
        """
        table = self._expr_target_types
        if table is None:
            return None
        key = ast.span_key(expr)
        if key is None:
            return None
        ty = table.get(key)
        if ty is None:
            return None
        return getattr(ty, "base", ty)

    def _target_codegen_type_refined(self, expr: ast.Expr) -> object | None:
        """The checker-recorded target of *expr* WITHOUT the refinement
        unwrap :py:meth:`_target_codegen_type_full` performs (#1426).

        The unwrap exists because every caller before #1426 asked a
        base-shaped question — "is this component a `@Nat`?", "an `@Int`?" —
        for which the refinement is noise.  A §2.6.5 guard asks the opposite
        question: the predicate IS the answer, and the base alone cannot
        reconstruct it.  So this reads the same table and hands back what is
        in it.
        """
        table = self._expr_target_types
        if table is None:
            return None
        key = ast.span_key(expr)
        if key is None:
            return None
        return table.get(key)

    @staticmethod
    def refined_type_expr(resolved_ty: object | None) -> ast.TypeExpr | None:
        """A ``TypeExpr`` the §2.6.5 guard lowering can consume, minted from
        a checker-side ``RefinedType`` — or ``None`` when there is no
        refinement to guard (#1426).

        Construction positions know their component's type only as the
        checker's SEMANTIC type: a constructor layout records a field's name
        with the predicate already discarded, a `Tuple` carrier has no
        per-field metadata at all, and an array literal carries a name
        string.  The guard emitter, by contrast, is written against the
        SYNTAX — it chases a `TypeExpr`'s alias chain to a
        `ast.RefinementType`.  The two meet here.

        There is no reverse map from a semantic refinement to the alias that
        declared it, and there could not be a well-defined one: two aliases
        may resolve to structurally identical types.  What makes the
        synthesis exact anyway is that `types.RefinedType` keeps the
        predicate's own AST node, so nothing is reconstructed — the minted
        node carries the same predicate the checker recorded, over a
        `NamedType` naming the RESOLVED base.  Resolving the base is what
        makes the binder agree: `refinement_binder_parts` names the binder
        from the base, the predicate references the base it was written
        over, and a resolved base cannot disagree with itself the way a
        written alias can.

        ``None`` for a non-refinement, for a refinement over a base with no
        nameable head (a function type, a bare type variable), and for a
        refinement OVER a refinement — the last because
        `_emit_bind_refine_guard` refuses that base anyway, and minting a
        node it will only reject reads as a guard that exists.
        """
        if resolved_ty is None or type(resolved_ty).__name__ != "RefinedType":
            return None
        base = getattr(resolved_ty, "base", None)
        predicate = getattr(resolved_ty, "predicate", None)
        if base is None or predicate is None:
            return None
        if type(base).__name__ == "RefinedType":
            return None
        base_name = getattr(base, "name", None)
        if not isinstance(base_name, str):
            return None
        return ast.RefinementType(
            base_type=ast.NamedType(name=base_name, type_args=None),
            predicate=predicate,
        )

    @staticmethod
    def _adt_arg_type(target: object | None, index: int) -> object | None:
        """*target*'s ``index``-th type argument, refinement INTACT (#1426).

        The sibling predicates beside this one answer base-shaped questions
        and unwrap; a §2.6.5 guard needs the refinement itself, so this hands
        back the argument as recorded.  ``None`` whenever the target is not
        an ADT with that many arguments — a `Tuple` carrier with no threaded
        target, an unverified `transform -> compile` — which leaves the
        component where it was rather than guessing at a predicate.
        """
        args = getattr(target, "type_args", None)
        if not isinstance(args, tuple) or index >= len(args):
            return None
        return args[index]

    @staticmethod
    def _adt_arg_is_int(target: object | None, index: int) -> bool:
        """True iff *target* is an ``AdtType`` whose ``index``-th type argument
        resolves (through a refinement) to ``@Int`` — used to decide the
        @Nat -> @Int widening guard at a tuple component / array element from
        the per-component *target* type recovered by ``_target_codegen_type_full``
        (#820).  Deliberately narrow (concrete ``Int`` only): a generic ``T`` or
        a ``@Nat`` slot is not ``Int`` and must not be guarded here."""
        args = getattr(target, "type_args", None)
        if not args or index >= len(args):
            return False
        arg = args[index]
        base = getattr(arg, "base", arg)
        return getattr(base, "name", None) == "Int"

    @staticmethod
    def _adt_arg_is_nat(target: object | None, index: int) -> bool:
        """The narrowing twin of :py:meth:`_adt_arg_is_int` (#1416).

        The widening direction at a tuple component has read the component's
        target type from the checker's threaded table since #820; the
        narrowing direction never did, so `Tuple(@Int.0, 2)` into a
        `Tuple<Nat, Int>` stored the `@Int` unchecked while its `@Nat` twin
        one field over was guarded.  Same table, same index, opposite base —
        written as its own method rather than a parameter on one, because
        each is read at a different arm of the construction site's
        narrowing/widening chain and a shared one would need the arm to pass
        the answer it is asking for.
        """
        args = getattr(target, "type_args", None)
        if not args or index >= len(args):
            return False
        arg = args[index]
        base = getattr(arg, "base", arg)
        return getattr(base, "name", None) == "Nat"

    def _is_static_int_typed(self, expr: ast.Expr) -> bool:
        """Return True iff *expr* has static type @Int by AST shape alone.

        AST-only fallback companion to :py:meth:`_is_static_nat_typed`, used
        only when the resolved-type table is unavailable.  Called *after* the
        @Nat check in :py:meth:`_overflow_codegen_type`, so a non-negative
        ``IntLit`` (which ``_is_static_nat_typed`` already claims as @Nat) does
        not reach here — only a negative ``IntLit``, an @Int slot, an @Int
        function return, or an arithmetic tree of @Int operands.  Conservative
        False elsewhere (a @Byte / @Float / @Bool / String operand is not @Int
        and must not be guarded).
        """
        if isinstance(expr, ast.SlotRef):
            return expr.type_name == "Int"
        if isinstance(expr, ast.IntLit):
            return True
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in (
                ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
                ast.BinOp.DIV, ast.BinOp.MOD,
            ):
                return (self._operand_is_int_or_nat(expr.left)
                        and self._operand_is_int_or_nat(expr.right))
            return False
        if isinstance(expr, ast.IfExpr):
            if expr.else_branch is None:
                return False
            return (self._is_static_int_typed(expr.then_branch)
                    and self._is_static_int_typed(expr.else_branch))
        if isinstance(expr, ast.Block):
            return self._is_static_int_typed(expr.expr)
        if isinstance(expr, ast.MatchExpr):
            if not expr.arms:
                return False
            return all(
                self._is_static_int_typed(arm.body) for arm in expr.arms
            )
        if isinstance(expr, ast.FnCall):
            return self._infer_fncall_vera_type(expr) == "Int"
        if isinstance(expr, ast.ModuleCall):
            return self._infer_fncall_vera_type(
                ast.FnCall(name=expr.name, args=expr.args, span=expr.span),
            ) == "Int"
        return False

    def _operand_is_int_or_nat(self, expr: ast.Expr) -> bool:
        """True iff *expr* is statically @Int or @Nat (AST-only).

        An arithmetic node is @Int when both operands are integral (Int or
        Nat) but at least one is @Int — the Nat<:Int subtyping rule.  Used by
        :py:meth:`_is_static_int_typed` so ``@Int.0 + 3`` (an @Int slot plus a
        non-negative @Nat-by-shape literal) still classifies @Int.
        """
        return (self._is_static_nat_typed(expr)
                or self._is_static_int_typed(expr))

    def _emit_overflow_guard(
        self,
        left: list[str],
        right: list[str],
        op: ast.BinOp,
        ovf: str,
        *,
        at: ast.Node | None,
    ) -> list[str]:
        """Dispatch to the per-(op, type) guarded arithmetic sequence (#798).

        Each sequence computes the wrapping result, checks whether the true
        (unbounded) result left the i64 (@Int) / u64 (@Nat) range, and on
        overflow signals ``overflow`` through ``vera.trap`` then traps, so
        the runtime reports the overflow kind and its Fix paragraph (#808)
        rather than the generic ``unreachable``; otherwise it leaves the
        wrapping result on the stack.  @Nat SUB never reaches here (excluded
        by the caller; it is ``nat_sub`` underflow).

        The trap is emitted ONCE, here, and handed to the sequence, which
        splices it at its single trap site — one check, one signal, one
        entry in the per-module record (#1479).
        """
        trap = self._emit_trap("wasm/operators.py:_emit_overflow_guard", at=at)
        if ovf == "Nat":
            if op == ast.BinOp.ADD:
                return self._emit_nat_add_guard(left, right, trap)
            # MUL (SUB is excluded by the caller).
            return self._emit_nat_mul_guard(left, right, trap)
        # @Int.
        if op == ast.BinOp.ADD:
            return self._emit_int_add_guard(left, right, trap)
        if op == ast.BinOp.SUB:
            return self._emit_int_sub_guard(left, right, trap)
        return self._emit_int_mul_guard(left, right, trap)

    def _emit_int_add_guard(
        self, left: list[str], right: list[str], trap: list[str],
    ) -> list[str]:
        """@Int ADD, signed i64.  Overflow iff ``((a^r) & (b^r)) < 0`` —
        the Hacker's-Delight 2-12 test: ``a+b`` overflows iff ``a`` and ``b``
        share a sign but the wrapped result ``r`` has the opposite sign.
        Leaves ``r`` on the stack."""
        a_tmp = self.alloc_local("i64")
        b_tmp = self.alloc_local("i64")
        r_tmp = self.alloc_local("i64")
        return [
            *left,
            f"local.set {a_tmp}",
            *right,
            f"local.set {b_tmp}",
            f"local.get {a_tmp}",
            f"local.get {b_tmp}",
            "i64.add",
            f"local.tee {r_tmp}",          # stack: [r]
            # (a ^ r):
            f"local.get {a_tmp}",
            f"local.get {r_tmp}",
            "i64.xor",                       # stack: [r, (a^r)]
            # (b ^ r):
            f"local.get {b_tmp}",
            f"local.get {r_tmp}",
            "i64.xor",                       # stack: [r, (a^r), (b^r)]
            "i64.and",                       # stack: [r, (a^r)&(b^r)]
            "i64.const 0",
            "i64.lt_s",                      # stack: [r, cond]
            "if",
            *(f"  {i}" for i in trap),
            "end",                           # stack: [r]
        ]

    def _emit_int_sub_guard(
        self, left: list[str], right: list[str], trap: list[str],
    ) -> list[str]:
        """@Int SUB, signed i64, ``a - b`` (left=minuend).  Overflow iff
        ``((a^b) & (a^r)) < 0``: ``a-b`` overflows iff ``a`` and ``b`` differ
        in sign and the result ``r`` differs in sign from ``a``.  Operand
        order is load-bearing (asymmetric test).  Leaves ``r`` on the stack."""
        a_tmp = self.alloc_local("i64")
        b_tmp = self.alloc_local("i64")
        r_tmp = self.alloc_local("i64")
        return [
            *left,
            f"local.set {a_tmp}",
            *right,
            f"local.set {b_tmp}",
            f"local.get {a_tmp}",
            f"local.get {b_tmp}",
            "i64.sub",
            f"local.tee {r_tmp}",          # stack: [r]
            # (a ^ b):
            f"local.get {a_tmp}",
            f"local.get {b_tmp}",
            "i64.xor",                       # stack: [r, (a^b)]
            # (a ^ r):
            f"local.get {a_tmp}",
            f"local.get {r_tmp}",
            "i64.xor",                       # stack: [r, (a^b), (a^r)]
            "i64.and",                       # stack: [r, (a^b)&(a^r)]
            "i64.const 0",
            "i64.lt_s",                      # stack: [r, cond]
            "if",
            *(f"  {i}" for i in trap),
            "end",                           # stack: [r]
        ]

    def _emit_int_mul_guard(
        self, left: list[str], right: list[str], trap: list[str],
    ) -> list[str]:
        """@Int MUL, signed i64 — the dangerous one.  Division round-trip with
        the ``INT_MIN * -1`` special case.

        ``overflow ⟺ a != 0 && ((a == -1 && b == INT_MIN) || (a != -1 && r/a != b))``

        The ``a == 0`` branch avoids ``r/0``; the ``a == -1`` pre-check avoids
        the native ``i64.div_s`` trap on ``INT_MIN / -1`` (testing ``b ==
        INT_MIN`` instead).  The two overflow conditions are folded into ONE
        i32 flag by value-producing ``if`` blocks, and the flag gates the
        single trap site — so the check signals once, whichever condition
        fired.  ``local.set r_tmp`` clears the operand stack before the
        nested blocks, and ``r`` is pushed at the end.  Leaves ``r`` on the
        stack."""
        a_tmp = self.alloc_local("i64")
        b_tmp = self.alloc_local("i64")
        r_tmp = self.alloc_local("i64")
        return [
            *left,
            f"local.set {a_tmp}",
            *right,
            f"local.set {b_tmp}",
            f"local.get {a_tmp}",
            f"local.get {b_tmp}",
            "i64.mul",
            f"local.set {r_tmp}",          # stack empty
            f"local.get {a_tmp}",
            "i64.eqz",
            "if (result i32)",               # a == 0 → safe
            "  i32.const 0",
            "else",
            f"  local.get {a_tmp}",
            "  i64.const -1",
            "  i64.eq",
            "  if (result i32)",             # a == -1: overflow iff b == INT_MIN
            f"    local.get {b_tmp}",
            f"    i64.const {self._I64_MIN_CODEGEN}",
            "    i64.eq",
            "  else",                        # a != 0 && a != -1 → safe to divide
            f"    local.get {r_tmp}",
            f"    local.get {a_tmp}",
            "    i64.div_s",
            f"    local.get {b_tmp}",
            "    i64.ne",                    # r/a != b → overflow
            "  end",
            "end",
            "if",                            # the one trap site
            *(f"  {i}" for i in trap),
            "end",
            f"local.get {r_tmp}",          # stack: [r]
        ]

    def _emit_nat_add_guard(
        self, left: list[str], right: list[str], trap: list[str],
    ) -> list[str]:
        """@Nat ADD, unsigned u64.  Overflow iff ``r <u a`` — an unsigned sum
        wraps iff the carry-out makes the result smaller than an addend.
        Leaves ``r`` on the stack.

        The condition is built ON TOP of the stashed ``r`` (via fresh
        ``local.get``s), not by consuming it: ``local.tee`` leaves exactly one
        copy on the stack, so the comparison must re-fetch its operands from
        the locals to keep ``r`` live at the bottom as the function result."""
        a_tmp = self.alloc_local("i64")
        r_tmp = self.alloc_local("i64")
        return [
            *left,
            f"local.set {a_tmp}",
            f"local.get {a_tmp}",
            *right,
            "i64.add",
            f"local.tee {r_tmp}",          # stack: [r]
            f"local.get {r_tmp}",
            f"local.get {a_tmp}",
            "i64.lt_u",                      # r <u a ?  stack: [r, cond]
            "if",
            *(f"  {i}" for i in trap),
            "end",                           # stack: [r]
        ]

    def _emit_nat_mul_guard(
        self, left: list[str], right: list[str], trap: list[str],
    ) -> list[str]:
        """@Nat MUL, unsigned u64.  Overflow iff ``a != 0 && r/u a != b``.
        No ``-1`` / INT_MIN hazard (unsigned div only traps on divide-by-zero,
        excluded by the ``a == 0`` branch).  Leaves ``r`` on the stack."""
        a_tmp = self.alloc_local("i64")
        b_tmp = self.alloc_local("i64")
        r_tmp = self.alloc_local("i64")
        return [
            *left,
            f"local.set {a_tmp}",
            *right,
            f"local.set {b_tmp}",
            f"local.get {a_tmp}",
            f"local.get {b_tmp}",
            "i64.mul",
            f"local.set {r_tmp}",          # stack empty
            f"local.get {a_tmp}",
            "i64.eqz",
            "if",                            # a == 0 → safe
            "else",
            f"  local.get {r_tmp}",
            f"  local.get {a_tmp}",
            "  i64.div_u",
            f"  local.get {b_tmp}",
            "  i64.ne",
            "  if",                          # r/u a != b → overflow
            *(f"    {i}" for i in trap),
            "  end",
            "end",
            f"local.get {r_tmp}",          # stack: [r]
        ]
