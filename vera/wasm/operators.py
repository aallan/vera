"""Operator and simple expression translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.skip import AdtEqNotDerivableError, CodegenInvariantError
from vera.slots import slot_ref_name, type_expr_slot_name
from vera.wasm.helpers import WasmSlotEnv


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
        # Shared recursive builder (#914 finding 2) — nested composite type
        # args are FULLY qualified, matching the env-key side so the lookup
        # cannot desync.
        type_name = slot_ref_name(ref)
        if type_name is None:
            raise CodegenInvariantError(  # pragma: no cover
                "slot reference type argument is not a NamedType", ref)
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

    def _translate_binary(
        self, expr: ast.BinaryExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate binary operators to WAT."""
        # Pipe: a |> f(x, y) → f(a, x, y)
        if expr.op == ast.BinOp.PIPE:
            if isinstance(expr.right, ast.FnCall):
                desugared = ast.FnCall(
                    name=expr.right.name,
                    args=(expr.left,) + expr.right.args,
                    span=expr.span,
                )
                return self._translate_call(desugared, env)
            # C7e: a |> Module.f(x) → f(a, x)
            if isinstance(expr.right, ast.ModuleCall):
                desugared = ast.FnCall(
                    name=expr.right.name,
                    args=(expr.left,) + expr.right.args,
                    span=expr.span,
                )
                return self._translate_call(desugared, env)
            raise CodegenInvariantError(  # pragma: no cover
                "pipe RHS is neither FnCall nor ModuleCall", expr)

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
            # @Nat subtraction underflow guard (#520) — mirrors the
            # static obligation emitted in vera/verifier.py.  When the
            # result is statically @Nat and at least one operand has
            # @Nat origin, emit a runtime check that traps on
            # underflow.  Programs that ran `vera verify` first will
            # have caught the violation statically; this guard is the
            # safety net for `vera compile` / `vera run` paths that
            # skipped verification.
            if op == ast.BinOp.SUB and self._is_nat_subtraction(expr):
                return self._emit_nat_sub_guard(left, right)
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
            ovf = self._overflow_arith_codegen_type(expr)
            if (op in (ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL)
                    and ovf is not None
                    and not (op == ast.BinOp.SUB and ovf == "Nat")):
                return self._emit_overflow_guard(left, right, op, ovf)
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
                lv_base = lv.split("<", 1)[0] if lv is not None else None
                if (op in (ast.BinOp.EQ, ast.BinOp.NEQ)
                        and lv is not None
                        and lv_base not in ("Bool", "Byte")
                        and lv_base in self._adt_type_names
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
    _ARITH_OPS_I32_BYTE: dict[ast.BinOp, str] = {
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
        """
        base = arg.split("<", 1)[0].strip()
        return (
            base not in self._CONCRETE_NON_ADT_BASES
            and base not in self._adt_type_names
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
        if base in self._adt_type_names:
            if len(args) != self._adt_tp_counts.get(base, 0):
                return False  # under-parameterized: an argument was erased
            return all(self._eq_type_name_fully_concrete(a) for a in args)
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
        """
        name = self._parameterize_ctor_operand(operand, bare)
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
        if base not in self._adt_type_names:
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

        adt_ctors = sorted(
            (
                (ctor_name, self._ctor_layouts[ctor_name])
                for ctor_name, parent in self._ctor_to_adt.items()
                if parent == base and ctor_name in self._ctor_layouts
            ),
            key=lambda x: x[1].tag,
        )
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
                first = True
                for (offset, _wt), ftype in zip(concrete, field_type_names):
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
        """
        if tp_idx is not None and field_index < len(tp_idx):
            pos = tp_idx[field_index]
            if pos is not None and pos < len(type_args):
                return type_args[pos]
        from vera.monomorphize import substitute_type_param_names

        return substitute_type_param_names(raw, tp_mapping)

    def _concrete_field_layout(
        self, field_type_names: list[str],
    ) -> list[tuple[int, str]]:
        """Recompute (offset, wasm_type) per field from concrete Vera types.

        Mirrors the construction site (``_translate_constructor_call``): tag at
        offset 0 (4 bytes), then each field aligned to its natural alignment.
        """
        sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8}
        aligns = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4}
        offset = 4
        out: list[tuple[int, str]] = []
        for ftype in field_type_names:
            wt = self._eq_field_wasm_type(ftype)
            align = aligns.get(wt, 8)
            offset = (offset + align - 1) & ~(align - 1)
            out.append((offset, wt))
            offset += sizes.get(wt, 8)
        return out

    @staticmethod
    def _eq_field_wasm_type(ftype: str) -> str:
        """WASM rep of a concrete field type for structural-eq layout."""
        base = ftype.split("<", 1)[0]
        if base in ("Int", "Nat"):
            return "i64"
        if base == "Float64":
            return "f64"
        if base in ("Bool", "Byte", "Unit"):
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
        if base in self._adt_type_names:
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
                then = self._emit_int_widen_guard(then)
            if (expr.else_branch is not None
                    and self._result_is_nat(expr.else_branch)):
                else_ = self._emit_int_widen_guard(else_)

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

    # Type -> to_string builtin dispatch (must match checker's map)
    _INTERP_TO_STRING: dict[str, str] = {
        "Int": "to_string",
        "Nat": "nat_to_string",
        "Bool": "bool_to_string",
        "Byte": "byte_to_string",
        "Float64": "float_to_string",
    }

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
                # Determine Vera type for auto-conversion
                vera_type = self._infer_vera_type(p)
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

        Evaluates the condition; if it's false (i32.eqz), executes
        unreachable (WASM trap).  Returns no value (Unit).
        """
        cond = self.translate_expr(expr.expr, env)
        # #657 / #630 [E615]: keep as `return None` — translate_expr returns
        # None reachably for a failed string interpolation (#630); this forward
        # propagates the [E615] drop.  Do NOT convert to assert/raise.
        # See vera/skip.py, "Reachable None via the [E615] channel".
        if cond is None:
            return None  # pragma: no cover
        return cond + ["i32.eqz", "if", "unreachable", "end"]

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
              push counter as @T binding
              evaluate predicate body → i32
              forall: if false → result=0, br $qbreak_N
              exists: if true  → result=1, br $qbreak_N
              counter++
              br $qloop_N
            end
          end
          local.get result
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

        # Evaluate predicate body (counter is in env as @T)
        for instr in body_instrs:
            instructions.append(f"    {instr}")

        # Short-circuit check
        if is_forall:
            # forall: if predicate is false → result=0, break
            instructions.append("    i32.eqz")
            instructions.append("    if")
            instructions.append("      i32.const 0")
            instructions.append(f"      local.set {result_local}")
            instructions.append(f"      br {brk}")
            instructions.append("    end")
        else:
            # exists: if predicate is true → result=1, break
            instructions.append("    if")
            instructions.append("      i32.const 1")
            instructions.append(f"      local.set {result_local}")
            instructions.append(f"      br {brk}")
            instructions.append("    end")

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
        type_name = self._extract_state_type_name(expr.effect_ref)
        if type_name is None:
            raise CodegenInvariantError(  # pragma: no cover
                "old(State<T>) effect ref has no extractable type name", expr)
        local_idx = self.get_old_state_local(type_name)
        if local_idx is None:
            raise CodegenInvariantError(  # pragma: no cover
                "old(State<T>) has no saved pre-execution state local", expr)
        return [f"local.get {local_idx}"]

    def _translate_new_expr(self, expr: ast.NewExpr) -> list[str] | None:
        """Translate new(State<T>) → call state_get to read current value."""
        type_name = self._extract_state_type_name(expr.effect_ref)
        if type_name is None:
            raise CodegenInvariantError(  # pragma: no cover
                "new(State<T>) effect ref has no extractable type name", expr)
        # Look up the state getter import
        if "get" not in self._effect_ops:
            raise CodegenInvariantError(  # pragma: no cover
                "new(State<T>) has no 'get' effect op registered", expr)
        call_target, _is_void = self._effect_ops["get"]
        return [f"call {call_target}"]

    @staticmethod
    def _extract_state_type_name(
        effect_ref: ast.EffectRefNode,
    ) -> str | None:
        """Extract the type name from a State<T> effect reference."""
        if not isinstance(effect_ref, ast.EffectRef):
            raise CodegenInvariantError(  # pragma: no cover
                "State type ref is not an EffectRef", effect_ref)
        if effect_ref.name != "State":
            raise CodegenInvariantError(  # pragma: no cover
                "State type ref name is not 'State'", effect_ref)
        if not effect_ref.type_args or len(effect_ref.type_args) != 1:
            raise CodegenInvariantError(  # pragma: no cover
                "State<T> must have exactly one type argument", effect_ref)
        # #914 finding 1: return the CANONICAL slot name (`Option<Int>`), not
        # the base name (`Option`).  `_state_types` and `get_old_state_local`
        # are keyed canonically, so a base-name key missed the registered
        # entry — no `old(State<T>)` snapshot local was allocated and the read
        # raised an uncaught `CodegenInvariantError` at run.  Shared recursive
        # builder so nested composites (`Option<Tuple<Int, Int>>`) are exact.
        name = type_expr_slot_name(effect_ref.type_args[0])
        if name is None:
            raise CodegenInvariantError(  # pragma: no cover
                "State<T> type argument is not a NamedType", effect_ref)
        return name

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
        return (self._is_static_nat_typed(expr.left)
                and self._is_static_nat_typed(expr.right)
                and (self._has_nat_origin_codegen(expr.left)
                     or self._has_nat_origin_codegen(expr.right)))

    def _is_static_nat_typed(self, expr: ast.Expr) -> bool:
        """Return True iff *expr* has static type @Nat.

        Mirrors :py:meth:`ContractVerifier._is_nat_typed`.  Returns
        True for SlotRef of type @Nat, non-negative IntLits,
        arithmetic expressions where both operands are @Nat (per
        vera/checker/expressions.py:264-267 Nat <: Int subtyping
        rule), IfExpr / MatchExpr with all branches @Nat, and FnCall
        returning @Nat.  Conservative False elsewhere — UnaryExpr
        (negation) always produces @Int.
        """
        if isinstance(expr, ast.SlotRef):
            return expr.type_name == "Nat"
        if isinstance(expr, ast.IntLit):
            return expr.value >= 0
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in (
                ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
                ast.BinOp.DIV, ast.BinOp.MOD,
            ):
                return (self._is_static_nat_typed(expr.left)
                        and self._is_static_nat_typed(expr.right))
            return False
        if isinstance(expr, ast.IfExpr):
            if expr.else_branch is None:
                return False
            return (self._is_static_nat_typed(expr.then_branch)
                    and self._is_static_nat_typed(expr.else_branch))
        if isinstance(expr, ast.Block):
            return self._is_static_nat_typed(expr.expr)
        if isinstance(expr, ast.MatchExpr):
            if not expr.arms:
                return False
            return all(
                self._is_static_nat_typed(arm.body) for arm in expr.arms
            )
        if isinstance(expr, ast.FnCall):
            ret_type_name = self._infer_fncall_vera_type(expr)
            return ret_type_name == "Nat"
        if isinstance(expr, ast.ModuleCall):
            # ModuleCall is desugared to FnCall in
            # vera/wasm/context.py:translate_expr (line 315), so the
            # callee's return type is reachable via the same
            # _infer_fncall_vera_type lookup once we synthesize the
            # flattened FnCall shape.
            return self._infer_fncall_vera_type(
                ast.FnCall(name=expr.name, args=expr.args, span=expr.span),
            ) == "Nat"
        return False

    def _result_is_nat(self, expr: ast.Expr) -> bool:
        """Codegen mirror of ``ContractVerifier._result_is_nat`` (#813).

        The *precise* result type — the join over a ``Block`` trailing expr,
        ``IfExpr`` branches, and ``MatchExpr`` arms — used to decide whether a
        value widening into an @Int slot needs the @Nat->@Int coercion guard.

        Unlike :py:meth:`_is_static_nat_typed`, a non-negative ``IntLit`` is NOT
        @Nat here (a literal in an @Int context is just an @Int literal, already
        range-checked) and arithmetic is @Nat only when *both* operands are — so
        a single @Int component makes the result @Int.  Must agree with the
        verifier's ``_result_is_nat`` so the codegen guard fires at exactly the
        sites the verifier obligates (the verifier<->codegen differential).

        Caveat (no-side-table fallback): when the checker's resolved-type table
        is absent (an unverified ``transform -> compile``), the ``FnCall`` arm
        recovers a callee's @Nat return from its *declared* return type — the
        same coarse basis as :py:meth:`_is_static_nat_typed`, NOT the verifier's
        precise ``_result_is_nat``.  This is deliberate: the precise join is
        unavailable without the side-table, and over-classifying a call result
        as @Nat here only ever suppresses a (dead) guard on a provably-@Nat
        value — never a wrong runtime verdict — so a verified build (which
        supplies the table) still matches the verifier site-for-site.
        """
        if isinstance(expr, ast.Block):
            return expr.expr is not None and self._result_is_nat(expr.expr)
        if isinstance(expr, ast.IfExpr):
            # #813 follow-up site 2a: a non-negative literal arm is @Nat-
            # compatible (always <= i64.MAX, so it never out-of-range-widens nor
            # false-traps the boundary guard).  Keep a heterogeneous-with-literal
            # if (`if c then { @Nat.0 } else { 0 }`) classified @Nat so the
            # boundary guard fires on the real @Nat arm — must mirror the
            # verifier's `_result_is_nat` exactly (the widening differential).
            if expr.else_branch is None:
                return False
            return (
                self._arm_nat_compatible(expr.then_branch)
                and self._arm_nat_compatible(expr.else_branch)
                and (self._result_is_nat(expr.then_branch)
                     or self._result_is_nat(expr.else_branch))
            )
        if isinstance(expr, ast.MatchExpr):
            return (
                bool(expr.arms)
                and all(self._arm_nat_compatible(a.body) for a in expr.arms)
                and any(self._result_is_nat(a.body) for a in expr.arms)
            )
        if isinstance(expr, ast.SlotRef):
            return expr.type_name == "Nat"
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in (
                ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
                ast.BinOp.DIV, ast.BinOp.MOD,
            ):
                return (self._result_is_nat(expr.left)
                        and self._result_is_nat(expr.right))
            return False
        if isinstance(expr, (ast.FnCall, ast.ModuleCall)):
            # Mirror the verifier: `nat_to_int(x)` explicitly widens its @Nat
            # argument to @Int.  Its declared @Int return hides the @Nat source
            # from the side-table, so special-case it so the result is guarded
            # at every widening boundary (#813 follow-up audit site 1).
            if (
                isinstance(expr, ast.FnCall)
                and expr.name == "nat_to_int"
                and expr.args
                and self._result_is_nat(expr.args[0])
            ):
                return True
            # Match the verifier's `_result_is_nat` FnCall branch, which reads
            # the checker's resolved-type side-table (`_resolved_type_of`).  A
            # call's @Nat return cannot be recovered from
            # `_infer_fncall_vera_type`: it maps the i64 WASM return back to
            # "Int" (both @Nat and @Int lower to i64) and so NEVER yields "Nat",
            # which left every @Nat-returning call result unguarded at the
            # return / let / call-argument sites while the verifier obligated it
            # `tier3` — an unsound silent reinterpretation (#813 review).
            # Consult the side-table first; fall back to `_infer_fncall_vera_type`
            # for built-in @Nat returns when codegen runs without the table.
            resolved = self._resolved_codegen_type(expr)
            if resolved is not None:
                return resolved == "Nat"
            # No side-table (an unverified `vera compile`): recover a user
            # callee's declared @Nat return from `_fn_ret_type_exprs`, mirroring
            # the verifier's `env.lookup_function().return_type` path.
            # `_infer_fncall_vera_type` cannot — it maps the erased i64 return
            # back to "Int" (both @Nat and @Int lower to i64), which would make
            # a genuine @Nat -> @Nat tail call (`count_down(@Nat.0 - 1)`) look
            # like a narrowing and break its return_call TCO (#758).
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
        # IntLit (literal in target context), UnaryExpr (negation -> @Int), else.
        return False

    def _arm_nat_compatible(self, expr: ast.Expr) -> bool:
        """Codegen mirror of ``ContractVerifier._arm_nat_compatible`` (#813 site
        2a): an if/match arm is @Nat-compatible if intrinsically @Nat or a
        non-negative literal (always <= i64.MAX, so safe at a widening join)."""
        return self._result_is_nat(expr) or self._is_nonneg_int_literal(expr)

    @staticmethod
    def _is_nonneg_int_literal(expr: ast.Expr) -> bool:
        """Codegen mirror: (a block trailing into) a non-negative int literal."""
        while isinstance(expr, ast.Block):
            if expr.expr is None:
                return False
            expr = expr.expr
        return isinstance(expr, ast.IntLit) and expr.value >= 0

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

    def _emit_nat_sub_guard(
        self, left: list[str], right: list[str],
    ) -> list[str]:
        """Emit a guarded `i64.sub` that traps on underflow.

        Pattern:

            [left] [right]
            local.set $rhs_tmp     ;; pop rhs into temp
            local.tee $lhs_tmp     ;; pop lhs into temp, leave on stack
            local.get $rhs_tmp     ;; push rhs back (stack: [lhs, rhs])
            i64.lt_s               ;; lhs < rhs?
            if
              unreachable          ;; trap; classified as "unreachable"
            end                    ;;   by vera/codegen/api.py:_classify_trap
            local.get $lhs_tmp
            local.get $rhs_tmp
            i64.sub

        The trap is the bare `unreachable` instruction so it's
        classified by the existing trap taxonomy as
        ``kind="unreachable"`` — adding a dedicated ``"underflow"``
        kind with a specific Fix paragraph requires new
        host-import scaffolding (mirroring how `vera.contract_fail`
        works) and is left as a follow-up enhancement.  Users who
        want a precise diagnostic should run ``vera verify`` first;
        the guard's role is preventing silent corruption of @Nat
        slots in programs that skipped verification.
        """
        lhs_tmp = self.alloc_local("i64")
        rhs_tmp = self.alloc_local("i64")
        return [
            *left,
            *right,
            f"local.set {rhs_tmp}",
            f"local.tee {lhs_tmp}",
            f"local.get {rhs_tmp}",
            "i64.lt_s",
            "if",
            "  unreachable",
            "end",
            f"local.get {lhs_tmp}",
            f"local.get {rhs_tmp}",
            "i64.sub",
        ]

    def _emit_nat_bind_guard(self, value: list[str]) -> list[str]:
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
              unreachable      ;; trap; classified "unreachable"
            end                ;;   by vera/codegen/api.py:_classify_trap
            local.get $tmp     ;; restore the (now-checked) value

        Like the #520 guard, the bare ``unreachable`` trap reuses the
        existing taxonomy; a dedicated "negative-nat" trap kind with a
        tailored Fix paragraph (#754) needs the contract-fail host-import
        channel wired through to a guard emitted mid-expression and is
        tracked as a follow-up.  The guard never fires on a value
        the verifier proved non-negative, so a Tier-1-clean program pays
        only dead instructions, never a trap.
        """
        return self._emit_negative_i64_guard(value)

    def _emit_int_widen_guard(self, value: list[str]) -> list[str]:
        """Emit a guarded value that traps if a @Nat exceeds i64.MAX (#813).

        The @Nat -> @Int widening dual of :py:meth:`_emit_nat_bind_guard`: a
        runtime safety net for the ``nat_to_int_coerce`` obligation (E530) the
        verifier could not discharge statically (Tier 3), or that reaches codegen
        without ``vera verify`` having run.  A @Nat is stored as an i64; its
        unsigned value exceeds i64.MAX exactly when the sign bit is set — i.e.
        when the i64 reads as negative — so the guard traps on ``value < 0``
        (the same negative-i64 mechanism as the nat-bind guard).  Emitted at the
        @Nat -> @Int coercion sites the verifier obligates (return, call
        argument, let).  The bare ``unreachable`` reuses the existing trap
        taxonomy (a dedicated *widening* trap kind — modelled on the
        ``kind="overflow"`` #808 added for arithmetic overflow — is a
        follow-up); the guard never fires on a value the verifier proved
        ``<= i64.MAX``, so a Tier-1-clean program pays only dead instructions.
        """
        return self._emit_negative_i64_guard(value)

    def _emit_negative_i64_guard(self, value: list[str]) -> list[str]:
        """Shared mechanism behind the @Int->@Nat narrowing guard (#552) and
        the @Nat->@Int widening guard (#813): leave *value* on the stack, but
        trap (bare ``unreachable``, classified by ``api.py:_classify_trap``)
        when it reads as a negative i64.  Both callers reduce to this same
        sign-bit check today; they stay distinct entry points because each has
        its own deferred dedicated trap kind (#754 narrowing, and a widening
        kind modelled on #808's ``kind="overflow"``) that will give them
        tailored Fix paragraphs.

            [value]
            local.tee $tmp     ;; leave value on stack, copy to temp
            i64.const 0
            i64.lt_s           ;; value < 0?
            if unreachable end ;; trap
            local.get $tmp     ;; restore the (now-checked) value
        """
        tmp = self.alloc_local("i64")
        return [
            *value,
            f"local.tee {tmp}",
            "i64.const 0",
            "i64.lt_s",
            "if",
            "  unreachable",
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
        (`_result_is_nat` — a genuine @Nat->@Nat tail call resolves its callee's
        @Nat return here and so is NOT collected), the per-leaf form of the
        whole-body ``narrow_guarded`` gate.  Descends ``Block`` / ``IfExpr`` /
        ``MatchExpr`` joins exactly as the verifier does.
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
        if self._narrows_into_nat(expr) and not self._result_is_nat(expr):
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
            return self._emit_nat_bind_guard(instrs)
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
        """Codegen mirror of ``ContractVerifier._has_underflow_leaf`` (#552).

        True iff a statically-@Nat *value*'s value-producing tree
        contains a pure-literal subtraction (no @Nat provenance) — the
        #520-exempt ``0 - 1`` idiom, however wrapped (block / if / match)
        or nested in arithmetic.
        """
        if isinstance(value, ast.BinaryExpr):
            if (value.op == ast.BinOp.SUB
                    and not self._has_nat_origin_codegen(value)):
                return True
            return (self._has_underflow_leaf(value.left)
                    or self._has_underflow_leaf(value.right))
        if isinstance(value, ast.Block):
            return self._has_underflow_leaf(value.expr)
        if isinstance(value, ast.IfExpr):
            if value.else_branch is None:
                return False
            return (self._has_underflow_leaf(value.then_branch)
                    or self._has_underflow_leaf(value.else_branch))
        if isinstance(value, ast.MatchExpr):
            return any(self._has_underflow_leaf(arm.body)
                       for arm in value.arms)
        return False

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
        lt = self._overflow_codegen_type(expr.left)
        rt = self._overflow_codegen_type(expr.right)
        if lt is None or rt is None:
            return None
        return "Int" if "Int" in (lt, rt) else "Nat"

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
    ) -> list[str]:
        """Dispatch to the per-(op, type) guarded arithmetic sequence (#798).

        Each sequence computes the wrapping result, checks whether the true
        (unbounded) result left the i64 (@Int) / u64 (@Nat) range, and on
        overflow calls ``vera.overflow_trap`` then ``unreachable`` so the trap
        classifies as the precise ``kind="overflow"`` (#808) — carrying the
        overflow Fix paragraph — rather than the generic ``unreachable``;
        otherwise it leaves the wrapping result on the stack.  @Nat SUB never
        reaches here (excluded by the caller; it is ``nat_sub`` underflow).
        """
        # #808: every guard below traps through `vera.overflow_trap` + an
        # `unreachable`, so declare the host import.
        self._needs_overflow_trap = True
        if ovf == "Nat":
            if op == ast.BinOp.ADD:
                return self._emit_nat_add_guard(left, right)
            # MUL (SUB is excluded by the caller).
            return self._emit_nat_mul_guard(left, right)
        # @Int.
        if op == ast.BinOp.ADD:
            return self._emit_int_add_guard(left, right)
        if op == ast.BinOp.SUB:
            return self._emit_int_sub_guard(left, right)
        return self._emit_int_mul_guard(left, right)

    def _emit_int_add_guard(
        self, left: list[str], right: list[str],
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
            "  call $vera.overflow_trap",
            "  unreachable",
            "end",                           # stack: [r]
        ]

    def _emit_int_sub_guard(
        self, left: list[str], right: list[str],
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
            "  call $vera.overflow_trap",
            "  unreachable",
            "end",                           # stack: [r]
        ]

    def _emit_int_mul_guard(
        self, left: list[str], right: list[str],
    ) -> list[str]:
        """@Int MUL, signed i64 — the dangerous one.  Division round-trip with
        the ``INT_MIN * -1`` special case.

        ``overflow ⟺ a != 0 && ((a == -1 && b == INT_MIN) || (a != -1 && r/a != b))``

        The ``a == 0`` branch avoids ``r/0``; the ``a == -1`` pre-check avoids
        the native ``i64.div_s`` trap on ``INT_MIN / -1`` (testing ``b ==
        INT_MIN`` instead).  Uses ``local.set r_tmp`` to clear the operand
        stack before the nested ``if`` blocks (a value left under an ``if``
        whose arms don't symmetrically consume it is a WASM validation error),
        then pushes ``r`` at the end.  Leaves ``r`` on the stack."""
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
            "if",                            # a == 0 → safe, no checks
            "else",
            f"  local.get {a_tmp}",
            "  i64.const -1",
            "  i64.eq",
            "  if",                          # a == -1
            f"    local.get {b_tmp}",
            f"    i64.const {self._I64_MIN_CODEGEN}",
            "    i64.eq",
            "    if",                        # b == INT_MIN → overflow
            "      call $vera.overflow_trap",
            "      unreachable",
            "    end",
            "  else",                        # a != 0 && a != -1 → safe to divide
            f"    local.get {r_tmp}",
            f"    local.get {a_tmp}",
            "    i64.div_s",
            f"    local.get {b_tmp}",
            "    i64.ne",
            "    if",                        # r/a != b → overflow
            "      call $vera.overflow_trap",
            "      unreachable",
            "    end",
            "  end",
            "end",
            f"local.get {r_tmp}",          # stack: [r]
        ]

    def _emit_nat_add_guard(
        self, left: list[str], right: list[str],
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
            "  call $vera.overflow_trap",
            "  unreachable",
            "end",                           # stack: [r]
        ]

    def _emit_nat_mul_guard(
        self, left: list[str], right: list[str],
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
            "    call $vera.overflow_trap",
            "    unreachable",
            "  end",
            "end",
            f"local.get {r_tmp}",          # stack: [r]
        ]
