"""Mixin for runtime contract insertion.

Compiles requires/ensures clauses into WASM precondition and
postcondition checks with informative failure messages.
"""

from __future__ import annotations

from vera import ast
from vera.skip import CodegenSkip
from vera.wasm import WasmContext, WasmSlotEnv
from vera.wasm.inference import substitute_type_vars

# Recursion bound for tuple-component boundary guards (#746).  A *finite* tuple
# type can nest only as deep as it is written, so any real program stays well
# under this; the limit exists to halt infinite recursion through mutually-
# recursive type aliases (which the checker currently accepts) and is failed
# CLOSED, never silently skipped — see `_emit_component_refinement_guards`.
_MAX_COMPONENT_GUARD_DEPTH = 16


class ContractsMixin:
    """Methods for compiling runtime contract checks."""

    def _refinement_guard_parts(
        self, te: ast.TypeExpr,
    ) -> tuple[ast.Expr, str] | None:
        """(predicate, base slot-name) if *te* is a refinement, else None
        (#746) — the codegen counterpart of the verifier's ``_refined_parts``.

        Resolves an alias chain (``type PosInt = { @Int | ... }``; also
        ``type P2 = PosInt``) to the underlying ``RefinementType`` and returns
        its predicate plus the base type's *name* (the binder slot, e.g.
        ``Int`` for ``{ @Int | ... }`` or the canonical ``Array<Int>`` for
        ``{ @Array<Int> | array_length(@Array<Int>.0) > 0 }`` — matching
        ``_translate_slot_ref``'s key, since a bare ``Array`` would never
        resolve).  Unlike the
        verify side — where Z3 cannot decide ``array_length`` so a collection
        base is Tier 3 — the runtime guard compiles the predicate to WASM
        directly, so it covers any base whose predicate
        :py:meth:`WasmContext.translate_expr` can lower (:py:meth:`_emit_refinement_check`
        returns None and emits no guard when it cannot)."""
        node: ast.TypeExpr = te
        seen: set[str] = set()
        while (isinstance(node, ast.NamedType)
               and node.name in self._type_aliases
               and node.name not in seen):
            seen.add(node.name)
            node = self._type_aliases[node.name]
        if isinstance(node, ast.RefinementType):
            base = node.base_type
            if isinstance(base, ast.NamedType):
                # Build the canonical slot name the predicate's binder uses —
                # ``Array<Int>`` for a parameterised base, ``Int`` otherwise —
                # matching `_translate_slot_ref`'s key (a bare ``Array`` would
                # never resolve).
                name = base.name
                if base.type_args:
                    arg_names: list[str] = []
                    for ta in base.type_args:
                        if isinstance(ta, ast.NamedType):
                            arg_names.append(ta.name)
                        else:
                            return None
                    name = f"{base.name}<{', '.join(arg_names)}>"
                predicate = node.predicate
                # Conjoin the `@Nat` base's implicit `>= 0` when the base
                # resolves to `@Nat` — directly OR through an alias chain
                # (`type Age = Nat`).  The *decision* follows the base's
                # aliases, but the synthetic slot ref uses `name` (the binder
                # key the predicate uses and the guard pushes the value under,
                # e.g. `@Age.0`), NOT a literal `@Nat.0` which wouldn't resolve.
                # Mirrors the verifier's `_translate_refined_predicate` so the
                # runtime guard (and its trap message, both derived here) reject
                # a negative value satisfying P — `-1` for `{ @Age | @Age.0 < 10
                # }` — at an FFI/public boundary (CR f1f2a26, db24433).
                base_node: ast.TypeExpr = base
                bseen: set[str] = set()
                while (isinstance(base_node, ast.NamedType)
                       and base_node.name in self._type_aliases
                       and base_node.name not in bseen):
                    bseen.add(base_node.name)
                    base_node = self._type_aliases[base_node.name]
                if isinstance(base_node, ast.RefinementType):
                    # Refinement-over-refinement (e.g. `type Tiny = { @Pos |
                    # @Pos.0 < 10 }` where `Pos = { @Int | @Int.0 > 0 }`): the
                    # outer guard would compile only the outer predicate and
                    # silently DROP the inner `> 0` membership — a soundness
                    # hole that wrongly accepts `f(-1)`.  The verifier already
                    # records such a narrowing as a Tier-3 E506 (its
                    # `_base_slot_name` returns None for a non-primitive base),
                    # so reject it loudly here at codegen (the "reject before
                    # codegen" choice) with a clean E600 — a non-zero-exit
                    # diagnostic, not a partial guard.  Returns None after
                    # recording the error so the helper stays total; the
                    # recorded error fails the compile.  This IS reachable.
                    inner = ast.format_type_expr(base_node.base_type)
                    self._error(
                        te,
                        f"Refinement base '{base.name}' resolves to another "
                        f"refinement ({{ {inner} | ... }}); a refinement base "
                        "must not itself resolve to a refinement.",
                        rationale="Composing nested refinement membership "
                        "predicates is unsupported — the runtime guard would "
                        "silently drop the inner base predicate, so codegen "
                        "rejects this rather than emit a partial guard.",
                        error_code="E618",
                    )
                    return None
                if (isinstance(base_node, ast.NamedType)
                        and base_node.name == "Unit"):
                    # `@Unit` is zero-size / erased: there is no value to load
                    # into a boundary predicate check, so emit NO guard (the
                    # verifier records such a refinement `tier3_unguarded`
                    # rather than claiming a runtime check; CR db24433).
                    return None
                if (isinstance(base_node, ast.NamedType)
                        and base_node.name == "Nat"):
                    predicate = ast.BinaryExpr(
                        op=ast.BinOp.AND,
                        left=ast.BinaryExpr(
                            op=ast.BinOp.GE,
                            left=ast.SlotRef(
                                type_name=name, type_args=None, index=0),
                            right=ast.IntLit(value=0),
                        ),
                        right=predicate,
                    )
                if (isinstance(base_node, ast.NamedType)
                        and base_node.name == "Byte"):
                    # Conjoin the `@Byte` base's implicit `0 <= @Byte.0 <= 255`
                    # range the way `@Nat` conjoins `>= 0` above (#766, the
                    # deferred PR #763 range-conjoin point).  A `@Byte` crosses
                    # a public / FFI boundary as an unbounded i32, so a value
                    # SATISFYING P but outside 0..255 (e.g. `300` for `@Byte.0
                    # > 5`) would otherwise launder past the guard.  The
                    # synthetic refs use the binder key `name` (`@SmallByte.0`
                    # through an alias, `@Byte.0` directly) — the key the
                    # predicate uses and the guard pushes the value under, NOT a
                    # literal `@Byte.0` which wouldn't resolve for an alias.
                    # The literal bounds are Byte-typed slot comparisons, so
                    # `_translate_byte_binop` (#766) lowers them at i32 too.
                    slot = ast.SlotRef(type_name=name, type_args=None, index=0)
                    predicate = ast.BinaryExpr(
                        op=ast.BinOp.AND,
                        left=ast.BinaryExpr(
                            op=ast.BinOp.AND,
                            left=ast.BinaryExpr(
                                op=ast.BinOp.GE,
                                left=slot,
                                right=ast.IntLit(value=0),
                            ),
                            right=ast.BinaryExpr(
                                op=ast.BinOp.LE,
                                left=slot,
                                right=ast.IntLit(value=255),
                            ),
                        ),
                        right=predicate,
                    )
                return (predicate, name)
        return None

    def _emit_refinement_check(
        self,
        ctx: WasmContext,
        predicate: ast.Expr,
        base_name: str,
        value_local: int,
        message: str,
        base_env: WasmSlotEnv,
    ) -> list[str] | None:
        """Compile a refinement-predicate runtime guard over *value_local*
        (#746).

        The predicate is closed over the binder ``@<base>.0``; translating it
        against *base_env* extended with that base bound to *value_local* reads
        the value and yields an i32 boolean, exactly like a ``requires``
        clause.  Extending the function's own slot env (rather than a bare one)
        preserves the surrounding type context a pair value such as ``Array``
        needs — its ``(ptr, len)`` representation — so ``array_length`` and the
        like translate.  Traps via the ``$vera.contract_fail`` host import (the
        same channel used for precondition / postcondition failures) when the
        predicate is false.  Returns None when the predicate falls outside the
        compilable fragment (no guard emitted).

        A predicate that *raises* ``CodegenSkip`` while lowering (most commonly
        a generic / monomorphised function call whose instance isn't registered
        in this guard's context) is surfaced as a loud E617 error rather than
        (a) crashing ``vera compile`` with a raw traceback — the guard-emission
        sites sit outside the function-body ``CodegenSkip`` handler — or (b)
        being swallowed to ``return None``, which would silently DROP the guard
        the verifier recorded as runtime-checked (a true boundary silent
        failure).  CR PR-review."""
        guard_env = base_env.push(base_name, value_local)
        try:
            cond = ctx.translate_expr(predicate, guard_env)
        except CodegenSkip as skip:
            self._error(
                predicate,
                "Refinement predicate cannot be compiled to a runtime guard "
                f"at this boundary ({skip}); the verifier recorded it as "
                "runtime-checked, but codegen cannot emit the guard.",
                rationale="A refined parameter / return is guarded at the "
                "boundary by lowering its predicate to WebAssembly.  This "
                "predicate calls a construct the backend cannot lower here "
                "(e.g. a generic / monomorphised function call whose instance "
                "is not registered in this context), so the promised guard "
                "cannot be emitted — rejected loudly rather than silently "
                "dropped.",
                error_code="E617",
            )
            return None
        if cond is None:
            return None
        ptr, length = self.string_pool.intern(message)
        self._needs_contract_fail = True
        self._needs_memory = True
        return [
            *cond,
            "i32.eqz",
            "if",
            f"  i32.const {ptr}",
            f"  i32.const {length}",
            "  call $vera.contract_fail",
            "  unreachable",
            "end",
        ]

    def _resolve_type_alias(self, te: ast.TypeExpr) -> ast.TypeExpr:
        """Walk a ``type Foo = Bar`` alias chain to the underlying TypeExpr,
        applying each *generic* alias's type-argument substitution (cycle-
        guarded).  ``type Box<T> = Tuple<T, Int>`` resolves ``Box<PosInt>`` to
        ``Tuple<PosInt, Int>`` — NOT ``Tuple<T, Int>`` — so a refined argument
        isn't silently dropped, leaving the component unclassified and its guard
        unemitted (CR PR-review).  Mirrors the substituting alias walk in
        ``registration._resolves_to_nat`` (``substitute_type_vars`` with the
        alias's ``type_params`` → the use-site ``type_args``).  The codegen
        counterpart of the alias walk inside ``_refinement_guard_parts``,
        hoisted so the component-guard helper can classify a tuple component's
        resolved shape."""
        node: ast.TypeExpr = te
        seen: set[str] = set()
        while (isinstance(node, ast.NamedType)
               and node.name in self._type_aliases
               and node.name not in seen):
            seen.add(node.name)
            body = self._type_aliases[node.name]
            params = self._type_alias_params.get(node.name)
            if (params and node.type_args
                    and len(params) == len(node.type_args)):
                body = substitute_type_vars(
                    body, dict(zip(params, node.type_args)))
            node = body
        return node

    def _resolve_tuple_type(self, te: ast.TypeExpr) -> ast.NamedType | None:
        """Resolve aliases AND unwrap a refinement to the underlying
        ``Tuple<...>`` NamedType, else None.  A refinement OVER a tuple base
        (``type Pair = { @Tuple<PosInt, Int> | P }``) carries no top-level
        Tuple shape, so without unwrapping its refined *components* would cross
        a boundary unguarded even though the top-level predicate is checked (CR
        PR-review)."""
        node = self._resolve_type_alias(te)
        if isinstance(node, ast.RefinementType):
            node = self._resolve_type_alias(node.base_type)
        if (isinstance(node, ast.NamedType)
                and node.name == "Tuple"
                and node.type_args):
            return node
        return None

    def _emit_component_refinement_guards(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
        te: ast.TypeExpr,
        value_local: int,
        env: WasmSlotEnv,
        role: str,
        _depth: int = 0,
    ) -> list[str]:
        """Per-component refinement / ``@Nat`` runtime guards for a boundary
        **tuple** value (#746, PR-review-found FFI gap).

        The top-level param / return guard (``_refinement_guard_parts``) fires
        only when the boundary *type itself* is a refinement; a
        ``Tuple<PosInt, Int>`` parameter carries no top-level refinement, so its
        refined *components* would cross a ``public`` / FFI boundary unchecked
        even though the verifier *assumes* each component satisfies its
        refinement (the ``_term_source_fact`` projection fact backing the R1
        param-assume).  An external caller passing ``Tuple(-5, 3)`` into a
        ``Tuple<PosInt, Int>`` boundary would otherwise launder a violating
        component into a Tier-1-clean callee.

        This descends the tuple layout, loads each refined / ``@Nat`` component
        from the heap value, and guards it with the same
        ``$vera.contract_fail`` predicate check the top-level guard uses, so the
        violating component traps at the boundary.  Recurses into nested tuples.

        Only ``Tuple`` is handled: its component types are recoverable directly
        from the declared ``type_args``.  A user ADT's refined field types need
        the generic substitution the guard layer does not carry (a refined ADT
        *field* is obligated statically at its construction site and tracked for
        a runtime guard separately) — so this never fabricates a guard it
        cannot ground in a declared component type.

        ``value_local`` is the tuple's heap pointer; it is transitively rooted
        (a parameter is shadow-pushed in the prologue, a return value is live on
        the operand stack) and the emitted predicate checks do not allocate, so
        the loaded components need no separate GC rooting.  Mirrors the offset
        algorithm in ``_translate_constructor_call`` exactly — the layout this
        decomposes is the one construction built."""
        if _depth > _MAX_COMPONENT_GUARD_DEPTH:
            # Fail CLOSED, not silent: a tuple nested deeper than the limit is
            # almost always an infinite type via mutually-recursive aliases
            # (`type A = Tuple<B, Int>; type B = Tuple<A, Int>`, which the
            # checker currently accepts) — that recursion would never terminate,
            # and a bare `return []` would silently drop the guards for every
            # component past the limit.  Emit a loud diagnostic so the compile
            # fails rather than shipping partial boundary guards (CR PR-review).
            self._error(
                te,
                "Tuple nesting in this boundary type exceeds the runtime-guard "
                f"depth limit ({_MAX_COMPONENT_GUARD_DEPTH}); the type is most "
                "likely infinitely recursive (mutually-recursive type aliases), "
                "so its refined components cannot be fully guarded.",
                rationale="A refined tuple component is guarded by decomposing "
                "the type at the boundary.  A type nested past the depth limit "
                "cannot be fully decomposed, so codegen fails closed rather than "
                "emitting partial guards that would let a deep component cross "
                "the boundary unchecked.",
                error_code="E617",
            )
            return []
        node = self._resolve_tuple_type(te)
        if node is None:
            return []

        _sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8}
        _aligns = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4}
        offset = 4  # after the tag (i32, 4 bytes) — as construction lays it out
        instrs: list[str] = []
        for comp_te in (node.type_args or ()):  # _resolve_tuple_type: non-empty
            wt = self._type_expr_to_wasm_type(comp_te)
            if wt is None or wt == "unsupported":
                # @Unit component: zero-size, occupies no slot and is erased —
                # no value to guard and no offset advance (matching how
                # construction / extraction skip a Unit field).
                continue
            align = _aligns.get(wt, 8)
            offset = (offset + align - 1) & ~(align - 1)
            field_offset = offset
            offset += _sizes.get(wt, 8)

            parts = self._refinement_guard_parts(comp_te)
            resolved = self._resolve_type_alias(comp_te)
            is_nat = (parts is None
                      and isinstance(resolved, ast.NamedType)
                      and resolved.name == "Nat")
            # A nested component may be a tuple OR a refinement over a tuple
            # (`Tuple<Pair, Int>` where `Pair = { @Tuple<PosInt, Int> | P }`) —
            # `_resolve_tuple_type` unwraps both, so its inner components are
            # guarded recursively (CR PR-review).  When the component IS a
            # refinement, `parts` is non-None (its top-level predicate is
            # guarded below) yet we still recurse to reach the inner tuple.
            is_nested = (not is_nat
                         and self._resolve_tuple_type(comp_te) is not None)
            if parts is None and not is_nat and not is_nested:
                continue

            # Load the component from the heap into a fresh local.  A pair
            # component (String / Array) loads its ptr half — the length is read
            # from memory by the predicate, exactly as the i32_pair return guard
            # does (a Vera string / array is self-describing from its pointer).
            load_wt = "i32" if wt == "i32_pair" else wt
            comp_local = ctx.alloc_local(load_wt)
            instrs.append(f"local.get {value_local}")
            instrs.append(f"{'i32' if wt == 'i32_pair' else wt}.load "
                          f"offset={field_offset}")
            instrs.append(f"local.set {comp_local}")

            # Guard the component's OWN predicate (a refined component) or the
            # bare-@Nat `>= 0`, THEN — if it also wraps a tuple — recurse into
            # its inner components.  A refinement OVER a tuple does both: its
            # top-level predicate here, its inner components via the recursion.
            pred_parts: tuple[ast.Expr, str] | None = parts
            if pred_parts is None and is_nat:
                pred_parts = (
                    ast.BinaryExpr(
                        op=ast.BinOp.GE,
                        left=ast.SlotRef(
                            type_name="Nat", type_args=None, index=0),
                        right=ast.IntLit(value=0)),
                    "Nat",
                )
            if pred_parts is not None:
                predicate, base_name = pred_parts
                msg = (
                    f"Refinement violation in {ast.format_fn_signature(decl)}\n"
                    f"  {role} (tuple component): "
                    f"{ast.format_expr(predicate)} failed"
                )
                guard = self._emit_refinement_check(
                    ctx, predicate, base_name, comp_local, msg, env)
                if guard is not None:
                    instrs.extend(guard)
            if is_nested:
                instrs.extend(self._emit_component_refinement_guards(
                    ctx, decl, comp_te, comp_local, env, role, _depth + 1))
        return instrs

    def _has_guardable_tuple_components(
        self, te: ast.TypeExpr, _depth: int = 0,
    ) -> bool:
        """True iff *te* resolves to a tuple with at least one component that
        ``_emit_component_refinement_guards`` would guard (refined / ``@Nat`` /
        a nested guardable tuple).

        Used to keep ``_compile_postconditions`` from early-returning ``[]`` for
        a tuple *return* that carries no top-level refinement but does have
        guardable components — mirrors the per-component classification in the
        emit helper (kept a pure predicate so the early-return decision needs no
        ``ctx``)."""
        if _depth > _MAX_COMPONENT_GUARD_DEPTH:
            # Conservatively report "guardable" so a deep *return* is NOT
            # short-circuited away by `_compile_postconditions` — it flows into
            # `_emit_component_refinement_guards`, whose matching depth check
            # fails closed with a loud diagnostic.  Routing the failure through
            # the one emit-side error keeps the fail-closed behaviour single-
            # sourced (CR PR-review).
            return True
        node = self._resolve_tuple_type(te)
        if node is None:
            return False
        for comp_te in (node.type_args or ()):  # _resolve_tuple_type: non-empty
            if self._refinement_guard_parts(comp_te) is not None:
                return True
            resolved = self._resolve_type_alias(comp_te)
            if isinstance(resolved, ast.NamedType) and resolved.name == "Nat":
                return True
            # A nested tuple OR refinement-over-tuple component (unwrapped by
            # `_resolve_tuple_type`) may carry guardable inner components.
            if (self._resolve_tuple_type(comp_te) is not None
                    and self._has_guardable_tuple_components(
                        comp_te, _depth + 1)):
                return True
        return False

    def _format_contract_message(
        self,
        decl: ast.FnDecl,
        contract: ast.Requires | ast.Ensures,
    ) -> str:
        """Build a human-readable contract failure message string.

        For a Requires:
          Precondition violation in clamp(@Int, @Int, @Int -> @Int)
            requires(@Int.1 <= @Int.2) failed

        For an Ensures:
          Postcondition violation in double(@Int -> @Int)
            ensures(@Int.result >= 0) failed
        """
        if isinstance(contract, ast.Requires):
            kind = "Precondition"
            clause = "requires"
        else:
            kind = "Postcondition"
            clause = "ensures"
        sig = ast.format_fn_signature(decl)
        expr_text = ast.format_expr(contract.expr)
        return f"{kind} violation in {sig}\n  {clause}({expr_text}) failed"

    def _format_refinement_message(
        self,
        decl: ast.FnDecl,
        te: ast.TypeExpr,
        role: str,
    ) -> str:
        """Build a refinement-violation message for a runtime guard (#746).

        e.g. ``Refinement violation in clamp(@Int -> @Percentage)
        / return value: @Int.0 >= 0 && @Int.0 <= 100 failed``.  *role* is
        ``"parameter"`` or ``"return value"``.
        """
        sig = ast.format_fn_signature(decl)
        parts = self._refinement_guard_parts(te)
        pred_text = ast.format_expr(parts[0]) if parts is not None else "?"
        return (
            f"Refinement violation in {sig}\n"
            f"  {role}: {pred_text} failed"
        )

    def _compile_preconditions(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
        env: WasmSlotEnv,
    ) -> list[str]:
        """Compile runtime precondition checks.

        Non-trivial requires() clauses are compiled as:
            [condition]
            i32.eqz
            if
              i32.const <msg_ptr>
              i32.const <msg_len>
              call $vera.contract_fail
              unreachable  ;; trap on precondition violation
            end
        """
        instrs: list[str] = []
        for contract in decl.contracts:
            if not isinstance(contract, ast.Requires):
                continue
            if self._is_trivial_contract(contract):
                continue

            # Translate the precondition expression
            cond_instrs = ctx.translate_expr(contract.expr, env)
            if cond_instrs is None:
                # Can't compile this contract — skip silently
                # (verifier already classified it as Tier 3)
                continue

            instrs.extend(cond_instrs)
            instrs.append("i32.eqz")
            instrs.append("if")

            # Report which contract failed before trapping
            msg = self._format_contract_message(decl, contract)
            ptr, length = self.string_pool.intern(msg)
            self._needs_contract_fail = True
            self._needs_memory = True
            instrs.append(f"  i32.const {ptr}")
            instrs.append(f"  i32.const {length}")
            instrs.append("  call $vera.contract_fail")

            instrs.append("  unreachable")
            instrs.append("end")
        return instrs

    def _compile_postconditions(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
        env: WasmSlotEnv,
        ret_wt: str | None,
    ) -> list[str]:
        """Compile runtime postcondition checks.

        For functions returning a value:
            local.set $result_tmp    ;; save body result
            [condition with @T.result → local.get $result_tmp]
            i32.eqz
            if
              unreachable            ;; trap on postcondition violation
            end
            local.get $result_tmp    ;; push result back

        For Unit-returning functions, no result to save/restore.
        """
        # Collect non-trivial ensures clauses
        ensures_clauses: list[ast.Ensures] = []
        for contract in decl.contracts:
            if isinstance(contract, ast.Ensures):
                if not self._is_trivial_contract(contract):
                    ensures_clauses.append(contract)

        # #746: a refined return type is an implicit postcondition on the
        # result — guarded here alongside the explicit ensures, so a function
        # returning a refinement-violating value traps even with trivial
        # ensures.
        refined_ret = self._refinement_guard_parts(decl.return_type)
        # #746 PR-review: a tuple return with refined / @Nat *components* but no
        # top-level refinement still needs per-component exit guards, so don't
        # short-circuit on `refined_ret is None` alone.
        ret_components = self._has_guardable_tuple_components(decl.return_type)

        if not ensures_clauses and refined_ret is None and not ret_components:
            return []

        # Pair returns (String/Array) don't support general ensures checks
        # — can't bind `@T.result` to a two-value result.  A refinement guard,
        # however, needs only the value's primary local (the ptr; the length
        # is read from memory, as the param-guard path shows), so a refined
        # String *or* Array return IS guarded by saving both halves around the
        # check.  `_refinement_guard_parts` resolves the canonical base name
        # for a collection base too, so a `@NonEmptyArray` return is guarded
        # here despite being Tier-3 *statically* (#746) — see
        # test_array_return_guard_traps_on_empty.
        if ret_wt == "i32_pair":
            if refined_ret is None:
                return []
            predicate, base_name = refined_ret
            ptr_l = ctx.alloc_local("i32")
            len_l = ctx.alloc_local("i32")
            msg = self._format_refinement_message(
                decl, decl.return_type, "return value")
            guard = self._emit_refinement_check(
                ctx, predicate, base_name, ptr_l, msg, env)
            if guard is None:
                return []
            # Result is (ptr, len) with len on top of the stack.
            return [
                f"local.set {len_l}",
                f"local.set {ptr_l}",
                *guard,
                f"local.get {ptr_l}",
                f"local.get {len_l}",
            ]

        instrs: list[str] = []

        if ret_wt is not None:
            # Function returns a value — save it to a temp local
            result_local = ctx.alloc_local(ret_wt)
            ctx.set_result_local(result_local)
            instrs.append(f"local.set {result_local}")

            # #746: emit the refined-return guard BEFORE the explicit ensures
            # — an `ensures(...)` may depend on the return's refinement
            # invariant (e.g. divide by `@NonZero.result`), so the guard must
            # establish it first and report the boundary violation via
            # $vera.contract_fail rather than letting the postcondition trap on
            # the bad value (symmetric with the param-guard ordering in
            # functions.py).
            # #746 PR-review: per-component boundary guards for a tuple return —
            # symmetric with the tuple param guards in functions.py.  A
            # `fn -> Tuple<PosInt, Int>` whose body yields a refinement-
            # violating component traps here rather than handing a Tier-1-
            # violating tuple back across the boundary.  Returns no instructions
            # for a non-tuple return, so this is a no-op for ordinary returns.
            # Emitted BEFORE the top-level refined-return guard: a refinement
            # OVER a tuple has its predicate potentially read the components, so
            # establish those first (mirrors the param-guard order, CR).
            instrs.extend(self._emit_component_refinement_guards(
                ctx, decl, decl.return_type, result_local, env,
                "return value"))

            if refined_ret is not None:
                predicate, base_name = refined_ret
                msg = self._format_refinement_message(
                    decl, decl.return_type, "return value")
                guard = self._emit_refinement_check(
                    ctx, predicate, base_name, result_local, msg, env)
                if guard is not None:
                    instrs.extend(guard)

            for ensures in ensures_clauses:
                cond_instrs = ctx.translate_expr(ensures.expr, env)
                if cond_instrs is None:
                    # Can't compile — skip
                    continue
                instrs.extend(cond_instrs)
                instrs.append("i32.eqz")
                instrs.append("if")

                msg = self._format_contract_message(decl, ensures)
                ptr, length = self.string_pool.intern(msg)
                self._needs_contract_fail = True
                self._needs_memory = True
                instrs.append(f"  i32.const {ptr}")
                instrs.append(f"  i32.const {length}")
                instrs.append("  call $vera.contract_fail")

                instrs.append("  unreachable")
                instrs.append("end")

            # Push result back
            instrs.append(f"local.get {result_local}")
        else:
            # Unit return — no result to save, just check
            for ensures in ensures_clauses:
                cond_instrs = ctx.translate_expr(ensures.expr, env)
                if cond_instrs is None:
                    continue
                instrs.extend(cond_instrs)
                instrs.append("i32.eqz")
                instrs.append("if")

                msg = self._format_contract_message(decl, ensures)
                ptr, length = self.string_pool.intern(msg)
                self._needs_contract_fail = True
                self._needs_memory = True
                instrs.append(f"  i32.const {ptr}")
                instrs.append(f"  i32.const {length}")
                instrs.append("  call $vera.contract_fail")

                instrs.append("  unreachable")
                instrs.append("end")

        return instrs

    @staticmethod
    def _is_trivial_contract(contract: ast.Contract) -> bool:
        """Check if a contract is trivially true (literal true).

        Trivial contracts are skipped — no runtime check needed.
        """
        if isinstance(contract, ast.Requires):
            return isinstance(contract.expr, ast.BoolLit) and contract.expr.value
        if isinstance(contract, ast.Ensures):
            return isinstance(contract.expr, ast.BoolLit) and contract.expr.value
        return False

    def _snapshot_old_state(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
    ) -> list[str]:
        """Emit instructions to snapshot state at function entry for old().

        Walks ensures clauses to find old(State<T>) references.
        For each unique State<T>, calls the host state_get import and
        saves the result to a temp local. Registers the mapping on ctx
        so translate_expr can resolve OldExpr later.

        Returns WASM instructions (call + local.set) to insert after
        preconditions and before the function body.
        """
        old_types = self._find_old_state_types(decl)
        if not old_types:
            return []

        instrs: list[str] = []
        old_locals: dict[str, int] = {}

        for type_name in sorted(old_types):
            # Determine the WASM type for this State<T>
            wasm_t = self._state_type_to_wasm(type_name)
            if wasm_t is None:
                continue
            # Allocate a temp local for the snapshot
            local_idx = ctx.alloc_local(wasm_t)
            # Emit: call $vera.state_get_<Type> ; local.set <idx>
            instrs.append(f"call $vera.state_get_{type_name}")
            instrs.append(f"local.set {local_idx}")
            old_locals[type_name] = local_idx

        if old_locals:
            ctx.set_old_state_locals(old_locals)

        return instrs

    def _find_old_state_types(self, decl: ast.FnDecl) -> set[str]:
        """Find all State<T> type names referenced by old() in ensures clauses.

        Walks each non-trivial ensures expression looking for OldExpr nodes.
        Returns a set of type names, e.g. {"Int"}.
        """
        types: set[str] = set()
        for contract in decl.contracts:
            if not isinstance(contract, ast.Ensures):
                continue
            if self._is_trivial_contract(contract):
                continue
            self._collect_old_types(contract.expr, types)
        return types

    def _collect_old_types(
        self, expr: ast.Expr, types: set[str],
    ) -> None:
        """Recursively collect State<T> type names from OldExpr nodes."""
        if isinstance(expr, ast.OldExpr):
            type_name = WasmContext._extract_state_type_name(
                expr.effect_ref,
            )
            if type_name is not None:
                types.add(type_name)
            return
        # Walk child expressions
        for child in self._expr_children(expr):
            self._collect_old_types(child, types)

    @staticmethod
    def _expr_children(expr: ast.Expr) -> list[ast.Expr]:
        """Return direct child expressions for AST walking."""
        children: list[ast.Expr] = []
        if isinstance(expr, ast.BinaryExpr):
            children.extend([expr.left, expr.right])
        elif isinstance(expr, ast.UnaryExpr):
            children.append(expr.operand)
        elif isinstance(expr, ast.FnCall):
            children.extend(expr.args)
        elif isinstance(expr, ast.IfExpr):
            children.append(expr.condition)
        elif isinstance(expr, ast.NewExpr):
            pass  # No child expressions to walk
        elif isinstance(expr, ast.OldExpr):
            pass  # Already handled by caller
        return children

    def _state_type_to_wasm(self, type_name: str) -> str | None:
        """Map a State type name (e.g. 'Int') to its WASM type."""
        for registered_name, wasm_t in self._state_types:
            if registered_name == type_name:
                return wasm_t
        return None
