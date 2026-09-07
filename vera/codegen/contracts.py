"""Mixin for runtime contract insertion.

Compiles requires/ensures clauses into WASM precondition and
postcondition checks with informative failure messages.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass

from vera import ast, naming
from vera.monomorphize import mangle_type_name
from vera.narrowing import measure_component_needs_range_check
from vera.skip import CodegenSkip
from vera.wasm import WasmContext, WasmSlotEnv
from vera.wasm.helpers import state_type_arg
from vera.wasm.inference import substitute_type_vars

# Recursion bound for tuple-component boundary guards (#746).  A *finite* tuple
# type can nest only as deep as it is written, so any real program stays well
# under this; the limit exists to halt infinite recursion through mutually-
# recursive type aliases (which the checker currently accepts) and is failed
# CLOSED, never silently skipped — see `_emit_component_refinement_guards`.
_MAX_COMPONENT_GUARD_DEPTH = 16


@dataclass(frozen=True)
class _ComponentGuardSite:
    """One component of a boundary tuple the guard layer acts on (#1210).

    Yielded by :meth:`ContractsMixin._tuple_component_guard_sites`, which is
    the ONE decomposition three consumers read: the guard EMITTER, the
    has-guardable predicate that decides whether the return epilogue runs at
    all, and the host-import PRE-SCAN.  Carrying the layout (*field_offset*,
    *load_wt*) alongside the classification (*guard*, *nested*) is what lets
    the emitter consume the same enumeration rather than re-deriving it: a
    component this record does not describe is one no guard is emitted for,
    and one the pre-scan therefore need not register.
    """

    field_offset: int
    load_wt: str
    #: `(predicate, base slot-name)` — the pair `_refinement_guard_parts`
    #: returns, or the synthesized `@Nat.0 >= 0` for a bare-`@Nat` component.
    #: None when the component is guarded only through its inner components.
    guard: tuple[ast.Expr, str] | None
    #: The component's own type expression when it wraps a further tuple, so
    #: the caller can recurse; None otherwise.
    nested: ast.TypeExpr | None


class ContractsMixin:
    """Methods for compiling runtime contract checks."""

    def _refinement_guard_parts(
        self, te: ast.TypeExpr,
    ) -> tuple[ast.Expr, str] | None:
        """(predicate, base slot-name) if *te* is a refinement, else None
        (#746) — the codegen counterpart of the verifier's ``_refined_parts``.

        The DERIVATION is :func:`vera.naming.refinement_binder_parts` (#1208):
        chase the alias chain (``type PosInt = { @Int | ... }``; also
        ``type P2 = PosInt``) to the underlying ``RefinementType``, name its
        base with the ONE renderer, and conjoin the ``@Nat`` / ``@Byte`` base's
        implicit range so a value satisfying the written predicate but outside
        the base's range cannot launder past the guard.  It used to be a second
        hand-maintained copy of that walk, and the two had already drifted
        apart at the erased-base and nested-refinement corners; layering
        codegen's two WASM-specific decisions ON TOP of one shared derivation
        is what keeps the guard's binder equal to the key the predicate's
        ``@Base.n`` resolves to (and to the key the checker bound it under).

        The two decisions that stay here, because they are about a type's WASM
        REPRESENTATION and :mod:`vera.naming` must not import the backend:

        * a nested refinement base is rejected LOUDLY (E618) — naming reports
          the shape, codegen decides what to do about it;
        * an erased base emits NO guard at all.
        """
        parts = naming.refinement_binder_parts(te, self._alias_env)
        if parts is None:
            return None
        if parts.base_is_refinement:
            # Refinement-over-refinement (e.g. `type Tiny = { @Pos |
            # @Pos.0 < 10 }` where `Pos = { @Int | @Int.0 > 0 }`): the
            # outer guard would compile only the outer predicate and
            # silently DROP the inner `> 0` membership — a soundness
            # hole that wrongly accepts `f(-1)`.  The verifier records
            # such a narrowing Tier-3 and, since #1268,
            # **UNGUARDED** — `_refined_boundary_codegen_guardable` bails
            # on a refinement base for exactly this reason.  It used to
            # claim `guarded`, so `vera verify` exited 0 promising a
            # runtime check for a program `vera compile` then refuses:
            # a promise about a run that can never happen.  Reject it
            # loudly here at codegen (the "reject before codegen"
            # choice) with a clean E618 — a non-zero-exit diagnostic,
            # not a partial guard.  Returns None after
            # recording the error so the helper stays total; the
            # recorded error fails the compile.  This IS reachable.
            # `base` IS the inner `RefinementType` on this branch; the
            # isinstance keeps the unwrap total rather than asserting it.
            inner = ast.format_type_expr(
                parts.base.base_type
                if isinstance(parts.base, ast.RefinementType)
                else parts.base
            )
            # Once per SITE, not once per visit (PR #1224 review).  This
            # helper is consulted from several places per declaration — and,
            # since round 7, from the import pre-scan's derivation as well —
            # and a generic carrying a concrete nested-refinement parameter is
            # compiled once per instantiation from the SAME spans, so
            # `forall<T> fn g(@T, @Tiny -> @Int)` used at two types reported
            # the one declaration twice.  `_error_once` keys on the resolved
            # diagnostic location, which carries the owning file — two modules
            # whose declarations happen to share a line/column stay distinct.
            self._error_once(
                te,
                f"Refinement base '{parts.binder_name}' resolves to another "
                f"refinement ({{ {inner} | ... }}); a refinement base "
                "must not itself resolve to a refinement.",
                rationale="Composing nested refinement membership "
                "predicates is unsupported — the runtime guard would "
                "silently drop the inner base predicate, so codegen "
                "rejects this rather than emit a partial guard.",
                error_code="E618",
            )
            return None
        if self._type_expr_to_wasm_type(parts.base) is None:
            # A zero-size / erased base — `@Unit`, or a `Future`
            # transparently wrapping one (`Future<Unit>`; #841/#943):
            # there is no WASM local to load into a boundary predicate
            # check, so emit NO guard (the verifier records such a
            # refinement `tier3_unguarded` rather than claiming a runtime
            # check; CR db24433).  Keyed on codegen's OWN erasure
            # (`_type_expr_to_wasm_type` returns None iff a type has no
            # WASM representation), so the guard-skip set is exactly the
            # set with no runtime local — #943 review found the literal
            # `base_node.name == "Unit"` keying missed `Future<Unit>`,
            # which erases identically and raised a raw `ValueError` at
            # the `wt is None` invariant in `_compile_fn` below.
            return None
        return (parts.predicate, parts.binder_name)

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

    def _emit_boundary_refinement_guard(
        self,
        ctx: WasmContext,
        te: ast.TypeExpr,
        value_local: int,
        message_head: str,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """The two guard halves — classify then lower — as ONE call, for a
        boundary that reaches this layer from inside expression translation
        (#1268).

        Every other §2.6.5 guard site is CodeGenerator code that already
        holds both halves and calls them in sequence.  A ``throw`` payload is
        not: it is discovered mid-expression by :class:`WasmContext`, which
        owns the representation decisions (which local, at what width) but
        none of the lowering machinery — the string pool the trap message
        interns into, the ``$vera.contract_fail`` import flag, the E617/E618
        diagnostics.  So the context is handed this bound pair via
        ``set_refinement_guard_emitter`` and supplies only the local.

        Returns ``None`` for an unrefined *te* and for the two refined shapes
        :meth:`_refinement_guard_parts` emits no guard for — an erased
        ``@Unit`` base, and a nested refinement (which it also reports as a
        loud E618).  The verifier's ``_refined_boundary_codegen_guardable``
        mirrors exactly that set, so a caller recording the obligation
        ``guarded`` is making a claim this method keeps.  The nested-refinement
        half of that mirror is #1268's: it answered ``True`` there, so a
        program `vera compile` refuses outright (E618) verified clean while
        recording a Tier-3 runtime check that could never run.

        *message_head* is everything before the predicate in the trap text,
        so the message reads in the same shape as every other boundary's
        (``Refinement violation in <where>\\n  <role>: <predicate> failed``).
        """
        parts = self._refinement_guard_parts(te)
        if parts is None:
            return None
        predicate, base_name = parts
        message = f"{message_head}: {ast.format_expr(predicate)} failed"
        return self._emit_refinement_check(
            ctx, predicate, base_name, value_local, message, env,
        )

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

    def _tuple_component_guard_sites(
        self, te: ast.TypeExpr, _depth: int = 0,
    ) -> Iterator[_ComponentGuardSite]:
        """Decompose ONE level of a boundary tuple into its guarded components.

        THE tuple decomposition (#1210 round 7).  Every consumer that needs to
        know what the boundary-guard layer does to a tuple reads it from here:
        the emitter (`_emit_component_refinement_guards`), the return-epilogue
        gate (`_has_guardable_tuple_components`), and the host-import pre-scan
        (`_signature_refinement_predicates`).  They used to carry three
        hand-kept copies of the same classification, and the pre-scan's copy
        did not exist at all — a `handle[State<Nat>]` written in the
        refinement of a tuple COMPONENT was lowered as a guard here and
        registered by nobody, so a check-green program died at whole-module
        WAT with `unknown func $vera.state_push_Nat`.  A component that is not
        described by a yielded `_ComponentGuardSite` is one no guard is
        emitted for; that equivalence is the invariant, and it now holds by
        construction rather than by three functions agreeing.

        Laziness matters: the emitter allocates a local per yielded site, so
        the sites must be produced one at a time, interleaved with the
        caller's `ctx.alloc_local` calls, to keep the local numbering (and the
        E618 report order) exactly as it was.

        The depth limit is enforced HERE, once, for all three consumers.  It
        fails CLOSED: a tuple nested deeper than the limit is almost always an
        infinite type via mutually-recursive aliases (`type A = Tuple<B, Int>;
        type B = Tuple<A, Int>`, which the checker currently accepts), so
        whichever consumer reaches the bound first records the loud E617 and
        the compile fails — never a silent `return []` that drops the guards
        for every component past the limit (CR PR-review).  `_error_once`
        keeps the three consumers from tripling the one diagnostic.
        """
        if _depth > _MAX_COMPONENT_GUARD_DEPTH:
            self._error_once(
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
            return
        node = self._resolve_tuple_type(te)
        if node is None:
            return

        _sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8}
        _aligns = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4}
        offset = 4  # after the tag (i32, 4 bytes) — as construction lays it out
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
            # guarded by the caller) yet it is still yielded as nested so the
            # caller reaches the inner tuple.
            is_nested = (not is_nat
                         and self._resolve_tuple_type(comp_te) is not None)
            if parts is None and not is_nat and not is_nested:
                continue

            guard: tuple[ast.Expr, str] | None = parts
            if guard is None and is_nat:
                guard = (
                    ast.BinaryExpr(
                        op=ast.BinOp.GE,
                        left=ast.SlotRef(
                            type_name="Nat", type_args=None, index=0),
                        right=ast.IntLit(value=0)),
                    "Nat",
                )
            yield _ComponentGuardSite(
                field_offset=field_offset,
                # A pair component (String / Array) loads its ptr half — the
                # length is read from memory by the predicate, exactly as the
                # i32_pair return guard does (a Vera string / array is
                # self-describing from its pointer).
                load_wt="i32" if wt == "i32_pair" else wt,
                guard=guard,
                nested=comp_te if is_nested else None,
            )

    def _emit_component_refinement_guards(
        self,
        ctx: WasmContext,
        sig_text: str,
        te: ast.TypeExpr,
        value_local: int,
        env: WasmSlotEnv,
        role: str,
        _depth: int = 0,
    ) -> list[str]:
        """Per-component refinement / ``@Nat`` runtime guards for a boundary
        **tuple** value (#746, PR-review-found FFI gap).

        *sig_text* is the rendered signature the violation message names —
        ``ast.format_fn_signature(decl)`` for a named function, the
        ``fn(… -> …)`` rendering for a closure (#1235).  A pre-rendered
        string rather than the declaration itself, because an ``AnonFn``
        has no ``FnDecl`` to format and the two callers already build the
        same text for their top-level guards.

        The top-level param / return guard (``_refinement_guard_parts``) fires
        only when the boundary *type itself* is a refinement; a
        ``Tuple<PosInt, Int>`` parameter carries no top-level refinement, so its
        refined *components* would cross a ``public`` / FFI boundary unchecked
        even though the verifier *assumes* each component satisfies its
        refinement (the ``_term_source_fact`` projection fact backing the R1
        param-assume).  An external caller passing ``Tuple(-5, 3)`` into a
        ``Tuple<PosInt, Int>`` boundary would otherwise launder a violating
        component into a Tier-1-clean callee.

        This descends the tuple layout — via ``_tuple_component_guard_sites``,
        the ONE decomposition the has-guardable predicate and the host-import
        pre-scan read too — loads each refined / ``@Nat`` component from the
        heap value, and guards it with the same ``$vera.contract_fail``
        predicate check the top-level guard uses, so the violating component
        traps at the boundary.  Recurses into nested tuples.

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
        instrs: list[str] = []
        for site in self._tuple_component_guard_sites(te, _depth):
            # Load the component from the heap into a fresh local.
            comp_local = ctx.alloc_local(site.load_wt)
            instrs.append(f"local.get {value_local}")
            instrs.append(f"{site.load_wt}.load offset={site.field_offset}")
            instrs.append(f"local.set {comp_local}")

            # Guard the component's OWN predicate (a refined component) or the
            # bare-@Nat `>= 0`, THEN — if it also wraps a tuple — recurse into
            # its inner components.  A refinement OVER a tuple does both: its
            # top-level predicate here, its inner components via the recursion.
            if site.guard is not None:
                predicate, base_name = site.guard
                msg = (
                    f"Refinement violation in {sig_text}\n"
                    f"  {role} (tuple component): "
                    f"{ast.format_expr(predicate)} failed"
                )
                guard = self._emit_refinement_check(
                    ctx, predicate, base_name, comp_local, msg, env)
                if guard is not None:
                    instrs.extend(guard)
            if site.nested is not None:
                instrs.extend(self._emit_component_refinement_guards(
                    ctx, sig_text, site.nested, comp_local, env, role,
                    _depth + 1))
        return instrs

    def _has_guardable_tuple_components(
        self, te: ast.TypeExpr, _depth: int = 0,
    ) -> bool:
        """True iff *te* resolves to a tuple with at least one component that
        ``_emit_component_refinement_guards`` would guard (refined / ``@Nat`` /
        a nested guardable tuple).

        Used to keep ``_compile_postconditions`` from early-returning ``[]`` for
        a tuple *return* that carries no top-level refinement but does have
        guardable components.  Reads the SAME decomposition the emitter does
        (``_tuple_component_guard_sites``) rather than mirroring its
        classification, so the early-return decision cannot disagree with what
        the epilogue would emit; it stays a pure predicate, needing no ``ctx``,
        because the sites carry the classification without emitting anything.

        A type nested past the depth limit yields no sites and reports the
        decomposition's own fail-closed E617, so this returns False for one —
        and the compile fails on that error rather than on a missing guard.
        """
        for site in self._tuple_component_guard_sites(te, _depth):
            if site.guard is not None:
                return True
            if (site.nested is not None
                    and self._has_guardable_tuple_components(
                        site.nested, _depth + 1)):
                return True
        return False

    def _signature_refinement_predicates(
        self, sig: ast.FnDecl | ast.AnonFn,
    ) -> Iterator[ast.Expr]:
        """Every refinement predicate LOWERED as a boundary guard for *sig*.

        THE derivation the host-import pre-scans consume (#1210 rounds 5 and
        7), stated once against the emitters it must equal and living beside
        them.  A parameter or return type that resolves to a `{ @Base | P }`
        refinement has `P` emitted as a runtime guard in the prologue /
        epilogue, so a `handle[State<T>]` or a host-imported builtin written
        in `P` is LOWERED here — `type Big = { @Int | nat_to_int(
        handle[State<Nat>] … ) > 0 && @Int.0 > 5 }` used as a parameter type
        died at whole-module WAT with `unknown func $vera.state_push_Nat`,
        from a check-green program.  The predicate is reached through the
        ALIAS table rather than structurally from the signature's `TypeExpr`,
        which is why no amount of walking the AST from the body finds it.

        Round 5 enumerated only a named `FnDecl`'s own params and return.  The
        guard emitters are reached from three further routes, all of which
        lowered predicates this never registered:

        * a TUPLE PARAMETER's components (`functions.py` ->
          `_emit_component_refinement_guards`) — `fn f(@Tuple<Big, Int> …)`;
        * a TUPLE RETURN's components (`_compile_postconditions`) —
          `fn f(… -> @Tuple<Big, Int>)`;
        * an `AnonFn`'s refined params and return (`closures.py`) —
          `fn(@Big -> @Int)` and `fn(@Int -> @Big)` behind an `apply_fn`.

        All four routes are enumerated here now, through the same helpers the
        emitters call: `_refinement_guard_parts` for a top-level refinement
        (so the two bails below are ITS bails, not a copy of them — a
        nested-refinement base is an E618 with no guard, an erased base emits
        no guard) and `_tuple_component_guard_sites` for the decomposition (so
        the depth cap, the `@Unit`-component skip and the nested recursion are
        the emitter's own).  Registration must equal what is emitted, not
        exceed it: an import declared for a guard that is never emitted is a
        host obligation nothing calls.

        COMPONENT decomposition applies to a closure signature as well as a
        named one (#1235).  It was a `FnDecl`-only leg for exactly as long as
        the closure path emitted top-level formal / return guards only —
        enumerating a closure's tuple components then would have registered
        families no lowering asked for.  `_compile_lifted_closure` now
        consumes the same `_tuple_component_guard_sites` decomposition the
        named path consumes, so emitter and registration flip together and
        this walks every signature the same way.
        """
        for te in (*sig.params, sig.return_type):
            parts = self._refinement_guard_parts(te)
            if parts is not None:
                yield parts[0]
            yield from self._component_guard_predicates(te)

    def _component_guard_predicates(
        self, te: ast.TypeExpr, _depth: int = 0,
    ) -> Iterator[ast.Expr]:
        """The predicates `_emit_component_refinement_guards` would lower for
        *te*, in its own order — the enumeration half of that emitter, walking
        the same `_tuple_component_guard_sites` decomposition to the same depth
        cap.  A bare-`@Nat` component's synthesized `>= 0` is included: it
        registers nothing, but it IS lowered, and enumerating exactly the
        emitted set is what makes the two provably co-extensive."""
        for site in self._tuple_component_guard_sites(te, _depth):
            if site.guard is not None:
                yield site.guard[0]
            if site.nested is not None:
                yield from self._component_guard_predicates(
                    site.nested, _depth + 1)

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
                ctx, ast.format_fn_signature(decl), decl.return_type,
                result_local, env, "return value"))

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
            # Emit: call $vera.state_get_<Type> ; local.set <idx>.
            # #914: mangle so a composite State<T> old()-read matches the
            # mangled import identifier emitted by `assembly.py`.
            instrs.append(f"call $vera.state_get_{mangle_type_name(type_name)}")
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
            # Key the snapshot set by the resolved cell FAMILY — matches
            # `_state_types` registration and the `_translate_old_expr`
            # read, so `old(State<Count>)` snapshots (and finds) the `Nat`
            # family (#1205) and `old(State<MaybeInt>)` the `Option<Int>`
            # one (#1209).  The fallback for a resolution that names no
            # family is derived inside `_family_name_te`, so the two sides
            # cannot pass different ones.
            types.add(self._family_name_te(state_type_arg(expr.effect_ref)))
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
        for cell, wasm_t in self._state_types:
            if cell.family == type_name:
                return wasm_t
        return None

    # -----------------------------------------------------------------
    # Runtime decreases guard (#1172)
    # -----------------------------------------------------------------

    def _dec_translate_measure(
        self,
        ctx: WasmContext,
        contract: ast.Decreases,
        env: WasmSlotEnv,
    ) -> list[list[str]] | None:
        """Translate every measure component to value-producing WAT.

        An i64 component passes through; an ADT component is ranked
        through its structural-size helper.  Snapshots the rank-helper
        accumulator up front and restores it on EVERY failure, so a
        partial translation never leaves committed helpers with no
        guard using them.  Shared by the entry check and the self-tail
        site check — the single home for the translate/rank/rollback
        discipline (PR #1179 review).
        """
        comp_values: list[list[str]] = []
        helpers_snapshot = dict(self._dec_rank_helpers)
        for expr in contract.exprs:
            instrs = ctx.translate_expr(expr, env)
            if instrs is None:
                self._dec_rank_helpers = helpers_snapshot
                return None
            wt = ctx._infer_expr_wasm_type(expr)
            if wt == "i64":
                comp_values.append(instrs)
                continue
            # An i32 component is an ADT pointer (E127 rejects Bool/Byte
            # measures at check time): rank it by structural size.
            adt_name = self._dec_measure_adt_name(expr)
            if adt_name is None:
                self._dec_rank_helpers = helpers_snapshot
                return None
            size_fn = self._dec_rank_helper(adt_name)
            if size_fn is None:
                self._dec_rank_helpers = helpers_snapshot
                return None
            comp_values.append([*instrs, f"call {size_fn}"])
        return comp_values

    def _dec_measure_bound_check(
        self,
        ctx: WasmContext,
        contract: ast.Decreases,
        measured: list[int],
        name: str,
        indent: str = "",
    ) -> list[str]:
        """Trap when a measure component leaves the range the guard compares
        in (#1222) — the chain path's entry point, over components it has
        already evaluated into *measured*.

        The termination guard below compares with ``i64.lt_s`` / ``i64.ge_s``
        and the prover reasons over unbounded integers, so the two agree
        exactly while the measure's value is an i64.  A ``@Nat`` measure is a
        u64 in that i64: above ``i64.MAX`` it reads NEGATIVE, the guard's
        ``m >= 0`` clause fails, and a program whose termination the verifier
        PROVED at Tier 1 aborts with "failed to decrease" — a true statement
        about the machine value and a false one about the program.  Measured:
        `halve(2^63)` over `decreases(@Nat.0)` traps where `halve(2^63 - 1)`
        returns.

        The remedy is disclosure, not a wider comparison: the whole compiler
        treats a ``@Nat`` above ``i64.MAX`` as an edge it discloses (E530 /
        E531 exist for exactly that), so widening this one comparison would
        support a range the rest of the language does not.  The verifier
        obligates ``component <= i64.MAX`` and this is its Tier-3 backstop —
        so the failure names its own cause instead of borrowing the
        termination rule's.

        Emitted only for a ``@Nat``-typed component
        (:meth:`_dec_nat_measure_indices`).  Returns ``[]`` when no component
        needs it.

        TYPE-driven, not tier-driven, which is this backend's standing rule
        for a range guard (spec §11.2: the #798 overflow guard is emitted at
        every classified site "regardless of the verifier's tier").  So a
        measure a `requires` bounds — obligation `verified` — still pays two
        dead compares per hop, at the entry check and the self-tail site.
        That is deliberate: codegen does not read the obligation stream, and
        making it do so would put the artifact's soundness behind whether
        `vera verify` had been run, which is precisely the coupling
        `vera compile` is free of.  The cost is two i64 compares against a
        constant, on a branch that predicts perfectly.
        """
        # By INDEX, never by AST membership: two components can be
        # structurally equal (`decreases(@Nat.0, @Nat.0)`) and an `in` test
        # would then pair a check with whichever local matched first.
        locals_ = [
            measured[k] for k in self._dec_nat_measure_indices(ctx, contract)
            if k < len(measured)
        ]
        return self._dec_bound_check_pairs(locals_, name, indent)

    def _dec_bound_check_pairs(
        self,
        locals_: list[int],
        name: str,
        indent: str = "",
    ) -> list[str]:
        """The emission itself: one range check per component local.

        Both entry points reduce to this — the chain path, which already has
        the components in locals, and :meth:`_dec_bound_checks_only`, which
        evaluates them itself when the chain guard is declined — so the check
        and its message are one derivation rather than two.
        """
        checks: list[str] = []
        for local in locals_:
            msg = (
                f"decreases() measure in '{name}' is outside the i64 range "
                f"the termination check compares in: a @Nat above i64.MAX "
                f"reads as negative, so the metric cannot be compared"
            )
            ptr, length = self.string_pool.intern(msg)
            self._needs_contract_fail = True
            self._needs_memory = True
            checks.extend([
                f"{indent}local.get {local}",
                f"{indent}i64.const 0",
                f"{indent}i64.lt_s",
                f"{indent}if",
                f"{indent}  i32.const {ptr}",
                f"{indent}  i32.const {length}",
                f"{indent}  call $vera.contract_fail",
                f"{indent}  unreachable",
                f"{indent}end",
            ])
        return checks

    def _dec_nat_measure_indices(
        self, ctx: WasmContext, contract: ast.Decreases,
    ) -> list[int]:
        """The measure components whose readings can differ (#1222).

        The rule is :func:`vera.narrowing.measure_component_needs_range_check`
        and the table is the CHECKER's, which is what the verifier's own
        selector reads — so the obligation and the guard cover the same
        components by construction.  They did not: codegen re-derived the
        type from its own walker, which answers ``'Int'`` for a call, and
        ``'Int'`` is also the value meaning "no check needed", so
        ``decreases(size(@Nat.0))`` was obligated `tier3` and guarded by
        nothing while `vera run` at 2^63 still reported a failure to
        decrease.
        """
        return [
            k for k, expr in enumerate(contract.exprs)
            if measure_component_needs_range_check(
                ctx._checker_resolved_type(expr))
        ]

    def _dec_bound_checks_only(
        self,
        ctx: WasmContext,
        contract: ast.Decreases,
        name: str,
        env: WasmSlotEnv,
    ) -> list[str]:
        """The measure-range checks alone, for a function whose CHAIN guard
        is declined (#1222).

        The chain guard is declined in three cases — the function declares
        `Exn` (a throw unwinds past the exit restores and would leave stale
        chain state), a measure component is untranslatable, or an ADT
        component has no structural-rank helper — and every one of them is a
        statement about the CHAIN, not about the range.  A `@Nat` component's
        range check reads one locally-evaluated value and compares it against
        a constant: it carries nothing across activations, so nothing that
        declines the chain applies to it.

        Emitting it here is what keeps the obligation honest.  Recorded as a
        guarded Tier 3 it claims a runtime check, and folded into the chain
        guard that claim was false for exactly those shapes — measured on an
        `Exn`-declaring function, and on a `decreases(@Nat.0, @List<Int>.0)`
        whose parameterized-ADT SIBLING declines the whole guard while the
        `@Nat` component translates perfectly well.

        Each component is evaluated exactly once, so a component with a side
        effect cannot be run twice by this path.  A component that turns out
        not to translate yields NO checks at all rather than a partial set —
        the verifier's mirror declines with it.
        """
        nat_indices = self._dec_nat_measure_indices(ctx, contract)
        if not nat_indices:
            return []
        instrs: list[str] = []
        locals_: list[int] = []
        for k in nat_indices:
            value = ctx.translate_expr(contract.exprs[k], env)
            if value is None:
                return []
            local = ctx.alloc_local("i64")
            instrs.extend(value)
            instrs.append(f"local.set {local}")
            locals_.append(local)
        return instrs + self._dec_bound_check_pairs(locals_, name)

    def _compile_decreases_entry(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
        env: WasmSlotEnv,
    ) -> tuple[list[str], list[str], list[str] | None]:
        """Compile the entry check-and-set of the termination guard (#1172).

        For a function carrying a ``decreases`` clause, emits at entry:

        1. save this function's guard globals into fresh locals,
        2. evaluate every measure component (an ADT component through its
           structural-size helper, :meth:`_dec_rank_helper`),
        3. if a previous activation is live, trap through
           ``$vera.contract_fail`` unless the components decrease
           lexicographically while staying non-negative — the runtime
           mirror of ``_verify_decreases``'s Z3 rule
           (``new < old && new >= 0``, ADTs by rank), extended
           componentwise per spec §5.6.1's lexicographic tuples,
        4. record this activation's components as the new baseline.

        Returns ``(entry_instrs, restore_instrs, self_tail_prefix)``.
        The restores run at every non-trap exit (`_compile_fn` places
        them after the postconditions).  ``self_tail_prefix`` keeps TCO
        alive for SELF-recursive tail calls — the #517 property the
        documented pure-iteration idiom depends on: prepended before a
        ``return_call`` back into this function, it captures the
        argument values into locals, evaluates the measure over them,
        traps unless the hop lexicographically decreases against this
        activation's live globals, restores this activation's saved
        state (its frame is about to be elided — the `$gc_sp` pattern),
        and re-pushes the arguments for the transfer; the callee's entry
        then re-baselines from the outer state, so the chain rides the
        site checks with no frame growth.  ``None`` when a piece is
        untranslatable — `_compile_fn` then demotes that function's
        self-tail ``return_call``s to plain calls, where the entry check
        covers every hop (correct, at native-stack depth).  A tail call
        to a DIFFERENT guarded function is always demoted (the mutual-
        tail corner: with the frame elided there is no placement of the
        restore that neither erases the chain nor leaks it), and a tail
        call to an unguarded target just prepends the restores.

        A measure component the backend cannot translate produces no
        guard (``([], [])``): the static tier has already disclosed the
        obligation, and a partial guard would claim a check it does not
        perform.  Per-function state lives in module globals
        (``$dec_prev_<fn>_<k>`` / ``$dec_active_<fn>``, emitted by
        assembly from ``_dec_guard_fns``); chains are per function, so
        distinct guarded functions never compare measures across
        namespaces.
        """
        contract = next(
            (c for c in decl.contracts
             if isinstance(c, ast.Decreases) and c.exprs),
            None,
        )
        if contract is None:
            return [], [], None
        # An Exn-declaring function gets no guard: a WASM `throw`
        # unwinds past the trailing exit restores, leaving
        # `$dec_active_<fn>` set and `$dec_prev_<fn>_<k>` holding the
        # aborted activation's measure, so a later unrelated call would
        # compare against that stale baseline and trap a terminating
        # program.  The per-activation baseline lives in the callee's
        # locals, so no handler-side restore can reconstruct it.  No
        # guard rather than a leaky one — the static tier keeps the
        # obligation disclosed (PR #1179 review).
        if self._dec_declares_exn(decl):
            # #1222: the CHAIN is declined, the range check is not.  The
            # reason above is entirely about state carried across
            # activations; a component's range check carries none.
            return (
                self._dec_bound_checks_only(ctx, contract, decl.name, env),
                [], None,
            )

        name = decl.name
        maybe_components = self._dec_translate_measure(ctx, contract, env)
        if maybe_components is None:
            # #1222: likewise here — a sibling component the backend cannot
            # translate or rank declines the chain, and says nothing about a
            # `@Nat` component that translates perfectly well.
            return (
                self._dec_bound_checks_only(ctx, contract, name, env),
                [], None,
            )
        comp_values = maybe_components

        n = len(comp_values)
        saved_prev = [ctx.alloc_local("i64") for _ in range(n)]
        saved_active = ctx.alloc_local("i32")
        measured = [ctx.alloc_local("i64") for _ in range(n)]

        entry: list[str] = []
        for k in range(n):
            entry.append(f"global.get $dec_prev_{name}_{k}")
            entry.append(f"local.set {saved_prev[k]}")
        entry.append(f"global.get $dec_active_{name}")
        entry.append(f"local.set {saved_active}")
        for k in range(n):
            entry.extend(comp_values[k])
            entry.append(f"local.set {measured[k]}")
        # #1222: before the comparison, not after — a component outside the
        # comparable range makes every verdict below meaningless, including
        # the FIRST activation's, which records a baseline without comparing.
        entry.extend(self._dec_measure_bound_check(
            ctx, contract, measured, name))

        entry.append(f"local.get {saved_active}")
        entry.append("if")
        # Lexicographic decrease against the saved previous components:
        #   ok_k = (m_k < p_k && m_k >= 0) || (m_k == p_k && ok_{k+1})
        # built innermost-first so the whole chain is straight-line
        # stack code.
        def _ok(k: int) -> list[str]:
            strict = [
                f"  local.get {measured[k]}",
                f"  local.get {saved_prev[k]}",
                "  i64.lt_s",
                f"  local.get {measured[k]}",
                "  i64.const 0",
                "  i64.ge_s",
                "  i32.and",
            ]
            if k == n - 1:
                return strict
            return [
                *strict,
                f"  local.get {measured[k]}",
                f"  local.get {saved_prev[k]}",
                "  i64.eq",
                *_ok(k + 1),
                "  i32.and",
                "  i32.or",
            ]

        entry.extend(_ok(0))
        entry.append("  i32.eqz")
        entry.append("  if")
        msg = (
            f"decreases() measure in '{name}' failed to decrease: the "
            f"termination metric must strictly decrease and stay "
            f"non-negative on every recursive call"
        )
        ptr, length = self.string_pool.intern(msg)
        self._needs_contract_fail = True
        self._needs_memory = True
        entry.append(f"    i32.const {ptr}")
        entry.append(f"    i32.const {length}")
        entry.append("    call $vera.contract_fail")
        entry.append("    unreachable")
        entry.append("  end")
        entry.append("end")

        for k in range(n):
            entry.append(f"local.get {measured[k]}")
            entry.append(f"global.set $dec_prev_{name}_{k}")
        entry.append("i32.const 1")
        entry.append(f"global.set $dec_active_{name}")

        restore: list[str] = []
        for k in range(n):
            restore.append(f"local.get {saved_prev[k]}")
            restore.append(f"global.set $dec_prev_{name}_{k}")
        restore.append(f"local.get {saved_active}")
        restore.append(f"global.set $dec_active_{name}")

        self._dec_guard_fns[name] = n
        tail_prefix = self._dec_self_tail_prefix(ctx, decl, contract, restore)
        return entry, restore, tail_prefix

    def _dec_self_tail_prefix(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
        contract: ast.Decreases,
        restore: list[str],
    ) -> list[str] | None:
        """The instruction prefix for a SELF-recursive ``return_call``.

        At the site, the callee's arguments are already on the operand
        stack in parameter order (a String/Array parameter as its
        ``ptr, len`` i32 pair; a Unit parameter contributes nothing).
        Capture them into fresh locals (popping in reverse), bind this
        function's parameter slot names to those locals, evaluate every
        measure component over that environment, and trap through
        ``$vera.contract_fail`` unless the components decrease
        lexicographically (and stay non-negative) against this
        function's LIVE chain globals — the previous activation's
        baseline, which for a self-tail site is this activation's own
        entry measure.  Then restore the saved guard state (the frame is
        about to be elided) and re-push the arguments.  Returns None
        when any parameter or measure shape is untranslatable; the
        caller demotes that site instead — never a partial check.
        """
        name = decl.name
        param_layout: list[tuple[str, list[int]]] = []
        capture_env = WasmSlotEnv()
        for param_te in decl.params:
            wt = self._type_expr_to_wasm_type(param_te)
            if wt == "unsupported":
                return None
            if wt is None:
                continue  # Unit — no operand-stack slot, no binder
            if wt == "i32_pair":
                ptr_l = ctx.alloc_local("i32")
                len_l = ctx.alloc_local("i32")
                locs = [ptr_l, len_l]
                bind = ptr_l
                kinds = "i32_pair"
            else:
                loc = ctx.alloc_local(wt)
                locs = [loc]
                bind = loc
                kinds = wt
            param_layout.append((kinds, locs))
            slot = self._type_expr_to_slot_name(param_te)
            if slot:
                capture_env = capture_env.push(slot, bind)

        maybe_components = self._dec_translate_measure(
            ctx, contract, capture_env,
        )
        if maybe_components is None:
            return None
        comp_values = maybe_components

        n = len(comp_values)
        measured = [ctx.alloc_local("i64") for _ in range(n)]

        prefix: list[str] = []
        # Capture: pop in reverse parameter order (a pair pops len, ptr).
        for _kinds, locs in reversed(param_layout):
            for loc in reversed(locs):
                prefix.append(f"local.set {loc}")
        for k in range(n):
            prefix.extend(comp_values[k])
            prefix.append(f"local.set {measured[k]}")
        # #1222, at the site too: a self-tail hop evaluates the measure here
        # and compares it the same way, so it needs the same backstop.
        prefix.extend(self._dec_measure_bound_check(
            ctx, contract, measured, name))
        prefix.append(f"global.get $dec_active_{name}")
        prefix.append("if")

        def _ok(k: int) -> list[str]:
            strict = [
                f"  local.get {measured[k]}",
                f"  global.get $dec_prev_{name}_{k}",
                "  i64.lt_s",
                f"  local.get {measured[k]}",
                "  i64.const 0",
                "  i64.ge_s",
                "  i32.and",
            ]
            if k == n - 1:
                return strict
            return [
                *strict,
                f"  local.get {measured[k]}",
                f"  global.get $dec_prev_{name}_{k}",
                "  i64.eq",
                *_ok(k + 1),
                "  i32.and",
                "  i32.or",
            ]

        prefix.extend(_ok(0))
        prefix.append("  i32.eqz")
        prefix.append("  if")
        msg = (
            f"decreases() measure in '{name}' failed to decrease: the "
            f"termination metric must strictly decrease and stay "
            f"non-negative on every recursive call"
        )
        ptr, length = self.string_pool.intern(msg)
        prefix.append(f"    i32.const {ptr}")
        prefix.append(f"    i32.const {length}")
        prefix.append("    call $vera.contract_fail")
        prefix.append("    unreachable")
        prefix.append("  end")
        prefix.append("end")
        prefix.extend(restore)
        # Re-push the arguments in parameter order for the transfer.
        for _kinds, locs in param_layout:
            for loc in locs:
                prefix.append(f"local.get {loc}")
        return prefix

    #: Field types that contribute nothing to a structural rank — safe to
    #: step over.  Everything else either recurses (a concrete layout
    #: ADT) or fails helper generation (see `_dec_rank_helper`).
    _DEC_SCALAR_FIELD_TYPES = frozenset(
        {"Int", "Nat", "Bool", "Float64", "Byte", "String", "Unit"},
    )

    @staticmethod
    def _dec_measure_adt_name(expr: ast.Expr) -> str | None:
        """The ADT layout key for an i32-valued measure component.

        A slot-reference measure — the dominant shape, ``decreases(
        @List.1)`` — carries its type name syntactically.  A
        PARAMETERIZED slot type (``@List<Int>.0``) is declined: the
        registered layout describes the generic shape, but concrete
        construction recomputes field offsets from the actual type
        arguments (an ``Int`` payload is an 8-byte i64, pushing the tail
        past the generic layout's offset), so a rank walk over the
        generic offsets reads a payload as a pointer.  Ranking those
        needs per-instantiation helpers (the ``$eq_<type>`` pattern);
        until then a generic-typed measure gets no guard rather than a
        wrong one.  Other ADT-valued expressions (a call returning an
        ADT) are likewise not yet rankable.
        """
        if isinstance(expr, ast.SlotRef) and "<" not in expr.type_name:
            return expr.type_name
        return None

    @staticmethod
    def _dec_declares_exn(decl: ast.FnDecl) -> bool:
        """True when *decl*'s effect row names ``Exn`` (any payload).

        Shared by `_compile_decreases_entry` (which declines the guard)
        and core's ``_dec_collect`` pre-pass (so the tail-call
        discipline never demotes a call into a function that has no
        guard) — the two MUST agree or a `return_call` patch and the
        emitted entry desynchronize.
        """
        return isinstance(decl.effect, ast.EffectSet) and any(
            isinstance(eff, ast.EffectRef) and eff.name == "Exn"
            for eff in decl.effect.effects
        )

    def _dec_rank_helper(self, adt_name: str) -> str | None:
        """Emit (once) and name the structural-size helper for *adt_name*.

        ``$dec_size_<T>(ptr) -> i64`` counts constructors: 1 for the node
        plus the recursive size of every field whose declared type is
        itself a layout-backed ADT.  Scalar fields and erased
        type-parameter fields contribute nothing — the order is the
        concrete structure's size, which spec §5.6.1(3) states.  Mutually
        recursive ADTs work because helpers are recorded before their
        bodies are built.  Returns None when the layout (or its parallel
        ``field_types``) is unavailable — the caller then emits no guard.
        """
        mangled = mangle_type_name(adt_name)
        fn_name = f"$dec_size_{mangled}"
        if fn_name in self._dec_rank_helpers:
            return fn_name
        layouts = self._adt_layouts.get(adt_name)
        if not layouts:
            return None
        # Snapshot the accumulator: on failure EVERY helper this walk
        # committed is rolled back, not just our own reservation.  A
        # nested helper completed through the reservation short-circuit
        # stores a real body that calls THIS name — keeping it after the
        # reservation is deleted dangles `unknown func` at wat2wasm,
        # killing the compile on a check-green program (the
        # `_lift_pending_closures` rollback discipline; PR #1179 review).
        snapshot = dict(self._dec_rank_helpers)
        # Reserve the name first so a recursive field type terminates.
        self._dec_rank_helpers[fn_name] = ""

        lines = [
            f"  (func {fn_name} (param $p i32) (result i64)",
            "    (local $tag i32)",
            "    (local $acc i64)",
            "    local.get $p",
            "    i32.load",
            "    local.set $tag",
            "    i64.const 1",
            "    local.set $acc",
        ]
        ok = True
        for _ctor_name, layout in sorted(
            layouts.items(), key=lambda kv: kv[1].tag,
        ):
            if not layout.field_offsets:
                continue
            if (layout.field_types
                    and len(layout.field_types) != len(layout.field_offsets)):
                ok = False
                break
            for i, (offset, _wt) in enumerate(layout.field_offsets):
                ftype = (
                    layout.field_types[i] if layout.field_types else None
                )
                if ftype in self._DEC_SCALAR_FIELD_TYPES:
                    continue  # contributes nothing to the rank
                if (
                    ftype is None
                    or "<" in ftype
                    or ftype not in self._adt_layouts
                ):
                    # No field metadata, a parameterized field (the
                    # registered generic offsets are not authoritative
                    # for concrete construction — see
                    # `_dec_measure_adt_name`), or a type-var / unknown
                    # field type: the rank cannot be computed soundly, so
                    # the WHOLE helper fails, the measure gets no guard —
                    # never a frozen or wrong-offset rank (both false-
                    # trapped genuinely shrinking programs:
                    # ch02_adt_recursive, ch02_adt_tuple_recursive).
                    ok = False
                    break
                sub = self._dec_rank_helper(ftype)
                if sub is None:
                    ok = False
                    break
                lines.append("    local.get $tag")
                lines.append(f"    i32.const {layout.tag}")
                lines.append("    i32.eq")
                lines.append("    if")
                lines.append("      local.get $acc")
                lines.append("      local.get $p")
                lines.append(f"      i32.load offset={offset}")
                lines.append(f"      call {sub}")
                lines.append("      i64.add")
                lines.append("      local.set $acc")
                lines.append("    end")
            if not ok:
                break
        if not ok:
            self._dec_rank_helpers = snapshot
            return None
        lines.append("    local.get $acc")
        lines.append("  )")
        self._dec_rank_helpers[fn_name] = "\n".join(lines)
        return fn_name
