"""Function call and effect handler translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.binding import symbol
from vera.builtins import INTRINSICS, Binding, Intrinsic
from vera.skip import CodegenSkip
from vera.slots import bare_call_denotes_user_fn
from vera.wasm.helpers import WasmSlotEnv


def _mentions_type_var(te: ast.TypeExpr, type_vars: frozenset[str]) -> bool:
    """Whether the type expression *te* names one of *type_vars*: the
    formal whose instantiation only the checker's table records, as the
    verifier's `_nat_binding_target` asks of a formal containing one."""
    if isinstance(te, ast.NamedType):
        return te.name in type_vars or any(
            _mentions_type_var(arg, type_vars) for arg in te.type_args or ())
    if isinstance(te, ast.RefinementType):
        return _mentions_type_var(te.base_type, type_vars)
    if isinstance(te, ast.FnType):
        return (any(_mentions_type_var(p, type_vars) for p in te.params)
                or _mentions_type_var(te.return_type, type_vars))
    return False


class CallsMixin:
    """Core dispatch mixin for WasmContext.

    Houses the primary ``_translate_call`` and ``_translate_qualified_call``
    dispatchers and the generic-call resolution helpers.

    Individual built-in families live in sibling mixins:

    - ``CallsArraysMixin``      (calls_arrays.py)
    - ``CallsContainersMixin``  (calls_containers.py) — Map/Set/Decimal
    - ``CallsEncodingMixin``    (calls_encoding.py)   — Base64/URL
    - ``CallsHandlersMixin``    (calls_handlers.py)   — Show/Hash/handle
    - ``CallsMarkupMixin``      (calls_markup.py)     — JSON/HTML/Md/Regex
    - ``CallsMathMixin``        (calls_math.py)
    - ``CallsParsingMixin``     (calls_parsing.py)
    - ``CallsStringsMixin``     (calls_strings.py)
    """

    def _translate_call(
        self, call: ast.FnCall, env: WasmSlotEnv,
        *, denotes_op: bool | None = None, tail: bool = False,
    ) -> list[str] | None:
        """Translate a function call to WASM call instruction.

        If the call name matches an effect operation (e.g. get/put for
        State<T>), redirects to the corresponding host import.

        *tail* marks a call in tail position that is not itself a key of
        ``_tail_call_sites``: a module-qualified call by the module's own
        path, which ``translate_expr`` desugars into a fresh ``FnCall``
        (#1558).  Every other call is looked up by its own id.

        *denotes_op* overrides the bare-call ownership question (#1284) for
        a call this dispatcher did not receive bare.  ``None`` — every
        ordinary ``ast.FnCall`` — asks :meth:`_bare_call_denotes_op`.
        ``True`` is for the QUALIFIED spellings that delegate here by
        synthesizing a bare node (``State.get``/``State.put``/``Exn.throw``,
        below): the qualifier already named the effect, so no user
        declaration can shadow it and the synthesized node must not be
        re-asked as if the user had written the bare form.
        """
        # Built-in intrinsics — only when no user-defined function
        # with the same name exists.  User definitions take priority
        # so that e.g. a user-defined length(@List<Int> -> @Nat) is
        # not mistakenly compiled as the array-length built-in.  Same
        # ownership rule the effect-op dispatch below applies, over the
        # same table (#1284); spelled through the shared predicate so a
        # change to the rule reaches both.  The table is the LEXICAL one
        # (#1299) — an intrinsic must not be displaced by a declaration
        # this call site cannot see, any more than an operation must.
        # Which names are intrinsics, at which arity, and the emitter
        # each lowers through, are the registry's (`vera.builtins`,
        # #735); a name called at another arity falls through to the
        # routes below, as an ordinary call does.
        if not bare_call_denotes_user_fn(call.name, self._scoped_fns):
            intrinsic = INTRINSICS.get(call.name)
            if intrinsic is not None and len(call.args) == intrinsic.arity:
                return self._lower_intrinsic(intrinsic, call, env)

        # Check if this is a closure application: apply_fn(closure, args...)
        if call.name == "apply_fn" and len(call.args) >= 2:
            return self._translate_apply_fn(call, env)

        # #1284: whose declaration this call site names, asked ONCE and
        # consumed by every op route below.  The op registries are keyed by
        # op NAME and say which cell that name reaches; they do NOT say
        # whether this call is the operation at all, and reading them as if
        # they did is the defect: a program declaring `fn get` had its
        # ordinary calls lowered to the host cell intrinsic under any
        # enclosing `handle[State<T>]` — a silently wrong value, a module
        # WASM validation rejected, or a spurious [E602] naming a State
        # operation the source never contained.  The checker resolved every
        # one of those call sites to the user's declaration (E201/E202
        # report against the user's signature), so this is that answer.
        if denotes_op is None:
            denotes_op = self._bare_call_denotes_op(call.name)

        if denotes_op:
            # #1233: inside an inlined clause body, an outward-routed op of
            # the SAME cell family cannot address the enclosing cell — the
            # intrinsics only reach the innermost cell of a family.  Refuse
            # it here, before either dispatch below picks a route, so both
            # the clause-inline and the bare-import path are covered by one
            # gate (and so is the qualified `State.get`/`State.put`
            # spelling, which delegates here).  Gated on ownership with the
            # dispatch it guards: a user function's call reaches no cell, so
            # asking whether it can address one refused compilable programs.
            self._reject_unaddressable_clause_op(call)

            # #976 option C: a get/put under a handle with registered clauses
            # inlines the clause body at the call site (intrinsic-hybrid
            # semantics) instead of the bare host-cell call below.
            if call.name in self._state_clause_ops:
                return self._translate_state_clause_op(call, env)
        # Inside an inlined State clause, resume(v)'s value IS the op's
        # result at the original call site (single-shot, tail position —
        # enforced before inlining).  resume(()) is a UnitLit: no value,
        # matching put's void result.
        if call.name == "resume" and self._in_state_clause:
            return self.translate_expr(call.args[0], env)

        # Check if this is an effect operation (e.g. get/put/throw)
        if denotes_op and call.name in self._effect_ops:
            target_name, _is_void = self._effect_ops[call.name]
            instructions: list[str] = []
            # #747: the effect-op-argument @Int -> @Nat narrowing is in
            # general unguarded here — `_effect_ops` carries only the
            # dispatch target, not the op's formal types (#754 tracks the
            # general registry).  The builtin State `put` is the exception
            # (#1203, PR #1202 adversarial round): the cell it writes is
            # recorded beside the dispatch target, so the same nat
            # guard the clause-inlined path emits wraps the argument on
            # the bare path too — a handler with no `put` clause, a `put`
            # inside another clause's body, and a delegated bare `put`
            # (handler in the caller) all previously stored a negative
            # silently.
            #
            # The cell's REPRESENTATION name, read from `_effect_op_cells`
            # (#1218).  This used to SLICE the family back out of the
            # dispatch target (`target_name[len("$vera.state_put_"):]`) and
            # hand the MANGLED result to `_resolve_base_type_name`, which
            # expects a canonical one — a second derivation of the family
            # that worked only because `Nat`/`Int`/`Byte` mangle to
            # themselves.  A refined `Nat` cell does not (its family carries
            # the predicate), so the slice would have matched nothing and
            # switched this guard off silently, while the verifier went on
            # recording the obligation as `tier3_runtime`.
            # ONE normalisation for all three sibling decisions (PR #1238
            # review).  The Nat/Int guards resolved `cell.base` and the Byte
            # width coercion did not, so a base that still needs alias
            # resolution — which `family_fallback_name`'s residue can produce
            # — would fire the guards and skip the coercion, putting an
            # `i64.const` into an i32 cell.
            cell = self._effect_op_cells.get(call.name)
            is_state_put = (
                call.name == "put" and len(call.args) == 1
                and cell is not None
            )
            # `throw`'s payload is the OTHER cell-carrying write boundary
            # (#1269).  The `Exn<E>` tag is declared at the payload's
            # representation width — i32 for a `@Byte` payload, refined or
            # not — while an int literal defaults to `i64.const`, so
            # `throw(5)` into `Exn<{ @Byte | … }>` emitted a module WASM
            # validation rejects at load.  Same marking, same derivation,
            # different op — and, since #1268, the same narrowing GUARDS
            # below: the payload is a write boundary in the full sense, not
            # only in its width.
            is_exn_throw = (
                call.name == "throw" and len(call.args) == 1
                and cell is not None
            )
            # `_boundary_base`'s composition with its FIRST hop already
            # performed, at registration: the registry carries a name, not
            # the type expression, so this site cannot call the named helper
            # and applies the residue chase itself.  Two of the three
            # producers (both `handle` sites) store an already-chased base,
            # so this is a no-op for them; the declaration-row producer
            # (`codegen/functions.py`) has no `_resolve_base_type_name` to
            # reach, which is the only reason the hop still lives here.
            #
            # UNTESTED as of #1273: deleting the chase leaves the suite green,
            # because `family_base_name` already answers `Byte` for every
            # refinement and alias reachable today, so no producer stores a
            # base that still needs chasing.  It is defence for the residue
            # `family_fallback_name` can return (a function or unknown type),
            # which no boundary that asks this question can currently carry.
            # A fixture exercising it needs a producer that stores an
            # UNCHASED base — construct one and this becomes testable.
            base = (
                self._resolve_base_type_name(cell.base)
                if (is_state_put or is_exn_throw) and cell is not None
                else None
            )
            for arg in call.args:
                arg_instrs = self.translate_expr(arg, env)
                if arg_instrs is None:
                    return None
                instructions.extend(arg_instrs)
            # The write boundary's guards.  `throw` joined `put` here in
            # #1268: its payload narrows into the `Exn<E>` slot exactly as
            # `put`'s argument narrows into the cell, but it crossed no
            # function boundary, so none of §2.6.5's composing guards covered
            # it — `throw(0 - 5)` into an `Exn<Nat>` ran to completion and
            # handed `-5` to a clause that had assumed non-negativity, and a
            # `@Nat`-typed consumer's Tier-1-PROVED `ensures` then failed at
            # run time.  The two arms mirror the verifier's
            # `_obligate_binding_triple` one-for-one, refined FIRST for the
            # same reason it is: the refinement's own predicate carries the
            # base's implicit range (`_refinement_guard_parts` conjoins it),
            # so the sign guards would be redundant under it, and running
            # them instead of it would check `>= 0` where the boundary
            # invariant is `> 0`.
            refined_payload: ast.TypeExpr | None = None
            if is_exn_throw and cell is not None:
                refined_payload = self._refined_exn_payload_type(cell, call)
                if refined_payload is not None:
                    instructions = self._emit_exn_payload_refine_guard(
                        instructions, refined_payload, cell, call, env)
            if refined_payload is None and (is_state_put or is_exn_throw):
                if base == "Nat" and self._narrows_into_nat(call.args[0]):
                    instructions = self._emit_nat_bind_guard(
                        instructions, at=call.args[0])
            # #754's registry contributes NOTHING on this route, and the
            # reason is a property of the route rather than an omission.
            # Only `get`, `put` and `throw` have a bare one — every other
            # operation is E217 at check, "must be called qualified" — and
            # all three take their formal from the CELL, which a declaration
            # cannot carry: `State` declares `put(T -> Unit)`, whose `T` is
            # the handler's instantiation.  So the formals here are the ones
            # `_effect_op_cells` supplies, above.  The claim that the
            # bare-routable set is exactly those three is asserted, not
            # remembered — see `test_guard_completeness`; a fourth op gaining
            # a bare route turns it red rather than passing unguarded.
            # throw uses WASM throw instruction, not call
            if call.name == "throw":
                instructions.append(f"throw {target_name}")
            else:
                instructions.append(f"call {target_name}")
            return instructions

        # Resolve call target — rewrite generic calls to mangled names
        call_target = call.name
        if call.name in self._generic_fn_info:
            resolved = self._resolve_generic_call(call)
            if resolved is None:
                # #1679: a generic call no instance answers is one in a
                # generic template's own body, which is compiled only
                # through its clones: the template is skipped here, as the
                # guard rail below skips a call to a name nothing registers.
                raise CodegenSkip(
                    call,
                    f"generic call {call.name!r} has no instance in the "
                    f"typed program",
                )
            call_target = resolved

        # Guard rail: reject calls to functions not defined in this module.
        # In practice the cross-module check upstream has already emitted
        # a diagnostic for genuine unknown-fn cases.  This path also fires
        # for prelude-mangled / forward-reference edge cases (e.g. the
        # #604 option_map mono-suffix mismatch) where the call target's
        # name was rewritten by mono but the rewritten name isn't yet
        # in `_known_fns`.
        if (self._known_fns
                and call_target not in self._known_fns
                # ctor-owner-exempt: membership test on a parsed call target,
                # not a layout read
                and call_target not in self._ctor_layouts):
            raise CodegenSkip(
                call,
                f"call target {call_target!r} not registered in this module",
            )

        # Regular function call
        instructions = []
        # #747 (CR #756): key the @Nat-parameter guard bitmap on the *resolved*
        # ``call_target``, not ``call.name``.  Monomorphisation registers the
        # specialised instance (`pick$Nat`) with its concrete @Nat flags
        # ``(True, …)`` while the generic decl (`pick`) keeps the erased
        # ``(False, …)``; looking up ``call.name`` would miss the guard on the
        # actual callee.  So `f<Nat>(@Int.0)` runtime-guards the narrowing
        # exactly like a concrete `f(@Nat -> …)` call.
        nat_params = self._fn_nat_params.get(call_target, ())
        # A formal the generic DECLARES with a type variable is guarded where
        # the checker instantiated it at `Nat` (`_guard_nat_instantiated_arg`):
        # the clone is named from the arguments' own types, so `pick(-3, 5)`
        # at `Nat` calls `pick$Int`, whose flags above are all False.
        forall_vars, generic_formals = self._generic_fn_info.get(
            call.name, ((), ()))
        for i, arg in enumerate(call.args):
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            if (i < len(nat_params) and nat_params[i]
                    and self._narrows_into_nat(arg)):
                arg_instrs = self._emit_nat_bind_guard(arg_instrs, at=arg)
            elif (i < len(generic_formals)
                    and _mentions_type_var(generic_formals[i],
                                           frozenset(forall_vars))):
                arg_instrs = self._guard_nat_instantiated_arg(arg, arg_instrs)
            instructions.extend(arg_instrs)

        # #517 — emit ``return_call $target`` for tail-position
        # calls whose WASM signature matches the current function's.
        # The analyzer in ``vera/tail_position.py`` populates
        # ``self._tail_call_sites`` with ids of syntactically tail-
        # position FnCalls; the type-match guard ensures WASM
        # ``return_call`` semantics are valid (the callee must
        # return the same type the caller returns).  Falls back to
        # plain ``call`` if either condition fails — never an error,
        # just a missed optimization.  See the post-process at the
        # end of ``_compile_fn`` in ``vera/codegen/functions.py``:
        # for allocating functions (#549) it PREPENDS a ``$gc_sp``
        # restore before each ``return_call`` so the shadow stack
        # stays bounded; for functions with a runtime postcondition
        # it REVERTS ``return_call`` → ``call`` so the post-check
        # runs.
        is_tail = tail or id(call) in self._tail_call_sites
        callee_ret_wt: str | None = None
        if is_tail:
            sig = self._fn_ret_types.get(call_target)
            callee_ret_wt = sig if isinstance(sig, str) else None
        if is_tail and callee_ret_wt == self._self_ret_wt:
            instructions.append(f"return_call ${symbol(call_target)}")
        else:
            instructions.append(f"call ${symbol(call_target)}")
        return instructions

    def _lower_intrinsic(
        self, intrinsic: Intrinsic, call: ast.FnCall, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Hand *call* to its intrinsic's emitter, in that emitter's
        argument convention (:class:`vera.builtins.Binding`)."""
        lowering = intrinsic.lowering
        emit = getattr(self, lowering.emitter)
        binding = lowering.binding
        if binding is Binding.ARGS:
            return emit(*call.args, env)
        if binding is Binding.ARGS_AT:
            return emit(*call.args, env, at=call)
        if binding is Binding.ARGS_SITE:
            return emit(*call.args, env, at=self._rendering_site(call))
        if binding is Binding.ARGS_CALL:
            return emit(*call.args, env, call)
        if binding is Binding.CALL:
            return emit(call, env)
        if binding is Binding.CALL_EXTRA:
            return emit(call, env, *lowering.extra)
        if binding is Binding.NONE:
            return emit()
        if binding is Binding.NAMED:
            return emit(call.name, *call.args, env)
        raise AssertionError(f"{call.name}: no argument convention {binding}")

    def _guard_effect_op_arg(
        self,
        arg: ast.Expr,
        arg_instrs: list[str],
        op_formals: tuple[str | None, ...],
        index: int,
    ) -> list[str]:
        """Wrap one effect-operation argument in the guard its FORMAL calls
        for (#754) — the operation-site twin of the `_fn_nat_params` bitmap
        a function call site reads.

        The same condition the function call site applies it under: an
        ``@Int`` value narrowing into a ``@Nat`` formal traps if it is
        negative.  It is gated on the VALUE — a value already at the
        formal's type needs no check — so a program whose arguments are
        provably in range pays dead instructions and never a trap.

        Returns *arg_instrs* unchanged for a formal the registry has nothing
        to say about: a type parameter, an ADT, a pair type, or an operation
        the registry does not know.
        """
        base = op_formals[index] if index < len(op_formals) else None
        if base == "Nat" and self._narrows_into_nat(arg):
            return self._emit_nat_bind_guard(arg_instrs, at=arg)
        return arg_instrs

    def _translate_qualified_call(
        self, call: ast.QualifiedCall, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a qualified call (e.g. IO.print) to host import call."""
        if (call.qualifier == "State" and call.name in ("get", "put")
                and (call.name in self._state_clause_ops
                     or call.name in self._effect_ops)):
            # The builtin State ops route through the UNQUALIFIED
            # dispatcher, which owns the clause-inline registry, the
            # #1203 argument guards, and the #865 Byte coercion — the
            # qualified spelling previously took a bare unguarded call:
            # `State.put(x)` inside a handled body skipped the clause's
            # `with` transform, stored a negative into a @Nat cell
            # silently, and emitted a Byte literal at i64 (round-4
            # review).  Delegation makes the two spellings identical by
            # construction — guarded on the op resolving, so a row that
            # registered no State cell still falls through to the legacy
            # path's loud unknown-func failure.
            #
            # `denotes_op=True` (#1284): the qualifier NAMED the effect, so
            # this call site is the operation whatever the program's
            # declarations are called.  Without it, the synthesized bare
            # node would be re-asked the ownership question and, in a
            # program that also declares `fn get`, silently dispatch to the
            # user's function — the round-5 hazard, which the pre-#1284
            # `_fn_sigs` registry guard sidestepped only by making the
            # registry incomplete (and so failing this spelling loudly at
            # the declared-row site: `unknown func: $vera.get`).
            return self._translate_call(
                ast.FnCall(name=call.name, args=call.args, span=call.span,
                           node_id=call.node_id),
                env, denotes_op=True,
            )
        if (call.qualifier == "Exn" and call.name == "throw"
                and "throw" in self._effect_ops):
            # `Exn.throw(x)` delegates for exactly the reason `State.put(x)`
            # does: the payload's #1212 Byte marking lives on the bare
            # dispatcher (#1269), and a qualified spelling that skipped it
            # emitted an `i64.const` under an i32 tag while the bare one
            # compiled.  Guarded on the op resolving, same as the State
            # twin — an unresolved `throw` falls through to the legacy path
            # below rather than synthesizing a bare call that would miss.
            # `denotes_op=True` for the same reason as the State twin.
            return self._translate_call(
                ast.FnCall(name=call.name, args=call.args, span=call.span,
                           node_id=call.node_id),
                env, denotes_op=True,
            )
        instructions: list[str] = []
        # #754: the op's DECLARED formals, from the registry built off the
        # same table the checker typed this call against.  `_effect_ops`
        # carries only a dispatch target, so before this an operation
        # argument was the one narrowing site with no formal to guard
        # against: `IO.sleep(@Int.0)` handed the host a negative on a
        # program the verifier had obligated.  The bare route reaches the
        # unqualified loop above, whose `get`/`put`/`throw` formals come
        # from the CELL (a property of the handler, not of the declaration);
        # every other op has no bare route at all (E217), so the two loops
        # together cover every reachable operation argument.
        op_formals = self._effect_op_params.get((call.qualifier, call.name), ())
        for i, arg in enumerate(call.args):
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            instructions.extend(
                self._guard_effect_op_arg(arg, arg_instrs, op_formals, i))
        # User-defined effect ops (e.g. Exn.throw, State.get/put) — delegate to
        # the effect_ops table, exactly as the unqualified _translate_call path does.
        # Guard: skip for host-import built-ins (Http, Inference, IO) whose op names
        # are handled by the branches below. Http.get and Http.post share the names
        # "get"/"post" with possible user effect ops; the qualifier check prevents
        # misrouting Http.get into _effect_ops when inside a handle[State<T>] body
        # where _effect_ops["get"] is populated.
        _host_import_qualifiers = {"Http", "Inference", "IO", "Random", "DB"}
        if call.qualifier not in _host_import_qualifiers and call.name in self._effect_ops:
            target_name, _is_void = self._effect_ops[call.name]
            if call.name == "throw":
                instructions.append(f"throw {target_name}")
            else:
                instructions.append(f"call {target_name}")
            return instructions
        # Http operations use prefixed names to avoid collision
        if call.qualifier == "Http":
            wasm_name = f"http_{call.name}"
            self._host_imports_used.add(wasm_name)
            self.needs_alloc = True
            instructions.append(f"call $vera.{wasm_name}")
        elif call.qualifier == "Inference":
            wasm_name = f"inference_{call.name}"
            self._host_imports_used.add(wasm_name)
            self.needs_alloc = True
            instructions.append(f"call $vera.{wasm_name}")
        elif call.qualifier == "DB":
            # #229 — DB.query / DB.execute → `call $vera.db_<op>`; both return
            # a Result ADT heap pointer, so $alloc is required.
            wasm_name = f"db_{call.name}"
            self._host_imports_used.add(wasm_name)
            self.needs_alloc = True
            instructions.append(f"call $vera.{wasm_name}")
        elif call.qualifier == "Random":
            # #465 — op names already begin with `random_`, so the
            # WASM import keeps the same name (`vera.random_int`,
            # `vera.random_float`, `vera.random_bool`).  None of the
            # Random ops allocate or return heap data, so $alloc is
            # not required.
            self._host_imports_used.add(call.name)
            instructions.append(f"call $vera.{call.name}")
        elif call.qualifier == "IO":
            self._host_imports_used.add(call.name)
            instructions.append(f"call $vera.{call.name}")
        else:
            instructions.append(f"call $vera.{call.name}")
        # IO.exit never returns — add unreachable to satisfy WASM validation
        if call.qualifier == "IO" and call.name == "exit":
            instructions.append("unreachable")
        return instructions

    def _resolve_generic_call(self, call: ast.FnCall) -> str | None:
        """The name of the clone a call to a generic function calls (#1679).

        The typed program derived the call's instantiation from the type
        arguments the checker inferred there and built the clone, so the
        call is lowered as a call of that clone, whose name is the one the
        typed instantiation gives it.  ``None`` for a call the typed program
        holds no instance for, which leaves the call on its bare name and
        reaches the guard rail's source-located [E602].
        """
        target = self._call_targets.get(call.node_id) if call.node_id else None
        return None if target is None else target.name

    def _call_target_mapping(
        self, call: ast.FnCall, forall_vars: tuple[str, ...],
    ) -> dict[str, str] | None:
        """Each of the generic callee's type variables, by the canonical name
        of the type *call* instantiates it at (#1679): the instance the typed
        program built for the call, whose clone the call calls, so a reading
        of the call's type is the clone's.  ``None`` for a call the typed
        program holds no instance for."""
        target = self._call_targets.get(call.node_id) if call.node_id else None
        if target is None:
            return None
        return dict(zip(forall_vars, target.args))
