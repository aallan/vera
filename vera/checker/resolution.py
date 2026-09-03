"""Type resolution mixin — AST TypeExpr to semantic Type conversion.

Provides _resolve_type, _resolve_named_type, _resolve_effect_row,
_resolve_effect_ref, _slot_type_name, _infer_type_args, and
_unify_for_inference methods extracted from TypeChecker.
"""

from __future__ import annotations

from vera import ast, naming
from vera.checker.registration import _RESERVED_TYPE_PREFIX_RE
from vera.types import (
    PRIMITIVES,
    REMOVED_ALIASES,
    AdtType,
    ConcreteEffectRow,
    EffectInstance,
    EffectRowType,
    FunctionType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    erases_to_unit,
    merge_inferred_types,
    pretty_type,
    substitute,
)


class ResolutionMixin:
    """Methods for resolving AST type expressions into semantic types."""

    # -----------------------------------------------------------------
    # Type resolution: AST TypeExpr -> semantic Type
    # -----------------------------------------------------------------

    def _resolve_type(self, te: ast.TypeExpr) -> Type:
        """Convert an AST TypeExpr into a resolved semantic Type."""
        if isinstance(te, ast.NamedType):
            return self._resolve_named_type(te)
        if isinstance(te, ast.FnType):
            params = tuple(self._resolve_type(p) for p in te.params)
            ret = self._resolve_type(te.return_type)
            eff = self._resolve_effect_row(te.effect)
            return FunctionType(params, ret, eff)
        if isinstance(te, ast.RefinementType):
            base = self._resolve_type(te.base_type)
            return RefinedType(base, te.predicate)
        return UnknownType()

    def _resolve_named_type(self, te: ast.NamedType) -> Type:
        """Resolve a named type (possibly parameterised)."""
        name = te.name

        # Type variable?
        if name in self.env.type_params:
            return self.env.type_params[name]

        # Primitive?
        if name in PRIMITIVES and not te.type_args:
            return PRIMITIVES[name]

        # Type alias?
        alias = self.env.type_aliases.get(name)
        if alias:
            # #660 — validate type-argument arity against the alias's
            # declared type parameters.  Pre-fix the `zip` below
            # silently truncated on length mismatch, producing a
            # substitution where some alias-local names stayed
            # unsubstituted; downstream codegen then leaked literal
            # alias-local names into mono suffixes (`option_map$Int_B`)
            # and the call site referenced a non-existent
            # function-table entry → `unknown table 0: table index
            # out of bounds` at runtime.  The arity mismatch is a
            # user error that the type checker is the right place
            # to surface.
            n_supplied = len(te.type_args) if te.type_args else 0
            n_expected = (
                len(alias.type_params) if alias.type_params else 0
            )
            if n_supplied != n_expected:
                params_phrase = (
                    f"`<{', '.join(alias.type_params)}>`"
                    if alias.type_params
                    else "no type parameters"
                )
                self._error(
                    te,
                    f"Type alias `{name}` expects {n_expected} type "
                    f"argument(s) but {n_supplied} supplied.",
                    rationale=(
                        f"`{name}` is declared with {params_phrase}.  "
                        f"Each use of the alias must supply exactly "
                        f"{n_expected} type argument(s) so the alias "
                        f"body can be fully instantiated.  Without "
                        f"complete arguments, downstream code "
                        f"generation cannot bind the alias-local "
                        f"type variables and may leak them into "
                        f"mangled symbol names — see #660."
                    ),
                    fix=(
                        f"Supply the missing type argument(s) at "
                        f"every use site of `{name}`, e.g. "
                        f"`{name}<Int" + (", Int" * max(0, n_expected - 1)) + ">`."
                        if n_supplied < n_expected
                        else f"Remove the extra type argument(s) "
                             f"so that `{name}` is given exactly "
                             f"{n_expected}."
                    ),
                    spec_ref='Chapter 2, Section 2.6.3 "Type Aliases with Refinements"',
                    error_code="E133",
                )
                return UnknownType()
            if te.type_args and alias.type_params:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                mapping = dict(zip(alias.type_params, args))
                return substitute(alias.resolved_type, mapping)
            return alias.resolved_type

        # ADT or parameterised built-in?
        adt = self.env.data_types.get(name)
        if adt is not None:
            if te.type_args and not (adt.type_params or ()):
                # #1372 fix round: a declared ADT applied to type arguments it
                # does not declare.  Refused HERE, at check, because a
                # declaration shadows every built-in reading of its name
                # (§8.4.1) — so under `private data Array { MkArr(Int) }` the
                # head of `Array<Array>` is that declaration, which takes no
                # arguments, and there is no container left for the arguments
                # to belong to.  Accepting it built an `AdtType("Array",
                # (…,))` that no constructor can produce, and every codegen
                # path that met it went wrong differently: the index emit
                # refused it, while `array_length` / `array_map` /
                # `array_fold` passed one word where the built-in pops a
                # (ptr, len) pair and shipped a `.wasm` that fails to load at
                # rc 0 with no diagnostic.  One rule at the resolution spine
                # closes all seven element shapes at once, and no codegen path
                # can reach any of them.
                #
                # Only the ZERO-arity direction is refused.  Under-application
                # of a parameterised ADT (`@Option` for `Option<T>`) is a
                # separate question with its own inference story, and widening
                # this to full arity equality would refuse programs that
                # compile correctly today.
                self._error(
                    te,
                    f"'{name}' is declared with no type parameters, so it "
                    f"cannot be applied to type arguments.",
                    rationale=(
                        f"A `data` declaration shadows every built-in "
                        f"reading of its name (Chapter 8, Section 8.4.1), so "
                        f"'{name}' here is this namespace's own declaration "
                        f"and not any built-in container of that name.  It "
                        f"declares no type parameters, so there is nothing "
                        f"for the type arguments to bind to."
                    ),
                    fix=(
                        f"Write '{name}' with no type arguments, or rename "
                        f"the declaration if you meant the built-in type of "
                        f"that name — a declaration in scope always wins."
                    ),
                    spec_ref='Chapter 8, Section 8.4.1 "Visibility Rules"',
                    error_code="E135",
                )
                # Report, then resolve EXACTLY as before.  The program is
                # already refused, so the type only has to stay consistent
                # with what `vera.naming._resolve_named` produces for the
                # same expression — and dropping the arguments here made the
                # checker and the renderer disagree about
                # `Option<Decimal<Int>>`, which is the very divergence class
                # this PR exists to close (`test_slot_naming_differential`
                # caught it).
                return AdtType(
                    name, tuple(self._resolve_type(a) for a in te.type_args))
            if te.type_args:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                return AdtType(name, args)
            return AdtType(name, ())

        # Decimal is a non-parameterised built-in opaque type
        if name == "Decimal":
            if te.type_args:
                self._error(
                    te, "Decimal does not accept type arguments.",
                    rationale=(
                        "`Decimal` is a non-parameterised, opaque "
                        "built-in type, so it takes no type "
                        "arguments.  Writing it with a `<...>` "
                        "argument list applies it as if it were a "
                        "generic type, which the type system does "
                        "not permit."
                    ),
                    fix="Write `Decimal` with no type arguments.",
                    spec_ref='Chapter 9, Section 9.7.2 "Decimal"',
                    error_code="E134",
                )
            return AdtType(name, ())

        # Array, Tuple, Map, Set (built-in parameterised types)
        if name in ("Array", "Tuple", "Map", "Set"):
            if te.type_args:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                # #945: an `Array<T>` whose element erases to a zero-size type
                # (`Unit`, or a `Future` transparently wrapping one) has no
                # valid WASM element layout — the element store/load would act
                # on a slot that holds no value, so the array compiles to
                # INVALID WASM (rejected by wasmtime at load) on a check-green +
                # verify-green program.  Reject at check: the element is
                # degenerate (`Array<Unit>` is isomorphic to a `Nat` count).
                # Same principle as the `@T`-at-zero-size family (#900/#939/#943).
                if (name == "Array" and len(args) == 1
                        and erases_to_unit(args[0])):
                    self._error(
                        te,
                        f"'Array' of a zero-size element type "
                        f"'{pretty_type(args[0])}' is not supported.",
                        rationale="A zero-size type (`Unit`, or a `Future` "
                        "wrapping one) occupies 0 bytes and has no runtime "
                        "value, so an array element of that type has no WASM "
                        "representation to store or load — the array would "
                        "compile to invalid WASM.",
                        fix="Use `Nat` for a count of zero-size items, or give "
                        "the element type a runtime value (e.g. `Array<Int>`, "
                        "or a boxed `Array<Option<Unit>>`).",
                        spec_ref='Chapter 2, Section 2.2 "Primitive Types"',
                        error_code="E135",
                    )
                # #1075: the Map/Set siblings of the Array gate above.  Map
                # keys/values and Set elements are raw host-serialized values
                # at a tag-determined width — exactly the Array-element
                # representation case, not the boxed-ADT-field case
                # (`Box<Unit>` / `Option<Unit>` fields live inside a heap
                # layout with a real representation and stay legal).  Without
                # this gate, `Map<String, Unit>` / `Set<Unit>` checked clean
                # and compiled exit-0 to INVALID WASM ("expected i32 but
                # nothing on stack" — the zero-size value pushes nothing where
                # the host import expects an i32 operand).
                if name == "Map" and len(args) == 2:
                    for role, arg in (("key", args[0]), ("value", args[1])):
                        if erases_to_unit(arg):
                            fix = (
                                "Use `Set<K>` if only key membership "
                                "matters, or give the value type a runtime "
                                "value (e.g. `Map<String, Int>`, or a boxed "
                                "`Map<String, Option<Unit>>`)."
                            ) if role == "value" else (
                                "Give the key type a runtime value "
                                "(e.g. `Map<String, ...>`)."
                            )
                            self._error(
                                te,
                                f"'Map' with a zero-size {role} type "
                                f"'{pretty_type(arg)}' is not supported.",
                                rationale="A zero-size type (`Unit`, or a "
                                "`Future` wrapping one) occupies 0 bytes and "
                                f"has no runtime value, so a Map {role} of "
                                "that type has no WASM representation to "
                                "store or load — the map operations would "
                                "compile to invalid WASM.",
                                fix=fix,
                                spec_ref='Chapter 2, Section 2.2 '
                                '"Primitive Types"',
                                error_code="E135",
                            )
                if (name == "Set" and len(args) == 1
                        and erases_to_unit(args[0])):
                    self._error(
                        te,
                        f"'Set' of a zero-size element type "
                        f"'{pretty_type(args[0])}' is not supported.",
                        rationale="A zero-size type (`Unit`, or a `Future` "
                        "wrapping one) occupies 0 bytes and has no runtime "
                        "value, so a Set element of that type has no WASM "
                        "representation to store or load — the set "
                        "operations would compile to invalid WASM.",
                        fix="Use `Bool` for a present/absent flag, or give "
                        "the element type a runtime value (e.g. `Set<Int>`).",
                        spec_ref='Chapter 2, Section 2.2 "Primitive Types"',
                        error_code="E135",
                    )
                return AdtType(name, args)
            return AdtType(name, ())

        # Removed alias? — produce a helpful "did you mean" error.
        canonical = REMOVED_ALIASES.get(name)
        if canonical is not None:
            if name not in self._reported_alias_errors:
                self._reported_alias_errors.add(name)
                self._error(
                    te,
                    f"'{name}' is not a type. Did you mean '{canonical}'?",
                    rationale=(f"'{name}' was removed; "
                               f"use '{canonical}' instead."),
                    fix=f"Replace '{name}' with '{canonical}'.",
                    spec_ref='Chapter 2, Section 2.2 "Primitive Types"',
                )
            return UnknownType()

        # Reserved prelude namespace? — the reference half of E154 (#1221).
        # Reaching here means nothing the checker knows carries this name, so
        # it would become an opaque head.  Codegen knows better: the prelude
        # injects its closure-parameter aliases under exactly these names, at
        # codegen and at the verifier's mono discovery but never at check, so
        # a `VeraOptionMapFn<Int, Bool>` parameter is one stack here and a
        # resolved function type there — codegen merges parameters this
        # binding table keeps apart and the export reads the wrong one.  The
        # declaration gate alone cannot close that: it stops a user DEFINING
        # a reserved name, not MENTIONING one the prelude defines.  Anchored
        # on the same regex the declaration gate uses, so the two halves of
        # the reservation cannot drift apart.
        if _RESERVED_TYPE_PREFIX_RE.match(name):
            if name not in self._reported_reserved_type_refs:
                self._reported_reserved_type_refs.add(name)
                self._error(
                    te,
                    f"Type '{name}' is reserved for the prelude.",
                    rationale=(
                        "Names beginning with 'Vera' followed by an "
                        "uppercase letter or digit are the prelude's "
                        "internal namespace — the declarations its "
                        "combinators resolve through, injected at code "
                        "generation and never visible to the type checker. "
                        "A user program that mentions one names a type this "
                        "checker cannot see and code generation can: the two "
                        "then partition a function's parameters differently, "
                        "and the compiled export reads a parameter the "
                        "binding table assigns to a different slot."
                    ),
                    fix=(
                        "Write out the type this name stands for — a "
                        "function type is spelled `fn(A -> B) "
                        "effects(pure)` — or declare your own alias for it "
                        "under a name outside the reserved namespace: any "
                        "name that does not start with 'Vera' followed by "
                        "an uppercase letter or digit. Stripping the prefix "
                        "is not a fix by itself; the reserved name is not a "
                        "declaration this program can reach under any "
                        "spelling."
                    ),
                    spec_ref='Chapter 8, Section 8.4.1 "Visibility Rules"',
                    error_code="E154",
                )
            return UnknownType()

        # Unknown — might be a type from an unresolved import
        return AdtType(name, tuple(
            self._resolve_type(a) for a in te.type_args
        ) if te.type_args else ())

    def _resolve_effect_row(self, er: ast.EffectRow) -> EffectRowType:
        """Convert an AST EffectRow into a semantic EffectRowType."""
        return self._resolve_effect_row_ordered(er)[0]

    def _resolve_effect_row_ordered(
        self, er: ast.EffectRow,
    ) -> tuple[EffectRowType, tuple[EffectInstance, ...]]:
        """Resolve an AST EffectRow to its row type AND its SOURCE order.

        One derivation, two views (#1215).  The row type carries a
        ``frozenset`` — the shape subeffect containment wants — which loses
        the declaration order a bare op name needs to resolve deterministically
        when two effects in the row declare it.  The second element is that
        order: the ``ast.EffectSet``'s own sequence, minus the row variable,
        with each instance resolved exactly once here so the two views can
        never describe different effects.
        """
        if isinstance(er, ast.PureEffect):
            return PureEffectRow(), ()
        if isinstance(er, ast.EffectSet):
            instances = []
            row_var = None
            for ref in er.effects:
                if isinstance(ref, ast.EffectRef):
                    # Check if it's a type variable (effect polymorphism)
                    if ref.name in self.env.type_params:
                        row_var = ref.name
                        continue
                    args = tuple(
                        self._resolve_type(a) for a in ref.type_args
                    ) if ref.type_args else ()
                    instances.append(EffectInstance(ref.name, args))
                elif isinstance(ref, ast.QualifiedEffectRef):
                    args = tuple(
                        self._resolve_type(a) for a in ref.type_args
                    ) if ref.type_args else ()
                    instances.append(
                        EffectInstance(f"{ref.module}.{ref.name}", args))
            return (ConcreteEffectRow(frozenset(instances), row_var),
                    tuple(instances))
        return PureEffectRow(), ()

    def _resolve_effect_ref(self, ref: ast.EffectRefNode) -> EffectInstance | None:
        """Resolve a single effect reference."""
        if isinstance(ref, ast.EffectRef):
            args = tuple(
                self._resolve_type(a) for a in ref.type_args
            ) if ref.type_args else ()
            return EffectInstance(ref.name, args)
        if isinstance(ref, ast.QualifiedEffectRef):
            args = tuple(
                self._resolve_type(a) for a in ref.type_args
            ) if ref.type_args else ()
            return EffectInstance(f"{ref.module}.{ref.name}", args)
        return None

    # -----------------------------------------------------------------
    # Canonical type name for slot references
    # -----------------------------------------------------------------

    def _naming_env(self) -> naming.AliasEnv:
        """The naming environment for the checker's CURRENT state.

        Rebuilt per call rather than cached: ``env.type_aliases`` grows
        through registration and ``env.type_params`` changes on entering and
        leaving every ``forall`` scope, so a cached env would render a
        ``forall<T>`` parameter against the wrong shadowing set.  The build is
        a copy of the module's alias table (user aliases only — no built-in
        seeds the table), which is small enough that the full suite shows no
        measurable cost.
        """
        return naming.alias_env_from_environment(self.env)

    def _check_slot_name_args(self, te: ast.TypeExpr) -> None:
        """Resolve a slot name's type ARGUMENTS for their diagnostics.

        The naming composition that used to live in the checker got E133 /
        E134 / E135 / removed-alias reporting for free, because it rendered
        each argument by RESOLVING it — and at a slot REFERENCE
        (``@Option<Box>.0`` for a parameterised ``Box``) that incidental
        report is the only one there is.  :mod:`vera.naming` is total and
        silent by design, so delegating the rendering to it would drop those
        diagnostics; this walk keeps them, following exactly the traversal
        the old composition took (refinement bases unwrapped, a function type
        naming nothing).  It is a reporting pass only — the name itself comes
        from the module.
        """
        while isinstance(te, ast.RefinementType):
            te = te.base_type
        if isinstance(te, ast.NamedType) and te.type_args:
            for arg in te.type_args:
                self._resolve_type(arg)

    def _slot_type_name(self, type_name: str,
                        type_args: tuple[ast.TypeExpr, ...] | None) -> str:
        """Form the canonical type name for slot reference matching.

        Delegates to :func:`vera.naming.slot_name` (#1208): the head is
        syntactic and the arguments resolve, which is what the binding side
        does too, so a reference and its binding cannot be keyed differently.
        """
        te = ast.NamedType(name=type_name, type_args=type_args)
        self._check_slot_name_args(te)
        return naming.slot_name(te, self._naming_env())

    def _slot_ref_key(self, ref: ast.SlotRef) -> str:
        """Binding-table key for a ``SlotRef``, keyed as ``bind()`` keys it.

        The #309 / #1160 provenance resolvers in :mod:`vera.checker.sql` need
        to look bindings up, and must do it with the CHECKER's renderer, not
        the syntactic one in :mod:`vera.slots`.  Binding keys resolve their
        type arguments (``_type_expr_to_slot_name`` →
        :func:`vera.naming.slot_name`: a syntactic head over resolved
        arguments, since #1208 routed both sides through the one renderer),
        so a syntactic render of ``@Array<Option<Txt>>``
        where ``type Txt = String`` yields ``Array<Option<Txt>>`` and matches
        the ``Array<Option<String>>`` key not at all.  A miss reads as "not
        statically known", so the check would silently do nothing — the exact
        failure #1160 fixed one level up.
        """
        return self._slot_type_name(ref.type_name, ref.type_args)

    # -----------------------------------------------------------------
    # Type inference helpers
    # -----------------------------------------------------------------

    def _infer_type_args(self, forall_vars: tuple[str, ...],
                         param_types: tuple[Type, ...],
                         arg_types: list[Type | None],
                         conflicts: set[str] | None = None,
                         ) -> dict[str, Type]:
        """Infer type variable bindings by matching args against params.

        When a forall var is bound by several arguments whose types share a
        parameterised head but each pin a *different* type parameter (a sparse
        multi-parameter ADT, `data Res<A, B> { MkOk(A), MkErr(B) }` reached via
        `eq2(MkErr(5), MkOk("x"))`), the per-argument bindings are MERGED
        position-wise so the fully-determined `Res<String, Int>` is recovered
        rather than the first-argument-wins `Res<?, Int>` (#898).  A genuine
        per-position CONFLICT (two arguments fixing the same parameter to
        different concrete types) records the var in *conflicts* so the caller
        emits a clear conflict diagnostic instead of a wrong-type E202.
        """
        mapping: dict[str, Type] = {}
        forall_set = set(forall_vars)
        for param_ty, arg_ty in zip(param_types, arg_types):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            self._unify_for_inference(param_ty, arg_ty, mapping, forall_set,
                                      conflicts)
        return mapping

    def _unify_for_inference(self, pattern: Type, concrete: Type,
                             mapping: dict[str, Type],
                             forall_vars: set[str] | None = None,
                             conflicts: set[str] | None = None,
                             ) -> None:
        """Simple unification for type argument inference."""
        # Skip when the concrete type has TypeVars matching the callee's
        # own forall vars (e.g. map_new() returns Map<K, V> where K, V
        # are the callee's forall vars — not yet resolved from args).
        # Other TypeVars (e.g. E$6 from constructor inference, or U from
        # an enclosing forall scope) are fine to unify with.
        if (forall_vars
                and isinstance(concrete, AdtType)
                and concrete.type_args
                and any(isinstance(a, TypeVar) and a.name in forall_vars
                        for a in concrete.type_args)):
            return
        if isinstance(pattern, TypeVar):
            # Prefer concrete resolutions over fresh TypeVars (those named
            # with '$', e.g. T$1 from _fresh_typevar).
            #
            # Fresh TypeVars are unresolved placeholders produced when a
            # nullary constructor like None or Ok(x) can't fill all type
            # parameters from its own args.  Recording A→T$1 from None's
            # inferred Option<T$1> is fine as a first approximation, but must
            # be overwritten when a later argument provides a concrete answer
            # (e.g. the fn(@Int->@Int) callback in option_map(None, ...)).
            #
            # Overwrite iff the existing mapping is a fresh TypeVar AND the
            # new concrete type is not itself a fresh TypeVar (#293).
            # Forall-to-forall mappings (e.g. T→U when wrap<U> calls identity,
            # where U has no '$') are recorded and kept as-is.
            existing = mapping.get(pattern.name)
            is_fresh = isinstance(concrete, TypeVar) and '$' in concrete.name
            if existing is None:
                mapping[pattern.name] = concrete
            elif (isinstance(existing, TypeVar)
                  and '$' in existing.name
                  and not is_fresh):
                # Overwrite a tentative fresh-TypeVar mapping with a concrete
                # (or forall-var) resolution.
                mapping[pattern.name] = concrete
            elif (isinstance(existing, TypeVar)
                  and not isinstance(concrete, TypeVar)):
                # #970 (dual): the existing binding is a bare type variable that
                # leaked UNRESOLVED from a nested generic call — e.g., given a
                # user-defined `forall<T> fn nothing(@Unit -> @Option<T>)`, the
                # call `option_unwrap_or(nothing(()), 11)`, where `nothing(())`
                # returns `@Option<T>`, binds `option_unwrap_or`'s param to
                # `nothing`'s escaped `T` before the concrete `11` arrives.  A
                # later argument that pins a CONCRETE type resolves it, exactly
                # as a fresh `$` placeholder would.  (Pre-rename a name
                # coincidence between the leaked var and the built-in's internal
                # var made the skip-guard fire and hide this; the #970 registry
                # rename removed the coincidence, so the concrete-wins rule must
                # be explicit — not a weakening, the same downstream subtype
                # check runs unchanged.)
                mapping[pattern.name] = concrete
            else:
                # #898: both the existing binding and the new one are (partly)
                # concrete.  Merge them position-wise so two sparse constructor
                # arguments each pinning a different type parameter combine into
                # one fully-determined type (`Res<?, Int>` ⊔ `Res<String, ?>` =
                # `Res<String, Int>`); a genuine per-position conflict is
                # recorded so the caller can report it clearly.
                merged, conflict = merge_inferred_types(existing, concrete)
                if conflict and conflicts is not None:
                    conflicts.add(pattern.name)
                mapping[pattern.name] = merged
            return

        if isinstance(pattern, AdtType) and isinstance(concrete, AdtType):
            if pattern.name == concrete.name:
                for p_arg, c_arg in zip(pattern.type_args, concrete.type_args):
                    self._unify_for_inference(
                        p_arg, c_arg, mapping, forall_vars, conflicts)

        if isinstance(pattern, FunctionType) and isinstance(concrete, FunctionType):
            for p_param, c_param in zip(pattern.params, concrete.params):
                self._unify_for_inference(
                    p_param, c_param, mapping, forall_vars, conflicts)
            self._unify_for_inference(
                pattern.return_type, concrete.return_type,
                mapping, forall_vars, conflicts)
