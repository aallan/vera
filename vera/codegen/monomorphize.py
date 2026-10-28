"""Mixin for generic function monomorphization (Pass 1.5).

Emits the clones the typed program built (#1679, :mod:`vera.typed`): the
instance set is derived once, from the instantiations the checker inferred,
and each clone is built there once, so code generation and the verifier read
one set.  What stays here is lowering: the order clones are emitted in, and
the hoisting of each clone's ``where`` helpers into standalone functions
(#904), with a generic helper's own instances taken from the typed program
under its parent clone (#1002).  An instance's ability constraints are
judged at check, at the call that chooses its type arguments
(:func:`vera.typed.judge`, E613), so every instance here satisfies them.
"""

from __future__ import annotations

from vera import ast
from vera.monomorphize import (
    collect_nested_generic_decls,
    declared_return_clone_key,
    where_helper_name,
)
from vera.skip import DERIVED_HELPER_DEPTH_CAP
from vera.slots import type_expr_slot_name

# Types that satisfy the built-in abilities.  #773: `Eq` is structural, so a
# field of ANY of these — String included (compared by content) — is
# Eq-derivable; the scalar-only carve-out that excluded String is gone.
_EQ_TYPES: frozenset[str] = frozenset({
    "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit",
})
def _simple_return_type_name(te: ast.TypeExpr | None) -> str | None:
    """The refinement-unwrapped base type name of a return TypeExpr.

    Thin wrapper over the shared :func:`vera.monomorphize.declared_return_clone_key`.
    ``None`` for shapes with no simple named base (e.g. a bare ``FnType``).
    """
    return declared_return_clone_key(te)


class MonomorphizationMixin:
    """Methods for monomorphizing generic functions."""

    def _monomorphize(
        self, program: ast.Program,
    ) -> list[ast.FnDecl]:
        """The clones the typed program built for *program*'s generics, in
        emission order, each clone's ``where`` helpers hoisted.

        The order is a worklist's over the instances: the instances a body
        that is not generic calls, per generic in declaration order and by
        argument, then transitively what each clone calls, then what each
        hoisted helper calls (#1223), the order the clones were emitted in
        when code generation derived them itself."""
        # Identify generic function declarations.  #990: a ``forall<T>``
        # where-helper under an all-NON-generic ancestor chain is a mono base
        # too.  #774: an imported PUBLIC generic joins under its link name,
        # with #998 the module it was declared in.
        generic_decls: dict[str, ast.FnDecl] = {}
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                if decl.forall_vars:
                    generic_decls[decl.name] = decl
                else:
                    collect_nested_generic_decls(decl, generic_decls)
        imported_generic_decls = getattr(
            self, "_imported_generic_decls", {},
        )
        imported_origins = getattr(self, "_imported_generic_origins", {})
        self._imported_generic_base_origins: dict[str, tuple[str, ...]] = {}
        for gname, gdecl in imported_generic_decls.items():
            if gname not in generic_decls:
                generic_decls[gname] = gdecl
                if gname in imported_origins:
                    self._imported_generic_base_origins[gname] = (
                        imported_origins[gname]
                    )

        if not generic_decls:
            return []

        # Record of every (generic name, type arguments) emitted, read by the
        # instruments that hold the emitted set to the typed program's.
        self._emitted_instances: set[tuple[str, tuple[str, ...]]] = set()
        self._hoisted_helper_scopes: dict[str, dict[str, str]] = {}
        typed = self._typed

        instances: dict[str, set[tuple[str, ...]]] = {
            name: set() for name in generic_decls
        }
        for inst in typed.seeds:
            if inst.parent is None and inst.key in instances:
                instances[inst.key].add(inst.args)

        seen: set[tuple[str, tuple[str, ...]]] = set()
        # Sorted per name, so the emission order is deterministic (PR #767).
        worklist: list[tuple[str, tuple[str, ...]]] = [
            (fn_name, ct)
            for fn_name, type_arg_set in instances.items()
            for ct in sorted(type_arg_set)
        ]
        mono_decls = self._drain_generic_worklist(
            worklist, seen, generic_decls,
        )

        # Store generic fn info for the call sites in wasm.py, which name a
        # generic call's clone from the typed program (`_resolve_generic_call`)
        # and read a generic's formals for the argument guards.
        self._generic_fn_info: dict[
            str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]
        ] = {}
        for name, decl in generic_decls.items():
            assert decl.forall_vars is not None  # noqa: S101
            self._generic_fn_info[name] = (decl.forall_vars, decl.params)

        # #904/#1223: hoist every clone's ``where``-helpers into standalone
        # mono decls, a FIXPOINT with the top-level worklist: a hoisted
        # helper's clone can call a top-level generic at a type nothing else
        # instantiates, and that clone's own helpers are hoisted in turn.
        emitted: list[ast.FnDecl] = []
        round_decls = mono_decls
        while round_decls:
            hoisted = self._hoist_clone_where_fns(round_decls)
            emitted.extend(hoisted)
            reseed: list[tuple[str, tuple[str, ...]]] = []
            found: dict[str, set[tuple[str, ...]]] = {
                name: set() for name in generic_decls
            }
            for body in hoisted:
                inst = typed.instance_named(body.name)
                for callee in (inst.calls.values() if inst else ()):
                    if callee.parent is None and callee.key in found:
                        found[callee.key].add(callee.args)
            for t_name, t_types in found.items():
                for t_ct in sorted(t_types):  # deterministic (see the seed)
                    if (t_name, t_ct) not in seen:
                        reseed.append((t_name, t_ct))
            round_decls = self._drain_generic_worklist(
                reseed, seen, generic_decls,
            ) if reseed else []
        return emitted

    def _drain_generic_worklist(
        self,
        worklist: list[tuple[str, tuple[str, ...]]],
        seen: set[tuple[str, tuple[str, ...]]],
        generic_decls: dict[str, ast.FnDecl],
    ) -> list[ast.FnDecl]:
        """The clones of *worklist*'s instances, then of what each calls,
        transitively, each taken from the typed program.

        ``seen`` is the caller's, so a second drain (#1223's re-seed from
        hoisted helper bodies) neither re-emits nor loses anything."""
        typed = self._typed
        produced: list[ast.FnDecl] = []
        while worklist:
            fn_name, concrete_types = worklist.pop()
            key = (fn_name, concrete_types)
            if key in seen:
                continue
            seen.add(key)
            if fn_name not in generic_decls:
                continue
            inst = typed.instance(fn_name, concrete_types)
            if inst is None or inst.clone is None:
                continue
            mono_fn = inst.clone
            produced.append(mono_fn)
            self._record_clone_origin(fn_name, mono_fn.name)
            self._clone_type_args[mono_fn.name] = concrete_types
            # #1002: this clone's concrete-FREE chain base, which keys a
            # generic-under-generic helper's `_emitted_instances` entry.
            self._clone_base_chain[mono_fn.name] = fn_name
            self._emitted_instances.add((fn_name, concrete_types))
            transitive: dict[str, set[tuple[str, ...]]] = {
                name: set() for name in generic_decls
            }
            for callee in inst.calls.values():
                if callee.parent is None and callee.key in transitive:
                    transitive[callee.key].add(callee.args)
            for t_name, t_types in transitive.items():
                for t_ct in sorted(t_types):  # deterministic order (see seed)
                    if (t_name, t_ct) not in seen:
                        worklist.append((t_name, t_ct))
        return produced

    def _hoist_clone_where_fns(
        self,
        mono_decls: list[ast.FnDecl],
    ) -> list[ast.FnDecl]:
        """Hoist every clone's ``where``-helpers into standalone mono decls (#904).

        For each monomorphized clone that carries a ``where`` block, rename each
        helper to a clone-aligned name (``<clone>$where$<helper>`` — ``$`` can't
        appear in a source identifier and ``where`` is a reserved keyword, so
        the name can collide with neither a real user function nor another mono
        clone), rewrite the clone body's (and each sibling helper's) bare call
        to that helper to the renamed target, strip ``where_fns`` off the clone,
        and append the renamed helpers as ordinary mono decls.

        Cloning per-instantiation (rather than emitting each helper once) is
        uniformly correct for both helper shapes:

        - a T-INDEPENDENT helper (``fn helper(@Int -> @Int)``) produces
          identical bodies under distinct names — redundant but sound;
        - a T-DEPENDENT helper (``fn id(@T -> @T)``) reads the enclosing ``@T``,
          so its substituted body genuinely differs per instantiation (an i64
          mover for ``@Int``, an i32 mover for ``@Bool``) and MUST be
          per-instantiation — a single shared emission would be type-wrong.

        Nested ``where`` blocks (a helper with its own helpers) are hoisted
        recursively under the same clone-qualified prefix.

        #1002: a ``where``-helper that is ITSELF generic (a ``forall`` under a
        generic ancestor) is NOT flattened here — its subtree depends on its
        own type variable and must be hoisted only after that variable is bound.
        ``_hoist_where_fns_under`` keeps such a helper's subtree intact (its
        bare name and calls to visible outer helpers still redirected), and this
        loop then monomorphizes it per its concrete call sites, re-queuing each
        resulting clone so its own where-tree is hoisted in turn (fixpoint over
        arbitrary generic-under-generic depth).
        """
        result: list[ast.FnDecl] = []
        # Worklist so a nested generic's freshly-emitted clone (which may carry
        # its own where-tree, generic or not) re-enters hoisting.
        pending: list[ast.FnDecl] = list(mono_decls)
        while pending:
            decl = pending.pop(0)
            if not decl.where_fns:
                result.append(decl)
                continue
            hoisted: list[ast.FnDecl] = []
            rewritten = self._hoist_where_fns_under(
                decl, decl.name, hoisted,
            )
            result.append(rewritten)
            # #1511: and it spells the parent clone's type arguments.
            parent_args = self._clone_type_args.get(decl.name, ())
            for h in hoisted:
                self._clone_type_args[h.name] = parent_args
            # #998: a hoisted helper's body is the same module's code as the
            # clone it was hoisted from — it needs the same span tables.
            origin = self._mono_clone_origins.get(decl.name)
            if origin is not None:
                for h in hoisted:
                    self._mono_clone_origins[h.name] = origin
            generic_helpers = [h for h in hoisted if h.forall_vars]
            result.extend(h for h in hoisted if not h.forall_vars)
            if generic_helpers:
                # #1002: still-generic (generic-under-generic).  Instantiate
                # per their calls in the just-hoisted parent + siblings; the
                # concrete clones re-enter `pending`.
                self._instantiate_hoisted_generics(
                    generic_helpers, decl.name, pending)
        return result

    def _instantiate_hoisted_generics(
        self,
        gens: list[ast.FnDecl],
        parent_clone_name: str,
        pending: list[ast.FnDecl],
    ) -> None:
        """Emit one clone's still-generic hoisted ``where``-helpers at the
        instances the typed program built under that clone (#1002).

        Each of *gens* is a ``forall`` helper hoisted under a generic
        ancestor's clone and renamed to its per-clone name
        (``parent$where$outer$Int$where$ginner``).  Each is registered as a
        generic base so a call to it names its clone (``…$ginner$Int``), and
        each instance's clone takes the calls redirect the hoist gave the
        helper, is recorded under the concrete-FREE chain key, and is queued
        so its own where-tree is hoisted."""
        from dataclasses import replace as _replace

        from vera.monomorphize import _qualify_generic_subtree_calls

        typed = self._typed
        parent = typed.instance_named(parent_clone_name)
        origin = self._mono_clone_origins.get(parent_clone_name)
        base_chain = self._clone_base_chain.get(
            parent_clone_name, parent_clone_name,
        )
        for gen in gens:
            assert gen.forall_vars is not None  # noqa: S101
            # Register for Pass 2 generic-call resolution under the emission name.
            self._generic_fn_info[gen.name] = (gen.forall_vars, gen.params)
            helper_bare = gen.name[len(parent_clone_name) + len("$where$"):]
            chain_key = f"{base_chain}$where${helper_bare}"
            if parent is None:
                continue
            scope = self._hoisted_helper_scopes.get(gen.name, {})
            # The helper's instances under this clone: its link name is the
            # parent generic's key and the same helper chain (#1002).
            helper_key = f"{parent.key}$where${helper_bare}"
            found = sorted(
                (inst for inst in typed.instances
                 if inst.parent is parent and inst.key == helper_key
                 and inst.clone is not None),
                key=lambda inst: inst.args)
            for inst in found:
                assert inst.clone is not None  # noqa: S101
                clone = _replace(
                    _qualify_generic_subtree_calls(inst.clone, scope),
                    name=inst.name)
                if origin is not None:
                    self._mono_clone_origins[clone.name] = origin
                self._clone_type_args[clone.name] = (
                    *self._clone_type_args.get(parent_clone_name, ()),
                    *inst.args,
                )
                # Chain the deeper base so a generic sub-helper of `gen`
                # keys concrete-free too.
                self._clone_base_chain[clone.name] = chain_key
                self._emitted_instances.add((chain_key, inst.args))
                pending.append(clone)

    def _hoist_where_fns_under(
        self,
        fn: ast.FnDecl,
        prefix: str,
        hoisted: list[ast.FnDecl],
        scope: dict[str, str] | None = None,
    ) -> ast.FnDecl:
        """Hoist ``fn``'s ``where``-helpers under ``prefix``, recursively.

        Returns ``fn`` with its ``where_fns`` stripped and every bare call to a
        lexically-visible helper redirected.  Each helper is appended to
        ``hoisted`` under ``<prefix>$where$<helper>``, with its OWN nested
        helpers hoisted under that new prefix.

        *scope* is the ``{helper name: renamed name}`` map of every helper
        visible from ENCLOSING ``where`` scopes, threaded down the recursion so
        full lexical resolution holds (#1012) — the exact mirror of the
        non-generic hoister's ``scope`` parameter
        (``_hoist_nongeneric_where_fns_under``): a helper body resolves a bare
        call to the NEAREST same-named helper in the enclosing tree — its own
        children first, then siblings, then any ancestor's (a grandchild
        calling an "aunt", a sibling of its parent, is redirected too), and an
        inner helper shadows an outer same-named one for its subtree.  A name
        absent from the combined scope is a top-level / builtin call and stays
        bare.  Pre-#1012 the recursion dropped the enclosing map, so a
        grandchild's aunt call stayed bare and WAT assembly failed with an
        unknown-func internal error on a check-green program.
        """
        from dataclasses import replace as _replace

        from vera.monomorphize import _qualify_generic_subtree_calls

        where_fns = fn.where_fns or ()
        rename = {
            wfn.name: f"{prefix}$where${where_helper_name(wfn.name)}"
            for wfn in where_fns
        }
        # This level's names shadow same-named ancestors for this subtree.
        combined = {**(scope or {}), **rename}
        for wfn in where_fns:
            if wfn.forall_vars:
                # #1002: a generic helper's subtree is per-INSTANTIATION
                # territory — it depends on the helper's own type variable, so
                # it must be hoisted only AFTER the helper is monomorphized (the
                # caller instantiates it and re-queues each clone).  Keep its
                # subtree intact; only redirect its calls to lexically-visible
                # OUTER helpers (shadow-aware, so a re-declared inner name still
                # binds to the inner helper), then rename it to its per-clone
                # emission name.
                redirected = _qualify_generic_subtree_calls(wfn, combined)
                hoisted.append(
                    _replace(redirected, name=rename[wfn.name]),
                )
                # #1679: each of its instances is a clone the typed program
                # built from the helper as it stood in the parent's clone,
                # whose calls take the same redirect when it is hoisted.
                self._hoisted_helper_scopes[rename[wfn.name]] = combined
                continue
            # The child body sees `combined` (ancestors + this level, so
            # sibling and aunt calls redirect); its own nested helpers extend
            # that scope inside the recursion, which also applies the final
            # rewrite — no second pass here.
            child = self._hoist_where_fns_under(
                wfn, rename[wfn.name], hoisted, combined,
            )
            hoisted.append(_replace(child, name=rename[wfn.name]))
        # Strip the parent's where block and redirect its calls with the full
        # lexical scope.
        stripped = _replace(fn, where_fns=None)
        rewritten = self._rewrite_call_names(stripped, combined)
        assert isinstance(rewritten, ast.FnDecl)  # noqa: S101
        return rewritten

    def _record_clone_origin(self, base_name: str, clone_name: str) -> None:
        """Record *clone_name*'s origin module when its base is an imported
        generic (#998).

        Local bases (including #990 nested helpers) are absent from
        ``_imported_generic_base_origins`` and record nothing — their clones
        keep reading the main-file span tables, which is where their template
        spans live.
        """
        origin = self._imported_generic_base_origins.get(base_name)
        if origin is not None:
            self._mono_clone_origins[clone_name] = origin

    def _rewrite_call_names(
        self, node: object, rename: dict[str, str],
    ) -> object:
        # Delegates to the shared standalone walker (vera/monomorphize.py) so
        # the #1014 qualification transform and this mixin can never drift.
        from vera.monomorphize import rewrite_fn_call_names

        return rewrite_fn_call_names(node, rename)

    def _adt_satisfies_eq(
        self, type_name: str, _seen: frozenset[str] = frozenset(),
    ) -> bool:
        """Check if an ADT type satisfies Eq via *structural* auto-derivation.

        An ADT satisfies Eq iff every constructor field's type does (§9.8).  A
        field is Eq iff it is an Eq primitive (Int/Nat/Bool/Float64/Byte/Unit
        **or String**, which compares by content) or a nested ADT that itself
        satisfies Eq (checked recursively).  A field with no Eq semantics —
        Array, Map, a host handle, a function — is *not* derivable and the ADT
        is rejected (E613).  Simple enums (all constructors zero-field) always
        satisfy Eq.

        This must agree exactly with codegen's structural-Eq generator
        (`OperatorsMixin._generate_adt_eq_fn`): a program the gate accepts must
        never hit the generator's loud "no Eq comparison" invariant, and vice
        versa — the checker↔codegen lockstep #732 relies on (differential-
        tested by ``test_structural_eq_gate_matches_codegen``).

        `_adt_layouts` is keyed by the bare ADT name (`Box`), so a
        parameterized name (`Box<String>`) is split into base + args; a
        TYPE-PARAMETER field's Eq-ness is its concrete type ARGUMENT's (per
        `_ctor_adt_tp_indices`), while a concrete field's is its declared type's
        (per `field_types`).  #773 lifted this from the old scalar-WASM-rep
        basis (which false-rejected String fields and false-accepted nested-ADT
        / Map pointer fields).
        """
        from vera.monomorphize import Monomorphizer, substitute_type_param_names

        parsed = Monomorphizer._parse_type_name(type_name)
        base = parsed.name
        args = [
            Monomorphizer._format_type_name(a)
            for a in (parsed.type_args or ())
            if isinstance(a, ast.NamedType)
        ]
        layouts = self._adt_layouts.get(base)
        if layouts is None:
            return False
        if base == "Tuple":
            # Tuple's registered layout is a variadic ZERO-FIELD placeholder
            # (real layouts are recomputed per construction site), not a
            # fieldless enum — accepting it here would generate a tag-only
            # equality that compares no components and returns always-true
            # (PR #870 review, Critical).  Reject until tuple structural Eq
            # carries real per-instantiation component metadata.
            return False
        if type_name in _seen:        # recursive ADT (e.g. List<T>) — break cycle
            return True
        # #933: bound POLYMORPHIC recursion.  A non-uniform ADT
        # (`Box<T>` field `Box<Box<T>>`) never repeats a `type_name`, so the
        # `_seen` cycle-break above never fires and each descent resolves a
        # fresh, strictly-deeper field type (`Box<Box<Int>>`,
        # `Box<Box<Box<Int>>>`, …) whose generic NESTING climbs one level per
        # step — this predicate recurs into a raw `RecursionError` on a
        # check-green program.  Past the cap, report the type NOT derivable so
        # the caller emits a clean E613 (the same degradation a structurally
        # non-Eq field already gets).  Uniform shapes recur at CONSTANT nesting
        # depth and never approach this bound; it stays in lockstep with
        # codegen's `$eq_<type>` generator, bounded at the SAME cap.
        if type_name.count("<") >= DERIVED_HELPER_DEPTH_CAP:
            return False
        seen = _seen | {type_name}
        # Param-NAME → concrete-arg mapping, for params nested inside a
        # parameterized declared field type (`List<T>` under `List<Int>`) —
        # the same substitution codegen's generator applies, keeping the two
        # in lockstep.
        tp_names = self._adt_tp_param_names.get(base, ())
        tp_mapping = dict(zip(tp_names, args))
        owned_tp = self._adt_ctor_tp_indices.get(base, {})
        for ctor_name, layout in layouts.items():
            # #1436: the OWNING ADT's indices.  `layouts` came from
            # `_adt_layouts[base]`, so the owner is in hand here and the flat
            # table — where another namespace's declaration of the same
            # constructor name may have won the slot — has no business
            # answering.  The gate must agree exactly with codegen's
            # structural-Eq generator, and the generator reads the layout of
            # THIS ADT.
            tp_indices = owned_tp.get(ctor_name)
            for i, (_offset, wasm_type) in enumerate(layout.field_offsets):
                tp_i = (
                    tp_indices[i]
                    if tp_indices is not None and i < len(tp_indices)
                    else None
                )
                if tp_i is not None:
                    # Type-parameter field — its Eq-ness is the concrete type
                    # argument's.
                    if tp_i >= len(args):
                        # No concrete type argument for this parameter (the
                        # #772 residue: a `ConstructorCall` monomorphizes to the
                        # bare ADT name `Box`, dropping `<String>`).  Codegen's
                        # structural generator cannot resolve the field's type
                        # either, so — to stay in lockstep — the gate reports it
                        # NOT derivable (a clean E613) rather than accepting it
                        # and letting codegen hit its loud invariant.  #772
                        # tracks recovering the lost type argument so this path
                        # derives instead of rejecting.
                        return False
                    if not self._type_eq_derivable(args[tp_i], seen):
                        return False
                elif layout.field_types:
                    # Concrete field — dispatch on its DECLARED Vera type,
                    # with nested type params substituted (`List<T>` →
                    # `List<Int>` under a `List<Int>` check, so the recursive
                    # tail hits the `_seen` cycle-break instead of failing on
                    # an unresolved `T`).
                    resolved = substitute_type_param_names(
                        layout.field_types[i], tp_mapping,
                    )
                    if not self._type_eq_derivable(resolved, seen):
                        return False
                elif wasm_type not in ("i64", "i32", "f64"):
                    # Built-in layout without field-type metadata: fall back to
                    # the scalar-rep basis (a non-scalar field is not derivable).
                    return False
        return True

    def _type_eq_derivable(self, name: str, seen: frozenset[str]) -> bool:
        """Is ``name`` Eq-derivable as an ADT field?

        True for an Eq primitive (Int/Nat/Bool/Float64/Byte/Unit **or String**,
        compared by content) or a recursively-Eq ADT.  False for Array / Map /
        host handles / functions — those have no auto-derived Eq.
        """
        base = name.split("<", 1)[0]
        if base in _EQ_TYPES:           # includes String (content comparison)
            return True
        if base in self._adt_layouts:
            return self._adt_satisfies_eq(name, seen)
        # #1070/#1076: an ALIAS or transparent-`Future` spelling (`U` via
        # `type U = Unit;`, `MyInt`, `FI` / `Future<Int>`, chains) names a
        # concrete type — GROUND it and re-judge.  Must stay in lockstep with
        # the `$eq` generator, whose field resolution grounds the same
        # spellings (`_canonical_field_type`): the gate accepting a type the
        # generator cannot lower (or vice versa) breaks the #732 differential.
        # Without this, `Box<U> == Box<U>` / `Box<MyInt> == Box<MyInt>` raised
        # a wrong E613 on a program whose checker (alias-resolving) accepted
        # the Eq.  A genuine free `T` grounds to itself: no recursion.
        ground = self._ground_field_type_name(name)
        if ground != name:
            return self._type_eq_derivable(ground, seen)
        return False

    def _ground_field_type_name(self, name: str) -> str:
        """Generator-side mirror of ``OperatorsMixin._canonical_field_type``.

        Ground spelling of a field / type-argument name: alias chains
        resolved hop by hop, transparent ``Future<…>`` wrappers peeled to
        their payload (#1070/#1076) — ``U`` → ``"Unit"``, ``MyInt`` →
        ``"Int"``, ``FI`` / ``Future<Int>`` → ``"Int"``.  The derivability
        gate runs on the ``CodeGenerator`` (it is threaded into contexts as
        the ``_adt_eq_derivable`` oracle), which holds ``_type_aliases`` but
        not the InferenceMixin walk — so the loop is reimplemented here over
        the same ``type_expr_slot_name`` canonical naming, cycle-cut by
        ``seen``.  A non-alias, non-Future name returns unchanged.
        """
        seen: set[str] = set()
        while True:
            if name.startswith("Future<") and name.endswith(">"):
                name = name[7:-1]
                continue
            if name in seen:
                return name
            te = self._type_aliases.get(name)
            if te is None:
                return name
            seen.add(name)
            target = type_expr_slot_name(te)
            if target is None or target == name:
                return name
            name = target
