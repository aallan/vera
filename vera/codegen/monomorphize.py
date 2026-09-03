"""Mixin for generic function monomorphization (Pass 1.5).

Drives the shared :class:`~vera.monomorphize.Monomorphizer` (instantiation
discovery + AST substitution) to produce monomorphized ``FnDecl`` copies for
WASM emission, and additionally checks ability-constraint satisfaction (E613) —
the one part of monomorphization that is layout-specific and so stays in
codegen.

The discovery + substitution logic itself lives in :mod:`vera.monomorphize` so
the verifier (#732) can reuse the *exact* same code: the verifier must check
precisely the instantiation set this pass emits, or a missed instantiation
becomes a false Tier-1.  Codegen owns the *orchestration* here — the seed walk
plus the transitive worklist, with constraint-failing instances filtered out
(and their subtrees pruned) so the emitted set matches today's behaviour.
"""

from __future__ import annotations

import contextlib
from collections.abc import Iterator

from vera import ast
from vera.monomorphize import (
    MonoContext,
    Monomorphizer,
    UninferredTypeArg,
    collect_nested_generic_decls,
    declared_return_clone_key,
    uninferred_type_arg_fix,
)
from vera.naming import EMPTY_ALIAS_ENV, AliasEnv
from vera.skip import DERIVED_HELPER_DEPTH_CAP
from vera.slots import effect_op_result_names, type_expr_slot_name

# Types that satisfy the built-in abilities.  #773: `Eq` is structural, so a
# field of ANY of these — String included (compared by content) — is
# Eq-derivable; the scalar-only carve-out that excluded String is gone.
_EQ_TYPES: frozenset[str] = frozenset({
    "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit",
})
# #921 (PR #929 review): `Bool` is deliberately ABSENT here.  §4.5 orders only
# Int/Nat/Float64/Byte/String — never Bool — so `Ord<Bool>` must FAIL this
# constraint gate.  With Bool present, a `forall<T where Ord<T>>` instantiated
# at Bool slipped past E613 and lowered `compare`/`<` on two Bool i32 values to
# a signed `i32.lt_s` — a silent order for an unorderable type.
_ORD_TYPES: frozenset[str] = frozenset({
    "Int", "Nat", "Float64", "String", "Byte",
})
_HASH_TYPES: frozenset[str] = frozenset({
    "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit",
})
_SHOW_TYPES: frozenset[str] = frozenset({
    "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit",
})

# Maps ability name → (type set, error description fragment).
_ABILITY_TYPE_SETS: dict[str, tuple[frozenset[str], str]] = {
    "Eq": (_EQ_TYPES, "primitive types (Int, Bool, Float64, String, Byte, Nat, Unit) and ADTs whose fields are themselves Eq (structural derivation)"),
    "Ord": (_ORD_TYPES, "the orderable primitive types (Int, Nat, Float64, String, Byte)"),
    "Hash": (_HASH_TYPES, "primitive types (Int, Nat, Bool, Float64, String, Byte, Unit)"),
    "Show": (_SHOW_TYPES, "primitive types (Int, Nat, Bool, Float64, String, Byte, Unit)"),
}

# Maps a WAT scalar return type to the Vera type name the old
# `_infer_fncall_vera_type_simple` returned for it.  Used to populate
# `MonoContext.fn_ret_types` from `_fn_sigs`, reproducing that behaviour
# exactly (other WAT types — i32_pair, None — yield no entry → `None`).
_WT_TO_VERA: dict[str | None, str] = {
    "i64": "Int",
    "i32": "Bool",
    "f64": "Float64",
}


def _simple_return_type_name(te: ast.TypeExpr | None) -> str | None:
    """The refinement-unwrapped base type name of a return TypeExpr.

    Thin wrapper over the shared :func:`vera.monomorphize.declared_return_clone_key`
    — THE single source of truth for the user-fn-return clone key, so codegen
    discovery, the #732 verifier, and the WASM call-rewrite cannot desync
    (#878 / #899).  ``None`` for shapes with no simple named base (e.g. a bare
    ``FnType``), which the caller then falls back to the WAT-signature collapse.
    """
    return declared_return_clone_key(te)


class MonomorphizationMixin:
    """Methods for monomorphizing generic functions."""

    def _build_mono_context(
        self,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
    ) -> MonoContext:
        """Pack codegen registration state into a shared MonoContext.

        ``fn_ret_types`` is seeded from each function's **declared** return
        TypeExpr (``_fn_ret_type_exprs``, populated by ``_register_fn`` for
        every top-level, prelude, and where-helper fn) — the *precise* Vera
        base type name (``Decimal``, ``Color``, ``Int``), exactly as the #732
        verifier does (``_simple_type_name``).

        This is load-bearing, not cosmetic: a generic whose type argument is
        recovered from a user-fn return in argument position (#878,
        ``pick_first(mkdec(()), …)`` where ``mkdec`` returns ``@Decimal``)
        would otherwise route through the lossy WAT collapse (``i32 → "Bool"``
        — a ``Decimal`` handle is ``i32``), hit the ``"Bool"`` phantom-var
        default, and desync from the verifier (which infers the precise
        ``Decimal``): a #732 differential divergence.  The WAT-signature
        collapse (``i64→Int, i32→Bool, f64→Float64``) is kept only as a
        fallback for any name without a registered return TypeExpr.
        """
        fn_ret_types: dict[str, str] = {}
        for name, sig in self._fn_sigs.items():
            ret_te = self._fn_ret_type_exprs.get(name)
            ret_vera = _simple_return_type_name(ret_te) if ret_te else None
            if ret_vera is None:
                ret_vera = _WT_TO_VERA.get(sig[1])
            if ret_vera is not None:
                fn_ret_types[name] = ret_vera
        return MonoContext(
            generic_decls=generic_decls,
            ctor_to_adt=ctor_to_adt,
            ctor_tp_indices=getattr(self, "_ctor_adt_tp_indices", {}),
            adt_tp_counts=getattr(self, "_adt_tp_counts", {}),
            type_aliases=getattr(self, "_type_aliases", {}),
            type_alias_params=getattr(self, "_type_alias_params", {}),
            # #1208: the same namespace as the two maps above, as one value.
            alias_env=getattr(self, "_alias_env", EMPTY_ALIAS_ENV),
            fn_ret_types=fn_ret_types,
            # #899 issue 1: the declared return TypeExprs (type args retained)
            # let discovery recover a user fn's parameterized return in
            # `Option<T>` argument position, mirroring the WASM call-rewrite.
            fn_ret_type_exprs=dict(self._fn_ret_type_exprs),
            # #1207: the very table the `_effect_ops` shadow guard in
            # `_compile_function` consults, so discovery decides "is this
            # `get` an effect op or a user function?" the same way the
            # rewrite does.  `_fn_sigs` — not `fn_ret_types` above, which
            # drops any name whose return WAT type has no Vera collapse.
            fn_names=frozenset(self._fn_sigs),
            # #1299: and the visibility tables that narrow it per walked
            # declaration.  `fn_names` above is the flat registry — the guard
            # rail needs every emitted symbol in it, including a module's
            # private helpers — so on its own it claimed a bare `get` the
            # entry program's body meant as the operation, and discovery
            # named a clone from the invisible declaration's return type
            # while the rewrite named one from the cell's.
            namespace_fn_names=getattr(self, "_namespace_tables", None),
            # #1274 (F1): every (module, name) the Pass-0 classification made
            # qualified-only, so a rerouted `deep::gen(...)` is not mistaken for
            # an instantiation of the importer's own `gen`.
            qualified_module_generics=frozenset(
                (path, name)
                for path, by_name in getattr(
                    self, "_shadowed_imported_generic_decls", {},
                ).items()
                for name in by_name
            ),
        )

    def _monomorphize(
        self, program: ast.Program,
    ) -> list[ast.FnDecl]:
        """Monomorphize generic functions for all concrete call sites.

        Returns a list of new FnDecl nodes with type variables replaced
        by concrete types and names mangled.
        """
        # Identify generic function declarations.  #990: a ``forall<T>``
        # where-helper under an all-NON-generic ancestor chain is a mono base
        # too — without collecting it here, no clone is emitted and the
        # parent's concrete call lowers to a dangling unmangled name.
        # #1327/#1366: records from the per-call throwaway walkers the
        # shadowed/qualified discovery builds (`_mono_infer_shadowed`), which
        # have no other way back to the drain at the end of this method.
        self._shadowed_uninferred_type_args: list[UninferredTypeArg] = []
        generic_decls: dict[str, ast.FnDecl] = {}
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                if decl.forall_vars:
                    generic_decls[decl.name] = decl
                else:
                    collect_nested_generic_decls(decl, generic_decls)

        # #774: cross-module generic monomorphization.  An imported PUBLIC
        # generic whose bare name is NOT locally shadowed joins `generic_decls`
        # so the importer discovers its instantiations and emits the clones;
        # both a bare call and a qualified `m::g` (which desugars to the bare
        # target) then route through `_generic_fn_info` to the emitted clone.
        # A LOCAL generic of the same name wins (already inserted above).
        # #998: bases that DID enter from the import registry are recorded with
        # their origin module path, so every clone emitted from them (main
        # worklist, shadowed-body transitive chase, and their hoisted
        # where-helpers) can be compiled against that module's own span-keyed
        # tables rather than the importer's.
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

        # Shadowed imported generics (a local non-generic owns the bare name,
        # #814) are monomorphized under a distinct per-module mono base, driven
        # separately below so bare calls stay on the local shadow.
        shadowed_imported: dict[tuple[str, ...], dict[str, ast.FnDecl]] = (
            getattr(self, "_shadowed_imported_generic_decls", {})
        )

        if not generic_decls and not shadowed_imported:
            return []

        # Build constructor → ADT name mapping
        ctor_to_adt: dict[str, str] = {}
        for adt_name in self._adt_layouts:
            for ctor_name in self._adt_layouts[adt_name]:
                ctor_to_adt[ctor_name] = adt_name

        mono = Monomorphizer(
            self._build_mono_context(generic_decls, ctor_to_adt),
        )

        # Record of every (generic name, concrete types) actually emitted —
        # i.e. that passed constraint checks.  Consumed by the #732 differential
        # soundness test, which asserts the verifier discovers a superset of
        # this set; harmless to WAT output (a plain bookkeeping set).
        self._emitted_instances: set[tuple[str, tuple[str, ...]]] = set()

        # Collect concrete instantiations from non-generic function bodies
        instances: dict[str, set[tuple[str, ...]]] = {
            name: set() for name in generic_decls
        }
        # #932: side-map from a TRUNCATED one-level constrained-var type name
        # (`List<List>`, the clone-mangling residue) to its FULLY-recovered
        # nested name (`List<List<Int>>`).  Consulted ONLY for the Eq-derivability
        # DECISION — by `_check_constraints` and the direct-`==` path inside a
        # clone body (`_translate_binary`, via each per-body WasmContext) — never
        # to key a clone symbol, so the mangled clone name codegen emits and
        # looks up is unchanged (the #772 hard constraint).  Populated here from
        # every constrained-generic call site's constructor arguments, across
        # both the seed decls and the transitively emitted mono bodies below.
        self._eq_full_type_names: dict[str, str] = {}
        # #999: seed from resolved-module bodies too.  An imported ``compute``'s
        # body call to its own nested generic ``compute$where$gid`` (or a
        # top-level imported generic) is only reachable through the module's
        # decls, not the main program's — so without walking them the importer
        # emits no clone and the module body's call dangles.  The verifier's
        # `_collect_instantiations` walks the identical set, keeping the #732
        # differential in lockstep.
        #
        # #1274 (F1): the module bodies walked here are the REROUTED copies
        # (`_imported_fn_decls`), not the raw `mod.program`.  A bare call that
        # Pass 0 turned into a `ModuleCall` is no longer a call to the bare name,
        # and seeding from the pre-reroute AST recorded it anyway — codegen
        # emitted a clone of the IMPORTER's same-named generic that nothing
        # calls and the verifier (which walks its rerouted copies) never
        # discovers: a differential desync, and an unverified clone if that
        # generic's contract lied.  These decls carry their where-helpers both
        # nested and as separate entries; `instances` is a set, so the overlap
        # costs nothing.
        # #1299: each declaration is walked in ITS OWN namespace, so a bare
        # call is discovered against the names that body can actually see.
        # The entry program's declarations answer to `None`; an imported body
        # arrives already paired with its module path, which was previously
        # discarded here.
        seed_decls: list[tuple[tuple[str, ...] | None, ast.FnDecl]] = [
            (None, tld.decl) for tld in program.declarations
            if isinstance(tld.decl, ast.FnDecl)
        ]
        seed_decls.extend(getattr(self, "_imported_fn_decls", []))
        for mod_path, decl in seed_decls:
            if not decl.forall_vars:
                with mono.namespace_scope(mod_path):
                    mono.collect_calls_in_node(
                        decl, generic_decls, ctor_to_adt, instances,
                    )
                    self._collect_eq_full_type_names(
                        decl, mono, generic_decls, ctor_to_adt,
                    )

        # Generate monomorphized FnDecls with transitive closure.
        # After generating the first round, scan the monomorphized bodies
        # for further generic calls and generate those too.  This handles
        # cases like array_map calling array_map_go (both generic).
        # Constraint-failing instances are skipped here (and their subtrees
        # pruned), so the emitted set excludes anything that wouldn't compile.
        seen: set[tuple[str, tuple[str, ...]]] = set()
        # Sort each per-name instantiation set so the worklist seed — and hence
        # the order clones are appended to `mono_decls` and emitted to WAT — is
        # deterministic across runs.  Without this, `set` iteration order varies
        # with PYTHONHASHSEED and `vera compile --wat` is not byte-stable (clone
        # bodies are identical; only their order differs), breaking reproducible
        # builds (PR #767 review).
        worklist: list[tuple[str, tuple[str, ...]]] = [
            (fn_name, ct)
            for fn_name, type_arg_set in instances.items()
            for ct in sorted(type_arg_set)
        ]
        mono_decls = self._drain_generic_worklist(
            worklist, seen, generic_decls, ctor_to_adt, mono,
        )

        # Store generic fn info for call rewriting in wasm.py
        self._generic_fn_info: dict[
            str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]
        ] = {}
        # Per-generic set of type vars carrying an ability bound.  The WASM
        # call-site rewriter (`_unify_param_arg_wasm`) recovers the type
        # argument of a `ConstructorCall` bound to one of these, matching the
        # parameterized clone name Pass 1.5 emits — see `_unify_param_arg`
        # (#772).  Without this the call site mangles to `eq2$Box` while the
        # clone is `eq2$Box<String>`, a dangling reference (E602).
        self._generic_constrained_vars: dict[str, frozenset[str]] = {}
        for name, decl in generic_decls.items():
            assert decl.forall_vars is not None  # noqa: S101
            self._generic_fn_info[name] = (decl.forall_vars, decl.params)
            self._generic_constrained_vars[name] = frozenset(
                c.type_var for c in (decl.forall_constraints or ())
            )

        # #814 asymmetric variant: an imported generic whose bare name a LOCAL
        # non-generic shadows is reachable ONLY via a qualified call `m::gen`,
        # so it can't join `generic_decls` (that would hijack the bare `gen`
        # to the module generic).  Discover its qualified instantiations and
        # emit each clone under a distinct ``mod$<path>$…`` mono name so the
        # ModuleCall desugar reaches the module's generic body rather than
        # falling back to the local shadow (the false-Tier-1: verify resolves
        # the module contract, codegen ran the local shadow).  ``generic_decls``
        # + ``seen`` are threaded so a shadowed clone body that calls ANOTHER
        # generic (unshadowed → a normal clone; a same-module shadowed sibling →
        # another ``mod$…`` clone) gets that transitive clone emitted too — a
        # shadowed clone body is scanned exactly like a normal clone body.
        self._register_shadowed_generic_bases(shadowed_imported)
        for path, decls_by_name in shadowed_imported.items():
            self._monomorphize_shadowed_module_generics(
                program, path, decls_by_name, ctor_to_adt, mono, mono_decls,
                generic_decls, seen,
            )

        # #904: hoist every clone's ``where``-helpers into standalone mono
        # decls.  A generic's ``where { fn helper(...) }`` block is carried into
        # each clone by ``monomorphize_fn`` (a total AST substitution), but the
        # generic PARENT is skipped in Pass 2 (its ``@T`` param is `unsupported`
        # WASM), so the parent's where-helpers — emitted only alongside a
        # COMPILABLE parent — were never emitted, and the clone's bare call to
        # ``$helper`` dangled (``unknown func``).  Give each clone its own copy
        # of every helper under a clone-aligned name and rewrite the intra-clone
        # calls to match, so the ordinary mono-decl emission path (register in
        # Pass 1.5, compile in Pass 2) emits them.
        #
        # #1223: hoisting and the top-level worklist are a FIXPOINT, not two
        # phases.  A generic `where`-helper under a generic ancestor is only
        # monomorphized during hoisting, and the concrete clone's body can
        # call a TOP-LEVEL generic at a type nothing else instantiates — its
        # still-generic spelling binds the enclosing type VARIABLE's name
        # (`pick$U`), so the worklist above never sees `pick$Bool` and the
        # rewrite's call dangles (E602, then the whole chain drops with
        # E620).  Each round therefore re-seeds the worklist from the bodies
        # hoisting just produced, and any clones that yields go back through
        # hoisting for their own where-trees.
        emitted: list[ast.FnDecl] = []
        round_decls = mono_decls
        while round_decls:
            hoisted = self._hoist_clone_where_fns(
                round_decls, mono, ctor_to_adt,
            )
            emitted.extend(hoisted)
            reseed: list[tuple[str, tuple[str, ...]]] = []
            found: dict[str, set[tuple[str, ...]]] = {
                name: set() for name in generic_decls
            }
            for body in hoisted:
                # #1299: a clone belongs to the module its base was declared
                # in, which `_mono_clone_origins` records (`None` for a local
                # one — the entry namespace).
                with mono.namespace_scope(
                    self._mono_clone_origins.get(body.name),
                ):
                    mono.collect_calls_in_node(
                        body, generic_decls, ctor_to_adt, found,
                    )
            for t_name, t_types in found.items():
                for t_ct in sorted(t_types):  # deterministic (see the seed)
                    if (t_name, t_ct) not in seen:
                        reseed.append((t_name, t_ct))
            round_decls = self._drain_generic_worklist(
                reseed, seen, generic_decls, ctor_to_adt, mono,
            ) if reseed else []
        # #1327/#1366: discovery is complete, so every type argument it could
        # not infer is now known.  Report each as [E622] — an error, not a
        # note: the instantiation set is what codegen emits clones from, and
        # one built on the phantom-var guess emits a clone the call-site
        # rewrite does not call (E602 with no explanation of why, or an
        # invalid module).  Failing here names the argument the walker could
        # not type, which is the fact the user can act on.
        self._report_uninferred_type_args(mono)
        return emitted

    def _report_uninferred_type_args(self, mono: Monomorphizer) -> None:
        """Turn discovery's un-inferable type arguments into [E622] errors.

        The fail-closed half of the #1327/#1366 family: the phantom-var
        default is retained for a variable no parameter determines, and every
        variable a DIRECT ``@T`` parameter DOES determine but whose argument
        no arm could name is reported here instead of being guessed.
        """
        from vera.errors import Diagnostic
        records = [
            *mono.uninferred_type_args,
            *getattr(self, "_shadowed_uninferred_type_args", []),
        ]
        # #1368 review: the shadowed/qualified discovery builds a THROWAWAY
        # walker per qualified call, so its records reach this accumulator
        # with no shared deduplication — only the per-walker one, which a
        # fresh walker per call cannot supply.  One argument is one
        # diagnostic, so the drain dedupes on the same key the walker uses
        # (`_record_uninferred_type_arg`).  No program in the suite or the
        # corpus currently reaches this second layer twice for one span —
        # removing it changes no measured count — so it is the belt to the
        # per-walker braces rather than a fix for an observed duplicate; the
        # "exactly one" cells in tests/test_uninferred_type_arg_e622.py pin
        # the property wherever it is supplied from.
        seen: set[tuple[str, str, object]] = set()
        for rec in records:
            span = getattr(rec.arg, "span", None)
            key = (
                rec.fn_name,
                rec.type_var,
                (span.line, span.column, span.end_line, span.end_column)
                if span is not None else None,
            )
            if key in seen:
                continue
            seen.add(key)
            loc, source_line = self._diag_location(rec.arg)
            self.diagnostics.append(Diagnostic(
                description=(
                    f"Cannot infer the type argument '{rec.type_var}' of "
                    f"generic call '{rec.fn_name}' from its "
                    f"{rec.arg_kind} argument."
                ),
                location=loc,
                source_line=source_line,
                rationale=(
                    "A generic is compiled by specialising it at each "
                    "concrete type it is called with, so the compiler must "
                    "know the type of every argument that fixes a type "
                    "variable. This argument's type could not be determined, "
                    "and specialising at a guessed type would emit a "
                    "specialisation nothing calls."
                ),
                fix=uninferred_type_arg_fix(
                    rec, self._expr_semantic_types),
                spec_ref='Chapter 5, Section 5.9 "Generic Functions"',
                severity="error",
                error_code="E622",
            ))

    def _drain_generic_worklist(
        self,
        worklist: list[tuple[str, tuple[str, ...]]],
        seen: set[tuple[str, tuple[str, ...]]],
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        mono: Monomorphizer,
    ) -> list[ast.FnDecl]:
        """Monomorphize *worklist* to a fixpoint, returning the new clones.

        The transitive closure over top-level generics: emit each clone, then
        rescan its body for further generic calls.  ``seen`` is the caller's,
        so a second drain (#1223's re-seed from hoisted helper bodies) neither
        re-emits nor loses anything — a key already drained is skipped, and a
        key reached for the first time from a hoisted body is emitted here.
        Constraint-failing instances are skipped (and their subtrees pruned),
        so the emitted set excludes anything that wouldn't compile.
        """
        produced: list[ast.FnDecl] = []
        while worklist:
            fn_name, concrete_types = worklist.pop()
            key = (fn_name, concrete_types)
            if key in seen:
                continue
            seen.add(key)
            if fn_name not in generic_decls:
                continue
            decl = generic_decls[fn_name]
            if not self._check_constraints(decl, concrete_types):
                continue  # constraint violation — error emitted
            # #1208: the clone's binders are named against the DEFINING
            # module's aliases, which is the namespace the consumers rebuild
            # its scope in — see `_clone_alias_env`.
            with self._clone_alias_env(
                    self._imported_generic_base_origins.get(fn_name)) as cenv:
                mono_fn = mono.monomorphize_fn(decl, concrete_types, cenv)
            produced.append(mono_fn)
            self._record_clone_origin(fn_name, mono_fn.name)
            # #1002: remember this clone's concrete-FREE chain base so the
            # per-clone where-tree hoister can key a generic-under-generic
            # helper's `_emitted_instances` entry identically to the verifier.
            self._clone_base_chain[mono_fn.name] = fn_name
            # #932: a transitively-reached nested-generic constrained call in
            # this clone body carries the same truncated constrained-var name —
            # record its full recovery so the next round's `_check_constraints`
            # can decide derivability on the un-truncated name.
            self._collect_eq_full_type_names(
                mono_fn, mono, generic_decls, ctor_to_adt,
            )
            self._emitted_instances.add((fn_name, concrete_types))
            # Scan the monomorphized body for further generic calls
            transitive: dict[str, set[tuple[str, ...]]] = {
                name: set() for name in generic_decls
            }
            with mono.namespace_scope(
                self._mono_clone_origins.get(mono_fn.name),
            ):
                mono.collect_calls_in_node(
                    mono_fn, generic_decls, ctor_to_adt, transitive,
                )
            for t_name, t_types in transitive.items():
                for t_ct in sorted(t_types):  # deterministic order (see seed)
                    if (t_name, t_ct) not in seen:
                        worklist.append((t_name, t_ct))
        return produced

    def _hoist_clone_where_fns(
        self,
        mono_decls: list[ast.FnDecl],
        mono: Monomorphizer,
        ctor_to_adt: dict[str, str],
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
                    generic_helpers, decl.name, [rewritten, *hoisted], pending,
                    mono, ctor_to_adt,
                )
        return result

    def _instantiate_hoisted_generics(
        self,
        gens: list[ast.FnDecl],
        parent_clone_name: str,
        bodies: list[ast.FnDecl],
        pending: list[ast.FnDecl],
        mono: Monomorphizer,
        ctor_to_adt: dict[str, str],
    ) -> None:
        """Instantiate one clone's still-generic hoisted ``where``-helpers (#1002).

        Each of *gens* is a ``forall`` helper hoisted under a generic ancestor's
        clone, renamed to its concrete-including per-clone name
        (``parent$where$outer$Int$where$ginner``).  Register them as generic
        bases so Pass 2's call-site rewriter mangles the (already-redirected)
        bare calls, discover instantiations from *bodies* (the hoisted parent
        clone + its sibling helpers), monomorphize each to a concrete per-clone
        clone (``…$ginner$Int``), record the emission under the concrete-FREE
        chain key so the #732 differential matches the verifier, and re-queue
        each clone so its own where-tree is hoisted.

        The whole FAMILY at once, over a growing body set (#1223).  Taking one
        helper at a time against the still-generic siblings missed every
        instantiation a sibling's own CONCRETE clone introduces: inside the
        generic ``outer<U>``, ``inner(@U.1, @U.0)`` binds ``inner``'s variable
        to the type variable's NAME, so only ``inner$U`` was discovered while
        ``outer$Bool``'s body called ``inner$Bool`` — a dangling target on a
        check-clean program.  Feeding each clone back in as a body closes it,
        and the discovery leaf is the one the verifier drives too
        (``collect_generic_helper_instances``), so neither side can find a
        different set.
        """
        by_name: dict[str, ast.FnDecl] = {}
        chain_keys: dict[str, str] = {}
        for gen in gens:
            assert gen.forall_vars is not None  # noqa: S101
            by_name[gen.name] = gen
            # Register for Pass 2 generic-call resolution under the emission name.
            self._generic_fn_info[gen.name] = (gen.forall_vars, gen.params)
            self._generic_constrained_vars[gen.name] = frozenset(
                c.type_var for c in (gen.forall_constraints or ())
            )
            # The concrete-FREE chain key: the parent clone's chain base plus
            # this helper's bare name (``gen.name`` is
            # ``<parent_clone_name>$where$<h>``).
            base_chain = self._clone_base_chain.get(
                parent_clone_name, parent_clone_name,
            )
            helper_bare = gen.name[len(parent_clone_name) + len("$where$"):]
            chain_keys[gen.name] = f"{base_chain}$where${helper_bare}"
        # Origin: a nested clone of an imported base is the module's own code.
        origin = self._mono_clone_origins.get(parent_clone_name)
        emitted: set[tuple[str, tuple[str, ...]]] = set()
        scan: list[ast.FnDecl] = list(bodies)
        while scan:
            # #1299: the helper family's bodies are the PARENT clone's code,
            # so their bare names resolve in the parent's namespace — the
            # same `origin` the alias env below is built from.  This leaf is
            # the discovery walk BOTH sides drive directly; left unscoped it
            # fell back to the flat table on both at once, so the two agreed
            # while both typed a bare `get(())` from an invisible module
            # declaration.  Agreeing wrongly is invisible to a differential,
            # which is why this one is pinned against the CHECKER's answer.
            with mono.namespace_scope(origin):
                found = mono.collect_generic_helper_instances(
                    by_name, scan, ctor_to_adt,
                )
            scan = []
            for gen_name, concretes in found.items():
                gen = by_name[gen_name]
                for concrete in sorted(concretes):
                    if (gen_name, concrete) in emitted:
                        continue
                    emitted.add((gen_name, concrete))
                    if not self._check_constraints(gen, concrete):
                        continue
                    with self._clone_alias_env(origin) as cenv:  # #1208
                        clone = mono.monomorphize_fn(gen, concrete, cenv)
                    if origin is not None:
                        self._mono_clone_origins[clone.name] = origin
                    # Chain the deeper base so a generic sub-helper of `gen`
                    # keys concrete-free too.
                    self._clone_base_chain[clone.name] = chain_keys[gen_name]
                    self._emitted_instances.add(
                        (chain_keys[gen_name], concrete))
                    pending.append(clone)
                    scan.append(clone)

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
            wfn.name: f"{prefix}$where${wfn.name}"
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

    @contextlib.contextmanager
    def _clone_alias_env(
        self, origin: tuple[str, ...] | None,
    ) -> Iterator[AliasEnv]:
        """Yield the naming env a clone of a generic from *origin* is named
        against (#1208), with the flat alias maps swapped to match.

        Aliases are module-scoped (spec §8.4.1), so the De Bruijn recount in
        ``monomorphize_fn`` has to render binder names in the namespace of the
        module that DECLARED the generic — which is also the namespace the
        clone is later registered and emitted under (``_module_alias_scope``
        at the Pass 1.5 registration and the Pass 2.5 / 2.6 emission doors).
        Named against the importer's instead, an imported generic's
        alias-typed parameter looks like a different class than it is, the
        recount misses the merge, and the emitted clone resolves a reference
        onto the wrong parameter — silently, with the right arity.

        ``origin=None`` (a main-file generic, or a nested helper of one) makes
        this the identity: the flat maps already hold that namespace.

        The source scope is paired with the alias scope here as at the other
        four doors (#1186/#1189, PR #1224 review): entering a module's
        namespace leaves ``file``/``source`` on the IMPORTER, so a diagnostic
        raised while the clone is built would carry the importer's path with
        module-local line/column — coordinates naming unrelated source, and a
        location-keyed dedup (E618) merging two modules' reports into one.
        Nothing under this door reports today; the pairing is what keeps that
        true of whatever moves into it.
        """
        with self._module_alias_scope(origin), self._module_source_scope(origin):
            yield self._alias_env

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

    def _register_shadowed_generic_bases(
        self,
        shadowed_imported: dict[tuple[str, ...], dict[str, ast.FnDecl]],
    ) -> None:
        """Record the ``mod$…`` qualified-call base for every shadowed generic.

        Done up front — before any body scanning — so both the ModuleCall
        desugar and ``_resolve_generic_call`` can resolve a shadowed generic
        (even one only reached transitively from another clone body) to its
        clone, and so a ``m::gen`` site with no discovered instance still routes
        to the module's generic rather than falling back to the local shadow.
        """
        for path, decls_by_name in shadowed_imported.items():
            for gen_name, gdecl in decls_by_name.items():
                assert gdecl.forall_vars is not None  # noqa: S101
                qual_base = self._module_qualified_wasm_name(path, gen_name)
                self._module_qualified_generic_bases[(path, gen_name)] = (
                    qual_base
                )
                self._generic_fn_info[qual_base] = (
                    gdecl.forall_vars, gdecl.params,
                )
                # #772: the qualified base needs the same constrained-var set as
                # a bare generic, so a `ConstructorCall`-inferred Eq call through
                # the `mod$…` clone recovers its type argument too.
                self._generic_constrained_vars[qual_base] = frozenset(
                    c.type_var for c in (gdecl.forall_constraints or ())
                )

    def _monomorphize_shadowed_module_generics(
        self,
        program: ast.Program,
        path: tuple[str, ...],
        decls_by_name: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        mono: Monomorphizer,
        mono_decls: list[ast.FnDecl],
        generic_decls: dict[str, ast.FnDecl],
        seen: set[tuple[str, tuple[str, ...]]],
    ) -> None:
        """Emit clones for a shadowed imported generic reached via ``m::gen``.

        Discovers the concrete instantiations of each shadowed generic from the
        importer's ``ast.ModuleCall`` sites (targeting this module path), emits
        each clone renamed to ``mod$<path>$gen$<types>`` (composing the #814
        ``mod$`` qualified-call prefix with the mono suffix so it can never
        collide with the local shadow's bare ``gen`` nor a normal clone), and
        runs a transitive worklist over the clone bodies exactly like the normal
        path — a shadowed generic whose body calls ANOTHER generic (unshadowed
        or a same-module shadowed sibling) gets that transitive clone emitted
        too, else the missing clone is an ``unknown func`` at run one level out
        (the #774 review, CR 3518737014).
        """
        from dataclasses import replace as _replace

        # Seed: `path::gen(...)` sites in the importer's non-generic bodies AND
        # in every already-emitted NORMAL clone body (CR 3519063445): an
        # UNshadowed generic `caller<T>` whose body qualified-calls a SHADOWED
        # `g::gen` reaches this shadowed generic only through its clone
        # (`caller$Int`), which the main worklist already emitted into
        # `mono_decls`.  Scanning those clones here is the reverse direction of
        # the shadowed→normal transitive scan — without it `caller$Int`'s
        # `g::gen(...)` has no `mod$g$gen$Int` target (`unknown func` at run).
        instances: dict[str, set[tuple[str, ...]]] = {
            name: set() for name in decls_by_name
        }
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and not decl.forall_vars:
                self._collect_shadowed_qualified_calls(
                    decl, path, decls_by_name, ctor_to_adt, instances,
                )
        # #1029: also seed from the imported NON-generic bodies (and their
        # where-helpers), which after the loop-top reroute carry a
        # ``path::inner(...)`` ModuleCall for each qualified-only generic call.
        # Without this a NON-generic caller of a private generic (`use_it` →
        # `inner`) never seeds `mod$<path>$inner$Int`, so Pass 2.5 emits
        # `use_it`'s body with a `call $inner` that dangles (`unknown func`) at
        # run.  These decls already live in `_imported_fn_decls` (rerouted).
        #
        # #1274 (F1): scan EVERY module's decls, not only this path's.  A module
        # can call a DIFFERENT module's qualified-only generic — `mid`'s body
        # calling `deep`'s `gen` — and that reroute lands a `deep::gen(...)`
        # ModuleCall inside a decl registered under `mid`.  Filtering by the
        # OWNING path skipped it, so no `mod$deep$gen$Bool` was emitted and
        # `mid`'s body was dropped.  The walk itself already matches on the call
        # node's own `path`, so widening the scan cannot pick up a foreign one.
        for _mp, fdecl in self._imported_fn_decls:
            if not fdecl.forall_vars:
                self._collect_shadowed_qualified_calls(
                    fdecl, path, decls_by_name, ctor_to_adt, instances,
                )
        for mono_fn in mono_decls:
            self._collect_shadowed_qualified_calls(
                mono_fn, path, decls_by_name, ctor_to_adt, instances,
            )

        # Transitive worklist over shadowed clones.  Each popped shadowed
        # instance is monomorphized under its `mod$…` name; its body is then
        # scanned two ways:
        #   * against `generic_decls` (unshadowed generics) — a discovered
        #     instance is queued into the MAIN worklist's `seen`/`mono_decls`
        #     stream so `inner$Int` etc. are emitted as ordinary clones;
        #   * against this module's shadowed `decls_by_name` (a same-module
        #     shadowed sibling reached by bare name inside the module body) —
        #     queued back onto this shadowed worklist.
        shadowed_seen: set[tuple[str, tuple[str, ...]]] = set()
        worklist: list[tuple[str, tuple[str, ...]]] = [
            (gen_name, ct)
            for gen_name, cts in instances.items()
            for ct in sorted(cts)
        ]
        while worklist:
            gen_name, concrete_types = worklist.pop()
            key = (gen_name, concrete_types)
            if key in shadowed_seen:
                continue
            shadowed_seen.add(key)
            gdecl = decls_by_name[gen_name]
            if not self._check_constraints(gdecl, concrete_types):
                continue
            with self._clone_alias_env(path) as cenv:  # #1208
                clone = mono.monomorphize_fn(gdecl, concrete_types, cenv)
            qual_base = self._module_qualified_generic_bases[(path, gen_name)]
            mangled = self._mono_shadowed_name(qual_base, gen_name, clone.name)

            # Scan the clone body BEFORE rewriting sibling calls, so discovery
            # sees the original bare names.  Unshadowed generics → emit the full
            # closure as ordinary clones; same-module shadowed siblings → queue
            # back onto this shadowed worklist.
            self._chase_normal_transitive(
                clone, generic_decls, ctor_to_adt, mono, mono_decls, seen,
                root_namespace=path,
            )
            trans_shadow: dict[str, set[tuple[str, ...]]] = {
                name: set() for name in decls_by_name
            }
            # #1274 (F1): this scan is keyed on THIS module's own generics, so a
            # `path::sibling(...)` here is the entry meant — see
            # `Monomorphizer.shadowed_module_scope`.
            # #1299: and its bare names resolve in that module's namespace too
            # — this clone's body is that module's code.
            with mono.shadowed_module_scope(path), mono.namespace_scope(path):
                mono.collect_calls_in_node(
                    clone, decls_by_name, ctor_to_adt, trans_shadow,
                )
            for s_name, s_types in trans_shadow.items():
                for s_ct in sorted(s_types):
                    if (s_name, s_ct) not in shadowed_seen:
                        worklist.append((s_name, s_ct))

            # A bare call to a same-module shadowed sibling inside this module
            # body must reach the sibling's ``mod$…`` clone, NOT the importer's
            # local shadow of that name.  The bare sibling name isn't in
            # `_generic_fn_info` (only its `mod$…` base is), so rewrite each such
            # `FnCall.name` to the sibling's `mod$…` base — then the WASM
            # call-site rewriter mangles it to the sibling's clone.
            sibling_bases = {
                s_name: self._module_qualified_generic_bases[(path, s_name)]
                for s_name in decls_by_name
            }
            clone = self._rewrite_sibling_generic_calls(clone, sibling_bases)
            mono_decls.append(_replace(clone, name=mangled))
            # #1029 (R3/R5): record this shadowed clone's concrete-FREE chain
            # base (the ``mod$<path>$gen`` qualified base, NOT the concrete-
            # including emission name).  The per-clone where-tree hoister
            # (`_instantiate_hoisted_generic`) reads `_clone_base_chain` to key a
            # nested generic-under-this-generic helper's `_emitted_instances`
            # entry — so a lying `ginner` under a shadowed/private generic keys
            # `mod$<path>$gen$where$ginner`, byte-identical to what the verifier
            # discovers and reconstructs from its enclosing chain.  Without it the
            # fallback keyed the concrete-including `mod$<path>$gen$Int$where$…`,
            # desyncing the #732 differential and leaving the liar a false Tier-1.
            self._clone_base_chain[mangled] = qual_base
            # #998: a shadowed module generic's clone body is the MODULE's
            # code — compile it against that module's own span tables.
            self._mono_clone_origins[mangled] = path
            # Record the shadowed MODULE clone under its `mod$…` base, NOT the
            # bare `gen_name` — a same-named LOCAL generic owns the bare key, and
            # collapsing both onto it would let the verifier's #732 differential
            # count the module clone as "covered" by the local generic's
            # verification (CR 3519156263).  The verifier records + verifies it
            # under the identical base, keeping the two in lockstep.
            self._emitted_instances.add((qual_base, concrete_types))

    def _chase_normal_transitive(
        self,
        root_fn: ast.FnDecl,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        mono: Monomorphizer,
        mono_decls: list[ast.FnDecl],
        seen: set[tuple[str, tuple[str, ...]]],
        root_namespace: tuple[str, ...] | None = None,
    ) -> None:
        """Emit the transitive closure of normal (unshadowed) clones reachable
        from a clone body scanned during shadowed emission.

        The main worklist has already drained by the time shadowed emission
        runs, so a normal generic reached ONLY from a shadowed clone body (e.g.
        `mod$g$outer$Int` → `inner` → `helper`) would otherwise never be
        emitted — an ``unknown func`` at run.  This re-runs the normal path's
        body-scan worklist rooted at ``root_fn`` (itself already emitted),
        feeding the shared ``seen`` set so nothing is emitted twice.

        *root_namespace* (#1299) is the module ``root_fn`` belongs to.  It is
        passed rather than looked up because a shadowed clone reaches here
        under its PRE-rename name (``gen$Bool``, not
        ``mod$lib$gen$Bool``), which is in no origin registry — and the
        caller has the path in hand.  Clones reached transitively from it get
        their own base's origin, which they are registered under.
        """
        stack: list[tuple[ast.FnDecl, tuple[str, ...] | None]] = [
            (root_fn, root_namespace),
        ]
        while stack:
            fn, namespace = stack.pop()
            transitive: dict[str, set[tuple[str, ...]]] = {
                name: set() for name in generic_decls
            }
            # #1299: each clone in ITS base's namespace (see the sibling scan).
            with mono.namespace_scope(namespace):
                mono.collect_calls_in_node(
                    fn, generic_decls, ctor_to_adt, transitive,
                )
            for t_name, t_types in transitive.items():
                for t_ct in sorted(t_types):
                    if (t_name, t_ct) in seen:
                        continue
                    seen.add((t_name, t_ct))
                    t_decl = generic_decls[t_name]
                    if not self._check_constraints(t_decl, t_ct):
                        continue
                    with self._clone_alias_env(  # #1208
                            self._imported_generic_base_origins.get(
                                t_name)) as cenv:
                        t_fn = mono.monomorphize_fn(t_decl, t_ct, cenv)
                    mono_decls.append(t_fn)
                    self._record_clone_origin(t_name, t_fn.name)
                    # #1029 (R3): a normal clone reached transitively from a
                    # shadowed clone body keys its concrete-FREE chain base the
                    # same way the main worklist does (line ~271), so its own
                    # nested generic-under-generic helper hoists under a
                    # concrete-free `_emitted_instances` key matching the verifier.
                    self._clone_base_chain[t_fn.name] = t_name
                    self._emitted_instances.add((t_name, t_ct))
                    stack.append(
                        (t_fn, self._mono_clone_origins.get(t_fn.name)),
                    )

    @staticmethod
    def _mono_shadowed_name(
        qual_base: str, gen_name: str, clone_name: str,
    ) -> str:
        """Compose the ``mod$…`` qualified prefix with the mono suffix.

        ``monomorphize_fn`` mangles the clone under the bare generic name
        (``gen$Int``); a shadowed generic must live under the module-qualified
        base (``mod$<path>$gen``) instead, so swap the ``gen`` prefix for
        ``qual_base`` while preserving the exact mono suffix (``$Int`` /
        ``$Int_JBool`` / …).  ``clone_name`` always starts with ``gen$`` (the
        mangler joins name + ``$`` + suffix), so this is a straight prefix
        substitution.
        """
        suffix = clone_name[len(gen_name):]  # e.g. "$Int"
        return qual_base + suffix

    def _rewrite_sibling_generic_calls(
        self,
        node: ast.FnDecl,
        sibling_bases: dict[str, str],
    ) -> ast.FnDecl:
        """Rewrite bare ``FnCall``s to same-module shadowed-generic siblings.

        Inside a shadowed generic's clone body (a ``mod$…`` function), a bare
        call to a sibling generic from the SAME module refers to the module's
        sibling — but the importer's flat namespace binds that bare name to the
        LOCAL shadow.  Renaming the ``FnCall.name`` to the sibling's ``mod$…``
        base (a ``_generic_fn_info`` key) makes the WASM call-site rewriter
        mangle it to the sibling's clone (``mod$g$inner$Int``) instead of
        resolving the bare name to the local shadow.  Only the ``.name`` field
        of a matching ``FnCall`` changes; the total dataclass walk leaves every
        other node — including nested ``AnonFn`` bodies — structurally intact.
        """
        result = self._rewrite_call_names(node, sibling_bases)
        assert isinstance(result, ast.FnDecl)  # noqa: S101
        return result

    def _rewrite_call_names(
        self, node: object, rename: dict[str, str],
    ) -> object:
        # Delegates to the shared standalone walker (vera/monomorphize.py) so
        # the #1014 qualification transform and this mixin can never drift.
        from vera.monomorphize import rewrite_fn_call_names

        return rewrite_fn_call_names(node, rename)

    def _collect_shadowed_qualified_calls(
        self,
        node: object,
        path: tuple[str, ...],
        decls_by_name: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
        op_result_types: dict[str, str] | None = None,
    ) -> None:
        """Total AST walk collecting ``path::gen(...)`` instantiation sites.

        #1310: unlike ``Monomorphizer._collect_calls`` (the unshadowed-generic
        discovery walk), this one had no ``HandleExpr`` arm, so a qualified-only
        generic's argument type inferred from an effect-operation result
        (``idg(get(()))`` inside ``handle[State<Int>]``) reached
        ``_mono_infer_shadowed`` with no operation-result registry at all and
        silently fell to the phantom-var ``Bool`` default: the wrong
        instantiation, discovered instead of ``idg$Int``. *op_result_types*
        threads the same merge-not-swap scoping ``_collect_calls`` already does
        (#1207), one node at a time since each qualified call gets its own
        throwaway ``Monomorphizer`` rather than a shared walk-scoped one.
        """
        from dataclasses import fields as _fields

        if op_result_types is None:
            op_result_types = {}

        if isinstance(node, ast.HandleExpr):
            # Same field-drift guard as ``Monomorphizer._collect_calls``: this
            # arm hand-enumerates HandleExpr's children because they are
            # walked in different scopes, so a field added to the dataclass
            # without a matching edit here would go silently unwalked, a
            # missed generic call with no diagnostic pointing at this line.
            enumerated = {"effect", "state", "clauses", "body"}
            declared = {f.name for f in _fields(node)} - {"span"}
            if declared != enumerated:  # pragma: no cover: guard
                msg = (
                    f"HandleExpr fields changed: {sorted(declared)}; this arm "
                    f"walks {sorted(enumerated)}.  Add the new field to the "
                    f"enclosing-scope group or to the handler-scope body walk, "
                    f"an unwalked child hides every generic call inside it."
                )
                raise AssertionError(msg)
            for child in (node.effect, node.state, node.clauses):
                self._collect_shadowed_qualified_calls(
                    child, path, decls_by_name, ctor_to_adt, instances,
                    op_result_types,
                )
            merged = {
                **op_result_types, **effect_op_result_names([node.effect]),
            }
            self._collect_shadowed_qualified_calls(
                node.body, path, decls_by_name, ctor_to_adt, instances,
                merged,
            )
            return

        if (isinstance(node, ast.ModuleCall)
                and tuple(node.path) == path
                and node.name in decls_by_name):
            decl = decls_by_name[node.name]
            type_args = self._mono_infer_shadowed(
                decl, node.args, ctor_to_adt, op_result_types,
            )
            if type_args is not None:
                instances[node.name].add(type_args)
        if isinstance(node, ast.Node):
            for f in _fields(node):
                if f.name == "span":
                    continue
                self._collect_shadowed_qualified_calls(
                    getattr(node, f.name), path, decls_by_name,
                    ctor_to_adt, instances, op_result_types,
                )
        elif isinstance(node, (tuple, list)):
            for item in node:
                self._collect_shadowed_qualified_calls(
                    item, path, decls_by_name, ctor_to_adt, instances,
                    op_result_types,
                )

    def _mono_infer_shadowed(
        self,
        decl: ast.FnDecl,
        args: tuple[ast.Expr, ...],
        ctor_to_adt: dict[str, str],
        op_result_types: dict[str, str] | None = None,
    ) -> tuple[str, ...] | None:
        """Infer a shadowed generic's type args from a qualified call's args."""
        m = Monomorphizer(self._build_mono_context({}, ctor_to_adt))
        if op_result_types:
            m._op_result_types = op_result_types
        result = m._infer_type_args_from_args(decl, args, ctor_to_adt, None)
        # #1327/#1366: this walker is a THROWAWAY built per qualified call, so
        # its fail-closed records would be dropped on the floor.  Carry them to
        # the codegen-level accumulator `_monomorphize` drains, or the shadowed
        # /qualified spelling of a shape (`mod$plib$gen2$Int`) would keep
        # guessing where the unshadowed one refuses.
        self._shadowed_uninferred_type_args.extend(m.uninferred_type_args)
        return result

    def _collect_eq_full_type_names(
        self,
        node: object,
        mono: Monomorphizer,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
    ) -> None:
        """Record TRUNCATED → FULLY-recovered constrained-var names (#932).

        Walks ``node`` for calls to an Eq-constrained generic (``FnCall`` /
        ``ModuleCall`` whose target has a ``where Eq<T>`` bound).  For each
        constrained-var parameter matched positionally to a ``ConstructorCall``
        argument, computes:

        * the TRUNCATED one-level name (`List<List>`) exactly as
          ``Monomorphizer._unify_param_arg`` does via ``_get_arg_type_info`` —
          this is the value `_check_constraints` receives as ``concrete`` and the
          name that keys the emitted clone; and
        * the FULLY-recovered nested name (`List<List<Int>>`) via
          ``Monomorphizer.full_arg_type_name``.

        When the two differ (the nesting was truncated) the pair is stored in
        ``self._eq_full_type_names``, letting ``_check_constraints`` retry the Eq
        derivability decision on the un-truncated name WITHOUT ever changing the
        clone-mangling tuple (the #772 hard constraint).
        """
        from dataclasses import fields as _fields

        call: ast.FnCall | ast.ModuleCall | None = None
        if isinstance(node, (ast.FnCall, ast.ModuleCall)) and (
            node.name in generic_decls
        ):
            call = node
        if call is not None:
            decl = generic_decls[call.name]
            constrained = frozenset(
                c.type_var for c in (decl.forall_constraints or ())
            )
            for param_te, arg in zip(decl.params, call.args):
                base_te = (
                    param_te.base_type
                    if isinstance(param_te, ast.RefinementType)
                    else param_te
                )
                if (
                    isinstance(base_te, ast.NamedType)
                    and base_te.name in constrained
                    and isinstance(arg, ast.ConstructorCall)
                ):
                    info = mono._get_arg_type_info(arg, ctor_to_adt)
                    if info is None:
                        continue
                    base_name, arg_names = info
                    if not (arg_names and all(a is not None for a in arg_names)):
                        continue
                    resolved = [a for a in arg_names if a is not None]
                    truncated = f"{base_name}<{', '.join(resolved)}>"
                    full = mono.full_arg_type_name(arg, ctor_to_adt)
                    if full is not None and full != truncated:
                        self._eq_full_type_names[truncated] = full
        if isinstance(node, ast.Node):
            for f in _fields(node):
                if f.name == "span":
                    continue
                self._collect_eq_full_type_names(
                    getattr(node, f.name), mono, generic_decls, ctor_to_adt,
                )
        elif isinstance(node, (tuple, list)):
            for item in node:
                self._collect_eq_full_type_names(
                    item, mono, generic_decls, ctor_to_adt,
                )

    def _check_constraints(
        self,
        decl: ast.FnDecl,
        concrete_types: tuple[str, ...],
    ) -> bool:
        """Verify all ability constraints are satisfied for an instantiation.

        Returns True if all constraints are satisfied, False otherwise
        (after emitting diagnostics).
        """
        if not decl.forall_constraints or not decl.forall_vars:
            return True

        from vera.errors import Diagnostic, SourceLocation

        mapping = dict(zip(decl.forall_vars, concrete_types))
        ok = True
        for constraint in decl.forall_constraints:
            concrete = mapping.get(constraint.type_var)
            if concrete is None:
                continue
            entry = _ABILITY_TYPE_SETS.get(constraint.ability_name)
            if entry is not None:
                type_set, desc = entry
                # For Eq, also check ADT auto-derivation.  A constrained var
                # bound to a constructor-inferred instance now carries its type
                # argument (`Box<String>`, not bare `Box`) — see
                # `_unify_param_arg` — so `_adt_satisfies_eq` resolves the
                # concrete field type (#772).
                if concrete in type_set:
                    continue
                # #932: the constructor-inferred name may be TRUNCATED one level
                # (`List<List>` for a `List<List<Int>>` operand — the
                # clone-mangling residue).  For the Eq-derivability DECISION only,
                # substitute the fully-recovered nested name recorded at the call
                # site (`_collect_eq_full_type_names`); the clone name codegen
                # emits stays the truncated `concrete` (the #772 hard constraint).
                eq_name = getattr(self, "_eq_full_type_names", {}).get(
                    concrete, concrete,
                )
                if (constraint.ability_name == "Eq"
                        and self._adt_satisfies_eq(eq_name)):
                    continue
                # #1086: an Eq-constrained var bound to an ALIAS or transparent-
                # `Future` spelling (`MyInt` via `type MyInt = Int;`, `FI` /
                # `Future<Int>`, an alias of a WHOLE ADT `MyBox`) is neither a
                # primitive in `type_set` NOR a registered ADT with a layout, so
                # both checks above missed it and the gate raised a wrong-loud
                # E613 on a check-green program (the checker, alias-resolving,
                # accepted the Eq).  `_type_eq_derivable` grounds the spelling
                # (hop-by-hop alias walk + transparent-Future peel) and re-judges
                # — the SAME oracle the `$eq` generator's field resolution
                # mirrors, so the #732 checker↔codegen differential holds at this
                # entry point too.  A genuinely non-Eq alias (`type BadArr =
                # Array<Int>;`) grounds to a non-Eq type and still falls through
                # to the E613 below.  The emitted clone name / message keep the
                # un-ground `concrete` (the #772/#932 hard constraint).
                if (constraint.ability_name == "Eq"
                        and self._type_eq_derivable(eq_name, frozenset())):
                    continue
                # #898: a SPARSE multi-type-parameter ADT reached via the
                # constructor-inferred path (`id1(MkErr(5))` on
                # `Res<A, B> { MkOk(A), MkErr(B) }`) recovers only the type
                # parameter present in the argument (`B = Int`) and leaves the
                # other (`A`) undetermined — the monomorphizer falls back to the
                # bare ADT name `Res`.  Structural Eq derivation checks EVERY
                # constructor's fields (`MkOk(A)` included), so derivability
                # genuinely depends on the free `A` and cannot be decided here.
                # Rejecting is correct (never unsound — the annotated
                # `Res<Array, Int>` form is a real E613), but "Res does not
                # satisfy Eq" misdescribes an under-determined type argument.
                # Report the clearer E619 for this shape only: a bare/partial
                # ADT name whose declared type-parameter count exceeds the type
                # arguments recovered.  A FULLY-determined non-Eq instance
                # (`Res<Array<Int>, Int>`, both params supplied) has no missing
                # argument and stays on the E613 path below.
                if (constraint.ability_name == "Eq"
                        and self._eq_type_arg_under_determined(concrete)):
                    # Render user-facing names WITHOUT the internal `?` sentinel:
                    # the display names each free slot by its declared parameter
                    # (`Res<A, Int>`), and the fix is a concrete, compilable
                    # annotation binding the free parameter to an Eq type
                    # (`let @Res<Int, Int> = ...;`) — #898 round-3 review.
                    display_name, annotation = (
                        self._under_determined_display_and_fix(concrete)
                    )
                    self.diagnostics.append(Diagnostic(
                        description=(
                            f"Cannot infer the type argument(s) for "
                            f"'{display_name}' from the constructor argument, so "
                            f"its 'Eq' derivability is under-determined."
                        ),
                        location=SourceLocation(file=self.file),
                        rationale=(
                            "Structural Eq derivation checks every "
                            "constructor's fields, so a multi-type-parameter "
                            "ADT built from a single constructor (which fixes "
                            "only some parameters) leaves the remaining "
                            "parameters — and thus whether the type derives "
                            "Eq — undetermined."
                        ),
                        fix=(
                            f"Annotate the value so every type parameter is "
                            f"fixed, binding each free parameter to a type that "
                            f"supports Eq — e.g. 'let @{annotation} = ...;' — "
                            f"and pass that slot reference; the constructor path "
                            f"then derives Eq exactly as the annotated form does."
                        ),
                        spec_ref='Chapter 9, Section 9.8 "Abilities"',
                        severity="error",
                        error_code="E619",
                    ))
                    ok = False
                    continue
                # Vera has no `derive` construct — for Eq the actionable fix
                # is structural: make every constructor field itself Eq.
                if constraint.ability_name == "Eq":
                    fix_text = (
                        f"Instantiate the generic with a type that supports "
                        f"'Eq'. An ADT derives Eq structurally when every "
                        f"constructor field is itself Eq — restructure "
                        f"'{concrete}' so its fields are Eq primitives or Eq "
                        f"ADTs (Array/Map/handle fields are not Eq)."
                    )
                else:
                    fix_text = (
                        f"Instantiate the generic with a type that supports "
                        f"'{constraint.ability_name}'."
                    )
                self.diagnostics.append(Diagnostic(
                    description=(
                        f"Type '{concrete}' does not satisfy ability "
                        f"'{constraint.ability_name}'. Only {desc} "
                        f"support {constraint.ability_name}."
                    ),
                    location=SourceLocation(file=self.file),
                    rationale=(
                        "A monomorphized generic instantiates each type "
                        "parameter with a concrete type that must satisfy the "
                        "parameter's ability bounds; this type does not."
                    ),
                    fix=fix_text,
                    spec_ref='Chapter 9, Section 9.8 "Abilities"',
                    severity="error",
                    error_code="E613",
                ))
                ok = False
            else:
                self.diagnostics.append(Diagnostic(
                    description=(
                        f"Ability '{constraint.ability_name}' is not yet "
                        f"supported for code generation."
                    ),
                    location=SourceLocation(file=self.file),
                    rationale=(
                        "Code generation implements a fixed set of built-in "
                        "abilities; this ability has no compilation support."
                    ),
                    fix=(
                        "Constrain the type parameter with a built-in ability "
                        "(Eq, Ord, Hash, or Show) instead."
                    ),
                    spec_ref='Chapter 9, Section 9.8 "Abilities"',
                    severity="error",
                    error_code="E613",
                ))
                ok = False
        return ok

    def _eq_type_arg_under_determined(self, type_name: str) -> bool:
        """Is ``type_name`` an under-determined ADT that WOULD derive Eq? (#898)

        Fires only for a sparse multi-parameter ADT reached via the constructor
        path with a genuinely-FREE type parameter AND whose *known* components
        are all Eq — so annotating the free parameter to an Eq type makes it
        derive.  The caller then reports the clearer E619 ("under-determined
        type argument — annotate it") instead of the misleading E613.

        Distinguishes the two shapes the count-only predecessor conflated
        (both were wrongly E619):

        - `id1(MkErr(5))` on `Res<A, B>`: `B = Int` (Eq), `A` free →  True (E619,
          annotating `A` to an Eq type derives).
        - `id1(MkErr([1]))` on `Res<A, B>` (`B = Array<Int>`, non-Eq recovered),
          and `id1(K([1], 7))` on `W<A, B> { K(Array<A>, B) }` (a structurally
          non-Eq `Array<A>` field) →  False (E613: a known/structural component
          is not Eq, so no annotation of the free parameter can help).

        The monomorphizer materialises a free slot as the ``?`` sentinel
        (`Res<?, Array>`); a bare name (`Res`, no recovery at all) is treated as
        all-free.  The predicate is: some slot is free AND, with every free slot
        provisionally bound to an Eq type, the ADT derives Eq structurally
        (`_adt_satisfies_eq`), which also rejects a structurally non-Eq field.

        False for a fully-applied instance (`Res<Array<Int>, Int>` — no free
        slot; a determined-and-non-Eq E613), a parameterless ADT, or a non-ADT.
        """
        from vera.monomorphize import _FREE_TYPE_PARAM, Monomorphizer

        parsed = Monomorphizer._parse_type_name(type_name)
        base = parsed.name
        if base not in self._adt_layouts:
            return False
        declared = self._adt_tp_counts.get(base, 0)
        if declared == 0:
            return False
        # Reconstruct the per-parameter slots: an explicit arg list may carry
        # the `?` sentinel for free slots; a bare name (`Res`) is all-free.
        arg_names = [
            Monomorphizer._format_type_name(a)
            for a in (parsed.type_args or ())
            if isinstance(a, ast.NamedType)
        ]
        if not arg_names:
            arg_names = [_FREE_TYPE_PARAM] * declared
        has_free = any(a == _FREE_TYPE_PARAM for a in arg_names)
        if not has_free:
            return False
        # Provisionally bind each free slot to a known-Eq type (`Int`) and ask
        # whether the ADT then derives Eq structurally.  If yes, only the free
        # parameters stand between this type and Eq (→ E619, annotate them); if
        # no, a known component or a structural field is non-Eq (→ E613).
        probe_args = [a if a != _FREE_TYPE_PARAM else "Int" for a in arg_names]
        probe_name = f"{base}<{', '.join(probe_args)}>"
        return self._adt_satisfies_eq(probe_name)

    def _under_determined_display_and_fix(
        self, type_name: str,
    ) -> tuple[str, str]:
        """Render user-facing names for an under-determined ADT (#898 round 3).

        Returns ``(display_name, annotation)`` for the E619 diagnostic, with the
        internal ``?`` sentinel (`_FREE_TYPE_PARAM`) never exposed:

        - ``display_name`` shows each free slot as the ADT's *declared* type
          parameter name (`Res<A, Int>`), so the message names the parameter the
          writer must pin — not the reserved `?` placeholder.
        - ``annotation`` is a concrete, compilable Vera type binding each free
          slot to a known-Eq type (`Res<Int, Int>`), so the suggested
          `let @Res<Int, Int> = ...;` fix actually type-checks and derives.

        Falls back to a bare parameterised form from the declared parameter names
        when the recovery carried no explicit slots (a fully-bare `Res`).
        """
        from vera.monomorphize import _FREE_TYPE_PARAM, Monomorphizer

        parsed = Monomorphizer._parse_type_name(type_name)
        base = parsed.name
        declared = self._adt_tp_counts.get(base, 0)
        param_names = self._adt_tp_param_names.get(base, ())
        arg_names = [
            Monomorphizer._format_type_name(a)
            for a in (parsed.type_args or ())
            if isinstance(a, ast.NamedType)
        ]
        if not arg_names:
            arg_names = [_FREE_TYPE_PARAM] * declared
        display_slots: list[str] = []
        fix_slots: list[str] = []
        for i, a in enumerate(arg_names):
            if a == _FREE_TYPE_PARAM:
                # Free slot: show its declared parameter name in the message,
                # and pin it to `Int` (an Eq type) in the actionable fix.
                display_slots.append(
                    param_names[i] if i < len(param_names) else f"T{i}"
                )
                fix_slots.append("Int")
            else:
                display_slots.append(a)
                fix_slots.append(a)
        display_name = f"{base}<{', '.join(display_slots)}>"
        annotation = f"{base}<{', '.join(fix_slots)}>"
        return display_name, annotation

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
        for ctor_name, layout in layouts.items():
            tp_indices = self._ctor_adt_tp_indices.get(ctor_name)
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
