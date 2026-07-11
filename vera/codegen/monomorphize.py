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

from typing import Any

from vera import ast
from vera.monomorphize import (
    MonoContext,
    Monomorphizer,
    collect_nested_generic_decls,
    declared_return_clone_key,
)
from vera.skip import DERIVED_HELPER_DEPTH_CAP

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
            fn_ret_types=fn_ret_types,
            # #899 issue 1: the declared return TypeExprs (type args retained)
            # let discovery recover a user fn's parameterized return in
            # `Option<T>` argument position, mirroring the WASM call-rewrite.
            fn_ret_type_exprs=dict(self._fn_ret_type_exprs),
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
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and not decl.forall_vars:
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
        mono_decls: list[ast.FnDecl] = []
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
            mono_fn = mono.monomorphize_fn(decl, concrete_types)
            mono_decls.append(mono_fn)
            self._record_clone_origin(fn_name, mono_fn.name)
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
            mono.collect_calls_in_node(
                mono_fn, generic_decls, ctor_to_adt, transitive,
            )
            for t_name, t_types in transitive.items():
                for t_ct in sorted(t_types):  # deterministic order (see seed)
                    if (t_name, t_ct) not in seen:
                        worklist.append((t_name, t_ct))

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
        return self._hoist_clone_where_fns(mono_decls)

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
        """
        result: list[ast.FnDecl] = []
        for decl in mono_decls:
            if not decl.where_fns:
                result.append(decl)
                continue
            hoisted: list[ast.FnDecl] = []
            rewritten = self._hoist_where_fns_under(
                decl, decl.name, hoisted,
            )
            result.append(rewritten)
            result.extend(hoisted)
            # #998: a hoisted helper's body is the same module's code as the
            # clone it was hoisted from — it needs the same span tables.
            origin = self._mono_clone_origins.get(decl.name)
            if origin is not None:
                for h in hoisted:
                    self._mono_clone_origins[h.name] = origin
        return result

    def _hoist_where_fns_under(
        self,
        fn: ast.FnDecl,
        prefix: str,
        hoisted: list[ast.FnDecl],
    ) -> ast.FnDecl:
        """Hoist ``fn``'s ``where``-helpers under ``prefix``, recursively.

        Returns ``fn`` with its ``where_fns`` stripped and every bare call to a
        (now-renamed) helper redirected.  Each helper is appended to ``hoisted``
        under ``<prefix>$where$<helper>``, with its OWN nested helpers hoisted
        under that new prefix.  The sibling-rename map is shared across the
        parent body and every helper body so a helper→sibling-helper call is
        rewritten identically to a parent→helper call.
        """
        from dataclasses import replace as _replace

        where_fns = fn.where_fns or ()
        rename = {
            wfn.name: f"{prefix}$where${wfn.name}"
            for wfn in where_fns
        }
        for wfn in where_fns:
            # Recurse first (under the helper's own hoisted name) so a nested
            # helper's calls are redirected before the sibling-rename pass.
            child = self._hoist_where_fns_under(
                wfn, rename[wfn.name], hoisted,
            )
            renamed = self._rewrite_call_names(child, rename)
            assert isinstance(renamed, ast.FnDecl)  # noqa: S101
            hoisted.append(_replace(renamed, name=rename[wfn.name]))
        # Strip the parent's where block and redirect its calls to the helpers.
        stripped = _replace(fn, where_fns=None)
        rewritten = self._rewrite_call_names(stripped, rename)
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
            clone = mono.monomorphize_fn(gdecl, concrete_types)
            qual_base = self._module_qualified_generic_bases[(path, gen_name)]
            mangled = self._mono_shadowed_name(qual_base, gen_name, clone.name)

            # Scan the clone body BEFORE rewriting sibling calls, so discovery
            # sees the original bare names.  Unshadowed generics → emit the full
            # closure as ordinary clones; same-module shadowed siblings → queue
            # back onto this shadowed worklist.
            self._chase_normal_transitive(
                clone, generic_decls, ctor_to_adt, mono, mono_decls, seen,
            )
            trans_shadow: dict[str, set[tuple[str, ...]]] = {
                name: set() for name in decls_by_name
            }
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
    ) -> None:
        """Emit the transitive closure of normal (unshadowed) clones reachable
        from a clone body scanned during shadowed emission.

        The main worklist has already drained by the time shadowed emission
        runs, so a normal generic reached ONLY from a shadowed clone body (e.g.
        `mod$g$outer$Int` → `inner` → `helper`) would otherwise never be
        emitted — an ``unknown func`` at run.  This re-runs the normal path's
        body-scan worklist rooted at ``root_fn`` (itself already emitted),
        feeding the shared ``seen`` set so nothing is emitted twice.
        """
        stack: list[ast.FnDecl] = [root_fn]
        while stack:
            fn = stack.pop()
            transitive: dict[str, set[tuple[str, ...]]] = {
                name: set() for name in generic_decls
            }
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
                    t_fn = mono.monomorphize_fn(t_decl, t_ct)
                    mono_decls.append(t_fn)
                    self._record_clone_origin(t_name, t_fn.name)
                    self._emitted_instances.add((t_name, t_ct))
                    stack.append(t_fn)

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
        from dataclasses import fields as _fields
        from dataclasses import replace as _replace

        if isinstance(node, ast.Node):
            changes: dict[str, Any] = {}
            for f in _fields(node):
                if f.name == "span":
                    continue
                val = getattr(node, f.name)
                new_val = self._rewrite_call_names(val, rename)
                if new_val is not val:
                    changes[f.name] = new_val
            if isinstance(node, ast.FnCall) and node.name in rename:
                changes["name"] = rename[node.name]
            if changes:
                return _replace(node, **changes)
            return node
        if isinstance(node, tuple):
            new_items = tuple(
                self._rewrite_call_names(v, rename) for v in node
            )
            if any(n is not o for n, o in zip(new_items, node)):
                return new_items
            return node
        return node

    def _collect_shadowed_qualified_calls(
        self,
        node: object,
        path: tuple[str, ...],
        decls_by_name: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
    ) -> None:
        """Total AST walk collecting ``path::gen(...)`` instantiation sites."""
        from dataclasses import fields as _fields

        if (isinstance(node, ast.ModuleCall)
                and tuple(node.path) == path
                and node.name in decls_by_name):
            decl = decls_by_name[node.name]
            type_args = self._mono_infer_shadowed(
                decl, node.args, ctor_to_adt,
            )
            if type_args is not None:
                instances[node.name].add(type_args)
        if isinstance(node, ast.Node):
            for f in _fields(node):
                if f.name == "span":
                    continue
                self._collect_shadowed_qualified_calls(
                    getattr(node, f.name), path, decls_by_name,
                    ctor_to_adt, instances,
                )
        elif isinstance(node, (tuple, list)):
            for item in node:
                self._collect_shadowed_qualified_calls(
                    item, path, decls_by_name, ctor_to_adt, instances,
                )

    def _mono_infer_shadowed(
        self,
        decl: ast.FnDecl,
        args: tuple[ast.Expr, ...],
        ctor_to_adt: dict[str, str],
    ) -> tuple[str, ...] | None:
        """Infer a shadowed generic's type args from a qualified call's args."""
        m = Monomorphizer(self._build_mono_context({}, ctor_to_adt))
        return m._infer_type_args_from_args(decl, args, ctor_to_adt, None)

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
        return False
