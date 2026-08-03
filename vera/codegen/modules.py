"""Mixin for cross-module registration and call detection (C7e).

Handles Pass 0 (module registration) and Pass 1.9 (cross-module
call detection) of the code generation pipeline.
"""

from __future__ import annotations

import contextlib
from collections.abc import Iterator
from typing import TYPE_CHECKING

from vera import ast
from vera.errors import Diagnostic, SourceLocation
from vera.monomorphize import canonicalize_type_aliases

if TYPE_CHECKING:
    from vera.codegen.core import CodeGenerator


class CrossModuleMixin:
    """Methods for registering imported module declarations."""

    @contextlib.contextmanager
    def _module_alias_scope(
        self, mod_path: tuple[str, ...] | None,
    ) -> Iterator[None]:
        """Resolve type aliases against *mod_path*'s own namespace (#1111).

        Spec §8.4.1: a type alias is module-local — not importable, so two
        modules may reuse one alias name for different targets, and the
        main file's aliases must never re-type a module's declarations.
        For the duration of the ``with`` block the flat
        ``_type_aliases`` / ``_type_alias_params`` maps (main file +
        non-shadowed prelude) are swapped for ``{prelude, **module_own}``
        — the module's aliases overlaying the prelude's, mirroring how
        the main file's own aliases overlay the prelude in the flat maps.
        Every alias consumer downstream (signature derivation, contract
        compilation, inference, closure lifting, compilability scans)
        reads the instance fields mid-compile, so one swap here scopes
        them all.  ``mod_path=None`` (a main-file declaration, or a mono
        clone with no recorded origin) is a no-op.

        The two maps are overlaid as a PAIR (#1184): a module alias
        shadowing a *parameterized* prelude alias with a
        *non*-parameterized one must not inherit the prelude's param
        list.  Merging them independently left exactly that mispairing,
        and ``resolve_type_alias`` substitutes whenever the arities
        happen to line up — so the module's target would be
        instantiated at the prelude's type parameters.  A name the
        module defines therefore takes the module's params entry or
        none at all.
        """
        if mod_path is None:
            yield
            return
        gen: CodeGenerator = self  # type: ignore[assignment]
        saved_aliases = gen._type_aliases
        saved_params = gen._type_alias_params
        mod_aliases = gen._module_type_aliases.get(mod_path, {})
        mod_params = gen._module_type_alias_params.get(mod_path, {})
        gen._type_aliases = {**gen._prelude_type_aliases, **mod_aliases}
        gen._type_alias_params = {
            name: params
            for name, params in gen._prelude_type_alias_params.items()
            if name not in mod_aliases
        }
        gen._type_alias_params.update(mod_params)
        try:
            yield
        finally:
            gen._type_aliases = saved_aliases
            gen._type_alias_params = saved_params

    @contextlib.contextmanager
    def _module_source_scope(
        self, mod_path: tuple[str, ...] | None,
    ) -> Iterator[None]:
        """Locate diagnostics from *mod_path*'s bodies in ITS file (#1186).

        ``_diag_location`` resolves every non-prelude node against
        ``self.file`` / ``self.source`` — the MAIN file.  An imported body's
        spans are module-local, so a skip inside it produced a diagnostic
        carrying the importer's path with the module's line/column: the
        rendered ``source_line`` quoted whatever happened to sit at that
        line in the importer (a stray ``}`` in the #1186 repro), and the
        cross-file branch in ``_drop_dangling_callers`` — which prefixes
        the [E620] caller message with the module the root came from —
        could never fire, because the root's file always compared equal to
        ``self.file``.

        For the duration of the ``with`` block both fields become the
        module's own, so the coordinates and the file finally agree.
        ``mod_path=None`` (or a path with no resolved module) is a no-op.
        """
        gen: CodeGenerator = self  # type: ignore[assignment]
        mod = None
        if mod_path is not None:
            mod = next(
                (m for m in gen._resolved_modules if m.path == mod_path),
                None,
            )
        if mod is None:
            yield
            return
        saved_file = gen.file
        saved_source = gen.source
        gen.file = str(mod.file_path)
        gen.source = mod.source
        try:
            yield
        finally:
            gen.file = saved_file
            gen.source = saved_source

    def _register_modules(self, program: ast.Program) -> None:
        """Register imported function signatures for cross-module codegen.

        Mirrors the verifier's ``_register_modules`` pattern (C7d):
        1. Build import-name filter from ImportDecl nodes.
        2. For each resolved module, register in isolation and harvest
           function signatures, ADT layouts, and type aliases.
        3. Detect name collisions across modules (E608/E609/E610).
        4. Inject into ``self._fn_sigs`` via ``setdefault`` so local
           definitions shadow imported names.
        5. Collect all imported FnDecls for compilation in Pass 2.5.
        """
        if not self._resolved_modules:
            return

        import dataclasses

        from vera.codegen.core import CodeGenerator
        from vera.monomorphize import (
            collect_nested_generic_decls,
            qualify_nested_generic_decls,
        )

        # #1015: give every imported module AST the same #991 parent-qualified
        # where-helper hoist the main program gets at Pass 0 (core.py) — BEFORE
        # any registration or harvesting below reads ``mod.program``.  Without
        # it, imported non-generic helpers keep bare names into the flat Pass
        # 2.5/2.6 namespace, and two imported fns' same-named helpers collide
        # first-seen-wins (silent wrong body).
        #
        # #999: chain the #1014 nested-generic qualification too — a `forall`
        # where-helper under an imported non-generic fn (``compute`` →
        # ``compute$where$gid``) becomes a uniquely-named mono base the importer
        # can discover + clone, exactly as the main program's nested generics
        # do.  Qualification runs BEFORE the hoist (same ordering as the main
        # program, core.py) so a non-generic imported helper calling a generic
        # sibling is qualified before the hoist lifts it out of the shared scope.
        # Both transforms only rename ``FnCall.name`` fields and re-parent helper
        # decls — every node keeps its original span, so the checker-built #987
        # ``_module_artifacts`` span tables stay valid for the transformed AST.
        # Rebind a NEW list of replaced (frozen) ``ResolvedModule``s rather than
        # mutating the caller's list: the verifier scopes where-helpers lexically
        # on the ORIGINAL nested AST and must keep seeing it.
        # #1029: namespace each imported module's nested-generic qualification
        # by the module path (``mod$<path>$compute$where$gid``) — byte-identical
        # to ``_module_qualified_wasm_name`` — so two imported modules' same-named
        # nested generics stay DISTINCT bases instead of collapsing first-seen-wins
        # (which left a lying namesake unemitted/unverified: a false Tier-1).  The
        # main program keeps the bare prefix (core.py Pass 0).
        self._resolved_modules = [
            dataclasses.replace(
                mod,
                program=self._hoist_nongeneric_where_helpers(
                    qualify_nested_generic_decls(
                        mod.program,
                        name_prefix="mod$" + "$".join(mod.path) + "$",
                    ),
                ),
            )
            for mod in self._resolved_modules
        ]

        # Pre-register builtin ADTs so we can identify them during collision
        # detection.  Every CodeGenerator registers Option, Result, Ordering,
        # UrlParts, Tuple, MdInline, MdBlock, etc. via _register_builtin_adts()
        # — they are global infrastructure, not owned by any particular module.
        # Seeing them in two imported modules must not trigger E609/E610.
        self._register_builtin_adts()
        builtin_adt_names: frozenset[str] = frozenset(self._adt_layouts.keys())

        # 1. Build import filter: path -> set of names (or None for wildcard)
        import_names: dict[tuple[str, ...], set[str] | None] = {}
        for imp in program.imports:
            import_names[imp.path] = (
                set(imp.names) if imp.names is not None else None
            )

        # #814 §8.5.3: names of LOCAL functions in the importing program,
        # INCLUDING (recursively) `where`-fn helpers.  A module fn whose bare
        # name appears here is shadowed for bare calls (§8.5.2); its module-
        # qualified target must point at a distinct ``mod$…`` WASM name so
        # ``m::f`` still reaches the module's body, and Pass 2.5 must not emit
        # it under a bare name that would collide with the local helper.  A
        # `where`-fn flattens to a bare ``$name`` just like a top-level fn, so
        # it shadows the namespace identically and must be collected too.
        local_fn_names = self._collect_local_fn_names(program)
        self._local_shadowed_fn_names = local_fn_names

        # Provenance tracking for collision detection
        fn_provenance: dict[str, tuple[str, ...]] = {}
        adt_provenance: dict[str, tuple[str, ...]] = {}
        ctor_provenance: dict[str, tuple[tuple[str, ...], str]] = {}

        # #890: names contributed by transitive-only modules vs names visible
        # to the top-level importer (its own locals + its direct imports'
        # public, in-filter declarations).  A transitive name that is NOT
        # importer-visible becomes `_transitive_only_names` (computed after the
        # loop) so the guard rail forbids a main-program body from calling it.
        transitive_contributed: set[str] = set()
        importer_visible: set[str] = set(local_fn_names)

        # 2. Register each module in isolation
        for mod in self._resolved_modules:
            # #1189: hand the throwaway registrar the module's OWN file.
            # ``_register_fn`` stamps every ``_fn_source_map`` entry with
            # ``self.file``, so without this the harvest below would carry
            # ``"<unknown>"`` — and the main generator, which registers only
            # LOCAL declarations, would stamp the importer's path onto
            # module-local coordinates.  ``ResolvedModule.file_path`` is the
            # same attribution source ``_module_source_scope`` (#1190) reads,
            # so the source map and the diagnostics can never disagree about
            # which file an imported body belongs to.
            temp = CodeGenerator(
                source=mod.source, file=str(mod.file_path),
            )
            temp._register_all(mod.program)

            # Build visibility map for this module
            vis_map: dict[str, str] = {}
            for tld in mod.program.declarations:
                if isinstance(tld.decl, ast.FnDecl):
                    vis_map[tld.decl.name] = tld.visibility or "private"
                elif isinstance(tld.decl, ast.DataDecl):
                    vis_map[tld.decl.name] = tld.visibility or "private"

            # #1000: names of this module's PRIVATE top-level generics.  They
            # are unimportable, so a public generic reaching one transitively
            # must route to the module's own version (``mod$<path>$inner``) — a
            # bare ``inner`` in the importer's flat namespace either dangles or
            # (a same-named local) is captured.  Rerouted below to a synthetic
            # ``ModuleCall`` so the existing shadowed-generic discovery finds it
            # and the ModuleCall desugar resolves it to the qualified clone.
            module_private_generics: set[str] = {
                tld.decl.name
                for tld in mod.program.declarations
                if isinstance(tld.decl, ast.FnDecl)
                and tld.decl.forall_vars
                and (tld.visibility or "private") != "public"
            }

            # Harvest function sigs — include all (public + private) so
            # private helpers called by imported public fns are available.
            name_filter = import_names.get(mod.path)
            for fn_name, sig in temp._fn_sigs.items():
                # Collision detection: same name from different module
                if fn_name in fn_provenance:
                    prev_path = fn_provenance[fn_name]
                    if prev_path != mod.path:
                        self._emit_collision_error(
                            program, fn_name, "Function",
                            prev_path, mod.path, "E608",
                        )
                        continue
                else:
                    fn_provenance[fn_name] = mod.path

                # For bare-call injection: only public + in import filter
                is_public = vis_map.get(fn_name) == "public"
                in_filter = (
                    name_filter is None or fn_name in name_filter
                )
                if is_public and in_filter:
                    self._fn_sigs.setdefault(fn_name, sig)
                # All module functions (including private helpers) get
                # registered so the guard rail sees them as known
                self._fn_sigs.setdefault(fn_name, sig)
                # #890: track importer visibility.  A direct import contributes
                # its public, in-filter names to the importer's namespace; a
                # transitive-only module contributes nothing visible here even
                # though its body is compiled into the flat module.
                if mod.direct:
                    if is_public and in_filter:
                        importer_visible.add(fn_name)
                else:
                    transitive_contributed.add(fn_name)

            # Harvest return-type expressions alongside _fn_sigs.
            # #628 — _fn_ret_type_exprs (added in #614 / re-used by
            # #602) stores each FnDecl's full Vera return-type AST so
            # inference walkers can extract element types from
            # `Array<T>`-returning calls and element types from
            # `String`-returning calls used inside interpolation
            # segments.  Pre-fix the registry was populated only for
            # functions defined in the current module; cross-module
            # calls hit `_fn_ret_type_exprs.get(name) → None` and
            # fell through to the silent-skip path that #602 / #614
            # had already closed in-module.  Same harvest shape as
            # `_fn_sigs` above — `setdefault` so first-seen wins (no
            # collision detection needed; if `fn_sigs` collision
            # detection above caught a name clash, the offending
            # decl was rejected before we reach this loop).
            # #1111: canonicalize each harvested return type against the
            # MODULE's own alias maps before it enters the shared
            # registries.  Spec §8.4.1 makes aliases module-local, so an
            # alias-spelled module return type (``-> @F``) stored raw
            # would later be re-resolved against whatever namespace the
            # consumer happens to hold (the main file's, or another
            # module's) — the #1111 corruption.  Canonical entries carry
            # no resolvable alias name, so every downstream consumer
            # (the fused-await classifier, index-element extraction) is
            # namespace-correct by construction.  A name the module's
            # own maps cannot resolve (e.g. a prelude alias) is left
            # as-is and falls back to the consumer-side resolution
            # against the flat maps, which do hold the prelude's.
            for fn_name, ret_te in temp._fn_ret_type_exprs.items():
                canonical_ret = canonicalize_type_aliases(
                    ret_te, temp._type_aliases, temp._type_alias_params,
                )
                self._fn_ret_type_exprs.setdefault(fn_name, canonical_ret)
                # #841 (PR #842 review round 2): also key by (module
                # path, name) so a module-qualified await classifies by
                # the RESOLVED target's return type.  The bare-name
                # registry above follows local-shadows-import (#814)
                # for unqualified calls, but `m::grab` must not be
                # classified by a colliding local `grab`.
                self._module_fn_ret_type_exprs[
                    (mod.path, fn_name)
                ] = canonical_ret

            # Harvest per-parameter concrete-@Nat flags (#747, CR #756).
            # Without this an imported function `f(@Nat -> …)` loses its
            # `_fn_nat_params` entry, so a cross-module call `f(@Int.0)`
            # would skip the `value >= 0` runtime guard the in-module call
            # gets.  Same `setdefault` first-seen-wins shape as `_fn_sigs`.
            for fn_name, nat_params in temp._fn_nat_params.items():
                self._fn_nat_params.setdefault(fn_name, nat_params)

            # #813: same harvest for the dual @Int-parameter bitmap, so a
            # cross-module call `f(@Nat.0)` into an imported `f(@Int -> …)`
            # keeps its runtime widening guard.
            for fn_name, int_params in temp._fn_int_params.items():
                self._fn_int_params.setdefault(fn_name, int_params)

            # #865: same harvest for the @Byte-parameter bitmap, so a
            # cross-module call `f(3)` into an imported `f(@Byte -> …)`
            # coerces the int-literal argument to i32.const.
            for fn_name, byte_params in temp._fn_byte_params.items():
                self._fn_byte_params.setdefault(fn_name, byte_params)

            # #1189: same harvest for the trap source map.  An imported body
            # is compiled into this WASM module (Pass 2.5/2.6) and can trap at
            # runtime, but only LOCAL declarations reach the main generator's
            # `_register_fn` — so pre-fix an imported frame missed
            # `fn_source_map` entirely and `_resolve_trap_frames` surfaced it
            # as `<unknown>`.  The entries carry the MODULE's file (stamped by
            # the `temp` generator above) with the module-local coordinates the
            # spans already held.  `setdefault` matches the sibling harvests;
            # Pass 1's `_register_all` later OVERWRITES any name a local also
            # defines, which is right — the local owns the bare `$name`
            # emission, and the module's shadowed body is emitted under
            # `mod$…` and mirrored in `_register_shadowed_import`.
            for fn_name, fn_loc in temp._fn_source_map.items():
                self._fn_source_map.setdefault(fn_name, fn_loc)

            # Harvest ADT layouts
            for adt_name, layouts in temp._adt_layouts.items():
                # Builtin ADTs (Option, Result, Ordering, etc.) appear in
                # every CodeGenerator's _adt_layouts — they are not owned by
                # any imported module and must not trigger false E609/E610.
                if adt_name in builtin_adt_names:
                    continue

                is_public = vis_map.get(adt_name) == "public"
                in_filter = (
                    name_filter is None or adt_name in name_filter
                )

                # ADT type name collision detection
                if adt_name in adt_provenance:
                    prev_path = adt_provenance[adt_name]
                    if prev_path != mod.path:
                        self._emit_collision_error(
                            program, adt_name, "Data type",
                            prev_path, mod.path, "E609",
                        )
                        continue
                else:
                    adt_provenance[adt_name] = mod.path

                # Constructor name collision detection
                ctor_collision = False
                for ctor_name in layouts:
                    if ctor_name in ctor_provenance:
                        prev_path, prev_adt = ctor_provenance[ctor_name]
                        if prev_path != mod.path:
                            self._emit_ctor_collision_error(
                                program, ctor_name,
                                prev_path, prev_adt,
                                mod.path, adt_name,
                            )
                            ctor_collision = True
                    else:
                        ctor_provenance[ctor_name] = (mod.path, adt_name)

                if not ctor_collision:
                    # #1008: register EVERY non-colliding module ADT's layout
                    # (public or private, in the import filter or not) — the
                    # module's OWN bodies compile in Pass 2.5/2.6 against
                    # ``self._adt_layouts``, so a module fn constructing its
                    # own ADT dropped to ``unknown constructor`` →
                    # ``CodegenSkip`` → a dangling ``$fn`` whenever the
                    # importer didn't name the TYPE (or the ADT is private).
                    # This softens no user-facing rail: the checker already
                    # rejects the MAIN program's use of an unimported ctor in
                    # both positions (E210 expression / E320 pattern), and
                    # importer VISIBILITY below stays public + in-filter.
                    self._adt_layouts.setdefault(adt_name, layouts)
                    # #912: propagate the imported ADT's type-parameter
                    # metadata alongside its layout.  Without these, an imported
                    # generic ADT (`Box<T>`) reached codegen with a layout but
                    # NO `_adt_tp_param_names` / `_adt_tp_counts` entry, so the
                    # structural-Eq machinery could neither substitute its
                    # parameters nor recognise a monomorphized clone that lost
                    # its type argument — a composite `==` on it fell back to a
                    # pointer compare or raised a spurious E613.  The `temp`
                    # generator computed the full metadata from this module's
                    # `DataDecl`s; carry it over in lockstep with the layout.
                    for _reg_name, _reg in (
                        (n, temp._adt_tp_param_names.get(n))
                        for n in (adt_name,)
                    ):
                        if _reg is not None:
                            self._adt_tp_param_names.setdefault(_reg_name, _reg)
                    if adt_name in temp._adt_tp_counts:
                        self._adt_tp_counts.setdefault(
                            adt_name, temp._adt_tp_counts[adt_name])
                    for _ctor_name in layouts:
                        if _ctor_name in temp._ctor_adt_tp_indices:
                            self._ctor_adt_tp_indices.setdefault(
                                _ctor_name,
                                temp._ctor_adt_tp_indices[_ctor_name])
                    self._needs_alloc = True
                    self._needs_memory = True
                    # #890: importer-visible only for a PUBLIC, in-filter ADT
                    # of a direct import; a transitive module's public ADT +
                    # ctors are compiled in (an imported body may construct
                    # them) but stay invisible to the top-level program.  A
                    # private / out-of-filter ADT registers its layout above
                    # (#1008) but joins NEITHER set — exactly its pre-#1008
                    # bookkeeping.
                    if is_public and in_filter:
                        if mod.direct:
                            importer_visible.add(adt_name)
                            importer_visible.update(layouts.keys())
                        else:
                            transitive_contributed.add(adt_name)
                            transitive_contributed.update(layouts.keys())

            # Capture type aliases PER MODULE (#1111) — never into the
            # flat maps.  Spec §8.4.1: a type alias is module-local, so
            # two modules may reuse one name for different targets and
            # neither the main file nor a sibling module may resolve
            # through it.  ``_module_alias_scope`` installs this
            # module's maps while its declarations compile / register;
            # the old flat ``setdefault`` merge (first module won, local
            # registration then overwrote) is exactly the #1111 bug.
            self._module_type_aliases[mod.path] = dict(temp._type_aliases)
            self._module_type_alias_params[mod.path] = dict(
                temp._type_alias_params,
            )

            # Collect ALL FnDecls from this module for compilation, and wire
            # up module-qualified-call resolution (#814 §8.5.3 + C2).
            #
            # Generic (`forall`) fns are excluded throughout: cross-module
            # generic monomorphisation is separately unimplemented (#774), and
            # a generic body can't be emitted under a mangled name.
            #
            # A module fn whose bare name a LOCAL shadows is emitted (Pass
            # 2.6) under a distinct ``mod$…`` name (collision-free: '$' is
            # illegal in Vera identifiers) so a qualified call can reach the
            # module's body while bare calls keep resolving to the local.  We
            # do this for BOTH public and private shadowed fns: a private
            # helper isn't qualified-callable, but a *public* shadowed fn's
            # body may call it, and inside the emitted ``mod$`` body that
            # intra-module call must reach the module's version too (C2) — so
            # both get a ``mod$`` emission and an intra-rename entry.  Only
            # public, in-filter fns additionally get a ``_module_qualified_
            # targets`` entry (the table the desugar consults for ``m::f``).
            for tld in mod.program.declarations:
                if not isinstance(tld.decl, ast.FnDecl):
                    continue
                # #1029: reroute EVERY imported decl's bare calls to this
                # module's private generics ONCE at the loop top, and use the
                # rerouted copy in ALL branches below.  Pre-fix only the PUBLIC
                # generic branch rerouted (#1000), so a NON-generic caller
                # (``use_it`` → private ``inner``), a private→private chain
                # (private ``A`` → private ``B``), and a private generic's own
                # body all kept the bare call — which dangled (``unknown func``)
                # or was captured by a same-named local.  The reroute is
                # shadow-aware (a where-helper of the same name owns the bare
                # call), so it never captures a lexically-nearer helper.  Only
                # the call nodes change; name/params/sig are untouched, so the
                # ``temp._fn_sigs``-keyed registration lookups below stay valid.
                routed = self._reroute_private_generic_calls(
                    tld.decl, mod.path, module_private_generics,
                )
                # #774: an imported PUBLIC generic is monomorphized by the
                # importer (Pass 1.5) at its own call sites — it can't be
                # emitted verbatim under a bare/mangled name in Pass 2.5, but
                # its concrete clones can.  Harvest its FnDecl here so
                # `_monomorphize` can discover instantiations of it and clone
                # its body; a private module generic is not callable from the
                # importer, so it never needs harvesting.  Split by local
                # shadowing (§8.5.2): an unshadowed generic routes bare +
                # qualified through `_generic_fn_info`; a shadowed one is
                # qualified-only (the bare name stays on the local).
                if tld.decl.forall_vars:
                    is_public = (tld.visibility or "private") == "public"
                    in_filter = (
                        name_filter is None or tld.decl.name in name_filter
                    )
                    if is_public and in_filter:
                        if tld.decl.name in local_fn_names:
                            self._shadowed_imported_generic_decls.setdefault(
                                mod.path, {},
                            ).setdefault(tld.decl.name, routed)
                        else:
                            self._imported_generic_decls.setdefault(
                                tld.decl.name, routed,
                            )
                            # #998: same first-seen-wins order as the decl
                            # registry, so a clone of this generic compiles
                            # against ITS module's span tables.
                            self._imported_generic_origins.setdefault(
                                tld.decl.name, mod.path,
                            )
                    elif not is_public:
                        # #1000: a PRIVATE module generic is reachable only
                        # transitively (through a public generic's body).
                        # Harvest it under the module-qualified shadowed-generic
                        # identity (``mod$<path>$name`` via the shared shadowed
                        # machinery) — NEVER the bare ``_imported_generic_decls``,
                        # where a bare-name entry would hijack a same-named local
                        # fn (E608's import-only provenance can't catch that).
                        # #1029: use the rerouted copy so a private→private chain
                        # (this private generic calls ANOTHER private generic)
                        # reaches the sibling's ``mod$<path>$sibling`` clone.
                        self._shadowed_imported_generic_decls.setdefault(
                            mod.path, {},
                        ).setdefault(tld.decl.name, routed)
                    continue
                is_public = (tld.visibility or "private") == "public"
                in_filter = name_filter is None or tld.decl.name in name_filter
                # #1029: the rerouted non-generic body carries the private-generic
                # ModuleCalls the Pass-2.5 emission + shadowed-generic discovery
                # (`_monomorphize_shadowed_module_generics`) both consume.
                self._imported_fn_decls.append((mod.path, routed))
                self._register_shadowed_import(
                    mod.path, routed, temp, local_fn_names,
                    qualified_eligible=is_public and in_filter,
                )
                # #999: harvest this imported NON-generic fn's nested `forall`
                # where-helpers (qualified to ``compute$where$gid`` above) as
                # imported mono bases, with origin threading (#998) so each
                # clone compiles against this module's span tables.  The
                # importer seeds their instantiations from the module BODY in
                # `_monomorphize` (that body's ``compute$where$gid(@Int.0)``
                # call), then emits + verifies the clones — pre-fix the call had
                # no base and WAT assembly dangled at ``unknown func $gid``.
                nested_gen: dict[str, ast.FnDecl] = {}
                collect_nested_generic_decls(routed, nested_gen)
                for _gname, _gdecl in nested_gen.items():
                    self._imported_generic_decls.setdefault(_gname, _gdecl)
                    self._imported_generic_origins.setdefault(
                        _gname, mod.path,
                    )
                # where-fns compile in Pass 2.5 too, so they need the SAME
                # shadow wiring: an imported body's call to a locally-shadowed
                # helper must reach the module's helper, not the local (#814
                # C2).  They are private nested fns, never qualified-callable,
                # so they never get a ``_module_qualified_targets`` entry.
                #
                # Walk the FULL where-fn tree, not just direct children (#989):
                # an imported ``libfn -> child -> grandchild`` chain registered
                # only ``child`` under a one-level loop, so ``grandchild`` was
                # checked + verified but never emitted in Pass 2.5, and
                # ``child``'s call to it dangled (``unknown func``).  Reuse the
                # same ``_flatten_where_fns`` walk the local non-generic Pass-2
                # emission loop uses (mirrors the #978 local-path fix).
                for wfn in self._flatten_where_fns(routed):
                    if wfn.forall_vars:
                        continue
                    self._imported_fn_decls.append((mod.path, wfn))
                    self._register_shadowed_import(
                        mod.path, wfn, temp, local_fn_names,
                        qualified_eligible=False,
                    )

        # #890: a name is transitive-only iff a transitive module contributes
        # it AND it is not visible to the importer (not a local, not a direct
        # import's public in-filter name).  A transitive symbol that a direct
        # import ALSO exposes stays callable — the direct exposure wins.  The
        # guard rail subtracts this set so a main-program body calling a purely
        # transitive symbol fails loudly (spec §8.6.4), while the imported
        # bodies that legitimately call it (compiled in Pass 2.5, not scanned
        # by the guard rail) keep resolving to the emitted definition.
        self._transitive_only_names = transitive_contributed - importer_visible

    @staticmethod
    def _collect_local_fn_names(program: ast.Program) -> set[str]:
        """All locally-declared function names that occupy (or may occupy) a
        bare ``$name`` in the single WASM module, including (recursively) the
        names of ``where``-fn helpers still nested in *program*.

        Only a name that flattens to a bare emission shadows the importer's
        namespace — an imported fn of the same name is then treated as
        shadowed (reached via ``mod$…``, never a clashing bare emission).
        Callers pass the POST-hoist program (#991 / PR #1013 round 4): a
        non-generic helper is by then a separate ``$``-qualified top-level
        decl that can never equal an import's bare name, so it no longer
        suppresses the import — its bare source name belongs to the import
        outside the parent (spec §5 helper locality; the stale pre-hoist
        shadow left the import unemitted and the bare call dangling, and at
        base the helper's bare emission silently CAPTURED it).  Helpers still
        nested here — RETAINED generic helpers, and everything under a
        generic top-level — must keep shadowing: an uninstantiated T-unused
        generic template still emits under its bare name, which would collide
        with the import's bare emission (duplicate func identifier).
        """
        def walk(decl: ast.FnDecl) -> set[str]:
            names = {decl.name}
            for wfn in decl.where_fns or ():
                names |= walk(wfn)
            return names

        out: set[str] = set()
        for tld in program.declarations:
            if isinstance(tld.decl, ast.FnDecl):
                out |= walk(tld.decl)
        return out

    def _register_shadowed_import(
        self,
        mod_path: tuple[str, ...],
        decl: ast.FnDecl,
        temp: CodeGenerator,
        local_fn_names: set[str],
        *,
        qualified_eligible: bool,
    ) -> None:
        """Wire up a module function (top-level or where-fn) whose bare name a
        LOCAL shadows (#814 §8.5.3 + C2).

        Only a SHADOWED name needs anything: the desugar and the intra-rename
        map fall back to the bare name otherwise, which is already correct for
        a non-shadowed module fn (emitted under its bare name).  For a shadowed
        one we emit the module's version under a distinct ``mod$…`` name (Pass
        2.6) and record an intra-rename so an imported body's bare sibling call
        reaches the module's version, not the local shadow.  Only a top-level
        public, in-filter declaration additionally gets a ``_module_qualified_
        targets`` entry (the table the ``m::f`` desugar consults) — a where-fn
        is private and never qualified-callable, so ``qualified_eligible`` is
        ``False`` for it.
        """
        fn_name = decl.name
        if fn_name not in local_fn_names:
            return
        mangled_sig = temp._fn_sigs.get(fn_name)
        if mangled_sig is None:
            return
        mangled = self._module_qualified_wasm_name(mod_path, fn_name)
        self._fn_sigs.setdefault(mangled, mangled_sig)
        self._shadowed_module_fns.append((mod_path, mangled, decl))
        self._module_intra_renames.setdefault(mod_path, {})[fn_name] = mangled
        # Mirror the per-name side-tables onto the mangled name so a call that
        # resolves to it keeps the same inference/guards as the bare name:
        #  - @Nat-parameter guard bitmap → call-site ``value >= 0`` narrowing;
        #  - return-type expression → index / interpolation element-type
        #    inference for a shadowed fn returning ``String`` / ``Array<T>``.
        self._fn_nat_params.setdefault(
            mangled, temp._fn_nat_params.get(fn_name, ()))
        self._fn_int_params.setdefault(  # #813: dual widening-guard bitmap
            mangled, temp._fn_int_params.get(fn_name, ()))
        self._fn_byte_params.setdefault(  # #865: byte-literal coercion bitmap
            mangled, temp._fn_byte_params.get(fn_name, ()))
        # #1189: and the trap source map, keyed on the MANGLED name.  A trap
        # inside this emission surfaces `mod$<path>$name` in the wasmtime
        # frame; the resolver's rightmost-`$` strip yields `mod$<path>`, which
        # is nobody's entry, so the bare-name harvest cannot cover it and the
        # frame resolved to `<unknown>`.  The location is the module's own
        # (`temp` carries the module's file), unchanged by the rename.
        fn_loc = temp._fn_source_map.get(fn_name)
        if fn_loc is not None:
            self._fn_source_map.setdefault(mangled, fn_loc)
        ret_te = temp._fn_ret_type_exprs.get(fn_name)
        if ret_te is not None:
            # #1111 (PR #1175 review): the shadowed door's mirror of the
            # Pass-0 canonical harvest.  The mangled ``mod$…`` entry feeds
            # the same shared registry, so a raw alias-spelled return type
            # here would be re-resolved against the flat maps (the main
            # file's aliases) by the qualified-call consumers — the exact
            # corruption the bare-name path just closed.
            self._fn_ret_type_exprs.setdefault(
                mangled,
                canonicalize_type_aliases(
                    ret_te, temp._type_aliases, temp._type_alias_params,
                ),
            )
        if qualified_eligible:
            self._module_qualified_targets[(mod_path, fn_name)] = mangled

    @staticmethod
    def _reroute_private_generic_calls(
        decl: ast.FnDecl,
        module_path: tuple[str, ...],
        private_generics: set[str],
    ) -> ast.FnDecl:
        """Rewrite bare calls to a module's PRIVATE generics into synthetic
        ``ModuleCall``s (#1000).

        A public imported generic's body may transitively call one of its
        module's private generics by bare name.  Once the importer clones that
        body, the bare name is ambiguous — it dangles (the private generic is
        unimportable) or a same-named local captures it.  Rewriting each such
        ``FnCall`` to ``ModuleCall(module_path, name)`` routes it through the
        existing shadowed-generic discovery + desugar
        (``_resolve_module_call_wasm_name`` → ``_module_qualified_generic_bases``
        → the ``mod$<path>$name`` clone), so it reaches the module's own version.
        Only the call NODE changes (``FnCall`` → ``ModuleCall`` with the same
        args, recursively rerouted); every other node — including nested
        ``AnonFn`` / ``where`` bodies — is structurally preserved with its span.

        Delegates to the shared shadow-aware walk
        (:func:`vera.monomorphize.reroute_module_private_generic_calls`) so this
        codegen reroute and the verifier's #732 mirror can never drift (#1029) —
        the two differ only in the terminal node each builds (codegen a
        ``ModuleCall`` resolved by the desugar; the verifier a name-renamed
        ``FnCall`` keyed to the same ``mod$…`` discovery base).
        """
        from vera.monomorphize import reroute_module_private_generic_calls

        return reroute_module_private_generic_calls(
            decl, private_generics,
            lambda call, args: ast.ModuleCall(
                path=module_path, name=call.name, args=args, span=call.span,
            ),
        )

    @staticmethod
    def _module_qualified_wasm_name(
        path: tuple[str, ...], name: str,
    ) -> str:
        """WASM name for a module fn reached via a qualified call ``m::f``
        when its bare name is shadowed by a local definition (#814 §8.5.3).

        Uses ``$`` as the separator — illegal in Vera identifiers, so the
        result can never collide with a user function name — mirroring the
        monomorphizer's ``name$TypeArg`` mangling convention.
        """
        return "mod$" + "$".join(path) + "$" + name

    # -----------------------------------------------------------------
    # Name collision diagnostics
    # -----------------------------------------------------------------

    def _emit_collision_error(
        self,
        program: ast.Program,
        name: str,
        kind: str,
        path_a: tuple[str, ...],
        path_b: tuple[str, ...],
        error_code: str,
    ) -> None:
        """Emit a diagnostic for a name collision between imported modules."""
        mod_a = ".".join(path_a)
        mod_b = ".".join(path_b)
        imp_node = self._find_import_node(program, path_b)
        loc = SourceLocation(file=self.file)
        if imp_node and imp_node.span:
            loc.line = imp_node.span.line
            loc.column = imp_node.span.column
        self.diagnostics.append(Diagnostic(
            description=(
                f"{kind} '{name}' is defined in both imported module "
                f"'{mod_a}' and '{mod_b}'."
            ),
            location=loc,
            source_line=self._get_source_line(loc.line),
            rationale=(
                "The flat compilation strategy (C7e) compiles all imported "
                "functions into a single WASM namespace. Names must be "
                "unique across imported modules to avoid silent overwrites."
            ),
            fix=f"Rename '{name}' in one of the source modules.",
            spec_ref='Chapter 11, Section 11.16 "Cross-Module Compilation"',
            severity="error",
            error_code=error_code,
        ))

    def _emit_ctor_collision_error(
        self,
        program: ast.Program,
        ctor_name: str,
        path_a: tuple[str, ...],
        adt_a: str,
        path_b: tuple[str, ...],
        adt_b: str,
    ) -> None:
        """Emit a diagnostic for a constructor name collision."""
        mod_a = ".".join(path_a)
        mod_b = ".".join(path_b)
        imp_node = self._find_import_node(program, path_b)
        loc = SourceLocation(file=self.file)
        if imp_node and imp_node.span:
            loc.line = imp_node.span.line
            loc.column = imp_node.span.column
        self.diagnostics.append(Diagnostic(
            description=(
                f"Constructor '{ctor_name}' is defined in both imported "
                f"module '{mod_a}' (data {adt_a}) and "
                f"'{mod_b}' (data {adt_b})."
            ),
            location=loc,
            source_line=self._get_source_line(loc.line),
            rationale=(
                "The flat compilation strategy (C7e) compiles all ADT "
                "constructors into a single namespace. Duplicate constructor "
                "names cause incorrect pattern matching and memory layouts."
            ),
            fix=f"Rename constructor '{ctor_name}' in one of the data types.",
            spec_ref='Chapter 11, Section 11.16 "Cross-Module Compilation"',
            severity="error",
            error_code="E610",
        ))

    @staticmethod
    def _find_import_node(
        program: ast.Program, path: tuple[str, ...],
    ) -> ast.ImportDecl | None:
        """Find the ImportDecl for a given module path."""
        for imp in program.imports:
            if imp.path == path:
                return imp
        return None

    # -----------------------------------------------------------------
    # Cross-module call detection
    # -----------------------------------------------------------------

    def _check_cross_module_calls(self, program: ast.Program) -> None:
        """Detect calls to imported functions that codegen cannot compile.

        Walks all function bodies looking for FnCall/ModuleCall nodes
        whose targets have no local definition.  Emits a proper Vera
        diagnostic instead of letting invalid WAT reach wasmtime.
        """
        # Build the set of locally-defined names the codegen knows about
        known: set[str] = set(self._fn_sigs.keys())
        for layouts in self._adt_layouts.values():
            known.update(layouts.keys())
        # #890: a purely transitive symbol (compiled in for an imported body,
        # but not visible to this program per spec §8.6.4) is NOT callable from
        # a main-program body — drop it so such a call is reported unresolved
        # rather than silently binding to the emitted-for-a-sibling definition.
        known -= self._transitive_only_names
        # Built-in names handled specially in _translate_call
        known.update({
            "array_length", "array_append", "array_range", "array_concat",
            "array_slice",
            # Higher-order combinators — all iterative WASM (#480).
            "array_map", "array_filter", "array_fold",
            # Array utilities (#466 phase 1) — also iterative WASM.
            "array_mapi", "array_reverse", "array_find",
            "array_any", "array_all", "array_flatten", "array_sort_by",
            "apply_fn", "get", "put", "throw", "resume",
            "string_length", "string_concat", "string_slice",
            "string_char_code", "string_from_char_code", "string_repeat",
            "parse_nat", "parse_int", "parse_float64", "parse_bool",
            "base64_encode", "base64_decode",
            "url_encode", "url_decode", "url_parse", "url_join",
            "to_string", "int_to_string", "bool_to_string",
            "nat_to_string", "byte_to_string", "float_to_string",
            "string_strip",
            "string_contains", "string_starts_with", "string_ends_with",
            "string_index_of",
            "string_upper", "string_lower", "string_replace",
            "string_split", "string_join",
            # String utilities (#470) — all iterative WAT.
            "string_chars", "string_lines", "string_words",
            "string_pad_start", "string_pad_end",
            "string_reverse", "string_trim_start", "string_trim_end",
            # Character classification + case conversion (#471) — all
            # ASCII-range checks inlined as WAT.
            "is_digit", "is_alpha", "is_alphanumeric",
            "is_whitespace", "is_upper", "is_lower",
            "char_to_upper", "char_to_lower",
            "abs", "min", "max", "floor", "ceil", "round", "sqrt", "pow",
            # Math builtins (#467) — log/trig via host imports,
            # pi/e/sign/clamp/float_clamp inlined as WAT.
            "log", "log2", "log10",
            "sin", "cos", "tan", "asin", "acos", "atan", "atan2",
            "pi", "e", "sign", "clamp", "float_clamp",
            "int_to_float", "float_to_int", "nat_to_int", "int_to_nat",
            "byte_to_int", "int_to_byte",
            "float_is_nan", "float_is_infinite", "nan", "infinity",
            "async", "await",
            "md_parse", "md_render", "md_has_heading",
            "md_has_code_block", "md_extract_code_blocks",
            "regex_match", "regex_find", "regex_find_all",
            "regex_replace",
            # Ability operations (§9.8) — rewritten or dispatched by codegen
            "eq", "compare", "show", "hash",
            # Map operations (§9.4.3) — host-import builtins
            "map_new", "map_insert", "map_get", "map_contains",
            "map_remove", "map_size", "map_keys", "map_values",
            # Set operations (§9.4.2) — host-import builtins
            "set_new", "set_add", "set_contains",
            "set_remove", "set_size", "set_to_array",
            # Decimal operations (§9.7.2) — host-import builtins
            "decimal_from_int", "decimal_from_float",
            "decimal_from_string", "decimal_to_string",
            "decimal_to_float", "decimal_add", "decimal_sub",
            "decimal_mul", "decimal_div", "decimal_neg",
            "decimal_compare", "decimal_eq",
            "decimal_round", "decimal_abs",
            # Json operations (§9.7.1) — host-import builtins
            "json_parse", "json_stringify",
            # Html operations (§9.7.4) — host-import builtins
            "html_parse", "html_to_string", "html_query", "html_text",
        })

        seen: set[str] = set()  # deduplicate by function name

        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and not decl.forall_vars:
                self._scan_body_for_unknown_calls(
                    decl.body, known, seen,
                )

    def _scan_body_for_unknown_calls(
        self,
        node: ast.Node,
        known: set[str],
        seen: set[str],
    ) -> None:
        """Recursively walk an AST node looking for unresolved calls."""
        if isinstance(node, ast.ModuleCall):
            # C7e: if the function is known (imported), skip it — wasm.py
            # will desugar the ModuleCall to a flat FnCall.
            if node.name not in known:
                qual = ".".join(node.path) + "::" + node.name
                if qual not in seen:
                    seen.add(qual)
                    self._emit_cross_module_error(node, node.name, qual)
            # Recurse into args even for known calls
            for arg in node.args:
                self._scan_body_for_unknown_calls(arg, known, seen)
            return

        if isinstance(node, ast.FnCall) and node.name not in known:
            if node.name not in seen:
                seen.add(node.name)
                self._emit_cross_module_error(node, node.name)

        # Recurse into child nodes
        if isinstance(node, ast.Block):
            for stmt in node.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._scan_body_for_unknown_calls(stmt.value, known, seen)
                elif isinstance(stmt, ast.ExprStmt):
                    self._scan_body_for_unknown_calls(stmt.expr, known, seen)
            self._scan_body_for_unknown_calls(node.expr, known, seen)
        elif isinstance(node, ast.BinaryExpr):
            self._scan_body_for_unknown_calls(node.left, known, seen)
            self._scan_body_for_unknown_calls(node.right, known, seen)
        elif isinstance(node, ast.UnaryExpr):
            self._scan_body_for_unknown_calls(node.operand, known, seen)
        elif isinstance(node, ast.IfExpr):
            self._scan_body_for_unknown_calls(node.condition, known, seen)
            self._scan_body_for_unknown_calls(node.then_branch, known, seen)
            if node.else_branch:
                self._scan_body_for_unknown_calls(
                    node.else_branch, known, seen,
                )
        elif isinstance(node, ast.FnCall):
            for arg in node.args:
                self._scan_body_for_unknown_calls(arg, known, seen)
        elif isinstance(node, ast.ConstructorCall):
            for arg in node.args:
                self._scan_body_for_unknown_calls(arg, known, seen)
        elif isinstance(node, ast.MatchExpr):
            self._scan_body_for_unknown_calls(node.scrutinee, known, seen)
            for arm in node.arms:
                self._scan_body_for_unknown_calls(arm.body, known, seen)
        elif isinstance(node, ast.InterpolatedString):
            for part in node.parts:
                if not isinstance(part, str):
                    self._scan_body_for_unknown_calls(part, known, seen)

    def _emit_cross_module_error(
        self,
        node: ast.Node,
        name: str,
        qualified: str | None = None,
    ) -> None:
        """Emit a diagnostic for an undefined function call."""
        display = qualified or name
        loc = SourceLocation(file=self.file)
        if node.span:
            loc.line = node.span.line
            loc.column = node.span.column
        description = (
            f"Function '{display}' is not defined in this module "
            f"and was not found in any imported module."
        )
        rationale = (
            "The WASM code generator compiles imported functions into the "
            "same binary.  An unresolved call has no target to compile "
            "against; the checker only warns (E200) on it, so the program "
            "still reaches code generation."
        )
        source_line = self._get_source_line(loc.line)
        # A module-qualified call (`m::f`) and a bare call (`f`) fail for
        # different reasons and cite different spec sections.  Emit each with a
        # *literal* spec_ref (rather than a branched variable) so the
        # diagnostic-fields gate can validate both citations against the spec.
        if qualified is not None:
            self.diagnostics.append(Diagnostic(
                description=description,
                location=loc,
                source_line=source_line,
                rationale=rationale,
                fix=(
                    f"Ensure '{qualified}' names a function exported by a "
                    f"module this file imports — check the import path and "
                    f"that the target module declares it."
                ),
                spec_ref='Chapter 8, Section 8.5.3 "Module-Qualified Calls"',
                severity="error",
            ))
        else:
            self.diagnostics.append(Diagnostic(
                description=description,
                location=loc,
                source_line=source_line,
                rationale=rationale,
                fix=(
                    f"Define '{name}' in this module, or import it from the "
                    f"module that declares it with 'import <module>({name});' "
                    f"(replace <module> with that module's path, e.g. "
                    f"'vera.math')."
                ),
                spec_ref='Chapter 8, Section 8.5.1 "Bare Calls"',
                severity="error",
            ))
