"""Mixin for cross-module registration and call detection (C7e).

Handles Pass 0 (module registration) and Pass 1.9 (cross-module
call detection) of the code generation pipeline.
"""

from __future__ import annotations

import contextlib
from collections.abc import Iterator, Mapping
from dataclasses import fields as dc_fields
from typing import TYPE_CHECKING

from vera import ast
from vera.builtins import INTRINSICS
from vera.errors import Diagnostic, SourceLocation
from vera.module_view import imported_data_types
from vera.monomorphize import (
    canonicalize_type_aliases,
    namespace_fn_names,
    namespace_module_reach,
    qualify_contended_data_decls,
)
from vera.naming import display_adt_name
from vera.prelude import PRELUDE_NAMESPACE, data_decl_shape, prelude_adt_names
from vera.resolver import merged_import_filters

if TYPE_CHECKING:
    from vera.codegen.core import CodeGenerator
    from vera.resolver import ResolvedModule


class _Ambiguous:
    """Two imports supply this name, so it denotes no one declaration.

    §8.5.2.2 refuses that shape rather than resolving it, so #1317's ADT
    rename must not treat it as an answer either — a distinct sentinel
    rather than ``None``, which means "denotes no MODULE declaration" and
    is an ordinary, renameable state.
    """

    __slots__ = ()

    def __repr__(self) -> str:  # pragma: no cover — debugging aid
        return "<ambiguous>"


_AMBIGUOUS = _Ambiguous()

#: The names `_translate_call` dispatches that are not in the built-in
#: registry's `INTRINSICS`: closure application, the `Eq` and `Ord`
#: operations it rewrites, and the effect operations a handler or an
#: effect row binds.
_DISPATCHED_NAMES: frozenset[str] = frozenset({
    "apply_fn", "eq", "compare", "get", "put", "throw", "resume",
})

# "No declaration keeps the bare spelling" — distinct from every
# `data_decl_shape` value, so a keeper comparison against it is always
# False rather than accidentally matching a shape.
_NOTHING = object()

# The ENTRY file, standing in a set of module paths.  No module's path is
# empty, so it can never name a declaration the #1317 rename could target —
# which is the point: the entry's own `data` is E623's business (#1312) and
# is only ever COUNTED here, never renamed.
_ENTRY_OWNER: tuple[str, ...] = ()


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
        non-shadowed prelude) — and the ``_alias_env`` those two describe
        (#1208) — are swapped for ``{prelude, **module_own}``
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
        # The declaration-index space is swapped with them (PR #1224 review):
        # it answers "was this name already declared when this alias body was
        # registered?", which is a question about ONE namespace.  The module's
        # own 0-based space overlays the prelude's negative block, mirroring
        # the alias overlay above; a main-file declaration is not in it, and a
        # module declaration is not in the main file's.
        saved_order = gen._decl_order
        gen._decl_order = {
            **gen._prelude_decl_order,
            **gen._module_decl_order.get(mod_path, {}),
        }
        # #1253: and so is ADT MEMBERSHIP — which names are data types HERE.
        # `_adt_layouts` is one map across every absorbed namespace, so
        # without this a sibling module's ADTs stayed members of this module's
        # namespace while the checker, registering each module in isolation,
        # never saw them: the two sides disagreeing about what a name MEANS.
        saved_active = gen._active_module_path
        gen._active_module_path = mod_path
        # #1208: the naming environment is part of the swapped pair — it
        # describes exactly these two maps, so it moves with them or it names
        # the module's declarations against the main file's aliases.
        saved_env = gen._alias_env
        gen._sync_alias_env()
        try:
            yield
        finally:
            gen._type_aliases = saved_aliases
            gen._type_alias_params = saved_params
            gen._decl_order = saved_order
            gen._active_module_path = saved_active
            gen._alias_env = saved_env

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
        #
        # Pre-register builtin ADTs so we can identify them during collision
        # detection.  Every CodeGenerator registers Option, Result, Ordering,
        # UrlParts, Tuple, MdInline, MdBlock, etc. via _register_builtin_adts()
        # — they are global infrastructure, not owned by any particular module.
        # Seeing them in two imported modules must not trigger E609/E610.
        # Registered BEFORE the transform below rather than after it (#1317):
        # the ADT rename reads this snapshot to hold the prelude's names back
        # from the rename, so it has to exist by then.  The call writes
        # `_adt_layouts` and nothing else, and is idempotent.
        self._register_builtin_adts()
        builtin_adt_names: frozenset[str] = frozenset(self._adt_layouts.keys())

        # #1317 / #187 (data half): the ADT analogue of the ``mod$…``
        # rerouting above.  A module ``data`` declaration that CONTENDS with
        # another module's — same bare name, layouts that cannot be one
        # layout — is renamed to ``mod$<path>$<Name>`` (with its
        # constructors) inside every namespace that can name it, so ADT
        # identity becomes ``(owner, name)`` by construction and the flat
        # registries stop being the thing that decides.  Computed over all
        # the modules at once, and EMPTY for every program with no contended
        # name, which is why no corpus program's emitted WAT moves.
        # #1493: every module's program as the checker saw it, before the
        # link step and the rewrites below.  Import lists keep source names
        # while the link step and the #1317 rename rewrite references, so
        # what a namespace imports is asked of these and then spelled
        # through that namespace's own renames (`_module_registrar`).
        checker_programs = {
            mod.path: mod.program for mod in self._unlinked_modules
        }
        adt_renames = self._contended_adt_renames(
            program, builtin_adt_names, checker_programs)
        self._resolved_modules = [
            dataclasses.replace(
                mod,
                program=self._hoist_nongeneric_where_helpers(
                    qualify_nested_generic_decls(
                        qualify_contended_data_decls(
                            mod.program,
                            *adt_renames.get(mod.path, ({}, {})),
                        ),
                    ),
                ),
            )
            for mod in self._resolved_modules
        ]

        # #1253: per-namespace ADT bookkeeping, filled in the harvest loop and
        # folded into membership sets after it.
        declared_adts: dict[tuple[str, ...], frozenset[str]] = {}
        # #1513: which of those each module EXPORTS, read by the
        # constructor fallback in `_namespace_ctor_projection`.
        public_adts: dict[tuple[str, ...], frozenset[str]] = {}

        # Provenance tracking for collision detection
        adt_provenance: dict[str, tuple[str, ...]] = {}
        ctor_provenance: dict[str, tuple[tuple[str, ...], str]] = {}

        # 2. Register each module in ITS OWN namespace (#1493): its own
        #    declarations, with the data types it imports in scope.
        for mod in self._resolved_modules:
            temp = self._module_registrar(
                mod, checker_programs, adt_renames.get(mod.path, ({}, {}))[0],
            )
            # #1317: capture this module's alias namespace BEFORE the ADT
            # harvest below, not after it.  The harvest's collision rails ask
            # `_adt_decls_share_a_layout`, which resolves each declaration's
            # field types through its OWN module's maps (§8.4.1) — so the
            # module being harvested has to be in the table by then, or a
            # restatement spelled through its own alias would key DIFFERENT
            # and be refused.  The capture is idempotent and depends on
            # nothing the harvest does; the block that used to hold it below
            # is now this one, moved, with its reasoning intact.
            #
            # Spec §8.4.1: a type alias is module-local, so two modules may
            # reuse one name for different targets and neither the main file
            # nor a sibling module may resolve through it.  These are NEVER
            # merged into the flat maps; `_module_alias_scope` installs this
            # module's while its declarations compile / register, and the old
            # flat `setdefault` merge (first module won, local registration
            # then overwrote) is exactly the #1111 bug.
            self._module_type_aliases[mod.path] = dict(temp._type_aliases)
            self._module_type_alias_params[mod.path] = dict(
                temp._type_alias_params,
            )

            # Build visibility map for this module
            vis_map: dict[str, str] = {}
            for tld in mod.program.declarations:
                if isinstance(tld.decl, ast.FnDecl):
                    vis_map[tld.decl.name] = tld.visibility or "private"
                elif isinstance(tld.decl, ast.DataDecl):
                    vis_map[tld.decl.name] = tld.visibility or "private"

            # #1253: what this module DECLARES as data types — its own, under
            # any #1317 rename.  With what it imports
            # (`vera.module_view.imported_data_types`) that is its membership
            # below: a module's namespace holds its own ADTs whatever their
            # visibility, which is exactly the checker's view.
            declared_adts[mod.path] = frozenset(
                tld.decl.name
                for tld in mod.program.declarations
                if isinstance(tld.decl, ast.DataDecl)
            )
            public_adts[mod.path] = frozenset(
                name for name in declared_adts[mod.path]
                if vis_map.get(name) == "public"
            )

            # Harvest function sigs — all of them, public and private, so the
            # private helpers an imported public function calls are there.
            # Every module function is registered under its link name
            # (`vera.binding.link`), which no other declaration has, so the
            # harvest takes each one as it is.
            for fn_name, sig in temp._fn_sigs.items():
                self._fn_sigs.setdefault(fn_name, sig)

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

            # #865: same harvest for the @Byte-parameter bitmap, so a
            # cross-module call `f(3)` into an imported `f(@Byte -> …)`
            # coerces the int-literal argument to i32.const.
            for fn_name, byte_params in temp._fn_byte_params.items():
                self._fn_byte_params.setdefault(fn_name, byte_params)

            # #1189: same harvest for the trap source map.  An imported body
            # is compiled into this WASM module (Pass 2.5) and can trap at
            # runtime, but only LOCAL declarations reach the main generator's
            # `_register_fn` — so pre-fix an imported frame missed
            # `fn_source_map` entirely and `_resolve_trap_frames` surfaced it
            # as `<unknown>`.  The entries carry the MODULE's file (stamped by
            # the `temp` generator above) with the module-local coordinates the
            # spans already held, keyed by link name like every harvest here.
            for fn_name, fn_loc in temp._fn_source_map.items():
                self._fn_source_map.setdefault(fn_name, fn_loc)

            # Harvest ADT layouts
            for adt_name, layouts in temp._adt_layouts.items():
                # Builtin ADTs (Option, Result, Ordering, etc.) appear in
                # every CodeGenerator's _adt_layouts — they are not owned by
                # any imported module and must not trigger false E609/E610.
                if adt_name in builtin_adt_names:
                    continue

                # ADT type name collision detection.  #1317: two modules that
                # declare the SAME LAYOUT under one name are not a collision
                # — the single registered slot serves both, which is the
                # rule #1277 already established for a module against the
                # prelude and #1312 for the entry file against a module.  A
                # restatement is an ordinary thing to write across a
                # dependency diamond, and refusing it left renaming in a
                # dependency's source as the only remedy.
                restatement = False
                if adt_name in adt_provenance:
                    prev_path = adt_provenance[adt_name]
                    if prev_path != mod.path:
                        if self._adt_decls_share_a_layout(
                            adt_name, prev_path, mod.path,
                        ):
                            restatement = True
                        else:
                            self._emit_collision_error(
                                program, adt_name, "Data type",
                                prev_path, mod.path, "E609",
                            )
                            continue
                else:
                    adt_provenance[adt_name] = mod.path

                # Constructor name collision detection.  A restatement's
                # constructors are the FIRST declaration's, name for name and
                # tag for tag — that is what sharing a layout means — so the
                # rail is skipped in lockstep with E609 above.  Relaxing one
                # without the other would close nothing: two modules restating
                # a type share its constructor names too, so E610 would refuse
                # exactly the programs E609 just admitted.
                ctor_collision = False
                if not restatement:
                    for ctor_name in layouts:
                        if ctor_name in ctor_provenance:
                            prev_ctor_path, prev_adt = ctor_provenance[ctor_name]
                            if prev_ctor_path != mod.path:
                                self._emit_ctor_collision_error(
                                    program, ctor_name,
                                    prev_ctor_path, prev_adt,
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
                    # #1227: and the namespace that declared it, so the
                    # naming env can order it where its own module did
                    # rather than at the built-in floor.  `setdefault`
                    # matches the layout above — the first module to
                    # register a name owns it, and a MAIN-file declaration
                    # of the same name is never routed here (it stamps
                    # `_decl_order`, which `_adt_decl_index` asks first).
                    self._adt_layout_owners.setdefault(adt_name, mod.path)
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
                    # #1436: carry the module's tp-indices under BOTH keys —
                    # the per-owner map the namespace-scoped projection reads,
                    # and the flat mirror.  Copying only the flat one left a
                    # module's own generic ADT absent from the scoped table, so
                    # its structural-Eq lost the type argument and
                    # `Wrap(3) == Wrap(3)` came back false.
                    _owned_tp = temp._adt_ctor_tp_indices.get(adt_name, {})
                    for _ctor_name in layouts:
                        if _ctor_name in _owned_tp:
                            self._adt_ctor_tp_indices.setdefault(
                                adt_name, {}).setdefault(
                                    _ctor_name, _owned_tp[_ctor_name])
                        # ctor-owner-exempt: the flat mirror, rebuilt per
                        # namespace by `_namespace_ctor_projection`
                        if _ctor_name in temp._ctor_adt_tp_indices:
                            # ctor-owner-exempt: the flat mirror carried
                            # alongside the per-owner copy above (#1436)
                            self._ctor_adt_tp_indices.setdefault(
                                _ctor_name,
                                # ctor-owner-exempt: the flat mirror carried
                                # alongside the per-owner copy above (#1436)
                                temp._ctor_adt_tp_indices[_ctor_name])
                    self._needs_alloc = True
                    self._needs_memory = True

            # The alias-namespace capture (#1111) that used to sit here now
            # runs immediately after `temp._register_all` above, where the
            # ADT harvest's shape comparison can already read it (#1317).
            #
            # #1208: capture this module's declaration ORDER as its OWN
            # namespace, exactly as the alias maps above are captured, in the
            # module's own source order (`temp` registered them 0-based).
            # `_module_alias_scope` installs it as {prelude, **module_own}
            # while the module compiles.
            #
            # It used to be folded into ONE shared index space instead, which
            # was a silent miscompile (PR #1224 review): `_stamp_decl_order`
            # is idempotent by name, modules are absorbed at Pass 0.5 and the
            # main file at Pass 1, so a name a module stamped kept that
            # earlier index in the MAIN file's namespace and turned its
            # forward reference into a backward one.  The reverse direction
            # (a main-file alias ordering against a module's namespace) was
            # never possible; this one was, and both directions are closed by
            # keying the space to its owner.
            self._module_decl_order[mod.path] = dict(temp._decl_order)

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
                decl = tld.decl
                if decl.forall_vars:
                    self._imported_generic_decls.setdefault(decl.name, decl)
                    self._imported_generic_origins.setdefault(
                        decl.name, mod.path,
                    )
                    continue
                self._imported_fn_decls.append((mod.path, decl))
                nested_gen: dict[str, ast.FnDecl] = {}
                collect_nested_generic_decls(decl, nested_gen)
                for _gname, _gdecl in nested_gen.items():
                    self._imported_generic_decls.setdefault(_gname, _gdecl)
                    self._imported_generic_origins.setdefault(
                        _gname, mod.path,
                    )
                for wfn in self._flatten_where_fns(decl):
                    if wfn.forall_vars:
                        continue
                    self._imported_fn_decls.append((mod.path, wfn))

        self._builtin_adt_names = builtin_adt_names
        self._module_public_adts = dict(public_adts)
        self._namespace_module_reach = self._build_namespace_module_reach()
        self._adt_namespace_members = self._build_adt_membership(
            program, declared_adts, checker_programs, adt_renames,
        )

    def _module_registrar(
        self,
        mod: ResolvedModule,
        checker_programs: Mapping[tuple[str, ...], ast.Program],
        renames: Mapping[str, str],
    ) -> CodeGenerator:
        """*mod*'s declarations, registered in *mod*'s own namespace (#1493).

        The registrar measures each signature's WASM widths by asking the
        resolution spine what every type name means, in the namespace it
        holds.  It used to hold the module's own declarations alone, so a
        data type the module IMPORTED — and returns, or takes — was no data
        type there: ``pick(@Int -> @Colour)`` registered as
        ``(['i64'], 'unsupported')``, and a direct ``match`` on the call, in
        the importer or in the module's own bodies, could not type its
        scrutinee and dropped the enclosing function (E602, then E620 up the
        call graph).  The same declarations compiled as the ENTRY registered
        ``(['i64'], 'i32')``, so the verdict depended on which file was the
        entry.

        What a namespace imports is the ONE derivation the checker's
        module registration reads (:func:`vera.module_view.imported_data_types`),
        asked of the programs as the checker saw them.  The #1317 rename
        rewrites a contended type's references but not the import lists that
        name it, so each imported name is then spelled through THIS
        namespace's renames — the symbol its rewritten signatures carry.

        The prelude's data types are data types in every namespace, as the
        checker's ``TypeEnv`` holds them all unconditionally
        (:func:`vera.prelude.prelude_adt_names`, the floor
        ``_adt_members_in_scope`` completes membership with).  The entry
        file registers the demand-injected ones (``Json``, ``HtmlNode``,
        ``Request``, ``Response``) at Pass 1.2 and re-measures its own
        signatures that named them; a module's are measured here, before
        that, so without them ``mk(@Int -> @Json)`` registered as
        ``unsupported`` and a direct match on the call dropped the function
        (PR #1508 review).  A module's own declaration of one of the names
        keeps its own index (``_sync_alias_env`` only fills a gap), and a
        module alias of one still takes the alias branch first, as in the
        checker.

        #1189: the registrar is handed the module's OWN file, because
        ``_register_fn`` stamps every ``_fn_source_map`` entry with
        ``self.file``; ``ResolvedModule.file_path`` is the attribution source
        ``_module_source_scope`` (#1190) reads, so the source map and the
        diagnostics agree about which file an imported body belongs to.
        """
        from vera.codegen.core import CodeGenerator

        temp = CodeGenerator(source=mod.source, file=str(mod.file_path))
        temp._imported_adt_names = frozenset(
            renames.get(name, name)
            for name in imported_data_types(
                checker_programs[mod.path], checker_programs,
            )
        ) | prelude_adt_names()
        temp._register_all(mod.program)
        return temp

    def _build_namespace_module_reach(
        self,
    ) -> dict[tuple[str, ...] | None, frozenset[tuple[str, ...]]]:
        """The modules each namespace's checker can see (#1513).

        The constructor fallback in `_namespace_ctor_projection` asks this,
        so a constructor the checker resolves among the modules it can see
        is resolved here among the same modules, and one outside them cannot
        make a name ambiguous on this side alone.  The derivation is the
        shared :func:`vera.monomorphize.namespace_module_reach`, which the
        verifier's :func:`~vera.monomorphize.namespace_ctor_owners` reads
        too, so the two sides of the #732 differential resolve a stranger
        constructor among the same modules.
        """
        return namespace_module_reach(
            (mod.path, mod.program) for mod in self._resolved_modules)

    def _build_adt_membership(
        self,
        program: ast.Program,
        declared_adts: dict[tuple[str, ...], frozenset[str]],
        checker_programs: Mapping[tuple[str, ...], ast.Program],
        adt_renames: Mapping[
            tuple[str, ...], tuple[dict[str, str], dict[str, str]]],
    ) -> dict[tuple[str, ...] | None, frozenset[str]]:
        """Which ADT names are data types in each namespace (#1253).

        A namespace holds its OWN declarations, whatever their visibility,
        plus what it IMPORTS — public only, and only the names an explicit
        import list mentions.  That is the checker's view of every module,
        and it is asked of the ONE derivation the checker's module
        registration and each module's registrar read
        (:func:`vera.module_view.imported_data_types`, #1493), so the
        namespace a module's signatures are measured in and the one its
        bodies are compiled in are the same namespace.  An unimported (or
        private) sibling's ADT is as opaque on this side as on the checker's.

        The derivation reads the programs as the checker saw them, and each
        imported name is then spelled through that namespace's own #1317
        renames: the rename rewrites a contended type's references but not
        the import lists that name it, so filtering the rewritten
        declarations by the bare list left a module that imports a renamed
        type — and returns it — without it, and dropped the module's body.

        Keyed by module path, with ``None`` for the entry program, which is
        never renamed.  Built-ins are NOT included: they belong to every
        namespace and are added by the reader (`_adt_members_in_scope`), so
        a namespace's entry stays a statement about source declarations.

        Imports are read per namespace, never inherited: §8.6.4 visibility is
        the importer's property, so a module reached transitively from here is
        a DIRECT import of whichever module names it, and holds exactly what
        THAT module's import list allows.
        """

        def imported(
            ns_program: ast.Program, renames: Mapping[str, str],
        ) -> frozenset[str]:
            return frozenset(
                renames.get(name, name)
                for name in imported_data_types(ns_program, checker_programs)
            )

        main_own = frozenset(
            tld.decl.name for tld in program.declarations
            if isinstance(tld.decl, ast.DataDecl)
        )
        members: dict[tuple[str, ...] | None, frozenset[str]] = {
            None: main_own | imported(program, {}),
        }
        for mod in self._resolved_modules:
            members[mod.path] = (
                declared_adts.get(mod.path, frozenset())
                | imported(checker_programs[mod.path],
                           adt_renames.get(mod.path, ({}, {}))[0])
            )
        # Every ADT some namespace DECLARES.  `_adt_members_in_scope`
        # subtracts this from the registered layouts to recover the global
        # infrastructure — the built-ins plus the PRELUDE's own ADTs, which
        # register after this pass runs and so cannot be snapshotted here.
        self._namespace_declared_adts = frozenset(main_own).union(
            *declared_adts.values()) if declared_adts else frozenset(main_own)
        # #1277: which MODULES declare each ADT name, read from the
        # declarations rather than from `_adt_layouts`, so the Pass-1.2
        # contention rail can see a module's `data Option` at all.  The
        # layout harvest above skips a built-in name outright (the temp
        # generator registers `Option`, `Result`, … for EVERY module,
        # declared or not, so `_adt_layouts` cannot tell the two apart) and
        # `_adt_layout_owners` therefore records only the non-built-in half
        # — which left the rail covering four of the prelude's eight names.
        #
        # EVERY declarer, in resolution order, not the first: contention is
        # a property of each declaration, and a first-wins map made the rail
        # order-dependent.  A library that restates the prelude's `Ordering`
        # answered for a sibling that declares a different one, so importing
        # the restating module first hid the other's contention entirely
        # (check-green, exit 0, the caller silently dropped) while the
        # reverse import order caught it.  Ownership of the LAYOUT stays
        # first-wins in `_adt_layout_owners`, which answers the declaration-
        # index question — the same separation of two questions that keeps
        # `_namespace_declared_adts` out of this one.
        declarers: dict[str, list[tuple[str, ...]]] = {}
        for mod_path, names in declared_adts.items():
            for adt_name in sorted(names):
                declarers.setdefault(adt_name, []).append(mod_path)
        self._module_adt_declarers = {
            name: tuple(paths) for name, paths in declarers.items()
        }
        return members

    # =================================================================
    # #1317 / #187 — per-owner ADT identity
    # =================================================================

    @classmethod
    def _exported_type_mentions(
        cls, decl: ast.Decl, aliases: Mapping[str, ast.TypeExpr],
    ) -> frozenset[str]:
        """Every type name *decl*'s EXPORTED surface mentions (#1317).

        The surface is what a value can cross a namespace boundary through:
        a function's parameters and return type, an ADT's constructor field
        types, an effect or ability operation's parameters and result.  A
        function BODY is deliberately excluded — a type mentioned only
        inside one cannot escape it, and counting it would refuse the
        rename on the very shape #1317 is about (a module that keeps its
        own ``data`` entirely to itself).  Contracts are excluded for the
        same reason: an ``@Shape.0`` in a `requires` names a PARAMETER
        already counted, and adds no route of its own.

        *aliases* are the DECLARING module's own, and the answer is closed
        over them.  A module-local alias is not importable (§8.4.1), so an
        importer can never name one — but a signature written through one
        still carries the underlying type, and reading only the spelling
        misses the crossing entirely.  Measured before the closure existed:
        ``type Sh = Shape;`` with ``aone(@Int -> @Sh)`` and
        ``bone(@Sh -> @Int)`` in two modules whose ``Shape``s differ by
        constructor order compiled clean and answered ``100`` where ``7``
        is correct.  The closure is iterative and bounded by the alias set,
        so a cyclic alias chain terminates rather than recursing.

        What this does NOT reach is the constructor namespace's own crossing
        between an entry file and a module on DIFFERENTLY named types —
        `#1436`, being fixed separately.  The surface answers which TYPE
        names a declaration carries, and two types that share only a
        constructor spelling carry neither of each other's names; the
        constructor axis reads this table through `ctor_reach`, which is
        where that gap is closed rather than here.
        """
        surface: list[object]
        if isinstance(decl, ast.FnDecl):
            surface = [decl.params, decl.return_type, decl.effect]
        elif isinstance(decl, ast.DataDecl):
            surface = [decl.constructors]
        elif isinstance(decl, (ast.EffectDecl, ast.AbilityDecl)):
            # UNREACHABLE today, and deliberately kept.  §8.4.1 makes an
            # effect declaration module-local and not importable, so no
            # caller reaches this arm: the loop that builds the surface
            # tables only asks about a module's PUBLIC declarations, and an
            # effect cannot be one.  It is written for the day effect export
            # lands — the operations are where a value of an ADT would cross
            # a namespace boundary through an effect, so the flow condition
            # needs them the moment that becomes possible, and an arm added
            # then would be an arm nobody thought to add.  Revisit it with
            # whatever makes an effect importable.
            surface = [decl.operations]
        elif isinstance(decl, ast.TypeAliasDecl):
            surface = [decl.type_expr]
        else:
            # FAIL CLOSED (PR review).  An `else: surface = []` reads a
            # declaration kind this dispatch has not learned as mentioning
            # NO types, which is the unsafe direction: the flow condition
            # would stop seeing a crossing that kind carries and the rename
            # would qualify apart two declarations a value can still pass
            # between.  Every whole declaration is walked instead, which
            # over-counts mentions — the safe direction, since an extra
            # mention can only refuse a rename, never admit an unsound one.
            surface = [decl]
        out: set[str] = set()

        def walk(node: object) -> None:
            if isinstance(node, ast.NamedType):
                out.add(node.name)
            elif isinstance(node, (ast.SlotRef, ast.ResultRef)):
                out.add(node.type_name)
            if isinstance(node, ast.Node):
                for f in dc_fields(node):
                    walk(getattr(node, f.name))
            elif isinstance(node, (tuple, list)):
                for item in node:
                    walk(item)

        for part in surface:
            walk(part)
        pending = out & set(aliases)
        expanded: set[str] = set()
        while pending:
            name = pending.pop()
            expanded.add(name)
            before = set(out)
            walk(aliases[name])
            pending |= (out - before) & set(aliases) - expanded
        return frozenset(out)

    def _contended_adt_renames(
        self, program: ast.Program, builtin_adt_names: frozenset[str],
        checker_programs: Mapping[tuple[str, ...], ast.Program],
    ) -> dict[tuple[str, ...], tuple[dict[str, str], dict[str, str]]]:
        """Which module ADTs must be renamed, and what each namespace calls
        them afterwards (#1317, the data half of #187).

        Returns, per module path, the ``({type renames}, {constructor
        renames})`` that namespace's program is rewritten with.  EMPTY for
        every program without a contended name — which is the whole reason
        the corpus's emitted WAT does not move.

        **What is contended.**  A ``data`` name declared by more than one
        MODULE, whose declarations do not all describe one layout
        (:func:`~vera.prelude.data_decl_shape`, the derivation the E609 /
        E621 / E623 rails already share).  A restatement is NOT contended:
        the single registered slot serves both, so renaming it would move
        emitted WAT for no reason.  The CONSTRUCTOR axis is asked
        separately, because the flat constructor registry holds one layout
        per constructor NAME — two modules may declare differently-named
        types that share a constructor spelling (E610's case) — and a
        rename there takes the whole declaration with it, since a
        constructor belongs to its type (§8.5.4 admits it by the type's
        name).

        **What keeps the bare spelling.**  The declaration the ENTRY's bare
        name denotes, if there is one.  That is not a preference: the entry
        program is never rewritten, so a declaration the entry can name
        must keep the spelling the entry writes.  Everything else is
        renamed — which makes every rename a declaration the entry could
        not name, and the relaxation therefore exactly the shape #1317
        calls provably distinct.

        **What is refused instead of renamed.**  A name TWO namespaces'
        imports both supply is ambiguous, and spec §8.5.2.2 refuses it
        rather than picking (E156 at check, E609/E610 as the codegen
        backstop) — so nothing is renamed for such a name and the rail
        speaks as before.  This is the ADT twin of
        :meth:`_declarations_cannot_collide`'s ambiguity condition, and it
        is asked of EVERY namespace, not just the entry's: a rename is only
        sound while each namespace agrees which declaration a bare name
        denotes.

        And a name is refused for a second reason that NAMEABILITY alone
        does not catch: two owners' declarations can MEET in a namespace
        that can name neither, because a VALUE of the type flows between
        them through the signatures the namespace imports.  With
        ``liba::aone(@Int -> @Shape)`` and ``libb::bone(@Shape -> @Int)``
        imported under filters that exclude the type, an entry may still
        write ``bone(aone(6))``: the checker unifies two same-named
        cross-module ADTs, so the composition type-checks, and renaming the
        two apart would hand ``bone`` a value laid out to ``liba``'s tags.
        Measured, before the flow condition existed: a check-green,
        verify-green program returning ``100`` where ``7`` is the answer —
        a silent wrong answer, which is worse than the refusal it replaced.
        So :func:`seen_owners` counts the owners a namespace can reach
        through its imports' TYPE SURFACE as well as by name, and a
        namespace reaching two of them makes the name unrenameable.

        **The prelude is exempt** (maintainer ruling R7): a module ``data``
        named after a prelude ADT stays E621's, exactly as a built-in
        function name stays E151's, an effect name E152's and a built-in
        ADT name E158's.  Per-owner ADT identity is a rule between USER
        modules; the prelude's names are reserved.  Without the exemption
        the rename would dissolve the very pairs E621 exists to refuse.

        **The ENTRY's own declaration is not a party.**  Its contention
        with a module's is E623's (#1312) and that rail is unchanged.  The
        two interact in one direction only: where several modules contend
        with each other AND the entry also declares the name, the entry can
        name none of the modules' declarations, so all of them are renamed
        and E623 correctly has no pair left to report.
        """
        reserved = builtin_adt_names | prelude_adt_names()

        # Per-module declarations, their visibility, and their imports —
        # the three inputs every question below is asked of.
        decls: dict[tuple[str, ...], dict[str, ast.DataDecl]] = {}
        public: dict[tuple[str, ...], set[str]] = {}
        # Each module's OWN alias namespace, read off its declarations.
        # `self._module_type_aliases` is filled by the harvest loop, which
        # runs AFTER this — so `shape()` below would compare declarations
        # through empty maps and read an alias-spelled restatement as a
        # different layout, renaming apart two declarations that
        # `_adt_decls_share_a_layout` (which sees the populated maps) then
        # calls compatible.  Two derivations of "can one layout serve both"
        # disagreeing is exactly what the three rails share a derivation to
        # prevent, so this one is given the same inputs (PR review).
        aliases: dict[tuple[str, ...], dict[str, ast.TypeExpr]] = {}
        alias_params: dict[tuple[str, ...], dict[str, tuple[str, ...]]] = {}
        # Each module's EXPORTED type surface: public declaration name -> the
        # type names its signature mentions.  A value of a type can cross a
        # namespace boundary through any of these even when the type itself
        # is unimportable, which is what the flow condition below reads.
        surface: dict[tuple[str, ...], dict[str, frozenset[str]]] = {}
        imports: dict[tuple[str, ...] | None, dict[
            tuple[str, ...], set[str] | None]] = {
            None: merged_import_filters(program.imports),
        }
        # The modules as the checker saw them: an import filter names a
        # public function by its source name, which the surface is keyed by.
        for path, mod_program in checker_programs.items():
            own: dict[str, ast.DataDecl] = {}
            pub: set[str] = set()
            surf: dict[str, frozenset[str]] = {}
            # Read off the module's own declarations rather than from
            # `_module_type_aliases`, which the harvest loop has not filled
            # yet — this runs at the top of `_register_modules`, ahead of it.
            mod_aliases = {
                tld.decl.name: tld.decl.type_expr
                for tld in mod_program.declarations
                if isinstance(tld.decl, ast.TypeAliasDecl)
            }
            aliases[path] = mod_aliases
            alias_params[path] = {
                tld.decl.name: tld.decl.type_params or ()
                for tld in mod_program.declarations
                if isinstance(tld.decl, ast.TypeAliasDecl)
            }
            for tld in mod_program.declarations:
                d = tld.decl
                if isinstance(d, ast.DataDecl):
                    own.setdefault(d.name, d)
                if (tld.visibility or "private") != "public":
                    continue
                pub.add(d.name)
                surf[d.name] = self._exported_type_mentions(d, mod_aliases)
            decls[path] = own
            public[path] = {
                name for name in pub if name in own
            }
            surface[path] = surf
            imports[path] = merged_import_filters(mod_program.imports)
        # The ENTRY is an owner like any other (#1423).  Its declarations
        # and its own alias namespace are read off `program` for the same
        # reason the modules' are read off theirs: Pass 1 has not registered
        # either yet when this runs.
        entry_decls: dict[str, ast.DataDecl] = {}
        for tld in program.declarations:
            if isinstance(tld.decl, ast.DataDecl):
                entry_decls.setdefault(tld.decl.name, tld.decl)
        entry_declares = set(entry_decls)
        decls[_ENTRY_OWNER] = entry_decls
        aliases[_ENTRY_OWNER] = {
            tld.decl.name: tld.decl.type_expr
            for tld in program.declarations
            if isinstance(tld.decl, ast.TypeAliasDecl)
        }
        alias_params[_ENTRY_OWNER] = {
            tld.decl.name: tld.decl.type_params or ()
            for tld in program.declarations
            if isinstance(tld.decl, ast.TypeAliasDecl)
        }

        # The entry appears once, as `None`; `decls` now also holds it under
        # `_ENTRY_OWNER` so `shape()` can be asked about it, and every walk
        # over MODULE namespaces excludes that key.
        module_paths = [path for path in decls if path != _ENTRY_OWNER]
        namespaces: list[tuple[str, ...] | None] = [None, *module_paths]

        def resolve(
            ns: tuple[str, ...] | None, name: str,
        ) -> tuple[str, ...] | None | _Ambiguous:
            """Which OWNER's declaration does *ns*'s bare *name* denote?

            An owner is a module path, or :data:`_ENTRY_OWNER` for the entry
            file — which is an owner like any other (#1423).  ``None`` when
            the name denotes no user declaration at all (the prelude's, or
            nothing).  :data:`_AMBIGUOUS` when two imports supply it, the
            shape §8.5.2.2 refuses rather than resolves.

            Answering ``_ENTRY_OWNER`` rather than ``None`` for the entry's
            own declaration is what keeps this function's answers and the
            ``decls`` keys in ONE vocabulary.  While they differed, an entry
            declaration added to the rename set was silently dropped when
            the per-namespace maps were built — ``resolve(None, name)`` said
            ``None`` and the owner key said ``()`` — so the guards that stop
            the entry being renamed were inert and could not be tested.
            """
            if name in (entry_declares if ns is None else decls[ns]):
                return _ENTRY_OWNER if ns is None else ns
            suppliers = [
                dep for dep, filt in imports[ns].items()
                if name in public.get(dep, ()) and (
                    filt is None or name in filt)
            ]
            if len(suppliers) > 1:
                return _AMBIGUOUS
            return suppliers[0] if suppliers else None

        def shape(path: tuple[str, ...], name: str) -> object:
            """The declaration's layout key, through ITS OWN aliases.

            §8.4.1 makes an alias module-local, so a declaration resolves
            through the aliases of the module that wrote it and no other —
            the same rule, and the same
            :func:`~vera.prelude.data_decl_shape` derivation, that
            :meth:`_adt_decls_share_a_layout`, ``_contends_with_prelude``
            and ``_check_entry_module_adt_contention`` are asked with.
            """
            return data_decl_shape(
                decls[path][name],
                aliases.get(path, {}),
                alias_params.get(path, {}),
            )

        def seen_owners(
            ns: tuple[str, ...] | None, name: str,
        ) -> set[tuple[str, ...]] | None:
            """Every owner of *name* whose declaration reaches *ns*.

            By NAME — its own declaration, or an import that supplies the
            type — and by FLOW: an imported declaration whose type surface
            mentions *name* hands this namespace values of whichever owner
            the EXPORTING module resolves the name to.  ``None`` when the
            answer is ambiguous, which is refused rather than counted.

            The ENTRY's own declaration counts, under :data:`_ENTRY_OWNER`:
            it is never renamed, so a module declaration renamed out from
            under it would leave E623 with no pair to refuse while the
            entry's own constructors still read a module's value.  It can
            never BE a rename target, since ``()`` is no module's path.

            A namespace that declares the name itself does not count what
            its imports SUPPLY: §8.5.4 shadowing means it can name none of
            them, so they meet nothing here.  What can still reach it is a
            flow, and that is asked separately and unconditionally.
            """
            own = name in (entry_declares if ns is None else decls[ns])
            seen: set[tuple[str, ...]] = set()
            if own:
                seen.add(_ENTRY_OWNER if ns is None else ns)
            for dep, filt in imports[ns].items():
                if dep not in decls:  # pragma: no cover — defensive
                    continue
                supplied = not own and name in public[dep] and (
                    filt is None or name in filt)
                flowed = any(
                    name in mentions and (filt is None or dname in filt)
                    for dname, mentions in surface[dep].items()
                )
                if not (supplied or flowed):
                    continue
                owner = resolve(dep, name)
                if owner is _AMBIGUOUS:
                    return None
                if isinstance(owner, tuple):
                    seen.add(owner)
            return seen

        # Which MODULE declarations own each constructor spelling, and under
        # which of their type names.  Both axes read it: the type axis to
        # check its constructors are unambiguous everywhere before it moves
        # them, and the constructor axis as its own contention input.
        by_ctor: dict[str, dict[tuple[str, ...], set[str]]] = {}
        for path, own in decls.items():
            for name, d in own.items():
                for ctor in d.constructors:
                    by_ctor.setdefault(ctor.name, {}).setdefault(
                        path, set()).add(name)

        def ctor_reach(
            ns: tuple[str, ...] | None, ctor_name: str,
        ) -> set[tuple[str, ...]] | None:
            """Every owner whose declaration of *ctor_name* reaches *ns*.

            §8.5.4 admits a constructor by its TYPE's name, so this is the
            type question asked once per owning type and collected by owner.
            """
            owners: set[tuple[str, ...]] = set()
            for path, names in by_ctor.get(ctor_name, {}).items():
                for name in names:
                    seen = seen_owners(ns, name)
                    if seen is None:
                        return None
                    if path in seen:
                        owners.add(path)
                        break
            return owners

        # A name no namespace resolves unambiguously cannot be renamed:
        # renaming needs every namespace to agree which declaration its bare
        # spelling denotes, and an ambiguous one has no such answer.  Nor can
        # one two owners' declarations MEET in — by name or by flow — since
        # the checker unifies same-named cross-module ADTs and renaming them
        # apart would let a value cross between two layouts.  Asked once,
        # over every namespace, so the two axes below share it.
        def unrenameable(name: str) -> bool:
            if name in reserved:
                return True
            for ns in namespaces:
                if resolve(ns, name) is _AMBIGUOUS:
                    return True
                seen = seen_owners(ns, name)
                if seen is None or len(seen) > 1:
                    return True
            return False

        def ctor_unrenameable(ctor_name: str) -> bool:
            """The constructor namespace's own ambiguity condition.

            Two owners' declarations of one constructor spelling that a
            namespace can reach BOTH of leave its bare use ambiguous
            (§8.5.2.2, E157) — and a rename would answer it by fiat, since
            the rewrite maps that namespace's bare ``Sq`` to exactly one
            owner's symbol.  So the pair stays refused, and E610 keeps its
            backstop.  Asked separately from the type axis because the
            spellings are independent: two DIFFERENTLY-named types can
            share a constructor and be a clash on the constructor alone.
            """
            for ns in namespaces:
                reach = ctor_reach(ns, ctor_name)
                if reach is None or len(reach) > 1:
                    return True
            return False

        def decl_unrenameable(path: tuple[str, ...], name: str) -> bool:
            """A declaration moves whole or not at all, so BOTH namespaces
            have to admit it — §8.5.4 ties a constructor to its type."""
            return unrenameable(name) or any(
                ctor_unrenameable(ctor.name)
                for ctor in decls[path][name].constructors
            )

        renamed: set[tuple[tuple[str, ...], str]] = set()

        # -------- the TYPE axis (E609) --------
        by_name: dict[str, list[tuple[str, ...]]] = {}
        for path, own in decls.items():
            for name in own:
                by_name.setdefault(name, []).append(path)
        for name, owners in by_name.items():
            if len(owners) < 2:
                continue
            if any(decl_unrenameable(path, name) for path in owners):
                continue
            shapes = {path: shape(path, name) for path in owners}
            if len(set(shapes.values())) < 2:
                continue  # every declaration describes the one layout
            # Which shape KEEPS the bare slot.  The entry's whenever it
            # declares the name: its program is the one codegen was handed
            # and is never rewritten, so the spelling it writes has to go on
            # meaning its own declaration.  Otherwise the declaration the
            # entry's bare name denotes, and otherwise nothing.
            keeper = resolve(None, name)
            keeps = (
                shapes[keeper]
                if isinstance(keeper, tuple) and keeper in shapes
                else _NOTHING
            )
            # The ENTRY is never a rename target, and needs no guard here to
            # say so: it is in `owners` exactly when it declares the name,
            # which is exactly when `resolve` names it the keeper, so its
            # shape IS `keeps` and the comparison below skips it.  Pinned by
            # `test_the_entry_keeps_the_bare_slot` rather than by a branch
            # that cannot fire.
            for path in owners:
                if shapes[path] != keeps:
                    renamed.add((path, name))

        # -------- the CONSTRUCTOR axis (E610) --------
        # Two modules may declare DIFFERENTLY-named types that share a
        # constructor spelling, and the flat constructor registry holds one
        # layout per constructor name.  The whole declaration moves, not just
        # the constructor: §8.5.4 admits a constructor by its type's name, so
        # splitting them would leave a type holding a constructor it no longer
        # names.
        for ctor_name, owners_types in by_ctor.items():
            if len(owners_types) < 2:
                continue
            pairs = {
                (name, shape(path, name))
                for path, names in owners_types.items() for name in names
            }
            if len(pairs) < 2:
                continue  # one type, restated; the single slot serves both
            if any(decl_unrenameable(path, name)
                   for path, names in owners_types.items() for name in names):
                continue
            keeps_ctor = {
                path for path, names in owners_types.items()
                if any(resolve(None, name) == path for name in names)
            }
            if len(keeps_ctor) > 1:  # pragma: no cover — `ctor_unrenameable`
                continue             # already refused every such pair
            for path, names in owners_types.items():
                if path in keeps_ctor:
                    continue
                for name in names:
                    renamed.add((path, name))

        if not renamed:
            return {}

        # -------- what each namespace calls them afterwards --------
        # Read through :func:`resolve`, so an IMPORTER of a renamed
        # declaration renames its references in lockstep with the declaring
        # module: `entry -> mid -> deep` keeps one answer for `Shape`.
        out: dict[tuple[str, ...], tuple[dict[str, str], dict[str, str]]] = {}
        for ns in namespaces:
            types: dict[str, str] = {}
            ctors: dict[str, str] = {}
            for owner, name in renamed:
                if resolve(ns, name) != owner:
                    continue
                prefix = "mod$" + "$".join(owner) + "$"
                types[name] = prefix + name
                for ctor in decls[owner][name].constructors:
                    ctors[ctor.name] = prefix + ctor.name
            if ns is None:
                # The entry program is NOT rewritten, so a rename it can name
                # would leave its own references dangling.  By construction
                # the keeper IS the entry's resolution, so this is empty; it
                # is asserted rather than assumed because the alternative
                # failure is silent (an unresolvable constructor reported as
                # an E602 skip, not as this rule being wrong).
                if types or ctors:  # pragma: no cover — defended, not reached
                    return {}
                continue
            if types or ctors:
                out[ns] = (types, ctors)
        # The display table is DERIVED, not remembered: its values come from
        # `display_adt_name`, the one strip every user-facing surface uses,
        # so the prose rewrite at the diagnostic boundary and the constructor
        # head `show` bakes into the data section cannot answer differently.
        self._contended_adt_display_names = {
            mangled: display_adt_name(mangled)
            for types, ctors in out.values()
            for mangled in (*types.values(), *ctors.values())
        }
        return out

    def _adt_decls_share_a_layout(
        self, name: str, path_a: tuple[str, ...], path_b: tuple[str, ...],
    ) -> bool:
        """Do two modules' ``data {name}`` declarations describe one layout?

        The ADT arm of the one-layout-per-name question
        (:func:`~vera.prelude.data_decl_shape`), asked between two IMPORTED
        modules (#1317) as :meth:`~CodeGenerator._contends_with_prelude` asks
        it of a module against the prelude (#1277) and
        :meth:`~CodeGenerator._check_entry_module_adt_contention` of the entry
        file against a module (#1312).  One derivation of "can the single
        registered slot serve both", so the three rails cannot disagree about
        which declarations are compatible.

        Each declaration's field types resolve through the aliases of ITS OWN
        module, never the other's — §8.4.1 makes an alias module-local, and
        resolving one module's spelling through another's maps would let a
        coincidentally-named alias collapse two incompatible layouts onto one
        key.

        A declaration this cannot find is treated as NOT sharing, the safe
        direction: the alternative is registering one layout for two shapes
        it may not fit.
        """
        decl_a = self._find_module_data_decl(path_a, name)
        decl_b = self._find_module_data_decl(path_b, name)
        if decl_a is None or decl_b is None:  # pragma: no cover — defensive
            return False
        return data_decl_shape(
            decl_a,
            self._module_type_aliases.get(path_a, {}),
            self._module_type_alias_params.get(path_a, {}),
        ) == data_decl_shape(
            decl_b,
            self._module_type_aliases.get(path_b, {}),
            self._module_type_alias_params.get(path_b, {}),
        )

    def _collect_namespace_fn_names(self, program: ast.Program) -> None:
        """Which FUNCTION names each namespace can name (#1299).

        Read off the LINKED programs (`vera.binding.link`): a namespace holds
        its own top-level declarations and what its import list admits, and
        every module declaration and every `where` helper is a `$`-bearing
        link name there, so the bare names a module's body can name are the
        prelude's alone, and the entry's body names its own and the
        prelude's.  :meth:`~CodeGenerator._scoped_fn_names` narrows the flat
        ``_fn_sigs`` registry with it before the #1284 ownership predicate
        reads it, so a module body's bare `get` is the operation even where
        the entry declares a `get`, and the VERIFIER narrows its discovery
        with the same tables (#1299), built by the same shared derivation
        (:func:`~vera.monomorphize.namespace_fn_names`) over the same linked
        programs, so the two sides of the #732 differential discover the
        same clones.

        Called twice: before ``_register_modules``, and again after the
        prelude pass, once ``_prelude_fn_names`` is populated, because the
        prelude's combinators are visible in every namespace and the first
        call cannot know them yet.  The derivation is pure, so the second
        call simply replaces the first's answer.  Route three of #1299 (a
        ``forall<T>`` parent's ``where`` helper) involves no imports at all,
        so the entry program needs its set whether or not any module exists.
        """
        tables = namespace_fn_names(
            program,
            [(mod.path, mod.program) for mod in self._resolved_modules],
            prelude=self._prelude_fn_names,
        )
        self._namespace_tables = tables
        self._namespace_fn_names = dict(tables.by_namespace)
        # #1316: and the PRELUDE's own namespace, whose declarations are its
        # combinators and nothing else.  Pass 2 compiles a prelude body under
        # `_module_alias_scope(PRELUDE_NAMESPACE)`, and `_scoped_fn_names`
        # reads the installed namespace's entry — so without this a bare call
        # from one combinator to another would find an EMPTY lexical set and
        # the #1284 ownership predicate would stop calling them user-owned.
        # Empty before the prelude pass populates `_prelude_fn_names`, which
        # is why the second of this method's two calls is the one that fills
        # it; nothing enters the prelude scope in between.
        if self._prelude_fn_names:
            self._namespace_fn_names[PRELUDE_NAMESPACE] = frozenset(
                self._prelude_fn_names,
            )

    def _check_cross_module_calls(self, program: ast.Program) -> None:
        """Detect calls code generation has no function for.

        Walks every function body it compiles, the entry's and each imported
        module's, for FnCall/ModuleCall nodes whose targets have no
        definition.  Emits a proper Vera diagnostic instead of letting
        invalid WAT reach wasmtime.
        """
        # The names the codegen knows about.  Over the linked program every
        # call the resolver pass binds names its target's link name, which
        # is registered, so a name missing here is a call the pass bound to
        # nothing: a function no namespace declares, or one it does not see
        # (a private helper of another module, a declaration of a module
        # reached only transitively, spec §8.6.4), whose module declaration
        # is registered under its link name and not this spelling.
        known: set[str] = set(self._fn_sigs.keys())
        for layouts in self._adt_layouts.values():
            known.update(layouts.keys())
        # Every name `_translate_call` lowers in place of a call: the
        # registry's built-ins with an emitter and its ability intrinsics,
        # and the names the dispatch reads that are neither.
        known.update(INTRINSICS)
        known.update(_DISPATCHED_NAMES)

        seen: set[str] = set()  # deduplicate by function name

        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and not decl.forall_vars:
                self._scan_body_for_unknown_calls(
                    decl.body, known, seen,
                )
        # An imported body is linked like the entry's, so the same rule
        # holds there, and its diagnostic names its own file (#1186).
        for path, idecl in self._imported_fn_decls:
            with self._module_source_scope(path):
                self._scan_body_for_unknown_calls(idecl.body, known, seen)

    def _scan_body_for_unknown_calls(
        self,
        node: ast.Node,
        known: set[str],
        seen: set[str],
    ) -> None:
        """Recursively walk an AST node looking for unresolved calls."""
        if isinstance(node, ast.ModuleCall):
            # The link step rewrites every qualified call the resolver pass
            # binds into a plain call (`vera.binding.link`), so one still
            # here names nothing this program can call.
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
            "against.  The checker refuses a call that names nothing (E200, "
            "E230, E233), and a call to an operation of a user-declared "
            "ability (E340), so a call reaching this was compiled without "
            "being checked."
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
