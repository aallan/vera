"""Mixin for cross-module registration and call detection (C7e).

Handles Pass 0 (module registration) and Pass 1.9 (cross-module
call detection) of the code generation pipeline.
"""

from __future__ import annotations

import contextlib
from collections.abc import Iterator
from typing import TYPE_CHECKING

from vera import ast
from vera.builtins import INTRINSICS
from vera.errors import Diagnostic, SourceLocation
from vera.monomorphize import (
    canonicalize_type_aliases,
    namespace_fn_names,
)
from vera.prelude import PRELUDE_NAMESPACE, prelude_adt_names

if TYPE_CHECKING:
    from vera.codegen.core import CodeGenerator
    from vera.resolver import ResolvedModule


#: The names `_translate_call` dispatches that are not in the built-in
#: registry's `INTRINSICS`: closure application, the `Eq` and `Ord`
#: operations it rewrites, and the effect operations a handler or an
#: effect row binds.
_DISPATCHED_NAMES: frozenset[str] = frozenset({
    "apply_fn", "eq", "compare", "get", "put", "throw", "resume",
})

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
           function signatures, ADT layouts, and type aliases.  Every
           declaration is under its link name (`vera.binding.link`), so no
           two modules' declarations share a key.
        3. Inject into ``self._fn_sigs`` via ``setdefault``.
        4. Collect all imported FnDecls for compilation in Pass 2.5.
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
        # to the helper's link name (`vera.binding.DeclId`) — so two imported modules' same-named
        # nested generics stay DISTINCT bases instead of collapsing first-seen-wins
        # (which left a lying namesake unemitted/unverified: a false Tier-1).  The
        # main program keeps the bare prefix (core.py Pass 0).
        #
        # Pre-register builtin ADTs so the harvest below can tell them from a
        # module's.  Every CodeGenerator registers Option, Result, Ordering,
        # UrlParts, Tuple, MdInline, MdBlock, etc. via _register_builtin_adts()
        # — they are global infrastructure, not owned by any particular module.
        # The call writes `_adt_layouts` and nothing else, and is idempotent.
        self._register_builtin_adts()
        builtin_adt_names: frozenset[str] = frozenset(self._adt_layouts.keys())

        # Every module's data types, aliases and constructors already carry
        # their link names (`vera.binding.link`), so two modules' same-named
        # declarations are two names here and no namespace's harvest can take
        # another's slot (#1694).
        self._resolved_modules = [
            dataclasses.replace(
                mod,
                program=self._hoist_nongeneric_where_helpers(
                    qualify_nested_generic_decls(mod.program),
                ),
            )
            for mod in self._resolved_modules
        ]

        # #1253: per-namespace ADT bookkeeping, filled in the harvest loop and
        # folded into membership sets after it.
        declared_adts: dict[tuple[str, ...], frozenset[str]] = {}

        # 2. Register each module in ITS OWN namespace (#1493): its own
        #    declarations, with the data types it imports in scope.
        for mod in self._resolved_modules:
            temp = self._module_registrar(mod)
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

            # #1253: what this module DECLARES as data types, by their link
            # names.  With what it imports that is its membership below: a
            # module's namespace holds its own ADTs whatever their
            # visibility, which is exactly the checker's view.
            declared_adts[mod.path] = frozenset(
                tld.decl.name
                for tld in mod.program.declarations
                if isinstance(tld.decl, ast.DataDecl)
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
                # any imported module.
                if adt_name in builtin_adt_names:
                    continue

                # #1008: register EVERY module ADT's layout
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
        self._adt_namespace_members = self._build_adt_membership(
            program, declared_adts,
        )

    def _module_registrar(self, mod: ResolvedModule) -> CodeGenerator:
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

        What a namespace imports is what the resolver pass bound its names
        to (:attr:`vera.binding.Binding.types`), each by its link name, which
        is the name its signatures carry in the linked program.

        The prelude's data types are data types in every namespace, as the
        checker's ``TypeEnv`` holds them all unconditionally
        (:func:`vera.prelude.prelude_adt_names`, the floor
        ``_adt_members_in_scope`` completes membership with).  The entry
        file registers the demand-injected ones (``Json``, ``HtmlNode``,
        ``Request``, ``Response``) at Pass 1.2 and re-measures its own
        signatures that named them; a module's are measured here, before
        that, so without them ``mk(@Int -> @Json)`` registered as
        ``unsupported`` and a direct match on the call dropped the function
        (PR #1508 review).

        #1189: the registrar is handed the module's OWN file, because
        ``_register_fn`` stamps every ``_fn_source_map`` entry with
        ``self.file``; ``ResolvedModule.file_path`` is the attribution source
        ``_module_source_scope`` (#1190) reads, so the source map and the
        diagnostics agree about which file an imported body belongs to.
        """
        from vera.codegen.core import CodeGenerator

        temp = CodeGenerator(
            self._typed, source=mod.source, file=str(mod.file_path))
        temp._imported_adt_names = (
            self._imported_type_link_names(mod.path) | prelude_adt_names())
        temp._register_all(mod.program)
        return temp

    def _imported_type_link_names(
        self, owner: tuple[str, ...],
    ) -> frozenset[str]:
        """The data types namespace *owner* imports, by their link names:
        the names the resolver pass bound to another namespace's ``data``."""
        binding = self._binding
        if binding is None:
            return frozenset()
        return frozenset(
            ident.link_name
            for ident in binding.types.get(owner, {}).values()
            if ident.kind == "data" and ident.owner != owner
        )

    def _build_adt_membership(
        self,
        program: ast.Program,
        declared_adts: dict[tuple[str, ...], frozenset[str]],
    ) -> dict[tuple[str, ...] | None, frozenset[str]]:
        """Which ADT names are data types in each namespace (#1253).

        A namespace holds its OWN declarations, whatever their visibility,
        plus what it IMPORTS — public only, and only the names an explicit
        import list mentions: what the resolver pass bound its type names to
        (:meth:`_imported_type_link_names`), which is the checker's view of
        every module.  Every name is a link name, so a type a namespace
        cannot name is no member of it, and an unimported (or private)
        sibling's ADT is as opaque on this side as on the checker's.

        Keyed by module path, with ``None`` for the entry program.
        Built-ins are NOT included: they belong to every namespace and are
        added by the reader (`_adt_members_in_scope`), so a namespace's
        entry stays a statement about source declarations.
        """
        from vera.binding import ENTRY

        main_own = frozenset(
            tld.decl.name for tld in program.declarations
            if isinstance(tld.decl, ast.DataDecl)
        )
        members: dict[tuple[str, ...] | None, frozenset[str]] = {
            None: main_own | self._imported_type_link_names(ENTRY),
        }
        for mod in self._resolved_modules:
            members[mod.path] = (
                declared_adts.get(mod.path, frozenset())
                | self._imported_type_link_names(mod.path)
            )
        # Every ADT some namespace DECLARES.  `_adt_members_in_scope`
        # subtracts this from the registered layouts to recover the global
        # infrastructure — the built-ins plus the PRELUDE's own ADTs, which
        # register after this pass runs and so cannot be snapshotted here.
        self._namespace_declared_adts = frozenset(main_own).union(
            *declared_adts.values()) if declared_adts else frozenset(main_own)
        return members

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
        # One code for both: the condition is one, a call with no target.
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
                error_code="E624",
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
                error_code="E624",
            ))

    # -----------------------------------------------------------------
    # Cross-module call detection
    # -----------------------------------------------------------------
