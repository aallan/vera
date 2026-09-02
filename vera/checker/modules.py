"""Mixin for cross-module registration (C7b/C7c).

Extracted from ``core.py`` so that import-related logic lives in its
own file while the main :class:`TypeChecker` stays focused on
single-module checking.
"""

from __future__ import annotations

from dataclasses import replace

from vera import ast
from vera.environment import TypeEnv
from vera.monomorphize import namespace_adt_names, namespace_fn_names
from vera.registration import where_helper_parents
from vera.resolver import ResolvedModule


class ModulesMixin:
    """Methods for registering declarations from resolved modules."""

    def _register_modules(self, program: ast.Program) -> None:
        """Register declarations from resolved modules (C7b/C7c).

        1. Build an import-name filter from the program's ``import``
           declarations (selective vs wildcard).
        1a. #1304: refuse a bare function, data-type or constructor name
           two of this namespace's imports both supply, and keep it out of
           the environment.
        2. For each resolved module, run the registration pass in an
           isolated TypeChecker to populate its ``TypeEnv``, then
           harvest the declarations into per-module dicts.
        3. C7c: filter to public declarations only.  Store unfiltered
           dicts for better "is private" error messages.
        4. C7c: emit errors when selective imports reference private names.
        5. Inject selectively imported *public* names into ``self.env`` so
           bare calls (``abs(42)`` after ``import vera.math(abs)``)
           resolve through the normal ``_check_call_with_args`` path.
        """
        from vera.checker.core import TypeChecker

        # 1. Build import filter
        for imp in program.imports:
            self._import_names[imp.path] = (
                set(imp.names) if imp.names is not None else None
            )

        # Snapshot builtin names (TypeEnv registers builtins in __post_init__).
        # Hoisted above the #1304 refusal, which needs them: every injection
        # below is a ``setdefault`` onto this same environment, so a name the
        # built-in registry already holds is never won by an import and is
        # therefore never ambiguous, however many dependencies export it.
        _builtins = TypeEnv()
        builtin_fn_names = set(_builtins.functions)
        builtin_data_names = set(_builtins.data_types)
        builtin_ctor_names = set(_builtins.constructors)

        # 1a. #1304.
        self._reject_ambiguous_imports(
            program, builtin_fn_names, builtin_data_names, builtin_ctor_names,
        )

        # 2. Register each module in isolation, harvest declarations
        for mod in self._resolved_modules:
            # Pass the module's file path so any harvested diagnostic (e.g. the
            # E151 below) carries `location.file`, matching every other
            # diagnostic; `temp` is built with the module's own source/path.
            temp = TypeChecker(source=mod.source, file=str(mod.file_path))
            temp._register_all(mod.program)

            # #815: surface E151 (a module fn redefining a built-in) into the
            # importer.  ``temp`` is built with the module's own source, so
            # these diagnostics already carry the correct module-file location
            # and source line.  Without this, a module imported but never
            # checked standalone would let the redefinition through silently —
            # the importer's verifier reasons with the built-in's model while
            # the module's body runs (verify proves, run violates).
            # #1149: E152 (a module redeclaring a built-in EFFECT) is surfaced
            # on the same grounds — the block is invisible to codegen, which
            # routes the qualified call to the host import regardless, so an
            # unchecked module would miscompile the importer.
            # #1181/#1187: E153 (a module fn named after a contract state form
            # or a grammar keyword) likewise — a module imported but never
            # checked standalone would otherwise carry a declaration no
            # importer could ever bare-call.
            self.errors.extend(
                e for e in temp.errors
                if e.error_code in ("E151", "E152", "E153", "E154")
            )

            # #1244: and CHECK the module's bodies, under ITS OWN import
            # filter.  Registration alone says what a module declares; it
            # says nothing about whether the module's bodies resolve, so a
            # name a module never imported was accepted whenever the module
            # was reached AS AN IMPORT and rejected when the same file was
            # checked directly — one program, two verdicts by entry point,
            # with the lenient one leaking names across a module boundary
            # the spec draws (§8.5.1).  The verifier has honoured the
            # module-local rule regardless of entry point since #1225; this
            # is the checker catching up.
            self._check_module_bodies(mod)

            # All module-declared names (exclude builtins)
            all_fns = {
                k: v for k, v in temp.env.functions.items()
                if k not in builtin_fn_names or v.span is not None
            }
            all_data = {
                k: v for k, v in temp.env.data_types.items()
                if k not in builtin_data_names
            }

            # C7c: keep unfiltered dicts for "is private" error messages
            self._module_all_functions[mod.path] = all_fns
            self._module_all_data_types[mod.path] = all_data

            # 3. C7c: filter to public only
            mod_fns = {
                k: v for k, v in all_fns.items()
                if self._is_public(v.visibility)
            }
            mod_data = {
                k: v for k, v in all_data.items()
                if self._is_public(v.visibility)
            }
            # Constructors: include only from public ADTs
            public_adt_ctors: set[str] = set()
            for dt_info in mod_data.values():
                public_adt_ctors.update(dt_info.constructors)
            mod_ctors = {
                k: v for k, v in temp.env.constructors.items()
                if k not in builtin_ctor_names
                and k in public_adt_ctors
            }

            self._module_functions[mod.path] = mod_fns
            self._module_data_types[mod.path] = mod_data
            self._module_constructors[mod.path] = mod_ctors

            # 4. C7c: check selective imports for private names
            name_filter = self._import_names.get(mod.path)
            mod_label = ".".join(mod.path)
            if name_filter is not None:
                imp_node = self._find_import_decl(program, mod.path)
                mod_helpers = where_helper_parents(
                    tld.decl for tld in mod.program.declarations
                    if isinstance(tld.decl, ast.FnDecl)
                )
                for name in sorted(name_filter):
                    priv_fn = all_fns.get(name)
                    priv_dt = all_data.get(name)
                    if (priv_fn is not None
                            and not self._is_public(priv_fn.visibility)):
                        self._error(
                            imp_node,
                            f"Cannot import '{name}' from module "
                            f"'{mod_label}': it is private.",
                            rationale=(
                                "Only public declarations can be imported."
                            ),
                            fix=(
                                f"Mark '{name}' as public in the module, "
                                f"or remove it from the import list."
                            ),
                            spec_ref=(
                                'Chapter 8, Section 8.4 '
                                '"Visibility"'
                            ),
                            error_code="E150",
                        )
                    elif (priv_dt is not None
                            and not self._is_public(priv_dt.visibility)):
                        self._error(
                            imp_node,
                            f"Cannot import '{name}' from module "
                            f"'{mod_label}': it is private.",
                            rationale=(
                                "Only public declarations can be imported."
                            ),
                            fix=(
                                f"Mark '{name}' as public in the module, "
                                f"or remove it from the import list."
                            ),
                            spec_ref=(
                                'Chapter 8, Section 8.4 '
                                '"Visibility"'
                            ),
                            error_code="E150",
                        )
                    elif name in mod_helpers:
                        # #1307: a helper is not a module-level declaration
                        # at all, so it is absent from the tables above —
                        # the name is refused here on the module's own AST.
                        owners = ", ".join(
                            f"'{o}'" for o in sorted(mod_helpers[name])
                        )
                        self._error(
                            imp_node,
                            f"Cannot import '{name}' from module "
                            f"'{mod_label}': it is a where-helper of "
                            f"{owners}, not a declaration of the module.",
                            rationale=(
                                "Only a module's public top-level "
                                "declarations can be imported.  A function "
                                "declared in a `where` block is local to the "
                                "function that declares it — it takes no "
                                "visibility modifier and is not part of the "
                                "module's namespace."
                            ),
                            fix=(
                                f"Remove '{name}' from the import list and "
                                f"call {owners} instead, or — if the helper "
                                f"is meant to be shared — lift it out of the "
                                f"`where` block to a top-level 'public fn "
                                f"{name}(...)' in that module."
                            ),
                            spec_ref=(
                                'Chapter 5, Section 5.8 '
                                '"Function Visibility"'
                            ),
                            error_code="E150",
                        )

            # 5. Inject public names into main env for bare calls.
            #
            # #890: only a DIRECTLY-imported module's public declarations are
            # visible to the top-level importer (spec §8.6.4 — a transitive
            # module reached only through another module's imports is *not*
            # transitively visible here).  A transitive module is still in
            # ``self._resolved_modules`` so codegen can compile the bodies that
            # call into it, but its names must not enter the importer's bare
            # namespace, and its qualified-call registries above stay unset for
            # it — ``main`` can neither bare-call nor ``base::``-call it.
            if not mod.direct:
                continue
            for fn_name, fn_info in mod_fns.items():
                # #1304: an ambiguous name is not injected AT ALL.  Injecting
                # one supplier and reporting the clash beside it would leave
                # the follow-on diagnostics keyed to whichever module the
                # injection loop reached first — the very artefact this
                # refusal removes — so the name simply denotes nothing here,
                # and a bare call to it misses (E200) rather than binding a
                # body chosen by iteration order.  Module-qualified calls are
                # unaffected: they resolve against
                # ``_module_functions[path]``, never this environment.
                if fn_name in self._ambiguous_import_fn_names:
                    continue
                if name_filter is None or fn_name in name_filter:
                    self.env.functions.setdefault(fn_name, fn_info)
            # #1304, data side: same rule and same reason as the functions
            # above.  A type name two imports supply denotes nothing here, and
            # so does a constructor name — which is filtered by its PARENT
            # type (spec §8.5.4), so the two sets are consulted separately.
            for dt_name, dt_info in mod_data.items():
                if dt_name in self._ambiguous_import_type_names:
                    continue
                if name_filter is None or dt_name in name_filter:
                    self.env.data_types.setdefault(dt_name, dt_info)
            for ct_name, ct_info in mod_ctors.items():
                if ct_name in self._ambiguous_import_ctor_names:
                    continue
                parent = ct_info.parent_type
                if name_filter is None or parent in name_filter:
                    self.env.constructors.setdefault(ct_name, ct_info)

    def _reject_ambiguous_imports(
        self, program: ast.Program,
        builtin_fns: set[str], builtin_types: set[str],
        builtin_ctors: set[str],
    ) -> None:
        """Refuse a bare name two of THIS namespace's imports supply (#1304).

        Spec §8.5 orders a local declaration against an import (§8.5.2) and
        prescribes the module-qualified form for reaching what a clash hides
        (§8.5.3), but it defines no order between two imports that both
        supply one name.  Neither did the implementation: the pick was a
        set-iteration artefact, and one unchanged program accepted on one run
        and reported ``body has type Bool`` on the next.  Refusing is what
        DESIGN.md's explicitness (§0.2.2) and constrained-expressiveness
        (§0.2.6) priorities give — an order would make the winning binding
        implicit in import sequence, and would let a dependency ADDING an
        export silently rebind a downstream bare call.

        DEFINITION-GATED, not use-gated: the clash is refused because the
        import pair exists, whether or not any body names it.  That is the
        semantics codegen's E608 rail already has — a program importing two
        suppliers and never calling either is E608 today — so the two layers
        answer one question the same way, which is the whole of #1304's
        complaint about three phases each deciding independently.  Both read
        :func:`~vera.monomorphize.namespace_fn_names`; this side asks for its
        OWN namespace's clashes (to report at its own import, and to keep the
        name unbound), the E608 side asks the union (to decide whether a PAIR
        of modules may share the flat namespace).

        Reported once per clashing name, at the LAST import that supplies it
        — the one whose presence completes the clash — and in sorted name
        order, so the diagnostic stream is a function of the source alone.

        Every namespace gets its own pass: the entry program here, and each
        module's through the fresh checker :meth:`_check_module_bodies`
        builds for it, whose diagnostics are surfaced into this one.  That is
        what makes the refusal reach a module the entry program only imports
        — the shape §8.5 left undefined and the only one where the flap was
        observable, since E608 already refused the entry-visible pair.

        THREE NAMESPACES, three codes, mirroring the split codegen's rails
        already use: functions (E155, backstopped by E608), data types (E156,
        by E609) and constructors (E157, by E610).  One code would have been
        cheaper and wrong — a constructor clash is not a type clash (two
        modules exporting differently-named ADTs can share a constructor
        name, and only E610 catches that today), and the registry's existing
        convention is one code per declaration namespace.

        The data side flapped exactly as the function side did — measured on
        two modules each exporting a ``public data Shape`` with different
        constructor field types, where ``Sq(3)`` type-checked on some hash
        seeds and was ``E213`` on others.  Its accepting seeds were the worse
        half: ``check`` and ``verify`` both passed, and the program then died
        at ``run`` with an ``E609`` located at line 0 of the entry file,
        naming two modules the entry never imported.

        Unlike the function side, the data side has no in-source escape
        hatch: E609/E610 refuse two modules' same-named ADTs by DECLARATION,
        with no visibility, filter, or shadowing relaxation (E608 got one in
        #1281; E609 did not).  Measured — narrowing the second import to
        exclude the type, and declaring the type locally, both leave the
        program ``E609`` at compile.  So these two diagnostics prescribe
        renaming, which is what actually works, rather than repeating the
        function side's remedies.  Every program they refuse is one
        E609/E610 already refused later and less precisely, so this moves a
        rejection rather than adding one.

        A name the BUILT-IN registry already owns is never ambiguous: every
        injection below is a ``setdefault`` onto an environment the built-ins
        populated first, so the incumbent wins and the imports never compete.
        The three snapshots are passed in for that reason, and not passing
        the function one was an over-refusal in this method's first version —
        two dependencies exporting their own ``option_map`` were reported as
        a clash when a bare ``option_map`` in fact resolves to the prelude's.
        """
        modules = [(mod.path, mod.program) for mod in self._resolved_modules]
        fn_clashes = namespace_fn_names(
            program, modules, prelude=builtin_fns,
        ).ambiguous_in(None)
        adt = namespace_adt_names(
            program, modules,
            owned_types=builtin_types, owned_ctors=builtin_ctors,
        )
        type_clashes = adt.types_in(None)
        ctor_clashes = adt.ctors_in(None)
        self._ambiguous_import_fn_names = frozenset(fn_clashes)
        self._ambiguous_import_type_names = frozenset(type_clashes)
        self._ambiguous_import_ctor_names = frozenset(ctor_clashes)

        for clashes, kind, article, code in (
            (fn_clashes, "function", "a", "E155"),
            (type_clashes, "data type", "a", "E156"),
            (ctor_clashes, "constructor", "a", "E157"),
        ):
            # Sorted, because the docstring above promises sorted name
            # order and the producers hand this back in IMPORT order —
            # deterministic (measured stable across hash seeds), but not
            # what the contract says.  Sorting by NAME leaves each name's
            # supplier list alone, which is the ordering
            # `ambiguous_in` deliberately keeps in import order so the
            # report can name the import that completed the clash
            # (#1330 review).
            for name, deps in sorted(clashes.items()):
                labels = [".".join(dep) for dep in deps]
                joined = ", ".join(f"'{label}'" for label in labels[:-1])
                joined = f"{joined} and '{labels[-1]}'"
                self._error(
                    self._find_import_decl(program, deps[-1]),
                    f"Bare {kind} name '{name}' is supplied by more than one "
                    f"import: modules {joined}.",
                    rationale=(
                        f"Two imports supplying one bare {kind} name leave it "
                        "ambiguous. The language defines no order between "
                        f"them, so a use of '{name}' here would name "
                        f"{article} declaration chosen by import sequence "
                        "rather than by the program's text — and a dependency "
                        "later adding this export would silently rebind it."
                    ),
                    fix=(
                        self._ambiguous_fn_fix(name, labels)
                        if code == "E155"
                        else self._ambiguous_data_fix(name, kind, labels)
                    ),
                    spec_ref=(
                        'Chapter 8, Section 8.5.2.2 '
                        '"Two Imports Supplying One Name"'
                    ),
                    error_code=code,
                )

    @staticmethod
    def _ambiguous_fn_fix(name: str, labels: list[str]) -> str:
        """The two remedies that work for a clashing FUNCTION name (#1304).

        Both measured end to end, through to the runtime value: narrowing one
        import leaves a single supplier, and a local declaration takes every
        bare call while leaving each import reachable under ``::``.
        """
        return (
            f"Import at most one supplier of '{name}': name the other "
            f"import's declarations selectively, as "
            f"'import {labels[-1]}(<other-name>);' (replace <other-name> "
            f"with a declaration you need from that module). To keep "
            f"reaching both, declare '{name}' in this file — a local "
            "declaration takes every bare call — and use the "
            f"module-qualified form '{labels[0]}::{name}(...)' for the "
            "imported ones."
        )

    @staticmethod
    def _ambiguous_data_fix(name: str, kind: str, labels: list[str]) -> str:
        """The remedy that works for a clashing TYPE or CONSTRUCTOR name.

        Renaming, and only renaming.  The function side's two remedies are
        deliberately NOT offered here: both were measured against this shape
        and both still fail at compile with E609, because that rail refuses
        two modules' same-named data declarations however the importer
        filters or shadows them (spec §11.16).
        """
        return (
            f"Rename the {kind} '{name}' in one of the two modules — "
            f"'{labels[0]}' or '{labels[-1]}'. Narrowing an import or "
            f"declaring '{name}' in this file does not resolve it: "
            "compilation refuses two modules' same-named data declarations "
            "whatever the importer does with them."
        )

    def _check_module_bodies(self, mod: ResolvedModule) -> None:
        """Type-check *mod*'s bodies as *mod* itself would be checked (#1244).

        A fresh checker over the module's own program, given the module's own
        imports — so every name its bodies mention is resolved against the
        namespace ITS file declares and imports, not the entry program's.  Its
        diagnostics are surfaced here, deduplicated against what this program
        has already reported (the E151/E152/E153/E154 harvest above re-derives
        some of them), so a module reached from two importers, or reported at
        registration and again here, is still described once.

        Kept OFF the ``temp`` used for the harvest above on purpose: checking
        a program injects its imports into its own ``env.functions``, and the
        harvest reads that dict to decide what the module EXPORTS — reusing
        one checker for both would re-export every name the module imported.

        Each module is checked once per top-level run, memoised by path
        through the nested checkers.  The memo is entered BEFORE the check, so
        an import cycle terminates here rather than recursing (the resolver's
        own E011 cycle diagnostic is what reports it).
        """
        from vera.checker.core import TypeChecker

        memo: set[tuple[str, ...]] | None = self._module_body_check_memo
        if memo is None:
            memo = set()
            self._module_body_check_memo = memo
        if mod.path in memo:
            return
        memo.add(mod.path)
        checker = TypeChecker(
            source=mod.source,
            file=str(mod.file_path),
            resolved_modules=self._modules_visible_to(mod),
        )
        checker._module_body_check_memo = memo
        checker.check_program(mod.program)
        seen = {
            (e.error_code, str(e.location.file), e.location.line,
             e.location.column, e.severity, e.description)
            for e in self.errors
        }
        for err in checker.errors:
            key = (err.error_code, str(err.location.file), err.location.line,
                   err.location.column, err.severity, err.description)
            if key in seen:
                continue
            seen.add(key)
            self.errors.append(err)

    def _modules_visible_to(
        self, mod: ResolvedModule,
    ) -> list[ResolvedModule]:
        """The resolved modules *mod* imports, re-scoped to *mod* (#1244).

        The same objects this program resolved, with ``direct`` recomputed
        against ``mod``'s own import list: what is transitive from here may be
        a direct import there, and §8.6.4 visibility is a property of the
        importer, not of the module.  A path this program never resolved is
        skipped — the resolver reaches every transitive import, so a missing
        one means the module was unreachable, and the name then misses loudly
        in the check below rather than binding something else.
        """
        by_path = {m.path: m for m in self._resolved_modules}
        direct = {tuple(imp.path) for imp in mod.program.imports}
        out: list[ResolvedModule] = []
        seen: set[tuple[str, ...]] = set()
        frontier = [p for p in direct if p in by_path]
        while frontier:
            path = frontier.pop()
            if path in seen:
                continue
            seen.add(path)
            dep = by_path[path]
            out.append(replace(dep, direct=path in direct))
            frontier.extend(
                tuple(imp.path) for imp in dep.program.imports
                if tuple(imp.path) in by_path
            )
        return out

    @staticmethod
    def _find_import_decl(
        program: ast.Program, path: tuple[str, ...],
    ) -> ast.Node:
        """Find the ImportDecl node for a given module path."""
        for imp in program.imports:
            if imp.path == path:
                return imp
        return program  # fallback
