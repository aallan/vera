"""Mixin for cross-module registration (C7b/C7c).

Extracted from ``core.py`` so that import-related logic lives in its
own file while the main :class:`TypeChecker` stays focused on
single-module checking.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from vera import ast
from vera.environment import AdtInfo, ConstructorInfo, FunctionInfo, TypeEnv
from vera.errors import Diagnostic
from vera.module_view import modules_visible_to
from vera.monomorphize import namespace_adt_names, namespace_fn_names
from vera.registration import where_helper_parents
from vera.resolver import (
    ResolvedModule,
    merged_import_filters,
    own_module_path,
)

if TYPE_CHECKING:
    from vera.checker.core import TypeChecker


#: The registration diagnostics every importer surfaces from a module (see
#: ``ModulesMixin._register_modules``).
_SURFACED_REGISTRATION_CODES = frozenset({"E151", "E152", "E153", "E154"})


@dataclass(frozen=True)
class ModuleRegistration:
    """One module's declarations, registered in its own namespace, and what
    they export — derived once per path for the whole run (#1489, #1275).

    ``checker`` holds the registration.  The tables are read off it here,
    once, rather than by every checker that can see the module: a
    registration carries the whole built-in registry beside the module's own
    declarations, so a chain re-reading it per checker paid that per
    (checker, module) pair.  ``all_functions`` and ``all_data_types`` are the
    module's declarations, private ones included (for the "is private"
    diagnostics); ``functions``, ``data_types`` and ``constructors`` are what
    it exports.  ``surfaced`` is the registration's own E151–E154, which
    every importer reports (see ``ModulesMixin._register_modules``).
    """

    checker: TypeChecker
    surfaced: tuple[Diagnostic, ...]
    all_functions: dict[str, FunctionInfo]
    all_data_types: dict[str, AdtInfo]
    functions: dict[str, FunctionInfo]
    data_types: dict[str, AdtInfo]
    constructors: dict[str, ConstructorInfo]
    #: The constructor names of each public data type the registration
    #: refused and left unregistered (a reserved name, #1469, #1497), by the
    #: type's name: an importer's use of one draws no error of its own,
    #: since the module's refusal is the one the program owes.
    refused_ctors: dict[str, tuple[str, ...]] = field(default_factory=dict)


def _module_exports(
    temp: TypeChecker, program: ast.Program,
    builtin_fns: set[str], builtin_ctors: set[str],
) -> ModuleRegistration:
    """Read a module's registration *temp* into its :class:`ModuleRegistration`.

    The data side is read off the module's own declarations: the
    registration also holds the data types the module IMPORTS (#1489), which
    it names but does not export.  No function is injected into a
    registration, so its function table is the module's own.
    """
    own_data = [
        tld.decl.name for tld in program.declarations
        if isinstance(tld.decl, ast.DataDecl)
    ]
    all_fns = {
        k: v for k, v in temp.env.functions.items()
        if k not in builtin_fns or v.span is not None
    }
    # What the module DECLARES, whatever the name (#1559).  Filtering by name
    # dropped a module's own `data Json` along with the built-in one it
    # replaces in `temp`, so its constructors never reached an importer:
    # `import a(Json)` admitted nothing, and a construction the spec admits
    # (§8.3.3) was an unknown constructor.  A declaration registers a new
    # `AdtInfo`, so of the names the module declares, the entries that are
    # not the built-ins' own -- `temp`'s snapshot of them, taken before
    # anything was injected or registered -- are the module's.  Keyed by the
    # name the module declares each under, which is what an import names;
    # each `AdtInfo` carries the type's identity (#1694).
    all_data: dict[str, AdtInfo] = {}
    for name in own_data:
        info = temp.env.lookup_type(name)
        if (info is not None and name not in all_data
                and temp._builtin_data_types.get(name) is not info):
            all_data[name] = info
    public_fns = {
        k: v for k, v in all_fns.items() if v.visibility == "public"
    }
    public_data = {
        k: v for k, v in all_data.items() if v.visibility == "public"
    }
    # Constructors: only those of the public ADTs.
    public_ctors: set[str] = set()
    for dt_info in public_data.values():
        public_ctors.update(dt_info.constructors)
    ctors = {
        k: v for k, v in temp.env.constructors.items()
        if k not in builtin_ctors and k in public_ctors
    }
    refused_ctors = {
        tld.decl.name: tuple(c.name for c in tld.decl.constructors)
        for tld in program.declarations
        if isinstance(tld.decl, ast.DataDecl)
        and tld.visibility == "public"
        and id(tld.decl) in temp._refused_decl_ids
    }
    return ModuleRegistration(
        checker=temp,
        surfaced=tuple(
            e for e in temp.errors
            if e.error_code in _SURFACED_REGISTRATION_CODES
        ),
        all_functions=all_fns,
        all_data_types=all_data,
        functions=public_fns,
        data_types=public_data,
        constructors=ctors,
        refused_ctors=refused_ctors,
    )


def _dependency_order(
    by_path: dict[tuple[str, ...], ResolvedModule],
) -> list[tuple[str, ...]]:
    """Every path in *by_path*, each after the modules it imports.

    An iterative depth-first post-order, so a module's registration can read
    its imports' and a deep chain costs no Python frame per hop.  An import
    that closes a cycle (already an E011) is skipped.  Roots are taken in
    resolution order and imports in source order, so the order is a function
    of the program text alone.
    """
    def deps(path: tuple[str, ...]) -> list[tuple[str, ...]]:
        return [
            p for p in merged_import_filters(by_path[path].program.imports)
            if p in by_path
        ]

    order: list[tuple[str, ...]] = []
    seen: set[tuple[str, ...]] = set()
    for root in by_path:
        if root in seen:
            continue
        seen.add(root)
        stack = [(root, iter(deps(root)))]
        while stack:
            path, pending = stack[-1]
            nxt = next(pending, None)
            if nxt is None:
                stack.pop()
                order.append(path)
            elif nxt not in seen:
                seen.add(nxt)
                stack.append((nxt, iter(deps(nxt))))
    return order


class ModulesMixin:
    """Methods for registering declarations from resolved modules."""

    def _register_modules(self, program: ast.Program) -> None:
        """Register declarations from resolved modules (C7b/C7c).

        1. Build an import-name filter from the program's ``import``
           declarations (selective vs wildcard).
        1a. #1304: refuse a bare function, data-type or constructor name
           two of this namespace's imports both supply, and keep it out of
           the environment.
        2. For each resolved module, its registration in an isolated
           TypeChecker, in the module's own namespace, and the per-module
           dicts read off it — built once per path for the whole run
           (:meth:`_module_registrations`).
        3. C7c: the public declarations, beside the unfiltered dicts kept
           for better "is private" error messages.
        4. C7c: emit errors when selective imports reference private names.
        5. Inject selectively imported *public* names into ``self.env`` so
           bare calls (``abs(42)`` after ``import vera.math(abs)``)
           resolve through the normal ``_check_call_with_args`` path.
        """
        # 1. Build import filter, unioned across repeated imports of one
        # path (#1433) — the one derivation the verifier and codegen read too.
        self._import_names.update(merged_import_filters(program.imports))
        resolved_paths = {m.path for m in self._resolved_modules}
        # #1489: an import whose module did not resolve (E011/E012/E013)
        # supplies nothing; E136 names it when a type it lists is used.
        self._unresolved_imports = {
            path: (frozenset(names) if names is not None else None)
            for path, names in self._import_names.items()
            if path not in resolved_paths
        }

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

        # 2. Each module's own declarations, registered in the module's own
        #    namespace (#1489), and what they export — both derived once per
        #    path for the whole run (#1275).
        registrations = self._module_registrations(
            builtin_fn_names, builtin_ctor_names,
        )
        for mod in self._resolved_modules:
            # Registered with the module's own source and file path, so any
            # surfaced diagnostic (the E151 below) carries `location.file`
            # matching every other diagnostic.
            reg = registrations[mod.path]

            # #815: surface E151 (a module fn redefining a built-in) into the
            # importer.  The registration is built with the module's own
            # source, so these diagnostics already carry the correct
            # module-file location and source line.  Without this, a module
            # imported but never checked standalone would let the
            # redefinition through silently — the importer's verifier
            # reasons with the built-in's model while the module's body runs
            # (verify proves, run violates).
            # #1149: E152 (a module redeclaring a built-in EFFECT) is surfaced
            # on the same grounds — the block is invisible to codegen, which
            # routes the qualified call to the host import regardless, so an
            # unchecked module would miscompile the importer.
            # #1181/#1187: E153 (a module fn named after a contract state form
            # or a grammar keyword) likewise — a module imported but never
            # checked standalone would otherwise carry a declaration no
            # importer could ever bare-call.
            self.errors.extend(reg.surfaced)

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

            # All module-declared names (builtins excluded), unfiltered — C7c
            # keeps them for the "is private" error messages.
            all_fns = reg.all_functions
            all_data = reg.all_data_types
            self._module_all_functions[mod.path] = all_fns
            self._module_all_data_types[mod.path] = all_data
            # #1694: and every one of them is a type a value can carry here,
            # through an imported signature, whether or not this namespace
            # can name it.  Keyed by identity, which no name spells, so this
            # grants no name: an import does (step 5).
            for dt_info in all_data.values():
                self.env.data_types.setdefault(dt_info.name, dt_info)

            # 3. C7c: the public ones, and the constructors of public ADTs.
            #    Shared by every checker that can see the module, and never
            #    written through: each is read, or copied into `self.env`.
            mod_fns = reg.functions
            mod_data = reg.data_types
            mod_ctors = reg.constructors

            self._module_functions[mod.path] = mod_fns
            self._module_data_types[mod.path] = mod_data
            self._module_constructors[mod.path] = mod_ctors
            # #1469: a refused public type's constructors, for an import
            # that admits the type: like a refused declaration's own
            # (#1497), a use of one draws no error after the module's.
            if mod.path in self._import_names:
                admitted = self._import_names[mod.path]
                for type_name, ctor_names in reg.refused_ctors.items():
                    if admitted is None or type_name in admitted:
                        self._refused_ctor_names.update(ctor_names)

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
        # 5b. #1694: the data type and constructor names an import supplies
        #     are what the resolver pass binds them to (the type names were
        #     taken before registration, `_take_type_names`): one supplier
        #     binds, two leave the name denoting nothing (#1304), and an
        #     import names a constructor by its TYPE (spec §8.5.4).
        self._take_imported_constructors()

    def _take_imported_constructors(self) -> None:
        """Each constructor name an import supplies this namespace, to the
        constructor the resolver pass binds it to (#1694).  The namespace's
        own constructors are registered with their types, and one of a type
        it imports none of is read where it is met
        (:meth:`_stranger_constructor`)."""
        names = self._names
        if names is None:
            return
        owner = self._namespace_owner()
        strangers = names.stranger_ctors.get(owner, frozenset())
        for name, ident in names.ctors.get(owner, {}).items():
            if ident.owner == owner or name in strangers:
                continue
            info = self._module_constructors.get(ident.owner, {}).get(
                ident.name)
            if info is not None:
                self.env.constructors.setdefault(name, info)

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
        import pair exists, whether or not any body names it, so the verdict
        is a function of the import lists alone.  It reads
        :func:`~vera.monomorphize.namespace_fn_names` for its OWN namespace's
        clashes, to report at its own import and to keep the name unbound;
        the resolver pass leaves a bare call two imports supply unbound by
        the same rule (:mod:`vera.binding`).

        Reported once per clashing name, at the LAST import that supplies it
        — the one whose presence completes the clash — and in sorted name
        order, so the diagnostic stream is a function of the source alone.

        Every namespace gets its own pass: the entry program here, and each
        module's through the fresh checker :meth:`_check_module_bodies`
        builds for it, whose diagnostics are surfaced into this one.  That is
        what makes the refusal reach a module the entry program only imports,
        the shape §8.5 left undefined and the one where the flap was
        observable (#1304).

        THREE NAMESPACES, three codes: functions (E155), data types (E156)
        and constructors (E157).  One code would have been cheaper and
        wrong: a constructor clash is not a type clash (two modules
        exporting differently-named ADTs can share a constructor name), and
        the registry's convention is one code per declaration namespace.

        The data side flapped exactly as the function side did — measured on
        two modules each exporting a ``public data Shape`` with different
        constructor field types, where ``Sq(3)`` type-checked on some hash
        seeds and was ``E213`` on others.  Its accepting seeds were the worse
        half: ``check`` and ``verify`` both passed, and the program then died
        at ``run`` with a code-generation collision error located at line 0
        of the entry file, naming two modules the entry never imported.

        The data side's escape hatches are the function side's: narrowing
        an import or declaring the name locally clears the clash.  Each
        module's declaration is a type of its own (#1694), named by its link
        name ``mod$<path>$<Name>``, so two declarations never contend in
        code generation; a value of one that reaches a place expecting the
        other is an ordinary type mismatch whose message names both owners.
        :meth:`_ambiguous_data_fix` says so.

        A name the BUILT-IN registry already owns is never ambiguous: every
        injection below is a ``setdefault`` onto an environment the built-ins
        populated first, so the incumbent wins and the imports never compete.
        The three snapshots are passed in for that reason, and not passing
        the function one was an over-refusal in this method's first version —
        two dependencies exporting their own ``option_map`` were reported as
        a clash when a bare ``option_map`` in fact resolves to the prelude's.
        """
        # A clash is between THIS namespace's imports, and the tables read
        # nothing else for it — so only the modules it imports are passed,
        # not every module it can see (#1275: a module checker sees its whole
        # transitive closure, and reading it here was one more pass per
        # (checker, module) pair).
        imported = {tuple(imp.path) for imp in program.imports}
        modules = [
            (mod.path, mod.program) for mod in self._resolved_modules
            if mod.path in imported
        ]
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
        # A clashing constructor name is refused at the import, and like a
        # refused declaration's constructor (#1497) a use of it draws no
        # error of its own: the E157 is the one the program owes (#1513).
        self._refused_ctor_names.update(ctor_clashes)

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
        """The remedies that work for a clashing TYPE or CONSTRUCTOR name.

        The two the function side offers, and the one a crossing value
        needs.  Each module's ``data`` declaration is a type of its own
        (#1694), so narrowing an import or declaring the name locally clears
        the clash, and a value of one module's type that must reach code
        expecting the other's is a type mismatch whatever the names:
        declaring the type once and importing it is the remedy for that.
        """
        return (
            f"Import at most one supplier of '{name}': name the other "
            f"import's declarations selectively, as "
            f"'import {labels[-1]}(<other-name>);' (replace <other-name> "
            f"with a declaration you need from that module). Declaring "
            f"'{name}' in this file resolves it too. Each module's "
            "declaration is a type of its own, so where a value made by "
            f"'{labels[0]}' must reach '{labels[-1]}', declare the type "
            "once, in one module, and import it in the other."
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

        Kept OFF the module's registration (:class:`ModuleRegistration`) on
        purpose: checking a program injects its imports into its own
        ``env.functions``, and the registration's tables are read from that
        dict to decide what the module EXPORTS — reusing one checker for both
        would re-export every name the module imported.

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
            resolved_modules=modules_visible_to(
                mod.program, self._resolved_modules),
        )
        checker._module_body_check_memo = memo
        # #1275: the per-path registrations this run has built travel with
        # the memo, so a nested checker reuses them instead of registering
        # every module it can see again.
        checker._module_registration_cache = self._module_registration_cache
        # #1558: the path the program reaches this module by, which its own
        # `module` declaration has to match for the path to name it.
        checker._resolved_as = mod.path
        # #1679: the module's nodes are typed into this check's tables,
        # which are keyed by node identity, so one table answers for every
        # file's nodes without a collision.
        checker.node_semantic_types = self.node_semantic_types
        checker.node_target_types = self.node_target_types
        checker.instantiations = self.instantiations
        checker.handler_cells = self.handler_cells
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

    def _own_module_paths(
        self, program: ast.Program,
    ) -> tuple[tuple[str, ...] | None, tuple[str, ...] | None]:
        """The path *program* declares, and the path that names it (#1558).

        The second is :func:`vera.resolver.own_module_path`'s answer — the
        declared path, where the program reaches the file by it — which a
        module-qualified call to it resolves against the file's own
        top-level functions (`_check_own_module_call`).  The first is kept
        for E230's fix when the two differ: a file imported as ``ma`` that
        declares another path, or none, is told to declare ``module ma;``.
        """
        declared = (tuple(program.module.path)
                    if program.module is not None else None)
        return declared, own_module_path(
            program, self._resolved_as, self._resolved_modules)

    def _module_registrations(
        self, builtin_fns: set[str], builtin_ctors: set[str],
    ) -> dict[tuple[str, ...], ModuleRegistration]:
        """Each resolved module's declarations, registered in ITS OWN
        namespace (#1489), once per path for the whole run (#1275).

        A module's signatures name the data types it imports, so registering
        them with none of its imports in scope sent every such name to the
        checker's last resort, which made an opaque placeholder of it.  The
        placeholder usually spelled the imported type exactly, and that hid
        the gap — but not always: a module importing a user ``data
        Decimal<T>`` registered ``unwrap(@Decimal<Int>)`` as the BUILT-IN
        ``Decimal``, whose branch drops type arguments, and the importer
        then refused a valid call (E202) that checked clean with the module
        as the entry.  So each registration is given the data types its
        module imports first, from the one derivation of what a namespace
        imports (:func:`vera.module_view.imported_data_types`), taken from
        the imported module's own registration.  Only data types: a
        signature names types, never a function or a constructor, and
        injecting nothing else keeps the harvest's view of what the module
        EXPORTS its own declarations.

        That makes a module's registration depend on its imports', so they
        are built in dependency order — iteratively, since a deep import
        chain must not cost a Python frame per hop.  A module's registration
        depends only on the module and its imports, never on who imports
        it, so it is built once per path and shared with every nested
        checker through ``_module_registration_cache``, together with what
        it exports (:class:`ModuleRegistration`).  Before, each checker
        registered every module it could see, and the #1244 body checks
        multiplied that into the O(N²) of #1275.

        An import cycle is already an E011; the module on the far side of
        the back edge is skipped rather than recursed into, so the cycle
        terminates and its types are simply not in scope there.
        """
        from vera.checker.core import TypeChecker

        cache = self._module_registration_cache
        if cache is None:
            cache = {}
            self._module_registration_cache = cache
        if all(m.path in cache for m in self._resolved_modules):
            # A nested checker: the run's first checker registered them all.
            return cache
        by_path = {m.path: m for m in self._resolved_modules}
        names = self._names
        assert names is not None  # bound by `check_program`  # noqa: S101
        for path in _dependency_order(by_path):
            if path in cache:
                continue
            mod = by_path[path]
            temp = TypeChecker(source=mod.source, file=str(mod.file_path))
            # The module's own data types take their identities (#1694), and
            # each data type name it writes denotes what the resolver pass
            # binds it to there: its own declaration, or the one import that
            # supplies it (two supply none, #1304: the module's own check
            # reports E156 at the import).
            temp._resolved_as = path
            types = names.types.get(path, {})
            temp._take_type_names(types)
            for ident in types.values():
                dep = cache.get(ident.owner)
                info = (None if dep is None or ident.kind != "data"
                        else dep.data_types.get(ident.name))
                if info is not None:
                    # The type is held by its identity.
                    temp.env.data_types.setdefault(info.name, info)
            temp._register_all(mod.program)
            cache[path] = _module_exports(
                temp, mod.program, builtin_fns, builtin_ctors,
            )
        return cache

    @staticmethod
    def _find_import_decl(
        program: ast.Program, path: tuple[str, ...],
    ) -> ast.Node:
        """Find the ImportDecl node for a given module path."""
        for imp in program.imports:
            if imp.path == path:
                return imp
        return program  # fallback
