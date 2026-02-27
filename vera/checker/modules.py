"""Mixin for cross-module registration (C7b/C7c).

Extracted from ``core.py`` so that import-related logic lives in its
own file while the main :class:`TypeChecker` stays focused on
single-module checking.
"""

from __future__ import annotations

from vera import ast
from vera.environment import TypeEnv


class ModulesMixin:
    """Methods for registering declarations from resolved modules."""

    def _register_modules(self, program: ast.Program) -> None:
        """Register declarations from resolved modules (C7b/C7c).

        1. Build an import-name filter from the program's ``import``
           declarations (selective vs wildcard).
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

        # Snapshot builtin names (TypeEnv registers builtins in __post_init__)
        _builtins = TypeEnv()
        builtin_fn_names = set(_builtins.functions)
        builtin_data_names = set(_builtins.data_types)
        builtin_ctor_names = set(_builtins.constructors)

        # 2. Register each module in isolation, harvest declarations
        for mod in self._resolved_modules:
            temp = TypeChecker(source=mod.source)
            temp._register_all(mod.program)

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
                                'Chapter 5, Section 5.8 '
                                '"Function Visibility"'
                            ),
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
                                'Chapter 5, Section 5.8 '
                                '"Function Visibility"'
                            ),
                        )

            # 5. Inject public names into main env for bare calls
            for fn_name, fn_info in mod_fns.items():
                if name_filter is None or fn_name in name_filter:
                    self.env.functions.setdefault(fn_name, fn_info)
            for dt_name, dt_info in mod_data.items():
                if name_filter is None or dt_name in name_filter:
                    self.env.data_types.setdefault(dt_name, dt_info)
            for ct_name, ct_info in mod_ctors.items():
                parent = ct_info.parent_type
                if name_filter is None or parent in name_filter:
                    self.env.constructors.setdefault(ct_name, ct_info)

    @staticmethod
    def _find_import_decl(
        program: ast.Program, path: tuple[str, ...],
    ) -> ast.Node:
        """Find the ImportDecl node for a given module path."""
        for imp in program.imports:
            if imp.path == path:
                return imp
        return program  # fallback
