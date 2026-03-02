"""Mixin for cross-module registration and call detection (C7e).

Handles Pass 0 (module registration) and Pass 1.9 (cross-module
call detection) of the code generation pipeline.
"""

from __future__ import annotations

from vera import ast
from vera.errors import Diagnostic, SourceLocation


class CrossModuleMixin:
    """Methods for registering imported module declarations."""

    def _register_modules(self, program: ast.Program) -> None:
        """Register imported function signatures for cross-module codegen.

        Mirrors the verifier's ``_register_modules`` pattern (C7d):
        1. Build import-name filter from ImportDecl nodes.
        2. For each resolved module, register in isolation and harvest
           function signatures, ADT layouts, and type aliases.
        3. Inject into ``self._fn_sigs`` via ``setdefault`` so local
           definitions shadow imported names.
        4. Collect all imported FnDecls for compilation in Pass 2.5.
        """
        if not self._resolved_modules:
            return

        from vera.codegen.core import CodeGenerator

        # 1. Build import filter: path -> set of names (or None for wildcard)
        import_names: dict[tuple[str, ...], set[str] | None] = {}
        for imp in program.imports:
            import_names[imp.path] = (
                set(imp.names) if imp.names is not None else None
            )

        # 2. Register each module in isolation
        for mod in self._resolved_modules:
            temp = CodeGenerator(source=mod.source)
            temp._register_all(mod.program)

            # Build visibility map for this module
            vis_map: dict[str, str] = {}
            for tld in mod.program.declarations:
                if isinstance(tld.decl, ast.FnDecl):
                    vis_map[tld.decl.name] = tld.visibility or "private"
                elif isinstance(tld.decl, ast.DataDecl):
                    vis_map[tld.decl.name] = tld.visibility or "private"

            # Harvest function sigs — include all (public + private) so
            # private helpers called by imported public fns are available.
            name_filter = import_names.get(mod.path)
            for fn_name, sig in temp._fn_sigs.items():
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

            # Harvest ADT layouts
            for adt_name, layouts in temp._adt_layouts.items():
                is_public = vis_map.get(adt_name) == "public"
                in_filter = (
                    name_filter is None or adt_name in name_filter
                )
                if is_public and in_filter:
                    self._adt_layouts.setdefault(adt_name, layouts)
                    self._needs_alloc = True
                    self._needs_memory = True

            # Harvest type aliases
            for alias_name, alias_expr in temp._type_aliases.items():
                self._type_aliases.setdefault(alias_name, alias_expr)

            # Collect ALL FnDecls from this module for compilation
            for tld in mod.program.declarations:
                if isinstance(tld.decl, ast.FnDecl):
                    self._imported_fn_decls.append(tld.decl)
                    # Also include where-block functions
                    if tld.decl.where_fns:
                        for wfn in tld.decl.where_fns:
                            self._imported_fn_decls.append(wfn)

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
        # Built-in names handled specially in _translate_call
        known.update({
            "length", "apply_fn", "get", "put", "resume",
            "string_length", "string_concat", "string_slice",
            "char_code", "parse_nat", "parse_float64",
            "to_string", "strip",
        })

        seen: set[str] = set()  # deduplicate by function name

        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
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
        self.diagnostics.append(Diagnostic(
            description=(
                f"Function '{display}' is not defined in this module "
                f"and was not found in any imported module."
            ),
            location=loc,
            source_line=self._get_source_line(loc.line),
            rationale=(
                "The WASM code generator compiles imported functions into "
                "the same binary.  If a function cannot be resolved, it "
                "cannot be called."
            ),
            severity="error",
        ))
