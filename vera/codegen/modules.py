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
        3. Detect name collisions across modules (E608/E609/E610).
        4. Inject into ``self._fn_sigs`` via ``setdefault`` so local
           definitions shadow imported names.
        5. Collect all imported FnDecls for compilation in Pass 2.5.
        """
        if not self._resolved_modules:
            return

        from vera.codegen.core import CodeGenerator

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

        # #814 §8.5.3: names of LOCAL functions in the importing program.  A
        # module fn whose bare name appears here is shadowed for bare calls
        # (§8.5.2); its module-qualified target must point at a distinct
        # ``mod$…`` WASM name so ``m::f`` still reaches the module's body.
        local_fn_names: set[str] = {
            tld.decl.name for tld in program.declarations
            if isinstance(tld.decl, ast.FnDecl)
        }

        # Provenance tracking for collision detection
        fn_provenance: dict[str, tuple[str, ...]] = {}
        adt_provenance: dict[str, tuple[str, ...]] = {}
        ctor_provenance: dict[str, tuple[tuple[str, ...], str]] = {}

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
            for fn_name, ret_te in temp._fn_ret_type_exprs.items():
                self._fn_ret_type_exprs.setdefault(fn_name, ret_te)

            # Harvest per-parameter concrete-@Nat flags (#747, CR #756).
            # Without this an imported function `f(@Nat -> …)` loses its
            # `_fn_nat_params` entry, so a cross-module call `f(@Int.0)`
            # would skip the `value >= 0` runtime guard the in-module call
            # gets.  Same `setdefault` first-seen-wins shape as `_fn_sigs`.
            for fn_name, nat_params in temp._fn_nat_params.items():
                self._fn_nat_params.setdefault(fn_name, nat_params)

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

                if not ctor_collision and is_public and in_filter:
                    self._adt_layouts.setdefault(adt_name, layouts)
                    self._needs_alloc = True
                    self._needs_memory = True

            # Harvest type aliases
            for alias_name, alias_expr in temp._type_aliases.items():
                self._type_aliases.setdefault(alias_name, alias_expr)

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
                # Generics are excluded before they enter any list: cross-
                # module generic monomorphisation is unimplemented (#774), and
                # a generic body (or its where-fns) can't be compiled in Pass
                # 2.5 nor emitted under a mangled name.
                if tld.decl.forall_vars:
                    continue
                self._imported_fn_decls.append(tld.decl)
                if tld.decl.where_fns:
                    for wfn in tld.decl.where_fns:
                        self._imported_fn_decls.append(wfn)
                fn_name = tld.decl.name
                is_public = (tld.visibility or "private") == "public"
                in_filter = name_filter is None or fn_name in name_filter
                # Only a SHADOWED name needs a table entry: the desugar falls
                # back to the bare name for any (path, name) not present, which
                # is already correct for a non-shadowed module fn (emitted
                # under its bare name).  So we register entries only when a
                # local shadows the bare name.
                if fn_name not in local_fn_names:
                    continue
                mangled = self._module_qualified_wasm_name(mod.path, fn_name)
                mangled_sig = temp._fn_sigs.get(fn_name)
                if mangled_sig is None:
                    continue
                self._fn_sigs.setdefault(mangled, mangled_sig)
                self._shadowed_module_fns.append((mod.path, mangled, tld.decl))
                self._module_intra_renames.setdefault(
                    mod.path, {})[fn_name] = mangled
                # Mirror the @Nat-parameter guard bitmap onto the mangled name
                # so a qualified call to a shadowed module fn with a @Nat
                # parameter still emits the call-site `value >= 0` narrowing
                # guard (it keys on the resolved target, #814).
                self._fn_nat_params.setdefault(
                    mangled, temp._fn_nat_params.get(fn_name, ()))
                if is_public and in_filter:
                    self._module_qualified_targets[(mod.path, fn_name)] = mangled

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
            spec_ref="Chapter 11, Section 11.16",
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
            spec_ref="Chapter 11, Section 11.16",
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
