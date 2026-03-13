"""Vera code generator — composed CodeGenerator class.

The ``CodeGenerator`` class is composed from several mixin modules that
each handle a specific concern:

* :mod:`~vera.codegen.modules` — cross-module registration (C7e)
* :mod:`~vera.codegen.registration` — Pass 1 forward declarations
* :mod:`~vera.codegen.monomorphize` — generic instantiation (Pass 1.5)
* :mod:`~vera.codegen.functions` — function body compilation (Pass 2)
* :mod:`~vera.codegen.closures` — closure lifting
* :mod:`~vera.codegen.contracts` — runtime contract insertion
* :mod:`~vera.codegen.assembly` — WAT module assembly
* :mod:`~vera.codegen.compilability` — compilability checks
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import wasmtime

from vera import ast
from vera.codegen.api import CompileResult, ConstructorLayout
from vera.errors import Diagnostic, SourceLocation
from vera.wasm import StringPool

from vera.codegen.modules import CrossModuleMixin
from vera.codegen.registration import RegistrationMixin
from vera.codegen.monomorphize import MonomorphizationMixin
from vera.codegen.functions import FunctionCompilationMixin
from vera.codegen.closures import ClosureLiftingMixin
from vera.codegen.contracts import ContractsMixin
from vera.codegen.assembly import AssemblyMixin
from vera.codegen.compilability import CompilabilityMixin

if TYPE_CHECKING:
    from vera.resolver import ResolvedModule


class CodeGenerator(
    CrossModuleMixin,
    RegistrationMixin,
    MonomorphizationMixin,
    FunctionCompilationMixin,
    ClosureLiftingMixin,
    ContractsMixin,
    AssemblyMixin,
    CompilabilityMixin,
):
    """Compiles a Vera Program AST to WebAssembly.

    Two-pass approach:
    1. Registration: collect function signatures for forward references
    2. Compilation: generate WAT for each compilable function
    """

    def __init__(
        self,
        source: str = "",
        file: str | None = None,
        resolved_modules: list[ResolvedModule] | None = None,
    ) -> None:
        self.source = source
        self.file = file
        self.diagnostics: list[Diagnostic] = []
        self.string_pool = StringPool()

        # Registered function signatures: name -> (param_types, return_type)
        self._fn_sigs: dict[str, tuple[list[str | None], str | None]] = {}
        # Track which effect operations are needed
        self._io_ops_used: set[str] = set()
        self._needs_contract_fail: bool = False
        self._needs_memory: bool = False
        self._state_types: list[tuple[str, str]] = []  # (type_name, wasm_type)
        self._exn_types: list[tuple[str, str]] = []  # (type_name, wasm_type)
        self._md_ops_used: set[str] = set()  # Markdown host-import builtins
        self._regex_ops_used: set[str] = set()  # Regex host-import builtins

        # ADT layout metadata (populated during registration)
        self._adt_layouts: dict[str, dict[str, ConstructorLayout]] = {}
        self._needs_alloc: bool = False

        # Type aliases (populated during registration)
        # Maps alias name -> TypeExpr (for resolving function type aliases)
        self._type_aliases: dict[str, ast.TypeExpr] = {}
        # Type alias parameters: alias name -> param names
        # Needed for generic type alias resolution in closure codegen
        self._type_alias_params: dict[str, tuple[str, ...]] = {}

        # Closure compilation state
        self._closure_table: list[str] = []  # lifted fn names for table
        self._closure_sigs: dict[str, str] = {}  # sig_key -> WAT type decl
        self._closure_fns_wat: list[str] = []  # WAT for lifted closures
        self._needs_table: bool = False
        self._next_closure_id: int = 0

        # Cross-module state (C7e)
        self._resolved_modules: list[ResolvedModule] = (
            resolved_modules or []
        )
        # Imported FnDecls to compile in Pass 2.5
        self._imported_fn_decls: list[ast.FnDecl] = []

    # -----------------------------------------------------------------
    # Diagnostics
    # -----------------------------------------------------------------

    def _warning(
        self,
        node: ast.Node,
        description: str,
        *,
        rationale: str = "",
        error_code: str = "",
    ) -> None:
        """Record a compilation warning (function skipped)."""
        loc = SourceLocation(file=self.file)
        if node.span:
            loc.line = node.span.line
            loc.column = node.span.column
        self.diagnostics.append(Diagnostic(
            description=description,
            location=loc,
            source_line=self._get_source_line(loc.line),
            rationale=rationale,
            severity="warning",
            error_code=error_code,
        ))

    def _get_source_line(self, line: int) -> str:
        """Extract a line from the source text."""
        lines = self.source.splitlines()
        if 1 <= line <= len(lines):
            return lines[line - 1]
        return ""

    # -----------------------------------------------------------------
    # Compilation entry point
    # -----------------------------------------------------------------

    def compile_program(self, program: ast.Program) -> CompileResult:
        """Compile a complete Vera program to WebAssembly."""
        # Pass 0: register imported module declarations (C7e)
        self._register_modules(program)

        # Pass 1: register local function signatures (shadows imports)
        self._register_all(program)

        # Pass 1.2: inject prelude combinator implementations
        # Prelude functions are registered as builtins in the type checker
        # (environment.py) but need compilable AST bodies for codegen.
        # inject_prelude prepends FnDecl + TypeAliasDecl nodes to
        # program.declarations; we register them here.
        existing_fns = set(self._fn_sigs.keys())
        from vera.prelude import inject_prelude
        inject_prelude(program)
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and decl.name not in existing_fns:
                self._register_fn(decl)
            elif isinstance(decl, ast.TypeAliasDecl):
                if decl.name not in self._type_aliases:
                    self._type_aliases[decl.name] = decl.type_expr
                    if decl.type_params:
                        self._type_alias_params[decl.name] = decl.type_params

        # Pass 1.5: monomorphize generic functions
        mono_decls = self._monomorphize(program)
        for mdecl in mono_decls:
            self._register_fn(mdecl)

        # Pass 1.6: rewrite ability operation calls → concrete expressions
        program, mono_decls = self._rewrite_ability_ops(program, mono_decls)

        # Pass 1.9: check for cross-module calls that codegen can't handle
        self._check_cross_module_calls(program)
        if any(d.severity == "error" for d in self.diagnostics):
            return CompileResult(
                wat="",
                wasm_bytes=b"",
                exports=[],
                diagnostics=self.diagnostics,
                state_types=list(self._state_types),
                md_ops_used=set(self._md_ops_used),
                regex_ops_used=set(self._regex_ops_used),
            )

        # Pass 2: compile function bodies
        functions_wat: list[str] = []
        exports: list[str] = []

        # Build visibility map for export gating
        fn_visibility: dict[str, str] = {}
        for tld in program.declarations:
            if isinstance(tld.decl, ast.FnDecl):
                fn_visibility[tld.decl.name] = tld.visibility or "private"

        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                is_public = tld.visibility == "public"
                fn_wat = self._compile_fn(decl, export=is_public)
                if fn_wat is not None:
                    functions_wat.append(fn_wat)
                    if is_public:
                        exports.append(decl.name)
                    # Also compile where-block functions
                    if decl.where_fns:
                        for wfn in decl.where_fns:
                            wfn_wat = self._compile_fn(wfn, export=False)
                            if wfn_wat is not None:
                                functions_wat.append(wfn_wat)

        # Compile monomorphized functions
        for mdecl in mono_decls:
            orig_name = mdecl.name.split("$")[0]
            is_public = fn_visibility.get(orig_name) == "public"
            fn_wat = self._compile_fn(mdecl, export=is_public)
            if fn_wat is not None:
                functions_wat.append(fn_wat)
                if is_public:
                    exports.append(mdecl.name)

        # Pass 2.5: compile imported function bodies (C7e)
        imported_seen: set[str] = set()
        for idecl in self._imported_fn_decls:
            if idecl.name in imported_seen:
                continue
            # Skip if a local function already defined this name
            if idecl.name in fn_visibility:
                continue
            imported_seen.add(idecl.name)
            fn_wat = self._compile_fn(idecl, export=False)
            if fn_wat is not None:
                functions_wat.append(fn_wat)

        # Assemble the module
        wat = self._assemble_module(functions_wat)

        # Convert WAT to WASM binary
        try:
            wasm_bytes = wasmtime.wat2wasm(wat)
        except Exception as exc:
            self.diagnostics.append(Diagnostic(
                description=f"WAT compilation failed: {exc}",
                location=SourceLocation(file=self.file),
                severity="error",
            ))
            return CompileResult(
                wat=wat,
                wasm_bytes=b"",
                exports=exports,
                diagnostics=self.diagnostics,
                state_types=list(self._state_types),
                md_ops_used=set(self._md_ops_used),
                regex_ops_used=set(self._regex_ops_used),
            )

        return CompileResult(
            wat=wat,
            wasm_bytes=bytes(wasm_bytes),
            exports=exports,
            diagnostics=self.diagnostics,
            state_types=list(self._state_types),
            md_ops_used=set(self._md_ops_used),
            regex_ops_used=set(self._regex_ops_used),
        )

    # -----------------------------------------------------------------
    # Type helpers (used by most mixins)
    # -----------------------------------------------------------------

    def _type_expr_to_wasm_type(self, te: ast.TypeExpr) -> str | None:
        """Map a Vera TypeExpr to a WAT type string.

        Returns None for Unit, "unsupported" for non-compilable types,
        "i32_pair" for types represented as (i32, i32) pairs (String, Array).
        """
        if isinstance(te, ast.NamedType):
            name = te.name
            if name in ("Int", "Nat"):
                return "i64"
            if name == "Float64":
                return "f64"
            if name in ("Bool", "Byte"):
                return "i32"
            if name == "Unit":
                return None
            if name in ("String", "Array"):
                return "i32_pair"
            # ADT types compile to i32 (heap pointer)
            if name in self._adt_layouts:
                return "i32"
            # Type aliases — recurse to resolve the underlying type
            if name in self._type_aliases:
                return self._type_expr_to_wasm_type(self._type_aliases[name])
            return "unsupported"
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_wasm_type(te.base_type)
        # Function types compile to i32 (closure pointer)
        if isinstance(te, ast.FnType):
            return "i32"
        return "unsupported"

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str | None:
        """Extract the slot name from a type expression."""
        if isinstance(te, ast.NamedType):
            if te.type_args:
                arg_names = []
                for a in te.type_args:
                    if isinstance(a, ast.NamedType):
                        arg_names.append(a.name)
                    else:
                        return None
                return f"{te.name}<{', '.join(arg_names)}>"
            return te.name
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_slot_name(te.base_type)
        if isinstance(te, ast.FnType):
            return "Fn"
        return None

    @staticmethod
    def _escape_wat_string(s: str) -> str:
        """Escape a string for WAT data section literal."""
        result: list[str] = []
        for ch in s:
            code = ord(ch)
            if ch == '"':
                result.append("\\22")
            elif ch == "\\":
                result.append("\\\\")
            elif ch == "\n":
                result.append("\\n")
            elif ch == "\t":
                result.append("\\t")
            elif 0x20 <= code < 0x7F:
                result.append(ch)
            else:
                # Encode as hex bytes
                for b in ch.encode("utf-8"):
                    result.append(f"\\{b:02x}")
        return "".join(result)

    # -----------------------------------------------------------------
    # Pass 1.6: Ability operation rewriting
    # -----------------------------------------------------------------

    def _rewrite_ability_ops(
        self,
        program: ast.Program,
        mono_decls: list[ast.FnDecl],
    ) -> tuple[ast.Program, list[ast.FnDecl]]:
        """Rewrite ability operation calls to concrete expressions.

        Replaces ``eq(a, b)`` with ``BinaryExpr(a, EQ, b)`` in all
        function bodies (regular and monomorphized).
        """
        from dataclasses import replace as _replace

        # Built-in ability operations that need AST-level rewriting.
        # eq(a, b) → BinaryExpr(a, EQ, b)
        # compare(a, b) → if a < b then Less elif a == b then Equal else Greater
        # (show and hash are dispatched at WASM level, not rewritten here)
        ability_ops: dict[str, str] = {"eq": "Eq", "compare": "Ord"}

        # Rewrite program declarations (non-generic only)
        new_tlds: list[ast.TopLevelDecl] = []
        prog_changed = False
        for tld in program.declarations:
            if isinstance(tld.decl, ast.FnDecl) and not tld.decl.forall_vars:
                new_body = self._rewrite_ops_in_expr(
                    tld.decl.body, ability_ops)
                new_where = self._rewrite_where_fns(
                    tld.decl.where_fns, ability_ops)
                if (new_body is not tld.decl.body
                        or new_where is not tld.decl.where_fns):
                    new_decl = _replace(
                        tld.decl, body=new_body,  # type: ignore[arg-type]
                        where_fns=new_where)
                    tld = _replace(tld, decl=new_decl)
                    prog_changed = True
            new_tlds.append(tld)
        if prog_changed:
            program = _replace(program, declarations=tuple(new_tlds))

        # Rewrite monomorphized declarations
        new_monos: list[ast.FnDecl] = []
        for mdecl in mono_decls:
            new_body = self._rewrite_ops_in_expr(mdecl.body, ability_ops)
            new_where = self._rewrite_where_fns(
                mdecl.where_fns, ability_ops)
            if new_body is not mdecl.body or new_where is not mdecl.where_fns:
                mdecl = _replace(
                    mdecl, body=new_body,  # type: ignore[arg-type]
                    where_fns=new_where)
            new_monos.append(mdecl)

        return program, new_monos

    def _rewrite_where_fns(
        self,
        where_fns: tuple[ast.FnDecl, ...] | None,
        ability_ops: dict[str, str],
    ) -> tuple[ast.FnDecl, ...] | None:
        """Rewrite ability ops in where-block function bodies."""
        if not where_fns:
            return where_fns
        from dataclasses import replace as _replace

        new_fns: list[ast.FnDecl] = []
        changed = False
        for wfn in where_fns:
            new_body = self._rewrite_ops_in_expr(wfn.body, ability_ops)
            if new_body is not wfn.body:
                new_fns.append(_replace(wfn, body=new_body))  # type: ignore[arg-type]
                changed = True
            else:
                new_fns.append(wfn)
        return tuple(new_fns) if changed else where_fns

    def _rewrite_ops_in_expr(
        self,
        expr: ast.Expr,
        ability_ops: dict[str, str],
    ) -> ast.Expr:
        """Recursively rewrite ability op calls in an expression tree."""
        from dataclasses import replace as _replace

        # FnCall: check if it's an ability op to rewrite
        if isinstance(expr, ast.FnCall):
            if (expr.name in ability_ops
                    and expr.name not in self._fn_sigs):
                # eq(a, b) → BinaryExpr(a, EQ, b)
                if expr.name == "eq" and len(expr.args) == 2:
                    left = self._rewrite_ops_in_expr(
                        expr.args[0], ability_ops)
                    right = self._rewrite_ops_in_expr(
                        expr.args[1], ability_ops)
                    return ast.BinaryExpr(
                        left=left, op=ast.BinOp.EQ, right=right,
                        span=expr.span,
                    )
                # compare(a, b) →
                #   if a < b then Less
                #   else if a == b then Equal
                #   else Greater
                if expr.name == "compare" and len(expr.args) == 2:
                    left = self._rewrite_ops_in_expr(
                        expr.args[0], ability_ops)
                    right = self._rewrite_ops_in_expr(
                        expr.args[1], ability_ops)
                    return ast.IfExpr(
                        condition=ast.BinaryExpr(
                            left=left, op=ast.BinOp.LT, right=right,
                            span=expr.span,
                        ),
                        then_branch=ast.Block(
                            statements=(), span=expr.span,
                            expr=ast.NullaryConstructor(
                                name="Less", span=expr.span),
                        ),
                        else_branch=ast.Block(
                            statements=(), span=expr.span,
                            expr=ast.IfExpr(
                                condition=ast.BinaryExpr(
                                    left=left, op=ast.BinOp.EQ,
                                    right=right, span=expr.span,
                                ),
                                then_branch=ast.Block(
                                    statements=(), span=expr.span,
                                    expr=ast.NullaryConstructor(
                                        name="Equal", span=expr.span),
                                ),
                                else_branch=ast.Block(
                                    statements=(), span=expr.span,
                                    expr=ast.NullaryConstructor(
                                        name="Greater", span=expr.span),
                                ),
                                span=expr.span,
                            ),
                        ),
                        span=expr.span,
                    )
            # Recurse into args of non-ability calls
            new_args = tuple(
                self._rewrite_ops_in_expr(a, ability_ops)
                for a in expr.args
            )
            if any(n is not o for n, o in zip(new_args, expr.args)):
                return _replace(expr, args=new_args)
            return expr

        # Block: rewrite statements + final expr
        if isinstance(expr, ast.Block):
            new_stmts = tuple(
                self._rewrite_ops_in_stmt(s, ability_ops)
                for s in expr.statements
            )
            new_final = self._rewrite_ops_in_expr(expr.expr, ability_ops)
            if (any(n is not o for n, o in zip(new_stmts, expr.statements))
                    or new_final is not expr.expr):
                return _replace(
                    expr, statements=new_stmts, expr=new_final)
            return expr

        if isinstance(expr, ast.BinaryExpr):
            left = self._rewrite_ops_in_expr(expr.left, ability_ops)
            right = self._rewrite_ops_in_expr(expr.right, ability_ops)
            if left is not expr.left or right is not expr.right:
                return _replace(expr, left=left, right=right)
            return expr

        if isinstance(expr, ast.UnaryExpr):
            operand = self._rewrite_ops_in_expr(expr.operand, ability_ops)
            if operand is not expr.operand:
                return _replace(expr, operand=operand)
            return expr

        if isinstance(expr, ast.IfExpr):
            cond = self._rewrite_ops_in_expr(expr.condition, ability_ops)
            then = self._rewrite_ops_in_expr(expr.then_branch, ability_ops)
            els = self._rewrite_ops_in_expr(expr.else_branch, ability_ops)
            if (cond is not expr.condition or then is not expr.then_branch
                    or els is not expr.else_branch):
                return _replace(
                    expr, condition=cond,
                    then_branch=then,  # type: ignore[arg-type]
                    else_branch=els)  # type: ignore[arg-type]
            return expr

        if isinstance(expr, ast.MatchExpr):
            scr = self._rewrite_ops_in_expr(expr.scrutinee, ability_ops)
            rewritten_arms: list[ast.MatchArm] = []
            for arm in expr.arms:
                new_body = self._rewrite_ops_in_expr(arm.body, ability_ops)
                if new_body is not arm.body:
                    rewritten_arms.append(_replace(arm, body=new_body))
                else:
                    rewritten_arms.append(arm)
            new_arms = tuple(rewritten_arms)
            if (scr is not expr.scrutinee
                    or any(n is not o
                           for n, o in zip(new_arms, expr.arms))):
                return _replace(expr, scrutinee=scr, arms=new_arms)
            return expr

        if isinstance(expr, ast.ConstructorCall):
            new_args = tuple(
                self._rewrite_ops_in_expr(a, ability_ops)
                for a in expr.args
            )
            if any(n is not o for n, o in zip(new_args, expr.args)):
                return _replace(expr, args=new_args)
            return expr

        if isinstance(expr, ast.AnonFn):
            new_body = self._rewrite_ops_in_expr(expr.body, ability_ops)
            if new_body is not expr.body:
                return _replace(expr, body=new_body)  # type: ignore[arg-type]
            return expr

        if isinstance(expr, ast.ModuleCall):
            new_args = tuple(
                self._rewrite_ops_in_expr(a, ability_ops)
                for a in expr.args
            )
            if any(n is not o for n, o in zip(new_args, expr.args)):
                return _replace(expr, args=new_args)
            return expr

        # Leaf nodes (literals, slot refs, etc.) — no rewriting needed
        return expr

    def _rewrite_ops_in_stmt(
        self,
        stmt: ast.Stmt,
        ability_ops: dict[str, str],
    ) -> ast.Stmt:
        """Rewrite ability ops inside a statement."""
        from dataclasses import replace as _replace

        if isinstance(stmt, ast.LetStmt):
            new_val = self._rewrite_ops_in_expr(stmt.value, ability_ops)
            if new_val is not stmt.value:
                return _replace(stmt, value=new_val)
        elif isinstance(stmt, ast.ExprStmt):
            new_expr = self._rewrite_ops_in_expr(stmt.expr, ability_ops)
            if new_expr is not stmt.expr:
                return _replace(stmt, expr=new_expr)
        return stmt
