"""Vera code generator — AST to WebAssembly compilation.

Compiles a type-checked and verified Vera Program AST to WebAssembly.
Generates WAT (WebAssembly Text Format) as the intermediate representation,
then converts to WASM binary via wasmtime.  Provides execution support
with host function bindings for IO and State effects.

See spec/11-compilation.md for the compilation specification.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field, fields, replace
from io import StringIO
from typing import Any

import wasmtime

from vera import ast
from vera.errors import Diagnostic, SourceLocation
from vera.types import (
    BOOL,
    INT,
    NAT,
    STRING,
    UNIT,
    ConcreteEffectRow,
    FunctionType,
    PrimitiveType,
    PureEffectRow,
    Type,
    base_type,
)
from vera.wasm import StringPool, WasmContext, WasmSlotEnv, wasm_type


# =====================================================================
# ADT memory layout
# =====================================================================


@dataclass
class ConstructorLayout:
    """WASM memory layout for a single ADT constructor."""

    tag: int  # discriminant (0, 1, 2, ...)
    field_offsets: tuple[tuple[int, str], ...]  # (byte_offset, wasm_type) per field
    total_size: int  # total bytes, 8-byte aligned


def _wasm_type_size(wt: str) -> int:
    """Byte size of a WASM value type."""
    if wt == "i32":
        return 4
    if wt in ("i64", "f64"):
        return 8
    raise ValueError(f"Unknown WASM type: {wt}")


def _wasm_type_align(wt: str) -> int:
    """Natural alignment of a WASM value type."""
    if wt == "i32":
        return 4
    if wt in ("i64", "f64"):
        return 8
    raise ValueError(f"Unknown WASM type: {wt}")


def _align_up(offset: int, align: int) -> int:
    """Round offset up to the next multiple of align."""
    return (offset + align - 1) & ~(align - 1)


# =====================================================================
# Public API
# =====================================================================

@dataclass
class CompileResult:
    """Result of compiling a Vera program to WebAssembly."""

    wat: str
    wasm_bytes: bytes
    exports: list[str]
    diagnostics: list[Diagnostic] = field(default_factory=list)
    state_types: list[tuple[str, str]] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        """True if compilation succeeded with no errors."""
        return not any(d.severity == "error" for d in self.diagnostics)


@dataclass
class ExecuteResult:
    """Result of executing a WASM function."""

    value: int | float | None  # Return value (None for void/Unit functions)
    stdout: str  # Captured IO.print output
    state: dict[str, int | float] = field(default_factory=dict)


def compile(
    program: ast.Program,
    source: str = "",
    file: str | None = None,
) -> CompileResult:
    """Compile a type-checked Vera Program AST to WebAssembly.

    Returns a CompileResult with WAT text, WASM binary, exports,
    and any diagnostics.  The program should already have passed
    type checking and (optionally) verification.
    """
    gen = CodeGenerator(source=source, file=file)
    return gen.compile_program(program)


def execute(
    result: CompileResult,
    fn_name: str | None = None,
    args: list[int | float] | None = None,
    initial_state: dict[str, int | float] | None = None,
) -> ExecuteResult:
    """Execute a function from a compiled WASM module.

    Uses wasmtime to instantiate the module with host bindings
    for IO and State effects.  Returns the function's return value,
    any captured stdout output, and final state values.
    """
    if not result.ok:
        raise RuntimeError("Cannot execute: compilation had errors")

    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, result.wat)
    linker = wasmtime.Linker(engine)
    store = wasmtime.Store(engine)

    # Captured output from IO.print
    output_buf = StringIO()

    # Host function: vera.print(ptr: i32, len: i32) -> ()
    def host_print(caller: wasmtime.Caller, ptr: int, length: int) -> None:
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)
        buf = memory.data_ptr(store)
        data = bytes(buf[ptr:ptr + length])
        text = data.decode("utf-8")
        output_buf.write(text)

    print_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [],
    )
    linker.define_func(
        "vera", "print", print_type, host_print, access_caller=True
    )

    # State<T> host functions
    _WASM_VAL_TYPE = {
        "i64": wasmtime.ValType.i64(),
        "i32": wasmtime.ValType.i32(),
        "f64": wasmtime.ValType.f64(),
    }
    _DEFAULT_STATE: dict[str, int | float] = {
        "i64": 0, "i32": 0, "f64": 0.0,
    }

    state_store: dict[str, int | float] = {}

    for type_name, wasm_t in result.state_types:
        state_key = f"State_{type_name}"
        state_store[state_key] = _DEFAULT_STATE[wasm_t]
        val_type = _WASM_VAL_TYPE[wasm_t]

        # Closure factories to capture correct state_key per type
        def _make_host_get(key: str):  # type: ignore[no-untyped-def]
            def host_get() -> int | float:
                return state_store[key]
            return host_get

        def _make_host_put(key: str):  # type: ignore[no-untyped-def]
            def host_put(val: int | float) -> None:
                state_store[key] = val
            return host_put

        get_type = wasmtime.FuncType([], [val_type])
        linker.define_func(
            "vera", f"state_get_{type_name}", get_type,
            _make_host_get(state_key),
        )

        put_type = wasmtime.FuncType([val_type], [])
        linker.define_func(
            "vera", f"state_put_{type_name}", put_type,
            _make_host_put(state_key),
        )

    # Apply initial state overrides (for testing)
    if initial_state:
        for key, val in initial_state.items():
            if key in state_store:
                state_store[key] = val

    instance = linker.instantiate(store, module)

    # Determine function to call
    if fn_name is None:
        # Try "main" first, then first export
        if "main" in result.exports:
            fn_name = "main"
        elif result.exports:
            fn_name = result.exports[0]
        else:
            raise RuntimeError("No exported functions to call")

    func = instance.exports(store).get(fn_name)
    if func is None or not isinstance(func, wasmtime.Func):
        raise RuntimeError(f"Function '{fn_name}' not found in exports")

    # Call with arguments
    call_args: list[int | float] = args or []
    raw_result = func(store, *call_args)

    # Extract return value
    value: int | float | None
    if raw_result is None:
        value = None
    elif isinstance(raw_result, float):
        value = raw_result
    elif isinstance(raw_result, int):
        value = raw_result
    else:
        value = int(raw_result)

    return ExecuteResult(
        value=value,
        stdout=output_buf.getvalue(),
        state=dict(state_store),
    )


# =====================================================================
# Code generator
# =====================================================================

class CodeGenerator:
    """Compiles a Vera Program AST to WebAssembly.

    Two-pass approach:
    1. Registration: collect function signatures for forward references
    2. Compilation: generate WAT for each compilable function
    """

    def __init__(
        self,
        source: str = "",
        file: str | None = None,
    ) -> None:
        self.source = source
        self.file = file
        self.diagnostics: list[Diagnostic] = []
        self.string_pool = StringPool()

        # Registered function signatures: name -> (param_types, return_type)
        self._fn_sigs: dict[str, tuple[list[str | None], str | None]] = {}
        # Track which effect operations are needed
        self._needs_io_print: bool = False
        self._needs_memory: bool = False
        self._state_types: list[tuple[str, str]] = []  # (type_name, wasm_type)

        # ADT layout metadata (populated during registration)
        self._adt_layouts: dict[str, dict[str, ConstructorLayout]] = {}
        self._needs_alloc: bool = False

        # Type aliases (populated during registration)
        # Maps alias name -> TypeExpr (for resolving function type aliases)
        self._type_aliases: dict[str, ast.TypeExpr] = {}

        # Closure compilation state
        self._closure_table: list[str] = []  # lifted fn names for table
        self._closure_sigs: dict[str, str] = {}  # sig_key -> WAT type decl
        self._closure_fns_wat: list[str] = []  # WAT for lifted closures
        self._needs_table: bool = False
        self._next_closure_id: int = 0

    # -----------------------------------------------------------------
    # Diagnostics
    # -----------------------------------------------------------------

    def _warning(
        self,
        node: ast.Node,
        description: str,
        *,
        rationale: str = "",
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
        # Pass 1: register all function signatures
        self._register_all(program)

        # Pass 1.5: monomorphize generic functions
        mono_decls = self._monomorphize(program)
        for mdecl in mono_decls:
            self._register_fn(mdecl)

        # Pass 2: compile function bodies
        functions_wat: list[str] = []
        exports: list[str] = []

        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                fn_wat = self._compile_fn(decl)
                if fn_wat is not None:
                    functions_wat.append(fn_wat)
                    exports.append(decl.name)
                    # Also compile where-block functions
                    if decl.where_fns:
                        for wfn in decl.where_fns:
                            wfn_wat = self._compile_fn(wfn, export=False)
                            if wfn_wat is not None:
                                functions_wat.append(wfn_wat)

        # Compile monomorphized functions
        for mdecl in mono_decls:
            fn_wat = self._compile_fn(mdecl)
            if fn_wat is not None:
                functions_wat.append(fn_wat)
                exports.append(mdecl.name)

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
            )

        return CompileResult(
            wat=wat,
            wasm_bytes=bytes(wasm_bytes),
            exports=exports,
            diagnostics=self.diagnostics,
            state_types=list(self._state_types),
        )

    # -----------------------------------------------------------------
    # Registration pass
    # -----------------------------------------------------------------

    def _register_all(self, program: ast.Program) -> None:
        """Register all function signatures, ADT layouts, and type aliases."""
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                self._register_fn(decl)
            elif isinstance(decl, ast.DataDecl):
                self._register_data(decl)
            elif isinstance(decl, ast.TypeAliasDecl):
                self._type_aliases[decl.name] = decl.type_expr

    def _register_fn(self, decl: ast.FnDecl) -> None:
        """Register a function's WASM signature."""
        param_types: list[str | None] = []
        for p in decl.params:
            wt = self._type_expr_to_wasm_type(p)
            param_types.append(wt)

        ret_type = self._type_expr_to_wasm_type(decl.return_type)
        self._fn_sigs[decl.name] = (param_types, ret_type)

        # Register where-block functions
        if decl.where_fns:
            for wfn in decl.where_fns:
                self._register_fn(wfn)

    def _register_data(self, decl: ast.DataDecl) -> None:
        """Register an ADT and precompute constructor layouts."""
        layouts: dict[str, ConstructorLayout] = {}
        for tag, ctor in enumerate(decl.constructors):
            layout = self._compute_constructor_layout(tag, ctor, decl)
            layouts[ctor.name] = layout
        self._adt_layouts[decl.name] = layouts
        self._needs_alloc = True
        self._needs_memory = True

    # -----------------------------------------------------------------
    # Monomorphization
    # -----------------------------------------------------------------

    def _monomorphize(
        self, program: ast.Program,
    ) -> list[ast.FnDecl]:
        """Monomorphize generic functions for all concrete call sites.

        Returns a list of new FnDecl nodes with type variables replaced
        by concrete types and names mangled.
        """
        # Identify generic function declarations
        generic_decls: dict[str, ast.FnDecl] = {}
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and decl.forall_vars:
                generic_decls[decl.name] = decl

        if not generic_decls:
            return []

        # Build constructor → ADT name mapping
        ctor_to_adt: dict[str, str] = {}
        for adt_name in self._adt_layouts:
            for ctor_name in self._adt_layouts[adt_name]:
                ctor_to_adt[ctor_name] = adt_name

        # Collect concrete instantiations from non-generic function bodies
        instances: dict[str, set[tuple[str, ...]]] = {
            name: set() for name in generic_decls
        }
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and not decl.forall_vars:
                self._collect_calls_in_expr(
                    decl.body, generic_decls, ctor_to_adt, instances,
                )

        # Generate monomorphized FnDecls
        mono_decls: list[ast.FnDecl] = []
        for fn_name, type_arg_set in instances.items():
            for concrete_types in type_arg_set:
                decl = generic_decls[fn_name]
                mono = self._monomorphize_fn(decl, concrete_types)
                mono_decls.append(mono)

        # Store generic fn info for call rewriting in wasm.py
        self._generic_fn_info: dict[
            str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]
        ] = {}
        for name, decl in generic_decls.items():
            assert decl.forall_vars is not None
            self._generic_fn_info[name] = (decl.forall_vars, decl.params)

        return mono_decls

    def _collect_calls_in_expr(
        self,
        expr: ast.Expr,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
    ) -> None:
        """Walk an expression tree collecting generic call sites."""
        if isinstance(expr, ast.FnCall) and expr.name in generic_decls:
            decl = generic_decls[expr.name]
            type_args = self._infer_type_args_from_call(
                decl, expr, ctor_to_adt, generic_decls,
            )
            if type_args is not None:
                instances[expr.name].add(type_args)

        # Recurse into sub-expressions
        if isinstance(expr, ast.Block):
            for stmt in expr.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._collect_calls_in_expr(
                        stmt.value, generic_decls, ctor_to_adt, instances,
                    )
                elif isinstance(stmt, ast.ExprStmt):
                    self._collect_calls_in_expr(
                        stmt.expr, generic_decls, ctor_to_adt, instances,
                    )
            self._collect_calls_in_expr(
                expr.expr, generic_decls, ctor_to_adt, instances,
            )
        elif isinstance(expr, ast.BinaryExpr):
            self._collect_calls_in_expr(
                expr.left, generic_decls, ctor_to_adt, instances,
            )
            self._collect_calls_in_expr(
                expr.right, generic_decls, ctor_to_adt, instances,
            )
        elif isinstance(expr, ast.UnaryExpr):
            self._collect_calls_in_expr(
                expr.operand, generic_decls, ctor_to_adt, instances,
            )
        elif isinstance(expr, ast.IfExpr):
            self._collect_calls_in_expr(
                expr.condition, generic_decls, ctor_to_adt, instances,
            )
            self._collect_calls_in_expr(
                expr.then_branch, generic_decls, ctor_to_adt, instances,
            )
            self._collect_calls_in_expr(
                expr.else_branch, generic_decls, ctor_to_adt, instances,
            )
        elif isinstance(expr, ast.FnCall):
            for arg in expr.args:
                self._collect_calls_in_expr(
                    arg, generic_decls, ctor_to_adt, instances,
                )
        elif isinstance(expr, ast.ConstructorCall):
            for arg in expr.args:
                self._collect_calls_in_expr(
                    arg, generic_decls, ctor_to_adt, instances,
                )
        elif isinstance(expr, ast.MatchExpr):
            self._collect_calls_in_expr(
                expr.scrutinee, generic_decls, ctor_to_adt, instances,
            )
            for arm in expr.arms:
                self._collect_calls_in_expr(
                    arm.body, generic_decls, ctor_to_adt, instances,
                )

    def _infer_type_args_from_call(
        self,
        decl: ast.FnDecl,
        call: ast.FnCall,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> tuple[str, ...] | None:
        """Infer concrete type variable bindings from a call's arguments.

        Returns a tuple of concrete type names, one per forall_var, or
        None if inference fails.
        """
        forall_vars = decl.forall_vars
        if not forall_vars:
            return None

        mapping: dict[str, str] = {}
        for param_te, arg in zip(decl.params, call.args):
            self._unify_param_arg(param_te, arg, forall_vars, ctor_to_adt,
                                  mapping, generic_decls)

        # Check all type vars are resolved
        result = []
        for tv in forall_vars:
            if tv not in mapping:
                return None
            result.append(mapping[tv])
        return tuple(result)

    def _unify_param_arg(
        self,
        param_te: ast.TypeExpr,
        arg: ast.Expr,
        forall_vars: tuple[str, ...],
        ctor_to_adt: dict[str, str],
        mapping: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> None:
        """Unify a parameter TypeExpr against an argument to bind type vars."""
        if isinstance(param_te, ast.RefinementType):
            self._unify_param_arg(
                param_te.base_type, arg, forall_vars, ctor_to_adt, mapping,
                generic_decls,
            )
            return

        if not isinstance(param_te, ast.NamedType):
            return

        if param_te.name in forall_vars:
            # Direct type variable — infer from argument
            vera_type = self._infer_vera_type_name(
                arg, ctor_to_adt, generic_decls)
            if vera_type and param_te.name not in mapping:
                mapping[param_te.name] = vera_type
            return

        # Parameterized type like Option<T> — match type args
        if param_te.type_args:
            arg_info = self._get_arg_type_info(arg, ctor_to_adt)
            if arg_info and arg_info[0] == param_te.name:
                for param_ta, arg_ta_name in zip(
                    param_te.type_args, arg_info[1]
                ):
                    if (isinstance(param_ta, ast.NamedType)
                            and param_ta.name in forall_vars
                            and param_ta.name not in mapping):
                        mapping[param_ta.name] = arg_ta_name

    def _infer_vera_type_name(
        self,
        expr: ast.Expr,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> str | None:
        """Infer the simple Vera type name of an expression."""
        if isinstance(expr, ast.IntLit):
            return "Int"
        if isinstance(expr, ast.BoolLit):
            return "Bool"
        if isinstance(expr, ast.FloatLit):
            return "Float64"
        if isinstance(expr, ast.UnitLit):
            return "Unit"
        if isinstance(expr, ast.SlotRef):
            return expr.type_name
        if isinstance(expr, ast.ConstructorCall):
            return ctor_to_adt.get(expr.name)
        if isinstance(expr, ast.NullaryConstructor):
            return ctor_to_adt.get(expr.name)
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in (ast.BinOp.EQ, ast.BinOp.NEQ, ast.BinOp.LT,
                           ast.BinOp.GT, ast.BinOp.LE, ast.BinOp.GE,
                           ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES):
                return "Bool"
            return self._infer_vera_type_name(
                expr.left, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.UnaryExpr):
            if expr.op == ast.UnaryOp.NOT:
                return "Bool"
            return self._infer_vera_type_name(
                expr.operand, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.IfExpr):
            return self._infer_vera_type_name(
                expr.then_branch.expr, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.FnCall) and generic_decls:
            return self._infer_fncall_vera_type(
                expr, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.FnCall):
            return self._infer_fncall_vera_type_simple(expr)
        return None

    def _infer_fncall_vera_type(
        self,
        call: ast.FnCall,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl],
    ) -> str | None:
        """Infer the Vera return type of a function call.

        For generic calls, infers type variable bindings from arguments,
        then substitutes into the return TypeExpr.
        """
        if call.name in generic_decls:
            decl = generic_decls[call.name]
            type_args = self._infer_type_args_from_call(
                decl, call, ctor_to_adt, generic_decls,
            )
            if type_args and decl.forall_vars:
                mapping = dict(zip(decl.forall_vars, type_args))
                ret_te = decl.return_type
                if isinstance(ret_te, ast.NamedType):
                    return mapping.get(ret_te.name, ret_te.name)
        return self._infer_fncall_vera_type_simple(call)

    def _infer_fncall_vera_type_simple(self, call: ast.FnCall) -> str | None:
        """Infer Vera return type from registered function signatures."""
        sig = self._fn_sigs.get(call.name)
        if sig:
            _, ret_wt = sig
            if ret_wt == "i64":
                return "Int"
            if ret_wt == "i32":
                return "Bool"
            if ret_wt == "f64":
                return "Float64"
        return None

    def _get_arg_type_info(
        self, expr: ast.Expr, ctor_to_adt: dict[str, str],
    ) -> tuple[str, tuple[str, ...]] | None:
        """Get (type_name, type_arg_names) for an argument expression.

        Used to match parameterized types like Option<T> against
        concrete arguments like @Option<Int>.0.
        """
        if isinstance(expr, ast.SlotRef):
            if expr.type_args:
                arg_names = []
                for ta in expr.type_args:
                    if isinstance(ta, ast.NamedType):
                        arg_names.append(ta.name)
                    else:
                        return None
                return (expr.type_name, tuple(arg_names))
            return (expr.type_name, ())
        if isinstance(expr, ast.ConstructorCall):
            adt_name = ctor_to_adt.get(expr.name)
            if adt_name:
                # Infer type args from constructor arguments
                arg_types = []
                for a in expr.args:
                    t = self._infer_vera_type_name(a, ctor_to_adt)
                    if t:
                        arg_types.append(t)
                    else:
                        return None
                return (adt_name, tuple(arg_types))
        return None

    @staticmethod
    def _mangle_fn_name(name: str, concrete_types: tuple[str, ...]) -> str:
        """Produce a mangled name for a monomorphized function.

        Example: identity + ("Int",) -> "identity$Int"
        """
        return f"{name}${'_'.join(concrete_types)}"

    def _monomorphize_fn(
        self,
        decl: ast.FnDecl,
        concrete_types: tuple[str, ...],
    ) -> ast.FnDecl:
        """Create a monomorphized copy of a generic function.

        Replaces type variables with concrete types throughout the AST
        and mangles the function name.
        """
        assert decl.forall_vars is not None
        mapping = dict(zip(decl.forall_vars, concrete_types))
        mangled = self._mangle_fn_name(decl.name, concrete_types)

        # Substitute type variables in the entire FnDecl
        substituted = self._substitute_in_ast(decl, mapping)
        assert isinstance(substituted, ast.FnDecl)

        # Override name and clear forall_vars
        return replace(substituted, name=mangled, forall_vars=None)

    def _substitute_in_ast(
        self, node: ast.Node, mapping: dict[str, str],
    ) -> ast.Node:
        """Recursively substitute type variable names in an AST subtree.

        Handles NamedType (type expressions) and SlotRef (slot references)
        as special cases; all other nodes are walked generically via
        dataclass fields.
        """
        # Special case: NamedType — substitute type variable names
        if isinstance(node, ast.NamedType):
            new_name = mapping.get(node.name, node.name)
            new_args: tuple[ast.TypeExpr, ...] | None = node.type_args
            if node.type_args:
                new_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )
            if new_name != node.name or new_args is not node.type_args:
                return replace(node, name=new_name, type_args=new_args)
            return node

        # Special case: SlotRef — substitute type_name and type_args
        if isinstance(node, ast.SlotRef):
            new_type_name = mapping.get(node.type_name, node.type_name)
            new_slot_args: tuple[ast.TypeExpr, ...] | None = node.type_args
            if node.type_args:
                new_slot_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )
            if (new_type_name != node.type_name
                    or new_slot_args is not node.type_args):
                return replace(
                    node, type_name=new_type_name, type_args=new_slot_args,
                )
            return node

        # Special case: ResultRef — substitute type_name and type_args
        if isinstance(node, ast.ResultRef):
            new_type_name = mapping.get(node.type_name, node.type_name)
            new_res_args: tuple[ast.TypeExpr, ...] | None = node.type_args
            if node.type_args:
                new_res_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )
            if (new_type_name != node.type_name
                    or new_res_args is not node.type_args):
                return replace(
                    node, type_name=new_type_name, type_args=new_res_args,
                )
            return node

        # Generic case: recurse into all dataclass fields
        changes: dict[str, Any] = {}
        for f in fields(node):
            if f.name == "span":
                continue
            val = getattr(node, f.name)
            new_val = self._substitute_value(val, mapping)
            if new_val is not val:
                changes[f.name] = new_val

        if changes:
            return replace(node, **changes)
        return node

    def _substitute_value(
        self, val: Any, mapping: dict[str, str],
    ) -> Any:
        """Recursively substitute type variables in a field value."""
        if isinstance(val, ast.Node):
            return self._substitute_in_ast(val, mapping)
        if isinstance(val, tuple):
            new_items = tuple(
                self._substitute_value(v, mapping) for v in val
            )
            if any(n is not o for n, o in zip(new_items, val)):
                return new_items
            return val
        return val

    def _substitute_type_expr(
        self, te: ast.TypeExpr, mapping: dict[str, str],
    ) -> ast.TypeExpr:
        """Substitute type variables in a TypeExpr, returning a TypeExpr."""
        result = self._substitute_in_ast(te, mapping)
        assert isinstance(result, ast.TypeExpr)
        return result

    def _compute_constructor_layout(
        self,
        tag: int,
        ctor: ast.Constructor,
        decl: ast.DataDecl,
    ) -> ConstructorLayout:
        """Compute the memory layout for a single constructor.

        Layout: [tag: i32 (4 bytes)] [pad] [field0] [field1] ...
        Total size rounded up to 8-byte multiple.
        """
        offset = 4  # tag (i32) at offset 0, occupies 4 bytes
        field_offsets: list[tuple[int, str]] = []

        if ctor.fields is not None:
            for field_te in ctor.fields:
                wt = self._resolve_field_wasm_type(field_te, decl)
                align = _wasm_type_align(wt)
                offset = _align_up(offset, align)
                field_offsets.append((offset, wt))
                offset += _wasm_type_size(wt)

        total_size = _align_up(offset, 8) if offset > 0 else 8
        return ConstructorLayout(
            tag=tag,
            field_offsets=tuple(field_offsets),
            total_size=total_size,
        )

    def _resolve_field_wasm_type(
        self,
        te: ast.TypeExpr,
        decl: ast.DataDecl,
    ) -> str:
        """Resolve a constructor field's TypeExpr to a WASM type.

        Type parameters and ADT references map to i32 (heap pointer).
        Known primitives map to their native WASM types.
        """
        if isinstance(te, ast.NamedType):
            # Type parameter of the parent ADT → pointer
            if decl.type_params and te.name in decl.type_params:
                return "i32"
            wt = self._type_expr_to_wasm_type(te)
            if wt is None:
                return "i32"  # Unit → pointer (shouldn't appear, safe fallback)
            if wt == "unsupported":
                return "i32"  # ADT/String/other → heap pointer
            return wt
        if isinstance(te, ast.RefinementType):
            return self._resolve_field_wasm_type(te.base_type, decl)
        return "i32"  # default: pointer

    # -----------------------------------------------------------------
    # Function compilation
    # -----------------------------------------------------------------

    def _compile_fn(
        self, decl: ast.FnDecl, *, export: bool = True
    ) -> str | None:
        """Compile a single function to WAT.

        Returns the WAT function string, or None if not compilable
        (with a warning diagnostic).
        """
        # Check if function is compilable
        if not self._is_compilable(decl):
            return None

        # Build effect_ops mapping for State<T> operations
        effect_ops: dict[str, tuple[str, bool]] = {}
        if isinstance(decl.effect, ast.EffectSet):
            for eff in decl.effect.effects:
                if (isinstance(eff, ast.EffectRef) and eff.name == "State"
                        and eff.type_args and len(eff.type_args) == 1):
                    type_name = self._type_expr_to_slot_name(eff.type_args[0])
                    if type_name:
                        # Only map if no user-defined function shadows the op
                        if "get" not in self._fn_sigs:
                            effect_ops["get"] = (
                                f"$vera.state_get_{type_name}", False
                            )
                        if "put" not in self._fn_sigs:
                            effect_ops["put"] = (
                                f"$vera.state_put_{type_name}", True
                            )

        # Flatten ADT layouts into ctor_name -> layout for WasmContext
        ctor_layouts = {}
        ctor_to_adt: dict[str, str] = {}
        for adt_name, layouts in self._adt_layouts.items():
            ctor_layouts.update(layouts)
            for ctor_name in layouts:
                ctor_to_adt[ctor_name] = adt_name
        adt_type_names = set(self._adt_layouts.keys())

        ctx = WasmContext(
            self.string_pool,
            effect_ops=effect_ops,
            ctor_layouts=ctor_layouts,
            adt_type_names=adt_type_names,
            generic_fn_info=getattr(self, "_generic_fn_info", None),
            ctor_to_adt=ctor_to_adt,
        )
        # Build function return type map for FnCall type inference
        fn_ret_types: dict[str, str | None] = {}
        for fn_name, (_, ret_wt) in self._fn_sigs.items():
            if ret_wt != "unsupported":
                fn_ret_types[fn_name] = ret_wt
        ctx.set_fn_ret_types(fn_ret_types)
        # Provide type aliases so closures can resolve FnType return types
        ctx.set_type_aliases(self._type_aliases)
        ctx.set_closure_id_start(self._next_closure_id)
        env = WasmSlotEnv()

        # Allocate parameters
        param_parts: list[str] = []
        for i, param_te in enumerate(decl.params):
            wt = self._type_expr_to_wasm_type(param_te)
            if wt is None:
                # Unit parameter — skip in WASM signature
                continue
            if wt == "unsupported":
                self._warning(
                    decl,
                    f"Function '{decl.name}' has unsupported parameter type.",
                    rationale="Only Int, Nat, Float64, Bool, and Unit types "
                    "are compilable in the current WASM backend.",
                )
                return None
            local_idx = ctx.alloc_param()
            param_parts.append(f"(param $p{i} {wt})")
            # Push into slot environment
            type_name = self._type_expr_to_slot_name(param_te)
            if type_name:
                env = env.push(type_name, local_idx)

        # Return type
        ret_wt = self._type_expr_to_wasm_type(decl.return_type)
        if ret_wt == "unsupported":
            self._warning(
                decl,
                f"Function '{decl.name}' has unsupported return type.",
                rationale="Only Int, Nat, Bool, and Unit types are "
                "compilable in the current WASM backend.",
            )
            return None
        result_part = f" (result {ret_wt})" if ret_wt else ""

        # Compile precondition checks
        pre_instrs = self._compile_preconditions(ctx, decl, env)

        # Compile body
        body_instrs = ctx.translate_block(decl.body, env)
        if body_instrs is None:
            self._warning(
                decl,
                f"Function '{decl.name}' body contains unsupported "
                f"expressions — skipped.",
                rationale="The WASM backend does not yet support all "
                "Vera expression types. This function will not appear "
                "in the compiled output.",
            )
            return None

        # Collect closures created during body compilation and lift them
        self._lift_pending_closures(ctx)

        # Compile postcondition checks (wrap around body result)
        post_instrs = self._compile_postconditions(ctx, decl, env, ret_wt)

        # Assemble function WAT
        export_part = f' (export "{decl.name}")' if export else ""
        header = f"  (func ${decl.name}{export_part}"
        if param_parts:
            header += " " + " ".join(param_parts)
        header += result_part

        lines = [header]

        # Extra locals (from let bindings + contract temps)
        for local_decl in ctx.extra_locals_wat():
            lines.append(f"    {local_decl}")

        # Precondition checks (at function entry)
        for instr in pre_instrs:
            lines.append(f"    {instr}")

        # Body instructions
        for instr in body_instrs:
            lines.append(f"    {instr}")

        # Postcondition checks (after body, wraps result)
        for instr in post_instrs:
            lines.append(f"    {instr}")

        lines.append("  )")
        return "\n".join(lines)

    # -----------------------------------------------------------------
    # Closure lifting
    # -----------------------------------------------------------------

    def _lift_pending_closures(self, ctx: WasmContext) -> None:
        """Lift all anonymous functions created during body compilation.

        Each pending closure is compiled to a module-level WASM function
        and added to the function table.
        """
        for anon_fn, captures, closure_id in ctx._pending_closures:
            lifted_wat = self._compile_lifted_closure(
                closure_id, anon_fn, captures,
            )
            if lifted_wat is not None:
                self._closure_fns_wat.append(lifted_wat)
                self._closure_table.append(f"$anon_{closure_id}")
                self._needs_table = True
                self._needs_alloc = True
                self._needs_memory = True

                # Register the closure signature for call_indirect
                param_wasm: list[str] = ["i32"]  # env param
                for p in anon_fn.params:
                    pname = self._type_expr_to_slot_name(p)
                    pwt = self._type_expr_to_wasm_type(p)
                    if pwt and pwt != "unsupported":
                        param_wasm.append(pwt)
                ret_wt = self._type_expr_to_wasm_type(anon_fn.return_type)
                param_part = " ".join(
                    f"(param {wt})" for wt in param_wasm
                )
                result_part = (
                    f" (result {ret_wt})" if ret_wt else ""
                )
                sig_content = f"{param_part}{result_part}"
                if sig_content not in self._closure_sigs:
                    sig_name = (
                        f"$closure_sig_{len(self._closure_sigs)}"
                    )
                    self._closure_sigs[sig_content] = sig_name

        # Update next closure ID for subsequent functions
        self._next_closure_id = ctx._next_closure_id
        # Merge closure sigs from the context (content → name)
        for sig_content, sig_name in ctx._closure_sigs.items():
            if sig_content not in self._closure_sigs:
                self._closure_sigs[sig_content] = sig_name

    def _compile_lifted_closure(
        self,
        closure_id: int,
        anon_fn: ast.AnonFn,
        captures: list[tuple[str, int, str]],
    ) -> str | None:
        """Compile an anonymous function to a module-level WASM function.

        The lifted function signature:
          (func $anon_N (param $env i32) (param ...) (result ...))

        The first parameter is the closure environment pointer.
        Captured values are loaded from the environment into locals.
        """
        # Flatten ADT layouts for context
        ctor_layouts: dict[str, ConstructorLayout] = {}
        ctor_to_adt: dict[str, str] = {}
        for adt_name, layouts in self._adt_layouts.items():
            ctor_layouts.update(layouts)
            for ctor_name in layouts:
                ctor_to_adt[ctor_name] = adt_name

        ctx = WasmContext(
            self.string_pool,
            ctor_layouts=ctor_layouts,
            adt_type_names=set(self._adt_layouts.keys()),
            ctor_to_adt=ctor_to_adt,
        )
        fn_ret_types: dict[str, str | None] = {}
        for fn_name, (_, ret_wt) in self._fn_sigs.items():
            if ret_wt != "unsupported":
                fn_ret_types[fn_name] = ret_wt
        ctx.set_fn_ret_types(fn_ret_types)
        ctx.set_type_aliases(self._type_aliases)
        env = WasmSlotEnv()

        # Parameter 0: $env (i32 — closure environment pointer)
        env_idx = ctx.alloc_param()
        param_parts = ["(param $env i32)"]

        # Allocate ALL function parameters BEFORE any locals.
        # WASM requires params to be contiguous at indices 0..N-1,
        # with locals following at N, N+1, etc.
        param_info: list[tuple[int, ast.TypeExpr, int]] = []
        for i, param_te in enumerate(anon_fn.params):
            wt = self._type_expr_to_wasm_type(param_te)
            if wt is None:
                continue  # Unit param, skip
            if wt == "unsupported":
                return None
            local_idx = ctx.alloc_param()
            param_parts.append(f"(param $p{i} {wt})")
            param_info.append((i, param_te, local_idx))

        # Compute capture layout (must match _translate_anon_fn)
        cap_offsets: list[tuple[int, str]] = []
        offset = 4  # skip func_table_idx
        for _tname, _cidx, cap_wt in captures:
            align = 8 if cap_wt in ("i64", "f64") else 4
            offset = _align_up(offset, align)
            cap_offsets.append((offset, cap_wt))
            offset += 8 if cap_wt in ("i64", "f64") else 4

        # Load captured values from env into locals (allocated AFTER params)
        cap_locals: list[tuple[str, int]] = []  # (type_name, local_idx)
        load_instrs: list[str] = []
        for i, (tname, _cidx, cap_wt) in enumerate(captures):
            cap_local = ctx.alloc_local(cap_wt)
            cap_offset, _ = cap_offsets[i]
            load_op = (
                "i64.load" if cap_wt == "i64"
                else "f64.load" if cap_wt == "f64"
                else "i32.load"
            )
            load_instrs.append(f"local.get {env_idx}")
            load_instrs.append(f"{load_op} offset={cap_offset}")
            load_instrs.append(f"local.set {cap_local}")
            cap_locals.append((tname, cap_local))

        # Build slot environment: captures first (outer scope, higher
        # De Bruijn indices), then function params on top (most recent).
        for tname, local_idx in cap_locals:
            env = env.push(tname, local_idx)
        for _i, param_te, local_idx in param_info:
            type_name = self._type_expr_to_slot_name(param_te)
            if type_name:
                env = env.push(type_name, local_idx)

        # Return type
        ret_wt = self._type_expr_to_wasm_type(anon_fn.return_type)
        if ret_wt == "unsupported":
            return None
        result_part = f" (result {ret_wt})" if ret_wt else ""

        # Compile the body
        body_instrs = ctx.translate_block(anon_fn.body, env)
        if body_instrs is None:
            return None

        # Assemble the lifted function WAT (not exported)
        fn_name = f"$anon_{closure_id}"
        header = f"  (func {fn_name}"
        if param_parts:
            header += " " + " ".join(param_parts)
        header += result_part

        lines = [header]
        for local_decl in ctx.extra_locals_wat():
            lines.append(f"    {local_decl}")
        for instr in load_instrs:
            lines.append(f"    {instr}")
        for instr in body_instrs:
            lines.append(f"    {instr}")
        lines.append("  )")
        return "\n".join(lines)

    # -----------------------------------------------------------------
    # Runtime contract insertion
    # -----------------------------------------------------------------

    def _compile_preconditions(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
        env: WasmSlotEnv,
    ) -> list[str]:
        """Compile runtime precondition checks.

        Non-trivial requires() clauses are compiled as:
            [condition]
            i32.eqz
            if
              unreachable  ;; trap on precondition violation
            end
        """
        instrs: list[str] = []
        for contract in decl.contracts:
            if not isinstance(contract, ast.Requires):
                continue
            if self._is_trivial_contract(contract):
                continue

            # Translate the precondition expression
            cond_instrs = ctx.translate_expr(contract.expr, env)
            if cond_instrs is None:
                # Can't compile this contract — skip silently
                # (verifier already classified it as Tier 3)
                continue

            instrs.extend(cond_instrs)
            instrs.append("i32.eqz")
            instrs.append("if")
            instrs.append("  unreachable")
            instrs.append("end")
        return instrs

    def _compile_postconditions(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
        env: WasmSlotEnv,
        ret_wt: str | None,
    ) -> list[str]:
        """Compile runtime postcondition checks.

        For functions returning a value:
            local.set $result_tmp    ;; save body result
            [condition with @T.result → local.get $result_tmp]
            i32.eqz
            if
              unreachable            ;; trap on postcondition violation
            end
            local.get $result_tmp    ;; push result back

        For Unit-returning functions, no result to save/restore.
        """
        # Collect non-trivial ensures clauses
        ensures_clauses: list[ast.Ensures] = []
        for contract in decl.contracts:
            if isinstance(contract, ast.Ensures):
                if not self._is_trivial_contract(contract):
                    ensures_clauses.append(contract)

        if not ensures_clauses:
            return []

        instrs: list[str] = []

        if ret_wt is not None:
            # Function returns a value — save it to a temp local
            result_local = ctx.alloc_local(ret_wt)
            ctx.set_result_local(result_local)
            instrs.append(f"local.set {result_local}")

            for ensures in ensures_clauses:
                cond_instrs = ctx.translate_expr(ensures.expr, env)
                if cond_instrs is None:
                    # Can't compile — skip
                    continue
                instrs.extend(cond_instrs)
                instrs.append("i32.eqz")
                instrs.append("if")
                instrs.append("  unreachable")
                instrs.append("end")

            # Push result back
            instrs.append(f"local.get {result_local}")
        else:
            # Unit return — no result to save, just check
            for ensures in ensures_clauses:
                cond_instrs = ctx.translate_expr(ensures.expr, env)
                if cond_instrs is None:
                    continue
                instrs.extend(cond_instrs)
                instrs.append("i32.eqz")
                instrs.append("if")
                instrs.append("  unreachable")
                instrs.append("end")

        return instrs

    @staticmethod
    def _is_trivial_contract(contract: ast.Contract) -> bool:
        """Check if a contract is trivially true (literal true).

        Trivial contracts are skipped — no runtime check needed.
        """
        if isinstance(contract, ast.Requires):
            return isinstance(contract.expr, ast.BoolLit) and contract.expr.value
        if isinstance(contract, ast.Ensures):
            return isinstance(contract.expr, ast.BoolLit) and contract.expr.value
        return False

    # -----------------------------------------------------------------
    # Module assembly
    # -----------------------------------------------------------------

    def _assemble_module(self, functions: list[str]) -> str:
        """Assemble a complete WAT module from compiled functions."""
        parts: list[str] = ["(module"]

        # Import IO.print if needed
        if self._needs_io_print:
            parts.append(
                '  (import "vera" "print" '
                "(func $vera.print (param i32 i32)))"
            )

        # Import State<T> host functions if needed
        for type_name, wasm_t in self._state_types:
            parts.append(
                f'  (import "vera" "state_get_{type_name}" '
                f"(func $vera.state_get_{type_name} (result {wasm_t})))"
            )
            parts.append(
                f'  (import "vera" "state_put_{type_name}" '
                f"(func $vera.state_put_{type_name} (param {wasm_t})))"
            )

        # Memory (for string data and heap)
        if self._needs_memory or self.string_pool.has_strings():
            parts.append('  (memory (export "memory") 1)')

        # Data section (string constants)
        for value, offset, _length in self.string_pool.entries():
            # Escape special characters for WAT string literals
            escaped = self._escape_wat_string(value)
            parts.append(f'  (data (i32.const {offset}) "{escaped}")')

        # Heap pointer global and bump allocator (for ADT allocation)
        if self._needs_alloc:
            heap_start = self.string_pool.heap_offset
            parts.append(
                f"  (global $heap_ptr (export \"heap_ptr\") "
                f"(mut i32) (i32.const {heap_start}))"
            )
            parts.append(
                "  (func $alloc (param $size i32) (result i32)\n"
                "    (local $ptr i32)\n"
                "    ;; Save current heap pointer\n"
                "    global.get $heap_ptr\n"
                "    local.set $ptr\n"
                "    ;; Advance heap_ptr by size rounded up to 8\n"
                "    global.get $heap_ptr\n"
                "    local.get $size\n"
                "    i32.const 7\n"
                "    i32.add\n"
                "    i32.const -8\n"
                "    i32.and\n"
                "    i32.add\n"
                "    global.set $heap_ptr\n"
                "    ;; Return old pointer\n"
                "    local.get $ptr\n"
                "  )"
            )

        # Closure type declarations (for call_indirect)
        for sig_content, sig_name in self._closure_sigs.items():
            parts.append(f"  (type {sig_name} (func {sig_content}))")

        # Function table (for indirect calls via closures)
        if self._needs_table and self._closure_table:
            table_size = len(self._closure_table)
            parts.append(f"  (table {table_size} funcref)")
            elem_entries = " ".join(self._closure_table)
            parts.append(
                f"  (elem (i32.const 0) func {elem_entries})"
            )

        # Functions (user-defined)
        for fn_wat in functions:
            parts.append(fn_wat)

        # Lifted closure functions
        for closure_wat in self._closure_fns_wat:
            parts.append(closure_wat)

        parts.append(")")
        return "\n".join(parts)

    # -----------------------------------------------------------------
    # Compilability check
    # -----------------------------------------------------------------

    def _is_compilable(self, decl: ast.FnDecl) -> bool:
        """Check if a function can be compiled to WASM.

        Accepts pure functions, IO effects, and State<T> where T is
        a compilable primitive type (Int, Nat, Bool, Float64).
        """
        # Check effect: must be pure, <IO>, or <State<T>>
        effect = decl.effect
        if isinstance(effect, ast.PureEffect):
            pass  # OK
        elif isinstance(effect, ast.EffectSet):
            for eff in effect.effects:
                if isinstance(eff, ast.EffectRef):
                    if eff.name == "IO":
                        self._needs_io_print = True
                        self._needs_memory = True
                    elif eff.name == "State":
                        # State<T> — T must be a compilable primitive
                        if not self._check_state_type(decl, eff):
                            return False
                    else:
                        self._warning(
                            decl,
                            f"Function '{decl.name}' uses unsupported "
                            f"effect '{eff.name}' — skipped.",
                            rationale="Only pure, IO, and State<T> effects "
                            "are compilable.",
                        )
                        return False
                else:
                    return False
        else:
            return False

        # Check parameter types
        for p in decl.params:
            wt = self._type_expr_to_wasm_type(p)
            if wt == "unsupported":
                self._warning(
                    decl,
                    f"Function '{decl.name}' has unsupported parameter type "
                    f"— skipped.",
                )
                return False

        # Check return type
        ret_wt = self._type_expr_to_wasm_type(decl.return_type)
        if ret_wt == "unsupported":
            self._warning(
                decl,
                f"Function '{decl.name}' has unsupported return type "
                f"— skipped.",
            )
            return False

        return True

    def _check_state_type(
        self, decl: ast.FnDecl, eff: ast.EffectRef
    ) -> bool:
        """Validate a State<T> effect and register its type.

        Returns True if compilable, False otherwise.
        """
        if not eff.type_args or len(eff.type_args) != 1:
            self._warning(
                decl,
                f"Function '{decl.name}' uses State without "
                f"a type argument — skipped.",
                rationale="State<T> requires exactly one type argument.",
            )
            return False
        type_arg = eff.type_args[0]
        wt = self._type_expr_to_wasm_type(type_arg)
        if wt is None or wt == "unsupported":
            self._warning(
                decl,
                f"Function '{decl.name}' uses State with "
                f"unsupported type — skipped.",
                rationale="State<T> requires a compilable primitive type "
                "(Int, Nat, Bool, Float64).",
            )
            return False
        type_name = self._type_expr_to_slot_name(type_arg)
        if type_name and (type_name, wt) not in self._state_types:
            self._state_types.append((type_name, wt))
        return True

    # -----------------------------------------------------------------
    # Type helpers
    # -----------------------------------------------------------------

    def _type_expr_to_wasm_type(self, te: ast.TypeExpr) -> str | None:
        """Map a Vera TypeExpr to a WAT type string.

        Returns None for Unit, "unsupported" for non-compilable types.
        """
        if isinstance(te, ast.NamedType):
            name = te.name
            if name in ("Int", "Nat"):
                return "i64"
            if name in ("Float64", "Float"):
                return "f64"
            if name == "Bool":
                return "i32"
            if name == "Unit":
                return None
            if name == "String":
                return "unsupported"
            # ADT types compile to i32 (heap pointer)
            if name in self._adt_layouts:
                return "i32"
            # Function type aliases compile to i32 (closure pointer)
            if name in self._type_aliases:
                alias_te = self._type_aliases[name]
                if isinstance(alias_te, ast.FnType):
                    return "i32"
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
