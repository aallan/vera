"""Vera code generator — AST to WebAssembly compilation.

Compiles a type-checked and verified Vera Program AST to WebAssembly.
Generates WAT (WebAssembly Text Format) as the intermediate representation,
then converts to WASM binary via wasmtime.  Provides execution support
with host function bindings for IO effects.

See spec/11-compilation.md for the compilation specification.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from io import StringIO

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
# Public API
# =====================================================================

@dataclass
class CompileResult:
    """Result of compiling a Vera program to WebAssembly."""

    wat: str
    wasm_bytes: bytes
    exports: list[str]
    diagnostics: list[Diagnostic] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        """True if compilation succeeded with no errors."""
        return not any(d.severity == "error" for d in self.diagnostics)


@dataclass
class ExecuteResult:
    """Result of executing a WASM function."""

    value: int | None  # Return value (None for void/Unit functions)
    stdout: str  # Captured IO.print output


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
    args: list[int] | None = None,
) -> ExecuteResult:
    """Execute a function from a compiled WASM module.

    Uses wasmtime to instantiate the module with host bindings
    for IO effects.  Returns the function's return value and
    any captured stdout output.
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
    call_args: list[int] = args or []
    raw_result = func(store, *call_args)

    # Extract return value
    if raw_result is None:
        value = None
    elif isinstance(raw_result, int):
        value = raw_result
    else:
        value = int(raw_result)

    return ExecuteResult(
        value=value,
        stdout=output_buf.getvalue(),
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
            )

        return CompileResult(
            wat=wat,
            wasm_bytes=bytes(wasm_bytes),
            exports=exports,
            diagnostics=self.diagnostics,
        )

    # -----------------------------------------------------------------
    # Registration pass
    # -----------------------------------------------------------------

    def _register_all(self, program: ast.Program) -> None:
        """Register all function signatures for forward references."""
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                self._register_fn(decl)

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

        ctx = WasmContext(self.string_pool)
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
                    rationale="Only Int, Nat, Bool, and Unit types are "
                    "compilable in the current WASM backend.",
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

        # Memory (for string data)
        if self._needs_memory or self.string_pool.has_strings():
            parts.append('  (memory (export "memory") 1)')

        # Data section (string constants)
        for value, offset, _length in self.string_pool.entries():
            # Escape special characters for WAT string literals
            escaped = self._escape_wat_string(value)
            parts.append(f'  (data (i32.const {offset}) "{escaped}")')

        # Functions
        for fn_wat in functions:
            parts.append(fn_wat)

        parts.append(")")
        return "\n".join(parts)

    # -----------------------------------------------------------------
    # Compilability check
    # -----------------------------------------------------------------

    def _is_compilable(self, decl: ast.FnDecl) -> bool:
        """Check if a function can be compiled to WASM."""
        # Check effect: must be pure or <IO>
        effect = decl.effect
        if isinstance(effect, ast.PureEffect):
            pass  # OK
        elif isinstance(effect, ast.EffectSet):
            # Check if all effects are IO
            for eff in effect.effects:
                if isinstance(eff, ast.EffectRef):
                    if eff.name == "IO":
                        self._needs_io_print = True
                        self._needs_memory = True
                    else:
                        self._warning(
                            decl,
                            f"Function '{decl.name}' uses unsupported "
                            f"effect '{eff.name}' — skipped.",
                            rationale="Only pure functions and functions "
                            "with IO effects are compilable.",
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
            if name == "Bool":
                return "i32"
            if name == "Unit":
                return None
            if name == "String":
                return "unsupported"
            return "unsupported"
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_wasm_type(te.base_type)
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
