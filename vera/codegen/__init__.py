"""Vera code generator — AST to WebAssembly compilation."""

from vera.codegen.api import (
    CompileResult,
    ConstructorLayout,
    ExecuteResult,
    _align_up,
    _wasm_type_align,
    _wasm_type_size,
    compile,
    execute,
)
from vera.codegen.core import CodeGenerator

__all__ = [
    "CodeGenerator",
    "CompileResult",
    "ConstructorLayout",
    "ExecuteResult",
    "_align_up",
    "_wasm_type_align",
    "_wasm_type_size",
    "compile",
    "execute",
]
