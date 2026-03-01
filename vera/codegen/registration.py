"""Mixin for function/ADT registration and layout computation (Pass 1).

Registers all function signatures, ADT constructor layouts, and type
aliases so forward references resolve during compilation.
"""

from __future__ import annotations

from vera import ast
from vera.codegen.api import ConstructorLayout, _align_up, _wasm_type_align, _wasm_type_size


class RegistrationMixin:
    """Methods for Pass 1 registration and ADT layout computation."""

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
