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
        self._register_builtin_adts()
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                self._register_fn(decl)
            elif isinstance(decl, ast.DataDecl):
                self._register_data(decl)
            elif isinstance(decl, ast.TypeAliasDecl):
                self._type_aliases[decl.name] = decl.type_expr
                if decl.type_params:
                    self._type_alias_params[decl.name] = decl.type_params

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

    def _register_builtin_adts(self) -> None:
        """Register minimal ADT layouts for built-in types (Option, Result).

        Tags and generic i32 field offsets enable match dispatch and
        wildcard offset advancement.  Concrete sizes are recomputed at
        construction / extraction time from actual types.  If the user
        writes an explicit ``data Result`` or ``data Option`` declaration,
        ``_register_data`` will overwrite these entries.
        """
        self._adt_layouts["Option"] = {
            "None": ConstructorLayout(tag=0, field_offsets=(), total_size=8),
            "Some": ConstructorLayout(
                tag=1, field_offsets=((4, "i32"),), total_size=8,
            ),
        }
        self._adt_layouts["Result"] = {
            "Ok": ConstructorLayout(
                tag=0, field_offsets=((4, "i32"),), total_size=8,
            ),
            "Err": ConstructorLayout(
                tag=1, field_offsets=((4, "i32"),), total_size=8,
            ),
        }
        # Ordering — result type for Ord's compare operation (§9.8)
        self._adt_layouts["Ordering"] = {
            "Less": ConstructorLayout(
                tag=0, field_offsets=(), total_size=8,
            ),
            "Equal": ConstructorLayout(
                tag=1, field_offsets=(), total_size=8,
            ),
            "Greater": ConstructorLayout(
                tag=2, field_offsets=(), total_size=8,
            ),
        }
        # UrlParts — URL components (§9.6.5)
        # 5 String fields (i32_pair: 8 bytes each, 4-byte align)
        self._adt_layouts["UrlParts"] = {
            "UrlParts": ConstructorLayout(
                tag=0,
                field_offsets=(
                    (4, "i32_pair"), (12, "i32_pair"),
                    (20, "i32_pair"), (28, "i32_pair"),
                    (36, "i32_pair"),
                ),
                total_size=48,
            ),
        }
        # Tuple — variadic product type (tag=0, layout recomputed per-call)
        self._adt_layouts["Tuple"] = {
            "Tuple": ConstructorLayout(
                tag=0, field_offsets=(), total_size=8,
            ),
        }
        # MdInline — inline Markdown elements (6 constructors)
        # String/Array fields are i32_pair (8 bytes, 4-byte align)
        self._adt_layouts["MdInline"] = {
            "MdText": ConstructorLayout(
                tag=0, field_offsets=((4, "i32_pair"),), total_size=16,
            ),
            "MdCode": ConstructorLayout(
                tag=1, field_offsets=((4, "i32_pair"),), total_size=16,
            ),
            "MdEmph": ConstructorLayout(
                tag=2, field_offsets=((4, "i32_pair"),), total_size=16,
            ),
            "MdStrong": ConstructorLayout(
                tag=3, field_offsets=((4, "i32_pair"),), total_size=16,
            ),
            "MdLink": ConstructorLayout(
                tag=4,
                field_offsets=((4, "i32_pair"), (12, "i32_pair")),
                total_size=24,
            ),
            "MdImage": ConstructorLayout(
                tag=5,
                field_offsets=((4, "i32_pair"), (12, "i32_pair")),
                total_size=24,
            ),
        }
        # MdBlock — block-level Markdown elements (8 constructors)
        # MdHeading: Nat (i64, 8-byte align) at offset 8, Array at 16
        # MdList: Bool (i32) at offset 4, Array at offset 8
        # MdThematicBreak: no fields (tag only)
        self._adt_layouts["MdBlock"] = {
            "MdParagraph": ConstructorLayout(
                tag=0, field_offsets=((4, "i32_pair"),), total_size=16,
            ),
            "MdHeading": ConstructorLayout(
                tag=1,
                field_offsets=((8, "i64"), (16, "i32_pair")),
                total_size=24,
            ),
            "MdCodeBlock": ConstructorLayout(
                tag=2,
                field_offsets=((4, "i32_pair"), (12, "i32_pair")),
                total_size=24,
            ),
            "MdBlockQuote": ConstructorLayout(
                tag=3, field_offsets=((4, "i32_pair"),), total_size=16,
            ),
            "MdList": ConstructorLayout(
                tag=4,
                field_offsets=((4, "i32"), (8, "i32_pair")),
                total_size=16,
            ),
            "MdThematicBreak": ConstructorLayout(
                tag=5, field_offsets=(), total_size=8,
            ),
            "MdTable": ConstructorLayout(
                tag=6, field_offsets=((4, "i32_pair"),), total_size=16,
            ),
            "MdDocument": ConstructorLayout(
                tag=7, field_offsets=((4, "i32_pair"),), total_size=16,
            ),
        }

        # Constructor → per-field ADT type-param index mapping for built-in ADTs.
        # Each tuple position corresponds to a constructor field; the value is the
        # index of that field's type in the parent ADT's type-param list, or None
        # for concrete (non-type-variable) fields.  This lets the monomorphizer
        # and WASM type inference correctly bind Err(e) to E (index 1 in
        # Result<T, E>), not to T (index 0) as naïve positional zipping would do.
        self._ctor_adt_tp_indices["None"] = ()         # Option<T>: no fields
        self._ctor_adt_tp_indices["Some"] = (0,)       # field 0 → T (index 0)
        self._ctor_adt_tp_indices["Ok"] = (0,)         # field 0 → T (index 0)
        self._ctor_adt_tp_indices["Err"] = (1,)        # field 0 → E (index 1)
        self._adt_tp_counts["Option"] = 1
        self._adt_tp_counts["Result"] = 2
        self._adt_tp_counts["Ordering"] = 0
        self._adt_tp_counts["UrlParts"] = 0
        self._adt_tp_counts["Tuple"] = 0

    def _register_data(self, decl: ast.DataDecl) -> None:
        """Register an ADT and precompute constructor layouts."""
        layouts: dict[str, ConstructorLayout] = {}
        for tag, ctor in enumerate(decl.constructors):
            layout = self._compute_constructor_layout(tag, ctor, decl)
            layouts[ctor.name] = layout
        self._adt_layouts[decl.name] = layouts
        self._needs_alloc = True
        self._needs_memory = True

        # Build per-constructor type-param index mapping so the monomorphizer and
        # WASM type inference can correctly bind forall vars from sparse constructors
        # (e.g. a constructor that only carries the *second* type param of the ADT).
        type_params = decl.type_params or ()
        tp_index: dict[str, int] = {tp: i for i, tp in enumerate(type_params)}
        self._adt_tp_counts[decl.name] = len(type_params)
        for ctor in decl.constructors:
            if ctor.fields is not None:
                indices: list[int | None] = []
                for field_te in ctor.fields:
                    if (isinstance(field_te, ast.NamedType)
                            and field_te.name in tp_index):
                        indices.append(tp_index[field_te.name])
                    else:
                        indices.append(None)
                self._ctor_adt_tp_indices[ctor.name] = tuple(indices)
            else:
                self._ctor_adt_tp_indices[ctor.name] = ()

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
