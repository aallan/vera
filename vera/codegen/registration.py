"""Mixin for function/ADT registration and layout computation (Pass 1).

Registers all function signatures, ADT constructor layouts, and type
aliases so forward references resolve during compilation.
"""

from __future__ import annotations

from vera import ast
from vera.codegen.memory import ConstructorLayout, _align_up, _wasm_type_align, _wasm_type_size
from vera.wasm.inference import substitute_type_vars


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
        # #747: per-parameter concrete-@Nat flags for the runtime
        # narrowing guard at call sites.  `decl.params` holds the
        # parameter TypeExprs; resolve through aliases / refinements so a
        # `type Count = Nat` or `{ @Nat | p }` formal is guarded too.
        self._fn_nat_params[decl.name] = tuple(
            self._type_resolves_to_nat(p) for p in decl.params
        )
        # #813: dual bitmap of concrete-@Int formals, for the runtime
        # @Nat -> @Int *widening* guard at call sites (a @Nat value above
        # i64.MAX reinterprets to a negative @Int).  Disjoint from the @Nat
        # bitmap above: a formal resolves to one primitive base or neither.
        self._fn_int_params[decl.name] = tuple(
            self._type_resolves_to_int(p) for p in decl.params
        )
        # #614: also register the full Vera return type expression so
        # `_infer_index_element_type_expr` can extract the element type
        # of an `Array<T>`-returning call inside `f()[i]`.  Without
        # this, the inference walker falls through to `return None`
        # for FnCall collections.
        self._fn_ret_type_exprs[decl.name] = decl.return_type

        # #516 Stage 2 — record source location so wasmtime trap frames
        # naming this function can be resolved to (file, line) at runtime.
        # Functions injected by `inject_prelude()` also have spans (their
        # bodies come from parse_to_ast of synthetic Vera source), but
        # those spans point at the synthetic source's line numbers — not
        # the user's file.  So registering them here would surface
        # misleading coordinates.  The post-prelude registration loop in
        # `compile_program` (core.py) calls `_register_fn` for prelude
        # decls and then immediately moves the entry from
        # `_fn_source_map` to `_prelude_fn_names`; the resolver tags
        # those as `<builtin>`.  Built-in WASM helpers (`$alloc`,
        # `$gc_collect`, `$contract_fail`, `$exn_*`, `$vera.*`) never go
        # through this method at all — they're emitted directly into WAT
        # by the assembly module.
        if decl.span is not None:
            self._fn_source_map[decl.name] = (
                self.file or "<unknown>",
                decl.span.line,
                decl.span.end_line,
            )

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
        # #773: ``field_types`` on the generic built-ins records the bare type
        # parameter ("T" / "E"); structural Eq substitutes the concrete type
        # argument (from the parameterized comparison-site name) before
        # dispatching.  Non-generic built-ins record their concrete field types.
        self._adt_layouts["Option"] = {
            "None": ConstructorLayout(tag=0, field_offsets=(), total_size=8),
            "Some": ConstructorLayout(
                tag=1, field_offsets=((4, "i32"),), total_size=8,
                field_types=("T",),
            ),
        }
        self._adt_layouts["Result"] = {
            "Ok": ConstructorLayout(
                tag=0, field_offsets=((4, "i32"),), total_size=8,
                field_types=("T",),
            ),
            "Err": ConstructorLayout(
                tag=1, field_offsets=((4, "i32"),), total_size=8,
                field_types=("E",),
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
                field_types=("String", "String", "String", "String", "String"),
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
                # #747 (CR #756): the level field is a concrete @Nat — flag it
                # so `MdHeading(@Int.0, ...)` runtime-guards the narrowing.
                # Manual built-in layouts bypass `_compute_constructor_layout`,
                # which is the only other `nat_fields` populator; MdHeading is
                # the sole built-in constructor with a @Nat field.
                nat_fields=(True, False),
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
        # #773: parameter names for the generic built-ins (structural-Eq
        # substitution); the rest have no type parameters.
        self._adt_tp_param_names["Option"] = ("T",)
        self._adt_tp_param_names["Result"] = ("T", "E")

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
        # #773: ordered type-parameter NAMES, so structural Eq can substitute
        # params nested inside a parameterized field type (`List<T>` under a
        # `List<Int>` comparison) — the positional `_ctor_adt_tp_indices`
        # table only covers fields that ARE a bare parameter.
        self._adt_tp_param_names[decl.name] = tuple(type_params)
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
        nat_fields: list[bool] = []
        int_fields: list[bool] = []
        field_types: list[str] = []

        if ctor.fields is not None:
            for field_te in ctor.fields:
                wt = self._resolve_field_wasm_type(field_te, decl)
                align = _wasm_type_align(wt)
                offset = _align_up(offset, align)
                field_offsets.append((offset, wt))
                offset += _wasm_type_size(wt)
                # #747: a concrete @Nat field receives the runtime
                # narrowing guard at construction.  A generic field
                # (type param) instantiated to @Nat is erased to i64
                # here, so it stays statically-only (verifier-obligated).
                nat_fields.append(self._type_resolves_to_nat(field_te))
                # #813: a concrete @Int field receives the runtime @Nat -> @Int
                # widening guard when constructed with a @Nat argument.
                int_fields.append(self._type_resolves_to_int(field_te))
                # #773: the RESOLVED Vera type name of the field, for
                # structural Eq derivation (type params stay bare, e.g. "T";
                # aliases and refinements resolve to their ground type).
                field_types.append(self._field_vera_type_name(field_te, decl))

        total_size = _align_up(offset, 8) if offset > 0 else 8
        return ConstructorLayout(
            tag=tag,
            field_offsets=tuple(field_offsets),
            total_size=total_size,
            nat_fields=tuple(nat_fields),
            int_fields=tuple(int_fields),
            field_types=tuple(field_types),
        )

    def _field_vera_type_name(
        self,
        te: ast.TypeExpr,
        decl: ast.DataDecl,
        _seen: frozenset[str] = frozenset(),
    ) -> str:
        """Canonical RESOLVED Vera type name of a constructor field (#773).

        Used to populate ``ConstructorLayout.field_types`` for structural
        ``Eq`` derivation.  Resolution mirrors the sibling field resolvers
        (``_resolve_field_wasm_type`` / ``_type_resolves_to_nat``): a type
        ALIAS resolves through ``self._type_aliases`` — including chains
        (``A2 = A1 = Int``, guarded by ``_seen``) and generic aliases
        (``Id<Nat>`` via ``substitute_type_vars``) — so an alias-typed field
        dispatches on its ground type, not the alias name; a
        ``RefinementType`` (``{ @Int | p }``, or an alias to one) unwraps to
        its base — a refinement of an Eq type is Eq and compared identically
        at the machine level.  Aliases populate in declaration order, so an
        alias declared *after* the ``data`` stays unresolved (same caveat as
        the siblings).  The parent ADT's type PARAMETERS render as their bare
        name (``"T"``, never alias-resolved — params shadow) and are
        substituted with the concrete type argument at the comparison site.
        A ``NamedType`` with type args renders parameterized
        (``"Map<String, Int>"``), matching ``Monomorphizer._format_type_name``
        so the comparison site can re-parse it, with each argument resolved
        recursively.
        """
        if isinstance(te, ast.RefinementType):
            return self._field_vera_type_name(te.base_type, decl, _seen)
        if isinstance(te, ast.NamedType):
            # Parent ADT's type parameter — stays bare; substituted with the
            # concrete type argument at the comparison site.
            if decl.type_params and te.name in decl.type_params:
                return te.name
            alias = self._type_aliases.get(te.name)
            if alias is not None and te.name not in _seen:
                params = self._type_alias_params.get(te.name)
                if (params and te.type_args
                        and len(params) == len(te.type_args)):
                    alias = substitute_type_vars(
                        alias, dict(zip(params, te.type_args)),
                    )
                return self._field_vera_type_name(
                    alias, decl, _seen | {te.name},
                )
            if not te.type_args:
                return te.name
            arg_names = [
                self._field_vera_type_name(ta, decl, _seen)
                for ta in te.type_args
            ]
            return f"{te.name}<{', '.join(arg_names)}>"
        # FnType or anything else has no Eq semantics; a placeholder the
        # derivability check treats as non-Eq (rejected loudly at the gate).
        return "<fn>"

    def _type_resolves_to_nat(self, te: ast.TypeExpr) -> bool:
        """True if *te* is ``@Nat`` directly, through a ``type X = Nat``
        alias, the base of a refinement (``{ @Nat | p }``), or a *generic*
        alias instantiated to @Nat (``type Id<T> = T`` used as ``Id<Nat>``)
        — used for the #747 runtime-guard metadata so an alias/refinement-
        typed @Nat formal or field is still guarded (CR #756), mirroring the
        verifier's alias-aware ``_is_nat_type``.

        Alias resolution uses ``self._type_aliases``, populated in
        declaration order during ``_register_all``; a `@Nat` alias declared
        *after* the function/data that uses it is not yet visible here and
        falls back to the verifier's static obligation.  Generic alias
        arguments are bound into the body via ``substitute_type_vars`` so
        ``Id<Nat>`` resolves to ``Nat`` rather than the bare type-param ``T``.
        """
        return self._type_resolves_to_base(te, "Nat")

    def _type_resolves_to_int(self, te: ast.TypeExpr) -> bool:
        """True if *te* resolves to a concrete ``@Int`` — directly, through a
        ``type X = Int`` alias, the base of a refinement (``{ @Int | p }``),
        or a generic alias instantiated to @Int.  The #813 dual of
        ``_type_resolves_to_nat``: a @Int formal receiving a @Nat-typed
        argument widens it, and a @Nat value above i64.MAX reinterprets to a
        negative @Int, so the call site needs the runtime widening guard."""
        return self._type_resolves_to_base(te, "Int")

    def _type_resolves_to_base(
        self, te: ast.TypeExpr, base_name: str,
    ) -> bool:
        """Shared alias/refinement-resolving check behind
        ``_type_resolves_to_nat`` / ``_type_resolves_to_int``: True if *te*
        resolves to the primitive named *base_name*."""
        seen: set[str] = set()
        while True:
            if isinstance(te, ast.RefinementType):
                te = te.base_type
                continue
            if isinstance(te, ast.NamedType):
                if te.name == base_name:
                    return True
                alias = self._type_aliases.get(te.name)
                if alias is not None and te.name not in seen:
                    seen.add(te.name)
                    params = self._type_alias_params.get(te.name)
                    if (params and te.type_args
                            and len(params) == len(te.type_args)):
                        alias = substitute_type_vars(
                            alias, dict(zip(params, te.type_args)),
                        )
                    te = alias
                    continue
            return False

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
