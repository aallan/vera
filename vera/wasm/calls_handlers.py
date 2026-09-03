"""Ability and effect handler translation mixin for WasmContext.

Handles: Show ability (_translate_show), Hash ability (_translate_hash,
_translate_hash_string), structural show/hash for composite types (#911),
and effect handlers (State<T>, Exn<E>).
"""

from __future__ import annotations

from typing import Callable, ClassVar

from dataclasses import fields, is_dataclass

from vera import ast, naming
from vera.monomorphize import mangle_type_name
from vera.slots import effect_op_result_names, type_expr_slot_name
from vera.skip import STATE_CLAUSE_INLINE_DEPTH_CAP, CodegenSkip
from vera.wasm.helpers import (
    CellNames,
    StateClauseEntry,
    WasmSlotEnv,
    _is_host_handle_type,
    gc_shadow_push,
)


# The built-in ``State<T>`` operations, by the bare names §7.4 gives them.
# The ONE place they are enumerated for codegen's "is this a State op?"
# questions — the addressability gate below asks it, and asking instead
# whether the op has a recorded cell was correct only while `State` was the
# sole cell-carrying effect (#1269).
_STATE_OP_NAMES = frozenset({"get", "put"})


class _ShowHashUnsupported(Exception):
    """Internal signal: a field is not showable/hashable here (#911).

    Raised mid-traversal from a nested field render/fold and caught by the
    top-level `_show_adt` / `_hash_adt` so the whole composite falls back to
    `CodegenSkip` (unchanged behaviour) rather than emitting partial code.
    Not a diagnostic — a control-flow unwind, hence the plain `Exception`.
    """


class CallsHandlersMixin:
    """Methods for translating Show/Hash dispatch and effect handlers."""

    # Declared for the type checker, not initialised here: ``WasmContext``
    # owns these registries (see its ``__init__``), and this mixin only
    # saves, swaps, and restores them around handler bodies and inlined
    # clause bodies.  Spelling them out keeps the mixin's view of each type
    # equal to the context's rather than inferred from whichever assignment
    # mypy reaches first — `_state_clause_family_base` is optional (None
    # outside a clause), and inferring it as `str` from an assignment here
    # contradicted the context's own declaration (#1211).
    _effect_ops: dict[str, tuple[str, bool]]
    _effect_op_result_wt: dict[str, str | None]
    _effect_op_result_vera: dict[str, str | None]
    _effect_op_cells: dict[str, CellNames]
    _state_getters: dict[str, str]
    _state_clause_ops: dict[str, StateClauseEntry]
    _state_clause_family_base: str | None
    _in_state_clause: bool
    _pushed_cell_families: list[str]
    _addressable_from: int
    _clause_inline_depth: int
    _refinement_guard_emitter: (
        Callable[[ast.TypeExpr, int, str, WasmSlotEnv], list[str] | None]
        | None
    )

    # -----------------------------------------------------------------
    # Ability operation dispatch: show and hash (§9.8)
    # -----------------------------------------------------------------

    # Dispatch map: Vera type → to_string builtin name
    _SHOW_DISPATCH: ClassVar[dict[str, str]] = {
        "Int": "to_string",
        "Nat": "nat_to_string",
        "Bool": "bool_to_string",
        "Byte": "byte_to_string",
        "Float64": "float_to_string",
    }

    def _translate_show(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate show(x) to the appropriate to_string builtin.

        Dispatches based on the inferred Vera type of the argument:
        - Int/Nat/Bool/Byte/Float64 → corresponding to_string call
        - String → identity (the string IS its own representation)
        - Unit → literal "unit"
        """
        vera_type = self._infer_vera_type(arg)
        if vera_type is None:
            raise CodegenSkip(
                arg, "could not infer show() argument type"
            )
        # #1087: ground an alias / transparent-`Future` spelling before dispatch.
        # A bare `Future<Int>` value or an alias of one (`type FI = Future<Int>;`,
        # `show(@FI.0)`) reached this dispatch as `Future<Int>` / `FI`, matched
        # no primitive / Unit / composite arm below, and loud-skipped the whole
        # function (E602) on a check-green program — while `show` of the literal
        # payload rendered fine.  `_canonical_field_type` resolves alias chains
        # and peels the transparent wrapper to its payload (`FI` → `Int`),
        # mirroring the #1076/#1077 grounding on the eq/field-resolution side;
        # #1077 keyed the Unit arm on erasure, this is the non-Unit sibling.  A
        # non-alias, non-Future name (a primitive, an ADT, a container) is
        # returned unchanged, so every other arm is unaffected.
        vera_type = self._canonical_field_type(vera_type)

        # String → identity: show("hello") == "hello"
        if vera_type == "String":
            return self.translate_expr(arg, env)

        # Unit → literal "unit" string.  #1077: keyed on ERASURE, not the
        # literal name — a bare value of an erases-to-Unit alias type
        # (`type U = Unit;` fn returning `@U`) otherwise missed this arm and
        # loud-skipped the function, while literal `Unit` rendered fine.
        if self._slot_name_erases_to_unit(vera_type):
            offset, length = self.string_pool.intern("unit")
            return [f"i32.const {offset}", f"i32.const {length}"]

        # Decimal → decimal_to_string host import.  #1321/#1331: unless this
        # namespace declares its own `Decimal`, which is an ADT with a tag
        # and fields, not an opaque host handle the host can stringify.
        if vera_type == "Decimal" and not self._declares_adt(vera_type):
            desugared = ast.FnCall(
                name="decimal_to_string", args=(arg,), span=arg.span,
            )
            return self._translate_call(desugared, env)

        # Dispatch to existing to_string builtins
        builtin = self._SHOW_DISPATCH.get(vera_type)
        if builtin is not None:
            # Reuse existing translate methods by constructing a FnCall
            desugared = ast.FnCall(
                name=builtin, args=(arg,), span=arg.span,
            )
            return self._translate_call(desugared, env)

        # Composite (#911): ADT / Tuple / Option / Result / Array.  Render
        # structurally, recursing into each field's own `show`.  Recover the
        # PARAMETERIZED type (`Option<Int>`, `Array<String>`) so inner field
        # types resolve — `_infer_vera_type` only reports the bare head.
        # #1091 / PR #1090 review: the recovery prefers the DECLARED spelling,
        # UNDOING the grounding above — `show(@FOI.0)` (`type FOI =
        # Future<Option<Int>>;`) grounded to `Option<Int>` at the top only for
        # the recovery to hand `_show_value` the raw `FOI` (no constructor
        # plans; E602 function drop), and an alias of a WHOLE ADT (`type MyBox
        # = Box;`) recovered as `MyBox` the same way.  Ground the recovered
        # spelling too: a grounded compound (`Option<Int>`, `Box<Int>`,
        # `Array<FI>`) passes through unchanged.
        param_type = self._canonical_field_type(
            self._parameterized_arg_type(arg, vera_type)
        )
        value_instrs = self.translate_expr(arg, env)
        if value_instrs is None:
            return None
        composite = self._show_value(param_type, value_instrs, arg)
        if composite is not None:
            return composite

        raise CodegenSkip(
            arg, f"show() not supported for type {vera_type!r}"
        )

    def _translate_hash(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate hash(x) to a type-specific hash implementation.

        Returns an i64 hash value:
        - Int/Nat → identity (the value IS the hash)
        - Bool/Byte → i64.extend_i32_u (widen to i64)
        - Float64 → i64.reinterpret_f64 (bit pattern)
        - Unit → i64.const 0
        - String → FNV-1a hash
        """
        vera_type = self._infer_vera_type(arg)
        if vera_type is None:
            raise CodegenSkip(
                arg, "could not infer hash() argument type"
            )
        # #1087: ground an alias / transparent-`Future` spelling — mirrors the
        # show dispatch above.  A bare or aliased `Future<Int>` (`hash(@FI.0)`)
        # otherwise matched no arm and loud-skipped the function (E602).
        vera_type = self._canonical_field_type(vera_type)

        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        # Int/Nat → identity: hash(42) == 42
        if vera_type in ("Int", "Nat"):
            return arg_instrs

        # Bool/Byte → extend to i64
        if vera_type in ("Bool", "Byte"):
            return arg_instrs + ["i64.extend_i32_u"]

        # Float64 → bit-level reinterpretation
        if vera_type == "Float64":
            return arg_instrs + ["i64.reinterpret_f64"]

        # Unit → constant 0.  #1077: keyed on erasure, mirroring show above.
        if self._slot_name_erases_to_unit(vera_type):
            return ["i64.const 0"]

        # String → FNV-1a hash
        if vera_type == "String":
            return self._translate_hash_string(arg_instrs)

        # Composite (#911): fold the constructor tag with each field's own
        # hash.  Parameterized type recovers inner field types (see show).
        # #1091 / PR #1090 review: ground the recovered spelling — the
        # recovery prefers the DECLARED form, undoing the grounding above
        # (mirrors the show dispatch).
        param_type = self._canonical_field_type(
            self._parameterized_arg_type(arg, vera_type)
        )
        composite = self._hash_value(param_type, arg_instrs, arg)
        if composite is not None:
            return composite

        raise CodegenSkip(
            arg, f"hash() not supported for type {vera_type!r}"
        )

    def _translate_hash_string(
        self, arg_instrs: list[str],
    ) -> list[str]:
        """Generate FNV-1a hash for a string (ptr, len) pair.

        FNV-1a: for each byte, hash = (hash XOR byte) * FNV_prime.
        Uses the 64-bit FNV-1a variant:
        - offset basis: 14695981039346656037
        - prime: 1099511628211
        """
        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        hash_val = self.alloc_local("i64")

        # FNV-1a offset basis (as signed i64)
        fnv_basis = -3750763034362895579  # 14695981039346656037 as signed
        fnv_prime = 1099511628211

        instructions: list[str] = []
        # Evaluate arg → (ptr, len) on stack
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {slen}")
        instructions.append(f"local.set {ptr}")

        # Initialize hash to FNV offset basis
        instructions.append(f"i64.const {fnv_basis}")
        instructions.append(f"local.set {hash_val}")

        # idx = 0
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")

        # Loop over each byte
        instructions.append("block $hbreak")
        instructions.append("  loop $hloop")
        # if idx >= len → break
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {slen}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $hbreak")
        # byte = mem[ptr + idx]
        instructions.append(f"    local.get {ptr}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u")
        instructions.append("    i64.extend_i32_u")
        # hash = hash XOR byte
        instructions.append(f"    local.get {hash_val}")
        instructions.append("    i64.xor")
        # hash = hash * FNV_prime
        instructions.append(f"    i64.const {fnv_prime}")
        instructions.append("    i64.mul")
        instructions.append(f"    local.set {hash_val}")
        # idx++
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $hloop")
        instructions.append("  end")
        instructions.append("end")

        # Push result
        instructions.append(f"local.get {hash_val}")
        return instructions

    # -----------------------------------------------------------------
    # Structural show / hash for composite types (#911)
    # -----------------------------------------------------------------
    #
    # `show`/`hash` are registered as universal builtins (§9.8), but codegen
    # historically only handled primitives — every composite `show`/`hash`
    # site tripped `CodegenSkip` and the enclosing function was dropped.
    #
    # These helpers render / fold a composite value INLINE, recursing into
    # each field by its own `show`/`hash`.  Recursion terminates on the
    # value's static type structure; a type that (transitively) contains
    # itself (a recursive ADT like `List<T>`) is detected via `_seen` and
    # cleanly skipped — those need generated helper functions, out of scope
    # for #911 (whose repros are all finite-depth composites).
    #
    # This mirrors the structural-`Eq` traversal in `operators.py`
    # (`_generate_adt_eq_fn` / `_emit_field_eq`): tag at offset 0, fields at
    # concrete offsets recomputed from their concrete WASM types via the same
    # `_concrete_field_layout`, and per-field dispatch by resolved Vera type.

    def _parameterized_arg_type(
        self, arg: ast.Expr, bare: str,
    ) -> str:
        """Recover a show/hash argument's PARAMETERIZED type name.

        `_infer_vera_type` reports the bare head (`"Option"`, `"Array"`);
        the structural traversal needs the type arguments to resolve inner
        field types.  Reuses `_get_arg_type_info_wasm` (the same routine the
        generic-call rewriter and structural-`==` use).  Falls back to the
        bare name when the type arguments cannot be inferred.
        """
        # Array literal: recover the element type directly from its elements
        # (`_get_arg_type_info_wasm` does not special-case a bare `ArrayLit`).
        # Resolve the first element's FULL parameterized type recursively so an
        # array of composites (`[Tuple(1, 2), …]`, `[Some(1), …]`) carries the
        # nested type args rather than a bare `Array<Tuple>` head.
        if isinstance(arg, ast.ArrayLit):
            if arg.elements:
                first = arg.elements[0]
                elem_bare = self._infer_vera_type(first)
                if elem_bare is not None:
                    elem = self._parameterized_arg_type(first, elem_bare)
                    return f"Array<{elem}>"
            elem = self._infer_array_element_type(arg)
            if elem is not None:
                return f"Array<{elem}>"
            return bare

        # SlotRef and FnCall carry a DECLARED type expression that formats
        # nested generics in full (`Option<Tuple<Int, Int>>`), which the flat
        # `_get_arg_type_info_wasm` list cannot (it Nones-out any type arg that
        # is itself parameterized).  Prefer it when present.
        declared = self._declared_type_expr_for_show(arg)
        if declared is not None:
            formatted = self._format_named_type(declared)
            # Only trust it if it is fully ground (no bare type-parameter head).
            if "<" in formatted or formatted == bare:
                return formatted

        # A direct constructor literal's flat `_get_arg_type_info_wasm` result
        # Nones-out (or bare-heads) any type arg that is itself a composite —
        # so inline `Some(Tuple(1, 2))` / `Ok(Some(1))` lose the nested type
        # args.  Recover the FULL parameterized type by resolving each argument
        # recursively.  `Tuple` is variadic (its type args ARE its element
        # types, one per arg); every other constructor maps args to the ADT's
        # type-parameter slots via `_ctor_adt_tp_indices`.
        if isinstance(arg, ast.ConstructorCall):
            recovered = self._recover_ctor_ptype(arg, bare)
            if recovered is not None:
                return recovered

        info = self._get_arg_type_info_wasm(arg)
        if info is None:
            return bare
        base_name, arg_names = info
        if arg_names and all(a is not None for a in arg_names):
            resolved = [a for a in arg_names if a is not None]
            return f"{base_name}<{', '.join(resolved)}>"
        return base_name

    def _recover_ctor_ptype(
        self, arg: ast.ConstructorCall, bare: str,
        _seen: frozenset[str] = frozenset(),
    ) -> str | None:
        """Recover a constructor call's FULL parameterized type, recursively.

        `Tuple(a, b, …)` → ``Tuple<Ta, Tb, …>`` (element types are the args'
        own parameterized types).  Any other constructor maps each argument to
        its ADT type-parameter slot (via ``_ctor_adt_tp_indices``) and resolves
        that slot's argument recursively, so `Some(Tuple(1, 2))` yields
        ``Option<Tuple<Int, Int>>``.

        A slot that no argument pins DIRECTLY (its field is not a bare ``T``)
        is recovered by DESCENDING into a NESTED generic field whose declared
        type carries the parameter (#934): `Grove(Rose<T>, Forest<T>)` has no
        bare-``T`` field, but the field-0 argument `Bloom(1, …)` is a `Rose<T>`
        whose own `Bloom(T, …)` pins `T = Int` from the literal `1` — so
        `Grove(Bloom(1, Empty), Empty)` recovers `Forest<Int>`.  ``_seen``
        bounds the descent (the ADTs are mutually recursive).

        Returns None when the recovery is not fully ground (a slot arg whose
        type can't be inferred), leaving the caller on its existing fallbacks.
        """
        if arg.name == "Tuple":
            elem_types = [
                self._parameterized_arg_type(a, self._infer_vera_type(a) or "")
                for a in arg.args
            ]
            if all(elem_types):
                return f"Tuple<{', '.join(elem_types)}>"
            return None

        adt_name = self._ctor_to_adt_name(arg.name)
        if adt_name is None:
            return None
        tp_count = self._adt_tp_counts.get(adt_name, 0)
        if tp_count == 0:
            return None  # non-generic ADT — bare name already correct
        field_tp_idx = self._ctor_adt_tp_indices.get(arg.name)
        if field_tp_idx is None:
            return None
        slots: list[str | None] = [None] * tp_count
        # Direct pass: a field that IS a bare type parameter pins its slot.
        for field_i, tp_idx in enumerate(field_tp_idx):
            if tp_idx is not None and field_i < len(arg.args):
                a = arg.args[field_i]
                a_bare = self._infer_vera_type(a)
                if a_bare is not None:
                    slots[tp_idx] = self._parameterized_arg_type(a, a_bare)
        # Nested-descent pass (#934): fill any slot the direct pass left None
        # by digging the parameter out of a nested generic field's argument.
        if not all(s is not None for s in slots):
            self._recover_ptype_via_nested_fields(
                arg, adt_name, tp_count, slots, _seen,
            )
        if all(s is not None for s in slots):
            return f"{adt_name}<{', '.join(s for s in slots if s)}>"
        return None

    def _recover_ptype_via_nested_fields(
        self,
        arg: ast.ConstructorCall,
        adt_name: str,
        tp_count: int,
        slots: list[str | None],
        _seen: frozenset[str],
    ) -> None:
        """Fill still-``None`` type-param slots via nested generic fields (#934).

        For each field whose DECLARED type is a generic ADT that places a
        parent type PARAMETER at some position (e.g. `Rose<T>` under
        `Forest<T>`, or the recursive `Forest<T>` itself), recover that field
        ARGUMENT's own parameterized type (`Rose<Int>` / `Forest<Int>`) and
        read the concrete argument sitting where the parent parameter appears —
        pinning that parent slot.  Mutates ``slots`` in place.  Bounded by
        ``_seen`` (the mutually-recursive ADTs) to guarantee termination.
        """
        if adt_name in _seen:
            return
        seen = _seen | {adt_name}
        tp_names = self._adt_tp_param_names.get(adt_name, ())
        # Parent parameter NAME → its slot index (`T` → 0).
        name_to_slot = {name: i for i, name in enumerate(tp_names)}
        layout = self._ctor_layouts.get(arg.name)
        field_types = layout.field_types if layout else ()
        for field_i, decl in enumerate(field_types):
            if field_i >= len(arg.args):
                break
            fbase, fargs = self._split_param_type(decl)
            # Only nested GENERIC ADT fields carry a recoverable parameter.
            if not fargs or fbase not in self._adt_type_names:
                continue
            # Which nested type-arg positions ARE a parent parameter still
            # needing a value?  (`Rose<T>` → position 0 holds `T`.)
            wanted = {
                pos: name_to_slot[fa]
                for pos, fa in enumerate(fargs)
                if fa in name_to_slot and slots[name_to_slot[fa]] is None
            }
            if not wanted:
                continue
            field_arg = arg.args[field_i]
            if not isinstance(field_arg, ast.ConstructorCall):
                continue
            nested_bare = self._infer_vera_type(field_arg)
            recovered = self._recover_ctor_ptype(
                field_arg, nested_bare or fbase, seen,
            )
            if recovered is None:
                continue
            _, rargs = self._split_param_type(recovered)
            for pos, slot in wanted.items():
                if pos < len(rargs):
                    slots[slot] = rargs[pos]

    def _declared_type_expr_for_show(
        self, arg: ast.Expr,
    ) -> ast.NamedType | None:
        """The declared/annotated NamedType of a show/hash argument, if any.

        A ``SlotRef`` carries its bound type (with type args); a non-generic
        user ``FnCall`` carries its declared return TypeExpr (registered by
        ``_register_fn``).  Both format nested generics in full via
        ``_format_named_type``.  Generic calls are excluded — their return
        type is over the callee's own type vars, not concrete types.
        """
        if isinstance(arg, ast.SlotRef):
            return ast.NamedType(name=arg.type_name, type_args=arg.type_args)
        if isinstance(arg, ast.FnCall) and arg.name not in self._generic_fn_info:
            ret_te = self._fn_ret_type_exprs.get(arg.name)
            if isinstance(ret_te, ast.RefinementType):
                ret_te = ret_te.base_type
            if isinstance(ret_te, ast.NamedType):
                return ret_te
        return None

    @staticmethod
    def _ptype_nesting_depth(ptype: str) -> int:
        """Max angle-bracket nesting depth of a parameterized type name (#933).

        ``Int`` → 0, ``List<Int>`` → 1, ``List<List<Int>>`` → 2.  This is the
        structural measure the derived-helper generators bound on: a UNIFORMLY-
        recursive ADT recurs at CONSTANT nesting depth (the `List<T>` tail is
        again `List<T>`, depth 1), whereas a POLYMORPHICALLY-recursive one
        (`Box<T>` field `Box<Box<T>>`) climbs one level per descent without
        limit.  Capping this depth (``DERIVED_HELPER_DEPTH_CAP``) turns that
        runaway into a clean skip while leaving every hand-writable finite
        nesting far below the bound.
        """
        depth = 0
        max_depth = 0
        for c in ptype:
            if c == "<":
                depth += 1
                max_depth = max(max_depth, depth)
            elif c == ">":
                depth -= 1
        return max_depth

    @staticmethod
    def _split_param_type(ptype: str) -> tuple[str, list[str]]:
        """Split ``"Option<Int>"`` → ``("Option", ["Int"])`` (top level only).

        Nested generics in the last argument keep their closing ``>``:
        ``"Result<Int, Option<Int>>"`` → ``("Result", ["Int", "Option<Int>"])``.
        """
        if "<" not in ptype:
            return ptype, []
        base, rest = ptype.split("<", 1)
        # Drop exactly ONE trailing ``>`` (the one matching this ``<``).  A
        # bare `rstrip(">")` strips EVERY trailing ``>``, corrupting a nested
        # generic in the last arg (`Option<Int>>` → `Option<Int`).
        inner = rest[:-1] if rest.endswith(">") else rest
        # Split on top-level commas (nested generics keep their commas).
        args: list[str] = []
        depth = 0
        cur = ""
        for ch in inner:
            if ch == "<":
                depth += 1
                cur += ch
            elif ch == ">":
                depth -= 1
                cur += ch
            elif ch == "," and depth == 0:
                args.append(cur.strip())
                cur = ""
            else:
                cur += ch
        if cur.strip():
            args.append(cur.strip())
        return base.strip(), args

    def _composite_ctor_plans(
        self, ptype: str,
    ) -> list[tuple[str, int, list[tuple[int, str, str]]]] | None:
        """Per-constructor field plan for a composite type.

        Returns ``[(ctor_name, tag, [(offset, wasm_type, field_vera_type)])]``
        sorted by tag, or None when ``ptype`` is not a known composite (its
        head is not in `_adt_type_names`, or it has no registered
        constructors).  Field offsets / WASM types are recomputed from the
        CONCRETE field types (type parameters substituted) exactly as the
        construction site and `$eq_<type>` helper do, so a `String`
        instantiation lays out an i32_pair, not a bare pointer.
        """
        base, type_args = self._split_param_type(ptype)
        if base not in self._adt_type_names:
            return None

        # Tuple is a VARIADIC product with an empty registered layout — its
        # fields come from the instantiation's type args, laid out exactly as
        # the construction site does (`_concrete_field_layout`).  A missing /
        # unparameterized Tuple type (no args recovered) is not showable here.
        # #1077: the args are GROUNDED first (`_canonical_field_type`, exactly
        # as the registered-ADT branch below grounds its resolutions via
        # `_resolve_field_type_for_eq`) — a `Tuple<U, Int>` component spelled
        # through an alias otherwise reached the per-field dispatch as the
        # unknown name "U" and loud-skipped the whole function, while the
        # literal `Tuple<Unit, Int>` rendered fine.
        if base == "Tuple":
            if not type_args:
                return None
            field_type_names = [
                self._canonical_field_type(a) for a in type_args
            ]
            concrete = self._concrete_field_layout(field_type_names)
            fields = [
                (offset, wt, ftype)
                for (offset, wt), ftype in zip(concrete, field_type_names)
            ]
            return [("Tuple", 0, fields)]

        tp_names = self._adt_tp_param_names.get(base, ())
        tp_mapping = dict(zip(tp_names, type_args))

        ctors = sorted(
            (
                (cname, self._ctor_layouts[cname])
                for cname, parent in self._ctor_to_adt.items()
                if parent == base and cname in self._ctor_layouts
            ),
            key=lambda x: x[1].tag,
        )
        if not ctors:
            return None

        plans: list[tuple[str, int, list[tuple[int, str, str]]]] = []
        for cname, layout in ctors:
            n_fields = len(layout.field_offsets)
            tp_idx = self._ctor_adt_tp_indices.get(cname)
            raw_types = (
                layout.field_types
                if layout.field_types
                else ("<opaque>",) * n_fields
            )
            field_type_names = [
                self._resolve_field_type_for_eq(
                    raw, i, tp_idx, type_args, tp_mapping,
                )
                for i, raw in enumerate(raw_types)
            ]
            concrete = self._concrete_field_layout(field_type_names)
            fields = [
                (offset, wt, ftype)
                for (offset, wt), ftype in zip(concrete, field_type_names)
            ]
            plans.append((cname, layout.tag, fields))
        return plans

    def _const_string(self, text: str) -> list[str]:
        """Instructions leaving an interned literal String (ptr, len)."""
        offset, length = self.string_pool.intern(text)
        return [f"i32.const {offset}", f"i32.const {length}"]

    # ---- recursive-ADT helper generation (#924) -----------------------
    #
    # A directly- (or mutually-) recursive ADT cannot be rendered / folded
    # INLINE — the traversal would expand forever at COMPILE time.  #911
    # detected this via the full-ptype `_seen` guard and cleanly skipped
    # (E602), dropping the enclosing function.  #924 upgrades the skip to an
    # actually-emitted, self-calling helper function `$show_<type>` /
    # `$hash_<type>` — one per recursive type — that recurses over the finite
    # VALUE at run time.  This mirrors the structural-`$eq_<type>` machinery
    # (operators.py `_generate_adt_eq_fn` / `_request_adt_eq_helper`).

    def _show_hash_fn_name(self, kind: str, ptype: str) -> str:
        """Mangle ``ptype`` into its ``$show_<type>`` / ``$hash_<type>`` name.

        Uses the shared `mangle_type_name` escape — the same injective
        convention the `$eq_<type>` helpers and mono-clone symbols use, so a
        `List<Int>` helper and a bare ADT literally named `List_LInt_R` cannot
        collide.
        """
        return f"${kind}_{mangle_type_name(ptype)}"

    def _request_show_hash_helper(
        self, kind: str, ptype: str, node: ast.Expr,
    ) -> str | None:
        """Ensure a recursive ``$show``/``$hash`` helper exists; return its name.

        ``kind`` is ``"show"`` or ``"hash"``.  Deduped by name and guarded
        against re-entry via ``_show_hash_pending`` so a self- (or mutually-)
        recursive ADT emits exactly one helper per type.  Returns None when the
        body cannot be generated (an unrenderable / unhashable field), leaving
        the caller to fall back to the clean E602 skip.
        """
        fn_name = self._show_hash_fn_name(kind, ptype)
        if fn_name in self._show_hash_helpers or fn_name in self._show_hash_pending:
            return fn_name
        self._show_hash_pending.add(fn_name)
        body = self._generate_show_hash_helper(kind, fn_name, ptype, node)
        if body is None:
            self._show_hash_pending.discard(fn_name)
            return None
        self._show_hash_helpers[fn_name] = body
        return fn_name

    def _generate_show_hash_helper(
        self, kind: str, fn_name: str, ptype: str, node: ast.Expr,
    ) -> str | None:
        """Generate the full WAT of a recursive ``$show``/``$hash`` helper.

        The helper takes the ADT pointer as ``$p`` (local 0) and returns the
        rendered String ``(result i32 i32)`` (show) or the i64 hash (hash).
        The body reuses the inline `_show_adt` / `_hash_adt` emitters (so there
        is exactly ONE structural-render implementation) run in a FRESH
        local-allocation scope with an EMPTY ``_seen`` — the emitter renders one
        full level and adds ``ptype`` to ``_seen`` before descending, so the
        recursive field (same ``ptype``) routes back through this same helper (a
        ``call $show_<type>`` self-reference) rather than re-expanding inline.
        The emitters allocate into the swapped-in scope, set ``needs_alloc``
        when they build strings, and their shadow-stack rooting is wrapped by a
        GC prologue/epilogue that saves and restores ``$gc_sp`` around the frame.

        Bounded against POLYMORPHIC recursion (#933): a non-uniform ADT
        (`Box<T>` with a `Box<Box<T>>` field) mints a strictly deeper type at
        each descent, so the `_seen` guard never routes back to a self-call and
        this generation recurs unboundedly.  The shared
        ``_derived_helper_depth`` cap catches that runaway and returns None → the
        caller falls back to the clean E602 skip (unchanged from the pre-#924
        behaviour for such types).  Uniform shapes recur on the SAME ptype and
        never reach the cap (measured generation depth 1).
        """
        if self._derived_helper_depth >= self._derived_helper_depth_cap:
            return None
        self._derived_helper_depth += 1
        try:
            return self._generate_show_hash_helper_body(kind, fn_name, ptype, node)
        finally:
            self._derived_helper_depth -= 1

    def _generate_show_hash_helper_body(
        self, kind: str, fn_name: str, ptype: str, node: ast.Expr,
    ) -> str | None:
        """Body of :meth:`_generate_show_hash_helper` (depth-bound wrapper above)."""
        base, _ = self._split_param_type(ptype)

        # Swap in a fresh local-allocation scope so the inline emitters'
        # `alloc_local` calls land in THIS helper's frame, not the caller's.
        # Local 0 is the `$p` parameter; body locals and the GC epilogue's
        # save/return locals are allocated from index 1 up.
        saved_locals = self._locals
        saved_next = self._next_local
        saved_needs_alloc = self.needs_alloc
        self._locals = []
        self._next_local = 1
        self.needs_alloc = False
        body_allocates = False
        try:
            # `_seen` starts EMPTY so `_show_adt` renders ONE full level of the
            # constructor (it adds `ptype` to `seen` before descending into
            # fields).  The recursive field — same `ptype`, now in `seen` — then
            # hits the guard and emits a `call $<kind>_<type>` self-reference
            # back into THIS helper, so the recursion runs over the value at run
            # time rather than expanding inline at compile time.
            value_instrs = ["local.get 0"]
            if kind == "show":
                inner = self._show_adt(base, ptype, value_instrs, node, frozenset())
                result_part = "(result i32 i32)"
            else:
                inner = self._hash_adt(base, ptype, value_instrs, node, frozenset())
                result_part = "(result i64)"
            if inner is None:
                return None
            body_allocates = self.needs_alloc
            gc_prologue, gc_epilogue = self._show_hash_gc_frame(kind)
            local_decls = self.extra_locals_wat()
        finally:
            self._locals = saved_locals
            self._next_local = saved_next
            # A helper that allocates forces the CALLER's frame to carry a GC
            # prologue too (the call site sees the returned pointer as a root).
            self.needs_alloc = saved_needs_alloc or body_allocates

        lines = [f"  (func {fn_name} (param $p i32) {result_part}"]
        lines.extend(f"    {d}" for d in local_decls)
        lines.extend(f"    {i}" for i in gc_prologue)
        lines.extend(f"    {i}" for i in inner)
        lines.extend(f"    {i}" for i in gc_epilogue)
        lines.append("  )")
        return "\n".join(lines)

    def _show_hash_gc_frame(
        self, kind: str,
    ) -> tuple[list[str], list[str]]:
        """Build the GC prologue/epilogue for a recursive show/hash helper.

        ALWAYS emitted — the inline `_show_adt` / `_hash_adt` body
        unconditionally shadow-pushes its struct pointer (`gc_shadow_push`),
        and each recursive `call $<kind>_<type>` re-enters and pushes again, so
        without a per-call ``$gc_sp`` restore a deep recursive value leaks one
        shadow slot per level and overflows the 4 096-slot shadow stack (a
        `hash` over a `List<Int>` allocates nothing yet still leaks the pointer
        push).  The frame saves ``$gc_sp`` on entry, roots the pointer
        parameter (local 0), and restores ``$gc_sp`` on exit — re-rooting the
        returned String pointer for ``show`` so the caller does not sweep it
        before consuming it.  Allocates its save/return locals from the CURRENT
        (swapped-in) scope, so they share the helper's index space with the
        body locals.
        """
        gc_sp_save = self.alloc_local("i32")
        # `needs_alloc` beside the push (#1376/#1379): the flag is what
        # declares `$gc_sp`, so a push without it emits a reference to an
        # undeclared global whenever nothing else in the module allocates —
        # and `_scope_shadow_roots` refuses it outright.
        self.needs_alloc = True
        prologue = [
            "global.get $gc_sp",
            f"local.set {gc_sp_save}",
            *gc_shadow_push(0),
        ]
        if kind == "show":
            ret_ptr = self.alloc_local("i32")
            ret_len = self.alloc_local("i32")
            epilogue = [
                f"local.set {ret_len}",
                f"local.set {ret_ptr}",
                f"local.get {gc_sp_save}",
                "global.set $gc_sp",
                *gc_shadow_push(ret_ptr),
                f"local.get {ret_ptr}",
                f"local.get {ret_len}",
            ]
        else:
            ret_i64 = self.alloc_local("i64")
            epilogue = [
                f"local.set {ret_i64}",
                f"local.get {gc_sp_save}",
                "global.set $gc_sp",
                f"local.get {ret_i64}",
            ]
        return prologue, epilogue

    # ---- show ---------------------------------------------------------

    def _show_value(
        self,
        ptype: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None = None,
    ) -> list[str] | None:
        """Render a value of parameterized type ``ptype`` to a String.

        ``value_instrs`` leaves the value on the stack in its natural WASM
        shape (i64 for Int/Nat, f64 for Float64, i32 for Bool/Byte/ADT
        pointer, i32_pair for String/Array).  Returns instructions that
        leave the rendered String (ptr, len) on the stack, or None if the
        type is not showable here (recursive ADT, opaque field).
        """
        base, type_args = self._split_param_type(ptype)

        # Primitives — reuse the value-instruction cores factored out for
        # #911.  These behave exactly as the top-level primitive show paths.
        if base == "Int" or base == "Nat":
            return self._to_string_core(value_instrs)
        if base == "Bool":
            return self._bool_to_string_core(value_instrs)
        if base == "Byte":
            return self._byte_to_string_core(value_instrs)
        if base == "Float64":
            return self._float_to_string_core(value_instrs)
        if base == "String":
            return value_instrs  # a String is its own representation
        if base == "Unit":
            # value_instrs leaves nothing useful; drop it and emit "unit".
            return self._const_string("unit")

        # #1321/#1331: a DECLARED `data Array` is not the container — it is
        # this namespace's own one-word ADT, and falling through to
        # `_show_adt` below is what renders it.  Taking the array arm would
        # walk its heap pointer as a (ptr, len) pair.
        if base == "Array" and not self._declares_adt(base):
            elem_type = type_args[0] if type_args else None
            if elem_type is None:
                return None
            # #1091 / PR #1090 review: the element arrives spelled as in the
            # recovered compound (`Array<FI>` keeps its declared `FI`; the
            # top-level grounding never touches nested args) — ground it so
            # the size table, the element load, and the recursive render all
            # see the payload type (`FI` -> `Int`), exactly as a literal
            # `Array<Int>` element does.
            elem_type = self._canonical_field_type(elem_type)
            return self._show_array(elem_type, value_instrs, node, _seen)

        # ADT / Tuple / Option / Result — heap pointer, tag-dispatched.
        return self._show_adt(base, ptype, value_instrs, node, _seen)

    def _show_adt(
        self,
        base: str,
        ptype: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None,
    ) -> list[str] | None:
        seen = _seen or frozenset()
        # Key the recursion guard on the FULL parameterized type, not the bare
        # head: `Option<Option<Int>>` nests `Option<Int>` — a DIFFERENT type,
        # finite depth — and must render INLINE, whereas a directly-recursive
        # ADT (`List<Int>` whose `Cons` field is again `List<Int>`) recurs on
        # the SAME parameterized type.  #911 collapsed the recursive case to a
        # clean skip; #924 routes it to a GENERATED self-calling helper
        # (`call $show_<type>`) so the finite value renders at run time.
        if ptype in seen:
            fn_name = self._request_show_hash_helper("show", ptype, node)
            if fn_name is None:
                return None
            return value_instrs + [f"call {fn_name}"]
        # #933: bound POLYMORPHIC recursion.  A non-uniform ADT (`Box<T>` field
        # `Box<Box<T>>`) never repeats a `ptype`, so the same-type guard above
        # never routes to a self-call: each descent renders INLINE on a
        # strictly-deeper, DISTINCT type whose generic NESTING climbs one level
        # per step without limit, until the walk (and `_parse_type_name` on the
        # ever-deeper type name) blows the Python stack on a check-green program.
        # Past the cap, return None → the enclosing `show` falls back to the
        # clean E602 skip (the same degradation an unrenderable field already
        # gets).  Uniform shapes recur at CONSTANT nesting depth and never
        # approach the cap.
        if self._ptype_nesting_depth(ptype) >= self._derived_helper_depth_cap:
            return None
        seen = seen | {ptype}

        plans = self._composite_ctor_plans(ptype)
        if plans is None:
            return None

        ptr = self.alloc_local("i32")
        acc_ptr = self.alloc_local("i32")
        acc_len = self.alloc_local("i32")
        result_ptr = self.alloc_local("i32")
        result_len = self.alloc_local("i32")

        instrs: list[str] = []
        instrs.extend(value_instrs)
        instrs.append(f"local.set {ptr}")
        # `needs_alloc` beside the push, as every other push site does
        # (#1371): the flag is what declares `$gc_sp`, so a push without
        # it references an undeclared global whenever nothing else in
        # the module allocates.
        self.needs_alloc = True
        instrs.extend(gc_shadow_push(ptr))
        # One shadow slot roots the running accumulator across the per-field
        # concat allocations (seeded with the struct pointer, overwritten with
        # the accumulator on first re-root).
        root_slot = self._reserve_root_slot(instrs, ptr)

        is_tuple = base == "Tuple"

        # Build a nested if/else on the tag.  Each branch renders one
        # constructor's String into (result_ptr, result_len).
        def render_ctor(cname: str, fields: list[tuple[int, str, str]]) -> None:
            # Head: `Ctor(` (or `(` for a Tuple; bare `Ctor` for nullary).
            if is_tuple:
                head = "("
            elif fields:
                head = f"{cname}("
            else:
                head = cname
            piece = self._const_string(head)
            instrs.extend(f"  {i}" for i in piece)
            instrs.append(f"  local.set {acc_len}")
            instrs.append(f"  local.set {acc_ptr}")
            self._reroot(instrs, root_slot, acc_ptr, indent="  ")
            for fi, (offset, wt, ftype) in enumerate(fields):
                if fi > 0:
                    self._concat_into(instrs, acc_ptr, acc_len,
                                      self._const_string(", "), indent="  ",
                                      root_slot=root_slot)
                load = self._load_field(ptr, offset, wt)
                rendered = self._show_value(ftype, load, node, seen)
                if rendered is None:
                    # Unrenderable field — abandon this whole show.
                    raise _ShowHashUnsupported
                self._concat_into(instrs, acc_ptr, acc_len,
                                  rendered, indent="  ", root_slot=root_slot)
            if fields:
                self._concat_into(instrs, acc_ptr, acc_len,
                                  self._const_string(")"), indent="  ",
                                  root_slot=root_slot)
            instrs.append(f"  local.get {acc_ptr}")
            instrs.append(f"  local.set {result_ptr}")
            instrs.append(f"  local.get {acc_len}")
            instrs.append(f"  local.set {result_len}")

        try:
            # tag = mem[ptr]
            n = len(plans)
            for depth, (cname, tag, fields) in enumerate(plans):
                if depth < n - 1:
                    instrs.append(f"local.get {ptr}")
                    instrs.append("i32.load")
                    instrs.append(f"i32.const {tag}")
                    instrs.append("i32.eq")
                    instrs.append("if")
                    render_ctor(cname, fields)
                    instrs.append("else")
                else:
                    # Last constructor: the fall-through else.
                    render_ctor(cname, fields)
            for _ in range(n - 1):
                instrs.append("end")
        except _ShowHashUnsupported:
            return None

        instrs.append(f"local.get {result_ptr}")
        instrs.append(f"local.get {result_len}")
        return instrs

    def _show_array(
        self,
        elem_type: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None,
    ) -> list[str] | None:
        # Render a probe element to confirm the element type is showable and
        # to reuse its instruction shape inside the loop body.
        arr_ptr = self.alloc_local("i32")
        arr_len = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        acc_ptr = self.alloc_local("i32")
        acc_len = self.alloc_local("i32")
        sp_save = self.alloc_local("i32")

        elem_size = self._element_mem_size(elem_type)
        if elem_size is None:
            return None

        # Element load: address = arr_ptr + idx*elem_size, then load per type.
        elem_load = self._load_array_element(arr_ptr, idx, elem_type, elem_size)
        if elem_load is None:
            return None
        elem_rendered = self._show_value(elem_type, elem_load, node, _seen)
        if elem_rendered is None:
            return None

        instrs: list[str] = []
        instrs.extend(value_instrs)  # (ptr, len)
        instrs.append(f"local.set {arr_len}")
        instrs.append(f"local.set {arr_ptr}")
        self.needs_alloc = True  # declares `$gc_sp` for the push (#1371)
        instrs.extend(gc_shadow_push(arr_ptr))

        # acc = "["
        opening = self._const_string("[")
        instrs.extend(opening)
        instrs.append(f"local.set {acc_len}")
        instrs.append(f"local.set {acc_ptr}")
        # Root the accumulator across the per-element concat allocations.
        root_slot = self._reserve_root_slot(instrs, acc_ptr)

        # idx = 0
        instrs.append("i32.const 0")
        instrs.append(f"local.set {idx}")
        instrs.append("block $show_arr_brk")
        instrs.append("  loop $show_arr_lp")
        instrs.append(f"    local.get {idx}")
        instrs.append(f"    local.get {arr_len}")
        instrs.append("    i32.ge_u")
        instrs.append("    br_if $show_arr_brk")
        # Snapshot $gc_sp at the top of the body.  Every string built this
        # iteration (the separator, the element render, the concat results)
        # shadow-pushes its buffer with NO matching pop — those slots unwind
        # only at function exit, so in this loop they leak one-plus per element
        # and overflow the 4 096-slot shadow stack on large arrays.  Restoring
        # $gc_sp to the snapshot at the end of the body reclaims them all; the
        # accumulator is separately rooted in `root_slot` (reserved BELOW the
        # snapshot), so the restore never orphans the live result.
        instrs.append("    global.get $gc_sp")
        instrs.append(f"    local.set {sp_save}")
        # separator ", " for idx > 0
        instrs.append(f"    local.get {idx}")
        instrs.append("    i32.const 0")
        instrs.append("    i32.gt_u")
        instrs.append("    if")
        self._concat_into(instrs, acc_ptr, acc_len,
                          self._const_string(", "), indent="      ",
                          root_slot=root_slot)
        instrs.append("    end")
        # render element
        self._concat_into(instrs, acc_ptr, acc_len,
                          elem_rendered, indent="    ", root_slot=root_slot)
        # Unwind this iteration's shadow slots (accumulator stays in root_slot).
        instrs.append(f"    local.get {sp_save}")
        instrs.append("    global.set $gc_sp")
        # idx++
        instrs.append(f"    local.get {idx}")
        instrs.append("    i32.const 1")
        instrs.append("    i32.add")
        instrs.append(f"    local.set {idx}")
        instrs.append("    br $show_arr_lp")
        instrs.append("  end")
        instrs.append("end")
        # acc = acc ++ "]"
        self._concat_into(instrs, acc_ptr, acc_len,
                          self._const_string("]"), indent="",
                          root_slot=root_slot)

        instrs.append(f"local.get {acc_ptr}")
        instrs.append(f"local.get {acc_len}")
        return instrs

    def _reserve_root_slot(
        self, instrs: list[str], init_ptr: int, indent: str = "",
    ) -> int:
        """Reserve one shadow-stack slot for a loop accumulator; return the
        local holding its address.

        A loop accumulator (`_show_adt` / `_show_array`) lives in a plain
        local across many per-concat `$alloc`s — between iterations it is
        neither on the operand stack nor a GC root, so a collection would
        sweep it.  This pushes ONE slot (via the standard `gc_shadow_push`,
        seeded with the initial accumulator ``init_ptr``) and captures its
        address so the caller re-stores the current accumulator into that
        FIXED slot after each concat (`_reroot`) — exactly one live root
        regardless of loop length (unlike per-iteration pushes, which would
        exhaust the shadow stack).  The slot unwinds at function exit with
        the rest of the frame's shadow region — the same lifetime the
        existing `gc_shadow_push` roots already have.
        """
        slot_addr = self.alloc_local("i32")
        # Capture the slot address (current $gc_sp) BEFORE the push advances it.
        instrs.append(f"{indent}global.get $gc_sp")
        instrs.append(f"{indent}local.set {slot_addr}")
        self.needs_alloc = True  # declares `$gc_sp` for the push (#1371)
        instrs.extend(indent + i for i in gc_shadow_push(init_ptr))
        return slot_addr

    def _reroot(
        self, instrs: list[str], slot_addr: int, ptr_local: int, indent: str,
    ) -> None:
        """Store ``ptr_local`` into the reserved shadow slot ``slot_addr``."""
        instrs.append(f"{indent}local.get {slot_addr}")
        instrs.append(f"{indent}local.get {ptr_local}")
        instrs.append(f"{indent}i32.store")

    def _concat_into(
        self,
        instrs: list[str],
        acc_ptr: int,
        acc_len: int,
        piece_instrs: list[str],
        indent: str,
        root_slot: int | None = None,
    ) -> None:
        """Append ``acc = concat(acc, piece)`` to ``instrs``, in place.

        ``acc_ptr`` / ``acc_len`` hold the running String; ``piece_instrs``
        leaves the piece (ptr, len) on the stack.  Rebinds the accumulator
        locals to the freshly allocated concatenation, then (when
        ``root_slot`` is given) re-roots the new accumulator into that fixed
        shadow slot so it survives the NEXT concat's allocation.
        """
        concat = self._string_concat_core(
            [f"local.get {acc_ptr}", f"local.get {acc_len}"],
            piece_instrs,
        )
        instrs.extend(indent + i for i in concat)
        instrs.append(f"{indent}local.set {acc_len}")
        instrs.append(f"{indent}local.set {acc_ptr}")
        if root_slot is not None:
            self._reroot(instrs, root_slot, acc_ptr, indent)

    def _load_field(
        self, ptr_local: int, offset: int, wt: str,
    ) -> list[str]:
        """Instructions leaving field at ``offset`` on the stack (by WASM type)."""
        if wt == "i64":
            return [f"local.get {ptr_local}", f"i64.load offset={offset}"]
        if wt == "f64":
            return [f"local.get {ptr_local}", f"f64.load offset={offset}"]
        if wt == "i32_pair":
            return [
                f"local.get {ptr_local}", f"i32.load offset={offset}",
                f"local.get {ptr_local}", f"i32.load offset={offset + 4}",
            ]
        # #1043: a zero-size Unit field ("unit" wt) stores nothing, so there is
        # nothing to load — `_show_value` / `_hash_value` render "unit" / fold a
        # constant and ignore these (empty) instructions.  Emitting a spurious
        # `i32.load` here would read the NEXT field's bytes (harmless only
        # because the caller discards it); return nothing instead.
        if wt == "unit":
            return []
        # i32 (Bool/Byte/ADT pointer)
        return [f"local.get {ptr_local}", f"i32.load offset={offset}"]

    def _load_array_element(
        self, arr_ptr: int, idx: int, elem_type: str, elem_size: int,
    ) -> list[str] | None:
        """Instructions leaving arr[idx] on the stack (natural WASM shape)."""
        is_pair = self._is_pair_element_type(elem_type)
        load_op = self._element_load_op(elem_type)
        if load_op is None and not is_pair:
            return None
        addr: list[str] = [f"local.get {arr_ptr}", f"local.get {idx}"]
        if elem_size == 1:
            addr.append("i32.add")
        else:
            addr.append(f"i32.const {elem_size}")
            addr.append("i32.mul")
            addr.append("i32.add")
        if is_pair:
            # addr on stack → duplicate via a temp local to load (ptr, len).
            tmp = self.alloc_local("i32")
            return addr + [
                f"local.set {tmp}",
                f"local.get {tmp}", "i32.load offset=0",
                f"local.get {tmp}", "i32.load offset=4",
            ]
        return addr + [load_op]

    # ---- hash ---------------------------------------------------------

    # 64-bit FNV constants, shared with the String hash above.
    _FNV_BASIS = -3750763034362895579  # 14695981039346656037 as signed i64
    _FNV_PRIME = 1099511628211

    def _hash_value(
        self,
        ptype: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None = None,
    ) -> list[str] | None:
        """Fold a value of type ``ptype`` into an i64 hash.

        Deterministic: primitives hash as their top-level `hash` does;
        composites seed with the constructor tag and mix each field's hash
        (FNV-style).  Returns None for unhashable / recursive types.
        """
        base, type_args = self._split_param_type(ptype)

        if base in ("Int", "Nat"):
            return value_instrs
        if base in ("Bool", "Byte"):
            return value_instrs + ["i64.extend_i32_u"]
        if base == "Float64":
            return value_instrs + ["i64.reinterpret_f64"]
        if base == "Unit":
            return ["i64.const 0"]
        if base == "String":
            return self._translate_hash_string(value_instrs)
        # The hash twin of the show arm above (#1321/#1331).
        if base == "Array" and not self._declares_adt(base):
            elem_type = type_args[0] if type_args else None
            if elem_type is None:
                return None
            # #1091 / PR #1090 review: ground the element spelling (mirrors
            # the show Array arm above).
            elem_type = self._canonical_field_type(elem_type)
            return self._hash_array(elem_type, value_instrs, node, _seen)
        return self._hash_adt(base, ptype, value_instrs, node, _seen)

    def _mix_hash(self, acc: int, field_hash: list[str]) -> list[str]:
        """``acc = (acc XOR field_hash) * FNV_PRIME`` — one fold step."""
        return [
            f"local.get {acc}",
            *field_hash,
            "i64.xor",
            f"i64.const {self._FNV_PRIME}",
            "i64.mul",
            f"local.set {acc}",
        ]

    def _hash_adt(
        self,
        base: str,
        ptype: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None,
    ) -> list[str] | None:
        seen = _seen or frozenset()
        # Full-ptype recursion guard (see `_show_adt`): distinguishes finite
        # same-base nesting (`Option<Option<Int>>`) from genuine self-reference
        # (`List<Int>`).  The former folds inline; the latter routes to a
        # generated self-calling helper (`call $hash_<type>`) that folds the
        # finite value at run time (#924).
        if ptype in seen:
            fn_name = self._request_show_hash_helper("hash", ptype, node)
            if fn_name is None:
                return None
            return value_instrs + [f"call {fn_name}"]
        # #933: bound POLYMORPHIC recursion (see `_show_adt`).  A non-uniform
        # ADT grows a strictly-deeper, DISTINCT `ptype` (one more nesting level)
        # at each inline descent, so the same-type guard above never fires and
        # the fold recurs unboundedly.  Past the cap, return None → the
        # enclosing `hash` falls back to the clean E602 skip.  Uniform shapes
        # recur at constant nesting depth and never approach the cap.
        if self._ptype_nesting_depth(ptype) >= self._derived_helper_depth_cap:
            return None
        seen = seen | {ptype}

        plans = self._composite_ctor_plans(ptype)
        if plans is None:
            return None

        ptr = self.alloc_local("i32")
        acc = self.alloc_local("i64")

        instrs: list[str] = []
        instrs.extend(value_instrs)
        instrs.append(f"local.set {ptr}")
        self.needs_alloc = True  # declares `$gc_sp` for the push (#1371)
        instrs.extend(gc_shadow_push(ptr))
        # Seed with the FNV basis, then mix the tag (distinguishes
        # constructors) and each field's hash.
        instrs.append(f"i64.const {self._FNV_BASIS}")
        instrs.append(f"local.set {acc}")
        instrs.extend(self._mix_hash(
            acc, [f"local.get {ptr}", "i32.load", "i64.extend_i32_u"]))

        def mix_ctor(fields: list[tuple[int, str, str]]) -> None:
            for offset, wt, ftype in fields:
                load = self._load_field(ptr, offset, wt)
                fh = self._hash_value(ftype, load, node, seen)
                if fh is None:
                    raise _ShowHashUnsupported
                fh_local = self.alloc_local("i64")
                instrs.extend(f"  {i}" for i in fh)
                instrs.append(f"  local.set {fh_local}")
                mix = self._mix_hash(acc, [f"local.get {fh_local}"])
                instrs.extend(f"  {i}" for i in mix)

        try:
            n = len(plans)
            for depth, (_cname, tag, fields) in enumerate(plans):
                if depth < n - 1:
                    instrs.append(f"local.get {ptr}")
                    instrs.append("i32.load")
                    instrs.append(f"i32.const {tag}")
                    instrs.append("i32.eq")
                    instrs.append("if")
                    mix_ctor(fields)
                    instrs.append("else")
                else:
                    mix_ctor(fields)
            for _ in range(n - 1):
                instrs.append("end")
        except _ShowHashUnsupported:
            return None

        instrs.append(f"local.get {acc}")
        return instrs

    def _hash_array(
        self,
        elem_type: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None,
    ) -> list[str] | None:
        arr_ptr = self.alloc_local("i32")
        arr_len = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        acc = self.alloc_local("i64")
        sp_save = self.alloc_local("i32")

        elem_size = self._element_mem_size(elem_type)
        if elem_size is None:
            return None
        elem_load = self._load_array_element(arr_ptr, idx, elem_type, elem_size)
        if elem_load is None:
            return None
        elem_hash = self._hash_value(elem_type, elem_load, node, _seen)
        if elem_hash is None:
            return None

        instrs: list[str] = []
        instrs.extend(value_instrs)  # (ptr, len)
        instrs.append(f"local.set {arr_len}")
        instrs.append(f"local.set {arr_ptr}")
        self.needs_alloc = True  # declares `$gc_sp` for the push (#1371)
        instrs.extend(gc_shadow_push(arr_ptr))
        # Seed with basis, mix the length, then each element hash.
        instrs.append(f"i64.const {self._FNV_BASIS}")
        instrs.append(f"local.set {acc}")
        instrs.extend(self._mix_hash(
            acc, [f"local.get {arr_len}", "i64.extend_i32_u"]))

        instrs.append("i32.const 0")
        instrs.append(f"local.set {idx}")
        instrs.append("block $hash_arr_brk")
        instrs.append("  loop $hash_arr_lp")
        instrs.append(f"    local.get {idx}")
        instrs.append(f"    local.get {arr_len}")
        instrs.append("    i32.ge_u")
        instrs.append("    br_if $hash_arr_brk")
        # A COMPOSITE element's hash shadow-pushes its struct pointer with no
        # matching pop; snapshot/restore $gc_sp around the element hash to
        # unwind those per-iteration slots (the i64 accumulator is a value, not
        # a heap root, so nothing here needs rooting).
        instrs.append("    global.get $gc_sp")
        instrs.append(f"    local.set {sp_save}")
        eh_local = self.alloc_local("i64")
        instrs.extend(f"    {i}" for i in elem_hash)
        instrs.append(f"    local.set {eh_local}")
        mix = self._mix_hash(acc, [f"local.get {eh_local}"])
        instrs.extend(f"    {i}" for i in mix)
        instrs.append(f"    local.get {sp_save}")
        instrs.append("    global.set $gc_sp")
        instrs.append(f"    local.get {idx}")
        instrs.append("    i32.const 1")
        instrs.append("    i32.add")
        instrs.append(f"    local.set {idx}")
        instrs.append("    br $hash_arr_lp")
        instrs.append("  end")
        instrs.append("end")

        instrs.append(f"local.get {acc}")
        return instrs

    # -----------------------------------------------------------------
    # Effect handlers: State<T> and Exn<E>
    # -----------------------------------------------------------------

    def _translate_handle_expr(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate a handle expression to WASM.

        Supports State<T> handlers via host imports and Exn<E>
        handlers via WASM exception handling (try_table/catch/throw).
        Other handler types cause the function to be skipped.
        """
        effect = expr.effect
        if not isinstance(effect, ast.EffectRef):
            raise CodegenSkip(
                expr, "handle expression effect must be an EffectRef"
            )

        if effect.name == "State" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_state(expr, env)

        if effect.name == "Exn" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_exn(expr, env)

        # Unsupported handler type
        raise CodegenSkip(
            expr,
            f"only State<T> and Exn<E> handlers supported (got {effect.name})",
        )

    def _translate_handle_state(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate handle[State<T>](@T = init) { ... } in { body }.

        Compiles by:
        1. Evaluating init_expr and calling state_put_T to set initial state
        2. Temporarily injecting get/put effect ops for the body
        3. Compiling the body with these ops active
        4. Restoring the previous effect ops
        """
        assert isinstance(expr.effect, ast.EffectRef)  # noqa: S101
        type_arg = expr.effect.type_args[0]  # type: ignore[index]
        if not isinstance(type_arg, ast.NamedType):
            raise CodegenSkip(
                expr, "State<T> type argument must be a named type"
            )
        # #914: use the FULL canonical slot name (`Tuple<Int, Int>`, not the
        # base `Tuple`) so the handler-body get/put/push/pop calls match the
        # `(import …)` decls emitted from `_state_types` (also full names) —
        # pre-fix the two diverged for composite T (`state_push_Option` vs
        # `state_push_Option<Int>`).  Then route through the injective
        # `mangle_type_name` (#775) so the WAT identifier is legal.
        # `type_name` is the alias-OPAQUE source spelling, and it survives
        # for exactly one role: the NAMEABILITY gate below.  The #1006
        # Vera-name mirror ("what did the source call this?", for
        # `_infer_vera_type`) reads the same spelling out of the shared
        # `effect_op_result_names` table instead, so mono discovery's copy
        # of that answer is derived once rather than twice (#1207).
        type_name = type_expr_slot_name(type_arg)
        if type_name is None:  # pragma: no cover — NamedType always resolves
            raise CodegenSkip(
                expr, "State<T> type argument has no slot name"
            )
        # The import FAMILY (names + WASM types) is the CELL the checker
        # typed (#1209), matching `_check_state_type` registration.
        # `State<Count>` with `type Count = Nat` joins the `state_*_Nat`
        # family every host already binds, instead of minting a
        # `state_*_Count` family whose derived WT (i32, the unknown-name
        # default) contradicts its registered i64 (#1205); `State<MaybeInt>`
        # with `type MaybeInt = Option<Int>` joins the `Option<Int>` family
        # a `State<Option<Int>>` sibling site targets, instead of splitting
        # the cell in two behind a check that typed them as one (#1209).
        # SLOT names stay checker-level: top name syntactic, type
        # arguments canonicalized (the checker's binding rule), so the
        # clause envs below use those, not the family.
        # IDENTITY and REPRESENTATION, derived side by side from the one
        # type expression (#1218).  `family` discriminates the refinement —
        # `State<Pos>` and `State<Neg>` over one base are two cells to the
        # checker and so two here — and is what the symbols, the pushed-cell
        # stack and the addressability gate use.  `family_base` strips it,
        # and is what every width / pointer-ness / write-guard decision
        # below uses, because all three refinements of one base share those.
        family = self._family_name(type_arg)
        # The boundary's REPRESENTATION base, matching the bare-`put` path
        # (PR #1238 review): both dispatch paths must classify one cell the
        # same way, and `family_fallback_name`'s residue can leave a
        # syntactic alias behind the first hop.  `_boundary_base` is that
        # two-hop composition, named once (#1256) rather than spelled out
        # at each of the sites that need it.
        family_base = self._boundary_base(type_arg)
        mangled = mangle_type_name(family)

        put_import = f"$vera.state_put_{mangled}"
        get_import = f"$vera.state_get_{mangled}"
        push_import = f"$vera.state_push_{mangled}"
        pop_import = f"$vera.state_pop_{mangled}"

        # The clause-scope STATE slot name — the `with` ANNOTATION's own
        # slot name under the CHECKER's rule (top name syntactic,
        # arguments canonicalized), mirroring control.py's binding.
        # None for a stateless handler: the checker binds NO state slot
        # then, and the clause translation must not either (pre-fix it
        # pushed the capture unconditionally, skewing a stateless put
        # clause's `@T.0` from the checker's binding — the op argument —
        # to the pre-store cell value).
        state_slot_name: str | None = None
        if expr.state is not None:
            state_slot_name = self._type_expr_to_slot_name(
                expr.state.type_expr)

        instructions: list[str] = []

        # 1. Evaluate the initial-state expression BEFORE pushing the new
        #    cell: the init expr belongs to the ENCLOSING scope, so a
        #    get/put inside it (an outer handler's op) must observe the
        #    OUTER cell — pushing first made the host's top-of-stack read
        #    hit the fresh inner cell's default 0 instead (PR #1003 panel;
        #    pre-existing).  The init value rides the operand stack across
        #    the zero-arg push call below.
        init_instrs: list[str] | None = None
        if expr.state is not None:
            # #865/#1212: mark a Byte cell's literal init (or the literal
            # leaves of an `if` / `match` init) BEFORE translating, so the
            # value lowers at the cell's i32 width in one pass.
            self._mark_state_byte_write(expr.state.init_expr, family_base)
            init_instrs = self.translate_expr(expr.state.init_expr, env)
            if init_instrs is None:
                return None
            # #1203: the init value BINDS into the state CELL — guard the
            # @Int -> @Nat narrowing (and the @Nat -> @Int widen dual)
            # exactly like a `let` binding, so an unverified compile traps
            # instead of storing a negative through the @Nat cell.  Keyed
            # off `family_base` — the cell's REPRESENTATION (#1218), the
            # same source every other guard site uses, derived from the
            # effect's `State<T>` argument — NOT the declared `with`
            # annotation, which can diverge (#1206) and, as a
            # RefinementType, has no `name` at all (PR #1202 review: the
            # getattr skipped both branches for refined binders while the
            # verifier recorded the obligation).  `type_name` survives as
            # the nameability gate alone.
            if (family_base == "Nat"
                    and self._narrows_into_nat(expr.state.init_expr)):
                init_instrs = self._emit_nat_bind_guard(init_instrs)
            elif (family_base == "Int"
                    and self._result_is_nat(expr.state.init_expr)):
                init_instrs = self._emit_int_widen_guard(init_instrs)
            instructions.extend(init_instrs)

        # 2. Push a fresh state cell (isolates this handler from any outer
        #    handler of the same type — fixes #417), then store the init
        #    value into it.  If no state clause, the cell starts at the
        #    default (0).
        instructions.append(f"call {push_import}")
        if init_instrs is not None:
            instructions.append(f"call {put_import}")

        # 3. Save current effect_ops and inject handler ops.  Record `get`'s
        #    result WAT type (#914 A2: a `match get(())` inside the body needs
        #    it to type the scrutinee — State<T>'s T is validated non-pair by
        #    the checker, so `_type_name_to_wasm` yields the op's result WT).
        # The four registries are SAVED BY REFERENCE and REPLACED with fresh
        # copies, so this handler's `get`/`put` never land in a dict some
        # enclosing scope (or a `StateClauseEntry` from an outer handler)
        # still holds — the in-place `self._effect_ops["get"] = …` this
        # replaces mutated exactly such a shared object and relied on the
        # rebinding below to hide it.  The restore is in a `finally` for the
        # same reason its twin `_translate_state_clause_op` has one: the body
        # translation raises `CodegenSkip` on any unsupported shape, and a
        # non-local exit past the restore would leak this handler's op
        # registry into whatever catches it.
        saved_ops = self._effect_ops
        saved_result_wt = self._effect_op_result_wt
        saved_result_vera = self._effect_op_result_vera
        saved_cells = self._effect_op_cells
        saved_clause_ops = self._state_clause_ops
        # The DECLARATION-time snapshot the clause entries carry (#1211) —
        # private copies, so nothing that runs later can alter what a clause
        # body's bare op resolves against.  `decl_addressable_from` is the
        # same idea for the host CELL stack (#1233): how many cells were
        # pushed here, i.e. how far back a clause body's outward-routed op has
        # to reach past cells the intrinsics cannot skip.
        decl_ops = dict(saved_ops)
        decl_result_wt = dict(saved_result_wt)
        decl_result_vera = dict(saved_result_vera)
        decl_cells = dict(saved_cells)
        decl_clause_ops = dict(saved_clause_ops)
        decl_addressable_from = self._addressable_from
        self._effect_ops = {
            **saved_ops,
            "get": (get_import, False),
            "put": (put_import, True),
        }
        # The fourth registry, in lock-step (#1218): which CELL a bare
        # `get`/`put` under this handler dispatches to, named
        # canonically instead of being recoverable only by unpicking
        # the mangled import name above.
        cell = CellNames(family=family, base=family_base)
        self._effect_op_cells = {
            **saved_cells, "get": cell, "put": cell,
        }
        self._effect_op_result_wt = {
            **saved_result_wt,
            "get": self._type_name_to_wasm(family_base),
        }
        # #1006: the VERA-name mirror of the WT record above —
        # `_infer_vera_type` needs the Vera name (not the layout-ambiguous
        # WAT type) to type a `get(())` array-literal element.  #1207: from
        # the shared derivation, which mono discovery pushes for the same
        # `handle` expression — one table, so the clone discovery emits is
        # the clone the rewrite below calls.
        #
        # No shadow guard at ANY of these four replacements, matching the
        # declared-row site (#1284): they record which cell this handler's
        # op names reach, which is true whatever the program's declarations
        # are called, and every consumer that has to know whether a given
        # bare call IS the op asks `_bare_call_denotes_op` at the call site.
        # "Inside a handler body the op owns the name" is what this used to
        # say, and it is not the language's rule — the checker resolves a
        # bare `get` to a user declaration of that name anywhere it is in
        # scope, handler body included.
        self._effect_op_result_vera = {
            **saved_result_vera,
            **effect_op_result_names([expr.effect]),
        }
        # No `_state_getters` (#1285) replacement rides along here, and that
        # is deliberate: the family-keyed getter table exists for
        # `new(State<T>)`, which is legal only in an `ensures` clause, and a
        # contract is compiled outside the handled body this restores around
        # — so a handler-scoped entry would be unreachable.  The declared
        # effect row, registered in `codegen/functions.py`, is the whole
        # population.
        # #976 option C: register the clauses so each get/put CALL SITE in
        # the body inlines its clause body (intrinsic-hybrid semantics)
        # instead of the bare host-cell call.  Start from an EMPTY registry:
        # the innermost handler owns the get/put op NAMES within its body
        # (matching the `_effect_ops` overwrite above), so an op this
        # handler declares no clause for is the bare intrinsic op — never an
        # OUTER handler's clause (PR #1003 review: a nested handler with
        # only a put clause inherited the outer get transform).
        # The clause bodies compile against THIS handler-declaration
        # scope's env (threaded through the registry), not the op
        # call-site's: the checker checks clause bodies at the handler
        # declaration, so a clause slot reference reaching past the
        # clause's own bindings must resolve against the declaration
        # scope — inlining at the call-site env silently re-resolved it
        # against same-typed bindings the handled body made before the op
        # call (PR #1202 adversarial round, F3; locals are function-wide
        # indices, so declaration-scope locals stay valid at every inline
        # site).  The Exn lowering already compiles its clause in the
        # handle's own env.
        self._state_clause_ops = {}
        for clause in expr.clauses:
            # #1208: the two class-collision skips that stood here are gone.
            # Both existed because codegen keyed clause slots by a rendering
            # that was not the checker's — one direction merged two checker
            # classes under one codegen key, the other split one checker
            # class across two.  Bind and ref now BOTH render through
            # `vera.naming`, so a pattern and an annotation are one key here
            # exactly when they are one class to the checker, and the shapes
            # the skips refused (two aliases of one refined class; a
            # refinement literal against its alias) lower with the checker's
            # own semantics.
            #
            # #1211: the entry carries the WHOLE declaration-time scope — the
            # env AND the three op registries and the clause registry as they
            # stood before this handler installed its own (the `decl_*`
            # snapshots above, taken before the replacements).  A bare
            # `get`/`put` in a clause body belongs to the ENCLOSING context,
            # the same rule as an outer slot reference in a clause body;
            # threading only the env left the op registries at THIS handler's,
            # so such a call read and wrote the inner cell while the checker
            # typed it against the outer one.
            self._state_clause_ops[clause.op_name] = StateClauseEntry(
                clause=clause,
                family=family,
                family_base=family_base,
                state_slot_name=state_slot_name,
                decl_env=env,
                get_import=get_import,
                put_import=put_import,
                decl_effect_ops=decl_ops,
                decl_effect_op_result_wt=decl_result_wt,
                decl_effect_op_result_vera=decl_result_vera,
                decl_effect_op_cells=decl_cells,
                decl_state_clause_ops=decl_clause_ops,
                decl_addressable_from=decl_addressable_from,
            )

        # 4. Compile handler body.  This handler's `state_push_T` has run, so
        #    its cell is now the innermost of family `family` — and an op in
        #    the BODY targets exactly that handler, so nothing is shadowed for
        #    it (`_addressable_from` moves to the top of the stack).  An op in
        #    a CLAUSE body rolls that index back to the declaration-time value
        #    the entries above carry (#1233).
        saved_pushed = self._pushed_cell_families
        saved_addressable = self._addressable_from
        self._pushed_cell_families = [*saved_pushed, family]
        self._addressable_from = len(self._pushed_cell_families)
        try:
            body_instrs = self.translate_block(expr.body, env)
            # Record this handle expression's stack shape HERE, while
            # the handler's effect-op registries are still installed
            # (#1371).  A `handle`'s value is its body's, and the body's
            # ops resolve through registries the `finally` below
            # restores — so asked afterwards, from the scoping wrapper,
            # a nested handler's `get` answers with the ENCLOSING
            # handler's result width.
            self._scoped_expr_shape[id(expr)] = (
                self._compute_stack_shape(expr))
        finally:
            # 5. Restore effect_ops (and the clause registry — nested
            #    handlers).  In a `finally` because the body translation
            #    raises `CodegenSkip` for any unsupported shape.
            self._effect_ops = saved_ops
            self._effect_op_result_wt = saved_result_wt
            self._effect_op_result_vera = saved_result_vera
            self._effect_op_cells = saved_cells
            self._state_clause_ops = saved_clause_ops
            self._pushed_cell_families = saved_pushed
            self._addressable_from = saved_addressable

        if body_instrs is None:
            return None

        instructions.extend(body_instrs)

        # 6. Pop the state cell (restores outer handler's value).
        # pop is stack-neutral so the body's return value is already on the
        # WASM value stack and is unaffected.
        instructions.append(f"call {pop_import}")

        return instructions

    def _reject_unaddressable_clause_op(self, call: ast.FnCall) -> None:
        """Refuse a clause-body bare op that cannot reach its own cell (#1233).

        §7.5.2 routes a bare ``get``/``put`` written in a clause body to the
        ENCLOSING context.  Codegen implements the routing half exactly — the
        call resolves against the handler's declaration-time registries — but
        the ADDRESSING half belongs to the host, and `state_get_T` /
        `state_put_T` reach only the INNERMOST pushed cell of family ``T``.
        The two halves agree exactly when the handler the op resolves to owns
        that innermost cell — i.e. when no cell of the target's family sits
        between the emission point and it.

        `_pushed_cell_families[_addressable_from:]` is precisely that "between"
        set: the cells pushed since the scope the op resolves into.  If the
        target family occurs in it, the store or read would land in the wrong
        cell — `handle[State<Int>]` nested in `handle[State<Int>]` with a bare
        `put(42)` in the inner clause writes the INNER cell where the rule
        says the outer one (the probe returns 5100 where the rule says 5042).
        The shadowing cell need not be the immediately enclosing one: with an
        `Int`/`Nat`/`Int`/`Nat` nest, the third level's clause routes to the
        second but its `state_put_Nat` addresses the fourth's cell.

        Different-family nesting has no such conflict, so it lowers exactly as
        specified — which is what the spec sentence now claims.  The
        unaddressable case is refused loudly here instead of compiling to
        hybrid semantics; true outward addressing needs depth-indexed host
        access across all three runtimes and is tracked as #1233.

        Both spellings reach this gate: `State.put(x)` is routed through
        `_translate_call` like the bare `put(x)`, so the refusal is one gate
        over one rule, and the message names both forms.
        """
        shadowed = self._pushed_cell_families[self._addressable_from:]
        if not shadowed:
            return
        # The refusal is about the State HOST INTRINSICS, which address only
        # the innermost cell — so the gate asks whether this is a State op,
        # not whether the op happens to have a cell recorded.  Those were
        # the same question only by accident: `_effect_op_cells` held State
        # entries alone until `throw` joined it (#1269), and
        # `_pushed_cell_families` carries FAMILY names, so `throw` under
        # `Exn<Int>` inside a `State<Int>` clause body compared equal and
        # the gate refused a program that has no addressing problem at all
        # (`throw` is a WASM tag, not a host cell).
        if call.name not in _STATE_OP_NAMES:
            return
        # ONE canonical family on both sides, and no mangling anywhere in the
        # comparison (#1218).  Round 5 of #1233 had the two sides in two
        # REPRESENTATIONS — `_pushed_cell_families` and a clause entry carry
        # the canonical family (`Option<Int>`), an import name carries the
        # mangled one (`Option_LInt_R`) — and reconciled them by mangling
        # both.  Mangling is not idempotent (`mangle_type_name` of
        # `Option_LInt_R` is `Option__LInt__R`), so re-mangling the
        # already-mangled side made every COMPOSITE family compare unequal to
        # itself and the gate returned instead of refusing:
        # `handle[State<Option<Int>>]` nested in itself, with the outer
        # declaring no `put` clause — the branch that read the import name —
        # compiled and ran 5100 where the enclosing-context rule says 5042.
        # The class is now gone rather than repaired: the op registry carries
        # the canonical family beside the dispatch target
        # (`_effect_op_cells`), so there is one derivation and nothing to
        # unpick.
        entry = self._state_clause_ops.get(call.name)
        if entry is not None:
            target_family = entry.family
            target_base = entry.family_base
        else:
            cell = self._effect_op_cells.get(call.name)
            # Absent for anything that reaches no host State cell — a user
            # effect's op, `throw`, an ability op.
            if cell is None:
                return
            target_family = cell.family
            target_base = cell.base
        if target_family not in shadowed:
            return
        # The message names the cell's BASE, not its identity: since #1218 a
        # refined family's canonical rendering carries the whole predicate,
        # which is a discriminator rather than something to read at the
        # width a diagnostic has.  The base is what a handler is written
        # over, and the shadowing cell shares it — the gate only fires when
        # the two identities are EQUAL, so one name describes both.
        raise CodegenSkip(
            call,
            # Wording covers BOTH spellings: `State.put(x)` delegates to this
            # same gate (calls.py routes the qualified form through
            # `_translate_call`), so naming only the bare form described the
            # refusal a user reading a `State.put` diagnostic did not write.
            f"a bare or qualified State operation '{call.name}' in a handler "
            f"clause body resolves to a "
            f"State<{target_base}> handler (or a declared State<"
            f"{target_base}> row) that an enclosing State<{target_base}> "
            "handler shadows: the host cell intrinsics address only the "
            "innermost cell of a family, so the enclosing-context rule of "
            "spec 7.5.2 cannot be honoured when the same cell family is "
            "nested (see https://github.com/aallan/vera/issues/1233) — nest "
            "handlers over different cell types, or refine the inner cell "
            "with 'with @T = ...', which is the clause's own state override",
        )

    def _translate_state_clause_op(
        self, call: ast.FnCall, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Inline a ``handle[State<T>]`` clause at a get/put call site (#976).

        The pinned intrinsic-hybrid semantics:

        1. ``put(x)`` stores ``x`` intrinsically; ``get`` reads intrinsically.
        2. The clause body EXECUTES; its ``resume(v)`` value IS the op's
           result at this call site (single-shot, tail position — enforced
           below).
        3. ``with @T = <expr>`` OVERRIDES the intrinsic store.
        4. The clause's ``@T.0`` is captured BEFORE the intrinsic store, so
           ``with @T = @T.0`` means *keep the old state*.

        Emission per site (all over the existing host-cell imports — no host
        changes): eval put's argument to a local; ``call get`` into a capture
        local (the clause's ``@T.0``); for put, ``call put`` with the
        argument (intrinsic store); inline the clause body with the op param
        bound FIRST and the captured state LAST (checker binding order:
        ``@T.0`` = state, ``@T.1`` = put's argument); then, if the clause
        carries ``with``, eval the override in the same scope and ``call
        put``.  Stack discipline: the body's net effect is exactly resume's
        value (``[]`` for put — ``resume(())`` is a ``UnitLit``; one ``T``
        for get), and the override's value is consumed by its own put, so
        the site's net stack effect equals the bare host-call it replaces.

        A get clause's ``@Unit`` op param carries no value and gets no env
        binding — a body referencing it fails slot resolution loudly rather
        than resolving to something wrong.
        """
        entry = self._state_clause_ops[call.name]
        clause = entry.clause
        # Only the cell's REPRESENTATION is needed here (#1218): every
        # decision below is a width, a pointer-ness, or a write guard,
        # and all of those are the base's.  The IDENTITY (`entry.family`)
        # is read by the addressability gate, which compares cells.
        family_base = self._resolve_base_type_name(entry.family_base)
        state_slot_name = entry.state_slot_name
        decl_env = entry.decl_env
        get_import = entry.get_import
        put_import = entry.put_import
        if not self._clause_lowerable(clause.body):
            raise CodegenSkip(
                call,
                "State clause requires exactly one resume(...) as the body's "
                "tail expression (single-shot); a missing, repeated, "
                "non-tail, or per-branch-arm resume is not lowerable — "
                "branch inside the argument instead: "
                "resume(if c then a else b)",
            )
        if (clause.state_update is not None
                and self._contains_resume(clause.state_update[1])):
            # A resume inside the `with` expression was silently IGNORED
            # (the lowering counts only the body's resume; the with-expr
            # just evaluates for its value) — reject loudly instead of
            # running a program whose resume does nothing (round-3
            # review, F5).
            raise CodegenSkip(
                call,
                "resume(...) inside a 'with' state-update expression has "
                "no effect (the clause body's tail resume is the "
                "single-shot continuation) — move the resume to the "
                "clause body and keep the 'with' expression pure",
            )
        # #1211: bound the outward re-entry.  Each nested clause body is a
        # fresh expansion of another clause, so the emitted code is
        # exponential in this depth; past the cap the function is a loud
        # [E602] skip rather than a multi-megabyte module.
        #
        # CHECK BEFORE MUTATE (round-5 review): this used to sit below the
        # six registry replacements, so its own raise left `_effect_ops`,
        # the two result-type maps, `_state_clause_ops`, `_in_state_clause`
        # and `_state_clause_family_base` at THIS clause's values — the
        # `CodegenSkip` path out of this method that did not restore them.
        # Unobservable today (the skip unwinds to a per-function boundary
        # that rebuilds the registries), but it is the invariant every other
        # exit here keeps, and a future caller that recovers closer in would
        # inherit a clause scope it never entered.
        if self._clause_inline_depth >= STATE_CLAUSE_INLINE_DEPTH_CAP:
            raise CodegenSkip(
                call,
                "handler clause bodies nest more than "
                f"{STATE_CLAUSE_INLINE_DEPTH_CAP} deep in outward operation "
                "re-entry: a bare get/put in a clause body is the ENCLOSING "
                "handler's operation (spec 7.5.2), so each one inlines "
                "another clause and the emitted code grows exponentially in "
                "the nesting depth — reduce the handler nesting, or move the "
                "clause-body operations into the handled body",
            )

        # WASM type and pointer-ness derive from the threaded FAMILY name
        # (computed once at the handle site — matching the import decls),
        # never the source alias spelling (#1205/#1209).
        state_wt = self._type_name_to_wasm(family_base)
        # Composite state is a heap pointer (i32, excluding the non-pointer
        # i32 scalars) — root the capture/argument locals on the GC shadow
        # stack so an allocating clause body (or `with` expr) cannot free or
        # move them: after the intrinsic store, the captured PRE-store value
        # is unreachable from the host cell, so these locals are its only
        # root.  Same pointer predicate as the closure GC prologue (#347:
        # host handles are i32 indices, not heap pointers).  The pushes are
        # reclaimed by the function's epilogue $gc_sp restore.
        state_is_ptr = (
            state_wt == "i32"
            and family_base not in ("Bool", "Byte")
            and not _is_host_handle_type(family_base)
        )
        instructions: list[str] = []

        # put's argument — the op param, bound under the clause PATTERN's
        # own slot name (the checker binds `put(@Count)`'s argument as
        # `@Count`, whatever the effect's argument was named).
        arg_local: int | None = None
        if call.name == "put":
            # #865/#1212: the Byte width of a literal (or branch-literal)
            # put argument, marked before translation — see the init above.
            self._mark_state_byte_write(call.args[0], family_base)
            arg_instrs = self.translate_expr(call.args[0], env)
            if arg_instrs is None:
                return None
            # #1203: put's argument writes the state cell — guard the
            # narrowing/widening at the boundary (the `let` guard's twin).
            if (family_base == "Nat"
                    and self._narrows_into_nat(call.args[0])):
                arg_instrs = self._emit_nat_bind_guard(arg_instrs)
            elif (family_base == "Int"
                    and self._result_is_nat(call.args[0])):
                arg_instrs = self._emit_int_widen_guard(arg_instrs)
            arg_local = self.alloc_local(state_wt)
            instructions.extend(arg_instrs)
            instructions.append(f"local.set {arg_local}")
            if state_is_ptr:
                self.needs_alloc = True
                instructions.extend(gc_shadow_push(arg_local))

        # Capture the PRE-store state — the clause's LAST-bound slot — but
        # ONLY when the handler declares state: a stateless handler's
        # clause scope has no state binding at all in the checker, so
        # capturing here skewed every clause slot index by one (`@T.0` in a
        # stateless put clause meant the OP ARGUMENT to the checker but
        # resolved to the pre-store cell value — silently wrong values
        # where the types align, a trap where a guard caught it).
        state_local: int | None = None
        if state_slot_name is not None:
            state_local = self.alloc_local(state_wt)
            instructions.append(f"call {get_import}")
            instructions.append(f"local.set {state_local}")
            if state_is_ptr:
                self.needs_alloc = True
                instructions.extend(gc_shadow_push(state_local))

        # Intrinsic store: put stores its argument regardless of the clause.
        if call.name == "put":
            instructions.append(f"local.get {arg_local}")
            instructions.append(f"call {put_import}")

        # The clause scope mirrors the checker exactly: it is based on
        # the HANDLER-DECLARATION env (threaded from the handle site, F3
        # — the call-site env would silently re-resolve outer references
        # against bindings the handled body made before the op call);
        # the op param binds ONLY when the clause declares one (a
        # patternless `put()` binds nothing in the checker's zip — the
        # argument still evaluates and stores, it just gets no name,
        # F2); names use the checker's canonicalization rule.
        clause_env = decl_env
        if arg_local is not None and clause.params:
            # #1208: no `or type_name` fallback.  `type_name` is the EFFECT's
            # type argument, not this pattern's name, so substituting it bound
            # the clause parameter under a key the checker never used — the
            # renderer disagreement the fallback was papering over.  The
            # renderer is now the checker's and reports `None` only for a
            # type expression the checker could not name either, which is a
            # skip, not a different name.
            param_slot = self._type_expr_to_slot_name(clause.params[0])
            if param_slot is None:  # pragma: no cover — defensive
                raise CodegenSkip(
                    clause.params[0],
                    "handler clause parameter has no slot name",
                )
            clause_env = clause_env.push(param_slot, arg_local)
        if state_slot_name is not None and state_local is not None:
            clause_env = clause_env.push(state_slot_name, state_local)

        saved_in_clause = self._in_state_clause
        saved_ops = self._effect_ops
        saved_result_wt = self._effect_op_result_wt
        saved_result_vera = self._effect_op_result_vera
        saved_cells = self._effect_op_cells
        saved_clause_ops = self._state_clause_ops
        saved_clause_family = self._state_clause_family_base
        self._in_state_clause = True
        # `_state_clause_family_base` and `_in_state_clause` describe THIS,
        # not the scope it compiles in: they type the `resume(v)` whose value
        # is this op's result (#865 Byte width), so they take this handler's
        # family however the op registries below are scoped.
        self._state_clause_family_base = family_base
        # LOAD-BEARING (#1211): a clause body is not part of the body it
        # refines, so its own bare `get`/`put` belong to the handler's
        # DECLARATION context — the §7.5.2 lexical rule the checker applies
        # (clauses are checked before the handled effect joins the row) and
        # the same rule `decl_env` already gives outer slot references.
        # Restoring the four declaration-time registries routes such a call
        # to the ENCLOSING handler: its clause if it declares one, otherwise
        # its bare intrinsic import.  Previously only `_state_clause_ops` was
        # cleared, leaving `_effect_ops` at THIS handler's imports, so a
        # nested handler's clause body read and wrote the INNER cell while
        # the checker typed it against the outer one — check-green, valid
        # WASM, silently wrong value.
        #
        # Termination: `decl_state_clause_ops` is the registry from strictly
        # OUTSIDE this handler, so it can never contain this clause; each
        # re-entry from a clause body moves one handler outwards through a
        # finite nesting, and the outermost restores an empty registry.  A
        # nested handle-expr inside a clause body still works — it installs
        # and restores its own registries around its own body.
        self._effect_ops = dict(entry.decl_effect_ops)
        self._effect_op_result_wt = dict(entry.decl_effect_op_result_wt)
        self._effect_op_result_vera = dict(entry.decl_effect_op_result_vera)
        self._effect_op_cells = dict(entry.decl_effect_op_cells)
        self._state_clause_ops = dict(entry.decl_state_clause_ops)
        # #1233: the clause body resolves into the DECLARATION scope, so every
        # cell pushed since then shadows it — `_reject_unaddressable_clause_op`
        # reads exactly this index at each bare-op site inside the body.
        saved_addressable = self._addressable_from
        self._addressable_from = entry.decl_addressable_from
        self._clause_inline_depth += 1
        try:
            body_instrs = self.translate_expr(clause.body, clause_env)
            if clause.state_update is not None:
                # #865/#1212: `with @Byte = <literal or branch join>` writes
                # the cell — mark before translating, as init and put do.
                self._mark_state_byte_write(
                    clause.state_update[1], family_base)
            upd_instrs = (
                self.translate_expr(clause.state_update[1], clause_env)
                if clause.state_update is not None else None
            )
        finally:
            self._in_state_clause = saved_in_clause
            self._effect_ops = saved_ops
            self._effect_op_result_wt = saved_result_wt
            self._effect_op_result_vera = saved_result_vera
            self._effect_op_cells = saved_cells
            self._state_clause_ops = saved_clause_ops
            self._state_clause_family_base = saved_clause_family
            self._addressable_from = saved_addressable
            self._clause_inline_depth -= 1
        if body_instrs is None:
            return None
        # #1203: for a GET clause the body's net value is the tail
        # `resume(v)` argument — the op's @T-typed RESULT at this call
        # site — so guard a narrowing/widening resume value the same way
        # the closure-return guard works (`_compile_lifted_closure`'s
        # analogue for the inlined clause).
        if call.name == "get":
            resume_arg = self._tail_resume_arg(clause.body)
            if resume_arg is not None:
                if (family_base == "Nat"
                        and self._narrows_into_nat(resume_arg)):
                    body_instrs = self._emit_nat_bind_guard(body_instrs)
                elif (family_base == "Int"
                        and self._result_is_nat(resume_arg)):
                    body_instrs = self._emit_int_widen_guard(body_instrs)
        instructions.extend(body_instrs)
        if clause.state_update is not None:
            if upd_instrs is None:
                return None
            # #1203: `with @T = <expr>` overrides the state cell — the
            # third write boundary; same guard pair as put's argument.
            if (family_base == "Nat"
                    and self._narrows_into_nat(clause.state_update[1])):
                upd_instrs = self._emit_nat_bind_guard(upd_instrs)
            elif (family_base == "Int"
                    and self._result_is_nat(clause.state_update[1])):
                upd_instrs = self._emit_int_widen_guard(upd_instrs)
            instructions.extend(upd_instrs)
            instructions.append(f"call {put_import}")
        return instructions

    @staticmethod
    def _contains_resume(node: object) -> bool:
        """Whether *node* contains a ``resume(...)`` call anywhere —
        nested ``HandleExpr`` clauses excluded (their resumes are the
        inner handler's), mirroring ``_clause_lowerable``'s counter."""
        if isinstance(node, ast.HandleExpr):
            if CallsHandlersMixin._contains_resume(node.body):
                return True
            return (node.state is not None
                    and CallsHandlersMixin._contains_resume(
                        node.state.init_expr))
        if isinstance(node, ast.FnCall) and node.name == "resume":
            return True
        if isinstance(node, (list, tuple)):
            return any(CallsHandlersMixin._contains_resume(i) for i in node)
        if is_dataclass(node) and not isinstance(node, type):
            return any(
                CallsHandlersMixin._contains_resume(getattr(node, f.name))
                for f in fields(node)
            )
        return False

    def _mark_state_byte_write(
        self, value: ast.Expr, family_base: str,
    ) -> None:
        """#865's Byte-literal width coercion at a State-cell WRITE
        boundary: ``@Byte`` is i32 (spec §11) but an int literal defaults
        to ``i64.const``, so a literal flowing into a ``State<Byte>``
        cell (init, put argument on either dispatch path, ``with``
        update, get-clause resume value) validated as ill-typed WASM —
        the family imports were correctly i32 all along.

        Only the cell-family question lives here; the branch descent and
        the width decision are ``WasmContext._mark_byte_write_value``
        (#1212), the ONE marking the `let` binding, the constructor field
        and the call argument drive too.  The coercion used to test for a
        bare ``IntLit`` and OVERWRITE the already-translated lowering,
        which is why every branch spelling — including
        ``resume(if c then { 1 } else { 2 })``, the form the E602 clause
        skip message recommends — compiled to invalid WASM.  Marking
        before the value is translated fixes the branch case and translates
        the written value exactly once.

        Takes the cell's REPRESENTATION name (#1218): a refined `Byte`
        cell has its own family carrying the predicate, and the same
        i32 width."""
        self._mark_byte_write_value(value, family_base)

    @staticmethod
    def _tail_resume_arg(body: ast.Expr) -> ast.Expr | None:
        """The tail ``resume(v)``'s argument expression, descending the
        join-free chain (Block trailing expression, single-arm match) —
        ``None`` when the tail is not a one-argument resume.  The SINGLE
        owner of the descent: :py:meth:`_clause_lowerable` consumes this
        helper, so the lowering predicate and the #1203 get-result guard
        can never drift apart."""
        tail: ast.Expr = body
        while True:
            if isinstance(tail, ast.Block):
                tail = tail.expr
                continue
            if isinstance(tail, ast.MatchExpr) and len(tail.arms) == 1:
                tail = tail.arms[0].body
                continue
            break
        if (isinstance(tail, ast.FnCall) and tail.name == "resume"
                and len(tail.args) == 1):
            return tail.args[0]
        return None

    def _clause_lowerable(self, body: ast.Expr) -> bool:
        """True when the clause body has EXACTLY one ``resume(...)`` and it
        IS the body's tail expression.

        The tail chain descends only through join-free positions: a Block's
        trailing expression and a SINGLE-arm match's arm body (no
        alternative, so the arm's value flows straight through).  An ``if``
        or a multi-arm ``match`` is a JOIN and is never a lowerable tail —
        even when one or every arm resumes: ``resume`` types as ``Unit``, so
        the checker records the branch as a VOID block, but the inline
        lowering makes a resume push the op's result value; a value on (or
        missing from) a void join's stack is an invalid WASM module either
        way (PR #1003 review: both the per-arm shape and the
        one-arm-resumes/other-arm-doesn't shape reproduced it).  The
        canonical form branches inside the argument instead
        (``resume(if c then a else b)``), which types the branch by the
        value.

        The total count treats a nested ``HandleExpr`` specially: its
        CLAUSES own their resumes (they are the inner handler's, and would
        otherwise spuriously reject this clause), but its body and
        state-init are lexically part of THIS clause — a resume there
        belongs here, is necessarily non-tail, and must reject the lowering
        rather than corrupt the inner body's stack.
        """
        def total_count(node: object) -> int:
            if isinstance(node, ast.HandleExpr):
                n = total_count(node.body)
                if node.state is not None:
                    n += total_count(node.state.init_expr)
                return n
            if isinstance(node, ast.FnCall) and node.name == "resume":
                # resume's own arguments cannot contain another resume in a
                # checkable program (resume returns Unit); count args anyway
                # so a pathological nesting is rejected, not miscounted.
                return 1 + sum(total_count(a) for a in node.args)
            if isinstance(node, (list, tuple)):
                return sum(total_count(item) for item in node)
            if is_dataclass(node) and not isinstance(node, type):
                return sum(
                    total_count(getattr(node, f.name))
                    for f in fields(node)
                )
            return 0

        # Single source of truth for the join-free tail descent: the same
        # helper the get-resume guard uses (PR #1202 review — two copies
        # of the descent would drift, and a drift silently un-guards a
        # clause this predicate still lowers).
        return (self._tail_resume_arg(body) is not None
                and total_count(body) == 1)

    def _refined_exn_payload_type(
        self, cell: CellNames, call: ast.FnCall,
    ) -> ast.TypeExpr | None:
        """This ``throw``'s payload type when it is a REFINEMENT, else None
        (#1268).

        The refined-first branch selector at the throw write boundary, asked
        BEFORE a guard local is allocated so an unrefined payload's WAT stays
        byte-identical to the pre-#1268 output.  It is the same
        :mod:`vera.naming` derivation :meth:`_refinement_guard_parts`
        resolves through — the naming layer answers "is this a refinement,
        and over what binder", and codegen layers its representation
        decisions on top — so this cannot select an arm the emitter then
        disagrees with.

        A ``throw`` cell with no payload type expression fails CLOSED.  Both
        producers (the declared-effect row in ``codegen/functions.py`` and
        the ``handle[Exn<E>]`` body below) thread it; a producer that forgot
        to would otherwise emit no guard silently while the verifier went on
        recording one — the exact false-``guarded`` claim this issue was.
        """
        if cell.type_expr is None:
            raise CodegenSkip(  # pragma: no cover — defensive
                call,
                f"Exn<{cell.family}> payload carries no type expression, so "
                "its refinement predicate cannot be guarded at the throw",
            )
        if naming.refinement_binder_parts(
                cell.type_expr, self._alias_env) is None:
            return None
        return cell.type_expr

    def _emit_exn_payload_refine_guard(
        self, value: list[str], payload_te: ast.TypeExpr, cell: CellNames,
        call: ast.FnCall, env: WasmSlotEnv,
    ) -> list[str]:
        """Wrap *value* with the §2.6.5 predicate guard for a refined
        ``Exn<E>`` payload (#1268) — the refined twin of the sign guards
        ``_emit_nat_bind_guard`` / ``_emit_int_widen_guard`` give the
        unrefined payload at the same call site.

        ``throw(v)`` narrows *v* into the payload slot exactly as a call
        argument narrows into a refined formal, but the payload crosses no
        function boundary, so none of §2.6.5's composing boundary guards
        covers it: pre-fix, ``throw(0 - 5)`` into an ``Exn<{ @Int | @Int.0 >
        0 }>`` ran to completion and handed ``-5`` to a clause that had
        assumed the predicate.  This is that boundary's own guard — save the
        value, test the predicate over it, push it back — so it traps through
        the same ``$vera.contract_fail`` channel a refined parameter does.

        Emitted UNGATED for every refined payload, matching the closure
        return guard rather than the sign guards' narrowing test: a value
        already typed at the refinement satisfies its own predicate, so the
        guard costs a dead check at worst, while a missing one is a false
        ``guarded`` claim in the obligation stream.  The verifier's mirror is
        ``_refined_boundary_codegen_guardable``, which downgrades exactly the
        shapes the emitter answers ``None`` for (an erased ``@Unit`` base, a
        nested refinement), so obligation and guard stay in lock-step.

        Called only with the *payload_te* :meth:`_refined_exn_payload_type`
        returned, which is the same expression ``cell.type_expr`` holds.
        """
        emitter = self._refinement_guard_emitter
        if emitter is None:
            raise CodegenSkip(  # pragma: no cover — defensive
                call,
                "no refinement-guard emitter is installed on this "
                f"translation context, so the refined Exn<{cell.family}> "
                "payload cannot be guarded at the throw",
            )
        # The payload's SOURCE spelling, not `cell.family`: a refined
        # family renders its own predicate (#1218), so naming the cell that
        # way printed the predicate twice in one two-line message, once as
        # the "type" and again as the thing that failed.
        head = (
            f"Refinement violation in "
            f"throw({ast.format_type_expr(payload_te)})\n"
            "  payload"
        )
        if self._is_pair_type_name(cell.base):
            # A `String`-based payload is (ptr, len) in two CONSECUTIVE
            # locals, checked over the ptr — the same shape the lifted
            # closure's i32_pair return guard uses.
            ptr_local = self.alloc_local("i32")
            len_local = self.alloc_local("i32")
            guard = emitter(payload_te, ptr_local, head, env)
            if guard is None:
                return value
            return [
                *value,
                f"local.set {len_local}",
                f"local.set {ptr_local}",
                *guard,
                f"local.get {ptr_local}",
                f"local.get {len_local}",
            ]
        value_local = self.alloc_local(self._type_name_to_wasm(cell.base))
        guard = emitter(payload_te, value_local, head, env)
        if guard is None:
            return value
        return [
            *value,
            f"local.set {value_local}",
            *guard,
            f"local.get {value_local}",
        ]

    def _translate_handle_exn(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate handle[Exn<E>] { throw(@E) -> handler } in { body }.

        Uses WASM exception handling (try_table/catch/throw):
          block $done (result T)
            block $catch (result E)
              try_table (result T) (catch $exn_E $catch)
                <body>
              end
              br $done
            end
            ;; caught value on stack
            local.set $thrown
            <handler clause body>
          end
        """
        assert isinstance(expr.effect, ast.EffectRef)  # noqa: S101
        type_arg = expr.effect.type_args[0]  # type: ignore[index]
        if not isinstance(type_arg, ast.NamedType):
            raise CodegenSkip(
                expr, "Exn<E> type argument must be a named type"
            )
        # #914: use the FULL canonical slot name (`Option<Int>`, not `Option`)
        # so the caught-payload slot env binds under the same key a
        # `@Option<Int>.n` ref in the handler body resolves against (root
        # cause C — pre-fix the push used the base name and the ref dangled,
        # E699).  The tag identifier is escaped via `mangle_type_name` (#775)
        # so a composite E yields a legal WAT tag name (root cause B3).
        type_name = type_expr_slot_name(type_arg)  # FAMILY question, see above
        if type_name is None:  # pragma: no cover — NamedType always resolves
            raise CodegenSkip(
                expr, "Exn<E> type argument has no slot name"
            )
        # Tag family, pair-ness, and payload WT derive from the RESOLVED
        # family (matching `_check_exn_type` registration) — `Exn<Code>`
        # with `type Code = Int` otherwise binds an i32 payload local
        # against the i64-tagged throw (#1205), and `Exn<Msg>` with
        # `type Msg = String` otherwise declares a second one-i32 tag
        # beside the `String` pair tag its throw sites use (#1209).  The
        # caught-value SLOT binding below stays source-level (the checker
        # binds the clause pattern's own name).
        family = self._family_name(type_arg)
        family_base = self._boundary_base(type_arg)
        tag_name = f"$exn_{mangle_type_name(family)}"
        # Pair-ness is the BASE's question (#1218): `Exn<Short>` under
        # `type Short = {@String | ...}` is its own tag and still carries a
        # (ptr, len) pair, so asking the identity name — which carries the
        # predicate and matches no representation the name table knows —
        # would bind a single i32 against a two-i32 tag.
        is_pair = self._is_pair_type_name(family_base)

        # Unique label ids for nested handlers
        hid = self._next_handle_id
        self._next_handle_id += 1
        done_label = f"$hd_{hid}"
        catch_label = f"$hc_{hid}"

        # Infer result type: try handler clause first (body may always
        # throw, making its inferred type None), then fall back to body.
        # Use `_infer_expr_wasm_type` rather than `_infer_block_result_type`
        # so expression-bodied handler clauses (e.g. `throw(@String) -> None`,
        # `throw(@Int) -> @Int.0 + 1`, etc.) are inferred correctly — pre-fix
        # only `ast.Block` clause bodies got their result type inferred,
        # leaving `result_wt = None` for any expression-bodied handler and
        # omitting the `(result ...)` annotation in emitted WAT.  #475 (1).
        # `expr.body` is statically typed `Block` (ast.py:481), so passing
        # it to `_infer_expr_wasm_type` produces the same answer as the
        # Block-specific helper would — using one helper for both call
        # sites is uniformity for free.
        result_wt = None
        if expr.clauses:
            result_wt = self._infer_expr_wasm_type(expr.clauses[0].body)
        if result_wt is None:
            result_wt = self._infer_expr_wasm_type(expr.body)

        # #1276: `result_wt is None` means one of TWO things, and the two want
        # opposite lowerings.  **Unit** — the handler completes carrying no
        # value, and a result-less `block` is exactly right.  **Divergence** —
        # every path out of the clause AND out of the handled body is a
        # `throw`, so the block never completes at all; a result-less block
        # then lands in a context expecting a value and the module is rejected
        # at load (`expected i64 but nothing on stack`) from check-green,
        # verify-green source.  Distinguishing them is the whole fix: the
        # divergent shape keeps its result-less block (it truly leaves nothing)
        # and gains an `unreachable` terminator, which makes the stack
        # polymorphic for whatever the context wanted.  The instruction is
        # emitted where control provably never arrives, so it cannot trap a
        # program that runs.
        diverges = result_wt is None and self._handle_exn_always_throws(expr)

        # Save/inject throw as an effect op for the body
        # Saved by reference, replaced with a fresh copy, restored in a
        # `finally` — the same discipline as the State twin: the body
        # translation raises `CodegenSkip` for any unsupported shape, and an
        # in-place `self._effect_ops["throw"] = …` would leave that entry in
        # a dict an enclosing scope still holds.
        #
        # The cell rides in lock-step (#1218's discipline, #1269's need): a
        # `throw` written INSIDE the handled body takes its dispatch target
        # from HERE rather than from the enclosing declaration's effect row,
        # so the payload's REPRESENTATION has to arrive by the same route
        # or the write boundary at the call site has nothing to ask.
        saved_ops = self._effect_ops
        saved_cells = self._effect_op_cells
        self._effect_ops = {**saved_ops, "throw": (tag_name, False)}
        self._effect_op_cells = {
            **saved_cells,
            # `type_arg` rides along for the same reason the two names do
            # (#1268): a `throw` in this body guards a refined payload by
            # lowering the predicate, which only the type expression carries.
            "throw": CellNames(
                family=family, base=family_base, type_expr=type_arg,
            ),
        }

        # Compile body
        try:
            body_instrs = self.translate_block(expr.body, env)
            # Record this handle expression's stack shape HERE, while
            # the handler's effect-op registries are still installed
            # (#1371).  A `handle`'s value is its body's, and the body's
            # ops resolve through registries the `finally` below
            # restores — so asked afterwards, from the scoping wrapper,
            # a nested handler's `get` answers with the ENCLOSING
            # handler's result width.
            self._scoped_expr_shape[id(expr)] = (
                self._compute_stack_shape(expr))
        finally:
            # Restore effect_ops
            self._effect_ops = saved_ops
            self._effect_op_cells = saved_cells

        if body_instrs is None:
            return None

        # Compile handler clause body
        if not expr.clauses:
            raise CodegenSkip(
                expr, "handle[Exn<E>] requires at least one clause"
            )
        clause = expr.clauses[0]  # Exn<E> has exactly one op: throw

        # Allocate locals for the caught exception value.
        # Pair types (String, Array<T>) use two consecutive i32 locals
        # (ptr at thrown_local, len at thrown_local + 1) matching the
        # convention used by _translate_slot_ref for pair types.
        if is_pair:
            thrown_local = self.alloc_local("i32")  # ptr
            _len_local = self.alloc_local("i32")    # len (consecutive: thrown_local + 1)
        else:
            thrown_wt = self._type_name_to_wasm(family_base)
            thrown_local = self.alloc_local(thrown_wt)

        # Push caught value into slot env for handler body, under the
        # clause PATTERN's own slot name in the checker's canonical form
        # (top name syntactic, arguments resolved — `throw(@Code)` binds
        # `@Code` whatever `E` was named).
        if clause.params:
            # #1208: no `or type_name` fallback — see the State twin.
            caught_slot = self._type_expr_to_slot_name(clause.params[0])
            if caught_slot is None:  # pragma: no cover — defensive
                raise CodegenSkip(
                    clause.params[0],
                    "handler clause parameter has no slot name",
                )
            handler_env = env.push(caught_slot, thrown_local)
        else:
            # A patternless `throw()` clause binds nothing in the checker
            # (its zip has no param to bind) — pushing the payload anyway
            # skewed the clause body's same-typed references onto it (PR
            # #1202 adversarial round, F2).
            handler_env = env
        handler_instrs = self.translate_expr(clause.body, handler_env)
        if handler_instrs is None:
            return None  # pragma: no cover

        # Assemble the try_table structure.
        # i32_pair (String, Array<T>) must expand to "i32 i32" in WAT result
        # annotations; "i32_pair" is an internal representation, not valid WAT.
        if result_wt == "i32_pair":
            result_spec = " (result i32 i32)"
        elif result_wt:
            result_spec = f" (result {result_wt})"
        else:
            # Unit, or (#1276) a handler no path completes — both leave the
            # block result-less; only the second gets the `unreachable` tail.
            result_spec = ""
        if is_pair:
            thrown_spec = " (result i32 i32)"
        else:
            thrown_spec = f" (result {thrown_wt})" if thrown_wt else ""

        instructions: list[str] = []
        instructions.append(f"block {done_label}{result_spec}")
        instructions.append(f"  block {catch_label}{thrown_spec}")
        instructions.append(
            f"    try_table{result_spec}"
            f" (catch {tag_name} {catch_label})"
        )
        instructions.extend(f"      {i}" for i in body_instrs)
        instructions.append("    end")
        instructions.append(f"    br {done_label}")
        instructions.append("  end")
        # Caught value(s) are on the stack — store into local(s).
        # Pair types: catch pushes (ptr, len); set len first (LIFO), then ptr.
        if is_pair:
            instructions.append(f"  local.set {_len_local}")
            instructions.append(f"  local.set {thrown_local}")
        else:
            instructions.append(f"  local.set {thrown_local}")
        instructions.extend(f"  {i}" for i in handler_instrs)
        instructions.append("end")
        if diverges:  # #1276 — see the `diverges` derivation above
            instructions.append("unreachable")

        return instructions

    def _handle_exn_always_throws(self, expr: ast.HandleExpr) -> bool:
        """Does EVERY path out of this ``handle[Exn]`` end in a ``throw`` (#1276)?

        True exactly when the handled body diverges (so the handler is entered
        or the throw escapes) and every clause body diverges too (so being
        entered does not help).  Both halves are required: a completing clause
        is the ordinary shape, and its inferred type is the block's result.

        Deliberately conservative — an unrecognized shape answers ``False`` and
        keeps the pre-existing lowering — because the answer authorizes an
        ``unreachable``, and a wrong ``True`` would trap a program that runs.

        A non-``Exn`` handler is one such shape, and it arrives here:
        ``_expr_always_throws`` routes EVERY nested ``HandleExpr`` to this
        method, so a ``handle[State<T>]`` was analysed as an Exn one and its
        body evaluated with ``throw_installed=True`` — a claim that a bare
        ``throw`` there IS this handler's operation, which a handler
        installing ``get``/``put`` does not make true.  Nothing reached a
        wrong ``True`` (a lowerable State clause body carries a tail
        ``resume(...)``, for which ``_expr_always_throws`` is ``False``, so
        the ``all(...)`` leg failed first), but that rested on the
        clause-lowering shape rule rather than on this predicate.  Asking the
        question the method's name asks puts the stated invariant back
        (PR #1283 review).
        """
        if (not isinstance(expr.effect, ast.EffectRef)
                or expr.effect.name != "Exn"):
            return False
        return bool(expr.clauses) and self._expr_always_throws(
            expr.body, throw_installed=True,
        ) and all(
            # A clause body is translated with the ENCLOSING scope's ops
            # restored (this handler's `throw` is injected over the handled
            # body only), so a `throw` there denotes an outer handler's op or
            # the declaration's own effect row — which is what makes the
            # rethrow shape divergent rather than a call to some `throw`.
            self._expr_always_throws(
                clause.body,
                throw_installed=(self._bare_call_denotes_op("throw")
                                 and "throw" in self._effect_ops),
            )
            for clause in expr.clauses
        )

    def _expr_always_throws(
        self, expr: ast.Expr, *, throw_installed: bool,
    ) -> bool:
        """Does every path through *expr* leave via a ``throw`` (#1276)?

        The narrow structural cases that can carry a divergent tail: a block
        (its trailing expression), both arms of an ``if``, every arm of a
        ``match``, a nested ``handle[Exn]`` that itself always throws, and the
        ``throw`` call at the leaf.  Everything else answers ``False``.

        ``throw_installed`` says whether a bare ``throw`` at this point IS the
        effect operation.  Inside a ``handle[Exn<E>]``'s handled body it always
        is — the injection at the translation site is unconditional — while
        elsewhere the enclosing ``_effect_ops`` decides, filtered by the
        bare-call ownership predicate (#1284) exactly as the lowering filters
        it, so a program that declares its own ``fn throw`` is read the same
        way the lowering reads it.
        """
        if isinstance(expr, ast.Block):
            return self._expr_always_throws(
                expr.expr, throw_installed=throw_installed,
            )
        if isinstance(expr, ast.IfExpr):
            return self._expr_always_throws(
                expr.then_branch, throw_installed=throw_installed,
            ) and self._expr_always_throws(
                expr.else_branch, throw_installed=throw_installed,
            )
        if isinstance(expr, ast.MatchExpr):
            return bool(expr.arms) and all(
                self._expr_always_throws(
                    arm.body, throw_installed=throw_installed,
                )
                for arm in expr.arms
            )
        if isinstance(expr, ast.HandleExpr):
            return self._handle_exn_always_throws(expr)
        if isinstance(expr, ast.FnCall):
            return expr.name == "throw" and throw_installed
        if isinstance(expr, ast.QualifiedCall):
            # The `Exn.throw(v)` spelling delegates to the bare dispatcher
            # (#1269), so it diverges under the same condition.
            return (
                expr.qualifier == "Exn" and expr.name == "throw"
                and throw_installed
            )
        return False
