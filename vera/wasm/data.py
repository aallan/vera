"""Constructor, match, and array translation mixin for WasmContext."""

from __future__ import annotations

from typing import TYPE_CHECKING

from vera import ast
from vera.wasm.helpers import (
    WasmSlotEnv,
    _element_mem_size,
    _element_load_op,
    _element_store_op,
    _is_pair_element_type,
    gc_shadow_push,
)

if TYPE_CHECKING:
    from vera.codegen import ConstructorLayout


class DataMixin:
    """Methods for translating constructors, match expressions, and arrays."""

    # -----------------------------------------------------------------
    # Constructors
    # -----------------------------------------------------------------

    def _translate_nullary_constructor(
        self, expr: ast.NullaryConstructor
    ) -> list[str] | None:
        """Translate a nullary constructor (e.g., None, Red) to WAT.

        Emits: alloc → store tag → return pointer.
        """
        layout = self._ctor_layouts.get(expr.name)
        if layout is None:
            return None

        self.needs_alloc = True
        tmp = self.alloc_local("i32")
        return [
            f"i32.const {layout.total_size}",
            "call $alloc",
            f"local.tee {tmp}",
            f"i32.const {layout.tag}",
            "i32.store",
            *gc_shadow_push(tmp),
            f"local.get {tmp}",
        ]

    def _translate_constructor_call(
        self, expr: ast.ConstructorCall, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a constructor call (e.g., Some(42)) to WAT.

        Emits: alloc → store tag → store each field → return pointer.
        Field offsets are computed from the concrete argument types so that
        generic constructors (e.g. Some(T) instantiated as Some(Int))
        use the correct WASM types and alignment.
        """
        layout = self._ctor_layouts.get(expr.name)
        if layout is None:
            return None

        # Translate all arguments and infer their concrete WASM types
        arg_instrs_list: list[list[str]] = []
        arg_wasm_types: list[str] = []
        for arg in expr.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            arg_wt = self._infer_expr_wasm_type(arg)
            if arg_wt is None:
                return None
            arg_instrs_list.append(arg_instrs)
            arg_wasm_types.append(arg_wt)

        # Compute field offsets from concrete argument types
        _sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8}
        _aligns = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4}
        offset = 4  # after tag (i32, 4 bytes)
        field_offsets: list[tuple[int, str]] = []
        for wt in arg_wasm_types:
            align = _aligns.get(wt, 8)
            offset = (offset + align - 1) & ~(align - 1)  # align up
            field_offsets.append((offset, wt))
            offset += _sizes.get(wt, 8)
        total_size = ((offset + 7) & ~7) if offset > 0 else 8  # 8-byte aligned

        self.needs_alloc = True
        tmp = self.alloc_local("i32")
        instructions: list[str] = [
            f"i32.const {total_size}",
            "call $alloc",
            f"local.tee {tmp}",
            f"i32.const {layout.tag}",
            "i32.store",
            *gc_shadow_push(tmp),
        ]

        # Store each field at its computed offset
        for i, (fo, wt) in enumerate(field_offsets):
            if wt == "i32_pair":
                # Pair type (String, Array<T>): store (ptr, len) as two i32s
                tmp_val_ptr = self.alloc_local("i32")
                tmp_val_len = self.alloc_local("i32")
                instructions.extend(arg_instrs_list[i])
                instructions.append(f"local.set {tmp_val_len}")
                instructions.append(f"local.set {tmp_val_ptr}")
                instructions.append(f"local.get {tmp}")
                instructions.append(f"local.get {tmp_val_ptr}")
                instructions.append(f"i32.store offset={fo}")
                instructions.append(f"local.get {tmp}")
                instructions.append(f"local.get {tmp_val_len}")
                instructions.append(f"i32.store offset={fo + 4}")
            else:
                instructions.append(f"local.get {tmp}")
                instructions.extend(arg_instrs_list[i])
                instructions.append(f"{wt}.store offset={fo}")

        # Leave pointer as result
        instructions.append(f"local.get {tmp}")
        return instructions

    # -----------------------------------------------------------------
    # Match expressions
    # -----------------------------------------------------------------

    def _translate_match(
        self, expr: ast.MatchExpr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a match expression to WAT.

        Evaluates the scrutinee once, saves to a local, then emits a
        chained if-else cascade for each arm.
        """
        # Translate scrutinee
        scr_instrs = self.translate_expr(expr.scrutinee, env)
        if scr_instrs is None:
            return None

        scr_wasm_type = self._infer_expr_wasm_type(expr.scrutinee)
        if scr_wasm_type is None:
            return None

        # Save scrutinee to a local
        scr_local = self.alloc_local(scr_wasm_type)
        instructions: list[str] = list(scr_instrs)
        instructions.append(f"local.set {scr_local}")

        # Infer result type of the match
        result_type = self._infer_match_result_type(expr)

        # Compile arms as chained if-else
        arm_instrs = self._compile_match_arms(
            expr.arms, scr_local, scr_wasm_type, result_type, env
        )
        if arm_instrs is None:
            return None

        instructions.extend(arm_instrs)
        return instructions

    def _infer_match_result_type(
        self, expr: ast.MatchExpr
    ) -> str | None:
        """Infer the WASM result type from the first arm body."""
        for arm in expr.arms:
            wt = self._infer_expr_wasm_type(arm.body)
            if wt is not None:
                return wt
        return None

    def _compile_match_arms(
        self,
        arms: tuple[ast.MatchArm, ...],
        scr_local: int,
        scr_wasm_type: str,
        result_type: str | None,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """Compile match arms as a chained if-else cascade."""
        if not arms:
            return None

        arm = arms[0]
        remaining = arms[1:]

        # Check if this arm needs a condition
        cond = self._translate_match_condition(
            arm.pattern, scr_local, scr_wasm_type
        )

        if cond is None or not remaining:
            # Unconditional arm (catch-all) or last arm — emit directly
            setup = self._setup_match_arm_env(
                arm.pattern, scr_local, scr_wasm_type, env
            )
            if setup is None:
                return None
            setup_instrs, arm_env = setup
            body = self.translate_expr(arm.body, arm_env)
            if body is None:
                return None
            return setup_instrs + body

        # Conditional arm with more arms following
        setup = self._setup_match_arm_env(
            arm.pattern, scr_local, scr_wasm_type, env
        )
        if setup is None:
            return None
        setup_instrs, arm_env = setup
        body = self.translate_expr(arm.body, arm_env)
        if body is None:
            return None

        # Compile remaining arms (else branch)
        else_instrs = self._compile_match_arms(
            remaining, scr_local, scr_wasm_type, result_type, env
        )
        if else_instrs is None:
            return None

        # Build if-else block
        if result_type == "i32_pair":
            result_annot = " (result i32 i32)"
        elif result_type:
            result_annot = f" (result {result_type})"
        else:
            result_annot = ""
        instrs: list[str] = list(cond)
        instrs.append(f"if{result_annot}")
        for i in setup_instrs:
            instrs.append(f"  {i}")
        for i in body:
            instrs.append(f"  {i}")
        instrs.append("else")
        for i in else_instrs:
            instrs.append(f"  {i}")
        instrs.append("end")
        return instrs

    def _translate_match_condition(
        self,
        pattern: ast.Pattern,
        scr_local: int,
        scr_wasm_type: str,
    ) -> list[str] | None:
        """Emit i32 condition for a pattern check.

        Returns None for unconditional patterns (wildcard/binding).
        """
        if isinstance(pattern, (ast.NullaryPattern, ast.ConstructorPattern)):
            name = pattern.name
            layout = self._ctor_layouts.get(name)
            if layout is None:
                return None
            instrs = [
                f"local.get {scr_local}",
                "i32.load",
                f"i32.const {layout.tag}",
                "i32.eq",
            ]
            # AND-chain nested tag checks for constructor sub-patterns
            if isinstance(pattern, ast.ConstructorPattern):
                nested = self._collect_nested_tag_checks(
                    pattern, scr_local, layout,
                )
                if nested is None:
                    return None
                for check in nested:
                    instrs.extend(check)
                    instrs.append("i32.and")
            return instrs

        if isinstance(pattern, ast.BoolPattern):
            if pattern.value:
                return [f"local.get {scr_local}"]
            else:
                return [f"local.get {scr_local}", "i32.eqz"]

        if isinstance(pattern, ast.IntPattern):
            return [
                f"local.get {scr_local}",
                f"i64.const {pattern.value}",
                "i64.eq",
            ]

        # WildcardPattern, BindingPattern — unconditional
        return None

    def _setup_match_arm_env(
        self,
        pattern: ast.Pattern,
        scr_local: int,
        scr_wasm_type: str,
        env: WasmSlotEnv,
    ) -> tuple[list[str], WasmSlotEnv] | None:
        """Extract fields and set up environment bindings for a match arm.

        Returns (instructions, new_env) or None on failure.
        """
        if isinstance(pattern, (ast.WildcardPattern, ast.NullaryPattern,
                                ast.BoolPattern, ast.IntPattern)):
            return ([], env)

        if isinstance(pattern, ast.BindingPattern):
            # Bind the scrutinee itself to a new local
            type_name = self._type_expr_to_slot_name(pattern.type_expr)
            if type_name is None:
                return None
            local_idx = self.alloc_local(scr_wasm_type)
            instrs = [
                f"local.get {scr_local}",
                f"local.set {local_idx}",
            ]
            new_env = env.push(type_name, local_idx)
            return (instrs, new_env)

        if isinstance(pattern, ast.ConstructorPattern):
            layout = self._ctor_layouts.get(pattern.name)
            if layout is None:
                return None
            return self._extract_constructor_fields(
                pattern, scr_local, layout, env
            )

        return None

    def _extract_constructor_fields(
        self,
        pattern: ast.ConstructorPattern,
        scr_local: int,
        layout: ConstructorLayout,
        env: WasmSlotEnv,
    ) -> tuple[list[str], WasmSlotEnv] | None:
        """Extract fields from a constructor match into locals.

        Computes field offsets from concrete binding types (same
        monomorphization approach as _translate_constructor_call).
        """
        _sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8}
        _aligns = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4}
        offset = 4  # after tag (i32, 4 bytes)
        instrs: list[str] = []
        new_env = env

        for i, sub_pat in enumerate(pattern.sub_patterns):
            if isinstance(sub_pat, ast.BindingPattern):
                # Resolve concrete WASM type from the binding's type_expr
                type_name = self._type_expr_to_slot_name(sub_pat.type_expr)
                if type_name is None:
                    return None
                # Unit bindings: no WASM representation, skip extraction
                if type_name == "Unit":
                    continue
                # Pair types (String, Array<T>): two consecutive i32 locals
                if self._is_pair_type_name(type_name):
                    align = _aligns.get("i32", 4)
                    offset = (offset + align - 1) & ~(align - 1)
                    ptr_local = self.alloc_local("i32")
                    len_local = self.alloc_local("i32")
                    instrs.append(f"local.get {scr_local}")
                    instrs.append(f"i32.load offset={offset}")
                    instrs.append(f"local.set {ptr_local}")
                    instrs.append(f"local.get {scr_local}")
                    instrs.append(f"i32.load offset={offset + 4}")
                    instrs.append(f"local.set {len_local}")
                    new_env = new_env.push(type_name, ptr_local)
                    offset += 8  # two i32s
                    continue
                wt = self._slot_name_to_wasm_type(type_name)
                if wt is None:
                    return None
                # Compute aligned offset for this field
                align = _aligns.get(wt, 8)
                offset = (offset + align - 1) & ~(align - 1)
                # Load field from scrutinee pointer
                local_idx = self.alloc_local(wt)
                instrs.append(f"local.get {scr_local}")
                instrs.append(f"{wt}.load offset={offset}")
                instrs.append(f"local.set {local_idx}")
                new_env = new_env.push(type_name, local_idx)
                offset += _sizes.get(wt, 8)

            elif isinstance(sub_pat, ast.WildcardPattern):
                # Skip this field but advance offset using layout's type
                if i < len(layout.field_offsets):
                    _, generic_wt = layout.field_offsets[i]
                    align = _aligns.get(generic_wt, 8)
                    offset = (offset + align - 1) & ~(align - 1)
                    offset += _sizes.get(generic_wt, 8)

            elif isinstance(sub_pat, ast.ConstructorPattern):
                # Nested constructor: load the field pointer (i32),
                # look up its layout, and recurse to extract its fields.
                align = _aligns.get("i32", 4)
                offset = (offset + align - 1) & ~(align - 1)
                sub_layout = self._ctor_layouts.get(sub_pat.name)
                if sub_layout is None:
                    return None
                sub_local = self.alloc_local("i32")
                instrs.append(f"local.get {scr_local}")
                instrs.append(f"i32.load offset={offset}")
                instrs.append(f"local.set {sub_local}")
                # Recurse into the nested constructor's sub-patterns
                nested = self._extract_constructor_fields(
                    sub_pat, sub_local, sub_layout, new_env,
                )
                if nested is None:
                    return None
                nested_instrs, new_env = nested
                instrs.extend(nested_instrs)
                offset += _sizes.get("i32", 4)

            elif isinstance(sub_pat, ast.NullaryPattern):
                # Nullary: tag was already checked in the condition phase.
                # Just advance offset by i32 size (ADT pointer).
                align = _aligns.get("i32", 4)
                offset = (offset + align - 1) & ~(align - 1)
                offset += _sizes.get("i32", 4)

            else:
                # Unknown sub-pattern type
                return None

        return (instrs, new_env)

    # -----------------------------------------------------------------
    # Nested pattern helpers
    # -----------------------------------------------------------------

    def _sub_pattern_wasm_type(
        self,
        sub_pat: ast.Pattern,
        field_index: int,
        layout: ConstructorLayout,
    ) -> str | None:
        """Return the WASM type for a sub-pattern's field.

        Used for offset computation when walking nested patterns.
        """
        if isinstance(sub_pat, ast.BindingPattern):
            type_name = self._type_expr_to_slot_name(sub_pat.type_expr)
            if type_name is None:
                return None
            # Unit bindings: no WASM representation — use generic layout type
            if type_name == "Unit":
                if field_index < len(layout.field_offsets):
                    _, generic_wt = layout.field_offsets[field_index]
                    return generic_wt
                return "i32"  # safe default
            # Pair types (String, Array<T>) use i32_pair representation
            if self._is_pair_type_name(type_name):
                return "i32_pair"
            return self._slot_name_to_wasm_type(type_name)
        if isinstance(sub_pat, ast.WildcardPattern):
            if field_index < len(layout.field_offsets):
                _, generic_wt = layout.field_offsets[field_index]
                return generic_wt
            return None
        if isinstance(sub_pat, (ast.ConstructorPattern, ast.NullaryPattern)):
            return "i32"  # ADT = heap pointer
        return None

    def _collect_nested_tag_checks(
        self,
        pattern: ast.ConstructorPattern,
        scr_local: int,
        layout: ConstructorLayout,
    ) -> list[list[str]] | None:
        """Collect tag checks for nested constructor/nullary sub-patterns.

        Walks *pattern.sub_patterns* and for each that is a
        ``ConstructorPattern`` or ``NullaryPattern``, emits a sequence of
        WASM instructions that (a) loads the field pointer from the parent,
        (b) loads the tag from that pointer, (c) compares to the expected
        tag.  For ``ConstructorPattern`` it recurses to collect deeper
        checks.

        Returns a list of instruction-lists, each producing an ``i32``
        boolean on the stack.  Returns ``None`` on layout lookup failure.
        """
        _sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8}
        _aligns = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4}
        offset = 4  # after tag

        checks: list[list[str]] = []

        for i, sub_pat in enumerate(pattern.sub_patterns):
            wt = self._sub_pattern_wasm_type(sub_pat, i, layout)
            if wt is None:
                return None
            align = _aligns.get(wt, 8)
            offset = (offset + align - 1) & ~(align - 1)

            if isinstance(sub_pat, (ast.ConstructorPattern, ast.NullaryPattern)):
                name = sub_pat.name
                sub_layout = self._ctor_layouts.get(name)
                if sub_layout is None:
                    return None
                # Load the nested ADT pointer, stash in a temp,
                # then load the tag and compare.
                tmp = self.alloc_local("i32")
                check: list[str] = [
                    f"local.get {scr_local}",
                    f"i32.load offset={offset}",
                    f"local.tee {tmp}",
                    "i32.load",
                    f"i32.const {sub_layout.tag}",
                    "i32.eq",
                ]
                checks.append(check)

                # Recurse for deeper nesting
                if isinstance(sub_pat, ast.ConstructorPattern):
                    deeper = self._collect_nested_tag_checks(
                        sub_pat, tmp, sub_layout,
                    )
                    if deeper is None:
                        return None
                    checks.extend(deeper)

            offset += _sizes.get(wt, 8)

        return checks

    # -----------------------------------------------------------------
    # Array literals
    # -----------------------------------------------------------------

    def _translate_array_lit(
        self, expr: ast.ArrayLit, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate an array literal to (ptr, len) on the stack.

        Allocates heap memory via $alloc, stores each element, then
        pushes (ptr, len) as an i32 pair.  Empty arrays push (0, 0).
        """
        n = len(expr.elements)
        if n == 0:
            return ["i32.const 0", "i32.const 0"]

        elem_type = self._infer_array_element_type(expr)
        if elem_type is None:
            return None
        elem_size = _element_mem_size(elem_type)
        if elem_size is None:
            return None
        is_pair = _is_pair_element_type(elem_type)
        store_op = _element_store_op(elem_type)
        # store_op is None only for pair types — handled below
        if store_op is None and not is_pair:
            return None

        self.needs_alloc = True
        total_bytes = n * elem_size
        tmp_ptr = self.alloc_local("i32")

        instructions: list[str] = []
        # Allocate
        instructions.append(f"i32.const {total_bytes}")
        instructions.append("call $alloc")
        instructions.append(f"local.set {tmp_ptr}")
        instructions.extend(gc_shadow_push(tmp_ptr))

        # Store each element
        for i, elem in enumerate(expr.elements):
            elem_instrs = self.translate_expr(elem, env)
            if elem_instrs is None:
                return None
            offset = i * elem_size
            if is_pair:
                # Pair type (String, Array<T>): element pushes (ptr, len)
                # Store into two consecutive i32 slots
                tmp_val_ptr = self.alloc_local("i32")
                tmp_val_len = self.alloc_local("i32")
                instructions.extend(elem_instrs)
                instructions.append(f"local.set {tmp_val_len}")
                instructions.append(f"local.set {tmp_val_ptr}")
                # Store ptr at offset
                instructions.append(f"local.get {tmp_ptr}")
                instructions.append(f"local.get {tmp_val_ptr}")
                instructions.append(f"i32.store offset={offset}")
                # Store len at offset+4
                instructions.append(f"local.get {tmp_ptr}")
                instructions.append(f"local.get {tmp_val_len}")
                instructions.append(f"i32.store offset={offset + 4}")
            else:
                instructions.append(f"local.get {tmp_ptr}")
                instructions.extend(elem_instrs)
                instructions.append(f"{store_op} offset={offset}")

        # Push (ptr, len)
        instructions.append(f"local.get {tmp_ptr}")
        instructions.append(f"i32.const {n}")
        return instructions

    def _translate_index_expr(
        self, expr: ast.IndexExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate array indexing with bounds check.

        Evaluates collection → (ptr, len), evaluates index,
        performs bounds check (trap on OOB), then loads the element.
        """
        elem_type = self._infer_index_element_type(expr)
        if elem_type is None:
            return None
        elem_size = _element_mem_size(elem_type)
        if elem_size is None:
            return None
        is_pair = _is_pair_element_type(elem_type)
        load_op = _element_load_op(elem_type)
        # load_op is None only for pair types — handled below
        if load_op is None and not is_pair:
            return None

        # Evaluate collection → (ptr, len) on stack
        coll_instrs = self.translate_expr(expr.collection, env)
        if coll_instrs is None:
            return None

        # Evaluate index (Int → i64)
        idx_instrs = self.translate_expr(expr.index, env)
        if idx_instrs is None:
            return None

        # Temp locals for ptr, len, index
        tmp_ptr = self.alloc_local("i32")
        tmp_len = self.alloc_local("i32")
        tmp_idx = self.alloc_local("i32")

        instructions: list[str] = []
        # Save (ptr, len)
        instructions.extend(coll_instrs)
        instructions.append(f"local.set {tmp_len}")
        instructions.append(f"local.set {tmp_ptr}")
        # Evaluate and wrap index from i64 to i32
        instructions.extend(idx_instrs)
        instructions.append("i32.wrap_i64")
        instructions.append(f"local.set {tmp_idx}")
        # Bounds check: if (u32)idx >= (u32)len then trap
        instructions.append(f"local.get {tmp_idx}")
        instructions.append(f"local.get {tmp_len}")
        instructions.append("i32.ge_u")
        instructions.append("if")
        instructions.append("  unreachable")
        instructions.append("end")
        # Compute address: ptr + idx * elem_size
        instructions.append(f"local.get {tmp_ptr}")
        if elem_size == 1:
            instructions.append(f"local.get {tmp_idx}")
            instructions.append("i32.add")
        else:
            instructions.append(f"local.get {tmp_idx}")
            instructions.append(f"i32.const {elem_size}")
            instructions.append("i32.mul")
            instructions.append("i32.add")
        # Load element
        if is_pair:
            # Pair type (String, Array<T>): load (ptr, len) from two
            # consecutive i32 slots.  Save computed address first.
            tmp_addr = self.alloc_local("i32")
            instructions.append(f"local.set {tmp_addr}")
            instructions.append(f"local.get {tmp_addr}")
            instructions.append("i32.load offset=0")
            instructions.append(f"local.get {tmp_addr}")
            instructions.append("i32.load offset=4")
        else:
            instructions.append(load_op)  # type: ignore[arg-type]
        return instructions
