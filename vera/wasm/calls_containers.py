"""Container type translation mixin for WasmContext.

Handles the three opaque-handle types: Map<K,V>, Set<E>, and Decimal.
All three use the host-import pattern with lazy registration of
type-specialised imports (e.g. ``map_insert$ks_vi`` for String key /
Int value).
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class CallsContainersMixin:
    """Methods for translating Map, Set, and Decimal built-in functions."""

    # -----------------------------------------------------------------
    # Decimal built-in operations (§9.7.2)
    # -----------------------------------------------------------------

    def _register_decimal_import(
        self, op: str, params: list[str], results: list[str],
    ) -> str:
        """Register a Decimal host import and return the WASM call name."""
        wasm_name = f"$vera.{op}"
        param_str = " ".join(f"(param {p})" for p in params)
        result_str = " ".join(f"(result {r})" for r in results)
        sig = f"(func {wasm_name} {param_str} {result_str})"
        self._decimal_imports.add(f'  (import "vera" "{op}" {sig})')
        self._decimal_ops_used.add(op)
        return wasm_name

    def _translate_decimal_unary(
        self, call: "ast.FnCall", env: WasmSlotEnv,
        op: str, param_type: str, result_type: str,
    ) -> list[str] | None:
        """Translate a unary Decimal operation (one param, one result)."""
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            op, [param_type], [result_type])
        return arg_instrs + [f"call {wasm_name}"]

    def _translate_decimal_binary(
        self, call: "ast.FnCall", env: WasmSlotEnv,
        op: str,
    ) -> list[str] | None:
        """Translate a binary Decimal operation (two handles → handle)."""
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            op, ["i32", "i32"], ["i32"])
        return a_instrs + b_instrs + [f"call {wasm_name}"]

    def _translate_decimal_from_string(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_from_string(s) → Option<Decimal> (i32 heap ptr)."""
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_from_string", ["i32", "i32"], ["i32"])
        self.needs_alloc = True
        return arg_instrs + [f"call {wasm_name}"]

    def _translate_decimal_to_string(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_to_string(d) → String (i32_pair)."""
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_to_string", ["i32"], ["i32", "i32"])
        self.needs_alloc = True
        return arg_instrs + [f"call {wasm_name}"]

    def _translate_decimal_div(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_div(a, b) → Option<Decimal> (i32 heap ptr)."""
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_div", ["i32", "i32"], ["i32"])
        self.needs_alloc = True
        return a_instrs + b_instrs + [f"call {wasm_name}"]

    def _translate_decimal_compare(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_compare(a, b) → Ordering (i32 heap ptr)."""
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_compare", ["i32", "i32"], ["i32"])
        self.needs_alloc = True
        return a_instrs + b_instrs + [f"call {wasm_name}"]

    def _translate_decimal_eq(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_eq(a, b) → Bool (i32)."""
        a_instrs = self.translate_expr(call.args[0], env)
        b_instrs = self.translate_expr(call.args[1], env)
        if a_instrs is None or b_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_eq", ["i32", "i32"], ["i32"])
        return a_instrs + b_instrs + [f"call {wasm_name}"]

    def _translate_decimal_round(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """decimal_round(d, places) → Decimal handle (i32)."""
        d_instrs = self.translate_expr(call.args[0], env)
        p_instrs = self.translate_expr(call.args[1], env)
        if d_instrs is None or p_instrs is None:
            return None
        wasm_name = self._register_decimal_import(
            "decimal_round", ["i32", "i64"], ["i32"])
        return d_instrs + p_instrs + [f"call {wasm_name}"]

    # ── Map<K, V> host-import builtins ──────────────────────────────

    @staticmethod
    def _map_wasm_tag(vera_type: str | None) -> str:
        """Map a Vera type name to a single-char WASM type tag.

        Used to build monomorphized host import names like
        ``map_insert$ki_vi`` (key=i64, value=i64).
        """
        if vera_type in ("Int", "Nat"):
            return "i"   # i64
        if vera_type == "Float64":
            return "f"   # f64
        if vera_type == "String":
            return "s"   # i32_pair
        # Bool, Byte, ADTs, Map handles → i32
        return "b"

    @staticmethod
    def _map_wasm_types(tag: str) -> list[str]:
        """Return WAT param types for a type tag."""
        if tag == "i":
            return ["i64"]
        if tag == "f":
            return ["f64"]
        if tag == "s":
            return ["i32", "i32"]
        return ["i32"]

    def _map_import_name(self, op: str, key_tag: str | None = None,
                         val_tag: str | None = None) -> str:
        """Build a mangled Map host import name and register it."""
        if key_tag is not None and val_tag is not None:
            suffix = f"$k{key_tag}_v{val_tag}"
        elif key_tag is not None:
            suffix = f"$k{key_tag}"
        elif val_tag is not None:
            suffix = f"$v{val_tag}"
        else:
            suffix = ""
        name = f"{op}{suffix}"
        self._map_ops_used.add(name)
        return name

    def _register_map_import(
        self, op: str, key_tag: str | None = None,
        val_tag: str | None = None,
        extra_params: list[str] | None = None,
        results: list[str] | None = None,
    ) -> str:
        """Register a Map host import and return the WASM call name."""
        name = self._map_import_name(op, key_tag, val_tag)
        wasm_name = f"$vera.{name}"
        params: list[str] = []
        if extra_params:
            params.extend(extra_params)
        param_str = " ".join(f"(param {p})" for p in params)
        result_str = ""
        if results:
            result_str = " ".join(f"(result {r})" for r in results)
        sig = f"(func {wasm_name} {param_str} {result_str})".rstrip()
        import_line = f'  (import "vera" "{name}" {sig})'
        self._map_imports.add(import_line)
        return wasm_name

    def _infer_map_key_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Map's key from the call arguments."""
        # For map_insert(m, k, v): key is arg[1]
        # For map_get/contains/remove(m, k): key is arg[1]
        # For map_new(): no key arg, infer from type context
        if call.name == "map_new":
            return None
        if len(call.args) >= 2:
            return self._infer_vera_type(call.args[1])
        return None

    def _infer_map_val_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Map's value from the call arguments."""
        # For map_insert(m, k, v): value is arg[2]
        if call.name == "map_insert" and len(call.args) >= 3:
            return self._infer_vera_type(call.args[2])
        return None

    def _translate_map_new(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_new() → i32 handle via host import.

        Since map_new has no arguments, we use a single unparameterised
        host import that returns a fresh empty map handle.
        """
        wasm_name = "$vera.map_new"
        sig = "(func $vera.map_new (result i32))"
        self._map_imports.add(f'  (import "vera" "map_new" {sig})')
        self._map_ops_used.add("map_new")
        return [f"call {wasm_name}"]

    def _translate_map_insert(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_insert(m, k, v) → i32 (new handle) via host import.

        Emits a type-specific host import based on the key and value types.
        """
        key_type = self._infer_vera_type(call.args[1])
        val_type = self._infer_vera_type(call.args[2])
        kt = self._map_wasm_tag(key_type)
        vt = self._map_wasm_tag(val_type)

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        params.extend(self._map_wasm_types(vt))  # value
        wasm_name = self._register_map_import(
            "map_insert", kt, vt,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_get(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_get(m, k) → i32 (Option<V> heap pointer) via host import.

        The host reads the value from its internal dict, constructs an
        Option ADT (Some/None) in WASM memory, and returns the pointer.
        """
        key_type = self._infer_vera_type(call.args[1])
        kt = self._map_wasm_tag(key_type)
        # We need the value tag too, so the host knows how to build Option<V>.
        # Infer from the map's type — look at the slot ref for arg[0].
        val_type = self._infer_map_value_from_map_arg(call.args[0])
        vt = self._map_wasm_tag(val_type)

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        wasm_name = self._register_map_import(
            "map_get", kt, vt,
            extra_params=params, results=["i32"],
        )
        self.needs_alloc = True
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _infer_map_value_from_map_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the value type V from a Map<K, V> expression."""
        # If the map arg is a slot ref like @Map<String, Int>.0,
        # extract V from the type_args (not the type_name string).
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Map" and expr.type_args:
                if len(expr.type_args) == 2:
                    val_te = expr.type_args[1]
                    if isinstance(val_te, ast.NamedType):
                        return val_te.name
            # Fallback: parse from composite type_name string
            # Uses depth-aware split to handle nested generics
            # like Map<Result<Int, Bool>, String>
            name = expr.type_name
            if name.startswith("Map<") and name.endswith(">"):
                v = self._split_map_type_args(name)
                if v is not None:
                    return v[1]
        # If it's a function call that returns Map, try to infer
        if isinstance(expr, ast.FnCall):
            if expr.name in ("map_new", "map_insert", "map_remove"):
                if expr.name == "map_insert" and len(expr.args) >= 3:
                    return self._infer_vera_type(expr.args[2])
                # Recurse into the map argument
                if expr.args:
                    return self._infer_map_value_from_map_arg(expr.args[0])
        return None

    def _translate_map_contains(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_contains(m, k) → i32 (Bool) via host import."""
        key_type = self._infer_vera_type(call.args[1])
        kt = self._map_wasm_tag(key_type)

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        wasm_name = self._register_map_import(
            "map_contains", kt, None,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_remove(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_remove(m, k) → i32 (new handle) via host import."""
        key_type = self._infer_vera_type(call.args[1])
        kt = self._map_wasm_tag(key_type)

        params = ["i32"]  # map handle
        params.extend(self._map_wasm_types(kt))  # key
        wasm_name = self._register_map_import(
            "map_remove", kt, None,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_size(
        self, arg: "ast.Expr", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_size(m) → i64 (Int) via host import."""
        wasm_name = "$vera.map_size"
        sig = "(func $vera.map_size (param i32) (result i64))"
        self._map_imports.add(f'  (import "vera" "map_size" {sig})')
        self._map_ops_used.add("map_size")
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_keys(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_keys(m) → (i32, i32) Array<K> via host import."""
        # Infer key type from the map argument
        key_type = self._infer_map_key_from_map_arg(call.args[0])
        kt = self._map_wasm_tag(key_type)

        wasm_name = self._register_map_import(
            "map_keys", kt, None,
            extra_params=["i32"], results=["i32", "i32"],
        )
        self.needs_alloc = True
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_map_values(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """map_values(m) → (i32, i32) Array<V> via host import."""
        val_type = self._infer_map_value_from_map_arg(call.args[0])
        vt = self._map_wasm_tag(val_type)

        wasm_name = self._register_map_import(
            "map_values", val_tag=vt,
            extra_params=["i32"], results=["i32", "i32"],
        )
        self.needs_alloc = True
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    @staticmethod
    def _split_map_type_args(name: str) -> tuple[str, str] | None:
        """Split 'Map<K, V>' into (K, V) with nesting-aware comma split.

        Handles nested generics like Map<Result<Int, Bool>, String>
        by tracking angle-bracket depth.
        """
        inner = name[4:-1]  # strip "Map<" and ">"
        depth = 0
        for i, ch in enumerate(inner):
            if ch == "<":
                depth += 1
            elif ch == ">":
                depth -= 1
            elif ch == "," and depth == 0:
                k = inner[:i].strip()
                v = inner[i + 1:].strip()
                if k and v:
                    return (k, v)
        return None

    def _infer_map_key_from_map_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the key type K from a Map<K, V> expression."""
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Map" and expr.type_args:
                if len(expr.type_args) >= 1:
                    key_te = expr.type_args[0]
                    if isinstance(key_te, ast.NamedType):
                        return key_te.name
            name = expr.type_name
            if name.startswith("Map<") and name.endswith(">"):
                v = self._split_map_type_args(name)
                if v is not None:
                    return v[0]
        if isinstance(expr, ast.FnCall):
            if expr.name == "map_insert" and len(expr.args) >= 2:
                return self._infer_vera_type(expr.args[1])
            if expr.args:
                return self._infer_map_key_from_map_arg(expr.args[0])
        return None

    # ── Set<T> host-import builtins ──────────────────────────────

    def _set_import_name(self, op: str, elem_tag: str | None = None) -> str:
        """Build a mangled Set host import name."""
        suffix = f"$e{elem_tag}" if elem_tag is not None else ""
        name = f"{op}{suffix}"
        self._set_ops_used.add(name)
        return name

    def _register_set_import(
        self, op: str, elem_tag: str | None = None,
        extra_params: list[str] | None = None,
        results: list[str] | None = None,
    ) -> str:
        """Register a Set host import and return the WASM call name."""
        name = self._set_import_name(op, elem_tag)
        wasm_name = f"$vera.{name}"
        params: list[str] = []
        if extra_params:
            params.extend(extra_params)
        param_str = " ".join(f"(param {p})" for p in params)
        result_str = ""
        if results:
            result_str = " ".join(f"(result {r})" for r in results)
        sig = f"(func {wasm_name} {param_str} {result_str})".rstrip()
        import_line = f'  (import "vera" "{name}" {sig})'
        self._set_imports.add(import_line)
        return wasm_name

    def _infer_set_elem_type(self, call: "ast.FnCall") -> str | None:
        """Infer the Vera type of a Set's element from call arguments."""
        if call.name == "set_new":
            return None
        if len(call.args) >= 2:
            return self._infer_vera_type(call.args[1])
        return None

    def _infer_set_elem_from_set_arg(
        self, expr: "ast.Expr",
    ) -> str | None:
        """Infer the element type T from a Set<T> expression."""
        if isinstance(expr, ast.SlotRef):
            if expr.type_name == "Set" and expr.type_args:
                if len(expr.type_args) >= 1:
                    elem_te = expr.type_args[0]
                    if isinstance(elem_te, ast.NamedType):
                        return elem_te.name
            name = expr.type_name
            if name.startswith("Set<") and name.endswith(">"):
                return name[4:-1]
        if isinstance(expr, ast.FnCall):
            if expr.name == "set_add" and len(expr.args) >= 2:
                return self._infer_vera_type(expr.args[1])
            # Only recurse into set-returning functions
            if expr.name in ("set_new", "set_add", "set_remove"):
                if expr.args:
                    return self._infer_set_elem_from_set_arg(expr.args[0])
        return None

    def _translate_set_new(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_new() → i32 handle via host import."""
        wasm_name = "$vera.set_new"
        sig = "(func $vera.set_new (result i32))"
        self._set_imports.add(f'  (import "vera" "set_new" {sig})')
        self._set_ops_used.add("set_new")
        return [f"call {wasm_name}"]

    def _translate_set_add(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_add(s, elem) → i32 (new handle) via host import."""
        elem_type = self._infer_vera_type(call.args[1])
        et = self._map_wasm_tag(elem_type)

        params = ["i32"]  # set handle
        params.extend(self._map_wasm_types(et))  # element
        wasm_name = self._register_set_import(
            "set_add", et,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_contains(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_contains(s, elem) → i32 (Bool) via host import."""
        elem_type = self._infer_vera_type(call.args[1])
        et = self._map_wasm_tag(elem_type)

        params = ["i32"]  # set handle
        params.extend(self._map_wasm_types(et))  # element
        wasm_name = self._register_set_import(
            "set_contains", et,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_remove(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_remove(s, elem) → i32 (new handle) via host import."""
        elem_type = self._infer_vera_type(call.args[1])
        et = self._map_wasm_tag(elem_type)

        params = ["i32"]  # set handle
        params.extend(self._map_wasm_types(et))  # element
        wasm_name = self._register_set_import(
            "set_remove", et,
            extra_params=params, results=["i32"],
        )
        ins: list[str] = []
        for arg in call.args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            ins.extend(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_size(
        self, arg: "ast.Expr", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_size(s) → i64 (Int) via host import."""
        wasm_name = "$vera.set_size"
        sig = "(func $vera.set_size (param i32) (result i64))"
        self._set_imports.add(f'  (import "vera" "set_size" {sig})')
        self._set_ops_used.add("set_size")
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins

    def _translate_set_to_array(
        self, call: "ast.FnCall", env: WasmSlotEnv,
    ) -> list[str] | None:
        """set_to_array(s) → (i32, i32) Array<T> via host import."""
        elem_type = self._infer_set_elem_from_set_arg(call.args[0])
        et = self._map_wasm_tag(elem_type)

        wasm_name = self._register_set_import(
            "set_to_array", et,
            extra_params=["i32"], results=["i32", "i32"],
        )
        self.needs_alloc = True
        arg_instrs = self.translate_expr(call.args[0], env)
        if arg_instrs is None:
            return None
        ins: list[str] = list(arg_instrs)
        ins.append(f"call {wasm_name}")
        return ins
