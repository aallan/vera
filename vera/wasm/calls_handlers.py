"""Ability and effect handler translation mixin for WasmContext.

Handles: Show ability (_translate_show), Hash ability (_translate_hash,
_translate_hash_string), and effect handlers (State<T>, Exn<E>).
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class CallsHandlersMixin:
    """Methods for translating Show/Hash dispatch and effect handlers."""

    # -----------------------------------------------------------------
    # Ability operation dispatch: show and hash (§9.8)
    # -----------------------------------------------------------------

    # Dispatch map: Vera type → to_string builtin name
    _SHOW_DISPATCH: dict[str, str] = {
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
            return None

        # String → identity: show("hello") == "hello"
        if vera_type == "String":
            return self.translate_expr(arg, env)

        # Unit → literal "unit" string
        if vera_type == "Unit":
            offset, length = self.string_pool.intern("unit")
            return [f"i32.const {offset}", f"i32.const {length}"]

        # Decimal → decimal_to_string host import
        if vera_type == "Decimal":
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

        return None

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
            return None

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

        # Unit → constant 0
        if vera_type == "Unit":
            return ["i64.const 0"]

        # String → FNV-1a hash
        if vera_type == "String":
            return self._translate_hash_string(arg_instrs)

        return None

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
            return None

        if effect.name == "State" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_state(expr, env)

        if effect.name == "Exn" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_exn(expr, env)

        # Unsupported handler type
        return None

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
        if isinstance(type_arg, ast.NamedType):
            type_name = type_arg.name
        else:
            return None

        wasm_type = self._type_name_to_wasm(type_name)
        put_import = f"$vera.state_put_{type_name}"
        get_import = f"$vera.state_get_{type_name}"
        push_import = f"$vera.state_push_{type_name}"
        pop_import = f"$vera.state_pop_{type_name}"

        instructions: list[str] = []

        # 1. Push a fresh state cell (isolates this handler from any outer
        #    handler of the same type — fixes #417).
        instructions.append(f"call {push_import}")

        # 2. Initialize state: compile init_expr, call state_put
        if expr.state is not None:
            init_instrs = self.translate_expr(expr.state.init_expr, env)
            if init_instrs is None:
                return None
            instructions.extend(init_instrs)
            instructions.append(f"call {put_import}")
        # If no state clause, state starts at default (0)

        # 3. Save current effect_ops and inject handler ops
        saved_ops = dict(self._effect_ops)
        self._effect_ops["get"] = (get_import, False)
        self._effect_ops["put"] = (put_import, True)

        # 4. Compile handler body
        body_instrs = self.translate_block(expr.body, env)

        # 5. Restore effect_ops
        self._effect_ops = saved_ops

        if body_instrs is None:
            return None

        instructions.extend(body_instrs)

        # 6. Pop the state cell (restores outer handler's value).
        # pop is stack-neutral so the body's return value is already on the
        # WASM value stack and is unaffected.
        instructions.append(f"call {pop_import}")

        return instructions

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
            return None
        type_name = type_arg.name
        tag_name = f"$exn_{type_name}"
        is_pair = self._is_pair_type_name(type_name)

        # Unique label ids for nested handlers
        hid = self._next_handle_id
        self._next_handle_id += 1
        done_label = f"$hd_{hid}"
        catch_label = f"$hc_{hid}"

        # Infer result type: try handler clause first (body may always
        # throw, making its inferred type None), then fall back to body.
        result_wt = None
        if expr.clauses:
            clause_body = expr.clauses[0].body
            if isinstance(clause_body, ast.Block):
                result_wt = self._infer_block_result_type(clause_body)
        if result_wt is None:
            result_wt = self._infer_block_result_type(expr.body)

        # Save/inject throw as an effect op for the body
        saved_ops = dict(self._effect_ops)
        self._effect_ops["throw"] = (tag_name, False)

        # Compile body
        body_instrs = self.translate_block(expr.body, env)

        # Restore effect_ops
        self._effect_ops = saved_ops

        if body_instrs is None:
            return None

        # Compile handler clause body
        if not expr.clauses:
            return None
        clause = expr.clauses[0]  # Exn<E> has exactly one op: throw

        # Allocate locals for the caught exception value.
        # Pair types (String, Array<T>) use two consecutive i32 locals
        # (ptr at thrown_local, len at thrown_local + 1) matching the
        # convention used by _translate_slot_ref for pair types.
        if is_pair:
            thrown_local = self.alloc_local("i32")  # ptr
            _len_local = self.alloc_local("i32")    # len (consecutive: thrown_local + 1)
        else:
            thrown_wt = self._type_name_to_wasm(type_name)
            thrown_local = self.alloc_local(thrown_wt)

        # Push caught value into slot env for handler body
        handler_env = env.push(type_name, thrown_local)
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
            result_spec = ""  # pragma: no cover
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

        return instructions
