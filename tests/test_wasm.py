"""Unit tests for vera.wasm — WASM translation layer.

Tests StringPool, WasmSlotEnv directly, and exercises less-common
expression translation branches via the full compilation pipeline.
"""

from __future__ import annotations

import tempfile


from vera.wasm import StringPool, WasmSlotEnv
from vera.codegen import CompileResult, compile, execute
from vera.parser import parse_file
from vera.transform import transform


# =====================================================================
# Helpers
# =====================================================================

def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    tree = parse_file(path)
    ast = transform(tree)
    return compile(ast, source=source, file=path)


def _compile_ok(source: str) -> CompileResult:
    result = _compile(source)
    assert result.wasm_bytes is not None, f"Compile failed: {result.errors}"
    return result


def _run(source: str, fn: str | None = None,
         args: list[int] | None = None) -> int:
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args or [])
    assert exec_result.value is not None
    return int(exec_result.value)


# =====================================================================
# StringPool
# =====================================================================

class TestStringPool:
    def test_empty_pool(self) -> None:
        pool = StringPool()
        assert not pool.has_strings()
        assert pool.entries() == []
        assert pool.heap_offset == 0

    def test_intern_string(self) -> None:
        pool = StringPool()
        offset, length = pool.intern("hello")
        assert offset == 0
        assert length == 5
        assert pool.has_strings()

    def test_deduplication(self) -> None:
        pool = StringPool()
        first = pool.intern("abc")
        second = pool.intern("abc")
        assert first == second

    def test_multiple_strings(self) -> None:
        pool = StringPool()
        o1, l1 = pool.intern("hi")
        o2, l2 = pool.intern("bye")
        assert o1 == 0
        assert l1 == 2
        assert o2 == 2  # immediately after "hi"
        assert l2 == 3

    def test_empty_string(self) -> None:
        pool = StringPool()
        offset, length = pool.intern("")
        assert length == 0

    def test_heap_offset_after_strings(self) -> None:
        pool = StringPool()
        pool.intern("abc")  # 3 bytes
        pool.intern("de")   # 2 bytes
        assert pool.heap_offset == 5

    def test_entries_sorted(self) -> None:
        pool = StringPool()
        pool.intern("beta")
        pool.intern("alpha")
        entries = pool.entries()
        offsets = [e[1] for e in entries]
        assert offsets == sorted(offsets)

    def test_utf8_encoding(self) -> None:
        pool = StringPool()
        # "é" is 2 bytes in UTF-8
        offset, length = pool.intern("é")
        assert length == 2


# =====================================================================
# WasmSlotEnv
# =====================================================================

class TestWasmSlotEnv:
    def test_empty_resolve(self) -> None:
        env = WasmSlotEnv()
        assert env.resolve("Int", 0) is None

    def test_push_and_resolve(self) -> None:
        env = WasmSlotEnv()
        env2 = env.push("Int", 5)
        assert env2.resolve("Int", 0) == 5

    def test_resolve_out_of_range(self) -> None:
        env = WasmSlotEnv()
        env2 = env.push("Int", 5)
        assert env2.resolve("Int", 1) is None

    def test_de_bruijn_ordering(self) -> None:
        env = WasmSlotEnv()
        env2 = env.push("Int", 10)
        env3 = env2.push("Int", 20)
        # Index 0 = most recent
        assert env3.resolve("Int", 0) == 20
        assert env3.resolve("Int", 1) == 10

    def test_separate_type_stacks(self) -> None:
        env = WasmSlotEnv()
        env2 = env.push("Int", 5)
        env3 = env2.push("Bool", 7)
        assert env3.resolve("Int", 0) == 5
        assert env3.resolve("Bool", 0) == 7

    def test_immutability(self) -> None:
        env = WasmSlotEnv()
        env.push("Int", 5)
        # Original env unchanged
        assert env.resolve("Int", 0) is None


# =====================================================================
# Expression translation edge cases (via compile pipeline)
# =====================================================================

class TestTranslationEdgeCases:
    def test_string_in_io_print(self) -> None:
        """IO.print with string literal compiles and runs."""
        source = """\
public fn hello(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("hello world")
}
"""
        result = _compile_ok(source)
        assert b"hello world" in result.wasm_bytes

    def test_float_mod_compiles(self) -> None:
        """Float MOD compiles to f64 instruction sequence (not skipped)."""
        source = """\
public fn fmod(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  @Float64.1 % @Float64.0
}
"""
        result = _compile_ok(source)
        assert "fmod" in (result.exports or [])
        assert "f64.trunc" in result.wat

    def test_call_helper_function(self) -> None:
        """Calling a helper function compiles correctly."""
        source = """\
public fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

public fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  helper(@Int.0)
}
"""
        assert _run(source, "outer", [10]) == 11

    def test_nested_if_in_let(self) -> None:
        """Nested if-then-else inside let binding."""
        source = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = if @Int.0 > 0 then { 1 } else { 0 };
  @Int.0 + 100
}
"""
        assert _run(source, "f", [5]) == 101
        assert _run(source, "f", [-1]) == 100

    def test_bool_comparison_result(self) -> None:
        """Boolean comparison operations return i32."""
        source = """\
public fn is_positive(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Int.0 > 0
}
"""
        assert _run(source, "is_positive", [5]) == 1
        assert _run(source, "is_positive", [-1]) == 0

    def test_multiple_let_bindings(self) -> None:
        """Chain of let bindings with different types."""
        source = """\
public fn chain(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0 + 1;
  let @Int = @Int.0 * 2;
  @Int.0
}
"""
        assert _run(source, "chain", [5]) == 12

    def test_negation_int(self) -> None:
        """Unary negation on integers."""
        source = """\
public fn negate(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  -@Int.0
}
"""
        assert _run(source, "negate", [42]) == -42

    def test_boolean_not(self) -> None:
        """Boolean not operation."""
        source = """\
public fn invert(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  !@Bool.0
}
"""
        assert _run(source, "invert", [1]) == 0
        assert _run(source, "invert", [0]) == 1


class TestSubstituteTypeVarsFnType:
    """`#659` review finding F5 — `substitute_type_vars` over `FnType`
    recurses through params + return_type but deliberately leaves the
    `effect` field untouched.

    All current parameterised FnType aliases use monomorphic effects
    (`effects(pure)`).  The contract here is "effect not substituted"
    — type-design-analyzer noted that an effect carrying a type-var
    (e.g. `fn(A -> A) effects(<State<T>>)`) would not have its `T`
    rewritten.  That's a deliberate gap, not a bug; pinning it via
    tests means a future refactor that "fixes" the gap by silently
    walking effects can't slip past unnoticed.

    See `vera/wasm/inference.py::substitute_type_vars` for the
    implementation comment + rationale.
    """

    def test_fntype_params_and_return_are_substituted(self) -> None:
        """Substitution rewrites `T` → `Int` in both param and return
        positions of an `FnType`."""
        from vera import ast
        from vera.wasm.inference import substitute_type_vars

        # fn(T -> T) effects(pure)
        fn_type = ast.FnType(
            params=(ast.NamedType(name="T", type_args=None),),
            return_type=ast.NamedType(name="T", type_args=None),
            effect=ast.PureEffect(),
        )
        subst: dict[str, ast.TypeExpr] = {
            "T": ast.NamedType(name="Int", type_args=None),
        }
        result = substitute_type_vars(fn_type, subst)
        assert isinstance(result, ast.FnType)
        assert len(result.params) == 1
        param = result.params[0]
        assert isinstance(param, ast.NamedType)
        assert param.name == "Int"
        assert isinstance(result.return_type, ast.NamedType)
        assert result.return_type.name == "Int"

    def test_fntype_effect_is_passed_through_unchanged(self) -> None:
        """`effect` is preserved verbatim — type-vars inside an effect
        are NOT substituted.  This pins the deliberate gap noted in
        the #659 review.

        Future refactor that walks effects must update this test (and
        the corresponding comment in `substitute_type_vars`) rather
        than silently flip the contract.
        """
        from vera import ast
        from vera.wasm.inference import substitute_type_vars

        # Construct an EffectSet referencing T (a type-var the alias
        # would bind).  In current Vera grammar this is unusual but
        # constructible via the AST.  The substitution should NOT
        # rewrite the `T` inside the effect's type_args.
        effect_with_typevar = ast.EffectSet(
            effects=(
                ast.EffectRef(
                    name="State",
                    type_args=(ast.NamedType(name="T", type_args=None),),
                ),
            ),
        )
        fn_type = ast.FnType(
            params=(ast.NamedType(name="T", type_args=None),),
            return_type=ast.NamedType(name="T", type_args=None),
            effect=effect_with_typevar,
        )
        subst: dict[str, ast.TypeExpr] = {
            "T": ast.NamedType(name="Int", type_args=None),
        }
        result = substitute_type_vars(fn_type, subst)
        assert isinstance(result, ast.FnType)
        # params + return were substituted
        assert isinstance(result.params[0], ast.NamedType)
        assert result.params[0].name == "Int"
        # but effect is identical (T NOT rewritten) — the contract
        result_effect = result.effect
        assert isinstance(result_effect, ast.EffectSet)
        eff_ref = result_effect.effects[0]
        assert isinstance(eff_ref, ast.EffectRef)
        assert eff_ref.type_args is not None
        eff_arg = eff_ref.type_args[0]
        assert isinstance(eff_arg, ast.NamedType)
        assert eff_arg.name == "T", (
            "Effect type-var should NOT be substituted; #659 review F5"
        )
