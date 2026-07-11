"""Tests for vera.codegen — Monomorphization of generic (forall<T>) functions."""

from __future__ import annotations

from pathlib import Path

import pytest
import wasmtime

from vera.codegen import (
    CompileResult,
    compile,
    execute,
)
from vera.parser import parse_file
from vera.transform import transform


# =====================================================================
# Helpers
# =====================================================================


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    # Write to a temp source and parse
    import tempfile

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name

    try:
        tree = parse_file(path)
        ast = transform(tree)
        return compile(ast, source=source, file=path)
    finally:
        Path(path).unlink(missing_ok=True)


def _compile_ok(source: str) -> CompileResult:
    """Compile and assert no errors."""
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected errors: {errors}"
    return result


def _run(source: str, fn: str | None = None, args: list[int] | None = None) -> int:
    """Compile, execute, and return the integer result."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _run_float(
    source: str, fn: str | None = None, args: list[int | float] | None = None
) -> float:
    """Compile, execute, and return the float result."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None, "Expected a return value"
    assert isinstance(exec_result.value, float), (
        f"Expected float, got {type(exec_result.value).__name__}"
    )
    return exec_result.value


def _run_io(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> str:
    """Compile, execute, and return captured stdout."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    return exec_result.stdout


def _run_trap(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> None:
    """Compile, execute, and assert a WASM trap."""
    result = _compile_ok(source)
    with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
        execute(result, fn_name=fn, args=args)


# =====================================================================
# C6i: Monomorphization of generic (forall<T>) functions
# =====================================================================


class TestMonomorphization:
    """Tests for monomorphization of forall<T> functions."""

    def test_identity_int(self) -> None:
        """forall<T> fn identity instantiated with Int."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        assert _run(source, fn="main") == 42

    def test_identity_bool(self) -> None:
        """forall<T> fn identity instantiated with Bool."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ identity(true) }
"""
        assert _run(source, fn="main") == 1

    def test_identity_two_instantiations(self) -> None:
        """Same generic function instantiated with both Int and Bool."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_int(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }

public fn test_bool(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ identity(false) }
"""
        result = _compile_ok(source)
        # Private generic -> monomorphized variants not exported
        assert "identity$Int" not in result.exports
        assert "identity$Bool" not in result.exports
        # Public callers are exported
        assert "test_int" in result.exports
        assert "test_bool" in result.exports
        # Run both
        exec_int = execute(result, fn_name="test_int")
        assert exec_int.value == 42
        exec_bool = execute(result, fn_name="test_bool")
        assert exec_bool.value == 0

    def test_identity_slot_ref_arg(self) -> None:
        """Generic function called with a slot reference argument."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(@Int.0) }
"""
        assert _run(source, fn="main", args=[99]) == 99

    def test_const_function(self) -> None:
        """forall<A, B> fn const with two type parameters."""
        source = """\
private forall<A, B> fn const(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{ @A.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ const(42, true) }
"""
        assert _run(source, fn="main") == 42

    def test_generic_with_adt_match(self) -> None:
        """forall<T> fn is_some with ADT match (Some case)."""
        source = """\
private data Option<T> { None, Some(T) }

private forall<T> fn is_some(@Option<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match @Option<T>.0 {
    None -> false,
    Some(@T) -> true
  }
}

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ is_some(Some(1)) }
"""
        assert _run(source, fn="main") == 1

    def test_generic_with_adt_match_none(self) -> None:
        """forall<T> fn is_some with ADT match (None case)."""
        source = """\
private data Option<T> { None, Some(T) }

private forall<T> fn is_some(@Option<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match @Option<T>.0 {
    None -> false,
    Some(@T) -> true
  }
}

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  is_some(@Option<Int>.0)
}
"""
        assert _run(source, fn="main") == 0

    def test_generic_over_param_adt_runs(self) -> None:
        """#891: a generic instantiated over a parameterized ADT (`gid(MkBox(7))`
        where `gid : forall<T> fn(@T -> @T)` and `data Box<T> { MkBox(T) }`) must
        run.  The postcondition `@T.result == @T.0` lowers `@T` (an i32 heap
        pointer once `T = Box`) — the `ResultRef` operand once inferred as the
        scalar i64 default emitted `i64.eq` against two i32 operands, trapping at
        run with `type mismatch: expected i64, found i32` in the `gid$Box` clone.
        The clone must lower an ADT-bound type variable as i32 on BOTH the
        signature AND the postcondition/body slot reads."""
        source = """\
public data Box<T> { MkBox(T) }

public forall<T> fn gid(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match gid(MkBox(42)) {
    MkBox(@Int) -> @Int.0
  }
}
"""
        # 42 is not a codegen fallback/default value; a wrong lowering traps at
        # compile so any observable value distinguishes fixed from broken, but
        # the unwrap also proves the ADT round-trips its payload intact.
        assert _run(source, fn="main") == 42

    def test_generic_nullary_ctor_leaf_runs(self) -> None:
        """#971: a bare nullary constructor `Leaf` returned under
        forall<T> -> @Tree<T> (a user-defined generic ADT) type-checks after
        the fix, monomorphizes at T = Int, and runs.  `empty_tree(())` yields
        Leaf; `tree_or` funnels both arms to the sentinel default, so the Leaf
        arm carries 555 through the compiled module — the run-level companion
        to the checker/verify pins for the bare-None-under-forall family."""
        source = """\
private data Tree<T> { Leaf, Node(T) }

private forall<T> fn empty_tree(@Unit -> @Tree<T>)
  requires(true) ensures(true) effects(pure)
{
  Leaf
}

private forall<T> fn tree_or(@Tree<T>, @T -> @T)
  requires(true) ensures(true) effects(pure)
{
  match @Tree<T>.0 {
    Node(@T) -> @T.0,
    Leaf -> @T.0
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  tree_or(empty_tree(()), 555)
}
"""
        # 555 is not a codegen fallback/default; a wrong lowering of the
        # nullary Leaf arm would trap at compile or produce a different value.
        assert _run(source, fn="main") == 555

    def test_generic_fn_wat_has_mangled_name(self) -> None:
        """WAT output contains mangled function name."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        result = _compile_ok(source)
        assert "$identity$Int" in result.wat

    def test_generic_fn_mangled_in_exports(self) -> None:
        """Private generic's mangled names not exported; public caller is."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        result = _compile_ok(source)
        # Private generic -> monomorphized variants not exported
        assert "identity$Int" not in result.exports
        assert "identity" not in result.exports
        # Public caller is exported
        assert "main" in result.exports

    def test_non_generic_fn_unaffected(self) -> None:
        """Non-generic functions compile normally alongside generic ones."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ double(identity(21)) }
"""
        assert _run(source, fn="main") == 42

    def test_generic_identity_in_let_binding(self) -> None:
        """Generic call result used in a let binding."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = identity(10);
  @Int.0 + 5
}
"""
        assert _run(source, fn="main") == 15

    def test_generic_chained_calls(self) -> None:
        """Generic function called with result of another generic call."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(identity(99)) }
"""
        assert _run(source, fn="main") == 99

    def test_generic_in_if_branch(self) -> None:
        """Generic call inside an if-then-else branch."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { identity(1) } else { identity(2) }
}
"""
        assert _run(source, fn="main", args=[1]) == 1
        assert _run(source, fn="main", args=[0]) == 2

    def test_generic_with_arithmetic_arg(self) -> None:
        """Generic function called with arithmetic expression as argument."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(3 + 4) }
"""
        assert _run(source, fn="main") == 7

    def test_generic_no_callers_skipped(self) -> None:
        """Generic function with no callers is gracefully skipped."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "main" in result.exports
        # identity has no callers -> no monomorphized version -> not in exports
        assert "identity" not in result.exports

    def test_generics_example_file(self) -> None:
        """examples/generics.vera compiles without errors."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "generics.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile(source)
        assert result.ok

    def test_list_ops_example_file(self) -> None:
        """examples/list_ops.vera compiles and runs correctly (#154)."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "list_ops.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_list")
        assert exec_result.value == 60


# =====================================================================
# C6j: Ability constraint satisfaction and operation codegen
# =====================================================================


class TestAbilityConstraints:
    """Tests for ability constraint checking and eq() operation rewriting."""

    def test_eq_int(self) -> None:
        """forall<T where Eq<T>> with Int — equal values return true."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(42, 42) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 1

    def test_eq_int_false(self) -> None:
        """forall<T where Eq<T>> with Int — unequal values return false."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(1, 2) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 0

    def test_eq_bool(self) -> None:
        """forall<T where Eq<T>> with Bool."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(true, true) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 1

    def test_eq_in_if(self) -> None:
        """eq result used directly as if condition."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(@Int.0, 10) then { 100 } else { 200 }
}
"""
        assert _run(source, fn="main", args=[10]) == 100
        assert _run(source, fn="main", args=[5]) == 200

    def test_eq_constraint_multiple_calls(self) -> None:
        """Same constrained fn called with Int and Bool."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn test_int(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(5, 5) then { 1 } else { 0 }
}

public fn test_bool(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(false, false) then { 1 } else { 0 }
}
"""
        result = _compile_ok(source)
        exec_int = execute(result, fn_name="test_int")
        assert exec_int.value == 1
        exec_bool = execute(result, fn_name="test_bool")
        assert exec_bool.value == 1

    def test_eq_non_generic_direct_call(self) -> None:
        """eq(1, 1) in a non-generic function — rewritten by Pass 1.6."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if eq(1, 1) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 1

    def test_eq_nested_in_expression(self) -> None:
        """eq in let bindings combined with boolean and."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = are_equal(3, 3);
  let @Bool = are_equal(7, 7);
  if @Bool.0 && @Bool.1 then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 1

    def test_eq_simple_enum(self) -> None:
        """Simple enum ADT satisfies Eq via auto-derivation."""
        source = """\
private data Color { Red, Green, Blue }

private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(Red, Blue) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 0

    def test_eq_simple_enum_equal(self) -> None:
        """Simple enum Eq returns true for same constructor."""
        source = """\
private data Color { Red, Green, Blue }

private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(Red, Red) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 1

    # ----------------------------------------------------------------
    # compare (Ord)
    # ----------------------------------------------------------------

    def test_compare_int_less(self) -> None:
        """compare(1, 2) → Less, matched to return 1."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match compare(1, 2) {
    Less -> 1,
    Equal -> 2,
    Greater -> 3
  }
}
"""
        assert _run(source, fn="main") == 1

    def test_compare_int_equal(self) -> None:
        """compare(5, 5) → Equal, matched to return 2."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match compare(5, 5) {
    Less -> 1,
    Equal -> 2,
    Greater -> 3
  }
}
"""
        assert _run(source, fn="main") == 2

    def test_compare_int_greater(self) -> None:
        """compare(9, 3) → Greater, matched to return 3."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match compare(9, 3) {
    Less -> 1,
    Equal -> 2,
    Greater -> 3
  }
}
"""
        assert _run(source, fn="main") == 3

    def test_compare_constrained_generic(self) -> None:
        """compare in constrained generic function."""
        source = """\
private forall<T where Ord<T>> fn cmp_result(@T, @T -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match compare(@T.1, @T.0) {
    Less -> 0 - 1,
    Equal -> 0,
    Greater -> 1
  }
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  cmp_result(3, 7)
}
"""
        # cmp_result(3, 7): @T.1 = 3 (first param), @T.0 = 7 (second)
        # compare(3, 7): 3 < 7 → Less → 0 - 1 = -1
        assert _run(source, fn="main") == -1

    # ----------------------------------------------------------------
    # show (Show)
    # ----------------------------------------------------------------

    def test_show_int(self) -> None:
        """show(42) produces the string \"42\"."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(show(42), "42")
}
"""
        assert _run(source, fn="main") == 1

    def test_show_bool(self) -> None:
        """show(true) produces the string \"true\"."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(show(true), "true")
}
"""
        assert _run(source, fn="main") == 1

    def test_show_string_identity(self) -> None:
        """show on a String is the identity."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(show("hello"), "hello")
}
"""
        assert _run(source, fn="main") == 1

    # ----------------------------------------------------------------
    # hash (Hash)
    # ----------------------------------------------------------------

    def test_hash_int_identity(self) -> None:
        """hash(42) == 42 (identity for Int)."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  hash(42)
}
"""
        assert _run(source, fn="main") == 42

    def test_hash_bool(self) -> None:
        """hash(true) == 1, hash(false) == 0."""
        source = """\
public fn test_true(-> @Int)
  requires(true) ensures(true) effects(pure)
{ hash(true) }

public fn test_false(-> @Int)
  requires(true) ensures(true) effects(pure)
{ hash(false) }
"""
        assert _run(source, fn="test_true") == 1
        assert _run(source, fn="test_false") == 0

    def test_hash_string_consistent(self) -> None:
        """hash of the same string is consistent and non-zero."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(hash("hello"), hash("hello"))
}
"""
        assert _run(source, fn="main") == 1

    # ----------------------------------------------------------------
    # Unsatisfied constraint errors
    # ----------------------------------------------------------------

    def test_unsatisfied_ord_adt(self) -> None:
        """ADT type with Ord constraint → E613."""
        source = """\
private data Color { Red, Green, Blue }

private forall<T where Ord<T>> fn cmp(@T, @T -> @Ordering)
  requires(true) ensures(true) effects(pure)
{ compare(@T.1, @T.0) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match cmp(Red, Blue) {
    Less -> 1,
    Equal -> 2,
    Greater -> 3
  }
}
"""
        result = _compile(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(d.error_code == "E613" for d in errors), (
            f"Expected E613, got: {[d.error_code for d in errors]}"
        )


# =====================================================================
# Structural show / hash for composite types (#911)
# =====================================================================


class TestCompositeShowHash:
    """show(x) / hash(x) on ADT / Tuple / Option / Result / Array (#911).

    Before #911 these were ``vera check``-green but dropped at codegen
    (``show()/hash() not supported for type ...`` → function skipped).
    Structural traversal mirrors the ``$eq_<type>`` machinery: render each
    field by its own ``show`` (recursively); fold field hashes with the tag.
    """

    # ---- show: user ADT ------------------------------------------------

    def test_show_adt_nullary(self) -> None:
        """A nullary enum constructor renders as its bare name."""
        source = """\
private data Color { Red, Green, Blue }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(Green), "Green") }
"""
        assert _run(source, fn="main") == 1

    def test_show_adt_one_field(self) -> None:
        """A single-field constructor renders as ``Ctor(field)``."""
        source = """\
private data Foo { MkFoo(Int) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(MkFoo(5)), "MkFoo(5)") }
"""
        assert _run(source, fn="main") == 1

    def test_show_adt_two_fields(self) -> None:
        """A multi-field constructor renders comma+space separated."""
        source = """\
private data Pair { MkPair(Int, Bool) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(MkPair(3, true)), "MkPair(3, true)") }
"""
        assert _run(source, fn="main") == 1

    # ---- show: Tuple ---------------------------------------------------

    def test_show_tuple(self) -> None:
        """A Tuple renders as ``(a, b)``."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(Tuple(1, 2)), "(1, 2)") }
"""
        assert _run(source, fn="main") == 1

    # ---- show: Option --------------------------------------------------

    def test_show_option_some(self) -> None:
        """``Some(x)`` renders with the inner value shown."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(some_int(3)), "Some(3)") }

private fn some_int(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(@Int.0) }
"""
        assert _run(source, fn="main") == 1

    def test_show_option_none(self) -> None:
        """``None`` renders as the bare name."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(none_int(0)), "None") }

private fn none_int(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None }
"""
        assert _run(source, fn="main") == 1

    # ---- show: Result --------------------------------------------------

    def test_show_result_ok(self) -> None:
        """``Ok(x)`` renders with the inner value shown."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(ok_int(7)), "Ok(7)") }

private fn ok_int(@Int -> @Result<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Ok(@Int.0) }
"""
        assert _run(source, fn="main") == 1

    def test_show_result_err(self) -> None:
        """``Err(e)`` renders with the error value shown."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(err_int(9)), "Err(9)") }

private fn err_int(@Int -> @Result<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Err(@Int.0) }
"""
        assert _run(source, fn="main") == 1

    # ---- show: Array ---------------------------------------------------

    def test_show_array(self) -> None:
        """An array renders as ``[e0, e1, e2]``."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show([1, 2, 3]), "[1, 2, 3]") }
"""
        assert _run(source, fn="main") == 1

    def test_show_array_empty(self) -> None:
        """An empty array renders as ``[]``."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(empty_arr(0)), "[]") }

private fn empty_arr(@Int -> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{ array_slice([@Int.0], 0, 0) }
"""
        assert _run(source, fn="main") == 1

    # ---- show: nested composites --------------------------------------

    def test_show_nested_adt(self) -> None:
        """An ADT field that is itself an ADT recurses."""
        source = """\
private data Inner { MkInner(Int) }
private data Outer { MkOuter(Inner) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(MkOuter(MkInner(4))), "MkOuter(MkInner(4))") }
"""
        assert _run(source, fn="main") == 1

    def test_show_option_of_tuple(self) -> None:
        """``Some`` wrapping a Tuple recurses through both."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(some_pair(1)), "Some((1, 2))") }

private fn some_pair(@Int -> @Option<Tuple<Int, Int>>)
  requires(true) ensures(true) effects(pure)
{ Some(Tuple(@Int.0, 2)) }
"""
        assert _run(source, fn="main") == 1

    def test_show_tuple_of_composite(self) -> None:
        """A Tuple whose fields are themselves composites recurses."""
        source = """\
private data Color { Red, Green, Blue }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(Tuple(Some(1), Green)), "(Some(1), Green)") }
"""
        assert _run(source, fn="main") == 1

    def test_show_array_of_tuples(self) -> None:
        """An array whose elements are composites recurses per element."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show([Tuple(1, 2), Tuple(3, 4)]), "[(1, 2), (3, 4)]") }
"""
        assert _run(source, fn="main") == 1

    def test_show_array_of_adt(self) -> None:
        """An array of ADT values renders each element structurally."""
        source = """\
private data Foo { MkFoo(Int) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show([MkFoo(1), MkFoo(2)]), "[MkFoo(1), MkFoo(2)]") }
"""
        assert _run(source, fn="main") == 1

    # ---- show: SAME-base finite nesting (#911 review finding #1) --------
    #
    # The recursion guard keys on the FULL parameterized type
    # (`Option<Option<Int>>` != `Option<Int>`), not the bare head — so a
    # finite composite nesting the same constructor at different type args
    # renders correctly instead of being mis-classified as recursive and
    # dropped.

    def test_show_option_of_option(self) -> None:
        """`Some(Some(x))` — same base (`Option`) nested finitely."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(nest(1)), "Some(Some(1))") }

private fn nest(@Int -> @Option<Option<Int>>)
  requires(true) ensures(true) effects(pure)
{ Some(Some(@Int.0)) }
"""
        assert _run(source, fn="main") == 1

    def test_show_result_of_result(self) -> None:
        """`Ok(Ok(x))` — same base (`Result`) nested finitely."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(nest(1)), "Ok(Ok(1))") }

private fn nest(@Int -> @Result<Result<Int, Int>, Int>)
  requires(true) ensures(true) effects(pure)
{ Ok(Ok(@Int.0)) }
"""
        assert _run(source, fn="main") == 1

    def test_show_inline_some_of_tuple(self) -> None:
        """Inline `show(Some(Tuple(1, 2)))` — bare-`Option` arg recovered."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(Some(Tuple(1, 2))), "Some((1, 2))") }
"""
        assert _run(source, fn="main") == 1

    def test_hash_option_of_option_runs(self) -> None:
        """hash on `Some(Some(x))` compiles and runs deterministically."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(nest(1)), hash(nest(1))) }

private fn nest(@Int -> @Option<Option<Int>>)
  requires(true) ensures(true) effects(pure)
{ Some(Some(@Int.0)) }
"""
        assert _run(source, fn="main") == 1

    # ---- show / hash: directly-recursive ADT (#924) --------------------
    #
    # `List<Int> = Cons(Int, List<Int>)` recurs on the SAME parameterized
    # type.  The inline #911 traversal cannot render unbounded depth, so it
    # requests a GENERATED recursive helper ($show_List_LInt_R /
    # $hash_List_LInt_R) that calls itself for the recursive field —
    # mirroring the $eq_<type> machinery (#773).  Codegen terminates (one
    # helper per recursive type), and the helper terminates at runtime by
    # recursing over the finite value.

    def test_show_recursive_list(self) -> None:
        """A directly-recursive ADT renders via a generated recursive helper."""
        source = """\
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(Cons(1, Cons(2, Nil))), "Cons(1, Cons(2, Nil))") }
"""
        result = _compile_ok(source)
        assert "main" in result.exports
        assert _run(source, fn="main") == 1

    def test_show_recursive_list_exported(self) -> None:
        """The `main` that shows a recursive ADT is no longer dropped (#924)."""
        source = """\
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(-> @String)
  requires(true) ensures(true) effects(pure)
{ show(Cons(1, Cons(2, Nil))) }
"""
        # Pre-#924 this dropped `main` (E602) → "No exported functions".
        assert "main" in _compile_ok(source).exports

    def test_show_recursive_list_nil(self) -> None:
        """The nullary base constructor renders as its bare name."""
        source = """\
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(nil_list(0)), "Nil") }

private fn nil_list(@Int -> @List<Int>)
  requires(true) ensures(true) effects(pure)
{ Nil }
"""
        assert _run(source, fn="main") == 1

    def test_hash_recursive_list_deterministic(self) -> None:
        """hash on a recursive ADT compiles, runs, and is deterministic."""
        source = """\
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(Cons(1, Cons(2, Nil))), hash(Cons(1, Cons(2, Nil)))) }
"""
        assert _run(source, fn="main") == 1

    def test_hash_recursive_list_distinguishes(self) -> None:
        """Structurally different recursive values hash differently."""
        source = """\
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(Cons(1, Cons(2, Nil))), hash(Cons(1, Cons(3, Nil)))) }
"""
        assert _run(source, fn="main") == 0

    def test_show_recursive_tree(self) -> None:
        """A recursive Tree with two self-referential fields renders."""
        source = """\
private data Tree<T> { Leaf, Node(Tree<T>, T, Tree<T>) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(Node(Leaf, 5, Node(Leaf, 7, Leaf))), "Node(Leaf, 5, Node(Leaf, 7, Leaf))") }
"""
        assert _run(source, fn="main") == 1

    def test_show_deep_list_no_shadow_overflow(self) -> None:
        """A deep (100-element) recursive value renders without shadow overflow.

        The generated helper recurses once per Cons cell; each level builds
        strings via `$alloc`.  100 levels confirms the recursion terminates
        (finite data) and the shadow-stack rooting holds — no `unreachable` /
        overflow.  Run under eager GC in the dedicated CLI test below.
        """
        source = """\
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{ string_length(show(build(100))) }

private fn build(@Nat -> @List<Nat>)
  requires(true) ensures(true) effects(pure)
{
  if @Nat.0 == 0 then { Nil } else { Cons(@Nat.0, build(@Nat.0 - 1)) }
}
"""
        # "Cons(100, Cons(99, … Cons(1, Nil) …))" — hundreds of chars.
        assert _run(source, fn="main") > 100

    def test_hash_deep_list_frame_restores_gc_sp(self) -> None:
        """A deep recursive `hash` restores `$gc_sp` and leaves it clean.

        The `hash` helper allocates nothing for a `List<Nat>`, yet `_hash_adt`
        still shadow-pushes its struct pointer per recursion.  The always-on GC
        frame restores `$gc_sp` on each return, so (a) a 500-level hash does not
        overflow the shadow stack, and (b) `$gc_sp` is left clean for the
        subsequent `show`, which builds strings that would trap or mis-root if
        the hash had leaked its pointer pushes into the caller's frame.  Pre-fix
        (frame gated on body allocation) the hash left `$gc_sp` advanced by 500.
        """
        source = """\
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @List<Nat> = build(500);
  eq(hash(@List<Nat>.0), hash(@List<Nat>.0)) && string_length(show(@List<Nat>.0)) > 500
}

private fn build(@Nat -> @List<Nat>)
  requires(true) ensures(true) effects(pure)
{
  if @Nat.0 == 0 then { Nil } else { Cons(@Nat.0, build(@Nat.0 - 1)) }
}
"""
        assert _run(source, fn="main") == 1

    def test_mutually_recursive_show(self) -> None:
        """A (non-generic) mutually-recursive ADT pair renders via helpers.

        `Forest` ↔ `Rose` reference each other; the generated `$show_Forest`
        and `$show_Rose` helpers cross-call.  (The GENERIC mutual case — where
        the type argument is buried in a nested generic field, `Grove(Rose<T>,
        Forest<T>)` — is now also supported via nested type-argument descent;
        see `test_generic_mutually_recursive_*` below and #934.)
        """
        source = """\
private data Forest { Empty, Grove(Rose, Forest) }
private data Rose { Bloom(Int, Forest) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(Grove(Bloom(1, Empty), Empty)), "Grove(Bloom(1, Empty), Empty)") }
"""
        assert _run(source, fn="main") == 1

    # ---- generic mutual recursion: nested type-arg recovery (#934) ------
    #
    # A GENERIC mutually-recursive ADT whose type argument is buried in a
    # NESTED generic field (`Grove(Rose<T>, Forest<T>)` — neither field IS a
    # bare `T`) could not recover its full parameterized type at a
    # show/hash/eq site.  The type argument is dug out of the nested generic
    # field's own constructor argument (`Bloom(T, …)` inside `Rose<T>` pins
    # `T = Int` from the literal `1`).  eq was a SILENT wrong result (two
    # structurally-equal values compared unequal by pointer); show/hash were
    # dropped at codegen (E602).

    _GENERIC_MUTUAL_DECLS = """\
private data Forest<T> { Empty, Grove(Rose<T>, Forest<T>) }
private data Rose<T> { Bloom(T, Forest<T>) }
"""

    def test_generic_mutually_recursive_eq_equal(self) -> None:
        """Structurally-equal generic-mutual values compare equal (#934).

        Pre-fix: the site fell back to a bare-pointer `i32.eq` of two freshly
        allocated structs → a SILENT `0`.  Post-fix: the recovered
        `Forest<Int>` routes to `$eq_Forest<Int>` → `1`.
        """
        source = self._GENERIC_MUTUAL_DECLS + """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if eq(Grove(Bloom(1, Empty), Empty), Grove(Bloom(1, Empty), Empty)) then { 1 } else { 0 } }
"""
        assert _run(source, fn="main") == 1

    def test_generic_mutually_recursive_eq_unequal(self) -> None:
        """Structurally-DIFFERENT generic-mutual values compare unequal (#934).

        Proves the fix is real structural equality, not a constant-1: the same
        constructors carrying `1` vs `2` must differ.
        """
        source = self._GENERIC_MUTUAL_DECLS + """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if eq(Grove(Bloom(1, Empty), Empty), Grove(Bloom(2, Empty), Empty)) then { 1 } else { 0 } }
"""
        assert _run(source, fn="main") == 0

    def test_generic_mutually_recursive_show(self) -> None:
        """A generic-mutual value renders exactly (#934).

        Pre-fix: `show()` on `Forest` (bare head, `<Int>` lost) tripped E602
        and dropped `main`.  Post-fix: renders `Grove(Bloom(1, Empty), Empty)`.
        """
        source = self._GENERIC_MUTUAL_DECLS + """
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(Grove(Bloom(1, Empty), Empty)), "Grove(Bloom(1, Empty), Empty)") }
"""
        assert "main" in _compile_ok(source).exports
        assert _run(source, fn="main") == 1

    def test_generic_mutually_recursive_hash_deterministic(self) -> None:
        """hash on a generic-mutual value is deterministic (#934)."""
        source = self._GENERIC_MUTUAL_DECLS + """
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(Grove(Bloom(1, Empty), Empty)), hash(Grove(Bloom(1, Empty), Empty))) }
"""
        assert _run(source, fn="main") == 1

    def test_generic_mutually_recursive_hash_discriminates(self) -> None:
        """hash discriminates structurally-different generic-mutual values (#934)."""
        source = self._GENERIC_MUTUAL_DECLS + """
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(Grove(Bloom(1, Empty), Empty)), hash(Grove(Bloom(2, Empty), Empty))) }
"""
        # Different payloads must not collide → eq of hashes is false (0).
        assert _run(source, fn="main") == 0

    def test_generic_mutual_non_eq_leaf_is_loud_e613(self) -> None:
        """A generic-mutual ADT with a non-Eq leaf still raises E613 (#934).

        No silent over-accept: an `Array<Int>` field is not Eq-derivable, so
        `eq` on the recovered generic-mutual type must be a clean, loud E613 —
        never a silent wrong result, never a traceback.
        """
        source = """\
private data Forest<T> { Empty, Grove(Rose<T>, Forest<T>) }
private data Rose<T> { Bloom(T, Forest<T>, Array<Int>) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if eq(Grove(Bloom(1, Empty, [1]), Empty), Grove(Bloom(1, Empty, [1]), Empty)) then { 1 } else { 0 } }
"""
        result = _compile(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(d.error_code == "E613" for d in errors), (
            f"Expected E613, got: {[d.error_code for d in errors]}"
        )

    def test_generic_mutual_non_show_leaf_is_loud_e602(self) -> None:
        """A generic-mutual ADT with a non-Show leaf still drops loud E602 (#934).

        A `Map` field has no `show`; the recovered generic-mutual `show`
        must E602-skip `main` (loud diagnostic) rather than silently mis-render.
        """
        source = """\
private data Forest<T> { Empty, Grove(Rose<T>, Forest<T>) }
private data Rose<T> { Bloom(T, Forest<T>, Map<Int, Int>) }

public fn main(-> @String)
  requires(true) ensures(true) effects(pure)
{ show(Grove(Bloom(1, Empty, map_new()), Empty)) }
"""
        result = _compile(source)
        assert "main" not in result.exports
        assert any(
            d.error_code == "E602" and "'main'" in d.description
            for d in result.diagnostics
        ), f"Expected E602 dropping main, got: {[(d.error_code, d.description) for d in result.diagnostics]}"

    # ---- hash: runs and is deterministic ------------------------------

    def test_hash_adt_nullary_runs(self) -> None:
        """hash on a nullary enum compiles, runs, and is stable."""
        source = """\
private data Color { Red, Green, Blue }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(Red), hash(Red)) }
"""
        assert _run(source, fn="main") == 1

    def test_hash_adt_distinguishes_tags(self) -> None:
        """Distinct nullary constructors hash differently."""
        source = """\
private data Color { Red, Green, Blue }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(Red), hash(Green)) }
"""
        # Red and Green must NOT collide → eq returns false (0).
        assert _run(source, fn="main") == 0

    def test_hash_adt_field_runs(self) -> None:
        """hash on a field-carrying ADT compiles, runs, and is stable."""
        source = """\
private data Foo { MkFoo(Int) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(MkFoo(5)), hash(MkFoo(5))) }
"""
        assert _run(source, fn="main") == 1

    def test_hash_adt_field_distinguishes(self) -> None:
        """Different field values hash differently."""
        source = """\
private data Foo { MkFoo(Int) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(MkFoo(5)), hash(MkFoo(6))) }
"""
        assert _run(source, fn="main") == 0

    def test_hash_tuple_runs(self) -> None:
        """hash on a Tuple compiles and runs deterministically."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(Tuple(1, 2)), hash(Tuple(1, 2))) }
"""
        assert _run(source, fn="main") == 1

    def test_hash_option_runs(self) -> None:
        """hash on Option (Some and None) compiles and runs."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash(some_int(3)), hash(some_int(3))) }

private fn some_int(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(@Int.0) }
"""
        assert _run(source, fn="main") == 1

    def test_hash_array_runs(self) -> None:
        """hash on an Array compiles and runs deterministically."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(hash([1, 2, 3]), hash([1, 2, 3])) }
"""
        assert _run(source, fn="main") == 1

    def test_show_large_array_no_shadow_overflow(self) -> None:
        """A large array's `show` unwinds per-element shadow slots.

        Each element render shadow-pushes its string buffers with no
        matching pop; without the per-iteration `$gc_sp` restore they leak
        one-plus per element and overflow the 4 096-slot shadow stack.  6 000
        elements (> 4 096) proves the restore reclaims them — pre-fix this
        traps with `unreachable`.
        """
        source = """\
public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{ string_length(show(array_range(0, 6000))) }
"""
        # array_range(0, 6000) → "[0, 1, …, 5999]"; assert it runs and returns
        # a plausible non-trivial length (no trap).
        assert _run(source, fn="main") > 6000

    def test_hash_large_composite_array_no_shadow_overflow(self) -> None:
        """A large array of ADTs `hash`es without shadow-stack overflow.

        A composite element's hash shadow-pushes its struct pointer per
        element; the per-iteration `$gc_sp` restore reclaims it.  5 000 ADT
        elements (> 4 096) proves it — pre-fix this traps with `unreachable`.
        """
        source = """\
private data Foo { MkFoo(Nat) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Foo> = array_map(array_range(0, 5000), fn(@Nat -> @Foo) effects(pure) { MkFoo(@Nat.0) });
  eq(hash(@Array<Foo>.0), hash(@Array<Foo>.0))
}
"""
        assert _run(source, fn="main") == 1

    # ---- non-uniform (polymorphic) recursion degrades cleanly (#933) ----
    #
    # A UNIFORMLY-recursive ADT (`List<T>` tail again `List<T>`) recurs on the
    # SAME parameterized type and renders via a single generated helper (the
    # #924 cases above).  A POLYMORPHICALLY-recursive ADT
    # (`Box<T>` with a `Box<Box<T>>` field) mints a strictly deeper, DISTINCT
    # type at every descent, so codegen's derived-helper generators would
    # expand without bound.  #933 caps that descent so the walk terminates with
    # the SAME clean skip a structurally-unsupported field takes — E602 for
    # show/hash (function dropped, loud warning), E613 for eq — rather than a
    # raw Python `RecursionError` traceback on a check-green program (which
    # #924's guard keying regressed).  These fixtures FAIL on the pre-#933
    # branch head with an uncaught `RecursionError`.

    _BOX_DECL = "private data Box<T> { BNil, BCons(T, Box<Box<T>>) }\n"

    def test_show_non_uniform_recursive_skips_cleanly(self) -> None:
        """`show` on a `Box<Box<T>>` degrades to a clean E602, not a traceback."""
        source = self._BOX_DECL + """
public fn main(-> @String)
  requires(true) ensures(true) effects(pure)
{ show(BCons(1, BNil)) }
"""
        # Pre-#933 this raised an uncaught RecursionError inside codegen.
        result = _compile(source)
        # `main` is dropped (unsupported show), not exported — the clean skip.
        assert "main" not in result.exports
        e602 = [d for d in result.diagnostics if d.error_code == "E602"]
        assert e602, "expected a clean [E602] skip, got none"
        # No error-severity diagnostic — a dropped-fn skip is a warning.
        assert not [d for d in result.diagnostics if d.severity == "error"]

    def test_hash_non_uniform_recursive_skips_cleanly(self) -> None:
        """`hash` on a `Box<Box<T>>` degrades to a clean E602, not a traceback."""
        source = self._BOX_DECL + """
public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{ hash(BCons(1, BNil)) }
"""
        result = _compile(source)
        assert "main" not in result.exports
        assert [d for d in result.diagnostics if d.error_code == "E602"]
        assert not [d for d in result.diagnostics if d.severity == "error"]

    def test_eq_non_uniform_recursive_skips_cleanly(self) -> None:
        """`eq` on a `Box<Box<T>>` degrades to a clean E613, not a traceback.

        The Eq-derivability gate (`_adt_satisfies_eq`) recurs unboundedly on
        the same non-uniform shape and crashed on the pre-#933 branch head
        (base crashed here too — this is a strict improvement: a loud E613
        replaces an uncaught traceback).
        """
        source = self._BOX_DECL + """
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(BCons(1, BNil), BCons(2, BNil)) }
"""
        result = _compile(source)
        e613 = [d for d in result.diagnostics if d.error_code == "E613"]
        assert e613, "expected a clean [E613] not-derivable diagnostic"

    def test_non_uniform_recursion_leaves_uniform_shapes_intact(self) -> None:
        """The #933 bound must not clip legitimate uniform show/hash/eq.

        Guards the bound's other direction: a uniformly-recursive `List<T>`
        (and its `List<List<Int>>` nesting) still renders / hashes / compares
        correctly with EXACTLY one helper per type — the bound fires only on
        genuinely-unbounded non-uniform expansion.
        """
        source = """\
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(show(Cons(Cons(1, Nil), Cons(Cons(2, Nil), Nil))),
     "Cons(Cons(1, Nil), Cons(Cons(2, Nil), Nil))")
  && eq(hash(Cons(1, Cons(2, Nil))), hash(Cons(1, Cons(2, Nil))))
  && eq(Cons(1, Nil), Cons(1, Nil))
}
"""
        # Compiles with `main` exported and every clause true at run time.
        wat = _compile_ok(source).wat
        # Exactly one helper per distinct type — no runaway duplication.
        assert wat.count("(func $show_List_LInt_R ") == 1
        assert wat.count("(func $show_List_LList_LInt_R_R ") == 1
        assert _run(source, fn="main") == 1

    def test_recursion_error_backstop_degrades_to_clean_skip(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The `RecursionError` catch converts an overflow into a clean E602.

        Belt-and-suspenders (#933): the nesting-depth cap normally fires first,
        but a future generator with a larger per-level frame cost could outrun
        it and blow Python's stack.  Simulated deterministically here — force
        `_show_adt` to raise `RecursionError` mid-body — the compile driver's
        `except RecursionError` MUST degrade to the same clean [E602]
        function-skip, never a raw traceback.
        """
        from vera.wasm.calls_handlers import CallsHandlersMixin

        def boom(*_args: object, **_kwargs: object) -> list[str] | None:
            raise RecursionError("maximum recursion depth exceeded")

        monkeypatch.setattr(CallsHandlersMixin, "_show_adt", boom)

        source = """\
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(-> @String)
  requires(true) ensures(true) effects(pure)
{ show(Cons(1, Cons(2, Nil))) }
"""
        result = _compile(source)
        # Clean skip, not a crash: `main` dropped, a loud [E602], no error.
        assert "main" not in result.exports
        assert [d for d in result.diagnostics if d.error_code == "E602"]
        assert not [d for d in result.diagnostics if d.severity == "error"]


class TestSplitParamType:
    """`_split_param_type` top-level type-argument splitting (#911 finding #2)."""

    def test_flat_two_args(self) -> None:
        from vera.wasm.calls_handlers import CallsHandlersMixin

        assert CallsHandlersMixin._split_param_type(
            "Result<Int, String>"
        ) == ("Result", ["Int", "String"])

    def test_single_arg(self) -> None:
        from vera.wasm.calls_handlers import CallsHandlersMixin

        assert CallsHandlersMixin._split_param_type(
            "Option<Int>"
        ) == ("Option", ["Int"])

    def test_nested_generic_in_last_position(self) -> None:
        """A nested generic in the LAST arg keeps its closing `>` intact.

        Pre-fix `rstrip(">")` stripped EVERY trailing `>`, yielding the
        corrupt `["Int", "Option<Int"]`.
        """
        from vera.wasm.calls_handlers import CallsHandlersMixin

        assert CallsHandlersMixin._split_param_type(
            "Result<Int, Option<Int>>"
        ) == ("Result", ["Int", "Option<Int>"])

    def test_same_base_nested(self) -> None:
        from vera.wasm.calls_handlers import CallsHandlersMixin

        assert CallsHandlersMixin._split_param_type(
            "Option<Option<Int>>"
        ) == ("Option", ["Option<Int>"])

    def test_bare_type_no_args(self) -> None:
        from vera.wasm.calls_handlers import CallsHandlersMixin

        assert CallsHandlersMixin._split_param_type("Foo") == ("Foo", [])


# =====================================================================
# Array operations: array_slice, array_map, array_filter, array_fold
# =====================================================================


class TestArrayOperations:
    """Tests for array_slice, array_map, array_filter, and array_fold."""

    # ----------------------------------------------------------------
    # array_slice
    # ----------------------------------------------------------------

    def test_array_slice_basic(self) -> None:
        """Slice [10,20,30,40,50] from index 1 to 4, expect length 3."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_slice([10, 20, 30, 40, 50], 1, 4))
}
"""
        assert _run(source, fn="main") == 3

    def test_array_slice_empty(self) -> None:
        """Slice with start >= end returns empty array."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_slice([1, 2, 3], 2, 2))
}
"""
        assert _run(source, fn="main") == 0

    def test_array_slice_clamped(self) -> None:
        """Out-of-range indices are clamped to array bounds."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_slice([1, 2, 3], 0, 100))
}
"""
        assert _run(source, fn="main") == 3

    # ----------------------------------------------------------------
    # array_map
    # ----------------------------------------------------------------

    def test_array_map_int(self) -> None:
        """Map *10 over [1,2,3], check first element is 10."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 * 10 });
  @Array<Int>.0[0]
}
"""
        assert _run(source, fn="main") == 10

    def test_array_map_identity(self) -> None:
        """Map identity function, result matches input length."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map([5, 10, 15], fn(@Int -> @Int) effects(pure) { @Int.0 });
  @Array<Int>.0[1]
}
"""
        assert _run(source, fn="main") == 10

    # ----------------------------------------------------------------
    # array_filter
    # ----------------------------------------------------------------

    def test_array_filter_basic(self) -> None:
        """Filter [1,2,3,4,5,6] where > 3, expect length 3."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_filter([1, 2, 3, 4, 5, 6], fn(@Int -> @Bool) effects(pure) { @Int.0 > 3 }))
}
"""
        assert _run(source, fn="main") == 3

    def test_array_filter_none(self) -> None:
        """Filter where always false returns empty array."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_filter([1, 2, 3], fn(@Int -> @Bool) effects(pure) { @Int.0 > 100 }))
}
"""
        assert _run(source, fn="main") == 0

    def test_array_filter_all(self) -> None:
        """Filter where always true returns same length."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_filter([1, 2, 3, 4], fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }))
}
"""
        assert _run(source, fn="main") == 4

    # ----------------------------------------------------------------
    # array_fold
    # ----------------------------------------------------------------

    def test_array_fold_sum(self) -> None:
        """Fold + over [1,2,3,4] with init 0, expect 10."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold([1, 2, 3, 4], 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 })
}
"""
        assert _run(source, fn="main") == 10

    def test_array_fold_product(self) -> None:
        """Fold * over [1,2,3,4] with init 1, expect 24."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold([1, 2, 3, 4], 1, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * @Int.0 })
}
"""
        assert _run(source, fn="main") == 24

    # ----------------------------------------------------------------
    # Chained operations
    # ----------------------------------------------------------------

    def test_array_map_filter_chain(self) -> None:
        """Map *2 then filter > 5: [1,2,3,4,5] -> [2,4,6,8,10] -> [6,8,10]."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map([1, 2, 3, 4, 5], fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });
  array_length(array_filter(@Array<Int>.0, fn(@Int -> @Bool) effects(pure) { @Int.0 > 5 }))
}
"""
        assert _run(source, fn="main") == 3

    # ----------------------------------------------------------------
    # Type-check tests (compile without errors)
    # ----------------------------------------------------------------

    def test_array_slice_type_check(self) -> None:
        """array_slice type-checks successfully."""
        source = """\
public fn main(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{
  array_slice([1, 2, 3], 0, 2)
}
"""
        _compile_ok(source)

    def test_array_map_type_check(self) -> None:
        """array_map type-checks successfully."""
        source = """\
public fn main(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{
  array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 + 1 })
}
"""
        _compile_ok(source)

    def test_array_filter_type_check(self) -> None:
        """array_filter type-checks successfully."""
        source = """\
public fn main(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{
  array_filter([1, 2, 3], fn(@Int -> @Bool) effects(pure) { @Int.0 > 1 })
}
"""
        _compile_ok(source)

    def test_array_fold_type_check(self) -> None:
        """array_fold type-checks successfully."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold([1, 2, 3], 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 })
}
"""
        _compile_ok(source)

    # ----------------------------------------------------------------
    # array_map — regression tests for the iterative implementation
    # (#480).  These exercise paths the existing tests above don't:
    # large inputs (stress the loop, not the recursion), closures
    # that capture outer variables, A != B with pair output, and
    # scalar Int → scalar Bool type change.
    # ----------------------------------------------------------------

    def test_array_map_large_input_no_stack_overflow(self) -> None:
        """10,000-element map without blowing the shadow stack.

        Regression guard: under the old recursive prelude implementation
        this would allocate 10,000 stack frames and hit the 16K shadow
        stack ceiling (post-#464).  The iterative implementation uses
        a single WAT ``loop`` with O(1) stack depth regardless of
        input size.  10K Int elements = 80,000 bytes of output —
        exercises a path that previously triggered #484 (now fixed;
        header size field is 31-bit).
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 10000);
  let @Array<Int> = array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });
  @Array<Int>.0[9999]
}
"""
        # Last element: 9999 * 2 = 19998
        assert _run(source, fn="main") == 19998

    def test_array_map_exact_65536_byte_boundary(self) -> None:
        """Output allocation of exactly 65,536 bytes — the first size
        corrupted under the old 16-bit header mask (#484).

        Precise regression guard: 8,192 Int elements × 8 bytes =
        65,536 bytes — the first size past the old ``0xFFFF`` ceiling.
        Under the pre-fix GC, the sweep would read the size as
        ``(131072 >> 1) & 0xFFFF = 0`` and treat the payload as an
        empty block, linking each 8-byte chunk into the free list and
        overwriting live data.  Any future regression that
        reintroduces a partial mask (e.g., 0x1FFFF) could still pass
        the 10K stress test but trip this one.

        The 65,535-byte boundary (CodeRabbit's matching case) isn't
        cleanly reachable with Int elements (which are 8-byte aligned)
        and Byte-element support is independently broken, so only the
        65,536-byte case is tested here.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 8192);
  let @Array<Int> = array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 + 7 });
  @Array<Int>.0[8191]
}
"""
        # Last element: 8191 + 7 = 8198.
        assert _run(source, fn="main") == 8198

    def test_array_map_type_change_int_to_bool(self) -> None:
        """Map Int → Bool — exercises the distinct-A-and-B codegen path.

        All the existing tests keep the element type (Int → Int).  This
        one converts to Bool, which has a different WASM type (i32) and
        different element width (1 byte vs 8) from Int.  The store ops
        must pick up the B-sized layout, not reuse A's.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Bool> = array_map([0, 1, 2, 3], fn(@Int -> @Bool) effects(pure) { @Int.0 > 1 });
  -- [false, false, true, true] → sum of 1-for-each-true = 0+0+1+1 = 2
  if @Array<Bool>.0[0] then { 1 } else { 0 } +
  if @Array<Bool>.0[1] then { 1 } else { 0 } +
  if @Array<Bool>.0[2] then { 1 } else { 0 } +
  if @Array<Bool>.0[3] then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 2

    def test_array_map_closure_captures_outer_variable(self) -> None:
        """Closure passed to array_map references a captured outer value.

        Ensures the iterative loop body correctly sets up the closure
        environment — the free-variable walker must lift the captured
        binding into the closure struct, and the inside-the-loop
        ``call_indirect`` must pass the env pointer so captures
        resolve.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 100;
  let @Array<Int> = array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 });
  @Array<Int>.0[2]
}
"""
        # Outer @Int.0 = 100 (captured); [1, 2, 3][2] = 3;
        # closure returns element + captured = 3 + 100 = 103.
        assert _run(source, fn="main") == 103

    def test_array_map_pair_element_output(self) -> None:
        """Map Int → String — output is a pair-typed element (i32_pair).

        This exercises the pair-output path in the iterative
        translator: the store sequence must lay down ptr at offset 0
        and len at offset 4, keyed off an 8-byte stride.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<String> = array_map([1, 2, 3], fn(@Int -> @String) effects(pure) { to_string(@Int.0) });
  string_length(@Array<String>.0[2])
}
"""
        # "3" has length 1
        assert _run(source, fn="main") == 1

    def test_array_map_empty_input(self) -> None:
        """Empty input → empty output; loop init/term exercised at n=0.

        Exercises the zero-length boundary: the loop's ``idx >= arr_len``
        guard must fire on the very first iteration so the body never
        runs, the closure is never invoked, and the allocated output
        array has length 0.
        """
        source = """\
public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 0);
  let @Array<Int> = array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });
  array_length(@Array<Int>.0)
}
"""
        assert _run(source, fn="main") == 0

    # ----------------------------------------------------------------
    # array_filter — regression tests for the iterative implementation
    # (#480 PR 2).  The iterative filter over-allocates
    # ``len * sizeof(T)`` (worst case, every element passes) and
    # returns ``(dst, write_idx)``.  Focus: boundary cases and
    # write-index correctness (separate from read-index).
    # ----------------------------------------------------------------

    def test_array_filter_large_input_no_stack_overflow(self) -> None:
        """10,000-element filter without blowing the shadow stack.

        Under the old recursive prelude each element pushed a stack
        frame and hit the 16K ceiling (#464) around 4K elements.
        The iterative loop is O(1) in shadow-stack depth.  10K Int
        elements = 80,000 bytes of worst-case output — exercises a
        path that previously triggered #484 (now fixed; header size
        field is 31-bit).
        """
        source = """\
public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 10000);
  let @Array<Int> = array_filter(@Array<Int>.0, fn(@Int -> @Bool) effects(pure) { @Int.0 < 100 });
  array_length(@Array<Int>.0)
}
"""
        # Elements 0..99 pass, rest rejected → length 100.
        assert _run(source, fn="main") == 100

    def test_array_filter_empty_input(self) -> None:
        """Empty input → empty output; loop init/term exercised at n=0.

        The loop's ``idx >= arr_len`` guard must fire on the very
        first iteration; the predicate is never invoked; the
        returned ``(dst, write_idx)`` has ``write_idx = 0``.
        """
        source = """\
public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 0);
  let @Array<Int> = array_filter(@Array<Int>.0, fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 });
  array_length(@Array<Int>.0)
}
"""
        assert _run(source, fn="main") == 0

    def test_array_filter_all_pass(self) -> None:
        """Every element passes → ``write_idx == arr_len``.

        Exercises the "no wasted tail" happy path: the dst buffer
        is fully used and the returned length equals the input
        length.  Reads several elements to confirm the write path
        copied values correctly, not just that the count is right.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_filter([10, 20, 30, 40, 50], fn(@Int -> @Bool) effects(pure) { true });
  @Array<Int>.0[0] + @Array<Int>.0[2] + @Array<Int>.0[4]
}
"""
        # 10 + 30 + 50 = 90; confirms elements at idx 0, 2, 4 were copied intact.
        assert _run(source, fn="main") == 90

    def test_array_filter_none_pass(self) -> None:
        """Predicate always false → empty output despite non-empty input.

        The dst buffer is allocated at worst-case size but
        ``write_idx`` never advances, so the returned length is 0.
        """
        source = """\
public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_filter([1, 2, 3, 4, 5], fn(@Int -> @Bool) effects(pure) { false });
  array_length(@Array<Int>.0)
}
"""
        assert _run(source, fn="main") == 0

    def test_array_filter_closure_captures_outer_variable(self) -> None:
        """Predicate closure captures an outer binding.

        Ensures the closure-env lifting path works for filter the
        same way it does for map — the captured threshold must be
        visible inside the predicate body.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 3;
  let @Array<Int> = array_filter([1, 2, 3, 4, 5], fn(@Int -> @Bool) effects(pure) { @Int.0 > @Int.1 });
  @Array<Int>.0[0] + @Array<Int>.0[1]
}
"""
        # Captured threshold = 3; elements > 3 → [4, 5]; sum = 9.
        assert _run(source, fn="main") == 9

    def test_array_filter_pair_element(self) -> None:
        """Filter Array<String> — output is pair-typed (i32_pair).

        Exercises the pair-element copy path: both i32 words (ptr
        at offset 0, len at offset 4) must be loaded from src[idx]
        into temp locals, fed to the predicate, AND stored into
        dst[write_idx] if the predicate passed — without re-reading
        src.
        """
        source = """\
public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Array<String> = array_filter(["a", "bb", "ccc", "d"], fn(@String -> @Bool) effects(pure) { string_length(@String.0) > 1 });
  string_length(@Array<String>.0[0]) + string_length(@Array<String>.0[1])
}
"""
        # Elements with length > 1: ["bb", "ccc"] — lengths 2 and 3; sum = 5.
        assert _run(source, fn="main") == 5

    def test_array_filter_of_array_map(self) -> None:
        """Nested ``array_filter(array_map(...), pred)`` — output-type inference.

        Regression for a latent bug exposed during PR 2 review:
        ``_infer_concat_elem_type`` didn't handle ``array_map``
        calls, so its output-type (the closure's return type) was
        invisible to the enclosing filter.  The filter would bail
        out silently and the whole module would fail to compile.
        Now the helper consults the inner map's closure return type
        to size the filter correctly.
        """
        source = """\
public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Bool> = array_filter(
    array_map([1, 2, 3, 4, 5], fn(@Int -> @Bool) effects(pure) { @Int.0 > 2 }),
    fn(@Bool -> @Bool) effects(pure) { @Bool.0 }
  );
  array_length(@Array<Bool>.0)
}
"""
        # map → [false, false, true, true, true]; filter trues → [true, true, true]; len 3.
        assert _run(source, fn="main") == 3

    def test_array_map_of_array_map(self) -> None:
        """Nested ``array_map(array_map(...), fn)`` — output-type inference.

        Sibling to the filter-of-map test: the outer map must see
        the inner map's output element type (the inner closure's
        return type), not the original array's element type.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map(
    array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }),
    fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }
  );
  @Array<Int>.0[2]
}
"""
        # [1,2,3] → [2,4,6] → [3,5,7]; [2] = 7.
        assert _run(source, fn="main") == 7

    # ----------------------------------------------------------------
    # array_fold — regression tests for the iterative implementation
    # (#480 PR 3).  Structurally different from map/filter: no output
    # allocation (returns a scalar ``U``), closure takes two value
    # parameters (acc + elem), and pair/ADT accumulators need shadow-
    # stack rooting that's updated in-place each iteration.
    # ----------------------------------------------------------------

    def test_array_fold_large_input_no_stack_overflow(self) -> None:
        """10,000-element fold without blowing the shadow stack.

        Regression guard analogous to the map/filter stress tests.
        Sum of range(0, 10000) = 49,995,000.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 10000),
    0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        # Sum of 0..9999 = 9999 * 10000 / 2 = 49,995,000.
        assert _run(source, fn="main") == 49_995_000

    def test_array_fold_empty_input(self) -> None:
        """Empty input → returns init unchanged; closure never invoked.

        The loop's ``idx >= arr_len`` guard must fire on iteration
        zero so the accumulator stays at its initial value.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 0),
    42,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        assert _run(source, fn="main") == 42

    def test_array_fold_pair_accumulator_gc_safety(self) -> None:
        """``String`` accumulator survives closure-allocation GC cycles.

        String concat allocates a new buffer each iteration.  With
        10 iterations and each iteration freshly concatenating a
        3-char suffix, the accumulator grows monotonically and the
        closure's allocations can trigger GC mid-loop.  If the
        shadow-stack root overwrite (``global.get $gc_sp; i32.const
        8; i32.sub; i32.store``) is wrong, the acc_ptr gets swept
        and the final length is garbage.
        """
        source = """\
public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @String = array_fold(
    ["ab", "cd", "ef", "gh", "ij", "kl", "mn", "op", "qr", "st"],
    "",
    fn(@String, @String -> @String) effects(pure) { string_concat(@String.1, @String.0) }
  );
  string_length(@String.0)
}
"""
        # 10 strings of length 2 concatenated → length 20.
        assert _run(source, fn="main") == 20

    def test_array_fold_closure_captures_outer_variable(self) -> None:
        """Fold closure captures an outer binding.

        The captured `bias` is added in every iteration — confirms
        the env pointer is threaded correctly to `call_indirect`
        and the free-variable walker lifts the capture into the
        closure struct.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 10;
  array_fold(
    [1, 2, 3],
    0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 + @Int.2 }
  )
}
"""
        # Each iteration adds (elem + captured 10) to acc.
        # Iter 1: 0 + 1 + 10 = 11.  Iter 2: 11 + 2 + 10 = 23.
        # Iter 3: 23 + 3 + 10 = 36.
        assert _run(source, fn="main") == 36

    def test_array_fold_of_array_map(self) -> None:
        """Nested ``array_fold(array_map(...), init, fn)``.

        Exercises ``_infer_concat_elem_type`` seeing an ``array_map``
        call as fold's input argument — same path PR 2 fixed for
        filter-of-map.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_map([1, 2, 3, 4, 5], fn(@Int -> @Int) effects(pure) { @Int.0 * @Int.0 }),
    0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        # squares = [1, 4, 9, 16, 25]; sum = 55.
        assert _run(source, fn="main") == 55


# =====================================================================
# #775 — injective mono-clone name mangling
# =====================================================================


class TestMangleInjectivity:
    """#775: ``_mangle_fn_name`` must be injective over instantiations.

    The pre-fix sanitizer (``ct.replace("<", "_").replace(">", "")
    .replace(", ", "_")`` joined with ``_``) was lossy: two DISTINCT
    instantiations of one generic could share a WAT symbol, so both
    clones were emitted under the same ``$name`` and WAT compilation
    failed with ``duplicate func identifier`` (confirmed empirically:
    Pass 1.5 has no collision detection — both clones emit, wasmtime's
    parser rejects the module).

    Collision classes killed (from the issue):

    - parameterized built-in vs. flat user ADT:
      ``g<Map<String, Int>>`` vs ``g<Map_String_Int>``
      (both mangled to ``g$Map_String_Int``)
    - multi-parameter joins across the ``_`` boundary:
      ``g<A_B, C>`` vs ``g<A, B_C>`` (both ``g$A_B_C``)
    """

    def test_mangle_distinct_across_component_boundary(self) -> None:
        """``g<A_B, C>`` and ``g<A, B_C>`` must get distinct symbols."""
        from vera.monomorphize import Monomorphizer

        a = Monomorphizer._mangle_fn_name("g", ("A_B", "C"))
        b = Monomorphizer._mangle_fn_name("g", ("A", "B_C"))
        assert a != b, (
            f"non-injective mangle: g<A_B, C> and g<A, B_C> both -> {a}"
        )

    def test_mangle_distinct_parameterized_vs_flat_adt(self) -> None:
        """``g<Map<String, Int>>`` vs ``g<Map_String_Int>`` (user ADT)."""
        from vera.monomorphize import Monomorphizer

        a = Monomorphizer._mangle_fn_name("g", ("Map<String, Int>",))
        b = Monomorphizer._mangle_fn_name("g", ("Map_String_Int",))
        assert a != b, (
            f"non-injective mangle: Map<String, Int> and the flat ADT "
            f"name Map_String_Int both -> {a}"
        )

    def test_mangle_pairwise_distinct_adversarial_vectors(self) -> None:
        """A battery of near-miss type-arg vectors, all pairwise distinct.

        Every entry is a distinct instantiation vector a Vera program can
        legally produce (type names may contain ``_``; parameterized
        names are canonical ``Name<A, B>`` forms).  The mangles must be
        pairwise distinct — any collision is a wrong-symbol bug.
        """
        from vera.monomorphize import Monomorphizer

        vectors: list[tuple[str, ...]] = [
            ("A_B", "C"),
            ("A", "B_C"),
            ("A_B_C",),
            ("A", "B", "C"),
            ("A", "B_C_D"),
            ("A_B", "C_D"),
            ("A__B", "C"),
            ("Map<String, Int>",),
            ("Map_String_Int",),
            ("Map<String_Int>",),
            ("Box<A_B>", "C"),
            ("Box<A>", "B_C"),
            ("Box<A, B>",),
            ("Box<A>", "B"),
            # These two pairs pin the ``_`` doubling specifically: without
            # it, a type name that literally spells an escape code or the
            # join separator forges another instantiation's symbol.
            ("Box_LInt_R",),   # vs the encoding of ("Box<Int>",)
            ("Box<Int>",),
            ("A_JB",),         # vs the joined encoding of ("A", "B")
            ("A", "B"),
        ]
        mangled = [
            Monomorphizer._mangle_fn_name("g", v) for v in vectors
        ]
        seen: dict[str, tuple[str, ...]] = {}
        for vec, name in zip(vectors, mangled):
            assert name not in seen, (
                f"collision: {seen[name]} and {vec} both mangle to {name}"
            )
            seen[name] = vec

    def test_mangle_deterministic(self) -> None:
        """Same instantiation always yields the same symbol."""
        from vera.monomorphize import Monomorphizer

        a = Monomorphizer._mangle_fn_name("g", ("Map<String, Int>", "A_B"))
        b = Monomorphizer._mangle_fn_name("g", ("Map<String, Int>", "A_B"))
        assert a == b

    def test_unmangle_inverts_mangle_over_canonical_names(self) -> None:
        """``unmangle_type_name`` round-trips every canonical type name (#884).

        The verifier's Array-element reverse lookup depends on inverting the
        mangler to recover a ``_z3_sorts`` key (``Box<Int>``) from a mangled
        element sort name (``Box_LInt_R``).  The mangler is a prefix code, so
        the inverse is exact over canonical names — including flat ADT names
        that literally spell escape codes (``Box_Int`` → ``Box__Int`` →
        ``Box_Int``) and nested generics with separators.
        """
        from vera.monomorphize import mangle_type_name, unmangle_type_name

        names = [
            "Int", "Box<Int>", "List<Int>", "Map<String, Int>",
            "Box_Int", "A_B_C", "Result<String, Int>",
            "Tuple<Tuple<Int>, Int>", "Tuple<Tuple<Int, Int>>",
            "Map<String, List<Int>>",
        ]
        for name in names:
            assert unmangle_type_name(mangle_type_name(name)) == name, (
                f"mangle/unmangle round-trip failed for {name!r}"
            )

    def test_unmangle_rejects_non_range_input(self) -> None:
        """``unmangle_type_name`` raises on strings outside the mangler range.

        A trailing lone ``_`` or an unknown ``_X`` code has no preimage; the
        Array-element lookup relies on this to *skip* a candidate rather than
        silently fabricate a wrong key.
        """
        import pytest

        from vera.monomorphize import unmangle_type_name

        with pytest.raises(ValueError):
            unmangle_type_name("Box_")  # trailing lone underscore
        with pytest.raises(ValueError):
            unmangle_type_name("Box_X")  # unknown escape code

    # Two-param collision program: `unwrap_second<A_B, C>` and
    # `unwrap_second<A, B_C>` collided to `$unwrap_second$A_B_C` pre-fix
    # (WAT: duplicate func identifier).  Outputs are chosen so no
    # accidental fallback can coincide: 100 + 7 = 107 requires BOTH
    # instantiations to route to their own clone.
    #
    # The single-letter ADT names (`data A`, `data C`) also double as a
    # #869 regression pin: pre-fix they collided with the prelude
    # generics' type parameters, pulling never-called prelude templates
    # into compilation whose `call_indirect` referenced a table nothing
    # emitted — wasmtime rejected the module with "unknown table 0",
    # and this fixture needed a table-forcing `array_fold` workaround
    # in `main` to validate.  #869 is fixed; if it regresses, this
    # test fails at instantiation with the same error.
    TWO_PARAM_SRC = """\
private data A_B { MkAB(Int) }
private data B_C { MkBC(Int) }
private data A { MkA(Int) }
private data C { MkC(Int) }

private forall<T, U> fn unwrap_second(@T, @U -> @U)
  requires(true) ensures(true) effects(pure)
{
  @U.0
}

private fn c_value(@C -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @C.0 { MkC(@Int) -> @Int.0 }
}

private fn bc_value(@B_C -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @B_C.0 { MkBC(@Int) -> @Int.0 }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  c_value(unwrap_second(MkAB(1), MkC(100)))
    + bc_value(unwrap_second(MkA(2), MkBC(7)))
}
"""

    def test_two_param_boundary_collision_end_to_end(self) -> None:
        """``g<A_B, C>`` + ``g<A, B_C>`` in one program compiles and runs."""
        assert _run(self.TWO_PARAM_SRC, fn="main") == 107

    def test_two_param_boundary_collision_distinct_wat_symbols(self) -> None:
        """The two instantiations must own two distinct WAT functions."""
        import re

        result = _compile_ok(self.TWO_PARAM_SRC)
        defs = re.findall(
            r"\(func (\$unwrap_second\$[A-Za-z0-9_]+)", result.wat
        )
        assert len(defs) == 2, (
            f"expected exactly 2 unwrap_second clones, got {defs}"
        )
        assert len(set(defs)) == 2, (
            f"mono clones share one WAT symbol (collision): {defs}"
        )
        # Every call site must reference an emitted definition.
        calls = set(re.findall(
            r"(?:return_)?call (\$unwrap_second\$[A-Za-z0-9_]+)",
            result.wat,
        ))
        assert calls == set(defs), (
            f"call sites {calls} do not match clone definitions {set(defs)}"
        )

    def test_nested_generic_call_ret_type_lookup_uses_shared_mangler(
        self,
    ) -> None:
        """Nested generic calls need the shared mangler at ALL THREE sites.

        ``unwrap_second(true, unwrap_second(false, 42))``: to bind the
        outer call's ``U``, `_infer_vera_type` looks up the INNER call's
        return type in the clone registry (``_fn_ret_types``), which is
        keyed by the names Pass 1.5 emitted.  This test pins the
        invariant that the lookup key is built by the SAME mangler as
        clone emission.  Pre-#775 the two sites only agreed by
        coincidence: the lookup joined RAW type names with ``_``, which
        happened to equal the old sanitizer's output for simple types
        (while silently missing every parameterized instantiation).
        Under the injective scheme the coincidence is gone — a reverted
        lookup site desyncs even for ``(Bool, Int)``, ``U`` falls back
        to the phantom-var default ``Bool``, and the outer call resolves
        to an unregistered clone name — `main` is E602-dropped with
        "call target 'unwrap_second$...' not registered".  (Mutation-
        validated: re-breaking the lookup site flips exactly this test.)
        """
        source = """\
private forall<T, U> fn unwrap_second(@T, @U -> @U)
  requires(true) ensures(true) effects(pure)
{
  @U.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  unwrap_second(true, unwrap_second(false, 42))
}
"""
        result = _compile_ok(source)
        e602 = [
            d for d in result.diagnostics
            if d.error_code == "E602" and "'main'" in d.description
        ]
        assert not e602, (
            f"main was dropped — the return-type-lookup mangling desynced "
            f"from clone emission: {[d.description for d in e602]}"
        )
        exec_result = execute(result, fn_name="main")
        assert exec_result.value == 42

    def test_map_vs_flat_adt_collision_end_to_end(self) -> None:
        """``g<Map<String, Int>>`` + ``g<Map_String_Int>`` coexist."""
        source = """\
private data Map_String_Int { MkMSI(Int) }

private forall<T> fn pass_through(@T -> @T)
  requires(true) ensures(true) effects(pure)
{
  @T.0
}

private fn msi_value(@Map_String_Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Map_String_Int.0 { MkMSI(@Int) -> @Int.0 }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "k", 3);
  let @Map<String, Int> = pass_through(@Map<String, Int>.0);
  msi_value(pass_through(MkMSI(39))) + map_size(@Map<String, Int>.0)
}
"""
        # 39 + 1 = 40: the ADT instantiation must return the ADT payload
        # and the Map instantiation must return the (usable) Map handle.
        assert _run(source, fn="main") == 40


class TestTransitiveAliasGenericHof867:
    """#867 class, PR #880 review round (blast-radius skeptic): the generic
    higher-order monomorphization path did SINGLE-hop alias lookups in both
    consultors — ``_resolve_arg_fn_shape`` / ``_infer_fn_alias_type_args``
    (vera/monomorphize.py, instantiation discovery) and their WASM
    call-rewrite twins in vera/wasm/calls.py.  A closure slot typed as a
    two-hop alias chain (`type MyFn = InnerFn;` where `InnerFn = fn(...)`)
    passed to a generic HOF failed shape resolution, so a type param bound
    ONLY by the closure (the ``B`` in ``fn(A -> B)``) fell to the
    phantom-var default: check-green, run-trap
    (`type mismatch: expected i64, found i32`).  The single-hop control
    always ran.  Both consultors now route through the shared
    ``resolve_fn_type_alias`` (vera/monomorphize.py)."""

    # `B` is inferable ONLY from the closure argument — the second arg
    # binds `A` alone.  This is deliberate: a shape where a literal arg
    # also binds the result param would mask the closure-arg resolution
    # failure (the phantom default could coincide).
    _TWO_HOP_ARG = """\
type MapFn<A, B> = fn(A -> B) effects(pure);
type InnerFn = fn(Int -> Int) effects(pure);
type MyFn = InnerFn;

private forall<A, B> fn my_map(@MapFn<A, B>, @A -> @B)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@MapFn<A, B>.0, @A.0)
}

private fn use_it(@MyFn -> @Int)
  requires(true) ensures(true) effects(pure)
{
  my_map(@MyFn.0, 7)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  use_it(fn(@Int -> @Int) effects(pure) { @Int.0 * 10 })
}
"""

    _SINGLE_HOP_ARG = """\
type MapFn<A, B> = fn(A -> B) effects(pure);
type MyFn = fn(Int -> Int) effects(pure);

private forall<A, B> fn my_map(@MapFn<A, B>, @A -> @B)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@MapFn<A, B>.0, @A.0)
}

private fn use_it(@MyFn -> @Int)
  requires(true) ensures(true) effects(pure)
{
  my_map(@MyFn.0, 7)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  use_it(fn(@Int -> @Int) effects(pure) { @Int.0 * 10 })
}
"""

    # The PARAM side of the same class: the generic HOF's declared fn
    # param is itself an alias chain (`MapFn2<X, Y> = MapFn<X, Y>`), so
    # `_infer_fn_alias_type_args*`'s lookup of the param alias body must
    # resolve transitively too — instantiated at the alias's own param
    # names so positional matching stays alias-local.
    _PARAM_ALIAS_CHAIN = """\
type MapFn<A, B> = fn(A -> B) effects(pure);
type MapFn2<X, Y> = MapFn<X, Y>;

private forall<A, B> fn my_map(@MapFn2<A, B>, @A -> @B)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@MapFn2<A, B>.0, @A.0)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  my_map(fn(@Int -> @Int) effects(pure) { @Int.0 * 10 }, 7)
}
"""

    def test_two_hop_arg_alias_generic_hof_runs(self) -> None:
        """A two-hop-alias-typed closure slot into a generic HOF: pre-fix
        the closure shape failed to resolve, `B` fell to the phantom-var
        default, and the mono clone's signature mismatched at WASM
        validation (`expected i64, found i32`)."""
        assert _run(self._TWO_HOP_ARG) == 70

    def test_single_hop_arg_alias_generic_hof_runs(self) -> None:
        """Control: the single-hop form has always resolved (#604)."""
        assert _run(self._SINGLE_HOP_ARG) == 70

    def test_two_hop_arg_alias_mangles_concrete_clone(self) -> None:
        """Compile-time discriminator, execution-free: the mono suffix
        must be `$Int_Int` (closure-bound `B` = Int), never a
        phantom-default suffix."""
        result = _compile_ok(self._TWO_HOP_ARG)
        wat = result.wat or ""
        # Clone names use the #775 injective encoding: multi-arg
        # instantiation vectors join with `_J` (`my_map$Int_JInt`).
        assert "$my_map$Int_JInt" in wat, (
            "expected the closure-bound instantiation my_map$Int_JInt; "
            "got: "
            + repr([ln for ln in wat.splitlines() if "my_map$" in ln][:4]))
        assert "$my_map$Int_JBool" not in wat, (
            "phantom-var default leaked into the mono suffix — the "
            "closure arg's alias chain did not resolve (#867 HOF path)")

    def test_param_alias_chain_generic_hof_runs(self) -> None:
        """The HOF's own fn param declared through an alias chain
        (`MapFn2<X, Y> = MapFn<X, Y>`) must resolve transitively in
        `_infer_fn_alias_type_args*` as well — pre-fix: same
        check-green → run-trap."""
        assert _run(self._PARAM_ALIAS_CHAIN) == 70


class TestUserFnReturnTypeInArgPosition878:
    """#878: mono instantiation inference for a generic whose type argument
    must be recovered from a **user-fn call's return type in argument
    position**.

    A generic like ``option_unwrap_or(@Option<VeraT>, @VeraT -> @VeraT)``
    called as ``option_unwrap_or(decimal_div(a, b), d("0"))`` — where
    ``decimal_div`` returns ``Option<Decimal>`` and the user fn ``d`` returns
    ``@Decimal`` — must monomorphize at ``VeraT = Decimal``.  Pre-fix, the
    WASM call-rewrite consultor (``vera/wasm``) failed to bind ``VeraT`` from
    either argument:

      * ``_get_arg_type_info_wasm`` had **no ``FnCall`` branch**, so a
        parameterized builtin return (``decimal_div`` → ``Option<Decimal>``)
        in ``Option<VeraT>`` position bound nothing; and
      * a user-fn call in bare ``@VeraT`` position resolved through the
        WAT-collapse ``i32 → "Bool"`` (a ``Decimal`` handle is ``i32``),
        the same value as the phantom-var default.

    The call site then emitted ``call $option_unwrap_or$Bool`` — a clone
    Pass 1.5 never emitted (discovery, which consults
    ``_BUILTIN_PARAMETERIZED_RETURNS`` and precise declared return types,
    correctly emitted ``$Decimal``) — so ``main`` was skipped and dropped
    from the exports on a ``vera check``-green program.

    The ``Decimal`` return value (``0.3333…``) can never coincide with the
    ``Bool`` phantom default (``true``/``false`` → ``1``/``0``), so wrong and
    right are observably distinct — the exact Bool-coincidence trap CLAUDE.md
    warns about.
    """

    # Canonical issue repro, wired to IO so the run observably prints the
    # Decimal division — a value that CANNOT coincide with the Bool default.
    _REPRO_IO = """\
effect IO {
  op print(String -> Unit);
}

private fn d(@String -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ option_unwrap_or(decimal_from_string(@String.0), decimal_from_int(0)) }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(decimal_to_string(
    option_unwrap_or(decimal_div(d("1"), d("3")), d("0"))))
}
"""

    def test_user_fn_return_in_arg_position_runs_and_prints(self) -> None:
        """The crash repro: pre-fix ``main`` is skipped (`option_unwrap_or$Bool`
        dangling call) and never exported — `_run_io` raises.  Post-fix it
        prints the true Decimal quotient, not the Bool default."""
        out = _run_io(self._REPRO_IO, fn="main")
        assert out.strip() == "0.3333333333333333333333333333", (
            f"expected the Decimal quotient; got {out!r} — the generic "
            f"instantiation resolved to the Bool phantom default instead of "
            f"Decimal (#878)"
        )

    def test_user_fn_return_in_arg_position_mangles_decimal(self) -> None:
        """Compile-time discriminator, execution-free: the emitted WAT must
        reference ``$option_unwrap_or$Decimal`` at the ``main`` call site and
        never the ``$Bool`` phantom-default clone."""
        result = _compile_ok(self._REPRO_IO)
        wat = result.wat or ""
        assert "$option_unwrap_or$Decimal" in wat, (
            "expected the Decimal instantiation option_unwrap_or$Decimal"
        )
        assert "$option_unwrap_or$Bool" not in wat, (
            "phantom-var Bool default leaked into the call target — the "
            "user-fn / parameterized-builtin return in argument position did "
            "not resolve (#878)"
        )
        # main must not be skipped: it must be a real exported function.
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, f"unexpected errors: {errors}"
        skip_notes = [
            d for d in result.diagnostics
            if "function skipped" in str(d.description)
            or "No exported functions" in str(d.description)
        ]
        assert not skip_notes, (
            f"main was skipped — dangling call to a non-emitted clone: "
            f"{[str(d.description) for d in skip_notes]}"
        )

    # A generic bound SOLELY by a user fn in bare ``@VeraT`` position: no
    # builtin, no constructor arg masks the resolution.  ``mkdec`` returns a
    # ``Decimal`` (i32 handle) — pre-fix both codegen discovery AND the WASM
    # call-rewrite collapse it to ``Bool``, so the discovery desyncs from the
    # verifier (which uses precise declared return types).  The identity clone
    # body masks the run (Decimal flows through an i32-identity fn unchanged),
    # so this shape is checked at the discovery level, not by output.
    _BARE_TYPEVAR_USER_FN = """\
private fn mkdec(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_from_int(7) }

private forall<VeraT> fn pick_first(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{
  decimal_to_string(pick_first(mkdec(()), mkdec(())))
}
"""

    def test_bare_typevar_user_fn_discovery_matches_verifier(self) -> None:
        """The codegen mono-discovery and the verifier discovery must agree
        on the concrete instantiation a user-fn return drives.  Pre-fix
        codegen discovered ``pick_first$Bool`` (WAT-collapse i32→Bool of the
        Decimal return) while the verifier discovered ``pick_first$Decimal``
        (precise declared return type) — a #732 differential desync."""
        from vera.codegen.core import CodeGenerator
        from vera.verifier import ContractVerifier

        import tempfile

        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(self._BARE_TYPEVAR_USER_FN)
            f.flush()
            path = f.name
        prog = transform(parse_file(path))

        gen = CodeGenerator(source=self._BARE_TYPEVAR_USER_FN, file=path)
        gen.compile_program(prog)
        codegen_set = getattr(gen, "_emitted_instances", set())

        verifier = ContractVerifier(
            source=self._BARE_TYPEVAR_USER_FN, file=path,
        )
        verifier.register_program(prog)
        verifier_set = {
            (n, ct)
            for n, cts in verifier._instances.items()
            for ct in cts
        }

        # Codegen collapses Decimal→? at the WAT level, but the CONCRETE
        # discovery must not be the Bool phantom default.
        assert ("pick_first", ("Bool",)) not in codegen_set, (
            f"codegen discovered the Bool phantom default for a Decimal "
            f"user-fn return: {sorted(codegen_set)}"
        )
        assert ("pick_first", ("Decimal",)) in codegen_set, (
            f"codegen did not discover pick_first$Decimal: "
            f"{sorted(codegen_set)}"
        )
        assert codegen_set <= verifier_set or all(
            (n, ct) in verifier_set for (n, ct) in codegen_set
        ), (
            f"codegen discovery desyncs from verifier (#732):\n"
            f"  codegen  = {sorted(codegen_set)}\n"
            f"  verifier = {sorted(verifier_set)}"
        )

    # ---- PR #899 review round 2: the two coupled consultors must agree ----
    # Both repros below are the SAME class the #878 fix targets — check-green
    # (and verify-green), then `run` drops `main` because ONE of the two
    # discovery↔call-rewrite consultor pairs was updated and the other wasn't.

    # ISSUE 1: a non-generic user fn returning a PARAMETERIZED type
    # (`Option<Decimal>`) in `Option<T>` position.  The WASM call-rewrite
    # (`_get_arg_type_info_wasm`) recovered `T = Decimal` and mangled the call
    # to `first_opt$Decimal`, but instantiation discovery
    # (`Monomorphizer._get_arg_type_info`) had NO user-fn parameterized-return
    # branch, so it emitted only `first_opt$Bool` — the `$Decimal` clone was
    # never generated, `main` was skipped.  The unwrapped value (7) can't
    # coincide with the Bool default.
    _ISSUE1_PARAM_RETURN = """\
private fn maybe(@Int -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ Some(decimal_from_int(@Int.0)) }

private forall<T> fn first_opt(@Option<T>, @Int -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{ @Option<T>.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match first_opt(maybe(7), 0) {
    Some(@Decimal) -> if decimal_eq(@Decimal.0, decimal_from_int(7)) then { 7 } else { 1 },
    None -> 2
  }
}
"""

    def test_issue1_param_user_fn_return_runs(self) -> None:
        """A user fn returning `Option<Decimal>` in `Option<T>` position must
        drive `T = Decimal` on BOTH the discovery and call-rewrite sides.
        Pre-fix `main` is skipped (`first_opt$Decimal` never emitted)."""
        assert _run(self._ISSUE1_PARAM_RETURN, fn="main") == 7

    def test_issue1_discovery_matches_call_rewrite(self) -> None:
        """Discovery must emit the SAME clone the call site references — the
        `$Decimal` clone, never the `$Bool` phantom default."""
        result = _compile_ok(self._ISSUE1_PARAM_RETURN)
        wat = result.wat or ""
        assert "$first_opt$Decimal" in wat, (
            "discovery did not emit first_opt$Decimal for a parameterized "
            "user-fn return (#899 issue 1)"
        )
        assert "$first_opt$Bool" not in wat, (
            "phantom Bool default leaked — discovery not mirrored to "
            "call-rewrite (#899 issue 1)"
        )
        skip_notes = [
            d for d in result.diagnostics
            if "function skipped" in str(d.description)
            or "No exported functions" in str(d.description)
        ]
        assert not skip_notes, f"main skipped: {[str(d.description) for d in skip_notes]}"

    # ISSUE 2: a user fn whose declared return is an ALIAS resolving to a
    # scalar (`type Age = Int`) in bare `@T` position.  Discovery + verifier
    # key the clone on the RAW alias name (`pick$Age`), but the call-rewrite
    # `_infer_fncall_vera_type` alias-resolved to the scalar and mangled the
    # call to `pick$Int` — a clone never emitted.  The value 20 (via `getage`)
    # can't coincide with the phantom default, and the two distinct getage
    # returns make the De Bruijn ordering observable.
    _ISSUE2_ALIAS_SCALAR_RETURN = """\
type Age = Int;

private fn getage(@Int -> @Age)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

private forall<T> fn pick_last(@T, @T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  pick_last(getage(10), getage(20))
}
"""

    def test_issue2_alias_scalar_return_runs(self) -> None:
        """A user fn returning a scalar-resolving alias (`type Age = Int`) in
        bare `@T` position: the call-rewrite must key the clone on the RAW
        declared name (`pick_last$Age`), matching discovery / the verifier.
        Pre-fix the call site referenced `pick_last$Int`, never emitted, so
        `main` was skipped.  `@T.0` (De Bruijn: most recent) returns the second
        arg, `getage(20)` == 20."""
        assert _run(self._ISSUE2_ALIAS_SCALAR_RETURN, fn="main") == 20

    def test_issue2_discovery_matches_call_rewrite(self) -> None:
        """The emitted clone (`pick_last$Age`, raw alias name) and the call
        target must agree — the call site must not reference the alias-resolved
        `pick_last$Int`."""
        result = _compile_ok(self._ISSUE2_ALIAS_SCALAR_RETURN)
        wat = result.wat or ""
        assert "$pick_last$Age" in wat, (
            "discovery emitted the raw-name clone pick_last$Age but it is "
            "absent from the WAT (#899 issue 2)"
        )
        skip_notes = [
            d for d in result.diagnostics
            if "function skipped" in str(d.description)
            or "No exported functions" in str(d.description)
        ]
        assert not skip_notes, (
            f"main skipped — call-rewrite alias-resolved to a non-emitted "
            f"clone: {[str(d.description) for d in skip_notes]}"
        )

    # ---- PR #899 review round 3: parameterized return into a BARE @T ----
    # ISSUE 3 (a NET regression vs base): a non-generic user fn whose declared
    # return is a LITERAL parameterized type (`Option<…>`/`Result<…>`/`Box<…>`
    # — a NamedType that CARRIES `type_args`) bound to a generic's bare `@T`.
    # Discovery names the clone by the BASE name (`pick_last$Option`), but the
    # round-2 `_declared_return_clone_name` gated on `not ret_te.type_args`, so
    # a parameterized return bailed and fell through to the i32→`Bool` collapse
    # — the call site referenced `pick_last$Bool`, never emitted, `main`
    # skipped.  On BASE both sides consistently emit/call `$Bool` (wrong but
    # linked) and it runs — so this is a regression the PR introduced, not a
    # base bug.  The round-3 fix routes all three consultors through the shared
    # `declared_return_clone_key`, which returns the base name for a
    # parameterized return.  The base-name key is SOUND: a bare-`@T` body is
    # representation-polymorphic (it moves an i32 handle, can't project the ADT).
    _ISSUE3_PARAM_RETURN_BARE_T = """\
private fn mk(@Int -> @Option<Option<Decimal>>)
  requires(true) ensures(true) effects(pure)
{ Some(Some(decimal_from_int(@Int.0))) }

private forall<VeraT> fn pick_last(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 0) effects(pure)
{
  match pick_last(mk(1), mk(2)) {
    Some(@Option<Decimal>) -> 0,
    None -> 1
  }
}
"""

    _ISSUE3_RESULT_RETURN_BARE_T = """\
private fn mkr(@Int -> @Result<Option<Decimal>, String>)
  requires(true) ensures(true) effects(pure)
{ Ok(Some(decimal_from_int(@Int.0))) }

private forall<VeraT> fn pick_last(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 0) effects(pure)
{
  match pick_last(mkr(1), mkr(2)) {
    Ok(@Option<Decimal>) -> 0,
    Err(@String) -> 1
  }
}
"""

    _ISSUE3_BOX_RETURN_BARE_T = """\
private data Box<T> { MkBox(T) }

private fn mkb(@Int -> @Box<Decimal>)
  requires(true) ensures(true) effects(pure)
{ MkBox(decimal_from_int(@Int.0)) }

private forall<VeraT> fn pick_last(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 0) effects(pure)
{
  match pick_last(mkb(1), mkb(2)) {
    MkBox(@Decimal) -> 0
  }
}
"""

    def test_issue3_param_return_into_bare_typevar_runs(self) -> None:
        """`Option<…>` return bound to bare `@VeraT`: discovery emits
        `pick_last$Option`, so the call site must reference it, not the
        i32→`Bool` collapse.  Pre-round-3 `main` was dropped."""
        assert _run(self._ISSUE3_PARAM_RETURN_BARE_T, fn="main") == 0

    def test_issue3_result_return_into_bare_typevar_runs(self) -> None:
        """`Result<Option<Decimal>, String>` return bound to bare `@VeraT`."""
        assert _run(self._ISSUE3_RESULT_RETURN_BARE_T, fn="main") == 0

    def test_issue3_box_return_into_bare_typevar_runs(self) -> None:
        """User ADT `Box<Decimal>` return bound to bare `@VeraT`."""
        assert _run(self._ISSUE3_BOX_RETURN_BARE_T, fn="main") == 0

    def test_issue3_discovery_matches_call_rewrite(self) -> None:
        """The emitted clone (`pick_last$Option`) and the call target must
        agree — the call site must not reference the phantom `pick_last$Bool`."""
        result = _compile_ok(self._ISSUE3_PARAM_RETURN_BARE_T)
        wat = result.wat or ""
        assert "$pick_last$Option" in wat, (
            "discovery's base-name clone pick_last$Option is absent from the "
            "WAT (#899 issue 3)"
        )
        assert "$pick_last$Bool" not in wat, (
            "call-rewrite fell through to the i32→Bool collapse for a "
            "parameterized return (#899 issue 3)"
        )
        skip_notes = [
            d for d in result.diagnostics
            if "function skipped" in str(d.description)
            or "No exported functions" in str(d.description)
        ]
        assert not skip_notes, (
            f"main skipped — parameterized return into bare @T desynced "
            f"call-rewrite from discovery: "
            f"{[str(d.description) for d in skip_notes]}"
        )

    def test_issue3_base_name_key_collision_is_sound(self) -> None:
        """The base-name-only key (`pick_last$Option`) is sound for a bare-`@T`
        body: `Option<Decimal>` and `Option<Int>` collide to ONE identity clone
        that is representation-polymorphic (moves an i32 handle, never projects
        the ADT).  Both instantiations run correctly through the shared clone."""
        source = """\
private fn mkd(@Int -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ Some(decimal_from_int(@Int.0)) }

private fn mki(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(@Int.0) }

private forall<VeraT> fn pick_last(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = pick_last(mkd(1), mkd(2));
  let @Option<Int> = pick_last(mki(3), mki(4));
  match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> 0 }
}
"""
        # @Option<Int>.0 (most recent) = pick_last(mki(3), mki(4)) = mki(4)
        # = Some(4); the Decimal instantiation flows through the SAME clone.
        assert _run(source, fn="main") == 4


class TestGenericWhereHelper904:
    """#904 — a `where`-helper inside a monomorphized generic must be emitted.

    A generic ``forall<T>`` carrying a ``where { fn helper(...) {...} }`` block
    passes ``vera check`` but crashed at codegen: the clone (``outer$Int``)
    calls ``$helper`` but the where-helper was never emitted (the generic
    parent is skipped in Pass 2 because its ``@T`` param is `unsupported`, and
    where-helpers used to be emitted only alongside their compilable parent).
    Both helper shapes must work:

    - (a) T-INDEPENDENT helper (``fn helper(@Int -> @Int)``, no ``@T``): its
      body is instantiation-agnostic; it must still be emitted and the clone's
      call must resolve.
    - (b) T-DEPENDENT helper (``fn id(@T -> @T)``): its signature/body reads
      the enclosing ``@T``, so it is monomorphized per-instantiation with a
      name aligned to the enclosing clone, and the clone's call resolves.
    """

    def test_t_independent_where_helper_runs(self) -> None:
        """(a) The #904 repro: a T-independent where-helper inside a generic.

        ``outer(99)`` instantiates ``outer<Int>``; the clone calls the
        T-independent ``helper(5)`` which returns 5.  Before the fix this
        crashed with ``unknown func: failed to find name $helper``.
        """
        source = """\
private forall<T> fn outer(@T -> @Int) requires(true) ensures(true) effects(pure)
{ helper(5) }
where {
  fn helper(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure) { outer(99) }
"""
        assert _run(source, fn="main") == 5

    def test_t_dependent_where_helper_runs(self) -> None:
        """(b) A where-helper whose signature/body reads the enclosing ``@T``.

        ``outer(7)`` instantiates ``outer<Int>``; the clone body calls the
        per-instantiation ``id(@T.0)`` (``id: @T -> @T``, here ``@Int -> @Int``)
        which returns its argument, 7.  Before the fix this crashed with
        ``unknown func: failed to find name $id``.
        """
        source = """\
private forall<T> fn outer(@T -> @T) requires(true) ensures(true) effects(pure)
{ id(@T.0) }
where {
  fn id(@T -> @T) requires(true) ensures(true) effects(pure) { @T.0 }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure) { outer(7) }
"""
        assert _run(source, fn="main") == 7

    def test_where_helper_multiple_instantiations(self) -> None:
        """Two instantiations of the same generic each resolve the helper.

        ``pick`` is instantiated at both ``Int`` and ``Bool``; each clone's
        ``dup`` helper (T-independent) must be emitted and resolved without a
        duplicate-definition collision between the two clones.
        """
        source = """\
private forall<T> fn pick(@T -> @Int) requires(true) ensures(true) effects(pure)
{ dup(3) }
where {
  fn dup(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 + @Int.0 }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure)
{
  let @Int = pick(10);
  let @Int = pick(true);
  @Int.0
}
"""
        # Both pick<Int> and pick<Bool> return dup(3) = 3 + 3 = 6; @Int.0 (most
        # recent) is pick<Bool>'s result, so each clone's helper must resolve.
        assert _run(source, fn="main") == 6

    def test_t_dependent_where_helper_two_instantiations(self) -> None:
        """A T-DEPENDENT helper monomorphized at two distinct concrete types.

        ``wrap<Int>`` and ``wrap<Bool>`` each get their own ``id`` clone; the
        Int one moves an i64, the Bool one an i32, so a single shared emission
        would be type-wrong — each clone must carry its own per-instantiation
        helper.
        """
        source = """\
private forall<T> fn wrap(@T -> @T) requires(true) ensures(true) effects(pure)
{ id(@T.0) }
where {
  fn id(@T -> @T) requires(true) ensures(true) effects(pure) { @T.0 }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure)
{
  let @Bool = wrap(true);
  let @Int = wrap(9);
  @Int.0
}
"""
        assert _run(source, fn="main") == 9

    def test_where_helper_sibling_call_in_generic(self) -> None:
        """A where-helper that calls a SIBLING where-helper, inside a generic.

        ``h1`` calls ``h2`` by bare name; both live inside the generic's
        ``where`` block.  Under monomorphization both bare sibling calls must
        be rewritten to the per-clone helper names so neither dangles.
        """
        source = """\
private forall<T> fn outer(@T -> @Int) requires(true) ensures(true) effects(pure)
{ h1(4) }
where {
  fn h1(@Int -> @Int) requires(true) ensures(true) effects(pure) { h2(@Int.0) + 1 }
  fn h2(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 * 10 }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure) { outer(0) }
"""
        # h1(4) = h2(4) + 1 = 40 + 1 = 41
        assert _run(source, fn="main") == 41

    def test_non_generic_where_helper_still_runs(self) -> None:
        """Regression: a NON-generic fn with a where-block still compiles+runs.

        This path (helper emitted alongside its compilable parent) must be
        left intact by the #904 fix.
        """
        source = """\
private fn ng(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ h1(@Int.0) }
where {
  fn h1(@Int -> @Int) requires(true) ensures(true) effects(pure) { h2(@Int.0) }
  fn h2(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure) { ng(42) }
"""
        assert _run(source, fn="main") == 42

    def test_generic_without_where_still_runs(self) -> None:
        """Regression: a generic with NO where-block still monomorphizes+runs."""
        source = """\
private forall<T> fn identity(@T -> @T) requires(true) ensures(true) effects(pure)
{ @T.0 }
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure)
{ identity(55) }
"""
        assert _run(source, fn="main") == 55

    def test_where_helper_calls_another_generic(self) -> None:
        """A where-helper body that calls a DIFFERENT top-level generic.

        ``helper`` (inside ``outer<T>``'s where block) calls ``inner<Int>``.
        That transitive generic instantiation must be discovered from the
        where-fn body (the transitive scan runs on the clone with its
        ``where_fns`` still attached, before hoisting), so ``inner$Int`` exists
        and the hoisted helper's call resolves to it.
        """
        source = """\
private forall<U> fn inner(@U -> @U) requires(true) ensures(true) effects(pure)
{ @U.0 }
private forall<T> fn outer(@T -> @Int) requires(true) ensures(true) effects(pure)
{ helper(5) }
where {
  fn helper(@Int -> @Int) requires(true) ensures(true) effects(pure)
  { inner(@Int.0) }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure)
{ outer(99) }
"""
        assert _run(source, fn="main") == 5


class TestNestedWhereHelperEmission978:
    """#978 — a where-helper's OWN where-helpers must be emitted (non-generic).

    A non-generic ``fn outer { ... } where { fn child { ... } where { fn
    grandchild ... } }`` passes ``vera check`` and ``vera verify`` but crashed
    at codegen: the Pass-2 emission loop compiled only ONE level of
    ``decl.where_fns`` (``child``), never a helper's OWN ``where_fns``
    (``grandchild``).  The checker (`_check_fn`), verifier (`_verify_fn`), and
    registration (`_register_fn`) all recurse into nested ``where`` blocks, so
    ``grandchild``'s NAME is registered — ``child``'s body lowers its call to
    ``return_call $grandchild`` — but the body was never emitted, so WAT
    assembly failed with ``unknown func: $grandchild``.  The generic path was
    unaffected: ``monomorphize._hoist_where_fns_under`` recurses.

    The run-level values distinguish the leaf actually executing from any
    default/passthrough: each level transforms its argument non-trivially.
    """

    def test_nested_where_grandchild_runs(self) -> None:
        """The #978 repro: outer → child → grandchild, all non-generic.

        ``outer(10)`` → ``child(10)`` → ``grandchild(10 + 1)`` → ``11 * 2`` =
        22.  Before the fix this failed to compile (``unknown func:
        $grandchild``); the ``* 2`` on ``arg + 1`` makes 22 reachable only if
        ``grandchild`` genuinely runs (a default/passthrough would not give 22).
        """
        source = """\
public fn outer(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ child(@Int.0) }
where {
  fn child(@Int -> @Int) requires(true) ensures(true) effects(pure)
  { grandchild(@Int.0 + 1) }
  where {
    fn grandchild(@Int -> @Int) requires(true) ensures(true) effects(pure)
    { @Int.0 * 2 }
  }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure)
{ outer(10) }
"""
        assert _run(source, fn="main") == 22

    def test_nested_where_three_levels_run(self) -> None:
        """Three levels of nesting: outer → a → b → c, all non-generic.

        ``outer(5)`` → ``a(5)`` → ``b(5 + 1)`` → ``c(6 + 10)`` → ``16 * 3`` =
        48.  Before the fix this failed at ``unknown func: $b`` (only ``a``,
        outer's direct helper, was emitted).
        """
        source = """\
public fn outer(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ a(@Int.0) }
where {
  fn a(@Int -> @Int) requires(true) ensures(true) effects(pure)
  { b(@Int.0 + 1) }
  where {
    fn b(@Int -> @Int) requires(true) ensures(true) effects(pure)
    { c(@Int.0 + 10) }
    where {
      fn c(@Int -> @Int) requires(true) ensures(true) effects(pure)
      { @Int.0 * 3 }
    }
  }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure)
{ outer(5) }
"""
        assert _run(source, fn="main") == 48

    def test_generic_parent_nested_where_still_runs(self) -> None:
        """Control (pin): the generic-parent path already emits nested helpers.

        ``monomorphize._hoist_where_fns_under`` recurses, so a ``forall<T>``
        parent carrying a nested ``where`` block was never affected by #978.
        ``outer<Int>(99)`` → ``child(5)`` → ``grandchild(5 + 1)`` → ``6 * 2`` =
        12.  This must stay green through the non-generic-path fix.
        """
        source = """\
private forall<T> fn outer(@T -> @Int) requires(true) ensures(true) effects(pure)
{ child(5) }
where {
  fn child(@Int -> @Int) requires(true) ensures(true) effects(pure)
  { grandchild(@Int.0 + 1) }
  where {
    fn grandchild(@Int -> @Int) requires(true) ensures(true) effects(pure)
    { @Int.0 * 2 }
  }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure)
{ outer(99) }
"""
        assert _run(source, fn="main") == 12

    # -- PR #989 review: ability-op rewrite must recurse into grandchildren ---
    #
    # The #978 emission-loop fix flattens `decl.where_fns` at any depth so a
    # grandchild's body IS handed to `_compile_fn`.  But Pass 1.6
    # (`_rewrite_where_fns`, called from `_rewrite_ability_ops`) only rewrote
    # each DIRECT child's body + contracts, never recursing into
    # `wfn.where_fns`.  So a grandchild using `eq`/`compare` kept a raw FnCall
    # to the unregistered ability op; `_compile_fn` tripped CodegenSkip and
    # returned None, the body was silently dropped, and the parent's
    # `return_call $grandchild` dangled (`unknown func`).  The values below are
    # chosen so a passthrough/default can't coincide with the leaf result.

    def test_nested_where_grandchild_eq_body_runs(self) -> None:
        """#989 (probeF1): a grandchild using `eq` in its BODY must compile.

        ``outer(5)`` → ``child(5)`` → ``grandchild(5)`` → ``eq(5, 5)`` = true
        (1).  Before the ability-op recursion, ``grandchild``'s raw ``eq(...)``
        was never rewritten, so its body was dropped and ``child``'s
        ``return_call $grandchild`` dangled (``unknown func: $grandchild``).
        """
        source = """\
public fn outer(@Int -> @Bool) requires(true) ensures(true) effects(pure)
{ child(@Int.0) }
where {
  fn child(@Int -> @Bool) requires(true) ensures(true) effects(pure)
  { grandchild(@Int.0) }
  where {
    fn grandchild(@Int -> @Bool) requires(true) ensures(true) effects(pure)
    { eq(@Int.0, 5) }
  }
}
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ outer(5) }
"""
        assert _run(source, fn="main") == 1

    def test_nested_where_grandchild_compare_contract_runs(self) -> None:
        """#989 (probeF2): a grandchild using `eq` in its CONTRACT must compile.

        ``grandchild``'s ``ensures(eq(@Int.result, @Int.result))`` is a
        contract-position ability op; the same Pass 1.6 rewrite must reach a
        grandchild's contracts, not just its body.  ``outer(7)`` returns 7 (the
        body is a passthrough), which is unreachable if ``grandchild``'s
        contract ``eq`` dangles at codegen.
        """
        source = """\
public fn outer(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ child(@Int.0) }
where {
  fn child(@Int -> @Int) requires(true) ensures(true) effects(pure)
  { grandchild(@Int.0) }
  where {
    fn grandchild(@Int -> @Int)
      requires(true)
      ensures(eq(@Int.result, @Int.result))
      effects(pure)
    { @Int.0 }
  }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure)
{ outer(7) }
"""
        assert _run(source, fn="main") == 7

    def test_nested_where_grandchild_compare_body_runs(self) -> None:
        """#989 (probeF4): a grandchild using `compare` in its BODY must compile.

        ``outer(9)`` → ``child(9)`` → ``grandchild(9)`` →
        ``match compare(9, 5) { Less->1, Equal->2, Greater->3 }`` = 3.  The
        ``Greater`` arm (3) is reachable only if ``compare`` lowered to the
        three-way ``if`` inside the grandchild — a dropped body would dangle.
        """
        source = """\
public fn outer(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ child(@Int.0) }
where {
  fn child(@Int -> @Int) requires(true) ensures(true) effects(pure)
  { grandchild(@Int.0) }
  where {
    fn grandchild(@Int -> @Int) requires(true) ensures(true) effects(pure)
    { match compare(@Int.0, 5) { Less -> 1, Equal -> 2, Greater -> 3 } }
  }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure)
{ outer(9) }
"""
        assert _run(source, fn="main") == 3

    def test_nested_where_branching_helpers_run(self) -> None:
        """#989 (test-analyzer): a node with TWO nested helpers emits BOTH.

        ``outer(10)`` → ``ha(10)`` → ``ha1(10) + ha2(10)`` → ``20 + 30`` = 50.
        Both sibling grandchildren are load-bearing, so the shape kills a
        drop-non-first-nested-subtree mutant (``[:1]`` on the flatten stack →
        ``ha2`` never emitted → ``unknown func: $ha2``) and a leftmost-path
        mutant.
        """
        source = """\
public fn outer(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ ha(@Int.0) }
where {
  fn ha(@Int -> @Int) requires(true) ensures(true) effects(pure)
  { ha1(@Int.0) + ha2(@Int.0) }
  where {
    fn ha1(@Int -> @Int) requires(true) ensures(true) effects(pure)
    { @Int.0 * 2 }
    fn ha2(@Int -> @Int) requires(true) ensures(true) effects(pure)
    { @Int.0 * 3 }
  }
}
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure)
{ outer(10) }
"""
        assert _run(source, fn="main") == 50


# =====================================================================
# #913: monomorphization DISCOVERY misses two call shapes
# =====================================================================


class TestGenericPipeMonomorphization:
    """A generic called via the ``|>`` pipe must be discovered and its type
    argument inferred from the piped value — exactly as a direct call is.

    Pre-fix, discovery walked the pipe's RHS ``FnCall`` with its *literal*
    (empty) argument list, so ``T`` never bound and no ``ident$Int`` clone was
    emitted; codegen then lowered ``42 |> ident()`` to ``call $ident$Int`` on a
    function that doesn't exist and the enclosing fn was dropped at run (#913).
    """

    _IDENT = (
        "private forall<T> fn ident(@T -> @T)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @T.0 }\n"
    )

    def test_pipe_int(self) -> None:
        """``42 |> ident()`` runs and returns 42 (was: ident$Int not
        registered → function dropped)."""
        source = self._IDENT + (
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 42 |> ident() }\n"
        )
        assert _run(source, fn="main") == 42

    def test_pipe_string(self) -> None:
        """``\"hi\" |> ident()`` resolves ident$String; length probe = 2."""
        source = self._IDENT + (
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ string_length(\"hi\" |> ident()) }\n"
        )
        # 2 cannot coincide with a 0 fallback / dropped-fn default.
        assert _run(source, fn="main") == 2

    def test_pipe_chained(self) -> None:
        """A chained pipe ``5 |> ident() |> ident()`` resolves ident$Int on
        both stages and returns 5."""
        source = self._IDENT + (
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 5 |> ident() |> ident() }\n"
        )
        assert _run(source, fn="main") == 5

    def test_pipe_two_instantiations_one_program(self) -> None:
        """Two distinct pipe instantiations of the same generic in one program
        each resolve (ident$Int and ident$Bool)."""
        source = self._IDENT + (
            "public fn ints(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 42 |> ident() }\n"
            "public fn bools(@Unit -> @Bool)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ true |> ident() }\n"
        )
        assert _run(source, fn="ints") == 42
        assert _run(source, fn="bools") == 1

    def test_pipe_with_explicit_extra_arg(self) -> None:
        """A pipe into a two-parameter generic prepends the piped value as the
        FIRST argument; the second arg is written explicitly."""
        source = (
            "private forall<T> fn first(@T, @T -> @T)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @T.1 }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 7 |> first(9) }\n"
        )
        # first(7, 9) returns @T.1 = the first (least-recent) arg = 7.
        assert _run(source, fn="main") == 7

    def test_direct_call_still_runs(self) -> None:
        """Regression: the direct call form keeps working unchanged."""
        source = self._IDENT + (
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ ident(42) }\n"
        )
        assert _run(source, fn="main") == 42

    def test_non_generic_pipe_still_runs(self) -> None:
        """Regression: a pipe into a NON-generic fn is unaffected."""
        source = (
            "private fn inc(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 + 1 }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 41 |> inc() }\n"
        )
        assert _run(source, fn="main") == 42


class TestGenericClosureTypeVarSubstitution:
    """A ``@T`` closure parameter inside a ``forall<T>`` body must be
    substituted with the concrete type argument during monomorphization.

    Pre-fix, the generic TEMPLATE itself was body-compiled (its ``Array<T>``
    params look compilable as i32_pair), which lifted its ``@T`` closure and
    hit the hard ``closure parameter has unsupported WASM type`` invariant
    ([E699]) at run — even though the emitted clone ``map_ident$Int`` is fine
    (#913)."""

    def test_generic_body_closure_type_var(self) -> None:
        """``forall<T>`` body maps an ``@T``-param closure over ``Array<T>``;
        instantiated at Int it runs (was: [E699])."""
        source = (
            "private forall<T> fn map_ident(@Array<T> -> @Array<T>)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ array_map(@Array<T>.0, fn(@T -> @T) effects(pure) { @T.0 }) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ array_length(map_ident([10, 20, 30])) }\n"
        )
        assert _run(source, fn="main") == 3

    def test_generic_body_closure_no_e699(self) -> None:
        """The compile must not surface an [E699] for the generic template."""
        source = (
            "private forall<T> fn map_ident(@Array<T> -> @Array<T>)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ array_map(@Array<T>.0, fn(@T -> @T) effects(pure) { @T.0 }) }\n"
            "public fn main(@Unit -> @Array<Int>)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ map_ident([1, 2, 3]) }\n"
        )
        result = _compile(source)
        assert not [d for d in result.diagnostics if d.error_code == "E699"], (
            "generic template with an @T closure must not raise [E699]: "
            f"{[(d.error_code, d.description) for d in result.diagnostics]}"
        )

    def test_generic_array_arg_binds_from_element_type(self) -> None:
        """A generic over ``Array<T>`` given an array literal binds ``T`` from
        the element type — the WASM call-rewrite consultor must agree with
        instantiation discovery on ``firstlen$Int`` (was: call rewritten to a
        never-emitted ``firstlen$Bool``, dropping the caller)."""
        source = (
            "private forall<T> fn firstlen(@Array<T> -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ array_length(@Array<T>.0) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ firstlen([1, 2, 3]) }\n"
        )
        assert _run(source, fn="main") == 3

    def test_generic_closure_compiles_with_no_warnings(self) -> None:
        """#913 review: a CORRECT generic-closure program compiles with ZERO
        warnings.

        The closure-param skip emits an [E602] whose description names the
        closure (not the enclosing fn), so the #604 description-prefix filter
        missed it and it leaked on a program that runs perfectly.  The #604
        filter's forall-origin arm now suppresses it once a clone compiles.
        """
        source = (
            "private forall<T> fn map_ident(@Array<T> -> @Array<T>)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ array_map(@Array<T>.0, fn(@T -> @T) effects(pure) { @T.0 }) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ array_length(map_ident([10, 20, 30])) }\n"
        )
        result = _compile(source)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert warnings == [], (
            "a correct generic-closure program must compile with no warnings: "
            f"{[(w.error_code, w.description) for w in warnings]}"
        )
        # The program must still export and run — suppression must not have
        # come from dropping the whole program.
        assert _run(source, fn="main") == 3

    def test_uninstantiated_generic_closure_still_warns(self) -> None:
        """#913 review: the suppression stays CONDITIONAL — a generic-closure
        template that is NEVER instantiated (no clone compiles) keeps its
        [E602] skip-warning, the honest signal it cannot compile.

        This is the guard that the forall-origin suppression is gated on
        ``mono_compiled`` (a clone actually compiled), not unconditional.
        """
        source = (
            "private forall<T> fn map_ident(@Array<T> -> @Array<T>)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ array_map(@Array<T>.0, fn(@T -> @T) effects(pure) { @T.0 }) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 42 }\n"
        )
        result = _compile(source)
        e602 = [d for d in result.diagnostics if d.error_code == "E602"]
        assert e602, (
            "an uninstantiated generic-closure template must keep its E602 "
            "skip-warning (suppression must stay conditional on a clone "
            f"compiling): {[d.description for d in result.diagnostics]}"
        )


# =====================================================================
# #769: monomorphizer completeness — builtin return tables, nested
# type-argument unification, scope-aware De Bruijn reindexing
# =====================================================================


def _transform_program(source: str):
    """Parse + transform a source string to a Program (no check/codegen)."""
    import tempfile

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    try:
        tree = parse_file(path)
        return transform(tree)
    finally:
        Path(path).unlink(missing_ok=True)


def _mono_fn(source: str, fn_name: str, concrete: tuple[str, ...]):
    """Transform ``source``, find FnDecl ``fn_name``, monomorphize it.

    Drives the public ``Monomorphizer.monomorphize_fn`` contract exactly the
    way both consumers do (#732): on the transform-level AST, with a
    context-free ``MonoContext`` (the reindex logic needs no registration
    state).
    """
    from vera import ast as vera_ast
    from vera.monomorphize import MonoContext, Monomorphizer

    program = _transform_program(source)
    decl = next(
        tld.decl for tld in program.declarations
        if isinstance(tld.decl, vera_ast.FnDecl) and tld.decl.name == fn_name
    )
    ctx = MonoContext(
        generic_decls={}, ctor_to_adt={}, ctor_tp_indices={},
        adt_tp_counts={}, type_aliases={}, type_alias_params={},
        fn_ret_types={},
    )
    return Monomorphizer(ctx).monomorphize_fn(decl, concrete)


def _slot_sigs(node) -> list[tuple[str, int]]:
    """(canonical slot name, De Bruijn index) for every SlotRef under
    ``node``, in deterministic dataclass-field order.

    Uses the shared namer ``vera.slots.slot_ref_name`` — the same key both
    codegen and the verifier resolve against — so an assertion here is an
    assertion about what the consumers will actually look up.
    """
    from dataclasses import fields as dc_fields

    from vera import ast as vera_ast
    from vera.slots import slot_ref_name

    out: list[tuple[str, int]] = []

    def walk(v: object) -> None:
        if isinstance(v, vera_ast.SlotRef):
            name = slot_ref_name(v)
            assert name is not None
            out.append((name, v.index))
        if isinstance(v, vera_ast.Node):
            for fld in dc_fields(v):
                if fld.name == "span":
                    continue
                walk(getattr(v, fld.name))
        elif isinstance(v, tuple):
            for item in v:
                walk(item)

    walk(node)
    return out


class TestBuiltinReturnTables769:
    """#769 gap 1 (+1b): the two builtin return-type tables in
    ``vera.monomorphize`` must cover every builtin the registry says has a
    concrete return, or generic instantiation discovery falls through to the
    ``Bool`` phantom default while the WASM call-rewrite side infers the real
    type — mismatched clone names, dangling calls, dropped ``main``.

    The registry (``TypeEnv._register_builtins``) is the source of truth for
    KEY coverage; the WASM inference chain's historical values are the source
    of truth for simple-name VALUES (clone-name agreement is the invariant,
    not name precision — see the ``string_length`` → "Int" pin).
    """

    @staticmethod
    def _registry():
        from vera.environment import TypeEnv

        return TypeEnv().functions

    @staticmethod
    def _contains_typevar(ty) -> bool:
        from vera import types as vtypes

        if isinstance(ty, vtypes.TypeVar):
            return True
        if isinstance(ty, vtypes.AdtType):
            return any(
                TestBuiltinReturnTables769._contains_typevar(a)
                for a in ty.type_args
            )
        if isinstance(ty, vtypes.RefinedType):
            return TestBuiltinReturnTables769._contains_typevar(ty.base)
        if isinstance(ty, vtypes.FunctionType):
            return (
                any(
                    TestBuiltinReturnTables769._contains_typevar(p)
                    for p in ty.params
                )
                or TestBuiltinReturnTables769._contains_typevar(ty.return_type)
            )
        return False

    def test_parameterized_table_matches_registry(self) -> None:
        """STRICT equality: the parameterized table holds exactly the
        builtins whose registry return is an ``AdtType`` with type args and
        no embedded ``TypeVar`` — no gaps (the #769 miss) and no generic
        returns (which would bind phantom vars)."""
        from vera import types as vtypes
        from vera.monomorphize import _BUILTIN_PARAMETERIZED_RETURNS

        expected: dict[str, tuple[str, tuple[str, ...]]] = {}
        for name, info in self._registry().items():
            ret = info.return_type
            if (
                isinstance(ret, vtypes.AdtType)
                and ret.type_args
                and not self._contains_typevar(ret)
            ):
                expected[name] = (
                    ret.name,
                    tuple(vtypes.pretty_type(a) for a in ret.type_args),
                )
        missing = sorted(set(expected) - set(_BUILTIN_PARAMETERIZED_RETURNS))
        extra = sorted(set(_BUILTIN_PARAMETERIZED_RETURNS) - set(expected))
        wrong = sorted(
            n for n in set(expected) & set(_BUILTIN_PARAMETERIZED_RETURNS)
            if expected[n] != _BUILTIN_PARAMETERIZED_RETURNS[n]
        )
        assert not missing and not extra and not wrong, (
            f"_BUILTIN_PARAMETERIZED_RETURNS out of sync with the registry —"
            f" missing: {missing}; extra (would bind phantom vars): {extra};"
            f" wrong values: {wrong}"
        )

    def test_parameterized_table_pins(self) -> None:
        """Readable spot pins for the #769 families (incl. nested inners and
        the ``array_range`` special-case fold-in)."""
        from vera.monomorphize import _BUILTIN_PARAMETERIZED_RETURNS as T

        assert T.get("string_chars") == ("Array", ("String",))
        assert T.get("string_split") == ("Array", ("String",))
        assert T.get("md_extract_code_blocks") == ("Array", ("String",))
        assert T.get("string_index_of") == ("Option", ("Nat",))
        assert T.get("regex_find_all") == ("Result", ("Array<String>", "String"))
        assert T.get("json_as_object") == ("Option", ("Map<String, Json>",))
        assert T.get("array_range") == ("Array", ("Int",))

    def test_simple_table_covers_all_concrete_outer_returns(self) -> None:
        """KEY completeness: every registry builtin whose return has a
        concrete OUTER constructor (primitive, or ADT even with generic
        args — cf. ``map_keys`` → "Array") must have a simple-name entry, so
        discovery never phantom-defaults where the call-rewrite infers a
        name.  Bare-``TypeVar`` returns must have NO entry."""
        from vera import types as vtypes
        from vera.monomorphize import _BUILTIN_VERA_RETURN_TYPES

        required: list[str] = []
        forbidden: list[str] = []
        for name, info in self._registry().items():
            ret = info.return_type
            if isinstance(ret, vtypes.RefinedType):
                ret = ret.base
            if isinstance(ret, vtypes.TypeVar):
                forbidden.append(name)
            elif isinstance(ret, (vtypes.PrimitiveType, vtypes.AdtType)):
                required.append(name)
        missing = sorted(
            n for n in required if n not in _BUILTIN_VERA_RETURN_TYPES
        )
        phantom = sorted(
            n for n in forbidden if n in _BUILTIN_VERA_RETURN_TYPES
        )
        assert not missing, (
            f"builtins with concrete outer returns absent from "
            f"_BUILTIN_VERA_RETURN_TYPES (discovery phantom-defaults, the "
            f"rewrite side does not — #769 desync): {missing}"
        )
        assert not phantom, (
            f"TypeVar-returning builtins must not have fixed entries: "
            f"{phantom}"
        )

    def test_simple_table_values_chain_parity(self) -> None:
        """VALUE pins: the simple names must equal what the WASM call-rewrite
        chain historically produced (clone-name agreement, warts included —
        ``string_length`` is "Int" not "Nat" there, ``string_char_code`` is
        "Nat").  Changing these is a clone-granularity decision out of #769's
        scope; agreement is the invariant."""
        from vera.monomorphize import _BUILTIN_VERA_RETURN_TYPES as S

        assert S.get("string_chars") == "Array"
        assert S.get("string_split") == "Array"
        assert S.get("string_length") == "Int"
        assert S.get("string_char_code") == "Nat"
        assert S.get("parse_int") == "Result"
        assert S.get("int_to_string") == "String"
        assert S.get("base64_decode") == "Result"
        assert S.get("md_parse") == "Result"

    def test_simple_and_parameterized_tables_agree_on_outer(self) -> None:
        """Internal consistency: where both tables carry a builtin, the
        simple name equals the parameterized entry's outer name."""
        from vera.monomorphize import (
            _BUILTIN_PARAMETERIZED_RETURNS,
            _BUILTIN_VERA_RETURN_TYPES,
        )

        disagree = sorted(
            n for n, (outer, _) in _BUILTIN_PARAMETERIZED_RETURNS.items()
            if n in _BUILTIN_VERA_RETURN_TYPES
            and _BUILTIN_VERA_RETURN_TYPES[n] != outer
        )
        assert not disagree, f"outer-name disagreement: {disagree}"


class TestScopeAwareReindex769:
    """#769 gap 3 (unit level): when type variables collapse to one concrete
    type, De Bruijn indices must be recomputed against the FULL binding
    scope at each reference site — parameters, ``let`` bindings, match-arm
    binders, and closure parameters, with contracts staying a params-only
    scope — not via a static params-only map applied body-wide.

    Assertions use ``vera.slots.slot_ref_name`` (the shared full-depth
    namer), i.e. exactly the keys codegen and the verifier resolve, and the
    public ``monomorphize_fn`` contract both consumers call (#732).
    """

    _BODY_LET = """\
private forall<A, B> fn confuse(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{
  let @B = @B.0;
  @A.0
}
"""

    def test_body_let_two_var_collapse(self) -> None:
        """A body ``let`` of a collapsing type interposes one extra binding:
        the trailing ``@A.0`` must land on index 2 (let, param B, param A),
        not the params-only 1."""
        mono = _mono_fn(self._BODY_LET, "confuse", ("Int", "Int"))
        assert _slot_sigs(mono.body) == [("Int", 0), ("Int", 2)], (
            f"got {_slot_sigs(mono.body)} — the params-only reindex map is "
            f"blind to the body let (#769 gap 3)"
        )

    def test_single_var_concrete_body_let(self) -> None:
        """The gap needs no second type variable: a body ``let`` of the
        CONCRETE target type interposes just the same.  ``@A.0`` after
        ``let @Int`` must become ``@Int.1``, else it silently reads the
        let-bound value."""
        source = """\
private forall<A> fn keep(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 5;
  @A.0
}
"""
        mono = _mono_fn(source, "keep", ("Int",))
        assert _slot_sigs(mono.body) == [("Int", 1)], (
            f"got {_slot_sigs(mono.body)} — @A.0 was left at index 0 and now "
            f"resolves to the let binding, not the parameter"
        )

    def test_branch_let_does_not_leak(self) -> None:
        """A ``let`` inside an if-branch block is popped at block exit: the
        trailing ``@A.0`` must stay index 0 (the branch's ``let @Int`` never
        reaches its scope).  Kills the leak-block-scopes mutation — a walker
        that forgets the block pop counts the branch let and mis-shifts every
        later reference."""
        source = """\
private forall<A> fn branchy(@A, @Bool -> @A)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = if @Bool.0 then { let @Int = 5; true } else { false };
  @A.0
}
"""
        mono = _mono_fn(source, "branchy", ("Int",))
        sigs = _slot_sigs(mono.body)
        assert sigs == [("Bool", 0), ("Int", 0)], (
            f"got {sigs} — a branch-scoped let leaked into the enclosing "
            f"scope's reindex (#769 gap 3)"
        )

    def test_match_binder_scope(self) -> None:
        """A match-arm binder shifts references INSIDE that arm only: the
        ``Some`` arm's ``@A.0`` needs index 2 (binder, param B, param A);
        the ``None`` arm's needs 1.  One function, two correct answers —
        unrepresentable in a single static (name, index) map."""
        source = """\
private forall<A, B> fn pick(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{
  match Some(@B.0) {
    Some(@B) -> @A.0,
    None -> @A.0
  }
}
"""
        mono = _mono_fn(source, "pick", ("Int", "Int"))
        sigs = _slot_sigs(mono.body)
        assert sigs == [("Int", 0), ("Int", 2), ("Int", 1)], (
            f"got {sigs} — expected scrutinee @B.0 -> 0, Some-arm @A.0 -> 2 "
            f"(arm binder interposes), None-arm @A.0 -> 1"
        )

    def test_closure_param_scope(self) -> None:
        """A closure parameter of a collapsing type interposes for
        references inside the closure body: ``@A.0`` there needs index 2
        (closure param, param B, param A)."""
        source = """\
private forall<A, B> fn via(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(fn(@B -> @A) effects(pure) { @A.0 }, @B.0)
}
"""
        mono = _mono_fn(source, "via", ("Int", "Int"))
        sigs = _slot_sigs(mono.body)
        assert sigs == [("Int", 2), ("Int", 0)], (
            f"got {sigs} — expected closure-body @A.0 -> 2 (closure param "
            f"interposes), argument @B.0 -> 0 (evaluated outside the "
            f"closure scope)"
        )

    def test_contracts_stay_params_only_scope(self) -> None:
        """Contracts are checked against a params-only scope (they are
        evaluated at the boundary, before/after the body): the ensures
        ``@A.0`` must be index 1 even though the body's trailing ``@A.0``
        is 2 (body let interposes there).  Guards the scope-aware walker
        against naively counting body binders into contract references."""
        source = """\
private forall<A, B> fn guarded(@A, @B -> @A)
  requires(true)
  ensures(@A.result == @A.0)
  effects(pure)
{
  let @B = @B.0;
  @A.0
}
"""
        mono = _mono_fn(source, "guarded", ("Int", "Int"))
        contract_sigs = _slot_sigs(mono.contracts)
        body_sigs = _slot_sigs(mono.body)
        assert contract_sigs == [("Int", 1)], (
            f"got {contract_sigs} — ensures @A.0 must resolve in the "
            f"params-only scope (index 1)"
        )
        assert body_sigs == [("Int", 0), ("Int", 2)], (
            f"got {body_sigs} — body @A.0 must count the interposed let "
            f"(index 2)"
        )

    def test_nested_type_arg_slot_names_collapse(self) -> None:
        """``Array<Option<A>>`` / ``Array<Option<B>>`` are DISTINCT slot
        namespaces pre-mono and the SAME one post-mono at A=B=Int — the
        one-level name truncation ("Array<Option>") must not hide the
        collapse.  Both the requires ref and the body ref (params-only
        scopes) must move to index 1 (param B is the more recent
        ``Array<Option<Int>>``)."""
        source = """\
private forall<A, B> fn confuse2(@Array<Option<A>>, @Array<Option<B>> -> @Option<A>)
  requires(array_length(@Array<Option<A>>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<Option<A>>.0[0]
}
"""
        mono = _mono_fn(source, "confuse2", ("Int", "Int"))
        contract_sigs = _slot_sigs(mono.contracts)
        body_sigs = _slot_sigs(mono.body)
        assert contract_sigs == [("Array<Option<Int>>", 1)], (
            f"got {contract_sigs} — the requires ref must follow the "
            f"full-depth name collapse (#769 gap 3, truncation half)"
        )
        assert body_sigs == [("Array<Option<Int>>", 1)], (
            f"got {body_sigs} — the body ref must follow the full-depth "
            f"name collapse (#769 gap 3, truncation half)"
        )

    def test_no_collapse_leaves_indices_unchanged(self) -> None:
        """Distinct concrete targets (A=Int, B=String) collapse nothing:
        every index survives unchanged.  Guards the walker's fast path."""
        mono = _mono_fn(self._BODY_LET, "confuse", ("Int", "String"))
        assert _slot_sigs(mono.body) == [("String", 0), ("Int", 0)], (
            f"got {_slot_sigs(mono.body)} — no-collapse monomorphization "
            f"must not move any index"
        )


class TestNestedArgTypeInfo769:
    """#769 gap 2 (unit level, argument side): ``_get_arg_type_info`` must
    surface FULL-DEPTH element names for nested literals so the recursive
    unifier has something to bind against."""

    def test_nested_array_literal_element_name(self) -> None:
        from vera import ast as vera_ast
        from vera.monomorphize import MonoContext, Monomorphizer

        program = _transform_program("""\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Int>> = [[100, 3]];
  0
}
""")
        arrays: list = []

        def find(v: object) -> None:
            from dataclasses import fields as dc_fields
            if isinstance(v, vera_ast.ArrayLit):
                arrays.append(v)
            if isinstance(v, vera_ast.Node):
                for fld in dc_fields(v):
                    if fld.name != "span":
                        find(getattr(v, fld.name))
            elif isinstance(v, tuple):
                for item in v:
                    find(item)

        find(program)
        outer = next(
            a for a in arrays
            if a.elements and isinstance(a.elements[0], vera_ast.ArrayLit)
        )
        ctx = MonoContext(
            generic_decls={}, ctor_to_adt={}, ctor_tp_indices={},
            adt_tp_counts={}, type_aliases={}, type_alias_params={},
            fn_ret_types={},
        )
        info = Monomorphizer(ctx)._get_arg_type_info(outer, {})
        assert info == ("Array", ("Array<Int>",)), (
            f"got {info} — a nested array literal must expose its element "
            f"type full-depth so Array<Array<E>> can bind E (#769 gap 2)"
        )


class TestMonomorphizerCompleteness769:
    """#769 end-to-end: the three completeness gaps, each driven through
    compile + execute with expected values that CANNOT coincide with the
    ``Bool`` phantom default (strings, and 100-vs-3 non-commutative picks).

    Codegen and the verifier share the ``Monomorphizer``, so ``vera verify``
    is green on every one of these while the pre-fix runtime behavior is a
    trap, a dropped ``main``, or a silently wrong answer — the
    agree-but-wrong signature the issue documents.
    """

    _IO = """\
effect IO {
  op print(String -> Unit);
}

"""

    # -- gap 1: parameterized builtin return in generic-arg position --------

    _FIRST_CHARS = _IO + """\
private forall<T> fn first(@Array<T> -> @T)
  requires(array_length(@Array<T>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<T>.0[0]
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(first(string_chars("abc")))
}
"""

    def test_builtin_parameterized_return_runs(self) -> None:
        """``first(string_chars("abc"))`` must bind T=String and print "a".
        Pre-fix both sides agree on the wrong ``first$Bool`` clone and the
        emitted module fails WASM validation at run time."""
        out = _run_io(self._FIRST_CHARS, fn="main")
        assert out.strip() == "a", (
            f"expected 'a'; got {out!r} — string_chars' Array<String> return "
            f"did not bind T (#769 gap 1)"
        )

    def test_builtin_parameterized_return_mangles_string(self) -> None:
        result = _compile_ok(self._FIRST_CHARS)
        wat = result.wat or ""
        assert "$first$String" in wat
        assert "$first$Bool" not in wat, (
            "phantom Bool clone emitted — _BUILTIN_PARAMETERIZED_RETURNS is "
            "missing string_chars (#769 gap 1)"
        )

    # -- gap 1b: simple-name divergence (discovery vs call-rewrite) ---------

    _IDENT_SCALAR = _IO + """\
private forall<T> fn ident(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(ident(int_to_string(42)))
}
"""

    _IDENT_CONTAINER = _IO + """\
private forall<T> fn ident(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(to_string(array_length(ident(string_chars("abc")))))
}
"""

    def test_builtin_simple_return_scalar_runs(self) -> None:
        """``ident(int_to_string(42))`` at a bare ``@T`` formal: discovery
        must bind T=String exactly like the call-rewrite chain does.
        Pre-fix discovery phantom-defaults to Bool while the rewrite mangles
        ``ident$String`` — dangling clone, ``main`` dropped (#769 gap 1b)."""
        out = _run_io(self._IDENT_SCALAR, fn="main")
        assert out.strip() == "42", (
            f"expected '42'; got {out!r} — simple-name table diverged from "
            f"the call-rewrite chain (#769 gap 1b)"
        )

    def test_builtin_simple_return_container_runs(self) -> None:
        """Same divergence, container family: ``ident(string_chars(...))``
        must bind T=Array on BOTH sides."""
        out = _run_io(self._IDENT_CONTAINER, fn="main")
        assert out.strip() == "3", (
            f"expected '3'; got {out!r} — simple-name table diverged from "
            f"the call-rewrite chain (#769 gap 1b)"
        )

    def test_builtin_simple_return_no_skip_notes(self) -> None:
        """Compile-time discriminator for the desync: no dangling-clone
        skip notes, and the call site must reference ``$ident$String``."""
        result = _compile_ok(self._IDENT_SCALAR)
        wat = result.wat or ""
        assert "$ident$String" in wat
        assert "$ident$Bool" not in wat, (
            "discovery emitted the phantom Bool clone the rewrite never "
            "calls (#769 gap 1b)"
        )
        skip_notes = [
            d for d in result.diagnostics
            if "function skipped" in str(d.description)
            or "No exported functions" in str(d.description)
        ]
        assert not skip_notes, (
            f"main was dropped over a dangling clone: "
            f"{[str(d.description) for d in skip_notes]}"
        )

    # -- gap 2: nested type-argument unification ----------------------------

    _HEAD_HEAD = _IO + """\
private forall<E> fn head_head(@Array<Array<E>> -> @E)
  requires(
    array_length(@Array<Array<E>>.0) > 0
      && array_length(@Array<Array<E>>.0[0]) > 0
  )
  ensures(true)
  effects(pure)
{
  @Array<Array<E>>.0[0][0]
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Array<Int>> = [[100, 3]];
  let @Int = head_head(@Array<Array<Int>>.0);
  IO.print(to_string(@Int.0))
}
"""

    def test_nested_unification_runs(self) -> None:
        """``Array<Array<E>>`` matched against ``Array<Array<Int>>`` must
        bind E=Int at depth 2.  Pre-fix E stays unbound, the Bool clone is
        instantiated (the E521 warning literally names ``head_head<Bool>``)
        and the run traps on the i64/i32 ABI mismatch."""
        out = _run_io(self._HEAD_HEAD, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — nested type-arg unification "
            f"stayed one level deep (#769 gap 2)"
        )

    def test_nested_unification_mangles_int(self) -> None:
        result = _compile_ok(self._HEAD_HEAD)
        wat = result.wat or ""
        assert "$head_head$Int" in wat
        assert "$head_head$Bool" not in wat, (
            "phantom Bool clone — _unify_param_arg did not recurse into "
            "nested type args (#769 gap 2)"
        )

    # -- gap 3: scope-aware De Bruijn reindexing -----------------------------

    _CONFUSE_LET = _IO + """\
private forall<A, B> fn confuse(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{
  let @B = @B.0;
  @A.0
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = confuse(100, 3);
  IO.print(to_string(@Int.0))
}
"""

    _KEEP_CONCRETE_LET = _IO + """\
private forall<A> fn keep(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 5;
  @A.0
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = keep(100);
  IO.print(to_string(@Int.0))
}
"""

    _CONFUSE2_NESTED = _IO + """\
private forall<A, B> fn confuse2(@Array<Option<A>>, @Array<Option<B>> -> @Option<A>)
  requires(array_length(@Array<Option<A>>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<Option<A>>.0[0]
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Option<Int>> = [Some(3)];
  let @Array<Option<Int>> = [Some(100)];
  match confuse2(@Array<Option<Int>>.0, @Array<Option<Int>>.1) {
    Some(@Int) -> IO.print(to_string(@Int.0)),
    None -> IO.print("NONE")
  }
}
"""

    _PICK_MATCH = _IO + """\
private forall<A, B> fn pick(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{
  match Some(@B.0) {
    Some(@B) -> @A.0,
    None -> @A.0
  }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = pick(100, 3);
  IO.print(to_string(@Int.0))
}
"""

    _VIA_CLOSURE = _IO + """\
private forall<A, B> fn via(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(fn(@B -> @A) effects(pure) { @A.0 }, @B.0)
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = via(100, 3);
  IO.print(to_string(@Int.0))
}
"""

    _GUARDED_ENSURES = _IO + """\
private forall<A, B> fn guarded(@A, @B -> @A)
  requires(true)
  ensures(@A.result == @A.0)
  effects(pure)
{
  let @B = @B.0;
  @A.0
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = guarded(100, 3);
  IO.print(to_string(@Int.0))
}
"""

    def test_reindex_body_let(self) -> None:
        """A body ``let`` of a collapsing type shifts the later ``@A.0``:
        the answer is the FIRST argument (100), not the second (3)."""
        out = _run_io(self._CONFUSE_LET, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — params-only reindex read the "
            f"wrong slot after a body let (#769 gap 3)"
        )

    def test_reindex_single_var_concrete_let(self) -> None:
        """One type variable suffices: a body ``let @Int`` interposes and
        ``@A.0`` must still reach the parameter (100), not the let (5)."""
        out = _run_io(self._KEEP_CONCRETE_LET, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — @A.0 resolved to the body let "
            f"after collapse (#769 gap 3)"
        )

    def test_reindex_nested_slot_name_collapse(self) -> None:
        """``Array<Option<A>>``/``Array<Option<B>>`` collapse at A=B=Int;
        the body ref must follow its ORIGINAL binder (arrA -> Some(100))."""
        out = _run_io(self._CONFUSE2_NESTED, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — one-level slot-name truncation "
            f"hid the collapse (#769 gap 3)"
        )

    def test_reindex_branch_let_scoped(self) -> None:
        """Behavioral twin of the leak test: with the branch let correctly
        popped, ``@A.0`` still resolves to the parameter (100); a leaking
        walker shifts it to a dangling index and the program fails to
        compile (E699)."""
        source = self._IO + """\
private forall<A> fn branchy(@A, @Bool -> @A)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = if @Bool.0 then { let @Int = 5; true } else { false };
  @A.0
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = branchy(100, true);
  IO.print(to_string(@Int.0))
}
"""
        out = _run_io(source, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — branch-scoped let leaked into "
            f"the reindex scope (#769 gap 3)"
        )

    def test_reindex_match_binder(self) -> None:
        """A match-arm binder interposes inside its arm only."""
        out = _run_io(self._PICK_MATCH, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — match-arm binder not counted "
            f"by the reindex (#769 gap 3)"
        )

    def test_reindex_closure_param(self) -> None:
        """A closure parameter interposes inside the closure body only."""
        out = _run_io(self._VIA_CLOSURE, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — closure param not counted by "
            f"the reindex (#769 gap 3)"
        )

    def test_reindex_contracts_params_only(self) -> None:
        """The ensures scope is params-only even with a body let present;
        the proved postcondition must describe the CORRECT body (result ==
        first argument)."""
        out = _run_io(self._GUARDED_ENSURES, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — contract/body scope confusion "
            f"in the reindex (#769 gap 3)"
        )

    # -- gap 1b, logic-arm parity: call shapes with no fixed table entry ----

    _APPLY_FN_ARG = _IO + """\
private forall<T> fn ident(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = ident(apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }, 21));
  IO.print(to_string(@Int.0))
}
"""

    _GENERIC_I32_RET_ARG = _IO + """\
private forall<T> fn ident(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private forall<U> fn pass(@U -> @U)
  requires(true) ensures(true) effects(pure)
{ @U.0 }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match ident(pass(Some(42))) {
    Some(@Int) -> IO.print(to_string(@Int.0)),
    None -> IO.print("NONE")
  }
}
"""

    _GENERIC_NAT_RET_ARG = _IO + """\
private forall<T> fn ident(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private forall<U> fn passnat(@U -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 7 }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Nat = ident(passnat(1));
  IO.print(to_string(@Nat.0))
}
"""

    _ASYNC_ARG = _IO + """\
private forall<T> fn ident(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn work(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO, Async>)
{
  let @Int = await(ident(async(work(41))));
  IO.print(to_string(@Int.0))
}
"""

    _AWAIT_ARG = _IO + """\
private forall<T> fn ident(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn work(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO, Async>)
{
  let @Future<Int> = async(work(41));
  let @Int = ident(await(@Future<Int>.0));
  IO.print(to_string(@Int.0))
}
"""

    def test_apply_fn_return_in_generic_arg(self) -> None:
        """``ident(apply_fn(closure, 21))``: the rewrite chain infers the
        closure's declared return (Int); discovery must infer the SAME name,
        not the phantom default — else ``ident$Int`` is called but never
        emitted and ``main`` is dropped (#769, logic-arm parity)."""
        out = _run_io(self._APPLY_FN_ARG, fn="main")
        assert out.strip() == "42", (
            f"expected '42'; got {out!r} — discovery lacks the apply_fn "
            f"closure-return arm the rewrite chain has (#769)"
        )

    def test_apply_fn_arg_mangles_int(self) -> None:
        result = _compile_ok(self._APPLY_FN_ARG)
        wat = result.wat or ""
        assert "$ident$Int" in wat
        assert "$ident$Bool" not in wat, (
            "discovery emitted the phantom Bool clone for an apply_fn "
            "argument the rewrite manglings as $Int (#769)"
        )

    def test_generic_i32_return_in_generic_arg(self) -> None:
        """``ident(pass(Some(42)))``: discovery substitutes the callee's
        declared return (``Option``); the rewrite's generic branch must do
        the SAME substitution instead of WAT-collapsing i32 to "Bool"
        (#769, generic-return parity)."""
        out = _run_io(self._GENERIC_I32_RET_ARG, fn="main")
        assert out.strip() == "42", (
            f"expected '42'; got {out!r} — the rewrite WAT-collapsed a "
            f"generic i32-handle return to Bool (#769)"
        )

    def test_generic_nat_return_in_generic_arg(self) -> None:
        """``ident(passnat(1))``: declared ``Nat`` return — discovery says
        ``Nat``; the rewrite's i64 WAT-collapse said ``Int`` (#769)."""
        out = _run_io(self._GENERIC_NAT_RET_ARG, fn="main")
        assert out.strip() == "7", (
            f"expected '7'; got {out!r} — generic declared-Nat return "
            f"desynced from the i64 WAT collapse (#769)"
        )

    def test_async_future_in_generic_arg(self) -> None:
        """``ident(async(work(41)))``: both sides must name the instantiation
        ``Future<Int>`` (#769, logic-arm parity)."""
        out = _run_io(self._ASYNC_ARG, fn="main")
        assert out.strip() == "42", (
            f"expected '42'; got {out!r} — async in generic-arg position "
            f"desynced (#769)"
        )

    def test_await_result_in_generic_arg(self) -> None:
        """``ident(await(@Future<Int>.0))``: both sides must strip the
        ``Future<>`` wrapper identically (#769, logic-arm parity)."""
        out = _run_io(self._AWAIT_ARG, fn="main")
        assert out.strip() == "42", (
            f"expected '42'; got {out!r} — await in generic-arg position "
            f"desynced (#769)"
        )

    # -- adversarial-panel round: handler-state scope + prelude overrides ---

    _STATE_BODY = _IO + """\
private forall<A> fn through_state(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    put(7);
    @A.0
  }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(to_string(through_state(100)))
}
"""

    _STATE_BODY_SILENT = _IO + """\
private forall<A> fn through_state2(@Int, @A -> @A)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    put(7);
    @A.0
  }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(to_string(through_state2(3, 100)))
}
"""

    _OVERRIDE_OPTION_MAP = _IO + """\
public fn option_map(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 42)
  effects(pure)
{
  42
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("value=\\(option_map(()))")
}
"""

    _OVERRIDE_JSON_TYPE = _IO + """\
public fn json_type(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(pure)
{
  7
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("x=\\(json_type(()))")
}
"""

    def test_reindex_state_handler_body(self) -> None:
        """A ``State<T>``-handled body carries NO state slot binding in
        codegen (state lives in host-side cells; ``_translate_handle_state``
        translates the body with the env unchanged) — the reindex walker
        must not count one.  A walker that mirrors the CHECKER's extra
        body-scope state binding shifts ``@A.0`` to a dangling index (E699)
        here (adversarial panel, PR #972)."""
        out = _run_io(self._STATE_BODY, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — the reindex counted a handler "
            f"state binding codegen never pushes"
        )

    def test_reindex_state_handler_body_silent(self) -> None:
        """Same shape with a second param below ``@A``: the phantom state
        binding lands the ref on an IN-RANGE but wrong local — silent wrong
        answer (3), not an E699."""
        out = _run_io(self._STATE_BODY_SILENT, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — the reindex counted a handler "
            f"state binding codegen never pushes (silent variant)"
        )

    def test_prelude_override_not_shadowed_by_dict(self) -> None:
        """``option_map`` is an E151-EXEMPT, user-overridable prelude
        combinator (#815).  The shared builtin-name dict must not shadow a
        user's override: the interpolation types the call by the USER's
        declared return (Int), not the prelude signature — pre-gate the
        literal segments were silently dropped (adversarial panel, PR #972)."""
        out = _run_io(self._OVERRIDE_OPTION_MAP, fn="main")
        assert out.strip() == "value=42", (
            f"expected 'value=42'; got {out!r} — the builtin-name dict "
            f"shadowed a user override of a prelude combinator"
        )

    def test_prelude_override_json_type_no_trap(self) -> None:
        """Same gate, trap variant: an overridden ``json_type`` returning
        Int must not be typed as the prelude's String (pre-gate: WASM
        validation failure at run time)."""
        out = _run_io(self._OVERRIDE_JSON_TYPE, fn="main")
        assert out.strip() == "x=7", (
            f"expected 'x=7'; got {out!r} — the builtin-name dict shadowed "
            f"a user override of json_type"
        )

    _OVERRIDE_INTO_GENERIC = _IO + """\
public fn option_map(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 42)
  effects(pure)
{
  42
}

private forall<T> fn ident_ov(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(to_string(ident_ov(option_map(()))))
}
"""

    def test_prelude_override_binds_generic_by_declared_type(self) -> None:
        """The override gate must hold on the DISCOVERY side too: a generic
        bound from an overridden combinator's return must instantiate at the
        user's declared type (Int), not the prelude signature — else
        discovery emits ``ident_ov$Option`` while the gated rewrite calls
        ``ident_ov$Int`` (dangling, ``main`` dropped)."""
        out = _run_io(self._OVERRIDE_INTO_GENERIC, fn="main")
        assert out.strip() == "42", (
            f"expected '42'; got {out!r} — discovery and rewrite gate the "
            f"override differently"
        )

    _NESTED_WHERE = _IO + """\
private forall<A> fn outer(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  helper(@A.0)
}
where {
  fn helper(@A -> @A)
    requires(true) ensures(true) effects(pure)
  {
    inner(@A.0)
  }
  where {
    fn inner(@A -> @A)
      requires(true) ensures(true) effects(pure)
    {
      let @Int = 5;
      @A.0
    }
  }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(to_string(outer(100)))
}
"""

    def test_reindex_nested_where_fn(self) -> None:
        """``where`` blocks nest; the reindex walker must recurse into a
        helper's OWN ``where_fns`` (each an independent param-rooted scope)
        — a depth-1 walk leaves the nested helper's collapsed indices stale
        and it silently reads its body ``let`` (5) instead of the parameter
        (PR #972 review)."""
        out = _run_io(self._NESTED_WHERE, fn="main")
        assert out.strip() == "100", (
            f"expected '100'; got {out!r} — nested where-fn indices were "
            f"not reindexed"
        )
