"""Tests for vera.codegen — effects (State/Exn/effect handlers, async futures, Random, expression-bodied handlers).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations


from vera.codegen import (
    compile,
    execute,
)
from vera.parser import parse_file
from vera.transform import transform

from tests.codegen_helpers import (
    _IO_PRELUDE,
    _compile,
    _compile_ok,
    _run,
    _run_float,
    _run_io,
    _run_state,
)


class TestStateEffect:

    def test_state_int_get_default(self) -> None:
        """get(()) returns 0 by default for State<Int>."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0

    def test_state_int_put_then_get(self) -> None:
        """put(42) then get(()) returns 42."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{
  put(42);
  get(())
}
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 42

    def test_increment_pattern(self) -> None:
        """Classic increment: get, add 1, put — state goes from 0 to 1."""
        source = """\
public fn increment(@Unit -> @Unit)
  requires(true) ensures(true) effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
"""
        exec_result = _run_state(source, fn="increment")
        assert exec_result.value is None  # Unit return
        assert exec_result.state["State_Int"] == 1

    def test_increment_example_file(self) -> None:
        """examples/increment.vera compiles and executes."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "increment.vera"
        source = path.read_text(encoding="utf-8")
        tree = parse_file(str(path))
        program = transform(tree)
        result = compile(program, source=source, file=str(path))
        assert result.ok
        assert "increment" in result.exports
        exec_result = execute(result, fn_name="increment")
        assert exec_result.state["State_Int"] == 1

    def test_state_bool_get_default(self) -> None:
        """Bool state defaults to 0 (false)."""
        source = """\
public fn f(-> @Bool)
  requires(true) ensures(true) effects(<State<Bool>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0

    def test_state_bool_put_get(self) -> None:
        """put(true) then get(()) returns 1."""
        source = """\
public fn f(-> @Bool)
  requires(true) ensures(true) effects(<State<Bool>>)
{
  put(true);
  get(())
}
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 1

    def test_state_float64_get_default(self) -> None:
        """Float64 state defaults to 0.0."""
        source = """\
public fn f(-> @Float64)
  requires(true) ensures(true) effects(<State<Float64>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0.0

    def test_state_nat_compiles(self) -> None:
        """State<Nat> compiles (Nat maps to i64)."""
        source = """\
public fn f(-> @Nat)
  requires(true) ensures(true) effects(<State<Nat>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0

    def test_state_string_rejected(self) -> None:
        """State<String> is unsupported — function skipped with warning."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<State<String>>)
{ 42 }
"""
        result = _compile(source)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert any("unsupported" in w.description.lower() for w in warnings)
        assert "f" not in result.exports

    def test_state_with_io(self) -> None:
        """Mixed effects(<State<Int>, IO>) compiles and both work."""
        source = """\
public fn f(@Unit -> @Unit)
  requires(true) ensures(true) effects(<State<Int>, IO>)
{
  put(42);
  IO.print("done");
  ()
}
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.state["State_Int"] == 42
        assert exec_result.stdout == "done"

    def test_state_wat_has_imports(self) -> None:
        """WAT output contains State import declarations."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{ get(()) }
"""
        result = _compile_ok(source)
        assert 'import "vera" "state_get_Int"' in result.wat
        assert 'import "vera" "state_put_Int"' in result.wat

    def test_multiple_state_types(self) -> None:
        """Multiple State types emit all imports."""
        source = """\
public fn f(@Int -> @Unit)
  requires(true) ensures(true) effects(<State<Int>, State<Bool>>)
{
  put(@Int.0);
  ()
}
"""
        result = _compile_ok(source)
        assert 'import "vera" "state_get_Int"' in result.wat
        assert 'import "vera" "state_put_Int"' in result.wat
        assert 'import "vera" "state_get_Bool"' in result.wat
        assert 'import "vera" "state_put_Bool"' in result.wat
        assert len(result.state_types) == 2

    def test_put_void_no_drop(self) -> None:
        """put(x) in ExprStmt does not emit a drop instruction."""
        source = """\
public fn f(@Unit -> @Unit)
  requires(true) ensures(true) effects(<State<Int>>)
{
  put(42);
  ()
}
"""
        result = _compile_ok(source)
        # The function body should NOT contain 'drop' after the put call
        fn_start = result.wat.index("(func $f")
        fn_body = result.wat[fn_start:]
        # put call should be present, drop should not follow it
        assert "call $vera.state_put_Int" in fn_body
        assert "drop" not in fn_body

    def test_state_initial_value(self) -> None:
        """Initial state override: get(()) returns the initial value."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{ get(()) }
"""
        exec_result = _run_state(
            source, fn="f", initial_state={"State_Int": 10}
        )
        assert exec_result.value == 10

    def test_pure_no_state_imports(self) -> None:
        """Pure functions don't produce State imports."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "state_get" not in result.wat
        assert "state_put" not in result.wat


# =====================================================================
# C6j: Effect Handlers
# =====================================================================


class TestEffectHandlers:
    """Tests for handle[State<T>] compilation — State handlers via
    host imports, state initialization, get/put in handler body."""

    _STATE_HANDLER = """\
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
"""

    def test_handle_state_get_init(self) -> None:
        """handle[State<Int>](@Int = 42) in { get(()) } returns 42."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 42) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""
        assert _run(src, "test") == 42

    def test_handle_state_put_get(self) -> None:
        """put then get returns the put value."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(99);
    get(())
  }
}
"""
        assert _run(src, "test") == 99

    def test_handle_state_increment(self) -> None:
        """put(get(()) + 1) increments the state."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(get(()) + 1);
    get(())
  }
}
"""
        assert _run(src, "test") == 1

    def test_handle_state_run_counter(self) -> None:
        """The run_counter pattern: init 0, put 0, then 3x increment."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(0);
    put(get(()) + 1);
    put(get(()) + 1);
    put(get(()) + 1);
    get(())
  }
}
"""
        assert _run(src, "test") == 3

    def test_handle_state_initial_value(self) -> None:
        """Non-zero initial state is set correctly."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 100) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(get(()) + 5);
    get(())
  }
}
"""
        assert _run(src, "test") == 105

    def test_handle_state_in_let(self) -> None:
        """Handler body can use let bindings."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(10);
    let @Int = get(());
    put(@Int.0 + 5);
    get(())
  }
}
"""
        assert _run(src, "test") == 15

    def test_handle_state_pure_function(self) -> None:
        """A pure function with handle[State<T>] compiles (not skipped)."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 7) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""
        result = _compile_ok(src)
        assert "test" in result.exports

    def test_handle_state_bool(self) -> None:
        """State<Bool> handler works."""
        src = """\
public fn test(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Bool>](@Bool = false) {
    get(@Unit) -> { resume(@Bool.0) },
    put(@Bool) -> { resume(()) }
  } in {
    put(true);
    get(())
  }
}
"""
        assert _run(src, "test") == 1  # true = 1

    def test_handle_state_wat_has_imports(self) -> None:
        """WAT output contains state host imports."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""
        result = _compile_ok(src)
        assert result.wat is not None
        assert '(import "vera" "state_get_Int"' in result.wat
        assert '(import "vera" "state_put_Int"' in result.wat
        assert '(import "vera" "state_push_Int"' in result.wat
        assert '(import "vera" "state_pop_Int"' in result.wat

    def test_nested_same_type_state_handlers(self) -> None:
        """Nested handle[State<Int>] of the same type have independent cells (#417)."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 10) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(99);
    handle[State<Int>](@Int = 1) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      put(2);
      ()
    };
    get(())
  }
}
"""
        assert _run(src, "test") == 99

    def test_nested_state_inner_does_not_corrupt_outer(self) -> None:
        """Inner handler put does not affect outer handler state (#417)."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    handle[State<Int>](@Int = 100) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      put(999);
      ()
    };
    get(())
  }
}
"""
        assert _run(src, "test") == 5

    def test_nested_state_outer_readable_after_inner(self) -> None:
        """After inner handler exits, outer handler value is restored (#417).

        The inner handler returns an Int (not Unit) so state_pop_Int is called
        with a live WASM value on the stack — verifying it is truly stack-neutral.
        The outer block captures the inner result via let, then reads outer state.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 42) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Int = handle[State<Int>](@Int = 0) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      put(7);
      get(())
    };
    get(())
  }
}
"""
        assert _run(src, "test") == 42

    def test_exn_handler_compiles(self) -> None:
        """Exn<E> handler compiles to WASM using exception handling."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
private data Option<T> { None, Some(T) }
public fn test(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { None }
  } in {
    Some(@Int.0)
  }
}
"""
        result = _compile(src)
        assert "test" in result.exports
        assert "try_table" in result.wat
        assert "tag $exn_Int" in result.wat

    def test_effect_handler_example_compiles(self) -> None:
        """examples/effect_handler.vera compiles without errors."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile(source)
        assert result.ok

    def test_effect_handler_example_run_counter(self) -> None:
        """examples/effect_handler.vera run_counter returns 3."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="run_counter")
        assert exec_result.value == 3

    def test_effect_handler_example_test_state_init(self) -> None:
        """examples/effect_handler.vera test_state_init returns 42."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_state_init")
        assert exec_result.value == 42

    def test_effect_handler_example_test_put_get(self) -> None:
        """examples/effect_handler.vera test_put_get returns 99."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_put_get")
        assert exec_result.value == 99

    def test_effect_handler_example_safe_div(self) -> None:
        """examples/effect_handler.vera safe_div(10, 2) returns 5."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="safe_div", args=[10, 2])
        assert exec_result.value == 5

    def test_effect_handler_example_safe_div_zero(self) -> None:
        """examples/effect_handler.vera safe_div(7, 0) returns -1."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="safe_div", args=[7, 0])
        assert exec_result.value == -1

    def test_effect_handler_example_main(self) -> None:
        """examples/effect_handler.vera main returns 4."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.value == 4


# =====================================================================
# Exn<E> exception handler compilation
# =====================================================================


class TestExnHandlers:
    """Tests for Exn<E> effect handler compilation using WASM exceptions."""

    def test_exn_throw_caught(self) -> None:
        """Body throws, handler catches and transforms the value."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 + 100 }
  } in {
    throw(42)
  }
}
"""
        assert _run(src, fn="test") == 142

    def test_exn_no_throw(self) -> None:
        """Body completes normally, handler clause is not invoked."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 + 100 }
  } in {
    99
  }
}
"""
        assert _run(src, fn="test") == 99

    def test_exn_cross_function(self) -> None:
        """Function with Exn effect throws, caller catches via handle."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
private fn risky(@Int -> @Int)
  requires(true) ensures(true) effects(<Exn<Int>>)
{
  if @Int.0 > 0 then { throw(@Int.0) } else { 0 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 * 2 }
  } in {
    risky(21)
  }
}
"""
        assert _run(src, fn="test") == 42

    def test_exn_no_throw_cross_function(self) -> None:
        """Cross-function call that doesn't throw."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
private fn safe(@Int -> @Int)
  requires(true) ensures(true) effects(<Exn<Int>>)
{
  if @Int.0 > 100 then { throw(@Int.0) } else { @Int.0 + 1 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { 0 - 1 }
  } in {
    safe(10)
  }
}
"""
        assert _run(src, fn="test") == 11

    def test_exn_qualified_throw_caught(self) -> None:
        """Exn.throw (qualified form) compiles and runs identically to bare throw."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
private fn require_non_negative(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(<Exn<Int>>)
{
  if @Int.0 < 0 then { Exn.throw(@Int.0) } else { @Int.0 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> 0
  } in {
    require_non_negative(0 - 3)
  }
}
"""
        assert _run(src, fn="test") == 0

    def test_exn_qualified_throw_no_throw(self) -> None:
        """Exn.throw (qualified form) — non-throwing path returns correct value."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
private fn require_non_negative(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(<Exn<Int>>)
{
  if @Int.0 < 0 then { Exn.throw(@Int.0) } else { @Int.0 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> 0
  } in {
    require_non_negative(5)
  }
}
"""
        assert _run(src, fn="test") == 5

    def test_state_qualified_get_put(self) -> None:
        """State.get / State.put (qualified forms) compile and run correctly."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int)  -> { resume(()) }
  } in {
    State.put(State.get(()) + 1);
    State.put(State.get(()) + 1);
    State.get(())
  }
}
"""
        assert _run(src, fn="test") == 2

    def test_exn_with_io(self) -> None:
        """Exn handler inside a function with IO effects."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 }
  } in {
    IO.print("before throw");
    throw(77)
  }
}
"""
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="test")
        assert exec_result.value == 77
        assert exec_result.stdout == "before throw"

    def test_exn_nested_inner_catches(self) -> None:
        """Nested handlers — inner catches, outer not triggered."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { 0 - 1 }
  } in {
    handle[Exn<Int>] {
      throw(@Int) -> { @Int.0 + 500 }
    } in {
      throw(10)
    }
  }
}
"""
        assert _run(src, fn="test") == 510

    def test_exn_nat_type(self) -> None:
        """Exn<Nat> with Nat exception value."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Nat>] {
    throw(@Nat) -> { @Nat.0 + 1000 }
  } in {
    throw(42)
  }
}
"""
        assert _run(src, fn="test") == 1042

    def test_exn_string_throw_caught(self) -> None:
        """Exn<String> throw+catch: pair type (ptr, len) uses (param i32 i32) tag."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> { string_length(@String.0) }
  } in {
    throw("hello")
  }
}
"""
        assert _run(src, fn="test") == 5

    def test_exn_string_no_throw(self) -> None:
        """Exn<String> handler with non-throwing body: pair type locals allocated."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> { 0 - 1 }
  } in {
    string_length("world")
  }
}
"""
        assert _run(src, fn="test") == 5

    def test_exn_string_handler_returns_string(self) -> None:
        """Handler clause returns a String (result_wt == i32_pair → result i32 i32)."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = handle[Exn<String>] {
    throw(@String) -> { @String.0 }
  } in {
    throw("caught")
  };
  IO.print(@String.0)
}
"""
        # Pin the ABI-level encoding: tag uses (param i32 i32) for the String
        # payload, and the outer block/try_table carry (result i32 i32) because
        # the handler clause returns a String.
        result = _compile_ok(src)
        assert "(tag $exn_String (param i32 i32))" in result.wat
        assert "result i32 i32" in result.wat
        # Verify runtime behaviour
        assert _run_io(src, fn="test") == "caught"

    def test_exn_string_empty_payload(self) -> None:
        """throw("") correctly passes a zero-length ptr/len pair through the tag."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> { string_length(@String.0) }
  } in {
    throw("")
  }
}
"""
        assert _run(src, fn="test") == 0


# =====================================================================
# Async / Future<T>
# =====================================================================


class TestAsync:
    """Async effect compiles and executes correctly (sequential/eager)."""

    def test_async_await_int(self) -> None:
        """async(42) → await → 42."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(42);
  await(@Future<Int>.0)
}
"""
        assert _run(source, fn="f") == 42

    def test_async_await_arithmetic(self) -> None:
        """async(5 * 7) → await → 35."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(5 * 7);
  await(@Future<Int>.0)
}
"""
        assert _run(source, fn="f") == 35

    def test_async_await_bool(self) -> None:
        """async(true) → await → 1 (Bool true)."""
        source = """\
public fn f(-> @Bool)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Bool> = async(true);
  await(@Future<Bool>.0)
}
"""
        assert _run(source, fn="f") == 1

    def test_async_await_multiple(self) -> None:
        """Two futures, await both, add results."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(10);
  let @Future<Int> = async(20);
  await(@Future<Int>.1) + await(@Future<Int>.0)
}
"""
        assert _run(source, fn="f") == 30

    def test_async_in_effectful_fn(self) -> None:
        """Private helper with effects(<Async>) called from main."""
        source = """\
private fn compute(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(100);
  await(@Future<Int>.0)
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ compute() }
"""
        assert _run(source, fn="main") == 100

    def test_async_with_io(self) -> None:
        """effects(<IO, Async>) — composition with IO."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO, Async>)
{
  let @Future<Int> = async(42);
  IO.print(to_string(await(@Future<Int>.0)))
}
"""
        assert _run_io(source, fn="main") == "42"

    def test_async_await_nat(self) -> None:
        """Nat type roundtrip through Future."""
        source = """\
public fn f(-> @Nat)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Nat> = async(string_length("hello"));
  await(@Future<Nat>.0)
}
"""
        assert _run(source, fn="f") == 5

    def test_async_await_float(self) -> None:
        """Float64 type roundtrip through Future."""
        source = """\
public fn f(-> @Float64)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Float64> = async(3.14);
  await(@Future<Float64>.0)
}
"""
        assert abs(_run_float(source, fn="f") - 3.14) < 0.001


class TestRandomEffect:
    """Tests for the Random effect (#465).

    The three Random ops are non-deterministic, so each test
    constrains the host's behaviour via Python ``random.seed`` to
    make assertions concrete.  All tests run multiple iterations to
    catch off-by-one errors at range boundaries that would only
    surface on specific seeds.
    """

    def test_random_int_in_range(self) -> None:
        """Random.random_int(low, high) returns Int in inclusive [low, high].

        Seeded with ``random.seed(0)`` so the test is deterministic
        — not just \"probably covers the range.\"  After 100 draws
        the produced set must:
          (a) stay strictly within [low, high] on every draw,
          (b) include both boundary values (enforces the inclusive
              semantics — the original `len(produced) >= 4` check
              didn't actually verify that `low` and `high` were hit),
          (c) hit at least 4 of the 6 possible values (distribution
              sanity).
        Also asserts the WAT imports `$vera.random_int` and does
        NOT import `$vera.random_float` or `$vera.random_bool` —
        confirms ``_random_ops_used`` gating is working.
        """
        import random
        random.seed(0)
        low, high = 5, 10
        source = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{{
  Random.random_int({low}, {high})
}}
"""
        result = _compile_ok(source)
        # WAT import-gating: only random_int should be imported.
        assert "$vera.random_int" in result.wat
        assert "$vera.random_float" not in result.wat
        assert "$vera.random_bool" not in result.wat

        produced = set()
        for _ in range(100):
            v = execute(result, fn_name="main").value
            assert low <= v <= high, f"out of range: {v}"
            produced.add(v)
        # Inclusive-range contract: both boundary values must appear.
        assert low in produced, f"low boundary {low} missing from {produced}"
        assert high in produced, f"high boundary {high} missing from {produced}"
        # Distribution sanity: at least 4 of 6 possible values in 100 draws.
        assert len(produced) >= 4, f"narrow distribution: {produced}"

    def test_random_int_zero_crossing_range(self) -> None:
        """random_int with a negative-to-positive range straddles zero.

        Covers signed-integer handling paths that all-positive ranges
        don't exercise: the Python `random.randint` accepts negative
        bounds transparently, but the WASM i64 marshalling and
        (browser-side) BigInt→Number conversion could in principle
        mishandle the sign bit or the zero crossing.  A `[-2, 2]`
        range forces every one of those 5 distinct values to appear
        to satisfy the boundary+distribution assertions.

        Also asserts WAT gating: only `random_int` imported.
        """
        import random
        random.seed(0)
        low, high = -2, 2
        source = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{{
  Random.random_int({low}, {high})
}}
"""
        result = _compile_ok(source)
        assert "$vera.random_int" in result.wat
        assert "$vera.random_float" not in result.wat
        assert "$vera.random_bool" not in result.wat

        produced = set()
        for _ in range(100):
            v = execute(result, fn_name="main").value
            assert low <= v <= high, f"out of range: {v}"
            produced.add(v)
        # Both boundaries must appear across the signed range.
        assert low in produced, f"low boundary {low} missing from {produced}"
        assert high in produced, f"high boundary {high} missing from {produced}"
        # Zero specifically must be reachable — catches a bug where
        # the zero value gets dropped or treated as a sentinel.
        assert 0 in produced, f"zero missing from {produced}"
        # Distribution sanity: the range has 5 values; seeded draws
        # of 100 should comfortably cover at least 4.
        assert len(produced) >= 4, f"narrow distribution: {produced}"

    def test_random_int_singleton_range(self) -> None:
        """random_int(n, n) always returns n — degenerate range.

        Also asserts WAT gating: only `random_int` imported, not
        `random_float` or `random_bool`.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{
  Random.random_int(7, 7)
}
"""
        result = _compile_ok(source)
        assert "$vera.random_int" in result.wat
        assert "$vera.random_float" not in result.wat
        assert "$vera.random_bool" not in result.wat
        for _ in range(20):
            assert execute(result, fn_name="main").value == 7

    def test_random_float_in_unit_interval(self) -> None:
        """Random.random_float() returns Float64 in [0.0, 1.0).

        Verifies the WASM f64 result is correctly marshalled back
        through wasmtime — Float64 returns are easy to mis-handle.
        Also asserts WAT gating: only `random_float` imported, not
        `random_int` or `random_bool`.
        """
        source = """\
public fn main(-> @Float64)
  requires(true) ensures(true) effects(<Random>)
{
  Random.random_float(())
}
"""
        result = _compile_ok(source)
        assert "$vera.random_float" in result.wat
        assert "$vera.random_int" not in result.wat
        assert "$vera.random_bool" not in result.wat
        for _ in range(50):
            v = execute(result, fn_name="main").value
            assert isinstance(v, float)
            assert 0.0 <= v < 1.0, f"out of [0, 1): {v}"

    def test_random_bool_produces_both(self) -> None:
        """Random.random_bool() produces both true and false in 100 draws.

        Deterministic via ``random.seed(0)``: asserts both `0` and
        `1` appear in the observed set (stronger than the previous
        probabilistic ``25 <= total <= 75`` bound, which could
        flake).  With a fixed seed the set is reproducible and the
        test fails deterministically if the host impl becomes
        degenerate.

        Also asserts WAT gating: only `random_bool` imported, not
        `random_int` or `random_float`.
        """
        import random
        random.seed(0)
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{
  if Random.random_bool(()) then { 1 } else { 0 }
}
"""
        result = _compile_ok(source)
        assert "$vera.random_bool" in result.wat
        assert "$vera.random_int" not in result.wat
        assert "$vera.random_float" not in result.wat
        observed = {execute(result, fn_name="main").value for _ in range(100)}
        assert {0, 1}.issubset(observed), (
            f"random_bool didn't produce both outcomes in 100 seeded "
            f"draws; observed {observed}"
        )


# =====================================================================
# WASM call translator critical bug fixes (#475 PR 1)
# =====================================================================

class TestExpressionBodiedExnHandler475:
    """`#475` finding 1: handle[Exn<E>] with expression-bodied catch arms.

    Pre-fix, `_translate_handle_exn` only inferred `result_wt` when
    the catch-clause body was an `ast.Block`; expression-bodied
    handlers (e.g. `throw(@String) -> None`) left `result_wt = None`
    and the emitted WAT omitted the `(result T)` annotation —
    producing invalid WAT that would fail validation when the body
    type was anything other than Unit.

    Post-fix, `_infer_expr_wasm_type` is used for both the catch
    clause and the body, handling all expression types uniformly.
    """

    def test_expression_bodied_handler_returns_option(self) -> None:
        """`throw(@String) -> None` (expression-bodied, returns Option)."""
        src = """
private fn try_div(@Int, @Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> None
  } in {
    Some(safe_div(@Int.0, @Int.1))
  }
}

private fn safe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  if @Int.1 == 0 then {
    throw("divide by zero")
  } else {
    @Int.0 / @Int.1
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match try_div(10, 2) {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        # Should compile cleanly and run; pre-#475 the missing
        # `(result ...)` annotation made the WAT invalid.
        assert _run(src) == 5

    def test_expression_bodied_handler_traps_on_zero(self) -> None:
        """Same shape as above but exercises the throw path returning None."""
        src = """
private fn try_div(@Int, @Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> None
  } in {
    Some(safe_div(@Int.0, @Int.1))
  }
}

private fn safe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  if @Int.1 == 0 then {
    throw("divide by zero")
  } else {
    @Int.0 / @Int.1
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match try_div(10, 0) {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        # try_div(10, 0) → throws → handler returns None → match → -1.
        assert _run(src) == -1

    def test_expression_bodied_handler_int_result(self) -> None:
        """Catch arm returns @Int (not Option) — verifies non-pair WAT result."""
        src = """
private fn safe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> 0 - 1
  } in {
    inner_div(@Int.0, @Int.1)
  }
}

private fn inner_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  if @Int.1 == 0 then {
    throw("divide by zero")
  } else {
    @Int.0 / @Int.1
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  safe_div(10, 0)
}
"""
        assert _run(src) == -1

# =====================================================================
# Concurrent <Async> (#841) — fused lowering + host-threaded futures
# =====================================================================

class TestConcurrentAsync841:
    """#841: async(Http.get/post(...)) fuses into a single host import that
    starts the request on a host worker thread and returns a Future as a
    #578-tagged handle wrapper; await blocks on the handle.  Everything
    else stays eager (checker-warned, spec-conformant)."""

    def test_async_http_get_fuses_to_task_import(self) -> None:
        """The direct-call shape imports vera.async_http_get (not http_get)
        and the await site imports vera.async_await."""
        result = _compile_ok("""
public fn fetch(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Future<Result<String, String>> = async(Http.get(@String.0));
  await(@Future<Result<String, String>>.0)
}
""")
        assert '(import "vera" "async_http_get"' in result.wat, result.wat[:800]
        assert '(import "vera" "async_await"' in result.wat
        # the fused path must NOT also route through the sync import
        assert '(import "vera" "http_get"' not in result.wat

    def test_async_http_post_fuses_to_task_import(self) -> None:
        result = _compile_ok("""
public fn send(@String, @String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Future<Result<String, String>> = async(Http.post(@String.1, @String.0));
  await(@Future<Result<String, String>>.0)
}
""")
        assert '(import "vera" "async_http_post"' in result.wat

    def test_async_pure_stays_eager_no_task_imports(self) -> None:
        """Non-fused shapes keep the identity lowering — no task imports."""
        result = _compile_ok("""
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(41 + 1);
  await(@Future<Int>.0)
}
""")
        assert "async_http_get" not in result.wat
        assert "async_await" not in result.wat

    def test_fused_future_wrapper_is_gc_registered(self) -> None:
        """The pending-future wrapper follows the #578/#573 pattern:
        register_wrapper with the Future kind (4) and a shadow push, so an
        unawaited future is reclaimed by Phase 2c like a Decimal handle."""
        result = _compile_ok("""
public fn fire(@String -> @Future<Result<String, String>>)
  requires(true) ensures(true) effects(<Http, Async>)
{ async(Http.get(@String.0)) }
""")
        wat = result.wat
        assert "call $register_wrapper" in wat
        import re
        assert re.search(r"i32\.const 4\s*\n\s*local\.get \d+\s*\n\s*call \$register_wrapper", wat), (
            "expected register_wrapper with kind 4 for the Future wrapper")

    def test_await_of_generic_fn_with_concrete_future_return(self) -> None:
        """PR #842 review round 2 pin: a generic fn with a CONCRETE
        Future<Result<String, String>> return classifies at the await
        site via its template name — classification runs on the
        pre-monomorphization AST (the call-site mangling to wrap$Int
        happens later, during translation), so the clone names never
        need to be in the future-return registry.  Pinned so a future
        move to AST-level mono rewriting fails here instead of
        silently smuggling a wrapper."""
        source = """
public forall<T> fn wrap(@T, @String -> @Future<Result<String, String>>)
  requires(true) ensures(true) effects(<Http, Async>)
{ async(Http.get(@String.0)) }

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Result<String, String> = await(wrap(1, "ftp://mono.invalid/x"));
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }
}
"""
        result = _compile_ok(source)
        assert '(import "vera" "async_await"' in result.wat
        assert _run(source) == 1

    def test_two_async_gets_overlap_deterministically(self) -> None:
        """Two fused gets actually overlap: the server holds request A until
        request B arrives (3s bound).  Eager evaluation answers SEQUENTIAL
        (A times out waiting before B is ever issued); concurrent answers
        CONCURRENT for both.  Server-side ordering — no wall-clock."""
        import http.server
        import threading

        arrived_b = threading.Event()
        log: list[str] = []

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self) -> None:  # noqa: N802 (stdlib API name)
                log.append(self.path)
                if self.path == "/a":
                    ok = arrived_b.wait(timeout=3.0)
                    body = b"CONCURRENT" if ok else b"SEQUENTIAL"
                else:
                    arrived_b.set()
                    body = b"CONCURRENT"
                self.send_response(200)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, *args: object) -> None:
                pass

        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        port = server.server_address[1]
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            out = _run_io(f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO, Http, Async>)
{{
  let @Future<Result<String, String>> = async(Http.get("http://127.0.0.1:{port}/a"));
  let @Future<Result<String, String>> = async(Http.get("http://127.0.0.1:{port}/b"));
  let @Result<String, String> = await(@Future<Result<String, String>>.1);
  match @Result<String, String>.0 {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print("ERR-A")
  }};
  let @Result<String, String> = await(@Future<Result<String, String>>.0);
  match @Result<String, String>.0 {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print("ERR-B")
  }};
  ()
}}
""")
        finally:
            server.shutdown()
            server.server_close()
        assert out == "CONCURRENTCONCURRENT", (out, log)
