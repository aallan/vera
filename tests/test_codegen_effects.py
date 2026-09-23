"""Tests for vera.codegen — effects (State/Exn/effect handlers, async futures, Random, expression-bodied handlers).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re


from vera.codegen import (
    compile,
    execute,
)
from vera.parser import parse_file
from vera.transform import transform

import pytest

from vera.codegen.api import WasmTrapError

from tests.codegen_helpers import (
    _compile,
    _compile_ok,
    _run,
    _run_float,
    _run_io,
    _run_state,
)


class TestHandledBodySlotIdentity973:
    """#973 (PR #975 review): the checker no longer binds handler state into
    the handled body's scope, so a body slot reference must name the same
    binding in the checker and in codegen.  These run end-to-end — the run
    result is the value codegen resolves, so a re-introduced phantom checker
    binding cannot silently re-diverge the two models."""

    def test_body_slot_resolves_to_same_typed_param_end_to_end(self) -> None:
        """A same-typed fn param inside a handled body: `@Int.0` is the param
        (the argument, 5) — never the state init (99) or the put value (7)."""
        source = """\
public fn probe(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 99) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(7);
    @Int.0
  }
}
"""
        assert _run(source, fn="probe", args=[5]) == 5

    def test_body_get_put_end_to_end(self) -> None:
        """The canonical body path under a custom-clause handler: put then
        get runs to the put value (builtin state-cell semantics; #976 tracks
        the clauses themselves not being executed)."""
        source = """\
public fn probe(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 2) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(8);
    get(())
  }
}
"""
        assert _run(source, fn="probe") == 8


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
        source = """\
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


# Shared source programs for the #1038 await-in-scrutinee family.  Each
# `scrut_*` helper awaits a Future directly in match-scrutinee position; the
# public `call_*` wrappers construct concrete payloads so both arms run.  The
# return values are distinguishing (payload-carrying, arm-specific) so a wrong
# scrutinee width or a mis-extracted payload fails the assertion — not merely
# the E602-skip that drops the function pre-fix.
_ASYNC_SCRUT_OPTION = """\
private fn scrut_opt(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Option<Int>> = async(@Option<Int>.0);
  match await(@Future<Option<Int>>.0) {
    Some(@Int) -> @Int.0 + 1,
    None -> -7
  }
}

public fn call_some(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ scrut_opt(Some(5)) }

public fn call_none(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ scrut_opt(None) }
"""

_ASYNC_SCRUT_ADT = """\
private data Shape {
  Circle(Int),
  Square(Int)
}

private fn scrut_shape(@Shape -> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Shape> = async(@Shape.0);
  match await(@Future<Shape>.0) {
    Circle(@Int) -> @Int.0 + 10,
    Square(@Int) -> @Int.0 + 20
  }
}

public fn call_circle(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ scrut_shape(Circle(3)) }

public fn call_square(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ scrut_shape(Square(4)) }
"""

_ASYNC_SCRUT_INT = """\
private fn scrut_int(@Int -> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(@Int.0);
  match await(@Future<Int>.0) {
    0 -> 100,
    _ -> 200
  }
}

public fn call_int_zero(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ scrut_int(0) }

public fn call_int_nonzero(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ scrut_int(9) }
"""


class TestAwaitMatchScrutinee1038:
    """#1038: `match await(@Future<T>.0) { ... }` — awaiting a Future directly
    in scrutinee position.

    The match-scrutinee WASM-type inference (`_ref_type_name_wasm_type`, reached
    via the `await` FnCall arm of `_infer_expr_wasm_type`) must unwrap Future<T>
    to T — the same transparency the let-binding path (`_slot_name_to_wasm_type`)
    already applies.  Without it the scrutinee inferred None and the enclosing
    function E602-skipped ("could not infer match scrutinee WASM type") on a
    check/verify-green program.  Each test exercises BOTH arms with
    distinguishing values, so a wrong scrutinee width or mis-extracted payload
    is caught, not merely that the function survived codegen.  The scalar-Int and
    user-ADT members are here alongside the reported Option member because all
    three share the one broken inference site.  The final test pins the
    await-into-let-then-match form (the semantic oracle) against regression."""

    def test_await_future_option_scrutinee_some_arm(self) -> None:
        """await(Future<Option<Int>>) scrutinee: Some(5) payload flows to 5+1."""
        assert _run(_ASYNC_SCRUT_OPTION, fn="call_some") == 6

    def test_await_future_option_scrutinee_none_arm(self) -> None:
        """await(Future<Option<Int>>) scrutinee: None selects the None arm."""
        assert _run(_ASYNC_SCRUT_OPTION, fn="call_none") == -7

    def test_await_future_adt_scrutinee_first_ctor(self) -> None:
        """await(Future<UserADT>) scrutinee: Circle(3) payload flows to 3+10."""
        assert _run(_ASYNC_SCRUT_ADT, fn="call_circle") == 13

    def test_await_future_adt_scrutinee_second_ctor(self) -> None:
        """await(Future<UserADT>) scrutinee: Square(4) payload flows to 4+20."""
        assert _run(_ASYNC_SCRUT_ADT, fn="call_square") == 24

    def test_await_future_int_scrutinee_literal_arm(self) -> None:
        """await(Future<Int>) scalar scrutinee: 0 matches the literal arm."""
        assert _run(_ASYNC_SCRUT_INT, fn="call_int_zero") == 100

    def test_await_future_int_scrutinee_wildcard_arm(self) -> None:
        """await(Future<Int>) scalar scrutinee: 9 falls to the wildcard arm."""
        assert _run(_ASYNC_SCRUT_INT, fn="call_int_nonzero") == 200

    def test_await_into_let_then_match_still_works(self) -> None:
        """Regression pin: the await-into-let-then-match form (the semantic
        oracle) keeps compiling and running — the fix must not disturb the
        working path it mirrors.  Green before and after; it guards the
        let-binding scrutinee inference against collateral breakage."""
        source = """\
private fn oracle_opt(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Option<Int>> = async(@Option<Int>.0);
  let @Option<Int> = await(@Future<Option<Int>>.0);
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0 + 1,
    None -> -7
  }
}

public fn call_oracle(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ oracle_opt(Some(41)) }
"""
        assert _run(source, fn="call_oracle") == 42

    def test_slotref_ctor_arg_future_field_runs(self) -> None:
        """A `Future<Int>` SLOT REFERENCE as a constructor argument compiles.

        Pins the constructor-argument call site of the same fixed mapper
        (`_ref_type_name_wasm_type`): `WI(@Future<Int>.0, 7)` passes the
        Future through a SlotRef, whose WASM type the constructor-argument
        inference asks the mapper for — without the Future-transparency arm
        the whole function E602-skipped, exactly like the scrutinee site
        (the #1041 adversarial review flagged this site as a live, unpinned
        manifestation).  RED on base (E602 skip; 41 + 7 = 48 end-to-end,
        values chosen so no zeroed default can coincide)."""
        source = """\
private data WrapI { WI(Future<Int>, Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(41);
  let @WrapI = WI(@Future<Int>.0, 7);
  match @WrapI.0 {
    WI(@Future<Int>, @Int) -> await(@Future<Int>.0) + @Int.0
  }
}
"""
        assert _run(source, fn="f") == 48


class TestAliasFutureRefMapper1054:
    """#1054: an ALIAS to a Future works at the #1038 mapper's call sites.

    `type FA = Future<Option<Int>>;` at the match-await scrutinee and the
    constructor-argument sites E602-skipped while the direct spelling
    compiled: `_ref_type_name_wasm_type` resolved the slot name through the
    name-only `_resolve_base_type_name` (dropping the alias's type
    arguments — `FA` -> bare `Future`) and its Future arm guards on AST
    `type_args` an alias-spelled ref does not carry.  The mapper now
    canonicalizes an alias to its target's full compound spelling first
    (`_canonicalize_alias_slot_name`, the #1037 walk) and adds the
    string-form Future arm its sibling `_slot_name_to_wasm_type` carries,
    recursing on the payload spelling.  The alias analog of #1046, in the
    last mapper of the family without the canonicalizer.
    """

    def test_alias_future_match_scrutinee_runs(self) -> None:
        """The #1054 repro: alias-spelled match-await scrutinee.

        RED on base (E602 scrutinee-inference skip; expect 5 + 1 = 6)."""
        source = """\
type FA = Future<Option<Int>>;

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @FA = async(Some(5));
  match await(@FA.0) {
    Some(@Int) -> @Int.0 + 1,
    None -> 0 - 7
  }
}
"""
        assert _run(source, fn="f") == 6

    def test_alias_future_ctor_arg_runs(self) -> None:
        """Alias-spelled Future SlotRef as a constructor argument.

        RED on base (E602 unsupported-SlotRef skip; 41 + 7 = 48)."""
        source = """\
type FA = Future<Int>;

private data WrapI { WI(FA, Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @FA = async(41);
  let @WrapI = WI(@FA.0, 7);
  match @WrapI.0 {
    WI(@FA, @Int) -> await(@FA.0) + @Int.0
  }
}
"""
        assert _run(source, fn="f") == 48

    def test_alias_chain_future_scrutinee_runs(self) -> None:
        """An alias-of-alias chain canonicalizes hop by hop.

        RED on base (same E602 skip)."""
        source = """\
type FA = Future<Option<Int>>;
type FA2 = FA;

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @FA2 = async(Some(5));
  match await(@FA2.0) {
    Some(@Int) -> @Int.0 + 1,
    None -> 0 - 7
  }
}
"""
        assert _run(source, fn="f") == 6


class TestFuturePairLetBinding1039:
    """#1039: a `let` of a pair-represented `Future<T>` payload
    (`Future<String>`, `Future<Array<T>>`) binds two locals like a bare
    String/Array let.

    `Future<T>` is representation-transparent (#841), so `Future<String>`
    is an `i32_pair`.  Pre-fix the let-binding translator's pair detection
    (`_is_pair_type_name`) keyed on the literal `String`/`Array` names and
    was NOT Future-transparent, so `Future<String>`/`Future<Array<T>>`
    missed the pair branch, fell to the scalar branch where
    `_slot_name_to_wasm_type` recursed through the transparent wrapper to a
    pair inner and returned None, and the whole enclosing function was
    dropped with the [E602] loud skip ("has no WASM representation") on a
    check/verify-green program — same family as #1006/#1031/#1037/#1038.

    The fix makes `_is_pair_type_name` Future-transparent (string-form
    strip-and-recurse, mirroring `_slot_name_to_wasm_type`'s Future arm),
    which covers BOTH the composite-string sites in the let path: the
    binding (`context.translate_block`) and the read emit
    (`_translate_slot_ref`).  The scalar and pointer pins plus the
    `Future<Unit>` loud-skip pin prove the transparency is to the
    *payload's* representation, not "every Future is a pair".
    """

    def test_string_payload_let_compiles(self) -> None:
        """The bare bug: `let @Future<String>` must compile (bind two pair
        locals) so the enclosing function is exported, not E602-skipped.
        Returns a constant so it pins compilation independent of any read
        path.  RED on base (function dropped → not exported)."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<String> = async("hello");
  42
}
"""
        assert _run(source, fn="f") == 42

    def test_string_payload_value_survives_end_to_end(self) -> None:
        """The issue's repro: bind, await via the slot ref, read the String.
        `string_length("hello") == 5` proves the (ptr, len) pair survived —
        a mis-bound pair (one local) would corrupt the value or trap, not
        return exactly 5.  RED on base (E602 skip)."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<String> = async("hello");
  let @String = await(@Future<String>.0);
  string_length(@String.0)
}
"""
        assert _run(source, fn="f") == 5

    def test_array_payload_value_survives_end_to_end(self) -> None:
        """`Future<Array<Int>>` — the other pair payload — binds, awaits, and
        reads back: `array_length([7, 8, 9]) == 3`.  A distinctive length
        (not 0/1) rules out a coincident default.  RED on base (E602 skip)."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Array<Int>> = async([7, 8, 9]);
  let @Array<Int> = await(@Future<Array<Int>>.0);
  array_length(@Array<Int>.0)
}
"""
        assert _run(source, fn="f") == 3

    def test_scalar_payload_let_stays_scalar(self) -> None:
        """Precision pin: `Future<Int>` is a scalar (i64), NOT a pair — it
        must keep the single-local scalar path.  Green before and after the
        fix; fails only if the Future recursion over-broadens a scalar
        payload to a pair."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(41);
  await(@Future<Int>.0)
}
"""
        assert _run(source, fn="f") == 41

    def test_pointer_payload_let_stays_pointer(self) -> None:
        """Precision pin: `Future<Box>` (ADT payload) is an i32 heap pointer,
        NOT a pair — single-local pointer path.  Green before and after;
        guards the Future recursion against pair-treating a pointer
        payload."""
        source = """\
private data Box { Wrap(Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Box> = async(Wrap(42));
  let @Box = await(@Future<Box>.0);
  match @Box.0 {
    Wrap(@Int) -> @Int.0
  }
}
"""
        assert _run(source, fn="f") == 42

    def test_unit_payload_let_still_skips_loudly(self) -> None:
        """The loud skip is preserved: `Future<Unit>` wraps a zero-size
        payload with no WASM representation (Unit is neither a pair nor a
        scalar), so the let must STILL reach the [E602] skip — never be
        silently pair-bound.  Exercises the Future recursion directly: it
        must return False for the Unit payload, so `f` is dropped, not
        exported.  Green before and after the fix (`_compile` runs codegen
        without the checker's E183 zero-size gate, so this reaches the
        codegen skip)."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Unit> = async(());
  42
}
"""
        result = _compile(source)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert any("unsupported" in w.description.lower() for w in warnings)
        assert "f" not in result.exports


class TestAliasPairFuture1046:
    """#1046: an ALIAS to a pair-payload Future binds like its target.

    `type FS = Future<String>;` then `let @FS = async("hello");` was
    check+verify-green but E602-skipped the enclosing function: the pair
    predicate (`_is_pair_type_name`) resolved the alias through the
    name-only `_resolve_base_type_name`, which drops type arguments — `FS`
    resolved to bare `"Future"`, missed the #1039 Future arm, and fell to
    the scalar mapper, whose canonical spelling (`String`) has no scalar
    representation.  The predicate now canonicalizes an alias to its
    target's full compound spelling first (`_canonicalize_alias_slot_name`,
    the #1037 walk), so an alias behaves exactly like its target written
    directly.  The scalar-alias sibling (`type FI = Future<Int>`) was
    already closed by #1037's `_slot_name_to_wasm_type` wiring and is
    pinned here as the must-not-change control.
    """

    def test_alias_to_pair_future_let_runs(self) -> None:
        """The #1046 repro: alias to Future<String> binds, awaits, reads.

        RED on base (E602 skip; string_length must return exactly 5)."""
        source = """\
type FS = Future<String>;

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @FS = async("hello");
  string_length(await(@FS.0))
}
"""
        assert _run(source, fn="f") == 5

    def test_alias_chain_to_pair_future_let_runs(self) -> None:
        """An alias-of-alias chain ending at Future<String> canonicalizes
        hop by hop.  RED on base (E602 skip)."""
        source = """\
type FS = Future<String>;
type FS2 = FS;

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @FS2 = async("hello");
  string_length(await(@FS2.0))
}
"""
        assert _run(source, fn="f") == 5

    def test_alias_to_scalar_future_stays_scalar(self) -> None:
        """Control: `type FI = Future<Int>` binds one i64 local (#1037's
        fix) — the pair predicate must NOT claim it."""
        source = """\
type FI = Future<Int>;

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @FI = async(41);
  await(@FI.0)
}
"""
        assert _run(source, fn="f") == 41


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
        assert "call $rt.register_wrapper" in wat
        import re
        assert re.search(r"i32\.const 4\s*\n\s*local\.get \d+\s*\n\s*call \$rt.register_wrapper", wat), (
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
            def do_GET(self) -> None:
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

    def test_indirect_closure_await_ok_path_payload_intact(self) -> None:
        """#843 Ok-path pin (PR #868 panel, minor): the indirect
        ``await(apply_fn(closure, url))`` shape must deliver the REAL
        response body through the ``Ok`` arm.  The Err-message tests in
        tests/test_codegen_modules.py discriminate only via the refusal
        substring — an Ok-corruption (wrapper read as the ADT yields a
        garbage payload) would read as the same 0 there.  Here a local
        server returns a distinctive body and the test requires it
        byte-exact on stdout."""
        import http.server
        import threading

        body = b"OK-PAYLOAD-843"

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self) -> None:
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
type Fetcher = fn(String -> Future<Result<String, String>>) effects(<Http, Async>);

private fn run_fetch(@Fetcher, @String -> @Unit)
  requires(true) ensures(true) effects(<IO, Http, Async>)
{{
  let @Result<String, String> = await(apply_fn(@Fetcher.0, @String.0));
  match @Result<String, String>.0 {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print("ERR")
  }}
}}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO, Http, Async>)
{{
  run_fetch(
    fn(@String -> @Future<Result<String, String>>) effects(<Http, Async>) {{
      async(Http.get(@String.0))
    }},
    "http://127.0.0.1:{port}/ok"
  )
}}
""")
        finally:
            server.shutdown()
            server.server_close()
        assert out == "OK-PAYLOAD-843", out


class TestConcurrentAsyncAlias1109:
    """#1109 (found probing #1095): the fused-await classifier matched the
    literal type ``Future<Result<String, String>>`` only, so a future bound
    through an alias-typed ``let`` — or returned from a helper declared to
    return the alias — fused its ``async`` (call-shape fusion ignores the
    binding type) but identity-lowered the ``await``: the kind-4 handle
    wrapper was read as the Result ADT and every match fell to ``Err`` on a
    successful request.  Aliases are transparent everywhere else; the
    classifier now resolves them (transitively, param-substituting) before
    the literal check.  Pins: the ``async_await`` import must be emitted for
    both alias shapes, and the Ok payload must arrive byte-exact."""

    def test_alias_let_future_imports_async_await(self) -> None:
        """WAT shape: alias-typed let binding classifies for the fused-handle
        check — async fuses AND the await imports async_await."""
        result = _compile_ok("""
type F = Future<Result<String, String>>;

public fn fetch(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @F = async(Http.get(@String.0));
  await(@F.0)
}
""")
        assert '(import "vera" "async_http_get"' in result.wat, result.wat[:800]
        assert '(import "vera" "async_await"' in result.wat
        assert '(import "vera" "http_get"' not in result.wat

    def test_alias_fn_return_future_imports_async_await(self) -> None:
        """WAT shape, sibling: a helper declared `-> @F` registers in the
        future-return registry, so await(fetch(...)) emits the check."""
        result = _compile_ok("""
type F = Future<Result<String, String>>;

private fn fetch(@String -> @F)
  requires(true) ensures(true) effects(<Http, Async>)
{
  async(Http.get(@String.0))
}

public fn run(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http, Async>)
{
  await(fetch(@String.0))
}
""")
        assert '(import "vera" "async_http_get"' in result.wat, result.wat[:800]
        assert '(import "vera" "async_await"' in result.wat

    def test_alias_let_future_ok_payload_intact(self) -> None:
        """Runtime: the aliased future must deliver the REAL response body
        through the Ok arm — pre-fix the identity await read the wrapper as
        the ADT and every match fell to Err on a 200."""
        import http.server
        import threading

        body = b"OK-PAYLOAD-1109-LET"

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self) -> None:
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
type F = Future<Result<String, String>>;

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO, Http, Async>)
{{
  let @F = async(Http.get("http://127.0.0.1:{port}/ok"));
  let @Result<String, String> = await(@F.0);
  match @Result<String, String>.0 {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print("ERR")
  }};
  ()
}}
""")
        finally:
            server.shutdown()
            server.server_close()
        assert out == "OK-PAYLOAD-1109-LET", out

    def test_alias_fn_return_future_ok_payload_intact(self) -> None:
        """Runtime, sibling: await(fetch(url)) with `-> @F` delivers the real
        body through the Ok arm."""
        import http.server
        import threading

        body = b"OK-PAYLOAD-1109-FN"

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self) -> None:
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
type F = Future<Result<String, String>>;

private fn fetch(@String -> @F)
  requires(true) ensures(true) effects(<Http, Async>)
{{
  async(Http.get(@String.0))
}}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO, Http, Async>)
{{
  let @Result<String, String> = await(fetch("http://127.0.0.1:{port}/ok"));
  match @Result<String, String>.0 {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print("ERR")
  }};
  ()
}}
""")
        finally:
            server.shutdown()
            server.server_close()
        assert out == "OK-PAYLOAD-1109-FN", out

    def test_payload_alias_future_imports_async_await(self) -> None:
        """WAT shape: an alias INSIDE the future's payload (`Future<R>` with
        `type R = Result<String, String>`) classifies too — the terminal
        check canonicalizes type arguments recursively, not just the outer
        name (PR #1110 review: the outer-name-only resolver left this shape
        identity-lowered — same #1109 mis-lower one level down)."""
        result = _compile_ok("""
type R = Result<String, String>;

public fn fetch(@String -> @R)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Future<R> = async(Http.get(@String.0));
  await(@Future<R>.0)
}
""")
        assert '(import "vera" "async_http_get"' in result.wat, result.wat[:800]
        assert '(import "vera" "async_await"' in result.wat
        assert '(import "vera" "http_get"' not in result.wat

    def test_payload_alias_future_ok_payload_intact(self) -> None:
        """Runtime: `Future<R>` delivers the real body through the Ok arm."""
        import http.server
        import threading

        body = b"OK-PAYLOAD-1109-PAYLOAD"

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self) -> None:
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
type R = Result<String, String>;

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO, Http, Async>)
{{
  let @Future<R> = async(Http.get("http://127.0.0.1:{port}/ok"));
  let @R = await(@Future<R>.0);
  match @R.0 {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print("ERR")
  }};
  ()
}}
""")
        finally:
            server.shutdown()
            server.server_close()
        assert out == "OK-PAYLOAD-1109-PAYLOAD", out

    def test_alias_chain_fn_return_imports_async_await(self) -> None:
        """WAT shape: a TWO-HOP alias chain on a helper's declared return
        (`-> @F` with `type F = G; type G = Future<...>`) registers in the
        future-return registry — transitive resolution in
        compute_future_ret_fns, not just the slot arm."""
        result = _compile_ok("""
type G = Future<Result<String, String>>;
type F = G;

private fn fetch(@String -> @F)
  requires(true) ensures(true) effects(<Http, Async>)
{
  async(Http.get(@String.0))
}

public fn run(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http, Async>)
{
  await(fetch(@String.0))
}
""")
        assert '(import "vera" "async_http_get"' in result.wat, result.wat[:800]
        assert '(import "vera" "async_await"' in result.wat

    def test_two_async_gets_overlap_deterministically_aliased(self) -> None:
        """The alias-typed overlap pin (PR #1110 review): two fused gets
        bound through an alias CHAIN (`type G = Future<...>; type F = G`)
        actually overlap — the server holds request A until B arrives (3s
        bound), so eager evaluation answers SEQUENTIAL (A times out before
        B is ever issued) while concurrent answers CONCURRENT for both —
        AND both real payloads arrive through the Ok arms.  Genuine
        concurrency and transitive alias substitution in one regression."""
        import http.server
        import threading

        arrived_b = threading.Event()
        log: list[str] = []

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self) -> None:
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
type G = Future<Result<String, String>>;
type F = G;

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO, Http, Async>)
{{
  let @F = async(Http.get("http://127.0.0.1:{port}/a"));
  let @G = async(Http.get("http://127.0.0.1:{port}/b"));
  let @Result<String, String> = await(@F.0);
  match @Result<String, String>.0 {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print("ERR-A")
  }};
  let @Result<String, String> = await(@G.0);
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


class TestHttpServerCompilability305:
    """#305: a handler declaring <HttpServer> compiles to WASM (the
    marker effect is in the compilability whitelist) and exports."""

    def test_handler_with_httpserver_compiles_and_exports(self) -> None:
        result = _compile_ok("""
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  match @Request.0 {
    Request(@String, @String, @Map<String, String>, @String) ->
      Response(200, map_new(), @String.0)
  }
}
""")
        assert "handle" in result.exports, (
            f"handler not exported; diagnostics: "
            f"{[d.description for d in result.diagnostics]}"
        )


class TestEffectCompositeTypeArgs914:
    """#914: effect handlers (State/Exn) and effect-op results over
    COMPOSITE / parameterized type arguments must compile and run.

    Six gaps, all ``vera check``-green but failing at codegen, split
    across three root causes:

    * A — effect-op RESULT type not inferred in constructor-argument /
      match-scrutinee position (function silently skipped).
    * B — effect-handler WAT names not escaped for composite type args,
      and an emit↔call desync between the full slot name used for the
      ``(import …)`` decl and the base name used in the handler body.
    * C — the Exn payload ``@T`` binding pushed the base type name, so a
      ``@Option<Int>.n`` slot ref in the handler body dangled (E699).

    A primitive-effect regression pin (`State<Int>` / `Exn<Int>`) lives
    in the sibling `TestStateEffect` / `TestExnHandlers` classes; the
    two pins below assert the composite path does not perturb it.
    """

    # --- Root cause A ------------------------------------------------

    def test_a1_state_get_directly_as_constructor_field(self) -> None:
        """A1: `get(())` (State<Int> op result) used directly as a
        Tuple constructor field. The op result type must be inferred at
        the constructor-argument site, else the function is skipped."""
        src = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{
  let @Tuple<Int, Int> = Tuple(get(()), 1);
  0
}
"""
        result = _compile_ok(src)
        assert "main" in result.exports, (
            "main was skipped — effect-op result type not inferred in "
            f"constructor-arg position; diagnostics: "
            f"{[d.description for d in result.diagnostics]}"
        )
        assert _run(src, fn="main") == 0

    def test_a2_match_scrutinee_is_effect_op_with_adt_result(self) -> None:
        """A2: `match get(())` where `get` returns a non-primitive ADT
        (`Box`). The op result type must be inferred at the
        match-scrutinee site."""
        src = """\
private data Box { Box(Int) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Box>](@Box = Box(0)) {
    get(@Unit) -> { resume(@Box.0) },
    put(@Box) -> { resume(()) }
  } in {
    match get(()) {
      Box(@Int) -> @Int.0
    }
  }
}
"""
        result = _compile_ok(src)
        assert "main" in result.exports, (
            "main was skipped — effect-op result type not inferred in "
            f"match-scrutinee position; diagnostics: "
            f"{[d.description for d in result.diagnostics]}"
        )
        assert _run(src, fn="main") == 0

    # --- Root cause B ------------------------------------------------

    def test_b1_state_handler_over_tuple(self) -> None:
        """B1: `handle[State<Tuple<Int, Int>>]` — the composite type arg
        must be escaped for the `state_*` WAT identifiers (raw `<`, `,`,
        ` ` are illegal in a WAT identifier)."""
        src = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Tuple<Int, Int>>](@Tuple<Int, Int> = Tuple(20, 22)) {
    put(@Tuple<Int, Int>) -> { resume(()) }
  } in {
    0
  }
}
"""
        assert _run(src, fn="main") == 0

    def test_b2_state_handler_over_option_get_and_put(self) -> None:
        """B2: `handle[State<Option<Int>>]` exercising get + put — the
        handler-body `state_push`/`get`/`put`/`pop` calls must use the
        SAME escaped full name as the `(import …)` decls (pre-fix the
        body used the base name `Option`, the import the full
        `Option<Int>` → `unknown func $vera.state_push_Option`)."""
        src = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(5)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    get(());
    7
  }
}
"""
        assert _run(src, fn="main") == 7

    def test_b3_exn_handler_tag_over_tuple(self) -> None:
        """B3: a function declaring `<Exn<Tuple<Int, Int>>>` emits an
        `(tag $exn_Tuple<Int, Int> …)` — the composite type arg must be
        escaped. Post-fix it compiles to valid WAT (main exported) and,
        as an uncaught throw, traps at run exactly like the primitive
        `Exn<Int>` case."""
        src = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(<Exn<Tuple<Int, Int>>>)
{
  throw(Tuple(1, 2))
}
"""
        result = _compile_ok(src)
        assert "main" in result.exports, (
            "main was skipped or emitted invalid WAT for the composite "
            f"Exn tag; diagnostics: "
            f"{[d.description for d in result.diagnostics]}"
        )
        # Uncaught throw traps at run (same as primitive Exn<Int>).
        with pytest.raises(WasmTrapError, match="thrown Wasm exception"):
            execute(result, fn_name="main")

    # --- Root cause C ------------------------------------------------

    def test_c_exn_payload_binding_over_option(self) -> None:
        """C: `handle[Exn<Option<Int>>]` — the caught-payload `@T`
        binding must materialize under the full canonical slot name
        `Option<Int>`, else `@Option<Int>.0` in the handler body
        resolves to no local (dangling @T.n, E699)."""
        src = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Option<Int>>] {
    throw(@Option<Int>) -> { option_unwrap_or(@Option<Int>.0, 0) }
  } in {
    throw(Some(9))
  }
}
"""
        assert _run(src, fn="main") == 9

    # --- Primitive regression pins (must be unaffected) --------------

    def test_primitive_state_int_still_works(self) -> None:
        """Pin: the common primitive `State<Int>` path is untouched."""
        src = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{
  put(42);
  get(())
}
"""
        assert _run(src, fn="main") == 42

    def test_primitive_exn_int_still_works(self) -> None:
        """Pin: the common primitive `Exn<Int>` path is untouched."""
        src = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 + 100 }
  } in {
    throw(42)
  }
}
"""
        assert _run(src, fn="main") == 142

    # --- Root cause D (round 2) --------------------------------------

    def test_old_state_composite_runs(self) -> None:
        """#914 finding 1: `old(State<Option<Int>>)` in a postcondition must
        allocate a pre-execution snapshot local and run, not crash codegen.

        Pre-fix `_extract_state_type_name` returned the BASE name (`Option`),
        which missed the canonical-keyed `_state_types` entry (`Option<Int>`),
        so no snapshot local was allocated and the `old` read raised an
        uncaught `CodegenInvariantError` (`old(State<T>) has no saved
        pre-execution state local`) at run."""
        src = """\
public fn keep(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Option<Int>>) == old(State<Option<Int>>))
  effects(<State<Option<Int>>>)
{
  let @Option<Int> = get(());
  put(@Option<Int>.0);
  ()
}
"""
        result = _compile_ok(src)
        assert "keep" in result.exports, (
            "keep was skipped for the composite old(State) snapshot; "
            f"diagnostics: {[d.description for d in result.diagnostics]}"
        )
        # get(()) defaults to a null Option pointer (0); put stores it back
        # unchanged, so new == old holds and the postcondition passes.
        exec_result = _run_state(src, fn="keep")
        assert exec_result.value is None  # Unit return

    def test_old_state_composite_verifies_and_runs_cli(
        self, tmp_path: object,
    ) -> None:
        """#914 finding 1 (CLI end-to-end): the composite `old(State<T>)`
        program `vera run`s with exit 0 (no traceback) and `vera verify`s."""
        import subprocess
        import sys
        from pathlib import Path

        src = """\
public fn keep(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Option<Int>>) == old(State<Option<Int>>))
  effects(<State<Option<Int>>>)
{
  let @Option<Int> = get(());
  put(@Option<Int>.0);
  ()
}
"""
        p = Path(tmp_path) / "old_state.vera"  # type: ignore[arg-type]
        p.write_text(src, encoding="utf-8")
        # Invoke the CLI as a module (`python -m vera.cli`) rather than the
        # `vera` console-script path — the latter is `vera.exe` on Windows, so
        # `Path(sys.executable).parent / "vera"` does not exist there ([WinError 2]).
        for cmd in (["run", "--fn", "keep"], ["verify", "--quiet"]):
            proc = subprocess.run(
                [sys.executable, "-m", "vera.cli", *cmd, str(p)],
                capture_output=True, text=True, encoding="utf-8", timeout=120,
                check=False,
            )
            assert proc.returncode == 0, (
                f"vera {cmd[0]} failed: {proc.stdout}\n{proc.stderr}"
            )
            assert "CodegenInvariantError" not in proc.stderr
            assert "Traceback" not in proc.stderr

    def test_nested_composite_state_distinct_names_and_values(self) -> None:
        """#914 finding 2: two State handlers over DISTINCT nested-composite
        types must produce DISTINCT mangled `state_*` names and independent
        cells — pre-fix `_type_expr_to_slot_name` dropped the inner type args
        (`Option<Tuple<Int, Int>>` and `Option<Tuple<Bool, Bool>>` both
        collapsed to the slot name `Option<Tuple>` → the SAME import)."""
        src = """\
private fn use_int_pair(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Tuple<Int, Int>>>](@Option<Tuple<Int, Int>> = Some(Tuple(3, 4))) {
    get(@Unit) -> { resume(@Option<Tuple<Int, Int>>.0) },
    put(@Option<Tuple<Int, Int>>) -> { resume(()) }
  } in {
    match get(()) {
      Some(@Tuple<Int, Int>) -> match @Tuple<Int, Int>.0 { Tuple(@Int) -> @Int.0 },
      None -> 0
    }
  }
}

private fn use_bool_pair(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Tuple<Bool, Bool>>>](@Option<Tuple<Bool, Bool>> = Some(Tuple(true, false))) {
    get(@Unit) -> { resume(@Option<Tuple<Bool, Bool>>.0) },
    put(@Option<Tuple<Bool, Bool>>) -> { resume(()) }
  } in {
    100
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  use_int_pair(()) + use_bool_pair(())
}
"""
        result = _compile_ok(src)
        assert "main" in result.exports, (
            "main skipped; diagnostics: "
            f"{[d.description for d in result.diagnostics]}"
        )
        wat = result.wat or ""
        # The two nested composites must NOT collapse to the same mangled
        # import name.  Pre-fix both were `state_get_Option_LTuple_R`.
        assert "state_get_Option_LTuple_LInt_CInt_R_R" in wat, wat[:400]
        assert "state_get_Option_LTuple_LBool_CBool_R_R" in wat, wat[:400]
        # use_int_pair reads the stored Some(Tuple(3, 4)) -> first field 3;
        # use_bool_pair returns 100 -> total 103.
        assert _run(src, fn="main") == 103

    def test_nested_composite_exn_distinct_tags(self) -> None:
        """#914 finding 2 (Exn tag): two Exn handlers over distinct
        nested-composite payloads must emit DISTINCT tags — a shared tag
        would be a type-confusion (a `Tuple<Int, Int>` payload caught as a
        `Tuple<Bool, Bool>`)."""
        src = """\
private fn a(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Option<Tuple<Int, Int>>>] {
    throw(@Option<Tuple<Int, Int>>) -> { 1 }
  } in {
    2
  }
}
private fn b(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Option<Tuple<Bool, Bool>>>] {
    throw(@Option<Tuple<Bool, Bool>>) -> { 3 }
  } in {
    4
  }
}
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  a(()) + b(())
}
"""
        result = _compile_ok(src)
        wat = result.wat or ""
        assert "$exn_Option_LTuple_LInt_CInt_R_R" in wat, wat[:400]
        assert "$exn_Option_LTuple_LBool_CBool_R_R" in wat, wat[:400]
        assert _run(src, fn="main") == 6  # a→2, b→4


# =====================================================================
# The declared-row State op registry: shadow-respecting, first-valid-wins
# =====================================================================

_SHADOWED_OP_ROW = """
private fn %s

public fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>, State<Bool>>)
{
  put(1);
  get(())
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Bool>](@Bool = false) {
    get(@Unit) -> { resume(@Bool.0) }
  } in {
    handle[State<Int>](@Int = 5) {
      get(@Unit) -> { resume(@Int.0) }
    } in {
      probe(())
    }
  }
}
"""

_SHADOW_GET = """get(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  77
}"""

_SHADOW_PUT = """put(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}"""


@pytest.mark.parametrize(
    ("shadow_fn", "shadowed", "intrinsic"),
    [
        pytest.param(
            _SHADOW_GET, "get", "$vera.state_put_Int", id="user_get"),
        pytest.param(
            _SHADOW_PUT, "put", "$vera.state_get_Int", id="user_put"),
    ],
)
def test_a_user_fn_shadows_one_state_op_without_disturbing_its_sibling(
    shadow_fn: str, shadowed: str, intrinsic: str,
) -> None:
    """Shadowing is decided per op and survives every instance in the row.

    `emit_function` populates the declared-row State op registry by walking
    the row, and `effects(<State<Int>, State<Bool>>)` walks it twice — so the
    question is whether the second instantiation can re-register or remap an
    op the first one skipped because a user function shadows it, and whether
    `get` and `put` answer that question the same way (round-5 review).  They
    do: each op is registered only when no user function of that name exists
    AND no earlier instantiation registered it, so the shadowed name compiles
    to the user function while its sibling keeps the FIRST instantiation's
    `Int` intrinsic — never the second's `Bool` one.
    """
    wat = _compile_ok(_SHADOWED_OP_ROW % shadow_fn).wat or ""
    # Scoped to `probe`'s own body: the module legitimately declares the
    # `Bool` imports for `main`'s handler, so a whole-module search would
    # confirm nothing about which family `probe` calls.
    body = re.search(r"\(func \$probe\b.*?\n  \)", wat, re.S)
    assert body is not None, f"no $probe function in the emitted WAT:\n{wat[:400]}"
    calls = [
        line.strip() for line in body.group(0).splitlines()
        if "call " in line
    ]
    assert any(c.endswith(f"${shadowed}") for c in calls), (
        f"the user-defined `{shadowed}` is not called from probe — the "
        f"declared row re-registered the shadowed op: {calls}"
    )
    assert not any(f"$vera.state_{shadowed}_" in c for c in calls), (
        f"a State intrinsic for `{shadowed}` was emitted despite the user "
        f"function shadowing it: {calls}"
    )
    assert any(intrinsic in c for c in calls), (
        "the sibling op lost its registration, or took the SECOND "
        f"instantiation's Bool family instead of the first's Int: {calls}"
    )
    assert not any("_Bool" in c for c in calls), (
        f"the second State instantiation overwrote the first's: {calls}"
    )
