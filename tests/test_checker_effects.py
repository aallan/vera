"""Tests for the Vera type checker — effects (effect declarations, abilities, effect subtyping, async, handler typing).

Split from tests/test_checker.py (#420). Shared helpers live in tests/checker_helpers.py.
"""
from __future__ import annotations

from tests.checker_helpers import (
    _check,
    _check_clean,
    _check_err,
    _check_ok,
    _warnings,
)


# =====================================================================
# Effects
# =====================================================================

class TestEffects:

    def test_pure_function(self) -> None:
        _check_ok("""
private fn pure_fn(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_effect_declaration(self) -> None:
        _check_ok("""
effect Logger {
  op log(String -> Unit);
}

private fn greet(@String -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  Logger.log(@String.0)
}
""")

    def test_pure_calling_effectful_error(self) -> None:
        _check_err("""
effect Logger {
  op log(String -> Unit);
}

private fn bad(@String -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  Logger.log(@String.0)
}
""", "Pure function")

    def test_handler_basic(self) -> None:
        """Handler with resume produces no errors or warnings."""
        _check_clean("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""")

    def test_resume_wrong_arg_type(self) -> None:
        """resume() type-checks its argument against operation return type."""
        # get(Unit) -> Int, so resume expects Int; passing Unit is a mismatch
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(()) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""", "has type Unit, expected Int")

    def test_resume_wrong_arity(self) -> None:
        """resume() takes exactly one argument."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0, @Int.1) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""", "expects 1 argument")

    def test_resume_outside_handler(self) -> None:
        """resume() outside a handler scope is unresolved."""
        diags = _check("""
private fn foo(@Unit -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  resume(42)
}
""")
        warns = [d for d in diags if d.severity == "warning"]
        assert any("Unresolved function 'resume'" in w.description
                    for w in warns), \
            f"Expected unresolved resume warning, got: " \
            f"{[w.description for w in warns]}"

    def test_with_clause_valid(self) -> None:
        """Handler with-clause with correct type produces no errors."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    put(42);
    get(())
  }
}
""")

    def test_with_clause_type_mismatch(self) -> None:
        """Handler with-clause value must match state type (E335)."""
        errs = _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = true
  } in {
    get(())
  }
}
""", "State update expression")
        assert any(e.error_code == "E335" for e in errs)

    def test_with_clause_no_state(self) -> None:
        """Handler with-clause without handler state is an error (E333)."""
        errs = _check_err("""
effect Exn<E> {
  op throw(E -> Never);
}
private fn bar(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> { 0 } with @String = @String.0
  } in {
    42
  }
}
""", "no state declaration")
        assert any(e.error_code == "E333" for e in errs)

    def test_with_clause_wrong_slot_type(self) -> None:
        """Handler with-clause type must match handler state type (E334)."""
        errs = _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Bool = true
  } in {
    get(())
  }
}
""", "does not match handler state type")
        assert any(e.error_code == "E334" for e in errs)

    def test_handle_unknown_effect_is_e330(self) -> None:
        """Handling an undeclared effect reports E330, not just a message."""
        errs = _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Bogus](@Int = 0) {
    get(@Unit) -> { resume(0) }
  } in {
    0
  }
}
""", "Unknown effect")
        assert any(e.error_code == "E330" for e in errs)

    def test_handler_unknown_operation_is_e332(self) -> None:
        """A handler clause for an operation the effect lacks reports E332."""
        errs = _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) },
    bogus(@Unit) -> { resume(()) }
  } in {
    get(())
  }
}
""", "has no operation")
        assert any(e.error_code == "E332" for e in errs)

    def test_handle_expression_has_body_type(self) -> None:
        """The handle expression's type is its body's type, so a mismatch with
        the function return type surfaces (kills `return body_type`)."""
        # Handler body yields Int (get's return type); foo declares @String.
        errs = _check_err("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""", "body has type Int")
        assert any(e.error_code == "E121" for e in errs)

    def test_state_effect_builtin(self) -> None:
        """The built-in State<T> effect is available."""
        _check_ok("""
private fn incr(@Unit -> @Unit)
  requires(true) ensures(true) effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
""")

    def test_qualified_effect_call(self) -> None:
        _check_ok("""
effect Counter {
  op get_count(Unit -> Int);
  op increment(Unit -> Unit);
}

private fn use_counter(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Counter>)
{
  Counter.increment(())
}
""")

    # ----- Diverge (built-in marker effect, Chapter 7 §7.7.3) --------

    def test_diverge_type_checks(self) -> None:
        """effects(<Diverge>) is a recognised built-in effect."""
        _check_ok("""
private fn loop(@Unit -> @Int)
  requires(true) ensures(true) effects(<Diverge>)
{ 0 }
""")

    def test_diverge_combined_with_io(self) -> None:
        """Diverge composes with other effects in the same row."""
        _check_ok("""
private fn serve(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Diverge, IO>)
{
  IO.print("running");
  ()
}
""")

    def test_diverge_no_operations(self) -> None:
        """Diverge has no operations — qualified calls produce a warning."""
        warns = _warnings("""
private fn bad(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Diverge>)
{
  Diverge.stop(())
}
""")
        assert any("Unresolved qualified call" in w.description for w in warns), \
            f"Expected unresolved call warning, got: {[w.description for w in warns]}"

    def test_diverge_registered_in_env(self) -> None:
        """Diverge is present in the environment's effect registry."""
        from vera.environment import TypeEnv
        env = TypeEnv()
        info = env.lookup_effect("Diverge")
        assert info is not None
        assert info.name == "Diverge"
        assert info.type_params is None
        assert info.operations == {}


# =====================================================================
# Abilities (Spec §9.8) — PR 2: registration + constraint validation
# =====================================================================

class TestAbilities:
    """Ability declarations, constraint validation, and operation resolution."""

    def test_ability_decl_accepted(self) -> None:
        """Ability declaration is accepted without errors."""
        _check_ok("""
        ability Eq<T> {
          op eq(T, T -> Bool);
        }

        private fn main(@Unit -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        { 0 }
        """)

    def test_forall_with_constraint_accepted(self) -> None:
        """Function with forall constraint is accepted."""
        _check_ok("""
        private forall<T where Eq<T>> fn contains(@Array<T>, @T -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        { true }
        """)

    def test_ability_with_builtin_eq(self) -> None:
        """Built-in Eq ability: eq() call in constrained function resolves."""
        _check_ok("""
        private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        { eq(@T.1, @T.0) }
        """)

    def test_ability_op_resolves_return_type(self) -> None:
        """eq() returns Bool, usable in if condition."""
        _check_ok("""
        private forall<T where Eq<T>> fn check(@T, @T -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          if eq(@T.1, @T.0) then { 1 } else { 0 }
        }
        """)

    def test_user_defined_ability_op_call(self) -> None:
        """User-defined ability operation resolves in constrained function."""
        _check_ok("""
        ability Show<T> {
          op show(T -> String);
        }

        private forall<T where Show<T>> fn display(@T -> @String)
          requires(true)
          ensures(true)
          effects(pure)
        { show(@T.0) }
        """)

    def test_unknown_ability_in_constraint(self) -> None:
        """Unknown ability in constraint → E180."""
        _check_err("""
        private forall<T where Unknown<T>> fn f(@T -> @T)
          requires(true)
          ensures(true)
          effects(pure)
        { @T.0 }
        """, "Unknown ability 'Unknown'")

    def test_undeclared_typevar_in_constraint(self) -> None:
        """Constraint references undeclared type variable → E181."""
        _check_err("""
        private forall<T where Eq<X>> fn f(@T -> @T)
          requires(true)
          ensures(true)
          effects(pure)
        { @T.0 }
        """, "undeclared type variable 'X'")

    def test_ability_op_wrong_arity(self) -> None:
        """Ability operation with wrong argument count → E240."""
        errs = _check_err("""
        private forall<T where Eq<T>> fn bad(@T -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        { eq(@T.0) }
        """, "expects 2 argument(s), got 1")
        assert any(e.error_code == "E240" for e in errs)

    def test_ability_op_type_mismatch(self) -> None:
        """Ability operation with mismatched argument types → E241."""
        errs = _check_err("""
        private fn bad(@Int, @String -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        { eq(@Int.0, @String.0) }
        """, "Argument 1 of 'eq'")
        assert any(e.error_code == "E241" for e in errs)

    def test_effect_op_wrong_arity_is_e203(self) -> None:
        """An effect operation called with the wrong argument count reports E203."""
        errs = _check_err("""
effect Counter { op tick(Int -> Int); }

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(<Counter>)
{ Counter.tick(1, 2) }
""", "expects 1 argument")
        assert any(e.error_code == "E203" for e in errs)

    def test_effect_op_arg_type_mismatch_is_e204(self) -> None:
        """An effect operation argument of the wrong type reports E204."""
        errs = _check_err("""
effect Counter { op tick(Int -> Int); }

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(<Counter>)
{ Counter.tick(true) }
""", "Argument 0 of 'tick'")
        assert any(e.error_code == "E204" for e in errs)


# =====================================================================
# Effect Subtyping (Spec §7.8)
# =====================================================================

class TestEffectSubtyping:
    """Call-site effect checking — functions can only call functions
    whose effects are a subset of the caller's effect row."""

    def test_pure_calling_effectful_fn_error(self) -> None:
        """Pure function calling an effectful *function* (not an op) → E125."""
        _check_err("""
effect Logger {
  op log(String -> Unit);
}

private fn effectful(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  Logger.log("hi")
}

private fn bad(@Unit -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  effectful(())
}
""", "requires effects(<Logger>) but call site only allows effects(pure)")

    def test_effectful_calling_same_effect_ok(self) -> None:
        """Calling a function with the same effect row is fine."""
        _check_ok("""
effect Logger {
  op log(String -> Unit);
}

private fn effectful(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  Logger.log("hi")
}

private fn caller(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  effectful(())
}
""")

    def test_effectful_calling_subset_ok(self) -> None:
        """Calling a function whose effects are a subset of the caller's."""
        _check_ok("""
effect Logger {
  op log(String -> Unit);
}

effect Tracer {
  op trace(String -> Unit);
}

private fn log_only(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  Logger.log("hi")
}

private fn caller(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger, Tracer>)
{
  log_only(())
}
""")

    def test_effectful_calling_superset_error(self) -> None:
        """Calling a function that needs more effects than the caller has."""
        _check_err("""
effect Logger {
  op log(String -> Unit);
}

effect Tracer {
  op trace(String -> Unit);
}

private fn needs_both(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger, Tracer>)
{
  Logger.log("hi");
  Tracer.trace("t")
}

private fn caller(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  needs_both(())
}
""", "requires effects(<Logger, Tracer>) but call site only allows effects(<Logger>)")

    def test_handler_discharges_effect_ok(self) -> None:
        """Handler body can use effects — handler discharges them."""
        _check_ok("""
private fn run(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(42);
    get(())
  }
}
""")

    def test_pure_calling_pure_fn_ok(self) -> None:
        """Pure calling pure is always fine."""
        _check_ok("""
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

private fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  helper(@Int.0)
}
""")

    def test_io_calling_pure_fn_ok(self) -> None:
        """An IO context can call a pure function (pure <: IO)."""
        _check_ok("""
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

private fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  helper(@Int.0)
}
""")


# =====================================================================
# Async effect
# =====================================================================


class TestAsyncEffect:
    """Async effect and Future<T> type checking."""

    def test_async_ok(self) -> None:
        """async(expr) in a function with effects(<Async>) type-checks."""
        _check_ok("""
private fn f(-> @Future<Int>)
  requires(true) ensures(true) effects(<Async>)
{ async(42) }
""")

    def test_await_ok(self) -> None:
        """await(future) in a function with effects(<Async>) type-checks."""
        _check_ok("""
private fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(42);
  await(@Future<Int>.0)
}
""")

    def test_async_requires_effect(self) -> None:
        """async(expr) in effects(pure) function produces an error."""
        _check_err("""
private fn f(-> @Future<Int>)
  requires(true) ensures(true) effects(pure)
{ async(42) }
""", "effect")

    def test_await_requires_effect(self) -> None:
        """await(future) in effects(pure) function produces an error."""
        _check_err("""
private fn f(@Future<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ await(@Future<Int>.0) }
""", "effect")

    def test_async_wrong_arity(self) -> None:
        """async() with no arguments is an error."""
        _check_err("""
private fn f(-> @Future<Int>)
  requires(true) ensures(true) effects(<Async>)
{ async() }
""", "expects 1 argument")

    def test_await_wrong_type(self) -> None:
        """await(42) where 42 is Int not Future<T> is an error."""
        _check_err("""
private fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ await(42) }
""", "expected Future")

    def test_async_with_io(self) -> None:
        """Async composes with IO in the same effect set."""
        _check_ok("""
private fn f(-> @Unit)
  requires(true) ensures(true) effects(<IO, Async>)
{
  let @Future<Int> = async(42);
  IO.print(to_string(await(@Future<Int>.0)));
  ()
}
""")


class TestAsyncConcurrencyWhitelist841:
    """#841: async(e) is concurrency-eligible only when e's effect row is
    within the commutative whitelist ({Http} in v1).  Anything else evaluates
    eagerly and the checker says so with a W002 warning — never silently."""

    def test_async_over_http_no_warning(self) -> None:
        """async(Http.get(...)) is whitelisted — no eager-evaluation warning."""
        warnings = _warnings("""
private fn f(@String -> @Future<Result<String, String>>)
  requires(true) ensures(true) effects(<Http, Async>)
{ async(Http.get(@String.0)) }
""")
        assert not any(w.error_code == "W002" for w in warnings), warnings

    def test_async_pure_no_warning(self) -> None:
        """async(pure expr) is trivially commutative — no warning."""
        warnings = _warnings("""
private fn f(-> @Future<Int>)
  requires(true) ensures(true) effects(<Async>)
{ async(42) }
""")
        assert not any(w.error_code == "W002" for w in warnings), warnings

    def test_async_over_io_warns_eager(self) -> None:
        """async over an IO-effect argument evaluates eagerly — W002."""
        warnings = _warnings("""
private fn f(-> @Future<Unit>)
  requires(true) ensures(true) effects(<IO, Async>)
{ async(IO.print("hi")) }
""")
        w002 = [w for w in warnings if w.error_code == "W002"]
        assert w002, f"expected W002, got: {[ (w.error_code, w.description) for w in warnings ]}"
        assert "eagerly" in w002[0].description.lower()

    def test_async_over_effectful_fn_call_warns_eager(self) -> None:
        """async over a call to a user function whose row is outside the
        whitelist ({IO} here) warns — the rule sees through fn calls."""
        warnings = _warnings("""
private fn log_and_get(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("side effect");
  7
}

private fn f(-> @Future<Int>)
  requires(true) ensures(true) effects(<IO, Async>)
{ async(log_and_get()) }
""")
        w002 = [w for w in warnings if w.error_code == "W002"]
        assert w002, f"expected W002, got: {[ (w.error_code, w.description) for w in warnings ]}"

    def test_async_over_http_via_fn_call_no_warning(self) -> None:
        """A user function whose row is exactly {Http} stays whitelisted."""
        warnings = _warnings("""
private fn fetch(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http>)
{ Http.get(@String.0) }

private fn f(@String -> @Future<Result<String, String>>)
  requires(true) ensures(true) effects(<Http, Async>)
{ async(fetch(@String.0)) }
""")
        assert not any(w.error_code == "W002" for w in warnings), warnings


# =====================================================================
# Coverage: control.py — handler type-checking
# =====================================================================

class TestHandlerCoverage:
    """Cover missed lines in handler type-checking."""

    # --- Lines 359, 363-368: unknown effect in handler ---

    def test_handle_unknown_effect(self) -> None:
        """Handler with unknown effect returns UnknownType (lines 363-368)."""
        diags = _check("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[NoSuchEffect] {
    some_op(@Int) -> { resume(()) }
  } in {
    42
  }
}
""")
        # Should produce a diagnostic mentioning the unknown effect
        assert any(
            "NoSuchEffect" in d.description for d in diags
        ), f"Expected diagnostic mentioning 'NoSuchEffect', got: {[d.description for d in diags]}"

    # --- Lines 400-406: unknown operation in handler clause ---

    def test_handle_unknown_operation(self) -> None:
        """Handler clause for non-existent operation produces E332 (lines 400-406)."""
        _check_err("""
effect Logger {
  op log(String -> Unit);
}

private fn foo(@Unit -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  handle[Logger] {
    nonexistent(@String) -> { resume(()) }
  } in {
    Logger.log("hi")
  }
}
""", "has no operation")

    # --- Line 470: restore saved_resume (when resume was previously bound) ---

    def test_nested_handlers_resume_restore(self) -> None:
        """Nested handlers restore outer resume binding (line 470)."""
        _check_ok("""
effect Inner {
  op inner_op(Unit -> Int);
}

effect Outer {
  op outer_op(Unit -> Int);
}

private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Outer] {
    outer_op(@Unit) -> {
      handle[Inner] {
        inner_op(@Unit) -> { resume(0) }
      } in {
        resume(inner_op(()))
      }
    }
  } in {
    outer_op(())
  }
}
""")

    # --- Lines 484-485: ConcreteEffectRow merging ---

    def test_handler_merges_effect_rows(self) -> None:
        """Handler body adds effect to existing ConcreteEffectRow (lines 484-485)."""
        _check_ok("""
effect Logger {
  op log(String -> Unit);
}

private fn foo(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  handle[Logger] {
    log(@String) -> { resume(()) }
  } in {
    Logger.log("inside handler");
    IO.print("also IO");
    ()
  }
}
""")

    def test_handler_state_init_type_mismatch(self) -> None:
        """Handler state initial value type doesn't match declared type (E331)."""
        errs = _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = "wrong") {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""", "Handler state initial value")
        assert any(e.error_code == "E331" for e in errs)


class TestHttpServerEffect305:
    """#305: <HttpServer> is a built-in marker effect (no operations —
    the accept loop lives in the host `vera serve` driver), and
    Request / Response are built-in prelude ADTs so a handler is an
    ordinary total, contract-checked function:

        public fn handle(@Request -> @Response) effects(<HttpServer>)
    """

    def test_httpserver_effect_row_accepted(self) -> None:
        _check_clean("""
public fn tick(@Int -> @Int)
  requires(true) ensures(true) effects(<HttpServer>)
{ @Int.0 + 1 }
""")

    def test_request_response_prelude_types(self) -> None:
        """Request/Response are prelude ADTs: fields destructure by
        match, Response constructs directly."""
        _check_clean("""
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  match @Request.0 {
    Request(@String, @String, @Map<String, String>, @String) ->
      Response(200, map_new(), @String.0)
  }
}
""")

    def test_httpserver_composes_with_state(self) -> None:
        _check_clean("""
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer, State<Int>>)
{
  put(get(()) + 1);
  Response(200, map_new(), "ok")
}
""")

    def test_response_status_contract_verifies(self) -> None:
        """The headline #305 property: a status-range postcondition on a
        handler is an ordinary contract."""
        _check_clean("""
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{ Response(204, map_new(), "") }
""")

    def test_httpserver_in_effect_registry(self) -> None:
        """HttpServer is a REGISTERED built-in marker effect (not merely
        a tolerated unknown row entry) — `vera effects` must list it."""
        from vera.environment import TypeEnv

        env = TypeEnv()
        info = env.effects.get("HttpServer")
        assert info is not None, "HttpServer missing from the effect registry"
        assert info.operations == {}, "HttpServer must be a marker effect"
