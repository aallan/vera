"""#1284: whose declaration a bare ``get``/``put`` call site denotes.

The checker answers user-fn-first: :meth:`_check_call_with_args` looks the
name up as a function *before* it looks it up as an effect operation, so a
program declaring ``fn get`` has every bare ``get(...)`` in it denote that
declaration — provably, since an arity or argument-type error at such a call
site reports against the USER's signature (E201/E202), never the op's.

Codegen used to answer that question twice more, and differently.  The
declared-effect-row registration in ``vera/codegen/functions.py`` guarded its
intrinsic mapping on the function table; the handler-expression installation
in ``vera/wasm/calls_handlers.py`` overwrote ``get``/``put`` unconditionally.
From check-green source that produced, depending on the nesting shape, a
silently wrong value, a module WASM validation rejects, or a spurious
``[E602]`` skip naming a State operation the user never wrote.

Every expected value below is derived from the CHECKER's story — the user's
function was called, so its result is the answer — never from what codegen
happened to emit.  The ``pre_fix`` note on each case records what codegen
actually produced before the fix, so a case that stops distinguishing the two
answers fails loudly rather than passing vacuously.

The controls matter as much as the cases: a program that does NOT shadow the
name must still route its bare ops to the host intrinsics, which is what the
whole conformance handler corpus asserts in bulk and what
``test_unshadowed_*`` asserts here in the small.
"""

from __future__ import annotations

import pytest

from tests.checker_helpers import _check_ok, _errors
from tests.codegen_helpers import _compile, _run, wat_calls
from tests.verifier_helpers import _verify_ok


# The user's own `get`: takes a @Nat, returns its successor.  Chosen so its
# answer can never coincide with a state cell's — every case below seeds the
# cell with a value the user function cannot produce from the argument used.
_USER_GET = """
private fn get(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0 + 1
}
"""

_USER_PUT = """
private fn put(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0 * 2
}
"""


# --- the resolution rule, stated at the checker ------------------------

# A TWO-argument user `get`, for the resolution pin alone.  The built-in
# State `get(@Unit)` is arity ONE, so the two candidates disagree about the
# NUMBER as well as about the code and the noun — see the assertions below.
_USER_GET_ARITY_2 = """
private fn get(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0 + @Nat.1
}
"""


def test_checker_resolves_bare_get_to_the_user_declaration() -> None:
    """The derivation this fix threads, pinned on three discriminators.

    An over-applied ``get`` under a ``handle[State<Int>]``.  The two
    candidate resolutions report DIFFERENT diagnostics, and all three ways
    they differ are asserted, because any one alone is weak:

    * the CODE — the function path is ``E201``, the operation path
      ``E203`` (measured: ``get(1, 2, 3)`` under ``effects(<State<Int>>)``
      with no user declaration reports ``E203``);
    * the NOUN — "Function 'get'" against "Effect operation 'get'";
    * the ARITY — 2 against the built-in ``get(@Unit)``'s 1, which is why
      this fixture takes two parameters where the rest of the file's takes
      one.  With a one-argument user ``get`` both candidates report
      "expects 1 argument" and the number distinguishes nothing.
    """
    errs = _errors(_USER_GET_ARITY_2 + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    nat_to_int(get(3, 4, 5))
  }
}
""")
    assert len(errs) == 1, [d.description for d in errs]
    assert errs[0].error_code == "E201", errs[0].description
    assert "Function 'get'" in errs[0].description, errs[0].description
    assert "expects 2 argument" in errs[0].description, errs[0].description


# --- shape 1: handled body, scalar result (silently wrong value) -------

_HANDLED_BODY = _USER_GET + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    nat_to_int(get(3))
  }
}
"""


def test_handled_body_user_get_returns_the_user_answer() -> None:
    """pre_fix: 5 (the cell).  The checker's answer is get(3) = 4."""
    _check_ok(_HANDLED_BODY)
    _verify_ok(_HANDLED_BODY)
    assert _run(_HANDLED_BODY) == 4


def test_handled_body_user_get_emits_the_user_call() -> None:
    """The dispatch target, not just the value: `call $:get`, no intrinsic."""
    result = _compile(_HANDLED_BODY)
    assert result.wat is not None
    assert wat_calls(result.wat, "get")
    assert not wat_calls(result.wat, "vera.state_get_Int")


# --- shape 2: handled body, Bool result (module fails validation) ------

_HANDLED_BODY_BOOL = """
private fn get(@Nat -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0 > 0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    if get(3) then {
      1
    } else {
      0
    }
  }
}
"""


def test_handled_body_user_get_bool_result_loads() -> None:
    """pre_fix: `state_get_Int`'s i64 into the `if`'s i32 — the module was
    rejected at load with wasmtime's raw `type mismatch: expected i32,
    found i64`.  get(3) is 3 > 0, so the checker's answer is 1."""
    _check_ok(_HANDLED_BODY_BOOL)
    assert _run(_HANDLED_BODY_BOOL) == 1


# --- shape 3: same-family nesting (spurious [E602] skip) ---------------

# The user's `get` sits in the INNER handler's put clause, whose
# declaration-time op registry is the OUTER handled body's — where the
# unconditional overwrite had installed the intrinsic.  Because both
# handlers are State<Int>, the #1233 unaddressable-cell gate then refused
# `main` outright, naming a State operation the user never wrote.
_NEST_SAME_FAMILY = _USER_GET + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    handle[State<Int>](@Int = 2) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) } with @Int = nat_to_int(get(3))
    } in {
      put(9);
      State.get(())
    }
  }
}
"""


def test_same_family_nesting_compiles_and_calls_the_user_fn() -> None:
    """pre_fix: [E602], `main` dropped from the output entirely.

    The inner put clause overrides the stored value with the USER `get`'s
    answer — get(3) = 4 — so the cell holds 4, not the 9 that was put.
    """
    _check_ok(_NEST_SAME_FAMILY)
    result = _compile(_NEST_SAME_FAMILY)
    assert "main" in result.exports
    assert not [d for d in result.diagnostics if d.error_code == "E602"], (
        [d.description for d in result.diagnostics]
    )
    assert wat_calls(result.wat, "get")
    assert _run(_NEST_SAME_FAMILY) == 4


# --- shape 4: different-family nesting (module fails validation) -------

_NEST_DIFF_FAMILY = _USER_GET + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Bool>](@Bool = false) {
    get(@Unit) -> { resume(@Bool.0) },
    put(@Bool) -> { resume(()) }
  } in {
    handle[State<Int>](@Int = 2) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) } with @Int = nat_to_int(get(3))
    } in {
      put(9);
      State.get(())
    }
  }
}
"""


def test_different_family_nesting_loads_and_calls_the_user_fn() -> None:
    """pre_fix: `call $vera.state_get_Bool` emitted for the user's `get`,
    and the module was rejected at load (`expected i64, found i32`)."""
    _check_ok(_NEST_DIFF_FAMILY)
    result = _compile(_NEST_DIFF_FAMILY)
    assert result.wat is not None
    assert wat_calls(result.wat, "get")
    assert _run(_NEST_DIFF_FAMILY) == 4


# --- the same rule for `put` ------------------------------------------

_USER_PUT_BODY = _USER_PUT + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    nat_to_int(put(3))
  }
}
"""


def test_user_put_is_not_hijacked_by_the_handler() -> None:
    """`put` is the void op; the user's returns a @Nat.  pre_fix the call
    lowered to `state_put_Int` and the value-position use had nothing on
    the stack.  The checker's answer is put(3) = 6."""
    _check_ok(_USER_PUT_BODY)
    result = _compile(_USER_PUT_BODY)
    assert result.wat is not None
    assert wat_calls(result.wat, "put")
    assert _run(_USER_PUT_BODY) == 6


# --- new(State<T>) still resolves when the op NAME is shadowed ---------

_SHADOWED_NEW = _USER_GET + """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(new(State<Int>) == 42)
  effects(<State<Int>>)
{
  nat_to_int(get(3))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    probe(())
  }
}
"""


def test_new_state_resolves_with_a_shadowed_op_name() -> None:
    """`new(State<Int>)` is a CONTRACT form keyed on the cell family, not a
    call named `get`, so a user `fn get` must not take its getter away.

    Withholding `get` from the op registry without a family-keyed getter
    would raise `new(State<T>) has no 'get' effect op registered`; this
    pins that the two changes compose.  probe's own body calls the USER's
    `get` (3 + 1 = 4) while its postcondition reads the cell (42).
    """
    _check_ok(_SHADOWED_NEW)
    assert _run(_SHADOWED_NEW) == 4


# --- controls: an UNSHADOWED name still reaches the intrinsics --------

_UNSHADOWED = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(7);
    get(())
  }
}
"""


def test_unshadowed_bare_ops_still_route_to_the_intrinsics() -> None:
    """The control the fix must not move: with no user declaration owning
    the name, `get`/`put` are the handler's ops exactly as before."""
    result = _compile(_UNSHADOWED)
    assert result.wat is not None
    assert wat_calls(result.wat, "vera.state_get_Int")
    assert wat_calls(result.wat, "vera.state_put_Int")
    assert _run(_UNSHADOWED) == 7


_UNSHADOWED_ROW = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  get(()) * 10
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 6) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    probe(())
  }
}
"""


def test_unshadowed_declared_row_op_still_routes_to_the_intrinsic() -> None:
    """The other injection site's control — the declared-effect-row path."""
    assert _run(_UNSHADOWED_ROW) == 60


# --- the two codegen sites answer with the checker, on one derivation --

@pytest.mark.parametrize(
    "source,shadowed,expected,pre_fix",
    [
        (_HANDLED_BODY, "get", 4, "5 (the cell, silently)"),
        (_HANDLED_BODY_BOOL, "get", 1, "module rejected at load"),
        (_NEST_SAME_FAMILY, "get", 4, "[E602], main dropped"),
        (_NEST_DIFF_FAMILY, "get", 4, "module rejected at load"),
        (_USER_PUT_BODY, "put", 6, "nothing on the stack"),
    ],
)
def test_checker_and_codegen_agree_on_every_shadowed_shape(
    source: str, shadowed: str, expected: int, pre_fix: str,
) -> None:
    """The cross-component differential: run both sides and compare.

    ``expected`` is read off the CHECKER's resolution — it resolved the
    call to the user's declaration, so the value is that function's — and
    the assertion is that the compiled program produces it.  A unit test on
    either side alone cannot see this: codegen was internally consistent
    with itself the whole time, and the checker never learned what codegen
    emitted.  ``pre_fix`` records what each shape did instead, so a case
    that stops distinguishing the two answers is visible in the table.
    """
    _check_ok(source)
    result = _compile(source)
    assert "main" in result.exports, pre_fix
    assert wat_calls(result.wat, shadowed), pre_fix
    assert _run(source) == expected, pre_fix
