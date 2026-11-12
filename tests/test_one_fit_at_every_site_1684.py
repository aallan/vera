"""Every site that holds a value to a required type asks the one fit, once
per value (#1684, the open lines of 2026-11-04).

`CallsMixin._fits` binds each type variable a value's type leaves open
once, by name, and matches the enclosing function's own variables (rigid)
by name alone (#1798).  Four sites did not ask it: an effect operation's
argument, an ability operation's argument and an applied function value's
argument each skipped a parameter that is a bare type variable whatever its
kind, so a rigid `T` took an `Int` (#1691's `put(9)` under
`handle[State<T>]`), and `apply_fn` took a value of a rigid type for a
function.  A destructuring `let` asked the fit once per component, so one
open variable took a different type in each.

The repros below are the issue's lines and the members measured beside
them at bf6d5003; the matrix crosses the site with the two positions'
types and their order.
"""

from __future__ import annotations

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/checker/calls.py",
    "vera/checker/control.py",
])


def _codes(source: str) -> list[str]:
    return [e.error_code for e in pipeline.check(source).errors]


def _fn(name: str, formals: str, ret: str, body: str, *,
        forall: str = "", visibility: str = "private") -> str:
    indented = "\n".join(f"  {line}" if line else line
                         for line in body.splitlines())
    return (f"{visibility} {forall}fn {name}({formals} -> @{ret})\n"
            f"  requires(true)\n  ensures(true)\n"
            f"  effects(pure)\n{{\n{indented}\n}}\n")


# ---------------------------------------------------------------------
# The repros (red at bf6d5003: each checks clean there)
# ---------------------------------------------------------------------

_OPERATION_ARGUMENT = """\
private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<T>](@T = @T.0) {
    get(@Unit) -> { resume(@T.0) },
    put(@T) -> { resume(()) }
  } in {
    put(9);
    0
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(true)
}
"""


def test_repro_1691_an_operation_argument_meets_a_rigid_variable() -> None:
    """#1691's repro: at bf6d5003 it checks and verifies, and `g$Bool`
    does not load (`expected i32, found i64`).  `put`'s parameter is the
    generic's own `T`, which an `Int` is not."""
    assert _codes(_OPERATION_ARGUMENT) == ["E204"]


_ABILITY_ARGUMENT = """\
private forall<T where Eq<T>> fn g(@T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(@T.0, 9)
}

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  g("abc")
}
"""


def test_repro_an_ability_argument_meets_a_rigid_variable() -> None:
    """At bf6d5003 it checks, `vera verify` reports an internal error
    (E699), and `g$String` does not load (`expected i64, found i32`)."""
    assert _codes(_ABILITY_ARGUMENT) == ["E241"]


_APPLY_RIGID_VALUE = """\
private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@T.0, 1)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(5)
}
"""


def test_repro_apply_fn_of_a_rigid_variable_is_no_function() -> None:
    """The `apply_fn` line: at bf6d5003 check and verify pass and code
    generation drops `g$Int` and `main` (E600, E616, E602, E620)."""
    assert _codes(_APPLY_RIGID_VALUE) == ["E202"]


_APPLY_RIGID_PARAMETER = """\
type Fn<T> = fn(T -> Nat) effects(pure);

private forall<T> fn g(@Fn<T> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@Fn<T>.0, 9)
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(fn(@String -> @Nat) effects(pure) { string_length(@String.0) })
}
"""


def test_repro_an_applied_argument_meets_a_rigid_variable() -> None:
    """At bf6d5003 it checks and verifies and the template `g` does not
    load (`expected i32, found i64`)."""
    assert _codes(_APPLY_RIGID_PARAMETER) == ["E202"]


_DESTRUCTURE_TUPLE = """\
private forall<T> fn dup(@T -> @Tuple<T, T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@T.0, @T.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Option<Int>, @Option<String>> = dup(None);
  5
}
"""

_DESTRUCTURE_DATA = """\
public data Two<A, B> {
  Two(A, B)
}

private forall<T> fn dup(@Option<T> -> @Two<Option<T>, Option<T>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Two(@Option<T>.0, @Option<T>.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Two<@Option<Int>, @Option<String>> = dup(None);
  5
}
"""


@pytest.mark.parametrize("source", [_DESTRUCTURE_TUPLE, _DESTRUCTURE_DATA],
                         ids=["tuple", "data"])
def test_repro_a_destructured_value_s_variable_takes_one_type(
        source: str) -> None:
    """The destructuring `let` line: at bf6d5003 both check and verify and
    print 5, `dup` instantiated at `Bool`, its one `T` read as `Int` in
    one component and `String` in the other."""
    assert _codes(source) == ["E170"]


_RESUME_ARGUMENT = """\
private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<T>](@T = @T.0) {
    get(@Unit) -> { resume(9) },
    put(@T) -> { resume(()) }
  } in {
    0
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(true)
}
"""

_HELPER_ARGUMENT = """\
private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  helper(9)
}
where {
  fn helper(@T -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    1
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(true)
}
"""


@pytest.mark.parametrize("source", [_RESUME_ARGUMENT, _HELPER_ARGUMENT],
                         ids=["resume", "where_helper"])
def test_repro_a_call_s_argument_meets_the_outer_rigid_variable(
        source: str) -> None:
    """A callee with no `forall` of its own whose parameter is the
    enclosing function's `T` (`resume` under `handle[State<T>]`, a `where`
    helper over the outer `T`) skipped that parameter as unresolved.  At
    bf6d5003 both check and verify, and `g(true)` fails to compile at run
    (`E800`; PR #1855 review).  The fix names a value of type `T`."""
    error, = pipeline.check(source).errors
    assert error.error_code == "E202", error.format()
    assert error.fix.startswith("Pass `@T.0`, or another value of type T: ")
    fixed = source.replace("resume(9)", "resume(@T.0)").replace(
        "helper(9)", "helper(@T.0)")
    _clears(fixed, "E202")
    assert pipeline.run(fixed).value in (0, 1)


_APPLY_UNFIXED = """\
type Endo<T> = fn(T -> T) effects(pure);

private forall<T> fn mk(@Unit -> @Endo<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T -> @T) effects(pure) { @T.0 }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  abs(apply_fn(mk(()), 40))
}
"""


def test_repro_an_applied_argument_meets_an_unfixed_variable() -> None:
    """A member measured beside the `apply_fn` line: `mk(())` gives `T` no
    type, so the identity is compiled at `Bool` (#1798's closure), and the
    applied argument skipped its bare `T` parameter.  At bf6d5003 it checks
    and verifies, and `main` does not load (`expected i32, found i64`)."""
    error, = pipeline.check(_APPLY_UNFIXED).errors
    assert error.error_code == "E202"
    assert error.description == (
        "Argument 1 of 'apply_fn' has type Int, expected T: no argument of "
        "the call that made the function value gives T a type, so its code "
        "was compiled at a type of its own.")


def test_repro_the_ability_member_verifies_without_an_internal_error(
        ) -> None:
    """`eq(@T.0, 9)` drew an internal error from `vera verify` (E699) at
    bf6d5003; it is refused at check, so verification never meets it."""
    verified = pipeline.verify(_ABILITY_ARGUMENT)
    assert [d.error_code for d in verified.errors] == ["E241"]


# ---------------------------------------------------------------------
# Each refusal's fix, applied as it is written, clears its code
# ---------------------------------------------------------------------


def _fix(source: str, code: str) -> str:
    error, = pipeline.check(source).errors
    assert error.error_code == code, error.format()
    return error.fix


def _clears(source: str, code: str) -> None:
    checked = pipeline.check(source)
    assert code not in [e.error_code for e in checked.errors], (
        [e.format() for e in checked.errors])


def test_the_operation_argument_fix_clears_e204() -> None:
    fix = _fix(_OPERATION_ARGUMENT, "E204")
    assert fix.startswith("Pass `@T.0`, or another value of type T: ")
    _clears(_OPERATION_ARGUMENT.replace("put(9)", "put(@T.0)"), "E204")


def test_the_ability_argument_fix_clears_e241() -> None:
    fix = _fix(_ABILITY_ARGUMENT, "E241")
    assert fix.startswith("Pass `@T.0`, or another value of type T: ")
    _clears(_ABILITY_ARGUMENT.replace("eq(@T.0, 9)", "eq(@T.0, @T.0)"),
            "E241")


_APPLY_RIGID_PARAMETER_HELD = _APPLY_RIGID_PARAMETER.replace(
    "fn g(@Fn<T> -> @Nat)", "fn g(@T, @Fn<T> -> @Nat)").replace(
    "  g(fn(", "  g(\"abc\", fn(")


def test_the_applied_argument_fix_clears_e202() -> None:
    """With no value of type `T` in scope the fix says to take one as a
    parameter; with one, it names it, and passing it clears the code."""
    assert _fix(_APPLY_RIGID_PARAMETER, "E202").startswith(
        "Pass a value of type T, taking one as a parameter `@T` of the "
        "enclosing function: ")
    fix = _fix(_APPLY_RIGID_PARAMETER_HELD, "E202")
    assert fix.startswith("Pass `@T.0`, or another value of type T: ")
    _clears(_APPLY_RIGID_PARAMETER_HELD.replace(
        "apply_fn(@Fn<T>.0, 9)", "apply_fn(@Fn<T>.0, @T.0)"), "E202")


def test_the_applied_value_fix_clears_e202() -> None:
    """The fix writes the function type out from the argument applied and
    the type the result is expected at; declaring it and holding the
    function at it, as the fix says (the caller passing a function of that
    type), clears the code."""
    fix = _fix(_APPLY_RIGID_VALUE, "E202")
    assert fix == (
        "Hold the function to apply at the type `fn(Int -> Int) "
        "effects(pure)`: declare `type Applied = fn(Int -> Int) "
        "effects(pure);`, take the function as a parameter or binding of "
        "type `@Applied`, and apply it in place of `@T.0`.")
    alias = fix.split("declare `", 1)[1].split("`", 1)[0]
    source = (alias + "\n\n" + _APPLY_RIGID_VALUE
              .replace("fn g(@T -> @Int)", "fn g(@T, @Applied -> @Int)")
              .replace("apply_fn(@T.0, 1)", "apply_fn(@Applied.0, 1)")
              .replace("g(5)",
                       "g(5, fn(@Int -> @Int) effects(pure) { @Int.0 })"))
    _clears(source, "E202")
    assert pipeline.run(source).value == 1


_APPLIED_VALUES = {
    # The enclosing function's own variable.
    "own_variable": "@T.0",
    # A variable the call that made the value left open: an empty
    # literal's element type, and a `None` no argument types.
    "empty_literal_element": "head_plain([])",
    "unfixed_option_payload": "option_unwrap_or(nothing(()), head_plain([]))",
}


@pytest.mark.parametrize("value", list(_APPLIED_VALUES.values()),
                         ids=list(_APPLIED_VALUES))
@pytest.mark.parametrize("result", ["Int", "T"])
def test_a_value_typed_by_a_bare_variable_is_no_function(
        value: str, result: str) -> None:
    """`apply_fn` of a value whose type is a bare type variable, whichever
    kind, is `E202`: no function type is there to check the application
    by.  At bf6d5003 the enclosing function's own variable and one a call
    left open were both taken as an unknown with no error, and code
    generation dropped the function (`E616`, `E602`).  The fix writes the
    function type out where the arguments and the expected result can be
    written, and applying it clears the code."""
    body = f"apply_fn({value}, @T.0)"
    source = (_HEAD_PLAIN
              + _fn("g", "@T", result, body, forall="forall<T> ")
              + "\n" + _main("Int", "g(5)"))
    error, = pipeline.check(source).errors
    assert error.error_code == "E202", error.format()
    assert error.description.startswith("Argument 0 of 'apply_fn' has ")
    alias_text = f"Applied<T> = fn(T -> {result})" if result == "T" else (
        "Applied<T> = fn(T -> Int)")
    assert f"declare `type {alias_text} effects(pure);`" in error.fix, (
        error.fix)
    head = alias_text.split(" = ", 1)[0]
    declared = error.fix.split("declare `", 1)[1].split("`", 1)[0]
    fixed = (declared + "\n\n" + source
             .replace(f"fn g(@T -> @{result})",
                      f"fn g(@T, @{head} -> @{result})")
             .replace(body, f"apply_fn(@{head}.0, @T.0)")
             .replace("g(5)",
                      "g(5, fn(@Int -> @Int) effects(pure) { @Int.0 })"))
    _clears(fixed, "E202")


_APPLY_RIGID_VALUE_OVER_T = """\
private forall<T> fn g(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@T.0, @T.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(5)
}
"""


def test_the_applied_value_fix_names_the_variables_its_alias_binds(
        ) -> None:
    """Where the function type the fix writes names the enclosing
    function's own `T`, its alias takes `T` as a parameter, so the
    declaration it says to write binds what it names (PR #1855 review)."""
    fix = _fix(_APPLY_RIGID_VALUE_OVER_T, "E202")
    assert fix == (
        "Hold the function to apply at the type `fn(T -> T) "
        "effects(pure)`: declare `type Applied<T> = fn(T -> T) "
        "effects(pure);`, take the function as a parameter or binding of "
        "type `@Applied<T>`, and apply it in place of `@T.0`.")
    alias = fix.split("declare `", 1)[1].split("`", 1)[0]
    source = (alias + "\n\n" + _APPLY_RIGID_VALUE_OVER_T
              .replace("fn g(@T -> @T)", "fn g(@T, @Applied<T> -> @T)")
              .replace("apply_fn(@T.0, @T.0)", "apply_fn(@Applied<T>.0, @T.0)")
              .replace("g(5)",
                       "g(5, fn(@Int -> @Int) effects(pure) { @Int.0 })"))
    _clears(source, "E202")
    assert pipeline.run(source).value == 5


def test_the_destructuring_fix_clears_e170() -> None:
    fix = _fix(_DESTRUCTURE_TUPLE, "E170")
    assert fix == "Write binding 2 as `@Option<Int>`, the type binding 1 gives T."
    source = _DESTRUCTURE_TUPLE.replace(
        "@Option<Int>, @Option<String>>", "@Option<Int>, @Option<Int>>")
    _clears(source, "E170")
    assert pipeline.run(source).value == 5


# ---------------------------------------------------------------------
# The accepted neighbours: what the fit admits stays admitted
# ---------------------------------------------------------------------

_NEIGHBOURS = {
    # An operation on a cell the generic's own `T` types, given a `T`.
    "operation_given_t": _OPERATION_ARGUMENT.replace("put(9)", "put(@T.0)"),
    # An operation on a concrete cell inside a generic.
    "operation_concrete_cell": _OPERATION_ARGUMENT.replace(
        "handle[State<T>](@T = @T.0)", "handle[State<Int>](@Int = 0)").replace(
        "get(@Unit) -> { resume(@T.0) },\n    put(@T)",
        "get(@Unit) -> { resume(@Int.0) },\n    put(@Int)"),
    # An ability operation whose second argument leaves a variable open
    # that the first fixes (#993).
    "ability_open_argument": """\
public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(Some(5), None)
}
""",
    # A function value whose variable its call fixes.
    "applied_fixed": _APPLY_UNFIXED.replace(
        "fn mk(@Unit -> @Endo<T>)", "fn mk(@T -> @Endo<T>)").replace(
        "mk(())", "mk(1)"),
    # A destructure whose components give the variable one type.
    "destructure_one_type": _DESTRUCTURE_TUPLE.replace(
        "@Option<Int>, @Option<String>>", "@Option<Int>, @Option<Int>>"),
}


_UNMAPPED = """\
private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  put(9);
  0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(true)
}
"""


def test_an_operation_no_instance_types_is_refused_by_the_row_alone(
        ) -> None:
    """`put` with no handler and no row entry: `State`'s own `T` has no
    type, and is not the generic's `T` of the same name, so the argument
    is not judged and the call is refused once, by the row (`E122`), as at
    bf6d5003."""
    assert _codes(_UNMAPPED) == ["E122"]


_HEAD_PLAIN = """\
private forall<T> fn head_plain(@Array<T> -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<T>.0[0]
}

private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  None
}

"""

_OPERATION_HOLE = _HEAD_PLAIN + """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(head_plain([]));
    get(())
  }
}
"""

_ABILITY_HOLE = _HEAD_PLAIN + """\
public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(nothing(()), Some(5))
}
"""


def _holds_and_stops(source: str) -> set[tuple[str, ...]]:
    """`head_plain`'s instances in *source*, which checks clean and stops
    at the empty array's index, the trap it owes (no load failure)."""
    checked = pipeline.check(source)
    assert checked.ok, [e.format() for e in checked.errors]
    ran = pipeline.run(source)
    assert ran.trap is not None and "Array index out of bounds" in str(
        ran.trap), ran.trap
    return {inst.args for inst in checked.typed.instances
            if inst.key == "head_plain"}


def test_a_variable_a_call_left_open_takes_the_operation_s_parameter(
) -> None:
    """A value whose type holds a variable its call left open (an empty
    literal's element type) at an operation's argument.  At bf6d5003 the
    fit bound the variable and dropped the binding, so `put(head_plain([]))`
    checked and its module did not load, and PR #1855 refused it (`E204`).
    The parameter is the type the argument is expected at, which now fixes
    the variable (spec §5.9, #1684 rule C): `head_plain` is at `Int`."""
    assert _holds_and_stops(_OPERATION_HOLE) == {("Int",)}


def test_a_variable_a_call_left_open_stays_refused_at_an_ability() -> None:
    """An ability operation's arguments are given no expected type, so the
    `None` no argument types stays open there and is refused (`E241`), as
    at bf6d5003."""
    assert _codes(_ABILITY_HOLE) == ["E241"]


def test_a_hole_at_a_rigid_parameter_takes_the_outer_variable() -> None:
    """A value whose call left its variable open, at an operation's
    parameter that is the enclosing function's own `T`: at bf6d5003 the
    parameter was skipped and the program accepted, running only where the
    hole's default `Bool` happened to be the instance; PR #1855 refused it
    (`E204`).  `T` is a type, the one the argument is expected at, so it
    fixes the variable (#1684 rule C), and `head_plain` is built at each
    instance of the enclosing function (here `g` at `Bool`)."""
    source = _HEAD_PLAIN + _OPERATION_ARGUMENT.replace(
        "put(9)", "put(head_plain([]))")
    assert _holds_and_stops(source) == {("Bool",)}


def test_a_hole_at_a_call_s_rigid_parameter_takes_the_outer_variable(
) -> None:
    """The same at a call's parameter that is the outer `T` (a `where`
    helper over it): at bf6d5003 the program checked and verified and
    `g$String` did not load, and PR #1855 refused it (`E202`).  The helper's
    parameter is now the argument's expected type as an operation's is
    (#1684 rule C)."""
    source = _HEAD_PLAIN + _HELPER_ARGUMENT.replace(
        "helper(9)", "helper(head_plain([]))")
    assert _holds_and_stops(source) == {("Bool",)}


_ABILITY_TWO_HOLES = _HEAD_PLAIN + """\
public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(head_plain([]), head_plain([]))
}
"""


def test_an_ability_parameter_a_call_left_open_is_not_judged() -> None:
    """`eq`'s `A` taken from the first argument's open variable: the second
    argument's own open variable is not held to it by name, as at
    bf6d5003, where the program checks, verifies and stops at the empty
    array's index; the context that fixes the two is #1684's next change.
    """
    assert _codes(_ABILITY_TWO_HOLES) == []
    ran = pipeline.run(_ABILITY_TWO_HOLES)
    assert ran.trap is not None and "Array index out of bounds" in str(
        ran.trap)


@pytest.mark.parametrize("source", list(_NEIGHBOURS.values()),
                         ids=list(_NEIGHBOURS))
def test_an_accepted_neighbour_still_checks_and_runs(source: str) -> None:
    checked = pipeline.check(source)
    assert checked.ok, [e.format() for e in checked.errors]
    assert pipeline.run(source).ok


# ---------------------------------------------------------------------
# Each refusal's whole diagnostic
# ---------------------------------------------------------------------

_RIGID_WHY = ("T is a type parameter of the enclosing function, which "
              "stands for whatever type each call gives it, so a value of "
              "type `Int` has type T only where a call makes T that type, and "
              "the body must hold at every type.")

_ABILITY_CONCRETE = """\
public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(1, "a")
}
"""

#: Each refusal: its program, then its code, description, rationale, fix
#: and spec reference, as a reader sees them.
_DIAGNOSTICS: dict[str, tuple[str, str, str, str, str, str]] = {
    "operation_argument": (
        _OPERATION_ARGUMENT, "E204",
        "Argument 0 of 'put' has type Int, expected T.",
        "Each argument to an effect operation must be a subtype of the "
        "parameter type declared in its 'op' signature.",
        f"Pass `@T.0`, or another value of type T: {_RIGID_WHY}",
        'Chapter 7, Section 7.4 "Performing Effects"'),
    "ability_argument_rigid": (
        _ABILITY_ARGUMENT, "E241",
        "Argument 1 of 'eq' has type Int, expected T.",
        "Each argument to an ability operation must be a subtype of the "
        "parameter type declared in its 'op' signature, after the "
        "ability's type variable is instantiated.",
        f"Pass `@T.0`, or another value of type T: {_RIGID_WHY}",
        'Chapter 9, Section 9.8 "Abilities"'),
    "ability_argument_concrete": (
        _ABILITY_CONCRETE, "E241",
        "Argument 1 of 'eq' has type String, expected Int.",
        "Each argument to an ability operation must be a subtype of the "
        "parameter type declared in its 'op' signature, after the "
        "ability's type variable is instantiated.",
        "Pass a value of type `Int` for argument 1 of 'eq'. Or make the "
        "ability's type variable resolve to a type that accepts `String`.",
        'Chapter 9, Section 9.8 "Abilities"'),
    "applied_argument": (
        _APPLY_RIGID_PARAMETER, "E202",
        "Argument 1 of 'apply_fn' has type Int, expected T.",
        "Each argument after the function value must be a subtype of the "
        "corresponding parameter of the applied function type.",
        "Pass a value of type T, taking one as a parameter `@T` of the "
        f"enclosing function: {_RIGID_WHY}",
        'Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"'),
    "applied_value": (
        _APPLY_RIGID_VALUE, "E202",
        "Argument 0 of 'apply_fn' has T, a type parameter of the enclosing "
        "function, expected a function value (a fn(...) type).",
        "apply_fn invokes a stored function value via call_indirect.  T "
        "stands for whatever type each call of the enclosing function "
        "gives it, and the body must hold at every type, most of which are "
        "no function, so a value of type T has no signature to call.",
        "Hold the function to apply at the type `fn(Int -> Int) "
        "effects(pure)`: declare `type Applied = fn(Int -> Int) "
        "effects(pure);`, take the function as a parameter or binding of "
        "type `@Applied`, and apply it in place of `@T.0`.",
        'Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"'),
    "applied_value_open": (
        _HEAD_PLAIN + _APPLY_RIGID_VALUE.replace(
            "apply_fn(@T.0, 1)", "apply_fn(head_plain([]), 1)"), "E202",
        "Argument 0 of 'apply_fn' has a type variable no argument of the "
        "call that made it fixes, expected a function value (a fn(...) "
        "type).",
        "apply_fn invokes a stored function value via call_indirect.  The "
        "call that made the value left its type open, so nothing gives it "
        "a function type, and the value has no signature to call.",
        "Hold the function to apply at the type `fn(Int -> Int) "
        "effects(pure)`: declare `type Applied = fn(Int -> Int) "
        "effects(pure);`, take the function as a parameter or binding of "
        "type `@Applied`, and apply it in place of `head_plain([])`.",
        'Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"'),
    "unfixed_application": (
        _APPLY_UNFIXED, "E202",
        "Argument 1 of 'apply_fn' has type Int, expected T: no argument of "
        "the call that made the function value gives T a type, so its code "
        "was compiled at a type of its own.",
        "A function a generic call returns is compiled at the types its "
        "call's arguments give its type variables; one they give no type "
        "is compiled at a type of its own, so the function takes no "
        "argument of another type there.",
        "Make the function value at the type it is applied at: give the "
        "call `mk(())` an argument that fixes T, or apply a function "
        "written to take `Int` there instead.",
        'Chapter 5, Section 5.9 "Generic Functions"'),
    "call_argument": (
        _HELPER_ARGUMENT, "E202",
        "Argument 0 of 'helper' has type Int, expected T.",
        "Each argument's type must be a subtype of the corresponding "
        "declared parameter type.",
        f"Pass `@T.0`, or another value of type T: {_RIGID_WHY}",
        'Chapter 5, Section 5.2 "Function Declaration Syntax"'),
    "destructuring_let": (
        _DESTRUCTURE_TUPLE, "E170",
        "Let binding expects Option<String>, component 2 of the "
        "destructured value has type Option<?>: the type variable T stands "
        "at the type argument of Option in component 1 and at the type "
        "argument of Option in component 2, where the bindings give it Int "
        "and String, and a type variable takes one type.",
        "A destructuring let binds every component of one value, and a "
        "type variable the value's type leaves open stands for one type, "
        "so the bindings must give it the same type at every position it "
        "holds.",
        "Write binding 2 as `@Option<Int>`, the type binding 1 gives T.",
        'Chapter 4, Section 4.7.1 "Tuple Destructuring"'),
}


@pytest.mark.parametrize("name", list(_DIAGNOSTICS))
def test_each_refusal_reads_as_written(name: str) -> None:
    """The whole diagnostic of each refusal this change adds or reaches:
    what a reader is told, why, what to write, and where the spec says it
    (PR #1855's mutation lane: the text was unpinned)."""
    source, code, description, rationale, fix, spec_ref = _DIAGNOSTICS[name]
    error, = pipeline.check(source).errors
    assert (error.error_code, error.description, error.rationale,
            error.fix, error.spec_ref) == (
        code, description, rationale, fix, spec_ref)


def _applied_value_fix(source: str) -> str:
    error, = pipeline.check(source).errors
    assert error.error_code == "E202", error.format()
    return error.fix


def test_the_applied_value_fix_writes_the_enclosing_row() -> None:
    """The function type the fix writes carries the enclosing function's
    row, which the applied value must keep within."""
    source = _APPLY_RIGID_VALUE.replace(
        "fn g(@T -> @Int)\n  requires(true)\n  ensures(true)\n  effects(pure)",
        "fn g(@T -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(<IO>)").replace(
        "public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)",
        "public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(<IO>)")
    assert "declare `type Applied = fn(Int -> Int) effects(<IO>);`" in (
        _applied_value_fix(source))


@pytest.mark.parametrize("body", [
    # No type the result is expected at: an operand.
    "apply_fn(@T.0, 1) + 1",
    # An argument with no type to write.
    "apply_fn(@T.0, [][0])",
], ids=["no_expected_result", "argument_with_no_type"])
def test_the_applied_value_fix_falls_back_to_prose(body: str) -> None:
    """Where the function type cannot be written out, the fix says what to
    do without one."""
    source = _APPLY_RIGID_VALUE.replace("apply_fn(@T.0, 1)", body)
    assert _applied_value_fix(source) == (
        "Hold the function to apply at a function type, declared through a "
        "type alias, and apply a value of that type in place of `@T.0`.")


@pytest.mark.parametrize(("declared", "alias"), [
    ("type Applied = Int;\n\n", "Applied2"),
    ("type Applied = Int;\n\ntype Applied2 = Bool;\n\n", "Applied3"),
], ids=["one_taken", "two_taken"])
def test_the_applied_value_fix_names_an_alias_the_program_lacks(
        declared: str, alias: str) -> None:
    """The alias the fix declares is one the program does not have."""
    fix = _applied_value_fix(declared + _APPLY_RIGID_VALUE)
    assert f"declare `type {alias} = fn(Int -> Int) effects(pure);`" in fix
    assert f"of type `@{alias}`" in fix


_APPLY_TWO_VARIABLES = """\
private forall<T, U> fn g(@T, @U -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@T.0, @U.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(5, true)
}
"""


def test_the_applied_value_fix_s_alias_binds_each_variable() -> None:
    """An alias over two of the enclosing function's variables lists both,
    in order, as its parameters."""
    assert ("declare `type Applied<T, U> = fn(U -> T) effects(pure);`, take "
            "the function as a parameter or binding of type "
            "`@Applied<T, U>`") in _applied_value_fix(_APPLY_TWO_VARIABLES)


_UNFIXED_TWO = """\
type Pairs<A, B> = fn(Tuple<A, B> -> Int) effects(pure);

private forall<A, B> fn mk2(@Unit -> @Pairs<A, B>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Tuple<A, B> -> @Int) effects(pure) { 1 }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(mk2(()), Tuple(1, "a"))
}
"""


def test_an_unfixed_application_names_each_variable() -> None:
    """Where the call that made the function value left two variables
    without a type, the refusal names both."""
    error, = pipeline.check(_UNFIXED_TWO).errors
    assert error.error_code == "E202", error.format()
    assert "gives A and B a type" in error.description, error.description
    assert "an argument that fixes A and B" in error.fix, error.fix


@pytest.mark.parametrize(("source", "named"), [
    (_APPLY_RIGID_VALUE, "in place of `the value`."),
    (_APPLY_UNFIXED, "give the call `the function value` an argument"),
], ids=["rigid_value", "unfixed_application"])
def test_an_apply_fn_fix_without_the_program_s_text_names_the_value(
        source: str, named: str) -> None:
    """`typecheck` takes the program's text as an optional argument
    (default empty); without it no argument's text can be quoted, and each
    `apply_fn` fix names the value in words (PR #1855's mutation lane)."""
    from vera.checker import typecheck

    errors = [d for d in typecheck(pipeline.parse(source).program)
              if d.severity == "error"]
    assert [d.error_code for d in errors] == ["E202"], errors
    assert named in errors[0].fix, errors[0].fix


def test_every_built_in_ability_operation_takes_one_variable() -> None:
    """The ability-argument judgement reads its operation's one type
    variable from any typed argument (`_ability_type_mapping`), so a later
    argument cannot disagree with a mapping an earlier one failed to set.
    That rests on this: every built-in ability has one type parameter, and
    every parameter of every operation is that variable.  An ability
    registered otherwise fails here first.  A user ability need not have
    that shape, and its arguments are judged too
    (`test_a_skipped_ability_argument_leaves_the_later_ones_judged`)."""
    from vera.environment import TypeEnv

    env = TypeEnv()
    assert env.abilities
    for ability in env.abilities.values():
        assert ability.type_params is not None
        assert len(ability.type_params) == 1, ability.name
        (var,) = ability.type_params
        for op in ability.operations.values():
            assert all(getattr(p, "name", None) == var
                       for p in op.param_types), (ability.name, op.name)


_TRI = """\
ability Tri<T> {
  op tri(SIGNATURE -> Int);
}

public fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  CALL
}
"""


@pytest.mark.parametrize(("signature", "call", "column"), [
    # The first argument has no type: skipped, and the third still judged.
    ("T, T, T", 'tri([][0], 1, "x")', 17),
    # The first argument is re-synthesized at the parameter and fits.
    ("T, T, T", 'tri(None, Some(1), Some("x"))', 22),
    # The first parameter is a variable a call left open (`head_plain([])`
    # gives `T` no type): skipped, and the second still judged.
    ("T, Int, T", 'tri(head_plain([]), "x", head_plain([]))', 23),
], ids=["untyped_argument", "resynthesized_argument", "open_parameter"])
def test_a_skipped_ability_argument_leaves_the_later_ones_judged(
        signature: str, call: str, column: int) -> None:
    """A user ability's operation is refused (E340) and its arguments are
    still checked.  It may take three arguments and a parameter that is not
    its variable, so an argument the judgement skips or passes leaves the
    next ones to it: the refused argument here is refused whatever the
    first one was (PR #1855's mutation lane)."""
    source = _HEAD_PLAIN + _TRI.replace("SIGNATURE", signature).replace(
        "CALL", call)
    line = _HEAD_PLAIN.count("\n") + 10
    e241 = [e for e in pipeline.check(source).errors
            if e.error_code == "E241"]
    assert [(e.location.line, e.location.column) for e in e241] == [
        (line, column)], [e.format() for e in e241]


# ---------------------------------------------------------------------
# The matrix: site × the two positions' types × their order
# ---------------------------------------------------------------------

#: The two positions' types, as (first, second).  `T` is the enclosing
#: generic's own type parameter.
PAIRS = {
    "equal": ("Int", "Int"),
    "one_refined": ("PosInt", "Int"),
    "nat_int": ("Nat", "Int"),
    "two_refinements": ("PosInt", "NegInt"),
    "unrelated": ("Int", "Bool"),
    "one_open": ("T", "Int"),
}

#: The pairs no instantiation of the site makes agree.
_REFUSED = {"unrelated", "one_open"}

#: A value of each type, as `main` passes it, and the cell a `State` of
#: the type starts at.
_VALUE = {"Int": "0 - 5", "Nat": "3", "PosInt": "2", "NegInt": "0 - 2",
          "Bool": "false", "T": "@T.0"}

_PRELUDE = ("type PosInt = { @Int | @Int.0 > 0 };\n\n"
            "type NegInt = { @Int | @Int.0 < 0 };\n\n")

#: The code each site refuses a pair with.
_CODE = {"operation_argument": "E204", "ability_argument": "E241",
         "applied_argument": "E202", "destructuring_let": "E170",
         "call_argument": "E202"}


def _formals(*types: str) -> str:
    """`g`'s parameters: `@T` first, then each other type once."""
    seen = ["T"] + [t for t in dict.fromkeys(types) if t != "T"]
    return ", ".join(f"@{t}" for t in seen)


def _main(ret: str, call: str) -> str:
    return _fn("main", "@Unit", ret, call, visibility="public")


def _call(*types: str) -> str:
    """`g` called at `T` = `Bool`, with a value of each other type."""
    rest = [_VALUE[t] for t in dict.fromkeys(types) if t != "T"]
    return f"g({', '.join(['true', *rest])})"


def _site_program(site: str, required: str, given: str) -> str:
    """A generic `g` whose body holds a value of type *given* where its
    site requires *required*, and a `main` that calls it."""
    if site == "operation_argument":
        body = (f"handle[State<{required}>](@{required} = "
                f"{_VALUE[required] if required != 'T' else '@T.0'}) {{\n"
                f"  get(@Unit) -> {{ resume(@{required}.0) }},\n"
                f"  put(@{required}) -> {{ resume(()) }}\n"
                f"}} in {{\n  put(@{given}.0);\n  0\n}}")
        return (_PRELUDE
                + _fn("g", _formals(required, given), "Int", body,
                      forall="forall<T> ")
                + "\n" + _main("Int", _call(required, given)))
    if site == "ability_argument":
        body = f"eq(@{required}.0, @{given}.0)"
        return (_PRELUDE
                + _fn("g", _formals(required, given), "Bool", body,
                      forall="forall<T where Eq<T>> ")
                + "\n" + _main("Bool", _call(required, given)))
    if site == "applied_argument":
        alias = (f"type F<T> = fn({required} -> Int) effects(pure);\n\n"
                 if required == "T" else
                 f"type F = fn({required} -> Int) effects(pure);\n\n")
        slot = "F<T>" if required == "T" else "F"
        closure_at = "Bool" if required == "T" else required
        body = f"apply_fn(@{slot}.0, @{given}.0)"
        formals = _formals(given).replace("@T", f"@T, @{slot}", 1)
        rest = [_VALUE[t] for t in dict.fromkeys([given]) if t != "T"]
        closure = f"fn(@{closure_at} -> @Int) effects(pure) {{ 1 }}"
        return (_PRELUDE + alias
                + _fn("g", formals, "Int", body, forall="forall<T> ")
                + "\n" + _main("Int",
                               f"g({', '.join(['true', closure, *rest])})"))
    if site == "call_argument":
        # A `where` helper with no `forall` of its own, whose parameter
        # may be the enclosing function's `T`.
        helper = _fn("helper", f"@{required}", "Int", "1",
                     visibility="").lstrip()
        helper = "\n".join(f"  {line}" if line else line
                           for line in helper.splitlines())
        source = _fn("g", _formals(given), "Int", f"helper(@{given}.0)",
                     forall="forall<T> ")
        return (_PRELUDE + source.rstrip("\n")
                + f"\nwhere {{\n{helper}\n}}\n"
                + "\n" + _main("Int", _call(given)))
    assert site == "destructuring_let"
    dup = _fn("dup", "@Option<A>", "Tuple<Option<A>, Option<A>>",
              "Tuple(@Option<A>.0, @Option<A>.0)", forall="forall<A> ")
    body = (f"let Tuple<@Option<{required}>, @Option<{given}>> = "
            f"dup(None);\n7")
    return (_PRELUDE + dup + "\n"
            + _fn("g", "@T", "Int", body, forall="forall<T> ")
            + "\n" + _main("Int", "g(true)"))


@pytest.mark.parametrize("order", ["ab", "ba"])
@pytest.mark.parametrize("pair", list(PAIRS))
@pytest.mark.parametrize("site", list(_CODE))
def test_a_site_holds_a_value_by_the_one_fit(
        site: str, pair: str, order: str) -> None:
    """One verdict for both orders of the two positions: a pair no
    instantiation makes agree is refused, with the site's code, and the
    enclosing function's own `T` is a type no `Int` fits; any other pair
    is accepted, and its module loads and runs without putting a value
    where its type does not hold (a refinement the run cannot keep is a
    guard's trap, never a load failure or a wrong-width value)."""
    first, second = PAIRS[pair]
    required, given = (first, second) if order == "ab" else (second, first)
    source = _site_program(site, required, given)
    codes = _codes(source)
    if pair in _REFUSED:
        assert codes == [_CODE[site]], (codes, source)
        return
    assert codes == [], (codes, source)
    ran = pipeline.run(source)
    if ran.trap is not None:
        assert "Refinement violation" in str(ran.trap) or (
            "Negative value" in str(ran.trap)), (str(ran.trap), source)
    else:
        assert ran.ok, source
