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


@pytest.mark.parametrize("source", list(_NEIGHBOURS.values()),
                         ids=list(_NEIGHBOURS))
def test_an_accepted_neighbour_still_checks_and_runs(source: str) -> None:
    checked = pipeline.check(source)
    assert checked.ok, [e.format() for e in checked.errors]
    assert pipeline.run(source).ok


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
         "applied_argument": "E202", "destructuring_let": "E170"}


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
