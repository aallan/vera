"""A call argument whose type leaves a type variable open takes one type for
it, and a function compiled before its variable had a type fits no other
(#1684).

`CallsMixin._fits` held a call argument to its parameter with each type
variable the argument's type left open a wildcard, one position at a time
(`_compatible_modulo_typevars`, #993).  A variable standing at two positions
took a different type at each, and a closure whose `T` no argument fixes,
which code generation compiles at a type of its own, fitted any function
type: the identity `fn(T -> T)` from `mk(())` fitted
`fn(Option<Nat> -> Option<String>)` and ran with a `Nat` read as a
`String`, and against `fn(Int -> Int)` it trapped.  A generic call's result
also took the data type its context expected on the type's name and arity
alone (`_synth_fn_call`), so an argument reached the fit already given a
type no instantiation gives it: a data value holding such a closure fitted
any instantiation of its type, an `if` gave `twice(None)` the other
branch's `Tuple<Option<Int>, Option<String>>` (#1690), and in a `forall<A>`
body `Two<A, A>` was taken as `Two<Int, Int>`.

Both now ask the join an array literal's elements and an `if`'s and a
`match`'s arms are given (`_join_parts`, #1668).  Each open variable is
bound once by name; a variable in a position code generation compiles
behaviour for (a function type, or a data field held over one) is not open
unless an argument fixed it; the enclosing function's own are rigid.  A
refusal names the variable, its positions and the types the parameter gives
it, or, for a function compiled at its own type, what to write instead.
Where the join fails only at a built-in's variable a failed substitution
lost (#1688), both keep the verdict they gave before.

The matrix crosses the shape of the argument's type over `T` (a closure, a
closure from an `Option` to an `Array`, a data value holding a closure, a
data value with two `Option<T>` fields, a tuple of two, a nested tuple) with
the parameter's type (one type at both positions, two types, a type and the
callee's own variable) and what fixes `T` (nothing, the argument, a literal
the expected type fills).  Each cell asserts the verdict the one-variable
rule gives, a refusal's claims, the value `f(7)` returns for an acceptance,
and that an acceptance at a behaviour position records the instance the fit
bound.
"""

from __future__ import annotations

import re

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/checker/calls.py",
    "vera/checker/expressions.py",
])


def _fn(name: str, formals: str, ret: str, body: str, *,
        forall: str = "", effect: str = "pure",
        visibility: str = "private") -> str:
    indented = "\n".join(f"  {line}" if line else line
                         for line in body.splitlines())
    return (f"{visibility} {forall}fn {name}({formals} -> @{ret})\n"
            "  requires(true)\n  ensures(true)\n"
            f"  effects({effect})\n{{\n{indented}\n}}\n")


#: Each shape: the declarations it needs, `make`'s result type over `T`,
#: `make`'s body, and the parameter's type at (A, B).  A slot cannot be
#: written at a function type, so a function type is named by an alias.
_SHAPES: dict[str, tuple[str, str, str, str]] = {
    "closure": (
        "type Endo<T> = fn(T -> T) effects(pure);\n"
        "type P<A, B> = fn(A -> B) effects(pure);\n\n",
        "Endo<T>", "fn(@T -> @T) effects(pure) { @T.0 }", "P<{a}, {b}>"),
    "fn_param_result": (
        "type Lift<T> = fn(Option<T> -> Array<T>) effects(pure);\n"
        "type Q<A, B> = fn(Option<A> -> Array<B>) effects(pure);\n\n",
        "Lift<T>", "fn(@Option<T> -> @Array<T>) effects(pure) { [] }",
        "Q<{a}, {b}>"),
    "held_closure": (
        "type IntEndo = fn(Int -> Int) effects(pure);\n\n"
        "public data Conv2<A, B> {\n  Conv2(fn(A -> B) effects(pure))\n}\n\n",
        "Conv2<T, T>", "Conv2(fn(@T -> @T) effects(pure) { @T.0 })",
        "Conv2<{a}, {b}>"),
    "data_fields": (
        "", "Two<T, T>", "Two(@Option<T>.0, @Option<T>.0)", "Two<{a}, {b}>"),
    "tuple": (
        "", "Tuple<Option<T>, Option<T>>",
        "Tuple(@Option<T>.0, @Option<T>.0)",
        "Tuple<Option<{a}>, Option<{b}>>"),
    "nested": (
        "", "Tuple<Array<Option<T>>, Option<Option<T>>>",
        "Tuple([@Option<T>.0], Some(@Option<T>.0))",
        "Tuple<Array<Option<{a}>>, Option<Option<{b}>>>"),
}

#: The shapes whose `T` stands where code generation compiles behaviour.
_BEHAVIOUR = {"closure", "fn_param_result", "held_closure"}

#: The parameter's type arguments: one type, two, a type and the callee's
#: own variable (`take` is then `forall<U>`).
_PARAMS = {"same": ("Int", "Int"), "diff": ("Int", "String"),
           "var": ("Int", "U")}

#: What `make` is given, and so what fixes `T`: nothing, the argument, a
#: literal the expected type fills (spec §4.2).
_BINDERS = {"nowhere": "None", "argument": "Some(@Int.0)",
            "expected": "Some(5)"}


def _consume(shape: str, a: str, b: str, slot: str) -> str:
    """`take`'s body: an `Int` read from the value, at (A, B)."""
    if shape == "closure":
        return (f"apply_fn(@{slot}.0, 40) + 2" if (a, b) == ("Int", "Int")
                else "0")
    if shape == "fn_param_result":
        return f"array_length(apply_fn(@{slot}.0, None)) + 3"
    if shape == "held_closure":
        if (a, b) != ("Int", "Int"):
            return "0"
        return (f"match @{slot}.0 {{\n"
                "  Conv2(@IntEndo) -> apply_fn(@IntEndo.0, 40) + 2\n}")
    if shape == "data_fields":
        return (f"match @{slot}.0 {{\n  Two(Some(@{a}), _) -> 10,\n"
                "  Two(None, _) -> 20\n}")
    if shape == "tuple":
        # The first component's `Option<Int>`: the second slot of the type
        # where both components have it.
        index = 1 if a == b else 0
        return (f"match @{slot}.0 {{\n"
                f"  Tuple(@Option<{a}>, @Option<{b}>) -> "
                f"match @Option<{a}>.{index} {{\n"
                "    Some(@Int) -> @Int.0,\n    None -> 20\n  }\n}")
    assert shape == "nested", shape
    return (f"match @{slot}.0 {{\n"
            f"  Tuple(@Array<Option<{a}>>, @Option<Option<{b}>>) -> "
            f"array_length(@Array<Option<{a}>>.0) + 30\n}}")


def _program(shape: str, param: str, binder: str) -> str:
    decls, made, body, param_form = _SHAPES[shape]
    a, b = _PARAMS[param]
    out = decls + "public data Two<A, B> {\n  Two(Option<A>, Option<B>)\n}\n\n"
    out += _fn("make", "@Option<T>", made, body, forall="forall<T> ") + "\n"
    slot = param_form.format(a=a, b=b)
    if param == "var":
        out += _fn("take", f"@{slot}, @Option<U>", "Int",
                   _consume(shape, a, "U", slot), forall="forall<U> ")
        call = f"take(make({_BINDERS[binder]}), None)"
    else:
        out += _fn("take", f"@{slot}", "Int", _consume(shape, a, b, slot))
        call = f"take(make({_BINDERS[binder]}))"
    return out + "\n" + _fn("f", "@Int", "Int", call, visibility="public")


def _refusal(shape: str, param: str, binder: str) -> str | None:
    """The refusal the one-variable rule gives the cell: `conflict` (`T`
    at two positions given two types), `behaviour` (a function compiled
    before `T` had a type), `mismatch` (`T` fixed, and the types differ),
    or None for an acceptance."""
    fixed = binder != "nowhere"
    if param == "diff":
        if fixed:
            return "mismatch"
        return "behaviour" if shape in _BEHAVIOUR else "conflict"
    if not fixed and shape in _BEHAVIOUR:
        return "behaviour"
    return None


def _value(shape: str, param: str, binder: str) -> int:
    """`f(7)` for an accepted cell, by the language's rules."""
    if shape in ("closure", "held_closure"):
        return 42 if param == "same" else 0
    if shape == "fn_param_result":
        return 3                      # the closure returns `[]`
    if shape == "nested":
        return 31                     # an array of one, plus 30
    option = {"nowhere": None, "argument": 7, "expected": 5}[binder]
    if shape == "data_fields":
        return 20 if option is None else 10
    assert shape == "tuple", shape
    return 20 if option is None else option


#: Where a conflict's two bindings stand, in the message's words.
_CONFLICT_AT = {
    "data_fields": ("type argument 1 of Two", "type argument 2 of Two"),
    "tuple": ("the type argument of Option in component 1",
              "the type argument of Option in component 2"),
    "nested": ("the type argument of Option in the type argument of Array "
               "in component 1",
               "the type argument of Option in the type argument of Option "
               "in component 2"),
}

#: Where a behaviour refusal meets `T`, in the message's words.
_BEHAVIOUR_AT = {
    "closure": "the parameter",
    "fn_param_result": "the type argument of Option in the parameter",
    "held_closure": "type argument 1 of Conv2",
}

#: The closure a closure refusal tells the program to write, by parameter;
#: a parameter that holds `take`'s own variable has no type to write.
_SIGNATURE = {
    ("closure", "same"): "fn(@Int -> @Int) effects(pure)",
    ("closure", "diff"): "fn(@Int -> @String) effects(pure)",
    ("fn_param_result", "same"): "fn(@Option<Int> -> @Array<Int>) effects(pure)",
    ("fn_param_result", "diff"): "fn(@Option<Int> -> @Array<String>) effects(pure)",
}


def _assert_refusal(error, shape: str, param: str, binder: str,
                    kind: str) -> None:
    text = error.description
    if kind == "mismatch":
        # `T` fixed at `Int`: an ordinary mismatch, which names no variable.
        assert "type variable" not in text and "no argument" not in text, text
        assert error.spec_ref.startswith("Chapter 5, Section 5.2"), error.spec_ref
        return
    assert error.spec_ref == 'Chapter 5, Section 5.9 "Generic Functions"'
    if kind == "conflict":
        first, second = _CONFLICT_AT[shape]
        assert (f"its type variable T stands at {first} and at {second}, "
                "where the parameter's type gives it Int and String, and a "
                "type variable takes one type.") in text, text
        assert error.fix.startswith("Pass a value of type "), error.fix
        return
    assert kind == "behaviour", kind
    made = "the value" if shape == "held_closure" else "the closure"
    assert (f"no argument of the call that made {made} gives T a type"
            in text), text
    assert (f"the parameter's type gives T Int at {_BEHAVIOUR_AT[shape]}."
            in text), text
    written = f"`make({_BINDERS[binder]})`"
    if shape == "held_closure":
        assert error.fix == ("Build the value at the parameter's type, from "
                             f"a function written at it, in place of {written}.")
    elif (shape, param) in _SIGNATURE:
        assert error.fix == (
            "Write the closure at the parameter's type, "
            f"`{_SIGNATURE[shape, param]} {{ ... }}`, and pass it in place "
            f"of {written}."), error.fix
    else:
        assert error.fix == (
            "Write the closure at the parameter's type, with each of its "
            f"type variables fixed, and pass it in place of {written}."), error.fix


@pytest.mark.parametrize("binder", list(_BINDERS))
@pytest.mark.parametrize("param", list(_PARAMS))
@pytest.mark.parametrize("shape", list(_SHAPES))
def test_an_argument_s_open_variable_takes_one_type(
        shape: str, param: str, binder: str) -> None:
    """The cell's verdict is the one-variable rule's: a refusal names what
    it names, an acceptance returns its value, and an acceptance at a
    behaviour position records `make` at the type the fit bound."""
    source = _program(shape, param, binder)
    checked = pipeline.check(source)
    if checked.ok and (shape in _BEHAVIOUR or binder != "nowhere"):
        # Whatever the verdict, an accepted fit gave `T` the parameter's
        # `Int`, and the instance code generation compiles is the one the
        # check recorded: a behaviour position's `T` is never left to a
        # type of its own.
        records = {inst.args for inst in checked.typed.instances
                   if inst.key == "make"}
        assert records == {("Int",)}, records
    kind = _refusal(shape, param, binder)
    if kind is not None:
        assert [e.error_code for e in checked.errors] == ["E202"], (
            [e.format() for e in checked.errors])
        _assert_refusal(checked.errors[0], shape, param, binder, kind)
        return
    assert checked.ok, [e.format() for e in checked.errors]
    assert pipeline.run(source, "f", [7]).value == _value(shape, param, binder)


# ---------------------------------------------------------------------
# The issue's members
# ---------------------------------------------------------------------

_REPRO = """\
type Conv = fn(Option<Nat> -> Option<String>) effects(pure);
type Endo<T> = fn(T -> T) effects(pure);

private forall<T> fn mk(@Unit -> @Endo<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T -> @T) effects(pure) { @T.0 }
}

private fn use(@Conv -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match apply_fn(@Conv.0, Some(0)) {
    Some(@String) -> IO.print(string_concat("[", string_concat(@String.0, "]"))),
    None -> IO.print("none")
  }
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  use(mk(()))
}
"""


def _only_error(source: str):
    checked = pipeline.check(source)
    assert [e.error_code for e in checked.errors] == ["E202"], (
        [e.format() for e in checked.errors])
    return checked.errors[0]


def test_repro_the_issue_s_closure_does_not_fit() -> None:
    """The issue's repro.  On `main` at 6f25a652 it checks and verifies,
    and `vera run` prints `[]`: the identity, compiled at `Bool`
    (`$mk$Bool`), is called as a function from `Option<Nat>` to
    `Option<String>`.  Now `E202`, naming `T`, where the parameter gives it
    a type, and the closure to write in its place."""
    error = _only_error(_REPRO)
    assert error.location.line == 28
    assert error.description == (
        "Argument 0 of 'use' has type fn(T -> T) effects(pure), expected "
        "fn(Option<Nat> -> Option<String>) effects(pure): no argument of the "
        "call that made the closure gives T a type, so its code was compiled "
        "at a type of its own, and the parameter's type gives T Option<Nat> "
        "at the parameter.")
    assert error.fix == (
        "Write the closure at the parameter's type, "
        "`fn(@Option<Nat> -> @Option<String>) effects(pure) { ... }`, and "
        "pass it in place of `mk(())`.")


def test_repro_the_fix_applied_as_written_runs() -> None:
    """The refusal's fix, applied as it is written: its closure, with a
    body for the `...`, in place of the call it names."""
    fix = _only_error(_REPRO).fix
    closure, = re.findall(r"`(fn\(.*\{ \.\.\. \})`", fix)
    written, = re.findall(r"in place of `([^`]+)`", fix)
    source = _REPRO.replace(f"use({written})",
                            f"use({closure.replace('...', 'None')})")
    assert source != _REPRO
    checked = pipeline.check(source)
    assert checked.ok, [e.format() for e in checked.errors]
    assert pipeline.run(source).stdout == "none"


_SAME_TYPE = """\
type IntEndo = fn(Int -> Int) effects(pure);
type Endo<T> = fn(T -> T) effects(pure);

private forall<T> fn mk(@Unit -> @Endo<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T -> @T) effects(pure) { @T.0 }
}

private fn use(@IntEndo -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@IntEndo.0, 40) + 2
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  use(mk(()))
}
"""


def test_repro_a_closure_compiled_at_its_own_type_fits_no_other() -> None:
    """The same closure at a parameter one mapping admits (`T` is `Int`).
    On `main` at 6f25a652 it checks and verifies, the check records `mk`
    with `T` unbound, and `vera run` traps (`indirect call type mismatch`):
    the fit's `T` and the record's disagreed.  Now `E202`."""
    error = _only_error(_SAME_TYPE)
    assert "the parameter's type gives T Int at the parameter." in (
        error.description)
    assert error.fix == (
        "Write the closure at the parameter's type, "
        "`fn(@Int -> @Int) effects(pure) { ... }`, and pass it in place of "
        "`mk(())`.")


_HELD = """\
type F = fn(Option<Nat> -> Option<String>) effects(pure);

public data Conv2<A, B> {
  Conv2(fn(A -> B) effects(pure))
}

private forall<T> fn mk(@Unit -> @Conv2<T, T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Conv2(fn(@T -> @T) effects(pure) { @T.0 })
}

private fn use(@Conv2<Option<Nat>, Option<String>> -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match @Conv2<Option<Nat>, Option<String>>.0 {
    Conv2(@F) -> match apply_fn(@F.0, Some(0)) {
      Some(@String) -> IO.print(string_concat("[", string_concat(@String.0, "]"))),
      None -> IO.print("none")
    }
  }
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  use(mk(()))
}
"""


def test_repro_a_value_holding_the_closure_does_not_fit() -> None:
    """The issue's repro through a data field.  On `main` at 6f25a652 it
    checks and verifies, and `vera run` prints `[]`: the call's
    `Conv2<T, T>` took the parameter's type on its name and arity
    (`_synth_fn_call`), before the fit saw it.  Now `E202`."""
    error = _only_error(_HELD)
    assert error.description == (
        "Argument 0 of 'use' has type Conv2<T, T>, expected "
        "Conv2<Option<Nat>, Option<String>>: no argument of the call that "
        "made the value gives T a type, so the function it holds was "
        "compiled at a type of its own, and the parameter's type gives T "
        "Option<Nat> at type argument 1 of Conv2.")
    assert error.fix == ("Build the value at the parameter's type, from a "
                         "function written at it, in place of `mk(())`.")


_HELD_SAME = """\
type G = fn(Int -> Int) effects(pure);

public data Wrap<A> {
  Wrap(fn(A -> A) effects(pure))
}

private forall<T> fn mk(@Unit -> @Wrap<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Wrap(fn(@T -> @T) effects(pure) { @T.0 })
}

private fn use(@Wrap<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Wrap<Int>.0 {
    Wrap(@G) -> apply_fn(@G.0, 40) + 2
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  use(mk(()))
}
"""


def test_repro_a_value_holding_the_closure_fits_no_one_type() -> None:
    """The same-type trap through a data field: on `main` at 6f25a652
    `vera run` traps.  Now `E202`, at the type argument of `Wrap`."""
    error = _only_error(_HELD_SAME)
    assert ("the parameter's type gives T Int at the type argument of Wrap."
            in error.description)


_EMPTY_LITERAL = """\
type Conv = fn(Array<Nat> -> Array<String>) effects(pure);

private forall<T> fn mk2(@Array<T> -> @fn(Array<T> -> Array<T>) effects(pure))
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Array<T> -> @Array<T>) effects(pure) { @Array<T>.0 }
}

private fn use(@Conv -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Array<String> = apply_fn(@Conv.0, [1234567]);
  IO.print(string_concat("[", string_concat(@Array<String>.0[0], "]")))
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  use(mk2([]))
}
"""


def test_repro_an_empty_literal_s_element_type_fits_no_type() -> None:
    """#1692's closure at a call argument: `mk2([])` leaves `T` the empty
    literal's unknown element type.  On `main` at 6f25a652 the `let` and
    the `if` of #1692's report are refused (`E170`, `E301`), and this call
    argument checks, verifies and prints `[]`.  Now `E202`, naming the
    literal's element type, which has no variable name."""
    error = _only_error(_EMPTY_LITERAL)
    assert error.description == (
        "Argument 0 of 'use' has type fn(Array<?> -> Array<?>) effects(pure), "
        "expected fn(Array<Nat> -> Array<String>) effects(pure): the call "
        "that made the closure was given an empty literal, whose element "
        "type no argument fixes, so its code was compiled at a type of its "
        "own, and the parameter's type gives that element type Nat at the "
        "type argument of Array in the parameter.")


_IF = """\
private forall<T> fn twice(@Option<T> -> @Tuple<Option<T>, Option<T>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Option<T>.0, @Option<T>.0)
}

public fn f(@Bool -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length([if @Bool.0 then { twice(None) } else { Tuple(Some(1), Some("a")) }])
}
"""


def test_repro_an_if_gives_a_call_no_type_no_instantiation_gives() -> None:
    """#1690: on `main` at 6f25a652 the check records `twice(None)` and the
    `if` at `Tuple<Option<Int>, Option<String>>`, which no `T` gives
    `twice`, re-synthesising the branch at the other's type.  The call
    now keeps its own type, and the branches disagree (`E301`)."""
    checked = pipeline.check(_IF)
    assert [e.error_code for e in checked.errors] == ["E301"], (
        [e.format() for e in checked.errors])


_CONFLICT = """\
private forall<T> fn twice(@Option<T> -> @Tuple<Option<T>, Option<T>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Option<T>.0, @Option<T>.0)
}

private fn takes(@Tuple<Option<Int>, Option<String>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Tuple<Option<Int>, Option<String>>.0 {
    Tuple(@Option<Int>, @Option<String>) -> 7
  }
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  takes(twice(None))
}
"""

_CONFLICT_HELD_VARIABLE = """\
private forall<T> fn trip(@Option<T> -> @Tuple<Option<T>, Option<T>, Option<T>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Option<T>.0, @Option<T>.0, @Option<T>.0)
}

private forall<U> fn take3(@Tuple<Option<Int>, Option<String>, Option<U>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  take3(trip(None))
}
"""


@pytest.mark.parametrize("source", [_CONFLICT, _CONFLICT_HELD_VARIABLE],
                         ids=["the_coercion", "the_fit"])
def test_repro_a_conflict_names_both_positions_and_both_types(
        source: str) -> None:
    """`T` at two components the parameter gives `Int` and `String`.  On
    `main` at 6f25a652 both check.  The first reached the fit as the
    parameter's own type (`_synth_fn_call`); the second, whose parameter
    holds `take3`'s `U`, was the fit's per-position wildcard."""
    error = _only_error(source)
    assert ("its type variable T stands at the type argument of Option in "
            "component 1 and at the type argument of Option in component 2, "
            "where the parameter's type gives it Int and String, and a type "
            "variable takes one type.") in error.description


_TWO_PARAMETERS = """\
type Two2<T> = fn(T, Int -> T) effects(pure);
type Want = fn(Int, Int -> Int) effects(pure);

private forall<T> fn mk(@Unit -> @Two2<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T, @Int -> @T) effects(pure) { @T.0 }
}

private fn use(@Want -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  use(mk(()))
}
"""

_RESULT = """\
type Out<T> = fn(Int -> Option<T>) effects(pure);
type Want = fn(Int -> Option<String>) effects(pure);

private forall<T> fn mk(@Unit -> @Out<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Option<T>) effects(pure) { None }
}

private fn use(@Want -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  use(mk(()))
}
"""


def test_a_refusal_numbers_a_parameter_and_names_the_result() -> None:
    """A position in a function of two parameters is the parameter's
    number, and one in a function's result is the result's."""
    error = _only_error(_TWO_PARAMETERS)
    assert ("the parameter's type gives T Int at parameter 1."
            in error.description), error.description
    assert error.fix == (
        "Write the closure at the parameter's type, "
        "`fn(@Int, @Int -> @Int) effects(pure) { ... }`, and pass it in "
        "place of `mk(())`.")
    error = _only_error(_RESULT)
    assert ("the parameter's type gives T String at the type argument of "
            "Option in the result." in error.description), error.description


# ---------------------------------------------------------------------
# The enclosing function's own variable
# ---------------------------------------------------------------------

_RIGID = """\
public data Two<A, B> {
  Two(Option<A>, Option<B>)
}

private forall<T> fn pair_of(@T -> @Two<T, T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Two(Some(@T.0), Some(@T.0))
}

private fn use(@Two<Int, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Two<Int, Int>.0 {
    Two(Some(@Int), _) -> @Int.0 + 1,
    Two(None, _) -> 0
  }
}

private forall<A> fn g(@A -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  use(pair_of(@A.0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(true)
}
"""


def test_repro_a_rigid_variable_is_not_taken_for_another_type() -> None:
    """In `forall<A> fn g`, `pair_of(@A.0)` is a `Two<A, A>`.  On `main`
    at 6f25a652 it took `use`'s `Two<Int, Int>` (`_synth_fn_call`), check
    and verify pass, and `g(true)` prints 68719476737, the `Bool` read as
    an `Int`.  Now the generic `E202`: `A` is `g`'s own, so no wording
    about an unfixed variable applies."""
    error = _only_error(_RIGID)
    assert error.description == (
        "Argument 0 of 'use' has type Two<A, A>, expected Two<Int, Int>.")


_RIGID_CLOSURE = """\
type IntEndo = fn(Int -> Int) effects(pure);
type Endo<T> = fn(T -> T) effects(pure);

private forall<T> fn endo_of(@T -> @Endo<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T -> @T) effects(pure) { @T.0 }
}

private fn use(@IntEndo -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@IntEndo.0, 40)
}

private forall<A> fn g(@A -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  use(endo_of(@A.0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(true)
}
"""


def test_a_rigid_variable_in_a_closure_is_no_unfixed_variable() -> None:
    """`endo_of(@A.0)` fixes its `T` at `g`'s `A`, in a closure: the
    refusal is the generic one, since an argument did give the variable a
    type."""
    error = _only_error(_RIGID_CLOSURE)
    assert error.description == (
        "Argument 0 of 'use' has type fn(A -> A) effects(pure), expected "
        "fn(Int -> Int) effects(pure).")


# ---------------------------------------------------------------------
# Two variables no argument fixes
# ---------------------------------------------------------------------

_BOTH_OPEN = """\
type Endo<T> = fn(T -> T) effects(pure);

private forall<T> fn mk(@Unit -> @Endo<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T -> @T) effects(pure) { @T.0 }
}

private forall<U> fn take_endo(@Endo<U>, @Option<U> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<U>.0 {
    Some(@U) -> 1,
    None -> 7
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  take_endo(mk(()), None)
}
"""


def test_a_closure_whose_variable_is_unfixed_fits_no_unfixed_variable() -> None:
    """A closure from a call that fixes nothing, at a parameter whose own
    variable nothing fixes either.  On `main` at 6f25a652 it checks and
    `vera run` prints 7; each variable is compiled at a type of its own,
    and nothing relates the two, so the fit refuses it as it refuses a
    fixed type.  The parameter's open variable renders as `?`, and the
    signature, which has no type to write, is left out."""
    error = _only_error(_BOTH_OPEN)
    assert error.description == (
        "Argument 0 of 'take_endo' has type fn(T -> T) effects(pure), "
        "expected fn(? -> ?) effects(pure): no argument of the call that "
        "made the closure gives T a type, so its code was compiled at a "
        "type of its own, and the parameter's type has a type variable no "
        "argument fixes at the parameter.")
    assert error.fix == (
        "Write the closure at the parameter's type, with each of its type "
        "variables fixed, and pass it in place of `mk(())`.")


# ---------------------------------------------------------------------
# A built-in's variable a failed substitution lost (#1688)
# ---------------------------------------------------------------------

_LOST_AT_ARGUMENT = """\
type M = {{ @Map<String, String> | map_size(@Map<String, String>.0) >= 0 }};

private fn takes(@{param} -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}

private fn first_value(@M -> @Nat)
  requires(map_size(@M.0) > 0)
  ensures(true)
  effects(pure)
{{
  takes(map_values(@M.0)[0])
}}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{{
  first_value(map_insert(map_new(), "k", "hello"))
}}
"""

_LOST_AT_LET = """\
type M = { @Map<String, String> | map_size(@Map<String, String>.0) >= 0 };

private fn values(@M -> @Array<String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<String> = map_values(@M.0);
  @Array<String>.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(values(map_insert(map_new(), "k", "hello")))
}
"""


def test_a_lost_built_in_variable_keeps_the_fit_it_had() -> None:
    """`map_values` over a refinement alias leaves its value variable
    unbound (#1688); the join neither fills nor refuses it, and the fit
    keeps the verdict it gave: the `String` element fits a `String`
    parameter, and `vera run` reads its length."""
    source = _LOST_AT_ARGUMENT.format(param="String",
                                      body="string_length(@String.0)")
    checked = pipeline.check(source)
    assert checked.ok, [e.format() for e in checked.errors]
    assert pipeline.run(source).value == 5


def test_a_lost_built_in_variable_keeps_the_coercion_it_had() -> None:
    """The same variable where a `let` expects `Array<String>`: the call
    takes the expected type, as it did before (`_synth_fn_call`).  No
    corpus or documentation program reaches this arm."""
    checked = pipeline.check(_LOST_AT_LET)
    assert checked.ok, [e.format() for e in checked.errors]
    assert pipeline.run(_LOST_AT_LET).value == 1


@pytest.mark.xfail(strict=True, reason="#1688: a built-in's variable a "
                   "failed substitution lost fits any argument type")
def test_a_lost_built_in_variable_fits_no_other_type() -> None:
    """The `String` element at a `Nat` parameter, which #1688 refuses at
    its source; until then the fit keeps the verdict it gave."""
    source = _LOST_AT_ARGUMENT.format(param="Nat", body="@Nat.0")
    assert not pipeline.check(source).ok
