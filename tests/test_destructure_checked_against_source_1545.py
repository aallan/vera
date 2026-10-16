"""A destructuring `let` is checked as the constructor pattern it is (#1545).

`let C<@T1, …, @Tn> = e;` takes `e` apart by the constructor `C`: it is the
one-arm `match e { C(@T1, …, @Tn) -> … }` whose arm is the rest of the
block.  The checker bound each written type as written and compared nothing
with the value: `let Tuple<@Int, @String> = Tuple(1, 2);` checked and
verified clean, and `@String.0` read the integer 2 as a string.  Nothing
checked that `C` was the value's constructor either, nor that it had as many
fields as there were bindings, so `let Other<@Int, @Int> = Pair(1, 2)`,
`let Some<@Int> = <None>` and `let Tuple<@Int, @String> = Tuple(1, "a",
true)` all checked clean and ran on whatever the layout of the bindings read.

The head names the value's shape by a constructor (`let MkBox<…>`) or by
the value's type (`let Wrap<…>` over a `Wrap<Int>` built by `W`; `let
Tuple<…>`), as the verifier already read it (`_destructure_ctor_name`) and
the #1503 instrument writes it: a type's name is read as the type where it
is the value's, even beside another type's constructor of that name.  A
type alias is a name of the type it stands for, so `let P<…>` with
`type P = Pair;` reads as `let Pair<…>`, as it ran before the rule.

The rule (spec §4.7.1): the destructure is held to the rules its one-arm
`match` is, decided by the functions that decide them for the arm, and each
binding to the rule a `let` binding is held to:

- the head names a constructor or a data type (E320);
- it is the value's: `Tuple` a tuple of as many components as there are
  bindings, a constructor one of the value's type (E314; `_head_misfit`,
  which a `match` arm's constructor pattern reads), a type's name or alias
  the value's type, whose one constructor it then takes the value apart by
  (E314, or E311 where the type has several);
- a data constructor has one binding per field (E321), each field read at
  the value's type arguments (`_constructor_fields`);
- the one arm covers the value's type (`vera.patterns.missing_cases` over
  `_pattern_domain`, the arm's coverage reading): a type with another
  constructor is refused, since a destructure has no second arm (E311), and
  so is a type no constructor builds, a type parameter's among them (E313);
- each component fits its binding (E170 at the binding), by `_fits`, the
  judgement a call argument is held to its parameter by: on concrete types
  it is `is_subtype`, the plain `let`'s rule, so a `@Nat` component widens
  into an `@Int` binding, an `@Int` component narrows into an `@Nat` or a
  refined binding with the verifier's obligation, and anything else is
  refused; a type variable the source leaves open fits whatever the binding
  gives it, as the `let`'s expected type would have fixed it.

A fix writes a type as code only where a program can be written with its
rendering: a refinement, whose predicate the rendering elides
(`{@Int | ...}`), a type an inference variable leaves open (`T$1`, shown as
`?`) and another function's type variable are named in prose or left out
(`_fix_writes`).

The value's type is the type it synthesizes without an expected type, never
the one the bindings would give it: an `if` whose branches build
`Tuple(1, 2)` is a `Tuple<Int, Int>` whatever the destructure says (issue
#1716 is the verifier-side shape of a join taking its context's type).

The class is every destructuring `let` whose head, arity or binding types
disagree with its value, whatever the value's form.  The instrument crosses
the head (a tuple of two components and of three, a data type with one
constructor named by the constructor, by the type and by an alias of the
type, a data type with two, the prelude's `Response`)
with the value's form (a construction, a slot, a call, an `if` join, a
`match` join, a block's tail), the relation of one component to its
binding (equal, `@Nat` into `@Int`, `@Int` into `@Nat`, `String` for `Int`,
a refinement of the component's base, a refined component into its base,
`String` for a refined component) and the arity (one binding per
component, one fewer, one more).  Each cell's verdict is stated as the rule
above: one error of the first rule the cell breaks, at the `let` for the
constructor's rules and at the binding for a component's, or a clean check
whose narrowings the verifier still records.  `Response` declares no `Nat`
field and no refined one, so its `@Nat`-into-`@Int` and refined-component
cells would restate the equal ones and are not cells.

The reported programs, the members the matrix does not span (an unknown
constructor, a prelude type with two constructors named by a constructor
and by the type, a value of no data type, a built-in type with no
constructors, another type's name and an alias of one, a generic data
type, a type parameter, a value of no known type, the other constructor of a tuple and of a data
type, a `@Byte` binding over an `Int` component, a closure field bound at a
narrower effect row, a `@Never` binding) and each mutant's killer are
unparametrised tests.  The negative space: the narrowing the destructure already had keeps
its record and its trap, the plain `let`'s refusal is unchanged, the corpus
destructures and the documented ones check clean, the components a match
arm and a plain `let` accept are accepted here, and a `match` arm's own
diagnostics are unchanged.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline
from vera.errors import Diagnostic

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file
# or a module that decides its class, the checker's reading of a destructure
# and of the constructor pattern it is held to.
pytestmark = pytest.mark.matrix(decides=[
    "vera/checker/expressions.py", "vera/checker/control.py"])

ROOT = Path(__file__).parent.parent


# =====================================================================
# Helpers
# =====================================================================


def _place(source: str, text: str) -> tuple[int, int]:
    """The 1-based line and column of the one occurrence of *text*."""
    assert source.count(text) == 1, text
    at = source.index(text)
    return (source.count("\n", 0, at) + 1,
            at - (source.rfind("\n", 0, at) + 1) + 1)


def _at(checked: pipeline.Checked) -> list[tuple[str, str, int, int]]:
    """Each diagnostic's code, severity and position, in order."""
    return [(d.error_code, d.severity, d.location.line, d.location.column)
            for d in checked.diagnostics]


def _refused_once(source: str, code: str, at: tuple[int, int]) -> None:
    """*source* is refused at check with one diagnostic, *code* at *at*."""
    checked = pipeline.check(source)
    assert _at(checked) == [(code, "error", *at)], [
        (d.error_code, d.description) for d in checked.diagnostics]


def _clean(source: str) -> pipeline.Checked:
    """*source* checks with no diagnostic at all."""
    checked = pipeline.check(source)
    assert not list(checked.diagnostics), [
        (d.error_code, d.description) for d in checked.diagnostics]
    return checked


def _one(source: str, code: str) -> Diagnostic:
    """The one diagnostic *source*'s check reports, which carries *code*."""
    checked = pipeline.check(source)
    assert [d.error_code for d in checked.diagnostics] == [code], [
        (d.error_code, d.description) for d in checked.diagnostics]
    return checked.diagnostics[0]


def _fn(body: str, *, sig: str = "@Int -> @Int", prelude: str = "",
        effects: str = "pure") -> str:
    """A program whose public `f` has *sig* and *body*, after *prelude*."""
    lead = f"{prelude}\n\n" if prelude else ""
    return (f"{lead}public fn f({sig})\n  requires(true)\n  ensures(true)\n"
            f"  effects({effects})\n{{\n  {body}\n}}\n")


# =====================================================================
# The reported programs, refused at check
# =====================================================================

_P1_ISSUE = _fn("let Tuple<@Int, @String> = Tuple(1, 2);\n  @Int.0")


def test_repro_the_issue_tuple_component_is_refused_at_its_binding() -> None:
    """The issue's program: component 2 is an `Int`, bound at `@String`."""
    _refused_once(_P1_ISSUE, "E170", _place(_P1_ISSUE, "String>"))


_P2_DATA = _fn(
    "let Pair<@Int, @String> = Pair(1, 2);\n  string_length(@String.0)",
    prelude="private data Pair { Pair(Int, Int) }")


def test_repro_a_data_field_is_refused_at_its_binding() -> None:
    """A data constructor's field: `Pair`'s second field is an `Int`."""
    _refused_once(_P2_DATA, "E170", _place(_P2_DATA, "String>"))


_P3_OTHER = _fn(
    "let Other<@Int, @Int> = Pair(1, 2);\n  @Int.0 + @Int.1",
    prelude=("private data Pair { Pair(Int, Int) }\n"
             "private data Other { Other(Int, Int) }"))


def test_repro_another_types_constructor_is_refused() -> None:
    """`Other` has `Pair`'s arity and field types and is not `Pair`'s
    constructor (the any-constructor-of-the-right-arity mutant's killer)."""
    _refused_once(_P3_OTHER, "E314", _place(_P3_OTHER, "let Other"))


_P4_IF = _fn(
    "let Tuple<@Int, @String> = if @Int.0 > 0 then { Tuple(1, 2) } else "
    "{ Tuple(3, 4) };\n  string_length(@String.0)")


def test_repro_an_if_join_is_read_at_its_own_type() -> None:
    """The join's branches build `Tuple<Int, Int>`; the bindings are not
    the type the join is read at."""
    _refused_once(_P4_IF, "E170", _place(_P4_IF, "String>"))


_P7_ARITY = _fn("let Tuple<@Int, @String> = Tuple(1, \"a\", true);\n  @Int.0")


def test_repro_a_tuple_of_another_width_is_refused() -> None:
    _refused_once(_P7_ARITY, "E314", _place(_P7_ARITY, "let Tuple"))


# =====================================================================
# Members the matrix does not span, refused at check
# =====================================================================


def test_named_an_unknown_constructor_is_refused() -> None:
    source = _fn("let Nope<@Int> = Tuple(1, 2);\n  @Int.0")
    _refused_once(source, "E320", _place(source, "let Nope"))


def test_named_a_prelude_type_with_two_constructors_is_refused() -> None:
    """`Option` has `None` beside `Some`: the destructure would read a
    field `None` does not have."""
    source = _fn(
        "let @Option<Int> = if @Int.0 > 0 then { Some(7) } else { None };\n"
        "  let Some<@Int> = @Option<Int>.0;\n  @Int.0")
    _refused_once(source, "E311", _place(source, "let Some"))


def test_named_a_json_value_is_refused() -> None:
    source = _fn("let JString<@String> = JNull;\n  string_length(@String.0)")
    _refused_once(source, "E311", _place(source, "let JString"))


def test_named_a_two_constructor_type_named_by_its_type_is_refused() -> None:
    source = _fn("let Option<@Int> = @Option<Int>.0;\n  @Int.0",
                 sig="@Option<Int> -> @Int")
    _refused_once(source, "E311", _place(source, "let Option"))


def test_named_another_types_name_is_refused() -> None:
    source = _fn("let Other<@Int, @Int> = Pair(1, 2);\n  @Int.0",
                 prelude=("private data Pair { Pair(Int, Int) }\n"
                          "private data Other { MkOther(Int, Int) }"))
    _refused_once(source, "E314", _place(source, "let Other"))


_ALIAS_OF_ANOTHER = _fn(
    "let Q<@Int, @Int> = Pair(1, 2);\n  @Int.0",
    prelude=("private data Pair { Pair(Int, Int) }\n"
             "private data Other { MkOther(Int, Int) }\n\n"
             "type Q = Other;"))


def test_named_an_alias_of_another_type_is_refused() -> None:
    """The message names the alias, the type it stands for and the
    value's type."""
    diagnostic = _one(_ALIAS_OF_ANOTHER, "E314")
    assert diagnostic.description == (
        "Destructuring let names the type alias 'Q', which stands for "
        "Other, but the value has type Pair.")
    assert (diagnostic.location.line, diagnostic.location.column) == (
        _place(_ALIAS_OF_ANOTHER, "let Q"))


def test_named_a_type_with_no_constructor_is_refused() -> None:
    """An `Array` has no constructor to take it apart by: at base the
    destructure read its length word as the element."""
    source = _fn("let Array<@Int> = [1, 2];\n  @Int.0")
    _refused_once(source, "E313", _place(source, "let Array"))


def test_named_a_value_of_no_data_type_is_refused() -> None:
    """An `Int` is no tuple: at base this compiled to an invalid module."""
    source = _fn("let Tuple<@Int, @Int> = 5;\n  @Int.0")
    _refused_once(source, "E314", _place(source, "let Tuple"))


def test_named_a_generic_data_field_is_read_at_the_values_type() -> None:
    """`Box(5)` is a `Box<Int>`: its field is an `Int` there."""
    source = _fn("let Box<@String> = Box(5);\n  string_length(@String.0)",
                 prelude="private data Box<T> { Box(T) }")
    _refused_once(source, "E170", _place(source, "String>"))


_TYPE_PARAMETER = """private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = @T.0;
  @Int.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(5)
}
"""


def test_named_a_type_parameter_is_refused() -> None:
    """A value of type `T` may be any value: at base `g(5)` compiled to an
    invalid module.  A `match` over `@T.0` with only a constructor arm is
    refused the same way (E313)."""
    _refused_once(_TYPE_PARAMETER, "E313",
                  _place(_TYPE_PARAMETER, "let Tuple"))


_UNKNOWN_VALUE = """private forall<F> fn g(@F -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = apply_fn(@F.0, 1);
  @Int.0
}
"""


def test_named_a_value_of_no_known_type_is_refused() -> None:
    """`apply_fn` over a type variable is typed `Unknown` with no error
    reported, and a `match` over it with only a constructor arm is refused
    E313, which is then the error that refuses the program (#1671)."""
    _refused_once(_UNKNOWN_VALUE, "E313", _place(_UNKNOWN_VALUE, "let Tuple"))


def test_a_bindings_error_says_nothing_about_the_value() -> None:
    """Whether an error has been reported is read before the bindings are
    resolved, as a `match` reads it before its arms: an unknown binding
    type (E136) leaves the value's own E313 standing."""
    source = _UNKNOWN_VALUE.replace("Tuple<@Int, @Int>", "Tuple<@Nope, @Int>")
    checked = pipeline.check(source)
    assert [d.error_code for d in checked.diagnostics] == ["E136", "E313"], [
        (d.error_code, d.description) for d in checked.diagnostics]


def test_named_a_tuple_destructure_of_data_is_refused() -> None:
    source = _fn("let Tuple<@Int, @Int> = Pair(1, 2);\n  @Int.0",
                 prelude="private data Pair { Pair(Int, Int) }")
    _refused_once(source, "E314", _place(source, "let Tuple"))


def test_named_a_data_destructure_of_a_tuple_is_refused() -> None:
    source = _fn("let Pair<@Int, @Int> = Tuple(1, 2);\n  @Int.0",
                 prelude="private data Pair { Pair(Int, Int) }")
    _refused_once(source, "E314", _place(source, "let Pair"))


def test_named_a_byte_binding_over_an_int_component_is_refused() -> None:
    """A `@Byte` is laid out narrower than the `Int` the tuple holds: at
    base `@Int.0` read 5, the first component, for the second."""
    source = _fn("let Tuple<@Byte, @Int> = Tuple(5, 7);\n  @Int.0")
    _refused_once(source, "E170", _place(source, "Byte,"))


_ROWS = """type IoFn = fn(Int -> Int) effects(<IO>);
type PureFn = fn(Int -> Int) effects(pure);

private data Box { Box(IoFn) }

private fn call_pure(@Box -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Box<@PureFn> = @Box.0;
  apply_fn(@PureFn.0, 1)
}

public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  call_pure(Box(fn(@Int -> @Int) effects(<IO>) { IO.print("x"); @Int.0 }))
}
"""


def test_named_a_closure_field_bound_at_a_narrower_row_is_refused() -> None:
    """An `<IO>` closure bound at a `pure` type: at base the `pure`
    function performed its `IO`.  The judgement is directional, so this is
    the killer of a mutant that compares the binding with the component the
    other way round."""
    _refused_once(_ROWS, "E170", _place(_ROWS, "PureFn> ="))


def test_named_a_never_binding_over_an_int_component_is_refused() -> None:
    """`Never` is a subtype of every type, so a `match` arm binds an `Int`
    field at `@Never` today (and code generation then drops the function,
    E602); the destructure holds the component to its binding in the one
    direction a `let` does."""
    source = _fn("let Tuple<@Never, @Int> = Tuple(1, 2);\n  @Int.0")
    _refused_once(source, "E170", _place(source, "Never,"))


# =====================================================================
# The fixes the diagnostics give, applied as written
# =====================================================================


def _fixed(source: str, code: str, old: str, new: str,
           named: str | None = None) -> None:
    """The *code* diagnostic's fix writes *named* (by default *new*), and
    *source* with *old* replaced by *new* checks with no diagnostic."""
    diagnostic = _one(source, code)
    assert (named or new) in diagnostic.fix, (named or new, diagnostic.fix)
    assert source.count(old) == 1, old
    _clean(source.replace(old, new))


def test_the_component_fix_is_the_components_type() -> None:
    _fixed(_P1_ISSUE, "E170", "@String>", "@Int>", named="`@Int`")


def test_the_data_field_fix_is_the_fields_type() -> None:
    _fixed(_fn("let Pair<@Int, @String> = Pair(1, 2);\n  @Int.0",
               prelude="private data Pair { Pair(Int, Int) }"),
           "E170", "@String>", "@Int>", named="`@Int`")


def test_the_other_constructor_fix_names_the_values_constructor() -> None:
    _fixed(_P3_OTHER, "E314", "Other<@Int, @Int>", "Pair<@Int, @Int>")


def test_the_tuple_width_fix_writes_one_binding_per_component() -> None:
    _fixed(_P7_ARITY, "E314", "Tuple<@Int, @String>",
           "Tuple<@Int, @String, @Bool>")


def test_the_not_a_tuple_fix_binds_the_value_whole() -> None:
    _fixed(_fn("let Tuple<@Int, @Int> = 5;\n  @Int.0"), "E314",
           "let Tuple<@Int, @Int> = 5;", "let @Int = 5;",
           named="`let @Int = ")


def test_the_unknown_constructor_fix_names_the_values_constructor() -> None:
    _fixed(_fn("let Nope<@Int, @Int> = Tuple(1, 2);\n  @Int.0"), "E320",
           "Nope<@Int, @Int>", "Tuple<@Int, @Int>")


def test_the_field_count_fix_writes_one_binding_per_field() -> None:
    _fixed(_fn("let Pair<@Int, @Int, @Int> = Pair(1, 2);\n  @Int.0",
               prelude="private data Pair { Pair(Int, Int) }"),
           "E321", "Pair<@Int, @Int, @Int>", "Pair<@Int, @Int>")


def test_the_refutable_fix_is_a_match() -> None:
    """The fix names a `match` with an arm for the destructure's
    constructor and one for each other constructor."""
    source = _fn("let Some<@Int> = @Option<Int>.0;\n  @Int.0",
                 sig="@Option<Int> -> @Int")
    diagnostic = _one(source, "E311")
    assert "match" in diagnostic.fix and "None" in diagnostic.fix, (
        diagnostic.fix)
    _clean(source.replace(
        "let Some<@Int> = @Option<Int>.0;\n  @Int.0",
        "match @Option<Int>.0 {\n    Some(@Int) -> @Int.0,\n"
        "    None -> 0\n  }"))


def test_the_other_type_name_fix_names_the_values_constructor() -> None:
    _fixed(_fn("let Other<@Int, @Int> = Pair(1, 2);\n  @Int.0",
               prelude=("private data Pair { Pair(Int, Int) }\n"
                        "private data Other { MkOther(Int, Int) }")),
           "E314", "Other<@Int, @Int>", "Pair<@Int, @Int>")


def test_the_other_alias_fix_names_the_values_constructor() -> None:
    _fixed(_ALIAS_OF_ANOTHER, "E314", "Q<@Int, @Int>", "Pair<@Int, @Int>")


def test_the_two_constructor_type_fix_is_a_match() -> None:
    source = _fn("let Option<@Int> = @Option<Int>.0;\n  @Int.0",
                 sig="@Option<Int> -> @Int")
    diagnostic = _one(source, "E311")
    assert "match" in diagnostic.fix and "Some(_)" in diagnostic.fix, (
        diagnostic.fix)
    _clean(source.replace(
        "let Option<@Int> = @Option<Int>.0;\n  @Int.0",
        "match @Option<Int>.0 {\n    None -> 0,\n"
        "    Some(@Int) -> @Int.0\n  }"))


def test_the_no_constructor_fix_binds_the_value_whole() -> None:
    _fixed(_fn("let Array<@Int> = [1, 2];\n  @Int.0"), "E313",
           "let Array<@Int> = [1, 2];\n  @Int.0",
           "let @Array<Int> = [1, 2];\n  0", named="`let @Array<Int> = ")


def test_the_type_parameter_fix_binds_the_value_whole() -> None:
    _fixed(_TYPE_PARAMETER.replace("  @Int.0\n}\n\npublic", "  0\n}\n\npublic"),
           "E313", "let Tuple<@Int, @Int> = @T.0;", "let @T = @T.0;",
           named="`let @T = ")


# A fix over a component an inference variable leaves open (`None`'s `T`)
# writes no code naming it: the open component is reached through `id`,
# which the bindings' types do not reach, so a binding can fit it.
_ID = """private forall<T> fn id(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}"""


def _no_unwritable_code(fix: str) -> None:
    """No code in *fix*, between backticks, is a display rendering no
    program can be written with: an open inference variable (`T$1`, or
    `?`) or a refinement with its predicate elided (`...`)."""
    code = fix.split("`")[1::2]
    assert not any("T$" in c or "?" in c or "..." in c for c in code), fix


def _open_fixed(source: str, code: str, old: str, new: str) -> None:
    """The *code* diagnostic's fix writes no unwritable type, and *source*
    with *old* replaced by *new*, as the fix says, checks clean."""
    diagnostic = _one(source, code)
    _no_unwritable_code(diagnostic.fix)
    assert source.count(old) == 1, old
    _clean(source.replace(old, new))


def test_the_open_component_fix_gives_the_component_its_type() -> None:
    source = _fn("let Tuple<@Int, @Int> = Tuple(None, 1);\n  @Int.0")
    assert _one(source, "E170").fix == (
        "Give the value a component of type Int there, or write the "
        "binding at the type of component 1.")
    _open_fixed(source, "E170", "Tuple(None, 1)", "Tuple(0, 1)")


def test_the_open_unknown_constructor_fix_names_the_constructor() -> None:
    source = _fn("let Nope<@Option<Int>, @Int> = id(Tuple(None, 1));\n"
                 "  @Int.0", prelude=_ID)
    _open_fixed(source, "E320", "let Nope<", "let Tuple<")


def test_the_open_tuple_width_fix_names_the_constructor() -> None:
    source = _fn("let Tuple<@Option<Int>, @Int, @Int> = id(Tuple(None, 1));\n"
                 "  @Int.0", prelude=_ID)
    _open_fixed(source, "E314", "<@Option<Int>, @Int, @Int>",
                "<@Option<Int>, @Int>")


def test_the_open_field_count_fix_counts_the_fields() -> None:
    source = _fn("let MkBox<@Option<Int>, @Int> = id(MkBox(None));\n  0",
                 prelude=f"private data Box<T> {{ MkBox(T) }}\n\n{_ID}")
    assert _one(source, "E321").fix == (
        "Write one binding per field of 'MkBox', 1 in all.")
    _open_fixed(source, "E321", "<@Option<Int>, @Int>", "<@Option<Int>>")


def test_the_open_value_fix_names_no_type_the_function_lacks() -> None:
    """`boom`'s result is its own `T`, which `f` does not declare, so the
    fix does not write `let @T`."""
    source = """private forall<T> fn boom(@Int -> @T)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  throw("boom")
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  let Tuple<@Int, @Int> = boom(@Int.0);
  @Int.0
}
"""
    assert _one(source, "E313").fix == "Destructure a tuple."
    _open_fixed(source, "E313", "boom(@Int.0);", "Tuple(@Int.0, 2);")


def test_the_open_whole_value_fix_writes_no_open_type() -> None:
    source = _fn("let Tuple<@Int> = None;\n  @Int.0")
    _no_unwritable_code(_one(source, "E314").fix)


# A component declared at a refinement is rendered with its predicate
# elided, `{@Int | ...}`, which no program can be written with.
_REFINED = ("type PosInt = { @Int | @Int.0 > 0 };\n\n"
            "private data R { MkR(PosInt) }")


def test_the_refined_component_fix_gives_the_component_its_type() -> None:
    source = _fn("let @PosInt = 5;\n  let Tuple<@String, @Int> = "
                 "Tuple(@PosInt.0, 1);\n  0", prelude=_REFINED)
    _open_fixed(source, "E170", "Tuple(@PosInt.0, 1)", "Tuple(\"a\", 1)")


def test_the_refined_unknown_constructor_fix_names_the_constructor() -> None:
    source = _fn("let Nope<@Int> = MkR(5);\n  0", prelude=_REFINED)
    _open_fixed(source, "E320", "let Nope<", "let MkR<")


def test_the_refined_value_fix_names_its_constructor() -> None:
    source = _fn("let Tuple<@Int> = MkR(5);\n  0", prelude=_REFINED)
    _open_fixed(source, "E314", "let Tuple<@Int>", "let MkR<@PosInt>")


def test_the_refined_field_count_fix_counts_the_fields() -> None:
    source = _fn("let MkR<@Int, @Int> = MkR(5);\n  0", prelude=_REFINED)
    _open_fixed(source, "E321", "<@Int, @Int>", "<@Int>")


# =====================================================================
# Negative space: what is accepted stays accepted, and as it was
# =====================================================================

_P5_NARROWING = _fn("let Tuple<@Nat, @Int> = Tuple(@Int.0, 2);\n"
                    "  nat_to_int(@Nat.0)")


def test_the_narrowing_keeps_its_record_and_its_trap() -> None:
    """`@Int.0` narrowing into `@Nat` is the verifier's obligation, refuted
    for an unconstrained parameter, and code generation's guard, which traps
    on -1 (issue #1695's two sides, unchanged)."""
    _clean(_P5_NARROWING)
    verified = pipeline.verify(_P5_NARROWING)
    assert [(o.kind, o.status, o.error_code) for o in verified.obligations
            if o.kind == "nat_bind"] == [("nat_bind", "violated", "E503")]
    ran = pipeline.run(_P5_NARROWING, fn="f", args=[-1])
    assert ran.trap is not None and ran.trap.kind == "nat_guard", ran


def test_the_plain_lets_refusal_is_unchanged() -> None:
    source = _fn("let @String = 1;\n  string_length(@String.0)")
    diagnostic = _one(source, "E170")
    assert diagnostic.description == (
        "Let binding expects String, value has type Int.")
    assert (diagnostic.location.line, diagnostic.location.column) == (
        _place(source, "1;"))


_CORPUS = (
    "tests/conformance/ch02_tuple_basic.vera",
    "tests/conformance/ch04_nat_binding.vera",
    "examples/maximum_syntax.vera",
    "examples/url_parsing.vera",
)


@pytest.mark.parametrize("path", _CORPUS)
def test_a_corpus_destructure_checks_and_verifies_clean(path: str) -> None:
    """The four corpus programs that destructure (three tuples, one
    `UrlParts`) keep their verdicts; the corpus differential holds their
    JSON and WAT byte for byte."""
    assert "let " in (ROOT / path).read_text(encoding="utf-8")
    checked = pipeline.check(ROOT / path)
    assert checked.ok, [(d.error_code, d.description)
                        for d in checked.diagnostics]
    assert pipeline.verify(ROOT / path).ok


def test_the_documented_destructures_check_clean() -> None:
    """The two destructures the spec shows (§3 Example 6, a fragment, and
    §4.7.1, a statement), written into whole programs."""
    _clean("""public fn f(@Tuple<Int, String, Bool> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let Tuple<@Int, @String, @Bool> = @Tuple<Int, String, Bool>.0;
  if @Bool.0 then {
    @Int.0 + string_length(@String.0)
  } else {
    0
  }
}
""")
    _clean("""private fn some_function(@Int -> @Tuple<Int, String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Int.0, "a")
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @String> = some_function(@Int.0);
  @Int.0
}
""")


_BOX_BESIDE_OTHER = """private data Other { Box(Nat, Nat) }

private data Box<T> { MkBox(Int, T) }

public fn f(@Int, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Box<@Int, @Int> = MkBox(@Int.0, @Nat.0);
  @Int.1
}
"""


def test_the_values_type_name_is_read_as_the_type() -> None:
    """`let Box<…>` over a `Box<Nat>` names the type, whose one constructor
    is `MkBox`, though `Other` has a constructor `Box` (the reading the
    verifier gives it, pinned for #1503 in `test_one_classifier_1503.py`)."""
    _clean(_BOX_BESIDE_OTHER)
    _clean(_BOX_BESIDE_OTHER.replace("let Box<", "let MkBox<"))


_ALIAS_OF_THE_VALUE = """private data Pair { Pair(Int, Int) }

type P = Pair;

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @P = Pair(@Int.0, 2);
  let P<@Int, @Int> = @P.0;
  @Int.1
}
"""


def test_an_alias_of_the_values_type_is_read_as_the_type() -> None:
    """`type P = Pair;` names `Pair`, so `let P<…>` takes a `Pair` apart
    by its constructor and runs as it did before the rule."""
    _clean(_ALIAS_OF_THE_VALUE)
    assert pipeline.run(_ALIAS_OF_THE_VALUE, fn="f", args=[5]).value == 5


def test_a_constructor_is_read_before_a_same_named_alias() -> None:
    """`B` is a constructor of `A` and an alias of `Other`: over an `A`
    the head is `A`'s constructor, as a `match` arm and the verifier read
    it, and over an `Other` it is the alias of the value's type; each ran
    at base and returns 5."""
    decls = ("private data A { B(Int) }\nprivate data Other { MkO(Int) }"
             "\n\ntype B = Other;")
    for value in ("B(@Int.0)", "MkO(@Int.0)"):
        source = _fn(f"let B<@Int> = {value};\n  @Int.0", prelude=decls)
        _clean(source)
        assert pipeline.run(source, fn="f", args=[5]).value == 5, value


def test_an_alias_of_a_tuple_type_reaches_the_tuple_rule() -> None:
    """`type IP = Tuple<Int, Int>;` names a tuple type, read by the
    `Tuple` rule; at base it returned 5."""
    source = _fn("let IP<@Int, @Int> = Tuple(@Int.0, 2);\n  @Int.1",
                 prelude="type IP = Tuple<Int, Int>;")
    _clean(source)
    assert pipeline.run(source, fn="f", args=[5]).value == 5


def test_an_alias_with_type_arguments_names_its_type() -> None:
    """`type IB = Box<Int>;` is a `Box<Int>`, the value's type; at base it
    returned 5."""
    source = _fn("let IB<@Int> = MkBox(@Int.0);\n  @Int.0",
                 prelude=("private data Box<T> { MkBox(T) }\n\n"
                          "type IB = Box<Int>;"))
    _clean(source)
    assert pipeline.run(source, fn="f", args=[5]).value == 5


def test_a_generic_alias_names_its_type_by_the_types_name() -> None:
    """`type Bx<T> = Box<T>;` written without arguments names `Box`."""
    source = _fn("let Bx<@Int, @Int> = MkBox(@Int.0, 7);\n  @Int.0",
                 prelude=("private data Box<T> { MkBox(Int, T) }\n\n"
                          "type Bx<T> = Box<T>;"))
    _clean(source)
    assert pipeline.run(source, fn="f", args=[5]).value == 7


def test_an_alias_of_a_tuple_type_is_held_to_its_components() -> None:
    """An alias of a tuple type is read as `Tuple`, its components held to
    the bindings, and the value's type to the alias's own arguments."""
    alias = "type Pt = Tuple<Int, Int>;"
    good = _fn("let @Pt = Tuple(@Int.0, 2);\n  let Pt<@Int, @Int> = @Pt.0;\n"
               "  @Int.1", prelude=alias)
    _clean(good)
    wrong = good.replace("let Pt<@Int, @Int>", "let Pt<@Int, @String>")
    _refused_once(wrong, "E170", _place(wrong, "String>"))
    wider = _fn("let Pt<@Int, @Int, @Int> = Tuple(@Int.0, 2, 3);\n  @Int.1",
                prelude=alias)
    _refused_once(wider, "E314", _place(wider, "let Pt"))


def test_a_rigid_type_variable_component_fits_itself() -> None:
    """A `forall<T>` body destructures a `Tuple<T, Int>` at `@T`."""
    _clean("""private forall<T> fn g(@Tuple<T, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@T, @Int> = @Tuple<T, Int>.0;
  @Int.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(Tuple(true, @Int.0))
}
""")


def test_a_rigid_type_variable_component_is_no_wildcard() -> None:
    """`T` is the body's own parameter, which no binding fixes."""
    source = """private forall<T> fn g(@Tuple<T, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = @Tuple<T, Int>.0;
  @Int.0
}
"""
    _refused_once(source, "E170", _place(source, "Int, @Int> ="))


def test_an_open_type_variable_component_fits_its_binding() -> None:
    """`id(Tuple(None, 1))` leaves `None`'s type argument open: the binding
    gives it, as the plain `let`'s expected type does (the killer of a
    mutant that compares by `is_subtype` alone)."""
    prelude = """private forall<T> fn id(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}"""
    _clean(_fn("let Tuple<@Option<Int>, @Int> = id(Tuple(None, 1));\n"
               "  @Int.0", prelude=prelude))
    _clean(_fn("let @Tuple<Option<Int>, Int> = id(Tuple(None, 1));\n"
               "  @Int.0", prelude=prelude))


def test_a_closure_field_bound_at_a_wider_row_is_accepted() -> None:
    """A `pure` closure stands where an `<IO>` one is expected, as a call
    argument does: the directional judgement's accepted side."""
    _clean(_ROWS.replace("private data Box { Box(IoFn) }",
                         "private data Box { Box(PureFn) }")
           .replace("let Box<@PureFn> = @Box.0;\n  apply_fn(@PureFn.0, 1)",
                    "let Box<@IoFn> = @Box.0;\n  0")
           .replace("effects(<IO>) { IO.print(\"x\"); @Int.0 }",
                    "effects(pure) { @Int.0 }"))


def test_a_match_arm_over_another_types_constructor_is_unchanged() -> None:
    source = _fn("match Pair(1, 2) {\n    Other(@Int, @Int) -> 1\n  }",
                 prelude=("private data Pair { Pair(Int, Int) }\n"
                          "private data Other { Other(Int, Int) }"))
    checked = pipeline.check(source)
    assert [(d.error_code, d.description) for d in checked.diagnostics] == [
        ("E314", "Pattern 'Other' is a constructor of Other, but the "
                 "scrutinee has type Pair."),
        ("E311", "Non-exhaustive match: missing patterns for Pair."),
    ]


def test_a_match_arm_over_a_tuple_of_another_width_is_unchanged() -> None:
    source = _fn("match Tuple(1, 2, 3) {\n    Tuple(@Int, @Int) -> 1\n  }")
    checked = pipeline.check(source)
    assert [(d.error_code, d.description) for d in checked.diagnostics] == [
        ("E314", "Pattern 'Tuple' with 2 sub-pattern(s) matches a tuple of "
                 "2 component(s), but the scrutinee has type "
                 "Tuple<Int, Int, Int>."),
    ]


def test_a_match_arm_tuple_over_a_value_of_no_tuple_is_unchanged() -> None:
    source = _fn("match @Int.0 {\n    Tuple(@Int, @Int) -> 1,\n"
                 "    _ -> 0\n  }")
    checked = pipeline.check(source)
    assert [(d.error_code, d.description) for d in checked.diagnostics] == [
        ("E314", "Pattern 'Tuple(...)' matches a tuple, but the scrutinee "
                 "has type Int."),
    ]


# The relation of a component to its binding, as (the component's type,
# a value of it in `f`, the binding's type).
_RELATIONS: dict[str, tuple[str, str, str]] = {
    "equal": ("Int", "@Int.0", "Int"),
    "widen": ("Nat", "@Nat.0", "Int"),
    "narrow": ("Int", "@Int.0", "Nat"),
    "mismatch": ("Int", "@Int.0", "String"),
    "refine": ("Int", "@Int.0", "PosInt"),
    "refined": ("PosInt", "@PosInt.0", "Int"),
    "refined-mismatch": ("PosInt", "@PosInt.0", "String"),
}

_POS_INT = "type PosInt = { @Int | @Int.0 > 0 };"


@pytest.mark.parametrize("relation", list(_RELATIONS))
def test_the_destructure_refuses_what_the_plain_let_refuses(
        relation: str) -> None:
    """Each relation, written as a plain `let` of the component and as a
    destructure of a tuple holding it: E170 exactly at `String` for an `Int`
    or a refined `Int`, and nothing for the rest."""
    _c, value, binding = _RELATIONS[relation]
    sig = "@Int, @Nat, @PosInt -> @Int"
    plain = _fn(f"let @{binding} = {value};\n  0", sig=sig, prelude=_POS_INT)
    destructure = _fn(f"let Tuple<@Int, @{binding}> = Tuple(1, {value});\n"
                      f"  0", sig=sig, prelude=_POS_INT)
    if relation in ("mismatch", "refined-mismatch"):
        _refused_once(plain, "E170", _place(plain, f"{value};"))
        _refused_once(destructure, "E170", _place(destructure, "String>"))
    else:
        _clean(plain)
        _clean(destructure)


# =====================================================================
# The class matrix
# =====================================================================


@dataclass(frozen=True)
class _Shape:
    """A constructor a destructure names, and the programs around it.

    *decl* declares its data type (a template over ``{c}``, the varied
    component's type); *type_text* is the type of the value it builds,
    *construct* a construction of it (over ``{c}`` and ``{v}``, a value of
    that type) and *bindings* its binding types (over ``{b}``, the varied
    binding's), *varied* the varied component's index.  *refutable*: its
    type has another constructor."""

    label: str
    ctor: str
    decl: str
    type_text: str
    construct: str
    bindings: tuple[str, ...]
    varied: int
    is_tuple: bool = False
    refutable: bool = False
    relations: tuple[str, ...] = tuple(_RELATIONS)


_SHAPES = (
    _Shape("tuple2", "Tuple", "", "Tuple<Int, {c}>", "Tuple(1, {v})",
           ("Int", "{b}"), 1, is_tuple=True),
    _Shape("tuple3", "Tuple", "", "Tuple<Int, String, {c}>",
           "Tuple(1, \"a\", {v})", ("Int", "String", "{b}"), 2,
           is_tuple=True),
    _Shape("data1", "Pair", "private data Pair {{ Pair(Int, {c}) }}",
           "Pair", "Pair(1, {v})", ("Int", "{b}"), 1),
    _Shape("data1-by-type", "Wrap", "private data Wrap {{ W(Int, {c}) }}",
           "Wrap", "W(1, {v})", ("Int", "{b}"), 1),
    _Shape("data1-by-alias", "PairAlias",
           "private data Pair {{ Pair(Int, {c}) }}\n\ntype PairAlias = Pair;",
           "Pair", "Pair(1, {v})", ("Int", "{b}"), 1),
    _Shape("data2", "Two", "private data Two {{ Two(Int, {c}), One(Int) }}",
           "Two", "Two(1, {v})", ("Int", "{b}"), 1, refutable=True),
    _Shape("prelude", "Response", "", "Response",
           "Response({v}, map_new(), \"x\")",
           ("{b}", "Map<String, String>", "String"), 0,
           relations=("equal", "narrow", "mismatch", "refine")),
)

# The value's form, as (a statement before the destructure, the value):
# templates over ``{cons}`` (a construction) and ``{type}`` (its type).
_SOURCES: dict[str, tuple[str, str]] = {
    "construction": ("", "{cons}"),
    "slot": ("let @{type} = {cons};\n  ", "@{type}.0"),
    "call": ("", "mk(@Int.0, @Nat.0, @PosInt.0)"),
    "if": ("", "if @Int.0 > 0 then {{ {cons} }} else {{ {cons} }}"),
    "match": ("", "match @Int.0 {{ 0 -> {cons}, _ -> {cons} }}"),
    "block": ("", "{{ {cons} }}"),
}

_ARITIES = ("equal", "fewer", "more")

_MK = """private fn mk(@Int, @Nat, @PosInt -> @{type})
  requires(true)
  ensures(true)
  effects(pure)
{{
  {cons}
}}

"""


@dataclass(frozen=True)
class _Cell:
    shape: _Shape
    source: str
    relation: str
    arity: str

    @property
    def bindings(self) -> list[str]:
        _c, _v, binding = _RELATIONS[self.relation]
        written = [t.format(b=binding) for t in self.shape.bindings]
        if self.arity == "fewer":
            return written[:-1]
        if self.arity == "more":
            return [*written, "Int"]
        return written

    @property
    def destructure(self) -> str:
        """The destructure's text up to its `=`."""
        return (f"let {self.shape.ctor}<"
                f"{', '.join('@' + t for t in self.bindings)}> =")

    def program(self) -> str:
        component, value, _b = _RELATIONS[self.relation]
        shape = self.shape
        type_text = shape.type_text.format(c=component)
        cons = shape.construct.format(v=value)
        decl = shape.decl.format(c=component)
        pre, src = _SOURCES[self.source]
        helper = (_MK.format(type=type_text, cons=cons)
                  if self.source == "call" else "")
        head = f"{_POS_INT}\n\n" + (f"{decl}\n\n" if decl else "")
        return (f"{head}{helper}public fn f(@Int, @Nat, @PosInt -> @Int)\n"
                f"  requires(true)\n  ensures(true)\n  effects(pure)\n{{\n"
                f"  {pre.format(type=type_text, cons=cons)}"
                f"{self.destructure} "
                f"{src.format(type=type_text, cons=cons)};\n  0\n}}\n")

    def binding_place(self, program: str, index: int) -> tuple[int, int]:
        """Where binding *index*'s type is written: after its `@`."""
        line, column = _place(program, self.destructure)
        offset = len(f"let {self.shape.ctor}<")
        for written in self.bindings[:index]:
            offset += len(f"@{written}, ")
        return line, column + offset + 1


def _expected(cell: _Cell) -> tuple[str, str] | None:
    """The rule: the code of the first rule *cell* breaks and where it is
    reported ("let" or "binding"), or None for a clean check.  The
    constructor's rules come before its components': a tuple of another
    width is the constructor's (E314), as a data constructor's field count
    is (E321); then a type with another constructor (E311); then the
    varied component, refused only for `String` against an `Int` or a
    refined `Int` (E170)."""
    if cell.arity != "equal":
        return ("E314" if cell.shape.is_tuple else "E321", "let")
    if cell.shape.refutable:
        return ("E311", "let")
    if cell.relation in ("mismatch", "refined-mismatch"):
        return ("E170", "binding")
    return None


# The obligation each accepted relation leaves at the binding, which the
# verifier records whatever its outcome (the component is an unconstrained
# parameter, or reached through an opaque call).
_RECORD = {"narrow": "nat_bind", "refine": "refine_bind"}

_CELLS = [
    _Cell(shape, source, relation, arity)
    for shape, source, arity in itertools.product(
        _SHAPES, _SOURCES, _ARITIES)
    for relation in shape.relations
]


@pytest.mark.parametrize(
    "cell", _CELLS,
    ids=[f"{c.shape.label}-{c.source}-{c.relation}-{c.arity}"
         for c in _CELLS])
def test_the_destructure_is_held_to_its_constructor_pattern(
        cell: _Cell) -> None:
    program = cell.program()
    expected = _expected(cell)
    checked = pipeline.check(program)
    if expected is not None:
        code, where = expected
        at = (_place(program, cell.destructure) if where == "let"
              else cell.binding_place(program, cell.shape.varied))
        assert _at(checked) == [(code, "error", *at)], [
            (d.error_code, d.description) for d in checked.diagnostics]
        return
    assert not list(checked.diagnostics), [
        (d.error_code, d.description) for d in checked.diagnostics]
    kinds = [o.kind for o in pipeline.verify(program).obligations]
    recorded = {k for k in kinds if k in ("nat_bind", "refine_bind")}
    assert recorded == ({_RECORD[cell.relation]} if cell.relation in _RECORD
                        else set()), kinds


# The open family: a tuple whose varied component is `None`, its type
# argument left open where no binding reaches it, over the value's forms a
# construction can take and through `id`, at each arity, bound at `@Int`
# (refused) and at `@Option<Int>` (fits).
_OPEN_SOURCES: dict[str, str] = {
    "construction": "{cons}",
    "if": "if @Int.0 > 0 then {{ {cons} }} else {{ {cons} }}",
    "match": "match @Int.0 {{ 0 -> {cons}, _ -> {cons} }}",
    "block": "{{ {cons} }}",
    "id": "id({cons})",
}


@dataclass(frozen=True)
class _OpenCell:
    shape: _Shape
    source: str
    binding: str
    arity: str

    def program(self) -> str:
        shape = self.shape
        cons = shape.construct.format(v="None")
        written = [t.format(b=self.binding) for t in shape.bindings]
        if self.arity == "fewer":
            written = written[:-1]
        elif self.arity == "more":
            written = [*written, "Int"]
        head = f"let Tuple<{', '.join('@' + t for t in written)}> ="
        return _fn(f"{head} {_OPEN_SOURCES[self.source].format(cons=cons)};"
                   f"\n  0", prelude=_ID)

    def expected(self) -> str | None:
        if self.arity != "equal":
            return "E314"
        return "E170" if self.binding == "Int" else None


_OPEN_CELLS = [
    _OpenCell(shape, source, binding, arity)
    for shape in _SHAPES if shape.is_tuple
    for source in _OPEN_SOURCES
    for binding in ("Int", "Option<Int>")
    for arity in _ARITIES
]


@pytest.mark.parametrize(
    "cell", _OPEN_CELLS,
    ids=[f"{c.shape.label}-{c.source}-{c.binding}-{c.arity}"
         for c in _OPEN_CELLS])
def test_an_open_component_is_held_to_the_rule(cell: _OpenCell) -> None:
    checked = pipeline.check(cell.program())
    assert [d.error_code for d in checked.diagnostics] == (
        [cell.expected()] if cell.expected() else []), [
        (d.error_code, d.description) for d in checked.diagnostics]
    for d in checked.diagnostics:
        _no_unwritable_code(d.fix)


def test_no_fix_writes_a_type_no_program_can_hold() -> None:
    """Over every matrix cell and every open cell, no destructure fix
    writes an open inference variable as code."""
    for program in [c.program() for c in _CELLS] + [
            c.program() for c in _OPEN_CELLS]:
        for d in pipeline.check(program).diagnostics:
            _no_unwritable_code(d.fix)


def test_the_matrix_spans_its_dimensions() -> None:
    """Every shape, value form, relation and arity has cells, and each of
    the rule's outcomes is reached (a vacuous dimension reads as
    coverage)."""
    assert {c.shape.label for c in _CELLS} == {s.label for s in _SHAPES}
    assert {c.source for c in _CELLS} == set(_SOURCES)
    assert {c.relation for c in _CELLS} == set(_RELATIONS)
    assert {c.arity for c in _CELLS} == set(_ARITIES)
    outcomes = {_expected(c) for c in _CELLS}
    assert outcomes == {None, ("E314", "let"), ("E321", "let"),
                        ("E311", "let"), ("E170", "binding")}
    assert len(_CELLS) == 828
