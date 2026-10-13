"""A result reference names the function's return type (#1517).

Spec §3.6: "`@T.result` refers to the function's return value, where `T` is
the return type."  The checker resolved a result reference's type arguments
(#1489) and then typed the reference as the return type whatever its head
named, so on `f(@Int -> @Int)` each of `ensures(@Qzt.result == 1)`,
`ensures(@Nat.result == 1)` and `ensures(@String.result == 1)` passed `vera
check`, and `vera verify` proved it at Tier 1: a proof about a value of a
type the function does not return.  On a function returning `@Bool`,
`@Int.result` reached code generation, which took the reference's width from
its head and wrote a module that does not validate.

The checker now holds a result reference to the return type with the
judgement a slot reference `@T.n` names its binding with (§3.4, §3.8): the
name the reference is keyed by and the name a binding of the declared return
type is bound under, both rendered by `vera.naming.slot_name`, are equal.  So
the rule is the slot rule.  The head is syntactic, and an alias stays opaque:
a `@Cnt` return is `@Cnt.result`, and neither `@Int.result` names it nor
`@Cnt.result` an `@Int` one.  Type arguments resolve: `@Option<Cnt>.result`
and `@Option<Int>.result` both name an `Option<Int>` result.  An inline
refinement is written as its base, an alias of a refinement by its own name,
a type parameter as itself, and an inline function type as `@Fn.result`.  A
reference that names another type is E163, reported at the reference.  Its
message quotes the reference as written and the return type as the
signature spells it, and its fix names the reference in that spelling, which
the program accepts in place of the refused one; the reference then types
as `Unknown`, so nothing else is reported about it, bar a `match` over it,
which is also reported E313 (#1671).  A return type the check refused where
it is written is not judged, so its own error stands alone, as on `main`.

The class is every result reference whose name is not the return type's.
The instrument crosses where the function is declared (at the top level, as
a `where` helper, in an imported module), what it returns (a primitive, an
alias, an inline refinement and an alias of one, constructors with
arguments, refinements among them, a type parameter, a concrete type in a
generic, an inline and an aliased function type), and how the reference's
name differs from the return type's (an undeclared name, another built-in,
`Nat` for `Int` and the reverse, an alias and its body either way, a
refinement's base at the head or in an argument, a type parameter for a
concrete type and the reverse, the right head with other, missing or
undeclared arguments, another head, `Fn` for a type that is not an inline
function type).  Every refused cell also writes the fix's reference in place
of the refused one and checks the program clean.  The complement holds every spelling that names
the result, in every position, clean at check with its postcondition's
verification unchanged, and chapter 3's own examples with them.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

import pytest

from tests import pipeline
from vera.checker import typecheck
from vera.errors import Diagnostic

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file
# or the module that decides its class, the checker's judgement of a result
# reference.
pytestmark = pytest.mark.matrix(decides=["vera/checker/expressions.py"])


# =====================================================================
# Helpers
# =====================================================================


def _place(source: str, text: str, offset: int = 0) -> tuple[int, int]:
    """The 1-based line and column of *offset* into the one occurrence of
    *text* in *source*."""
    assert source.count(text) == 1, text
    at = source.index(text) + offset
    line = source.count("\n", 0, at) + 1
    column = at - (source.rfind("\n", 0, at) + 1) + 1
    return line, column


def _codes(checked: pipeline.Checked) -> list[str]:
    """The error codes the check reported, in order."""
    return [d.error_code for d in checked.errors]


def _e163(checked: pipeline.Checked) -> list[tuple[str, int, int]]:
    """Where each E163 the check reported is placed: its file's name, line
    and column."""
    return [(Path(str(d.location.file)).name if d.location.file else "",
             d.location.line, d.location.column)
            for d in checked.diagnostics if d.error_code == "E163"]


# =====================================================================
# The reported programs
# =====================================================================

_ISSUE = """public fn f(@Int -> @Int)
  requires(true)
  ensures({ref} == 1)
  effects(pure)
{{
  1
}}
"""

#: The issue comment's instance: the mistyped reference reached code
#: generation, which compared it as an `Int` (`i64.eq`) and wrote a module
#: that does not validate.
_ISSUE_BOOL = """public fn gt(@Int, @Int -> @Bool)
  requires(true)
  ensures(@Int.result == (@Int.1 > @Int.0))
  effects(pure)
{
  @Int.1 > @Int.0
}
"""


def _refused_at_the_reference(source: str, ref: str) -> Diagnostic:
    """Check *source*: one error, E163, at the result reference *ref*."""
    checked = pipeline.check(source)
    assert _codes(checked) == ["E163"], checked.errors
    (line, column) = _place(source, ref)
    assert _e163(checked) == [("", line, column)]
    (diag,) = checked.errors
    return diag


def test_repro_an_undeclared_result_type_is_refused() -> None:
    source = _ISSUE.format(ref="@Qzt.result")
    diag = _refused_at_the_reference(source, "@Qzt.result")
    assert diag.description == (
        "@Qzt.result does not refer to the result of 'f', which returns "
        "Int: its result is @Int.result.")
    assert diag.fix == "Write @Int.result."
    assert diag.spec_ref == 'Chapter 3, Section 3.6 "The `@result` Reference"'
    assert diag.rationale
    assert not pipeline.verify(source).ran


def test_repro_a_nat_result_on_an_int_function_is_refused() -> None:
    source = _ISSUE.format(ref="@Nat.result")
    diag = _refused_at_the_reference(source, "@Nat.result")
    assert diag.description == (
        "@Nat.result does not refer to the result of 'f', which returns "
        "Int: its result is @Int.result.")
    assert not pipeline.verify(source).ran


def test_repro_a_string_result_on_an_int_function_is_refused() -> None:
    source = _ISSUE.format(ref="@String.result")
    diag = _refused_at_the_reference(source, "@String.result")
    assert diag.description == (
        "@String.result does not refer to the result of 'f', which returns "
        "Int: its result is @Int.result.")
    assert not pipeline.verify(source).ran


def test_repro_an_int_result_on_a_bool_function_never_reaches_codegen() -> None:
    diag = _refused_at_the_reference(_ISSUE_BOOL, "@Int.result")
    assert diag.description == (
        "@Int.result does not refer to the result of 'gt', which returns "
        "Bool: its result is @Bool.result.")
    compiled = pipeline.compile(_ISSUE_BOOL)
    assert [d.error_code for d in compiled.errors] == ["E163"]


def test_the_correct_reference_still_checks_and_proves() -> None:
    # The issue's control: `@Int.result` on `f(@Int -> @Int)`.
    verified = pipeline.verify(_ISSUE.format(ref="@Int.result"))
    assert verified.diagnostics == ()
    assert {(o.kind, o.status) for o in verified.obligations} == {
        ("requires", "verified"), ("ensures", "verified")}


# =====================================================================
# The class: where the function is x what it returns x how the name differs
# =====================================================================

#: The aliases every program declares, beside the function: an alias of a
#: primitive, of a refinement and of a function type.
_PRE = """type Cnt = Int;
type PosInt = { @Int | @Int.0 > 0 };
type IntFn = fn(Int -> Int) effects(pure);
"""

#: How a reference's name can differ from the return type's.  Every kind is
#: used by at least one return type (`test_every_kind_is_exercised`).
KINDS: dict[str, str] = {
    "undeclared": "a name nothing declares",
    "builtin": "another built-in type",
    "nat_int": "`Nat` for `Int`, or `Int` for `Nat`",
    "alias": "an alias of the return type",
    "alias_body": "the type the return type's alias stands for",
    "refinement_base": "the base of the refinement the return type's alias "
                       "names",
    "refinement_arg_base": "the base of a refinement among the return type's "
                           "arguments",
    "type_param": "a type parameter for a concrete type",
    "concrete": "a concrete type for a type parameter",
    "wrong_args": "the return type's head with other type arguments",
    "missing_args": "the return type's head without its type arguments",
    "undeclared_arg": "the return type's head with an argument nothing "
                      "declares",
    "other_head": "a constructor head for a primitive return, or a "
                  "primitive head for a constructor return",
    "fn_head": "`Fn` for a return type that is not an inline function type",
}


@dataclass(frozen=True)
class Ret:
    """A return type, a function of that type, and the names that do and do
    not name its result.

    *written* is the name its result reference is written with, spelled as
    the signature spells the return type: an argument as written, a
    refinement written out at the head by its base, and a function type
    written out at the head as `Fn`.  *ensures* is the postcondition the
    complement proves of the result, with `{r}` where the reference goes; *proved* is whether `vera verify` proves it at Tier 1
    (a function-typed result's postcondition is a runtime check, E522).
    A generic's *caller* instantiates it, so its postcondition is verified
    at a concrete type: the caller's parameters, return type and body, with
    `{callee}` where the generic's name goes.  *cascade* is what the check
    reports after E163 about a postcondition built on the refused
    reference: a `match` over it is also reported E313 (#1671).
    """

    spelling: str
    written: str
    params: str
    args: str
    body: str
    ensures: str
    right: tuple[str, ...]
    wrong: dict[str, str]
    forall: str = ""
    requires: str = "true"
    caller: tuple[str, str, str] | None = None
    proved: bool = True
    cascade: tuple[str, ...] = ()


_CLOSURE = "fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }"

RETURNS: dict[str, Ret] = {
    "int": Ret(
        "@Int", "Int", "@Int", "@Int.0", "@Int.0", "{r} == @Int.0",
        right=("Int",),
        wrong={"undeclared": "Qzt", "builtin": "String", "nat_int": "Nat",
               "alias": "Cnt", "other_head": "Option<Int>",
               "fn_head": "Fn"}),
    "nat": Ret(
        "@Nat", "Nat", "@Nat", "@Nat.0", "@Nat.0", "{r} == @Nat.0",
        right=("Nat",),
        wrong={"undeclared": "Qzt", "builtin": "Bool", "nat_int": "Int"}),
    "alias": Ret(
        "@Cnt", "Cnt", "@Cnt", "@Cnt.0", "@Cnt.0", "{r} == @Cnt.0",
        right=("Cnt",),
        wrong={"undeclared": "Qzt", "alias_body": "Int", "nat_int": "Nat"}),
    "refined": Ret(
        "@{ @Int | @Int.0 > 0 }", "Int", "@Int", "@Int.0", "@Int.0",
        "{r} == @Int.0", requires="@Int.0 > 0",
        right=("Int",),
        wrong={"undeclared": "Qzt", "builtin": "String", "nat_int": "Nat",
               "alias": "PosInt"}),
    "refined_alias": Ret(
        "@PosInt", "PosInt", "@PosInt", "@PosInt.0", "@PosInt.0",
        "{r} == @PosInt.0",
        right=("PosInt",),
        wrong={"undeclared": "Qzt", "nat_int": "Nat",
               "refinement_base": "Int"}),
    "option": Ret(
        "@Option<Int>", "Option<Int>", "@Int", "@Int.0", "Some(@Int.0)",
        "{r} == Some(@Int.0)",
        right=("Option<Int>", "Option<Cnt>"),
        wrong={"undeclared": "Qzt", "wrong_args": "Option<Nat>",
               "missing_args": "Option", "undeclared_arg": "Option<Qzt>",
               "other_head": "Int"}),
    "option_alias_arg": Ret(
        "@Option<Cnt>", "Option<Cnt>", "@Int", "@Int.0", "Some(@Int.0)",
        "{r} == Some(@Int.0)",
        right=("Option<Int>", "Option<Cnt>"),
        wrong={"wrong_args": "Option<String>", "missing_args": "Option"}),
    "option_refined_alias_arg": Ret(
        "@Option<PosInt>", "Option<PosInt>", "@PosInt", "@PosInt.0",
        "Some(@PosInt.0)", "{r} == Some(@PosInt.0)",
        right=("Option<PosInt>", "Option<{ @Int | @Int.0 > 0 }>"),
        wrong={"refinement_arg_base": "Option<Int>", "missing_args": "Option"}),
    "array_refined_arg": Ret(
        "@Array<{ @Int | @Int.0 > 0 }>", "Array<{ @Int | @Int.0 > 0 }>",
        "@Array<{ @Int | @Int.0 > 0 }>", "@Array<{ @Int | @Int.0 > 0 }>.0",
        "@Array<{ @Int | @Int.0 > 0 }>.0",
        "array_length({r}) == array_length(@Array<{{ @Int | @Int.0 > 0 }}>.0)",
        right=("Array<{ @Int | @Int.0 > 0 }>", "Array<PosInt>"),
        wrong={"refinement_arg_base": "Array<Int>", "missing_args": "Array"}),
    "tuple": Ret(
        "@Tuple<Int, String>", "Tuple<Int, String>", "@Int, @String",
        "@Int.0, @String.0", "Tuple(@Int.0, @String.0)",
        "match {r} {{ Tuple(@Int, @String) -> @Int.0 == @Int.1 }}",
        cascade=("E313",),
        right=("Tuple<Int, String>",),
        wrong={"wrong_args": "Tuple<String, Int>", "missing_args": "Tuple"}),
    "array_param": Ret(
        "@Array<T>", "Array<T>", "@Array<T>", "@Array<T>.0", "@Array<T>.0",
        "array_length({r}) == array_length(@Array<T>.0)",
        forall="forall<T> ",
        caller=("@Array<Int>", "@Nat", "array_length({callee}(@Array<Int>.0))"),
        right=("Array<T>",),
        wrong={"concrete": "Array<Int>", "missing_args": "Array",
               "type_param": "T", "other_head": "Option<T>"}),
    "type_param": Ret(
        "@T", "T", "@T", "@T.0", "@T.0", "{r} == @T.0",
        forall="forall<T where Eq<T>> ",
        caller=("@Int", "@Int", "{callee}(@Int.0)"),
        right=("T",),
        wrong={"undeclared": "Qzt", "concrete": "Int",
               "other_head": "Option<T>"}),
    "concrete_in_generic": Ret(
        "@Int", "Int", "@T, @Int", "@T.0, @Int.0", "@Int.0", "{r} == @Int.0",
        forall="forall<T> ",
        caller=("@Int", "@Int", "{callee}(true, @Int.0)"),
        right=("Int",),
        wrong={"type_param": "T"}),
    "function": Ret(
        "@fn(Int -> Int) effects(pure)", "Fn", "@Int", "@Int.0", _CLOSURE,
        "apply_fn({r}, 0) == @Int.0", proved=False,
        right=("Fn",),
        wrong={"undeclared": "Qzt", "builtin": "Int", "alias": "IntFn"}),
    "function_alias": Ret(
        "@IntFn", "IntFn", "@Int", "@Int.0", _CLOSURE,
        "apply_fn({r}, 0) == @Int.0", proved=False,
        right=("IntFn",),
        wrong={"builtin": "Int", "fn_head": "Fn"}),
}


def _ref(name: str) -> str:
    return f"@{name}.result"


def _caller(ret: Ret, callee: str) -> str:
    if ret.caller is None:
        return ""
    params, result, body = ret.caller
    return (f"\npublic fn main({params} -> {result})\n  requires(true)\n"
            f"  ensures(true)\n  effects(pure)\n{{\n"
            f"  {body.format(callee=callee)}\n}}\n")


@dataclass(frozen=True)
class Program:
    """A program holding one function whose postcondition carries the
    reference: the file it is written in, the function's name, its source,
    and the files to write (empty for a single source)."""

    file: str
    fn: str
    source: str
    files: dict[str, str] = field(default_factory=dict)


def _top_level(ret: Ret, ensures: str) -> Program:
    vis = "private" if ret.forall else "public"
    source = (
        f"{_PRE}\n{vis} {ret.forall}fn f({ret.params} -> {ret.spelling})\n"
        f"  requires({ret.requires})\n  ensures({ensures})\n  effects(pure)\n"
        f"{{\n  {ret.body}\n}}\n{_caller(ret, 'f')}")
    return Program("", "f", source)


def _where_helper(ret: Ret, ensures: str) -> Program:
    vis = "private" if ret.forall else "public"
    source = (
        f"{_PRE}\n{vis} {ret.forall}fn f({ret.params} -> {ret.spelling})\n"
        f"  requires({ret.requires})\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  g({ret.args})\n}}\nwhere {{\n"
        f"  fn g({ret.params} -> {ret.spelling})\n"
        f"    requires({ret.requires})\n    ensures({ensures})\n"
        f"    effects(pure)\n  {{\n    {ret.body}\n  }}\n}}\n"
        f"{_caller(ret, 'f')}")
    return Program("", "g", source)


_IMPORTER = """import lib(g);

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(pure)
{
  ()
}
"""


def _imported(ret: Ret, ensures: str) -> Program:
    source = (
        f"module lib;\n\n{_PRE}\npublic {ret.forall}fn g({ret.params} -> "
        f"{ret.spelling})\n  requires({ret.requires})\n  ensures({ensures})\n"
        f"  effects(pure)\n{{\n  {ret.body}\n}}\n{_caller(ret, 'g')}")
    return Program("lib.vera", "g", source,
                   {"lib.vera": source, "main.vera": _IMPORTER})


#: Where the function is declared.  An imported function is checked through
#: the program that imports it, as `vera check main.vera` checks it.
LOCATIONS = {
    "top_level": _top_level,
    "where_helper": _where_helper,
    "imported": _imported,
}


def _fixed_reference(diag: Diagnostic) -> str:
    """The reference an E163's fix says to write."""
    prefix, suffix = "Write ", "."
    assert diag.fix.startswith(prefix) and diag.fix.endswith(suffix), diag.fix
    return diag.fix[len(prefix):-len(suffix)]


def _check(program: Program, tmp_path: Path) -> pipeline.Checked:
    if not program.files:
        return pipeline.check(program.source)
    entry = pipeline.write_tree(tmp_path, program.files)
    return pipeline.check(entry, root=tmp_path)


def _wrong_cells() -> list[tuple[str, str, str]]:
    return [(location, ret_name, kind)
            for location in LOCATIONS
            for ret_name, ret in RETURNS.items()
            for kind in ret.wrong]


def _right_cells() -> list[tuple[str, str, str]]:
    return [(location, ret_name, name)
            for location in LOCATIONS
            for ret_name, ret in RETURNS.items()
            for name in ret.right]


def test_every_kind_is_exercised() -> None:
    used = {kind for ret in RETURNS.values() for kind in ret.wrong}
    assert used == set(KINDS)


def test_the_wrong_and_right_names_are_disjoint() -> None:
    for ret in RETURNS.values():
        assert ret.written in ret.right
        assert not set(ret.right) & set(ret.wrong.values())


@pytest.mark.parametrize(("location", "ret_name", "kind"), _wrong_cells())
def test_a_reference_of_another_type_is_refused_where_it_is_written(
        location: str, ret_name: str, kind: str, tmp_path: Path) -> None:
    ret = RETURNS[ret_name]
    wrong = _ref(ret.wrong[kind])
    program = LOCATIONS[location](ret, ret.ensures.format(r=wrong))
    checked = _check(program, tmp_path)
    expected = (["E136"] if kind == "undeclared_arg" else []) + ["E163"]
    assert _codes(checked) == expected + list(ret.cascade), checked.errors
    line, column = _place(program.source, wrong)
    assert _e163(checked) == [(program.file, line, column)]
    diag = next(d for d in checked.errors if d.error_code == "E163")
    # The reference the fix names is one the program accepts: written in
    # place of the refused one, the program checks clean.
    fixed = _fixed_reference(diag)
    repaired = LOCATIONS[location](ret, ret.ensures.format(r=fixed))
    assert _check(repaired, tmp_path).diagnostics == (), diag.fix
    # Every spelling in the message is the program's own: the reference as
    # written, the return type as the signature spells it, and the
    # reference to write in that spelling.
    assert diag.description == (
        f"{wrong} does not refer to the result of '{program.fn}', which "
        f"returns {ret.spelling[1:]}: its result is {_ref(ret.written)}.")
    assert diag.fix == f"Write {_ref(ret.written)}."


@pytest.mark.parametrize(("location", "ret_name", "name"), _right_cells())
def test_a_reference_of_the_return_type_checks_and_verifies(
        location: str, ret_name: str, name: str, tmp_path: Path) -> None:
    ret = RETURNS[ret_name]
    right = _ref(name)
    ensures = ret.ensures.format(r=right)
    program = LOCATIONS[location](ret, ensures)
    checked = _check(program, tmp_path)
    assert checked.diagnostics == ()
    # The postcondition is verified in the file that declares it, where its
    # function is checked and, for a generic, instantiated by its caller.
    subject: pipeline.Source = program.source
    if program.files:
        subject = tmp_path / program.file
    verified = pipeline.verify(subject, root=tmp_path if program.files else None)
    assert verified.errors == ()
    line, _ = _place(program.source, f"ensures({ensures})")
    (ensured,) = [o for o in verified.obligations
                  if o.kind == "ensures" and o.fn_name == program.fn
                  and o.line == line]
    assert ensured.status == ("verified" if ret.proved else "tier3")


# =====================================================================
# Chapter 3's examples, each completed into a program where the spec gives
# a fragment: every one checks clean, and its postcondition verifies as it
# did before the reference was held to the return type.
# =====================================================================

SPEC_EXAMPLES: dict[str, tuple[str, str]] = {
    # §3.4.1, scope ordering.
    "scope_ordering": ("verified", """public fn f(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Int = @Int.0 + 1;
  @Int.0
}
"""),
    # §3.5, Example 1.
    "simple_function": ("verified", """private fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + @Int.1)
  effects(pure)
{
  @Int.0 + @Int.1
}
"""),
    # §3.5, Example 2.
    "mixed_types": ("tier3", """public fn f(@Int, @String, @Int -> @String)
  requires(@Int.0 > @Int.1)
  ensures(string_length(@String.result) > 0)
  effects(pure)
{
  string_concat(string_concat(to_string(@Int.1), @String.0), to_string(@Int.0))
}
"""),
    # §3.5, Example 3.
    "nested_lets": ("verified", """public fn f(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @Int = @Int.0 * 2;
  let @Int = @Int.0 + 1;
  let @String = to_string(@Int.0);
  @Int.0
}
"""),
    # §3.5, Example 4.  Its postcondition does not hold (a `Some` of a
    # negative returns it), and is refuted, as it was.
    "pattern_matching": ("violated", """public fn f(@Option<Int> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
"""),
    # §3.5, Example 6.
    "tuple_destructuring": ("tier3", """public fn f(@Tuple<Int, String, Bool> -> @Int)
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
"""),
    # §3.5, Example 7.
    "recursive_decreases": ("verified", """private fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    1
  } else {
    let @Nat = @Nat.0 - 1;
    @Nat.1 * factorial(@Nat.0)
  }
}
"""),
    # §3.5, Example 8.
    "higher_order": ("tier3", """private forall<A, B> fn map_array(@Array<A>, @fn(A -> B) effects(pure) -> @Array<B>)
  requires(true)
  ensures(array_length(@Array<B>.result) == array_length(@Array<A>.0))
  effects(pure)
{
  array_map(@Array<A>.0, @Fn.0)
}
"""),
    # §3.5, Example 10.
    "return_type_references": ("verified", """private fn clamp_between(@Int, @Int, @Int -> @Int)
  requires(@Int.2 <= @Int.1)
  ensures(@Int.result >= @Int.2 && @Int.result <= @Int.1)
  effects(pure)
{
  if @Int.0 < @Int.2 then {
    @Int.2
  } else {
    if @Int.0 > @Int.1 then {
      @Int.1
    } else {
      @Int.0
    }
  }
}
"""),
    # §3.6, the result reference.
    "result_reference": ("verified", """public fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{
  @Int.0 + 1
}
"""),
    # §3.6, a compound result.
    "compound_result": ("verified", """public fn f(@Int -> @Tuple<Int, String>)
  requires(true)
  ensures(match @Tuple<Int, String>.result { Tuple(@Int, @String) -> @Int.0 > @Int.1 })
  effects(pure)
{
  Tuple(@Int.0 + 1, "a")
}
"""),
    # §3.7, a function type through an alias.
    "function_type_alias": ("tier3", """type IntTransform = fn(Int -> Int) effects(pure);

private fn apply_to_array(@Array<Int>, @IntTransform -> @Array<Int>)
  requires(array_length(@Array<Int>.0) > 0)
  ensures(array_length(@Array<Int>.result) == array_length(@Array<Int>.0))
  effects(pure)
{
  array_map(@Array<Int>.0, @IntTransform.0)
}
"""),
}


@pytest.mark.parametrize("name", sorted(SPEC_EXAMPLES))
def test_a_chapter_3_example_checks_and_verifies_as_it_did(name: str) -> None:
    status, source = SPEC_EXAMPLES[name]
    assert pipeline.check(source).diagnostics == ()
    verified = pipeline.verify(source)
    assert [o.status for o in verified.obligations
            if o.kind == "ensures"] == [status]


# =====================================================================
# Mutant killers: each fails against the mutant the test names
# =====================================================================

_OPTION = """public fn f(@Int -> @Option<Int>)
  requires(true)
  ensures({ref} == Some(@Int.0))
  effects(pure)
{{
  Some(@Int.0)
}}
"""


def test_mutant_the_type_arguments_are_compared_not_only_the_head() -> None:
    # A checker that compares the head's name alone accepts the right head
    # with the wrong argument.
    source = _OPTION.format(ref="@Option<Nat>.result")
    diag = _refused_at_the_reference(source, "@Option<Nat>.result")
    assert diag.fix == "Write @Option<Int>.result."


def test_mutant_a_declared_type_that_is_not_the_return_type_is_refused() -> None:
    # A checker that refuses only a name nothing declares accepts a declared
    # type, a built-in or an alias, that the function does not return.
    for ref in ("@String.result", "@Nat.result", "@Cnt.result"):
        source = _PRE + _ISSUE.format(ref=ref)
        _refused_at_the_reference(source, ref)


_REFUSED_RETURN = """type Box<T> = Option<T>;
type PosInt = {{ @Int | @Int.0 > 0 }};

public fn f({params} -> {ret})
  requires(true)
  ensures({ens})
  effects(pure)
{{
  {body}
}}
"""


def _refused_return(params: str, ret: str, body: str,
                    ens: str) -> list[str]:
    """The error codes of a function whose return type is *ret*."""
    source = _REFUSED_RETURN.format(params=params, ret=ret, body=body,
                                    ens=ens)
    return _codes(pipeline.check(source))


def test_repro_an_unresolved_argument_of_the_return_type_is_not_judged() -> None:
    # `Box` takes one argument and is given none (E133), so the return type
    # resolves to no type, and the reference is not held to it: E133 alone,
    # as on `main`.
    assert _refused_return("@Int", "@Option<Box>", "None",
                           "@Option<Int>.result == None") == ["E133"]


def test_repro_an_undeclared_argument_of_the_return_type_is_not_judged() -> None:
    # `Qzt` is declared nowhere (E136): E136 alone, as on `main`.
    assert _refused_return("@Int", "@Array<Qzt>", "[]",
                           "array_length(@Array<Int>.result) == 0") == ["E136"]


#: Return types refused where they are written, each beside a reference of
#: another type, with the codes `main` reports for the program: the return
#: type's own errors, then whatever the reference, typed as the return type,
#: draws there.  A removed alias is reported at its first use only, here the
#: parameter, so the return type that repeats it is reported nowhere and is
#: still not judged.
_REFUSED_RETURNS: dict[str, tuple[str, str, str, str, list[str]]] = {
    "arity": ("@Int", "@Box", "None", "@Option<Int>.result == None",
              ["E133"]),
    "undeclared": ("@Qzt", "@Qzt", "@Qzt.0", "@Int.result == 1",
                   ["E136", "E136", "E142"]),
    "zero_size_argument": ("@Int", "@Array<Unit>", "[]",
                           "array_length(@Array<Int>.result) == 0", ["E135"]),
    "removed_alias_argument": ("@Float", "@Option<Float>", "None",
                               "@Option<Float64>.result == None", [""]),
}


def test_mutant_a_return_type_refused_where_it_is_written_is_not_judged() -> None:
    # A reference held to a return type the check refused would add an
    # E163 naming a spelling that is itself refused.
    for name, (params, ret, body, ens, codes) in _REFUSED_RETURNS.items():
        assert _refused_return(params, ret, body, ens) == codes, name


_HOLE_IN_RETURN = """public fn f(@Int -> @{{ @{base} | ? }})
  requires(true)
  ensures({ens})
  effects(pure)
{{
  {body}
}}
"""


def test_repro_a_warning_inside_the_return_type_leaves_it_judged() -> None:
    # A typed hole in the return type's refinement is a warning (W001), and
    # a warning refuses nothing: the reference is still held to the type,
    # so the program is refused and nothing about it is proved.
    for base, ref, ens, body in (
            ("Bool", "@Int.result", "@Int.result", "true"),
            ("Int", "@Nat.result", "@Nat.result == 1", "@Int.0")):
        source = _HOLE_IN_RETURN.format(base=base, ens=ens, body=body)
        checked = pipeline.check(source)
        assert [d.error_code for d in checked.warnings] == ["W001"], base
        assert _codes(checked) == ["E163"], base
        assert _e163(checked) == [("", *_place(source, ref))], base
        assert not pipeline.verify(source).ran, base


_HOLE_IN_ARGUMENT = """public fn f(@Int -> @Option<{ @Int | ? }>)
  requires(true)
  ensures(@Option<Nat>.result == None)
  effects(pure)
{
  None
}
"""


def test_repro_a_warning_inside_a_return_type_argument_leaves_it_judged() -> None:
    # The same hole, in the refinement of a type argument.
    checked = pipeline.check(_HOLE_IN_ARGUMENT)
    assert [d.error_code for d in checked.warnings] == ["W001"]
    assert _codes(checked) == ["E163"]
    assert _e163(checked) == [
        ("", *_place(_HOLE_IN_ARGUMENT, "@Option<Nat>.result"))]
    assert not pipeline.verify(_HOLE_IN_ARGUMENT).ran


def test_repro_an_alias_return_is_named_as_declared() -> None:
    source = _PRE + _ISSUE.format(ref="@Int.result").replace(
        "-> @Int)", "-> @Cnt)")
    diag = _refused_at_the_reference(source, "@Int.result")
    assert diag.description == (
        "@Int.result does not refer to the result of 'f', which returns "
        "Cnt: its result is @Cnt.result.")
    assert diag.fix == "Write @Cnt.result."


def test_repro_a_refinement_argument_is_written_as_declared() -> None:
    # The return type's key elides the refinement's predicate, so it is no
    # spelling: the fix names the argument as the signature writes it.
    source = _REFUSED_RETURN.format(
        params="@Int", ret="@Option<PosInt>", body="None",
        ens="@Option<Int>.result == None")
    diag = _refused_at_the_reference(source, "@Option<Int>.result")
    assert diag.description == (
        "@Option<Int>.result does not refer to the result of 'f', which "
        "returns Option<PosInt>: its result is @Option<PosInt>.result.")
    assert diag.fix == "Write @Option<PosInt>.result."
    repaired = source.replace("@Option<Int>.result", _fixed_reference(diag))
    assert pipeline.check(repaired).diagnostics == ()


def test_repro_the_reference_is_quoted_as_written() -> None:
    # The reference's key resolves its argument (`Option<Int>`); the message
    # quotes what the program wrote.
    source = _PRE + _OPTION.format(ref="@Option<Cnt>.result").replace(
        "-> @Option<Int>)", "-> @Option<String>)").replace(
        "Some(@Int.0)", "None")
    diag = _refused_at_the_reference(source, "@Option<Cnt>.result")
    assert diag.description == (
        "@Option<Cnt>.result does not refer to the result of 'f', which "
        "returns Option<String>: its result is @Option<String>.result.")


_ACROSS_LINES = """public fn f(@Int -> @Option<
    Int>)
  requires(true)
  ensures(@Option<Nat>.result == None)
  effects(pure)
{
  None
}
"""


def test_a_return_type_written_across_lines_is_quoted_on_one_line() -> None:
    diag = _refused_at_the_reference(_ACROSS_LINES, "@Option<Nat>.result")
    assert diag.description == (
        "@Option<Nat>.result does not refer to the result of 'f', which "
        "returns Option< Int>: its result is @Option< Int>.result.")
    repaired = _ACROSS_LINES.replace("@Option<Nat>.result",
                                     _fixed_reference(diag))
    assert pipeline.check(repaired).diagnostics == ()


def test_a_check_without_source_text_names_the_keys() -> None:
    # `typecheck` takes the source text as an option.  Without it there is
    # no spelling to quote, so the message names what the rule compares.
    source = _PRE + _ISSUE.format(ref="@Int.result").replace(
        "-> @Int)", "-> @Cnt)")
    (diag,) = typecheck(pipeline.parse(source).program)
    assert diag.error_code == "E163"
    assert diag.description == (
        "@Int.result does not refer to the result of 'f', which returns "
        "Int: its result is @Cnt.result.")
    assert diag.fix == "Write @Cnt.result."


_SECOND_OPERAND = """public fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.0 == @Nat.result)
  effects(pure)
{
  @Int.0
}
"""


def test_mutant_the_report_is_at_the_reference_not_the_clause() -> None:
    # The reference is the clause's second operand, so the clause, its
    # expression and the reference each start somewhere else.
    source = _SECOND_OPERAND
    at_reference = _place(source, "@Nat.result")
    assert at_reference not in (_place(source, "ensures("),
                                _place(source, "@Int.0 =="))
    _refused_at_the_reference(source, "@Nat.result")
