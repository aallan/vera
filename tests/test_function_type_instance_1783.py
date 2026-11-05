"""A generic instantiated at a function type is compiled and runs (#1783).

A call that instantiates a generic at a function type, `idg(f)` for
`forall<T> fn idg(@T -> @T)` and a closure `f`, passed `vera check` and
`vera verify`, and code generation refused the clone: its type arguments
are spelled by name (`fn(Int -> Int)`), and the width of a type
expression was read from the name, which no primitive, alias, data type or
container answers, so the clone's parameter or return was "unsupported"
(E600, E601) and every caller was dropped (E620).  A function value has a
representation, the closure pointer, which code generation lowers wherever
the type is written as one.  The width is now read from the typed program:
a type expression the check typed as a function type is the closure
pointer, whatever its clone spells it.

The class is every program whose clone holds a function type at a type
argument: the matrix crosses the generic's kind (a top-level declaration, a
`where` helper) with the function type (pure, arity one and two; effectful)
and the position the argument reaches in the generic (the type argument
itself, an `Array` element, an `Option` built in the generic, a user data
type's field, a `Map` value, a `State` cell, an `Exn` payload, a closure
over it), each compiled with no diagnostic and run, its output pinned.  At
the base every cell is dropped.  The negative space: the shapes no clone
reaches compile as they did, and a function type at an `Eq` constraint is
still refused at check (E613).
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/codegen/core.py",
    "vera/codegen/compilability.py",
    "vera/typed.py",
    "vera/monomorphize.py",
])


def _fn(head: str, body: str, effects: str = "pure") -> str:
    return (f"{head}\n  requires(true)\n  ensures(true)\n  effects({effects})\n"
            f"{{\n  {body}\n}}\n")


#: Each function type: its alias, a closure of it, how it is applied, and
#: what the program prints (the effectful closure prints before it returns).
_ARGS: dict[str, tuple[str, str, str, str]] = {
    "pure_arity1": (
        "fn(Int -> Int) effects(pure)",
        "fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }",
        "apply_fn(@F.0, 21)",
        "42"),
    "pure_arity2": (
        "fn(Int, Int -> Int) effects(pure)",
        "fn(@Int, @Int -> @Int) effects(pure) { @Int.1 - @Int.0 }",
        "apply_fn(@F.0, 50, 8)",
        "42"),
    "io_arity1": (
        "fn(Int -> Int) effects(<IO>)",
        'fn(@Int -> @Int) effects(<IO>) { IO.print("io\\n"); @Int.0 * 2 }',
        "apply_fn(@F.0, 21)",
        "io\n42"),
}

#: Each position: the generic's declaration (named `NAME`), and the
#: expression that passes `@F.0` through it and gives back an `@F`.
_POSITIONS: dict[str, tuple[str, str]] = {
    "type_argument": (
        _fn("forall<T> fn NAME(@T -> @T)", "@T.0"),
        "NAME(@F.0)"),
    "array_element": (
        _fn("forall<T> fn NAME(@Array<T>, @T -> @T)",
            "if array_length(@Array<T>.0) > 0 then { @Array<T>.0[0] } "
            "else { @T.0 }"),
        "NAME(array_append([], @F.0), @F.0)"),
    "option_field": (
        _fn("forall<T> fn NAME(@T -> @Option<T>)", "Some(@T.0)"),
        "match NAME(@F.0) { Some(@F) -> @F.0, None -> @F.0 }"),
    "data_field": (
        _fn("forall<T> fn NAME(@Box<T> -> @T)",
            "match @Box<T>.0 { MkBox(@T) -> @T.0 }"),
        "NAME(MkBox(@F.0))"),
    "map_value": (
        _fn("forall<V> fn NAME(@Map<String, V>, @V -> @V)",
            'match map_get(map_insert(@Map<String, V>.0, "k", @V.0), "k") '
            "{ Some(@V) -> @V.0, None -> @V.0 }"),
        "NAME(map_new(), @F.0)"),
    "state_cell": (
        _fn("forall<T> fn NAME(@T -> @T)",
            "handle[State<T>](@T = @T.0) {\n"
            "    get(@Unit) -> { resume(@T.0) },\n"
            "    put(@T) -> { resume(()) }\n"
            "  } in { get(()) }"),
        "NAME(@F.0)"),
    "exn_payload": (
        _fn("forall<T> fn NAME(@T, @T -> @T)",
            "handle[Exn<T>] {\n    throw(@T) -> { @T.0 }\n"
            "  } in { throw(@T.1) }"),
        "NAME(@F.0, @F.0)"),
    "closure_over": (
        _fn("forall<T> fn NAME(@T -> @K<T>)",
            "fn(@Int -> @T) effects(pure) { @T.0 }"),
        "apply_fn(NAME(@F.0), 0)"),
}

_KINDS = ("top_level", "where_helper")

_PRELUDE = ("private data Box<T> { MkBox(T) }\n\n"
            "type K<T> = fn(Int -> T) effects(pure);\n\n")


def _program(kind: str, arg: str, position: str) -> str:
    alias, closure, apply, _ = _ARGS[arg]
    decl, through = _POSITIONS[position]
    name = "gen" if kind == "top_level" else "helper"
    decl = decl.replace("NAME", name)
    body = (f"let @F = {closure};\n"
            f"  let @F = {through.replace('NAME', name)};\n"
            f"  IO.print(int_to_string({apply}))")
    main = _fn("public fn main(@Unit -> @Unit)", body, "<IO>")
    if kind == "top_level":
        return (f"type F = {alias};\n\n{_PRELUDE}"
                f"private {decl}\n{main}")
    helper = "\n".join(f"  {line}" if line else line
                       for line in decl.splitlines())
    return f"type F = {alias};\n\n{_PRELUDE}{main}where {{\n{helper}\n}}\n"


def _runs_clean(source: str, expected: str) -> None:
    """*source* compiles with no diagnostic, runs to completion without a
    trap, and prints *expected*."""
    compiled = pipeline.compile(source)
    codes = [d.error_code for d in compiled.result.diagnostics]
    assert not codes, codes
    ran = pipeline.run(compiled)
    assert ran.ok, ran.trap
    assert ran.stdout == expected


@pytest.mark.parametrize("position", sorted(_POSITIONS))
@pytest.mark.parametrize("arg", sorted(_ARGS))
@pytest.mark.parametrize("kind", _KINDS)
def test_a_function_typed_instance_compiles_and_runs(
    kind: str, arg: str, position: str,
) -> None:
    source = _program(kind, arg, position)
    checked = pipeline.check(source)
    assert checked.ok, [d.error_code for d in checked.errors]
    _runs_clean(source, _ARGS[arg][3])


# ---------------------------------------------------------------------
# The issue's instances, unparametrised
# ---------------------------------------------------------------------

_MLIB = """module mlib;

type IntToInt = fn(Int -> Int) effects(pure);

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn compute(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = idg(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });
  apply_fn(@IntToInt.0, 21)
}
"""

_MAIN = """import mlib(compute);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  compute(())
}
"""


def test_repro_the_issue_program_runs(tmp_path: Path) -> None:
    """The issue's two-module program: a closure literal passed to a
    module's private generic.  It printed nothing at the base: the clone
    was refused (E600) and `compute` and `main` dropped (E620)."""
    entry = pipeline.write_tree(
        tmp_path, {"mlib.vera": _MLIB, "main.vera": _MAIN})
    compiled = pipeline.compile(entry)
    assert not [d.error_code for d in compiled.result.diagnostics]
    assert pipeline.run(compiled).value == 42


def test_repro_a_prelude_generic_at_a_function_type() -> None:
    """`option_unwrap_or`, the prelude's, at `Option<F>`: its clone was
    refused (E600) as a user generic's was."""
    body = ("let @F = fn(@Int -> @Int) effects(pure) { @Int.0 * 2 };\n"
            "  let @Option<F> = Some(@F.0);\n"
            "  apply_fn(option_unwrap_or(@Option<F>.0, @F.0), 21)")
    source = ("type F = fn(Int -> Int) effects(pure);\n\n"
              + _fn("public fn main(@Unit -> @Int)", body))
    compiled = pipeline.compile(source)
    assert not [d.error_code for d in compiled.result.diagnostics]
    assert pipeline.run(compiled).value == 42


def test_repro_a_function_type_inside_a_function_type_argument() -> None:
    """A closure returning a closure, at `idg`'s `T`."""
    body = ("let @FF = idg(fn(@Int -> @F) effects(pure) "
            "{ fn(@Int -> @Int) effects(pure) { @Int.0 + 1 } });\n"
            "  apply_fn(apply_fn(@FF.0, 0), 41)")
    source = ("type F = fn(Int -> Int) effects(pure);\n"
              "type FF = fn(Int -> F) effects(pure);\n\n"
              "private " + _fn("forall<T> fn idg(@T -> @T)", "@T.0")
              + _fn("public fn main(@Unit -> @Int)", body))
    compiled = pipeline.compile(source)
    assert not [d.error_code for d in compiled.result.diagnostics]
    assert pipeline.run(compiled).value == 42


# ---------------------------------------------------------------------
# Negative space
# ---------------------------------------------------------------------

#: Shapes no clone reaches: a function type in a data type's field, a
#: `Map` value, an `array_map` result and a `State` cell, written directly.
#: Each compiled and ran at the base.
_NO_CLONE: dict[str, str] = {
    "data_field": (
        "let @Box<F> = MkBox(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });\n"
        "  match @Box<F>.0 { MkBox(@F) -> apply_fn(@F.0, 21) }"),
    "map_value": (
        'let @Map<String, F> = map_insert(map_new(), "k", '
        "fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });\n"
        '  match map_get(@Map<String, F>.0, "k") '
        "{ Some(@F) -> apply_fn(@F.0, 21), None -> 0 }"),
    "array_map": (
        "let @Array<F> = array_map([1, 2], fn(@Int -> @F) effects(pure) "
        "{ fn(@Int -> @Int) effects(pure) { @Int.0 * 21 } });\n"
        "  apply_fn(@Array<F>.0[1], 2)"),
    "state_cell": (
        "let @F = handle[State<F>](@F = fn(@Int -> @Int) effects(pure) "
        "{ @Int.0 * 2 }) {\n"
        "    get(@Unit) -> { resume(@F.0) },\n"
        "    put(@F) -> { resume(()) }\n"
        "  } in { get(()) };\n"
        "  apply_fn(@F.0, 21)"),
}


@pytest.mark.parametrize("shape", sorted(_NO_CLONE))
def test_a_function_type_no_clone_reaches_compiles_as_before(
    shape: str,
) -> None:
    source = ("type F = fn(Int -> Int) effects(pure);\n\n"
              "private data Box<T> { MkBox(T) }\n\n"
              + _fn("public fn main(@Unit -> @Int)", _NO_CLONE[shape]))
    compiled = pipeline.compile(source)
    assert not [d.error_code for d in compiled.result.diagnostics]
    assert pipeline.run(compiled).value == 42


def test_an_eq_constraint_at_a_function_type_is_still_refused() -> None:
    """A function type has no `Eq`: the instantiation is refused at check,
    at the call (E613), as at the base."""
    body = ("let @F = fn(@Int -> @Int) effects(pure) { @Int.0 * 2 };\n"
            "  same(@F.0, @F.0)")
    source = ("type F = fn(Int -> Int) effects(pure);\n\n"
              "private " + _fn("forall<T where Eq<T>> fn same(@T, @T -> @Bool)",
                               "@T.0 == @T.1")
              + _fn("public fn main(@Unit -> @Bool)", body))
    checked = pipeline.check(source)
    assert [d.error_code for d in checked.errors] == ["E613"]


def test_repro_a_run_that_prints_and_then_traps_is_not_clean() -> None:
    """The matrix's run assertion is not satisfied by output alone: a
    program that prints the expected text and then traps fails it, since
    `Ran.stdout` returns what a trapped run printed."""
    body = ('IO.print("42");\n  let @Array<Int> = [1];\n'
            "  IO.print(int_to_string(@Array<Int>.0[5]))")
    source = _fn("public fn main(@Unit -> @Unit)", body, "<IO>")
    with pytest.raises(AssertionError):
        _runs_clean(source, "42")
