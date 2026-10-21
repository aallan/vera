"""One resolver: every name resolved once (#1694, #1469; ROADMAP Stage 25).

A declaration used to be identified by its bare name wherever it was looked
up: the prelude's functions and data types, a module's declarations, the
entry file's, a generic's type parameters, a type alias and the compiler's
own generated symbols shared one string namespace per lookup.  So a
same-named declaration in another file or in the prelude captured a
reference meant for a different one, two declarations no namespace could
name together collided in the WASM symbol table, a declaration registered
before the name it used stayed unresolved, and a slot name rendered from a
type's spelling folded two types into one stack.

The ``repro`` cells are the class's instances, each the program its issue
reports, unparametrised so every pull request runs them.  Each asserts the
outcome the resolver gives: the declared declaration runs, or the program is
refused at check with the code that names its mistake.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from tests import pipeline
from vera import ast as vast
from vera.binding import (
    BUILTIN, ENTRY, PRELUDE, SYMBOL_PREFIX, DeclId, bind_program,
)
from vera.fold import walk as _walk
from vera.prelude import prelude_declarations

pytestmark = pytest.mark.matrix(decides=[
    "vera/binding.py",
    "vera/resolver.py",
    "vera/prelude.py",
    "vera/naming.py",
    "vera/checker/registration.py",
    "vera/codegen/modules.py",
])


_CONTRACT = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _fn(signature: str, body: str, *, visibility: str = "private") -> str:
    """A function declaration with the trivial contract."""
    return f"{visibility} fn {signature}\n{_CONTRACT}{{\n  {body}\n}}\n"


def _tree(tmp_path: Path, files: dict[str, str]) -> Path:
    return pipeline.write_tree(tmp_path, files)


def _codes(diagnostics: object) -> list[str | None]:
    return [d.error_code for d in diagnostics]  # type: ignore[attr-defined]


# The mechanisms still to land, each a strict xfail on the cells it flips:
# a cell that starts passing fails the run until its mark is removed.
_SLOTS = pytest.mark.xfail(strict=True, reason=(
    "#1694: a refinement in a type argument keeps its predicate in the "
    "slot name (spec 3.8.1)"))


def _refused(source: str | Path, code: str) -> None:
    """*source* is refused at check, and *code* is among its errors."""
    checked = pipeline.check(source)
    assert not checked.ok, "the program passed check"
    assert code in _codes(checked.errors), _codes(checked.errors)


# =====================================================================
# #1494 and the eq_String sighting: a user function named after a symbol
# code generation emits.
# =====================================================================

@pytest.mark.parametrize("name", ["alloc", "gc_collect"])
def test_repro_1494_runtime_helper_name(name: str) -> None:
    """A user ``alloc`` or ``gc_collect`` beside a program that allocates."""
    source = (
        _fn(f"{name}(@Int -> @Int)", "@Int.0 + 1", visibility="public") + "\n"
        + _fn("main(@Int -> @String)",
              f'string_concat(int_to_string({name}(@Int.0)), "!")',
              visibility="public"))
    assert pipeline.run(source, "main", [3]).value == "4!"


def test_repro_1494_lifted_closure_name() -> None:
    """A user ``anon_0`` beside a program that lifts a closure."""
    source = (
        _fn("anon_0(@Int -> @Int)", "@Int.0 + 1", visibility="public") + "\n"
        + _fn("main(@Int -> @Int)",
              "array_length(array_map([1, 2, 3], fn(@Int -> @Int) "
              "effects(pure) { @Int.0 + 1 })) + anon_0(@Int.0)",
              visibility="public"))
    assert pipeline.run(source, "main", [3]).value == 7


def test_repro_1694_string_equality_helper_name() -> None:
    """A user ``eq_String`` beside a ``String``-keyed ``Map`` (#1694's
    sighting from the persistent collections pull request)."""
    source = (
        _fn("eq_String(@Int -> @Int)", "@Int.0 + 1", visibility="public")
        + "\npublic fn main(@Int -> @Int)\n" + _CONTRACT + "{\n"
        "  let @Map<String, Int> = map_insert(map_new(), \"a\", 7);\n"
        "  match map_get(@Map<String, Int>.0, \"a\") {\n"
        "    Some(@Int) -> @Int.0 + eq_String(@Int.1),\n"
        "    None -> 0\n"
        "  }\n}\n")
    assert pipeline.run(source, "main", [3]).value == 11


# =====================================================================
# #1495: a user function named after a prelude function.  The prelude's
# function names are reserved (#1469), so the declaration is refused at
# check, whatever its signature.
# =====================================================================

_JSON_MAIN = (
    "public fn main(@Unit -> @Int)\n" + _CONTRACT + "{\n"
    '  match json_parse("{\\"a\\": \\"bc\\"}") {\n'
    '    Ok(@Json) -> match json_get_string(@Json.0, "a") {\n'
    "      Some(@String) -> string_length(@String.0),\n"
    "      None -> 0\n"
    "    },\n"
    "    Err(@String) -> 0 - 1\n"
    "  }\n}\n")


@pytest.mark.parametrize("declaration", [
    _fn("json_get(@Int -> @Int)", "@Int.0"),
    _fn("json_as_string(@Int -> @Int)", "@Int.0"),
    _fn("json_get(@Json, @String -> @Option<Json>)", "None"),
], ids=["json_get-other-signature", "json_as_string-other-signature",
        "json_get-prelude-signature"])
def test_repro_1495_prelude_function_name(declaration: str) -> None:
    _refused(declaration + "\n" + _JSON_MAIN, "E151")


def test_repro_1495_control_runs_the_prelude() -> None:
    """The program without the declaration: the prelude's own bodies."""
    assert pipeline.run(_JSON_MAIN, "main").value == 2


# =====================================================================
# #1496, #1560, #1600: a declaration under a prelude data type's name.
# Reserved (#1469): refused at check in the entry file and in a module,
# whatever the shape.
# =====================================================================

def test_repro_1496_entry_ordering() -> None:
    _refused(
        "public data Ordering {\n  Lt,\n  Same,\n  Gt\n}\n\n"
        + _fn("main(@Unit -> @Int)",
              "match compare(1, 2) {\n    Lt -> 1,\n    Same -> 2,\n"
              "    Gt -> 3\n  }", visibility="public"),
        "E158")


def test_repro_1496_entry_option() -> None:
    _refused(
        "public data Option<T> {\n  Nothing,\n  Just(T)\n}\n\n"
        + _fn("main(@Unit -> @Int)", "option_unwrap_or(Nothing, 5)",
              visibility="public"),
        "E158")


_MODULE_JSON = "public data Json {\n  {ctor}(Int)\n}\n"


def test_repro_1560_module_json(tmp_path: Path) -> None:
    module = (
        "module b;\n\n" + _MODULE_JSON.replace("{ctor}", "MyJ") + "\n"
        + _fn("unwrap(@Json -> @Int)",
              "match @Json.0 {\n    MyJ(@Int) -> @Int.0\n  }",
              visibility="public") + "\n"
        + _fn("val(@Int -> @Int)",
              'match json_parse("1") {\n    Ok(@Json) -> unwrap(@Json.0)'
              " + @Int.0,\n    Err(@String) -> 0\n  }",
              visibility="public"))
    entry = "import b(val);\n\n" + _fn("main(@Unit -> @Int)", "val(41)",
                                        visibility="public")
    _refused(_tree(tmp_path, {"main.vera": entry, "b.vera": module}),
             "E158")


def test_repro_1600_imported_module_json(tmp_path: Path) -> None:
    module = (
        "module mj;\n\n" + _MODULE_JSON.replace("{ctor}", "Mine") + "\n"
        + _fn("mk(@Int -> @Int)",
              "match Mine(@Int.0) {\n    Mine(@Int) -> @Int.0\n  }",
              visibility="public"))
    entry = (
        "import mj;\n\n"
        + _fn("un(@Json -> @Int)",
              "match @Json.0 {\n    Mine(@Int) -> @Int.0\n  }") + "\n"
        + _fn("main(@Unit -> @Int)", "un(Mine(4))", visibility="public"))
    _refused(_tree(tmp_path, {"main.vera": entry, "mj.vera": module}),
             "E158")


# =====================================================================
# #1498: same-named functions no namespace can name together.  Every
# declaration has its own symbol, so nothing is refused at compile.
# =====================================================================

def _lib(path: str, decls: str) -> str:
    return f"module {path};\n\n{decls}"


def test_repro_1498_selective_import(tmp_path: Path) -> None:
    files = {
        "liba.vera": _lib("liba", _fn("f(@Int -> @Int)", "@Int.0 + 100",
                                      visibility="public")),
        "libb.vera": _lib("libb", _fn("f(@Int -> @Int)", "@Int.0 + 200",
                                      visibility="public") + "\n"
                          + _fn("g(@Int -> @Int)", "f(@Int.0)",
                                visibility="public")),
        "main.vera": "import liba(f);\nimport libb(g);\n\n"
        + _fn("main(@Unit -> @Int)", "f(1) * 1000 + g(1)",
              visibility="public"),
    }
    assert pipeline.run(_tree(tmp_path, files), "main").value == 101201


def test_repro_1498_module_shadows_its_import(tmp_path: Path) -> None:
    files = {
        "deep.vera": _lib("deep", _fn("f(@Int -> @Int)", "@Int.0 + 100",
                                      visibility="public")),
        "mid.vera": "module mid;\n\nimport deep;\n\n"
        + _fn("f(@Int -> @Int)", "deep::f(@Int.0) + 10",
              visibility="public"),
        "main.vera": "import mid;\n\n"
        + _fn("main(@Unit -> @Int)", "f(1)", visibility="public"),
    }
    assert pipeline.run(_tree(tmp_path, files), "main").value == 111


def test_repro_1498_two_private_helpers(tmp_path: Path) -> None:
    def lib(path: str, add: int, public: str) -> str:
        return _lib(path, _fn("h(@Int -> @Int)", f"@Int.0 + {add}") + "\n"
                    + _fn(f"{public}(@Int -> @Int)", "h(@Int.0)",
                          visibility="public"))
    files = {
        "liba.vera": lib("liba", 100, "x"),
        "libb.vera": lib("libb", 200, "y"),
        "main.vera": "import liba(x);\nimport libb(y);\n\n"
        + _fn("main(@Unit -> @Int)", "x(1) * 1000 + y(1)",
              visibility="public"),
    }
    assert pipeline.run(_tree(tmp_path, files), "main").value == 101201


# =====================================================================
# #1519, #1548: a type name read in a namespace other than the one that
# wrote it.
# =====================================================================

def test_repro_1519_alias_named_like_the_type_argument(tmp_path: Path) -> None:
    files = {
        "gl.vera": "module gl;\n\ntype Shape = Int;\n\n"
        "public forall<T> fn idg(@T -> @T)\n" + _CONTRACT + "{\n  @T.0\n}\n\n"
        + _fn("seven(@Unit -> @Int)", "let @Shape = 7;\n  @Shape.0",
              visibility="public"),
        "main.vera": "import gl(idg);\n\n"
        "private data Shape {\n  Circle(Int),\n  Square(Int)\n}\n\n"
        + _fn("main(@Unit -> @Int)",
              "match idg(Circle(4)) {\n    Circle(@Int) -> @Int.0,\n"
              "    Square(@Int) -> @Int.0 * 10\n  }", visibility="public"),
    }
    assert pipeline.run(_tree(tmp_path, files), "main").value == 4


def _colour_tree(tmp_path: Path, alias: str, body: str, ret: str) -> Path:
    module = _lib("mb", "public data Colour {\n  Red,\n  Green\n}\n\n"
                  + _fn("favourite(@Unit -> @Colour)", "Green",
                        visibility="public"))
    entry = (f"import mb(favourite);\n\n{alias}"
             + _fn(f"main(@Unit -> @{ret})", body, visibility="public"))
    return _tree(tmp_path, {"main.vera": entry, "mb.vera": module})


@pytest.mark.parametrize("alias", ["type Colour = Int;\n\n",
                                   "type Colour = String;\n\n"],
                         ids=["Int", "String"])
def test_repro_1548_show_through_an_importer_alias(
        tmp_path: Path, alias: str) -> None:
    path = _colour_tree(tmp_path, alias, "show(favourite(()))", "String")
    assert pipeline.run(path, "main").value == "Green"


def test_repro_1548_hash_through_an_importer_alias(tmp_path: Path) -> None:
    plain = _colour_tree(tmp_path / "plain", "", "hash(favourite(()))", "Int")
    aliased = _colour_tree(tmp_path / "aliased", "type Colour = Int;\n\n",
                           "hash(favourite(()))", "Int")
    assert (pipeline.run(aliased, "main").value
            == pipeline.run(plain, "main").value)


# =====================================================================
# #1549: a user function's E602 at a line inside a prelude generic's
# span.  The diagnostic is the function's, whatever line it is on.  The
# E602 itself is #1679's (a `Map` keyed by an `Array`).
# =====================================================================

_BAD = (
    "private fn bad(@Unit -> @Int)\n" + _CONTRACT + "{\n"
    "  let @Map<Array<Int>, Int> = map_insert(map_new(), [1], 5);\n"
    "  match map_get(@Map<Array<Int>, Int>.0, [1]) {\n"
    "    Some(@Int) -> @Int.0,\n"
    "    None -> 0\n"
    "  }\n}\n")
_UNWRAP_MAIN = _fn("main(@Unit -> @Int)",
                   "option_unwrap_or(Some(1), 2) + bad(())",
                   visibility="public")


@pytest.mark.parametrize("gap", [
    pytest.param(1, id="inside-span"),
    pytest.param(16, id="outside-span"),
])
def test_repro_1549_e602_kept_at_any_line(gap: int) -> None:
    """``bad``'s E602 sits at line 14 with one blank line between the two
    functions, inside ``option_unwrap_or``'s prelude span (lines 9 to 18);
    sixteen blank lines put it at line 29, outside every span."""
    source = _UNWRAP_MAIN + "\n" * gap + _BAD
    compiled = pipeline.compile(source)
    assert "E602" in _codes(compiled.diagnostics), _codes(compiled.diagnostics)


# =====================================================================
# #1552: an alias naming an alias declared after it.
# =====================================================================

def test_repro_1552_alias_forward_reference() -> None:
    source = (
        "type A = B;\n\ntype B = Int;\n\n"
        + _fn("inc(@A -> @Int)", "@A.0 + 1") + "\n"
        + _fn("main(@Unit -> @Int)", "inc(41)", visibility="public"))
    assert pipeline.run(source, "main").value == 42


# The class: a type expression a registration pass resolves (an alias body,
# a constructor field, an operation's signature) that names an alias or a
# data type declared further down.  THE ALIAS RULE (vera.naming.alias_visible)
# admits every alias of the namespace except one on a cycle of mentions with
# the body's alias declared after it, and a data type wherever it is
# declared, so each shape gives one outcome in both declaration orders.
_ORDERED_SHAPES = {
    "alias_in_a_type_argument": (
        ("type A = Array<B>;", "type B = Int;"),
        _fn("main(@Unit -> @Int)", "let @A = [41];\n  @A.0[0] + 1",
            visibility="public")),
    "constructor_field": (
        ("private data Box { MkBox(A) }", "type A = Int;"),
        _fn("main(@Unit -> @Int)",
            "match MkBox(41) {\n    MkBox(@A) -> @A.0 + 1\n  }",
            visibility="public")),
    "removed_alias_data_name": (
        ("type M = Float;", "private data Float { MkF(Int) }"),
        _fn("main(@Unit -> @Int)",
            "let @M = MkF(41);\n  match @M.0 {\n"
            "    MkF(@Int) -> @Int.0 + 1\n  }",
            visibility="public")),
    "function_signature": (
        (_fn("inc(@A -> @Int)", "@A.0 + 1"), "type A = Int;"),
        _fn("main(@Unit -> @Int)", "inc(41)", visibility="public")),
}


@pytest.mark.parametrize("order", ["as_written", "reversed"])
@pytest.mark.parametrize("shape", sorted(_ORDERED_SHAPES))
def test_class_1552_one_outcome_in_either_order(shape: str, order: str) -> None:
    decls, main = _ORDERED_SHAPES[shape]
    ordered = decls if order == "as_written" else tuple(reversed(decls))
    source = "\n\n".join(ordered) + "\n\n" + main
    assert pipeline.run(source, "main").value == 42


_OP_SHAPES = {
    "effect_operation": (
        "effect Ask {\n  op ask(Unit -> A);\n}",
        "public fn main(@Unit -> @Int)\n" + _CONTRACT + "{\n"
        "  handle[Ask] {\n    ask(@Unit) -> { resume(41) }\n"
        "  } in {\n    ask(()) + 1\n  }\n}\n"),
    "ability_operation": (
        "ability Sz<T> {\n  op size(T -> A);\n}",
        _fn("main(@Unit -> @Int)", "size(1) + 1", visibility="public")),
}


@pytest.mark.parametrize("order", ["as_written", "reversed"])
@pytest.mark.parametrize("shape", sorted(_OP_SHAPES))
def test_class_1552_an_operation_signature_reads_a_later_alias(
        shape: str, order: str) -> None:
    """A user effect's or ability's operation is refused by code generation's
    lowering rule (E340) whatever its signature; with the alias resolved its
    type is the same in both orders, so the refusal is all there is."""
    decl, main = _OP_SHAPES[shape]
    pair = (decl, "type A = Int;")
    ordered = pair if order == "as_written" else tuple(reversed(pair))
    checked = pipeline.check("\n\n".join(ordered) + "\n\n" + main)
    assert _codes(checked.errors) == ["E340"], _codes(checked.errors)


@pytest.mark.parametrize("order", ["as_written", "reversed"])
def test_class_1552_the_verifier_reads_a_later_alias(order: str) -> None:
    """The verifier's own registration takes the rule: a parameter typed by
    an alias of a refined alias declared below it carries the refinement,
    so the postcondition is proved (Tier 1)."""
    pair = ("type A = B;", "type B = { @Int | @Int.0 > 0 };")
    ordered = pair if order == "as_written" else tuple(reversed(pair))
    source = ("\n\n".join(ordered) + "\n\n"
              "public fn pos(@A -> @Int)\n  requires(true)\n"
              "  ensures(@Int.result > 0)\n  effects(pure)\n{\n"
              "  @A.0\n}\n")
    verified = pipeline.verify(source)
    assert verified.ok, _codes(verified.errors)
    statuses = {o.kind: o.status for o in verified.obligations}
    assert statuses.get("ensures") == "verified", statuses


@pytest.mark.parametrize("order", ["as_written", "reversed"])
def test_class_1552_a_generic_alias_resolves_ahead(order: str) -> None:
    """An alias applying a parameterised alias declared below it substitutes
    the arguments as it does declared above it.  Checked, not run: a
    parameterised alias of a two-word value fails in code generation in
    either order, the find in this PR's last section."""
    from vera.checker.core import TypeChecker
    from vera.parser import parse_to_ast
    from vera.types import pretty_type

    pair = ("type P = Wrap<Int>;", "type Wrap<T> = Array<T>;")
    ordered = pair if order == "as_written" else tuple(reversed(pair))
    source = "\n\n".join(ordered) + "\n\n" + _fn(
        "main(@Unit -> @Int)", "2", visibility="public")
    checker = TypeChecker(source=source, file="<generic>")
    checker.check_program(parse_to_ast(source))
    assert not _codes([d for d in checker.errors if d.severity == "error"])
    assert pretty_type(
        checker.env.type_aliases["P"].resolved_type) == "Array<Int>"


@pytest.mark.parametrize("order", ["as_written", "reversed"])
def test_class_1552_a_long_forward_chain_resolves(order: str) -> None:
    """Resolving an alias ahead takes no Python frame per hop: a 400-link
    chain declared in either direction checks and runs."""
    links = [f"type A{i} = A{i + 1};" for i in range(400)] + ["type A400 = Int;"]
    ordered = links if order == "as_written" else list(reversed(links))
    source = ("\n".join(ordered) + "\n\n"
              + _fn("main(@Unit -> @Int)", "let @A0 = 41;\n  @A0.0 + 1",
                    visibility="public"))
    assert pipeline.run(source, "main").value == 42


@pytest.mark.parametrize("order", ["as_written", "reversed"])
@pytest.mark.parametrize("shape, expected", [
    pytest.param(("type F = fn(F -> Int) effects(pure);",),
                 {"F": "fn(F -> Int) effects(pure)"}, id="self_reference"),
    pytest.param(("type F = fn(G -> Int) effects(pure);",
                  "type G = fn(F -> Int) effects(pure);"),
                 {"F": "fn(G -> Int) effects(pure)",
                  "G": "fn(fn(G -> Int) effects(pure) -> Int) effects(pure)"},
                 id="mutual_as_written"),
])
def test_class_1552_inside_a_cycle_source_order_holds(
        shape: tuple[str, ...], expected: dict[str, str], order: str) -> None:
    """Negative space: aliases on a cycle of mentions through a function type
    (no E132, which is structural) resolve as at the base, the later one
    opaque inside the earlier one's body.  The reversed order of the mutual
    pair swaps which one is earlier, so its expectation swaps too."""
    from vera.checker.core import TypeChecker
    from vera.parser import parse_to_ast
    from vera.types import pretty_type

    ordered = shape if order == "as_written" else tuple(reversed(shape))
    if order == "reversed" and len(shape) == 2:
        expected = {"G": "fn(F -> Int) effects(pure)",
                    "F": "fn(fn(F -> Int) effects(pure) -> Int) effects(pure)"}
    source = "\n\n".join(ordered) + "\n\n" + _fn(
        "main(@Unit -> @Int)", "2", visibility="public")
    checker = TypeChecker(source=source, file="<cycle>")
    checker.check_program(parse_to_ast(source))
    assert not _codes([d for d in checker.errors if d.severity == "error"])
    aliases = checker.env.type_aliases
    assert {name: pretty_type(aliases[name].resolved_type)
            for name in expected} == expected


# =====================================================================
# #1553, #1556: a built-in type's name at a binder other than `data`.
# =====================================================================

@pytest.mark.parametrize("alias, body", [
    ("type Decimal = Int;", "show(decimal_from_int(5))"),
    ("type Array<T> = Int;", "show([1, 2])"),
], ids=["Decimal", "Array"])
def test_repro_1553_alias_takes_a_builtin_type_name(
        alias: str, body: str) -> None:
    _refused(alias + "\n\n" + _fn("main(@Unit -> @String)", body,
                                  visibility="public"), "E158")


def test_repro_1556_type_parameter_takes_a_builtin_type_name() -> None:
    source = (
        "private forall<Array> fn idd(@Array -> @Array)\n" + _CONTRACT
        + "{\n  @Array.0\n}\n\n"
        + _fn("main(@Unit -> @Int)", "array_length(idd([1, 2, 3]))",
              visibility="public"))
    _refused(source, "E158")


# =====================================================================
# #1581: a module generic's call to its `where` helper, in an importer.
# =====================================================================

def test_repro_1581_where_helper_beside_a_same_named_generic(
        tmp_path: Path) -> None:
    module = (
        "module m;\n\n"
        "private forall<T> fn pick(@T -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result == 1)\n  effects(pure)\n{\n  go(@T.0)\n}\n"
        "where {\n  fn go(@T -> @Int)\n    requires(true)\n"
        "    ensures(@Int.result == 1)\n    effects(pure)\n  {\n    1\n  }\n"
        "}\n\n"
        "private forall<T> fn go(@T -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result == 2)\n  effects(pure)\n{\n  2\n}\n\n"
        "public fn one(@Unit -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result == 1)\n  effects(pure)\n{\n  pick(true)\n}\n")
    entry = "import m(one);\n\n" + _fn("main(@Unit -> @Int)", "one(())",
                                        visibility="public")
    path = _tree(tmp_path, {"main.vera": entry, "m.vera": module})
    assert pipeline.run(path, "main").value == 1


# =====================================================================
# #1674: a refinement in a type argument names its own slot stack.
# =====================================================================

@_SLOTS
def test_repro_1674_refinements_in_a_type_argument_are_two_stacks() -> None:
    """The reference written with ``> 0`` reaches the parameter declared
    ``> 0``: parameter 1, whose array has one element."""
    source = (
        "public fn f(@Array<{ @Int | @Int.0 > 0 }>, "
        "@Array<{ @Int | @Int.0 < 0 }> -> @Nat)\n" + _CONTRACT
        + "{\n  array_length(@Array<{ @Int | @Int.0 > 0 }>.0)\n}\n\n"
        + _fn("main(@Unit -> @Nat)", "f([1], [0 - 1, 0 - 2])",
              visibility="public"))
    assert pipeline.run(source, "main").value == 1


@_SLOTS
def test_repro_1674_result_reference_predicate() -> None:
    """A result reference whose refinement the result's type lacks."""
    source = (
        "type PosInt = { @Int | @Int.0 > 0 };\n\n"
        "public fn f(@Int -> @Option<PosInt>)\n  requires(true)\n"
        "  ensures(@Option<{ @Int | @Int.0 > 99 }>.result == None)\n"
        "  effects(pure)\n{\n  None\n}\n")
    _refused(source, "E163")


# =====================================================================
# The resolver pass (vera/binding.py): every declaration's DeclId, every
# call's binding.  Unit cells over the rule order, each the shape one
# instance or one negative-space neighbour has.
# =====================================================================

def _bound(tmp_path: Path, files: dict[str, str]):
    """Check the tree, then bind it with the prelude it compiles with."""
    checked = pipeline.check(_tree(tmp_path, files))
    assert checked.ok, _codes(checked.errors)
    modules = checked.resolved or []
    prelude, _source = prelude_declarations(
        checked.program, {m.path: m.program for m in modules})
    return checked.program, modules, bind_program(
        checked.program, modules, prelude)


def _calls_in(decl: vast.FnDecl, name: str) -> list[vast.Node]:
    return [n for n in _walk(decl.body)
            if isinstance(n, (vast.FnCall, vast.ModuleCall)) and n.name == name]


def _decl(program: vast.Program, name: str) -> vast.FnDecl:
    return next(t.decl for t in program.declarations
                if isinstance(t.decl, vast.FnDecl) and t.decl.name == name)


def test_binding_link_names_are_unique_and_prefixed() -> None:
    idents = [DeclId(ENTRY, "f"), DeclId(("liba",), "f"),
              DeclId(("a", "b"), "f"), DeclId(PRELUDE, "option_map"),
              DeclId(ENTRY, "h", ("f",)), DeclId(("liba",), "h", ("f",))]
    links = [i.link_name for i in idents]
    assert links == ["f", "mod$liba$f", "mod$a$b$f", "option_map",
                     "f$where$h", "mod$liba$f$where$h"]
    assert len(set(links)) == len(links)
    assert all(i.symbol == SYMBOL_PREFIX + i.link_name for i in idents)


def test_binding_selective_import_and_the_other_modules_own_call(
        tmp_path: Path) -> None:
    """#1498 shape 1: the entry's `f` is liba's; libb's `g` calls libb's."""
    files = {
        "liba.vera": _lib("liba", _fn("f(@Int -> @Int)", "@Int.0 + 100",
                                      visibility="public")),
        "libb.vera": _lib("libb", _fn("f(@Int -> @Int)", "@Int.0 + 200",
                                      visibility="public") + "\n"
                          + _fn("g(@Int -> @Int)", "f(@Int.0)",
                                visibility="public")),
        "main.vera": "import liba(f);\nimport libb(g);\n\n"
        + _fn("main(@Unit -> @Int)", "f(1) * 1000 + g(1)",
              visibility="public"),
    }
    program, modules, binding = _bound(tmp_path, files)
    main = _decl(program, "main")
    assert binding.of(_calls_in(main, "f")[0]) == DeclId(("liba",), "f")
    assert binding.of(_calls_in(main, "g")[0]) == DeclId(("libb",), "g")
    libb = next(m for m in modules if m.path == ("libb",)).program
    assert (binding.of(_calls_in(_decl(libb, "g"), "f")[0])
            == DeclId(("libb",), "f"))


def test_binding_where_helper_beats_a_same_named_top_level(
        tmp_path: Path) -> None:
    """#1581's shape, in one file: `pick`'s `go` is its helper."""
    source = (
        "private forall<T> fn pick(@T -> @Int)\n" + _CONTRACT
        + "{\n  go(@T.0)\n}\nwhere {\n  fn go(@T -> @Int)\n"
        "    requires(true)\n    ensures(true)\n    effects(pure)\n"
        "  {\n    1\n  }\n}\n\n"
        "private forall<T> fn go(@T -> @Int)\n" + _CONTRACT + "{\n  2\n}\n\n"
        + _fn("main(@Unit -> @Int)", "pick(true) + go(true)",
              visibility="public"))
    program, _modules, binding = _bound(tmp_path, {"main.vera": source})
    pick = _decl(program, "pick")
    assert binding.of(_calls_in(pick, "go")[0]) == DeclId(ENTRY, "go", ("pick",))
    main = _decl(program, "main")
    assert binding.of(_calls_in(main, "go")[0]) == DeclId(ENTRY, "go")


def test_binding_module_shadows_its_import(tmp_path: Path) -> None:
    """#1498 shape 2: `mid`'s own `f` and its `deep::f` are two decls."""
    files = {
        "deep.vera": _lib("deep", _fn("f(@Int -> @Int)", "@Int.0 + 100",
                                      visibility="public")),
        "mid.vera": "module mid;\n\nimport deep;\n\n"
        + _fn("f(@Int -> @Int)", "deep::f(@Int.0) + 10",
              visibility="public"),
        "main.vera": "import mid;\n\n"
        + _fn("main(@Unit -> @Int)", "f(1)", visibility="public"),
    }
    program, modules, binding = _bound(tmp_path, files)
    assert (binding.of(_calls_in(_decl(program, "main"), "f")[0])
            == DeclId(("mid",), "f"))
    mid = next(m for m in modules if m.path == ("mid",)).program
    assert (binding.of(_calls_in(_decl(mid, "f"), "f")[0])
            == DeclId(("deep",), "f"))


def test_binding_prelude_bodies_bind_the_prelude(tmp_path: Path) -> None:
    """#1495: `json_get_string`'s `json_get` is the prelude's own, and a
    built-in stays a built-in."""
    program, _modules, binding = _bound(tmp_path, {"main.vera": _JSON_MAIN})
    main = _decl(program, "main")
    assert (binding.of(_calls_in(main, "json_get_string")[0])
            == DeclId(PRELUDE, "json_get_string"))
    assert binding.of(_calls_in(main, "json_parse")[0]) == DeclId(
        BUILTIN, "json_parse")
    getter = binding.decls[DeclId(PRELUDE, "json_get_string")]
    assert (binding.of(_calls_in(getter, "json_get")[0])
            == DeclId(PRELUDE, "json_get"))


def test_binding_transitive_module_is_not_visible(tmp_path: Path) -> None:
    """A module reached only through another's imports binds nothing bare
    in the entry (spec §8.6.4)."""
    files = {
        "base.vera": _lib("base", _fn("b(@Int -> @Int)", "@Int.0",
                                      visibility="public")),
        "mid.vera": "module mid;\n\nimport base;\n\n"
        + _fn("m(@Int -> @Int)", "b(@Int.0)", visibility="public"),
        "main.vera": "import mid;\n\n"
        + _fn("main(@Unit -> @Int)", "m(1)", visibility="public"),
    }
    program, modules, binding = _bound(tmp_path, files)
    mid = next(m for m in modules if m.path == ("mid",)).program
    assert (binding.of(_calls_in(_decl(mid, "m"), "b")[0])
            == DeclId(("base",), "b"))
    assert DeclId(("base",), "b") in binding.decls


# =====================================================================
# The reservation's fixes, applied literally: the replacement name each
# diagnostic's `fix` suggests clears it.
# =====================================================================

def _suggested(fix: str) -> str:
    """The example name a fix text gives, as `(for example 'NAME')`."""
    match = re.search(r"for example '([A-Za-z_][A-Za-z0-9_]*)'", fix)
    assert match is not None, fix
    return match.group(1)


def _apply_fix(source: str, code: str, name: str) -> str:
    checked = pipeline.check(source)
    found = [d for d in checked.errors if d.error_code == code]
    assert found, _codes(checked.errors)
    return re.sub(rf"\b{name}\b", _suggested(found[0].fix), source)


def test_e151_fix_for_a_prelude_function_name_clears_it() -> None:
    source = (_fn("json_get(@Int -> @Int)", "@Int.0 + 1") + "\n"
              + _fn("main(@Unit -> @Int)", "json_get(41)",
                    visibility="public"))
    fixed = _apply_fix(source, "E151", "json_get")
    checked = pipeline.check(fixed)
    assert checked.ok and "E151" not in _codes(checked.diagnostics)
    assert pipeline.run(fixed, "main").value == 42


@pytest.mark.parametrize("source, name", [
    ("public data Option<T> {\n  Nothing,\n  Just(T)\n}\n\n"
     + _fn("main(@Unit -> @Int)",
           "match Just(4) {\n    Just(@Int) -> @Int.0,\n    Nothing -> 0\n  }",
           visibility="public"), "Option"),
    ("type Decimal = Int;\n\n"
     + _fn("main(@Unit -> @Int)", "let @Decimal = 4;\n  @Decimal.0",
           visibility="public"), "Decimal"),
    ("private forall<Array> fn idd(@Array -> @Array)\n" + _CONTRACT
     + "{\n  @Array.0\n}\n\n"
     + _fn("main(@Unit -> @Int)", "idd(4)", visibility="public"), "Array"),
], ids=["data", "alias", "type-parameter"])
def test_e158_fix_for_a_reserved_type_name_clears_it(
        source: str, name: str) -> None:
    fixed = _apply_fix(source, "E158", name)
    checked = pipeline.check(fixed)
    assert checked.ok and "E158" not in _codes(checked.diagnostics)
    assert pipeline.run(fixed, "main").value == 4


# =====================================================================
# E609's retirement (#1694): two modules' same-named `data` are two types.
# A value of one meeting the other is an ordinary mismatch at check, whose
# message names both owners, and whose fix, applied as written, compiles.
# =====================================================================

_MEET = {
    "liba.vera": _lib("liba", "public data Shape {\n  Cr(Int),\n  Sq(Int)\n}\n\n"
                      + _fn("aone(@Int -> @Shape)", "Sq(@Int.0)",
                            visibility="public")),
    "libb.vera": _lib("libb", "public data Shape {\n  Sq(Int),\n  Cr(Int)\n}\n\n"
                      + _fn("bone(@Shape -> @Int)",
                            "match @Shape.0 {\n    Sq(@Int) -> @Int.0 + 1,\n"
                            "    Cr(@Int) -> 100\n  }", visibility="public")),
    "main.vera": "import liba(aone);\nimport libb(bone);\n\n"
    + _fn("main(@Unit -> @Int)", "bone(aone(6))", visibility="public"),
}


def test_repro_1694_a_meeting_of_two_owners_types_is_refused(
        tmp_path: Path) -> None:
    checked = pipeline.check(_tree(tmp_path, _MEET))
    found = [d for d in checked.errors if d.error_code == "E202"]
    assert found, _codes(checked.errors)
    assert "liba.Shape" in found[0].description
    assert "libb.Shape" in found[0].description
    assert "mod$" not in found[0].description + found[0].fix


def test_e202_fix_for_a_meeting_of_two_owners_types_clears_it(
        tmp_path: Path) -> None:
    main = _tree(tmp_path, _MEET)
    checked = pipeline.check(main)
    (fix,) = [d.fix for d in checked.errors if d.error_code == "E202"]
    line = re.search(r"'(import libb\([^)]*\);)'", fix)
    ctor = re.search(r"constructors: ([A-Z][A-Za-z0-9_]*)\(\.\.\.\)", fix)
    assert line is not None and ctor is not None, fix
    source = main.read_text(encoding="utf-8")
    source = source.replace("import libb(bone);", line.group(1))
    source = source.replace("aone(6)", f"{ctor.group(1)}(6)")
    main.write_text(source, encoding="utf-8")
    fixed = pipeline.check(main)
    assert fixed.ok and "E202" not in _codes(fixed.diagnostics), (
        _codes(fixed.errors))
    assert pipeline.run(main, "main").value == 7
