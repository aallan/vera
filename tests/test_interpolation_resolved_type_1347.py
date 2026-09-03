"""#1347 — interpolation decides on the RESOLVED type, not the spelling.

`"\\(@T.0)"` accepted a binding whose type was a plain alias of an
interpolable primitive and rejected one whose type was a *refinement*
over that same primitive:

    [E148] Type '{@Float64 | ...}' cannot be automatically converted to
    String in string interpolation.

The checker tested `isinstance(part_ty, PrimitiveType)`, which a
`RefinedType` is not, while an alias had already been resolved away by
type resolution — so the two spellings of "a Float64 with a constraint
attached" disagreed.  A refinement's rendering is its base's; the
predicate says nothing about how the value prints.

Measured while writing the cells, and wider than the issue: the ALIAS
case the issue calls "OK" is only check-green.  At 6dc41d40 and at this
PR's base, `type Celsius = Float64;` + `"\\(@Celsius.0)"` compiled to

    Cannot interpolate value of unknown type — the compiler couldn't
    determine the Vera type of this expression …
    Function 'main' body contains unsupported expressions — skipped.

with `Available exports: (none)`.  Codegen's dispatch keyed on the
inferred type NAME (`Celsius`) against its own copy of the to_string
table, and never resolved the alias either.  Fixing only the checker
would have moved refinements from a loud rejection to that silent drop,
so both halves resolve through the shared alias/refinement walker
(`resolve_type_alias`) and both read ONE table.
"""
from __future__ import annotations

import pytest

from tests.checker_helpers import _check, _errors
from tests.codegen_helpers import _compile, _run_io


def _render(decls: str, binder: str, value: str) -> str:
    """A program that interpolates one binding and prints it."""
    return (
        f"{decls}"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(<IO>)\n"
        "{\n"
        f"  let {binder} = {value};\n"
        f'  IO.print("v=\\({binder}.0)");\n'
        "  0\n"
        "}\n"
    )


ALIAS_F = "type Celsius = Float64;\n\n"
REFINE_F = "type Warm = { @Float64 | @Float64.0 > 0.0 };\n\n"
REFINE_I = "type Count = { @Int | @Int.0 >= 0 };\n\n"
ALIAS_OF_REFINE = (
    "type Warm = { @Float64 | @Float64.0 > 0.0 };\n\n"
    "type Temp = Warm;\n\n"
)


class TestIssueRepro:

    def test_refinement_over_float_is_accepted_and_renders(self) -> None:
        src = _render(REFINE_F, "@Warm", "21.5")
        assert _errors(src) == [], [d.description for d in _errors(src)]
        assert _run_io(src, "main", []) == "v=21.5"

    def test_refinement_over_int_is_accepted_and_renders(self) -> None:
        src = _render(REFINE_I, "@Count", "7")
        assert _errors(src) == [], [d.description for d in _errors(src)]
        assert _run_io(src, "main", []) == "v=7"

    def test_the_alias_control_also_renders(self) -> None:
        """The issue's "OK" case, taken past `vera check`."""
        src = _render(ALIAS_F, "@Celsius", "21.5")
        assert _errors(src) == []
        assert _run_io(src, "main", []) == "v=21.5"


class TestEveryInterpolablePrimitiveThroughEverySpelling:
    """The axis the rule turns on: primitive × how the type is spelled.

    Each cell must render EXACTLY what the bare primitive renders — a
    spelling cannot change how a value prints.
    """

    @pytest.mark.parametrize(
        ("prim", "value", "expected"),
        [
            ("Int", "7", "v=7"),
            ("Nat", "7", "v=7"),
            ("Float64", "21.5", "v=21.5"),
            ("Bool", "true", "v=true"),
        ],
    )
    @pytest.mark.parametrize("spelling", ["bare", "alias", "refinement",
                                          "alias-of-refinement"])
    def test_renders_identically(
        self, prim: str, value: str, expected: str, spelling: str,
    ) -> None:
        pred = "true"
        if spelling == "bare":
            decls, binder = "", f"@{prim}"
        elif spelling == "alias":
            decls, binder = f"type A = {prim};\n\n", "@A"
        elif spelling == "refinement":
            decls = f"type A = {{ @{prim} | {pred} }};\n\n"
            binder = "@A"
        else:
            decls = (f"type B = {{ @{prim} | {pred} }};\n\n"
                     "type A = B;\n\n")
            binder = "@A"
        src = _render(decls, binder, value)
        assert _errors(src) == [], [d.description for d in _errors(src)]
        assert _run_io(src, "main", []) == expected


class TestStillRejected:
    """The rule refuses what has no rendering — in both directions."""

    def test_alias_of_an_adt(self) -> None:
        src = _render("type J = Option<Int>;\n\n", "@J", "Some(1)")
        assert any(d.error_code == "E148" for d in _check(src))

    def test_refinement_over_an_array(self) -> None:
        src = _render(
            "type NE = { @Array<Int> | array_length(@Array<Int>.0) > 0 };\n\n",
            "@NE", "[1, 2]",
        )
        assert any(d.error_code == "E148" for d in _check(src))

    def test_bare_adt(self) -> None:
        src = _render("", "@Option<Int>", "Some(1)")
        assert any(d.error_code == "E148" for d in _check(src))

    def test_a_string_refinement_is_fine(self) -> None:
        """`String` needs no conversion, refined or not."""
        src = _render(
            "type NonEmpty = { @String | string_length(@String.0) > 0 };\n\n",
            "@NonEmpty", '"hi"',
        )
        assert _errors(src) == []
        assert _run_io(src, "main", []) == "v=hi"


class TestOneTable:
    """The checker and codegen read the same to_string table (#1347).

    Two hand-maintained copies existed, the second carrying the comment
    "must match checker's map".  A second copy is what let the two sides
    disagree about what is interpolable at all.
    """

    def test_the_two_consumers_share_one_source(self) -> None:
        from vera.checker.expressions import ExpressionsMixin
        from vera.types import TO_STRING_BUILTINS
        from vera.wasm.operators import OperatorsMixin

        assert ExpressionsMixin._TO_STRING_TYPES is TO_STRING_BUILTINS
        assert OperatorsMixin._INTERP_TO_STRING is TO_STRING_BUILTINS

    def test_the_table_names_real_builtins(self) -> None:
        from vera.environment import TypeEnv
        from vera.types import TO_STRING_BUILTINS

        env = TypeEnv()
        for prim, fn in TO_STRING_BUILTINS.items():
            assert env.lookup_function(fn) is not None, (
                f"{prim} maps to {fn}, which is not a built-in"
            )


class TestCheckGreenMeansCompilable:
    """Every spelling the checker accepts must also lower."""

    @pytest.mark.parametrize(
        "decls,binder,value",
        [
            (REFINE_F, "@Warm", "21.5"),
            (REFINE_I, "@Count", "7"),
            (ALIAS_F, "@Celsius", "21.5"),
            (ALIAS_OF_REFINE, "@Temp", "21.5"),
        ],
        ids=["refined-float", "refined-int", "alias", "alias-of-refinement"],
    )
    def test_accepted_programs_keep_their_exports(
        self, decls: str, binder: str, value: str,
    ) -> None:
        src = _render(decls, binder, value)
        assert _errors(src) == []
        result = _compile(src)
        assert not [d for d in result.diagnostics if d.severity == "error"]
        assert "main" in result.exports and result.dropped_fns == {}
