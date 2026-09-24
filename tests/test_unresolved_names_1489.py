"""Every type and effect name resolves, or check refuses it (#1489, #1506).

The reported programs and the rules around them, pinned one by one; the
matrix over every grammar position is ``tests/test_check_implies_compile.py``.

* **E136** — a type name nothing in scope declares.  The checker's last
  resort used to make an opaque type of any such name and report nothing,
  so a misspelt type was check-green and verify-green, and code generation
  dropped each function that needed its layout.  A FORWARD reference — a
  signature naming a declaration further down the file — is not an unknown
  name, and stays legal.  The instruction names the cause when there is a
  better one than "declare it": another import's clash, an import that did
  not resolve, a module that declares the type but is not imported for it.
* **E338** — an effect-row name that denotes no effect.  A qualified
  reference (``<IO.Write>``) is always one: no effect has a qualified name,
  and code generation dropped such a function with no diagnostic at all.
* **The module registration sees its imports.**  The checker registered
  each module's signatures with none of the module's own imports in scope;
  the placeholder usually spelled the imported type exactly, but a module
  importing a user ``data Decimal<T>`` registered its ``@Decimal<Int>``
  parameter as the BUILT-IN ``Decimal``, and the importer refused a valid
  call.
* **E179** (#1506) — a quantifier predicate that is not a function of the
  index to ``Bool``.  Nothing checked its signature, and code generation
  stopped with E699 on a refined parameter or a wrong arity and emitted an
  unloadable module for a ``Bool`` parameter or an ``Int`` result.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vera import ast, naming
from vera.checker.core import TypeChecker
from vera.parser import parse_to_ast

from tests.test_check_implies_compile import (
    Outcome,
    locate,
    pipeline,
    run_main,
)

_CONTRACT = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _check(tmp_path: Path, source: str) -> Outcome:
    return pipeline(tmp_path, {"main.vera": source})


def _codes_at(outcome: Outcome, code: str) -> list[tuple[int, int]]:
    return sorted(
        (d.location.line, d.location.column)
        for d in outcome.check_errors if d.error_code == code
    )


def _diag(outcome: Outcome, code: str):
    found = [d for d in outcome.check_errors if d.error_code == code]
    assert found, outcome.describe()
    return found[0]


# =====================================================================
# The programs the issue reports
# =====================================================================

_F = """\
public fn f(@Nonexistent -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  42
}
"""

_H = """\
private fn h(@Option<Nonexistent> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Nonexistent>.0 {
    None -> 1,
    Some(@Nonexistent) -> 2
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  h(None)
}
"""


class TestTheReportedPrograms:
    """#1489's reproductions, each refused where the name is written."""

    def test_an_unknown_parameter_type(self, tmp_path: Path) -> None:
        out = _check(tmp_path, _F)
        assert _codes_at(out, "E136") == [locate(_F, "Nonexistent")]

    def test_every_occurrence_is_reported(self, tmp_path: Path) -> None:
        """In the parameter, the slot reference and the nested binder."""
        out = _check(tmp_path, _H)
        assert _codes_at(out, "E136") == [
            locate(_H, "Nonexistent", 0),
            locate(_H, "Nonexistent", 1),
            locate(_H, "Nonexistent", 2),
        ]

    def test_an_unknown_constructor_field(self, tmp_path: Path) -> None:
        src = (
            "private data Box {\n  MkBox(Nonexistent),\n  Empty\n}\n\n"
            "public fn main(@Unit -> @Int)\n" + _CONTRACT + "{\n"
            "  match Empty {\n    MkBox(@Nonexistent) -> 1,\n"
            "    Empty -> 2\n  }\n}\n"
        )
        out = _check(tmp_path, src)
        assert locate(src, "Nonexistent") in _codes_at(out, "E136")

    def test_a_type_the_file_did_not_import(self, tmp_path: Path) -> None:
        """A value can reach a file through a function; its type's NAME
        needs an import of its own, and the fix says which."""
        main = (
            "import ma(pick);\n\npublic fn main(@Unit -> @Int)\n"
            + _CONTRACT + "{\n  let @Colour = pick(1);\n  1\n}\n"
        )
        out = pipeline(tmp_path, {
            "mb.vera": "module mb;\n\npublic data Colour {\n  Red,\n"
                       "  Green\n}\n",
            "ma.vera": "module ma;\n\nimport mb(Colour);\n\n"
                       "public fn pick(@Int -> @Colour)\n" + _CONTRACT
                       + "{\n  Red\n}\n",
            "main.vera": main,
        })
        assert _codes_at(out, "E136") == [locate(main, "Colour")]
        assert "import mb(Colour);" in _diag(out, "E136").fix

    def test_an_unknown_effect_in_a_row(self, tmp_path: Path) -> None:
        src = _F.replace("@Nonexistent", "@Int").replace(
            "effects(pure)", "effects(<Nonexistent>)")
        out = _check(tmp_path, src)
        assert _codes_at(out, "E338") == [locate(src, "Nonexistent")]

    def test_a_qualified_effect_in_a_row(self, tmp_path: Path) -> None:
        """No effect has a qualified name; the function used to vanish
        from the compiled module without any diagnostic."""
        src = _F.replace("@Nonexistent", "@Int").replace(
            "effects(pure)", "effects(<IO.Write>)")
        out = _check(tmp_path, src)
        assert _codes_at(out, "E338") == [locate(src, "IO.Write")]
        assert "effects(<Write>)" in _diag(out, "E338").fix

    def test_the_known_names_stay_legal(self, tmp_path: Path) -> None:
        """Primitives, containers, the prelude's types, Decimal, Future,
        type parameters and effect row variables all resolve."""
        src = (
            "public forall<T, E> fn f(@T, @Array<Option<Result<Int, "
            "String>>>, @Map<String, Set<Int>>, @Decimal, @Future<Int>, "
            "@Ordering, @Json -> @Int)\n  requires(true)\n  ensures(true)\n"
            "  effects(<IO, State<Nat>, E>)\n{\n  1\n}\n"
        )
        out = _check(tmp_path, src)
        assert not {"E136", "E338"} & {
            d.error_code for d in out.check_errors}, out.describe()


# =====================================================================
# Forward references are not unknown names
# =====================================================================

_FORWARD = """\
public fn f(@Colour -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Colour.0 {
    Red -> 1,
    Green -> 2
  }
}

public fn g(@Cnt -> @Cnt)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Cnt.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(Red) + g(3)
}

public data Colour {
  Red,
  Green
}

type Cnt = Int;
"""


class TestForwardReferencesStayLegal:
    """A name declared further down the file resolves at registration."""

    def test_a_data_type_and_an_alias_declared_below(
        self, tmp_path: Path,
    ) -> None:
        out = _check(tmp_path, _FORWARD)
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", 4)

    def test_recursive_and_mutually_recursive_data(
        self, tmp_path: Path,
    ) -> None:
        src = (
            "private data Tree {\n  Leaf,\n  Node(Forest)\n}\n\n"
            "private data Forest {\n  Nil,\n  Cons(Tree, Forest)\n}\n\n"
            "type Wood = Forest;\n\n"
            "public fn main(@Unit -> @Int)\n" + _CONTRACT
            + "{\n  match Cons(Leaf, Nil) {\n    Nil -> 0,\n"
            "    Cons(@Tree, @Forest) -> 1\n  }\n}\n"
        )
        out = _check(tmp_path, src)
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", 1)

    def test_an_effect_declared_below(self, tmp_path: Path) -> None:
        """The row's twin: E338 is not a forward reference either."""
        src = (
            "public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
            "  effects(<Tally>)\n{\n  @Int.0\n}\n\n"
            "effect Tally {\n  op tally(Int -> Unit);\n}\n"
        )
        out = _check(tmp_path, src)
        assert "E338" not in {d.error_code for d in out.check_errors}, (
            out.describe())


# =====================================================================
# The instruction names the cause
# =====================================================================

_MB_PRIVATE = (
    "module mb;\n\nprivate data Secret {\n  Hidden\n}\n\n"
    "public fn open(@Int -> @Int)\n" + _CONTRACT + "{\n  @Int.0\n}\n"
)


def _uses(type_name: str, imports: str) -> str:
    return (
        f"{imports}\npublic fn f(@{type_name} -> @Int)\n" + _CONTRACT
        + "{\n  1\n}\n"
    )


class TestTheInstructionNamesTheCause:
    """E136's fix says what to do about THIS name (DESIGN principle 1)."""

    @pytest.mark.parametrize("imports", (
        "import nosuch(Thing);\n", "import nosuch;\n",
    ))
    def test_an_import_that_did_not_resolve(
        self, imports: str, tmp_path: Path,
    ) -> None:
        out = _check(tmp_path, _uses("Thing", imports))
        assert "E012" in {d.error_code for d in out.check_errors}
        diag = _diag(out, "E136")
        assert "did not resolve" in diag.rationale, diag.rationale
        assert "Fix the import of 'nosuch'" in diag.fix, diag.fix

    def test_a_private_type_of_a_module(self, tmp_path: Path) -> None:
        out = pipeline(tmp_path, {
            "mb.vera": _MB_PRIVATE,
            "main.vera": _uses("Secret", "import mb(open);\n"),
        })
        diag = _diag(out, "E136")
        assert "private" in diag.rationale and "public" in diag.fix

    def test_an_import_list_naming_no_such_type(
        self, tmp_path: Path,
    ) -> None:
        out = pipeline(tmp_path, {
            "mb.vera": _MB_PRIVATE,
            "main.vera": _uses("Nope", "import mb(open, Nope);\n"),
        })
        assert "import mb(...)" in _diag(out, "E136").rationale

    def test_a_name_two_imports_supply(self, tmp_path: Path) -> None:
        shape = "public data Shape {\n  {C}\n}\n"
        out = pipeline(tmp_path, {
            "ma.vera": "module ma;\n\n" + shape.replace("{C}", "Sq(Int)"),
            "mb.vera": "module mb;\n\n" + shape.replace("{C}", "Cr(Bool)"),
            "main.vera": _uses("Shape", "import ma(Shape);\n"
                                        "import mb(Shape);\n"),
        })
        assert "E156" in {d.error_code for d in out.check_errors}
        assert "E156" in _diag(out, "E136").fix

    def test_the_function_slot_head(self, tmp_path: Path) -> None:
        """`@Fn.0` references a function-typed slot, which invites `@Fn`
        where a type is written; the fix spells the function type."""
        src = (
            "public fn main(@Unit -> @Int)\n" + _CONTRACT + "{\n"
            "  match Some(fn(@Int -> @Int) effects(pure) { @Int.0 }) {\n"
            "    Some(@Fn) -> 5,\n    None -> 0\n  }\n}\n"
        )
        out = _check(tmp_path, src)
        assert _codes_at(out, "E136") == [locate(src, "Fn)")]
        assert "@fn(Int -> Int) effects(pure)" in _diag(out, "E136").fix

    def test_another_modules_alias(self, tmp_path: Path) -> None:
        """An alias is module-local (§8.4.1): the fix says to declare a
        copy, quoting the module's own definition, and never to import it —
        and the copy it quotes is accepted."""
        mb = ("module mb;\n\ntype Score = Int;\n\n"
              "public fn s(@Int -> @Score)\n" + _CONTRACT
              + "{\n  @Int.0 + 1\n}\n")
        body = ("public fn main(@Unit -> @Int)\n" + _CONTRACT
                + "{\n  let @Score = s(1);\n  @Score.0\n}\n")
        out = pipeline(tmp_path / "bare", {
            "mb.vera": mb, "main.vera": "import mb(s);\n\n" + body,
        })
        diag = _diag(out, "E136")
        assert "module-local" in diag.rationale, diag.rationale
        assert "'type Score = Int;'" in diag.fix, diag.fix
        assert "import" not in diag.fix, diag.fix
        fixed = pipeline(tmp_path / "fixed", {
            "mb.vera": mb,
            "main.vera": "import mb(s);\n\ntype Score = Int;\n\n" + body,
        })
        assert fixed.accepted and fixed.compiles_clean, fixed.describe()
        assert run_main(fixed) == ("ok", 2)

    def test_another_modules_effect(self, tmp_path: Path) -> None:
        """Effects are module-local: the fix says to declare a copy."""
        out = pipeline(tmp_path, {
            "mb.vera": "module mb;\n\neffect Tally {\n  op tally(Int -> "
                       "Unit);\n}\n\npublic fn open(@Int -> @Int)\n"
                       + _CONTRACT + "{\n  @Int.0\n}\n",
            "main.vera": "import mb(open);\n\npublic fn f(@Int -> @Int)\n"
                         "  requires(true)\n  ensures(true)\n"
                         "  effects(<Tally>)\n{\n  @Int.0\n}\n",
        })
        assert "module-local" in _diag(out, "E338").fix


# =====================================================================
# One report, and the same type after it
# =====================================================================

class TestTheReportItself:
    """A signature type is resolved twice (registration and check) — one
    report; and the type after the report is the renderer's."""

    def test_one_report_per_occurrence(self, tmp_path: Path) -> None:
        out = _check(tmp_path, _F)
        assert len([d for d in out.check_errors
                    if d.error_code == "E136"]) == 1

    def test_the_type_after_the_report_renders_as_the_renderer_does(
        self,
    ) -> None:
        """The checker keeps the opaque placeholder after reporting, so a
        refused program still renders byte-identically on both sides."""
        src = "public fn f(@Option<Qzt> -> @Int)\n" + _CONTRACT + "{\n  1\n}\n"
        program = parse_to_ast(src)
        checker = TypeChecker(source=src)
        checker.check_program(program)
        decl = program.declarations[0].decl
        assert isinstance(decl, ast.FnDecl)
        resolved = checker._resolve_type(decl.params[0])
        env = checker._naming_env()
        assert naming.resolve_type_expr(decl.params[0], env) == resolved
        assert naming.slot_name(decl.params[0], env) == "Option<Qzt>"


# =====================================================================
# A module's registration sees the module's imports
# =====================================================================

class TestModuleRegistrationSeesItsImports:
    """The Decimal case: a placeholder that did NOT spell the import."""

    def test_an_imported_user_decimal_keeps_its_arguments(
        self, tmp_path: Path,
    ) -> None:
        out = pipeline(tmp_path, {
            "mb.vera": "module mb;\n\npublic data Decimal<T> {\n  Dec(T)\n}\n",
            "ma.vera": "module ma;\n\nimport mb(Decimal);\n\n"
                       "public fn unwrap(@Decimal<Int> -> @Int)\n" + _CONTRACT
                       + "{\n  match @Decimal<Int>.0 {\n"
                       "    Dec(@Int) -> @Int.0\n  }\n}\n",
            "main.vera": "import ma(unwrap);\nimport mb(Decimal);\n\n"
                         "public fn main(@Unit -> @Int)\n" + _CONTRACT
                         + "{\n  unwrap(Dec(41)) + 1\n}\n",
        })
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", 42)


# =====================================================================
# #1506: the quantifier predicate is a function of the index to Bool
# =====================================================================

def _quantifier(predicate: str, binder: str = "@Nat",
                prelude: str = "", form: str = "forall") -> str:
    return (
        prelude + "public fn main(@Unit -> @Int)\n" + _CONTRACT
        + f"{{\n  if {form}({binder}, 5, {predicate}) then {{ 1 }} "
        f"else {{ 0 }}\n}}\n"
    )


_SMALL = "type Small = { @Nat | @Nat.0 < 2 };\ntype Idx = Nat;\n\n"


def eval_index(expr: str, n: int) -> bool:
    """Evaluate a test's small predicate over the index *n* in Python."""
    # Test-authored comparisons over one integer, with no names: evaluated
    # with no builtins in scope.
    return bool(eval(
        expr.replace("@Nat.0", str(n)).replace("true", "True")
        .replace("==>", "<="), {"__builtins__": {}}, {}))


class TestQuantifierPredicate:
    """#1506: every predicate shape code generation cannot lower is E179,
    and every shape it can lower still runs."""

    @pytest.mark.parametrize("form", ("forall", "exists"))
    @pytest.mark.parametrize(("predicate", "why"), (
        ("fn(@{ @Nat | @Nat.0 < 100 } -> @Bool) effects(pure) { true }",
         "refinement"),
        ("fn(@Small -> @Bool) effects(pure) { @Small.0 < 2 }", "refinement"),
        ("fn(@Bool -> @Bool) effects(pure) { @Bool.0 }", "Bool"),
        ("fn(@Nat -> @Int) effects(pure) { 5 }", "returns Int"),
        ("fn(@Nat, @Nat -> @Bool) effects(pure) { true }", "2 parameters"),
        ("fn(-> @Bool) effects(pure) { true }", "0 parameters"),
    ))
    def test_refused(self, predicate: str, why: str, form: str,
                     tmp_path: Path) -> None:
        out = _check(tmp_path, _quantifier(predicate, prelude=_SMALL,
                                           form=form))
        diag = _diag(out, "E179")
        assert why in diag.description, diag.description

    @pytest.mark.parametrize(("predicate", "value"), (
        ("fn(@Nat -> @Bool) effects(pure) { @Nat.0 < 5 }", 1),
        ("fn(@Int -> @Bool) effects(pure) { @Int.0 < 4 }", 0),
        ("fn(@Idx -> @Bool) effects(pure) { @Idx.0 < 5 }", 1),
        ("fn(@Nat -> @{ @Bool | true }) effects(pure) { true }", 1),
    ))
    def test_accepted_and_run(self, predicate: str, value: int,
                              tmp_path: Path) -> None:
        out = _check(tmp_path, _quantifier(predicate, prelude=_SMALL))
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", value)

    @pytest.mark.parametrize(("form", "binder", "body", "value"), (
        # R-1508's repros: the refinement is the range, so a body that holds
        # only inside it makes `forall` true, and `exists` over a refinement
        # no index below the bound satisfies is false.
        ("forall", "@{ @Nat | @Nat.0 < 2 }", "@Nat.0 < 2", 1),
        ("forall", "@Small", "@Nat.0 < 2", 1),
        ("forall", "@Nat", "@Nat.0 < 2", 0),
        ("exists", "@{ @Nat | @Nat.0 > 10 }", "true", 0),
        ("exists", "@{ @Nat | @Nat.0 > 3 }", "true", 1),
        ("exists", "@Nat", "@Nat.0 > 3", 1),
    ))
    def test_the_index_types_refinement_is_honoured(
        self, form: str, binder: str, body: str, value: int,
        tmp_path: Path,
    ) -> None:
        out = _check(tmp_path, _quantifier(
            f"fn(@Nat -> @Bool) effects(pure) {{ {body} }}",
            binder=binder, prelude=_SMALL, form=form))
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", value)

    @pytest.mark.parametrize("binder", ("@String", "@Bool", "@Byte"))
    def test_an_index_type_that_is_no_count_is_refused(
        self, binder: str, tmp_path: Path,
    ) -> None:
        out = _check(tmp_path, _quantifier(
            "fn(@Nat -> @Bool) effects(pure) { true }", binder=binder))
        diag = _diag(out, "E186")
        assert binder[1:] in diag.description, diag.description

    @pytest.mark.parametrize("form", ("forall", "exists"))
    def test_each_suggested_rewrite_means_the_refinement(
        self, form: str, tmp_path: Path,
    ) -> None:
        """E179's two rewrites of a refined PARAMETER — refine the index
        type instead, or test P in the body with `==>` for `forall` and `&&`
        for `exists` — mean the same thing, over predicates and bodies whose
        answers differ."""
        connective = "==>" if form == "forall" else "&&"
        refused = _check(tmp_path / "refused", _quantifier(
            "fn(@{ @Nat | @Nat.0 < 3 } -> @Bool) effects(pure) { true }",
            form=form))
        assert connective in _diag(refused, "E179").fix
        cases = [
            ("@Nat.0 < 3", "@Nat.0 < 2"), ("@Nat.0 < 3", "@Nat.0 < 5"),
            ("@Nat.0 > 10", "true"), ("@Nat.0 > 1", "@Nat.0 == 4"),
            ("@Nat.0 > 1", "@Nat.0 == 9"), ("true", "@Nat.0 < 4"),
        ]
        for i, (pred, body) in enumerate(cases):
            index_form = _check(tmp_path / f"i{i}", _quantifier(
                f"fn(@Nat -> @Bool) effects(pure) {{ {body} }}",
                binder=f"@{{ @Nat | {pred} }}", form=form))
            body_form = _check(tmp_path / f"b{i}", _quantifier(
                f"fn(@Nat -> @Bool) effects(pure) {{ ({pred}) {connective} "
                f"({body}) }}", form=form))
            assert index_form.accepted and body_form.accepted
            expected = [n for n in range(5) if eval_index(pred, n)]
            want = (all(eval_index(body, n) for n in expected)
                    if form == "forall"
                    else any(eval_index(body, n) for n in expected))
            assert run_main(index_form) == run_main(body_form) == (
                "ok", int(want)), (pred, body)

    def test_an_unknown_parameter_type_is_reported_once(
        self, tmp_path: Path,
    ) -> None:
        """E136 names the mistake; no second E179 for the same one."""
        out = _check(tmp_path, _quantifier(
            "fn(@Qzt -> @Bool) effects(pure) { true }"))
        codes = [d.error_code for d in out.check_errors]
        assert "E136" in codes and "E179" not in codes, codes
