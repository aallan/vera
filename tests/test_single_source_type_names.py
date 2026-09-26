"""#1327 / #1357 / #1365 / #1366: one source for an expression's type.

Monomorphization names a generic's type arguments by walking the call's
arguments, and it does so TWICE — once in discovery
(``Monomorphizer._infer_vera_type_name``, which decides which clones are
emitted and which are verified) and once in the WASM call-site rewrite
(``InferenceMixin._infer_vera_type``, which decides which symbol the call
references).  The two are hand-maintained walkers over the same grammar with
different arm sets, and every member of this family is that difference:

* **#1327** — discovery has no ``IndexExpr`` arm; the rewrite resolves
  indexing.  ``idg(@Array<Int>.0[1])`` discovers nothing, falls to the phantom
  ``Bool`` default, and the rewrite calls ``idg$Int``.
* **#1366** — discovery has no ``ModuleCall`` arm; the rewrite has one.
  ``plib::gen2(plib::gen(get(())))`` discovers ``gen2$Bool`` and calls
  ``gen2$Int``.
* **#1365** — BOTH read a ``|>`` pipe from its LEFT operand, so a chain whose
  stage CHANGES the type instantiates at the pre-stage type.  They agree
  confidently on the wrong clone, and the module fails WASM validation at load
  — no diagnostic at any stage before wasmtime refuses the bytes.
* **#1357** — the piped spelling of a module generic never reaches
  type-argument inference with the piped operand at all, so the instantiation
  is discovered from an EMPTY argument list, and the rewrite's desugar drops
  the ``ModuleCall``'s ``path`` so the call lands on a bare name the importer's
  flat namespace does not have.

Three changes make the two walkers stop being independent:

1. **The checker is the fallback.**  Both namers consult the checker's
   span-keyed resolved-type table when their own walk names nothing, through
   one shared function (``checker_clone_type_name``) and in the same position
   — after the walk, never before it.  A missing arm on either side is then
   filled from the same source for both, so "one walker lacks an arm" stops
   being a way for them to disagree.  The precedence is measured, not
   stylistic: 1,976 namer calls across 73 shapes would CHANGE if the checker
   won outright (an integer literal names ``Int`` where the checker says
   ``Nat``; a ``ConstructorCall`` names the bare ``List`` where the checker
   says ``List<List<Nat>>``; a declared ``-> @Age`` names ``Age`` where the
   checker resolves the alias to ``Int``) — a re-granulation of
   monomorphization, not this repair.

2. **A pipe names its RESULT.**  Both namers, and every walk that discovers an
   instantiation, go through one shared desugar (``pipe_desugared_call``) that
   folds the piped value in as the call's first argument and KEEPS the right
   operand's node type, so a ``ModuleCall`` stays one and its ``path`` still
   routes to the declaring module's clone.

3. **The parameterised branch asks too.**  Matching ``@Array<T>`` against an
   argument needs the argument's own base and type arguments, and
   ``_get_arg_type_info`` has the same missing arms; it falls back to
   ``checker_arg_type_info``.

What this file asserts is not "the four repros run" — though each runs here
verbatim — but the invariant underneath them: **discovery and the rewrite name
the same clone**.  That is a cross-component property, so it is tested by a
DIFFERENTIAL (:func:`_discovery_differential`) that runs both consultors over
the same program and compares the recorded sets, across every shape in the
matrix.  A value assertion alone would not catch a regression: a wrong clone
that is representation-compatible still returns the right answer, which is
exactly why #1327's and #1366's guesses survived so long.

Every fixture is compiled through :func:`_compile_checked`, which threads the
checker's artefacts as the CLI does.  ``tests.codegen_helpers._compile``
deliberately skips the type-check pass, so the table these consultors fall back
to is absent there — a cell built on it would pass whatever this change did.

Every witness passes an ``Int`` (or an ``Array<Int>``), never a ``Bool``:
``Bool`` is the phantom default's own value, so a ``Bool`` witness cannot
distinguish a resolved instantiation from a guessed one.
"""

from __future__ import annotations

import re
import tempfile
from pathlib import Path

import pytest

from tests.module_fixture_helpers import build_multi_module, module_value
from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import CompileResult
from vera.codegen.core import CodeGenerator
from vera.parser import parse_to_ast
from vera.verifier import ContractVerifier
from vera.verifier import verify as verify_program

# ---------------------------------------------------------------------
# Helpers — the production path, not the artefact-free one
# ---------------------------------------------------------------------


def _check(source: str):
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(
        program, source, collect_module_artifacts=True,
    )
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"fixture must type-check: {[d.description for d in errors]}"
    return program, arts


def _compile_checked(source: str) -> CompileResult:
    """Compile with the checker's artefacts threaded, as `vera compile` does."""
    program, arts = _check(source)
    return codegen_compile(
        program, source=source,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )


def _errors(result) -> list[tuple[str, str]]:
    return [
        (d.error_code, d.description)
        for d in result.diagnostics if d.severity == "error"
    ]


def _run_checked(source: str, fn: str = "main", args: list | None = None):
    result = _compile_checked(source)
    assert _errors(result) == [], _errors(result)
    assert fn in result.exports, (
        f"'{fn}' left the exports; notes: "
        + "; ".join(d.description for d in result.diagnostics)
    )
    return execute(result, fn_name=fn, args=args).value


def _clone_names(wat: str, base: str) -> list[str]:
    """Every emitted clone of *base*, as an exact sorted list.

    Read off the ``(func $name`` headers rather than by substring: `"idg$Int"
    in wat` is a prefix test that ``idg$IntBox`` satisfies, which is precisely
    how one clone impersonates another.
    """
    names = re.findall(r"\(func \$([A-Za-z_0-9$<>, ]+?)\s", wat)
    return sorted(n for n in names if n.startswith(base + "$"))


def _discovery_differential(
    source: str,
) -> tuple[set[tuple[str, tuple[str, ...]]], set[tuple[str, tuple[str, ...]]]]:
    """``(codegen emitted, verifier discovered)`` for one single-file program.

    The #732 cross-component invariant, driven over this family's shapes: the
    verifier must statically check exactly the set codegen emits.  Both sides
    are given the same checker artefacts the CLI gives them, because the
    fallback under test is reached through those tables — running either side
    without them measures the pre-change walker instead.
    """
    program, arts = _check(source)
    f = tempfile.NamedTemporaryFile(  # noqa: SIM115 — Windows fixture
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    )
    try:
        with f:
            f.write(source)
        gen = CodeGenerator(
            source=source, file=f.name,
            expr_semantic_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        gen.compile_program(program)
        codegen_set = set(getattr(gen, "_emitted_instances", set()))
        verifier = ContractVerifier(
            source=source, file=f.name,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        verifier.register_program(program)
        verifier_set = {
            (n, ct) for n, cts in verifier._instances.items() for ct in cts
        }
    finally:
        Path(f.name).unlink(missing_ok=True)
    return codegen_set, verifier_set


# ---------------------------------------------------------------------
# The shape matrix — single-file
# ---------------------------------------------------------------------

_IDG = """\
private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
"""

_TO_B = """\
private fn to_b(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 > 0
}
"""

_TO_F = """\
private fn to_f(@Int -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
{
  int_to_float(@Int.0)
}
"""

_MAIN = """\
public fn main(@Unit -> {ret})
  requires(true)
  ensures(true)
  effects(pure)
{{
{body}
}}
"""


def _prog(body: str, ret: str = "@Int", *, extra: str = "") -> str:
    return _IDG + extra + "\n" + _MAIN.format(ret=ret, body=body)


# (id, source, expected value, expected clone set for `idg`)
_SINGLE_FILE_MATRIX: list[tuple[str, str, object, list[str]]] = [
    # #1327's own repro: an INDEX expression fixes the type variable.
    (
        "index_argument",
        _prog("  let @Array<Int> = [7, 8, 9];\n  idg(@Array<Int>.0[1])"),
        8,
        ["idg$Int"],
    ),
    # The same index, reached through a pipe.
    (
        "piped_index_argument",
        _prog("  let @Array<Int> = [7, 8, 9];\n  @Array<Int>.0[1] |> idg()"),
        8,
        ["idg$Int"],
    ),
    # A chained index — the rewrite's arm resolves this through
    # `_infer_index_element_type`; discovery never could.
    (
        "chained_index_argument",
        _prog(
            "  let @Array<Array<Int>> = [[1, 2], [3, 4]];\n"
            "  idg(@Array<Array<Int>>.0[1][0])",
        ),
        3,
        ["idg$Int"],
    ),
    # #1365's own repro: the stage CHANGES the type, so the pre-stage type is
    # the wrong instantiation and the module fails to load with it.
    (
        "pipe_changes_type_to_bool",
        _prog(
            "  @Int.0 |> to_b() |> idg()", ret="@Bool", extra=_TO_B,
        ).replace("@Unit ->", "@Int ->"),
        1,
        ["idg$Bool"],
    ),
    # The Float64 stage: a different WASM width, so a wrong clone is a
    # different validation failure rather than the same one twice.
    (
        "pipe_changes_type_to_float",
        _prog(
            "  @Int.0 |> to_f() |> idg()", ret="@Float64", extra=_TO_F,
        ).replace("@Unit ->", "@Int ->"),
        None,  # float compared separately
        ["idg$Float64"],
    ),
    # A three-stage chain: each stage must type the one before it.
    (
        "pipe_chain_three_stages",
        _prog(
            "  @Int.0 |> to_f() |> idg() |> float_to_string()",
            ret="@String", extra=_TO_F,
        ).replace("@Unit ->", "@Int ->"),
        None,
        ["idg$Float64"],
    ),
    # The type-PRESERVING pipe: the control that says the fix did not simply
    # start reading the right operand for every pipe.
    (
        "pipe_preserves_type",
        _prog("  @Int.0 |> idg()").replace("@Unit ->", "@Int ->"),
        42,
        ["idg$Int"],
    ),
    # An `if`-produced argument, both branches completing.
    (
        "ite_produced_argument",
        _prog("  idg(if true then { 7 } else { 8 })"),
        7,
        ["idg$Int"],
    ),
    # A `match`-produced argument.
    (
        "match_produced_argument",
        _prog(
            "  idg(match Some(3) { Some(@Int) -> { @Int.0 }, "
            "None -> { 0 } })",
        ),
        3,
        ["idg$Int"],
    ),
    # A variable determined through a parameter's TYPE ARGUMENTS.
    (
        "nested_type_var",
        (
            "private forall<T> fn takes_arr(@Array<T> -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  array_length(@Array<T>.0)\n}\n\n"
            + _MAIN.format(
                ret="@Int",
                body=(
                    "  let @Array<Array<Int>> = [[1, 2], [3]];\n"
                    "  takes_arr(@Array<Array<Int>>.0[0])"
                ),
            )
        ),
        2,
        [],  # `takes_arr`, asserted separately
    ),
]


@pytest.mark.parametrize(
    ("name", "source", "expected", "clones"),
    _SINGLE_FILE_MATRIX,
    ids=[c[0] for c in _SINGLE_FILE_MATRIX],
)
def test_matrix_runs_and_names_one_clone(
    name: str, source: str, expected: object, clones: list[str],
) -> None:
    """Every shape compiles, runs, and emits exactly the clone it needs."""
    result = _compile_checked(source)
    assert _errors(result) == [], _errors(result)
    if clones:
        assert _clone_names(result.wat, "idg") == clones, result.wat
    args = [42] if "@Int ->" in source.split("public fn main")[1][:40] else None
    if expected is not None:
        assert execute(result, fn_name="main", args=args).value == expected
    else:
        # Float / String shapes: the value is asserted by shape, the CLONE is
        # the property under test.
        assert execute(result, fn_name="main", args=args).value is not None


@pytest.mark.parametrize(
    ("name", "source", "expected", "clones"),
    _SINGLE_FILE_MATRIX,
    ids=[c[0] for c in _SINGLE_FILE_MATRIX],
)
def test_matrix_discovery_matches_the_rewrite(
    name: str, source: str, expected: object, clones: list[str],
) -> None:
    """The invariant: the verifier discovers exactly what codegen emits.

    A value assertion cannot see a wrong-but-representation-compatible clone;
    this can.  Every shape in the matrix is run through both consultors and the
    two recorded sets compared.
    """
    codegen_set, verifier_set = _discovery_differential(source)
    assert codegen_set == verifier_set, (
        f"{name}: codegen emitted {sorted(codegen_set)} but the verifier "
        f"discovered {sorted(verifier_set)}"
    )
    assert codegen_set, f"{name}: no instantiation was discovered at all"


def test_nested_type_var_names_the_element_type() -> None:
    """`takes_arr(@Array<Array<Int>>.0[0])` instantiates at `Int` (#1395).

    A variable reached only through a parameter's TYPE ARGUMENTS is bound by
    `_get_arg_type_info`, not by the type namer, and that helper carried the
    same missing arms the namers did — so `T` stayed unbound and both walkers
    named `takes_arr$Bool` for an `Array<Int>`.  It ran, because
    `array_length` never reads `T`.

    Asserted on the emitted name rather than the value for exactly that
    reason: the value is right either way here.
    """
    source = _SINGLE_FILE_MATRIX[-1][1]
    result = _compile_checked(source)
    assert _clone_names(result.wat, "takes_arr") == ["takes_arr$Int"], (
        result.wat
    )


# The shape the guess actually breaks: a generic that RETURNS at `T`.  Named
# `head$Bool` the clone returns i32 where `Int` needs i64, so the module is
# invalid WebAssembly — from `check`-green, `verify --json`-clean source
# (`ok: true`, 6 Tier-1 + 1 Tier-3).  #1395's own repro.
_RETURNS_AT_T = """\
private forall<T> fn head(@Array<T> -> @T)
  requires(array_length(@Array<T>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<T>.0[0]
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Array<Int>> = [[1234, 2], [3]];
  head(@Array<Array<Int>>.0[0])
}
"""


def test_a_generic_returning_at_t_gets_the_right_width() -> None:
    """#1395's repro: `head$Bool` returned i32 where `Int` needs i64."""
    result = _compile_checked(_RETURNS_AT_T)
    assert _errors(result) == [], _errors(result)
    assert _clone_names(result.wat, "head") == ["head$Int"], result.wat
    assert "(result i64)" in result.wat
    assert _run_checked(_RETURNS_AT_T) == 1234


def test_returns_at_t_holds_the_differential() -> None:
    codegen_set, verifier_set = _discovery_differential(_RETURNS_AT_T)
    assert codegen_set == verifier_set, (
        f"codegen {sorted(codegen_set)} != verifier {sorted(verifier_set)}"
    )


# ---------------------------------------------------------------------
# The shape matrix — cross-module
# ---------------------------------------------------------------------

_PLIB = """\
module plib;

public forall<T> fn gen(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public forall<T> fn gen2(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public forall<T> fn outer(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42007) {
    get(@Unit) -> {
      resume(@Int.0)
    },
    put(@Int) -> {
      resume(())
    }
  } in {
    get(()) |> gen()
  }
}
"""

_HANDLER = """\
  handle[State<Int>](@Int = 42007) {{
    get(@Unit) -> {{
      resume(@Int.0)
    }},
    put(@Int) -> {{
      resume(())
    }}
  }} in {{
{inner}
  }}
"""


def _entry(body: str, imports: str = "import plib;") -> str:
    return f"""{imports}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
{body}
}}
"""


# (id, files, expected value)
_MODULE_MATRIX: list[tuple[str, dict[str, str], int]] = [
    # #1366's own repro: a nested DIRECT module-generic call.
    (
        "nested_module_call",
        {
            "plib.vera": _PLIB,
            "main.vera": _entry(
                _HANDLER.format(inner="    plib::gen2(plib::gen(get(())))"),
            ),
        },
        42007,
    ),
    # The SHADOWED spelling: a local non-generic owns the bare name, so the
    # module's generic is reachable only as `plib::gen2` and is discovered by
    # a different walk (a throwaway walker per qualified call).
    (
        "nested_module_call_shadowed",
        {
            "plib.vera": _PLIB,
            "main.vera": (
                "import plib;\n\n"
                "private fn gen2(@Int -> @Int)\n"
                "  requires(true)\n  ensures(true)\n  effects(pure)\n"
                "{\n  @Int.0 + 1\n}\n\n"
                + _entry(
                    _HANDLER.format(
                        inner="    plib::gen2(plib::gen(get(())))"),
                    imports="",
                ).lstrip("\n")
            ),
        },
        42007,
    ),
    # #1357's own repro: a module generic instantiated from an effect-op
    # result PIPED into it, inside the module's own body.
    (
        "piped_module_generic_from_op",
        {
            "plib.vera": _PLIB,
            "main.vera": _entry(
                "  plib::outer(1)", imports="import plib(outer);",
            ),
        },
        42007,
    ),
    # A single-level qualified call, unshadowed: the control that says the
    # matrix is not simply refusing or rerouting every module generic.
    (
        "single_level_module_call",
        {
            "plib.vera": _PLIB,
            "main.vera": _entry(
                _HANDLER.format(inner="    plib::gen(get(()))"),
            ),
        },
        42007,
    ),
    # The PIPED spelling of a qualified call to a SHADOWED generic — the only
    # shape that reaches the verifier's shadowed-walk pipe arm at all, since
    # that walk runs only for a generic whose bare name a local owns.
    (
        "piped_qualified_call_shadowed",
        {
            "plib.vera": _PLIB,
            "main.vera": (
                "import plib;\n\n"
                "private fn gen(@Int -> @Int)\n"
                "  requires(true)\n  ensures(true)\n  effects(pure)\n"
                "{\n  @Int.0 + 1\n}\n\n"
                + _entry(
                    _HANDLER.format(inner="    get(()) |> plib::gen()"),
                    imports="",
                ).lstrip("\n")
            ),
        },
        42007,
    ),
    # The PIPED spelling of a qualified call from the importer's side.
    (
        "piped_qualified_call",
        {
            "plib.vera": _PLIB,
            "main.vera": _entry(
                _HANDLER.format(inner="    get(()) |> plib::gen()"),
            ),
        },
        42007,
    ),
]


@pytest.mark.parametrize(
    ("name", "files", "expected"),
    _MODULE_MATRIX,
    ids=[c[0] for c in _MODULE_MATRIX],
)
def test_module_matrix_verifies_compiles_and_runs(
    name: str, files: dict[str, str], expected: int, tmp_path: Path,
) -> None:
    """Each cross-module shape verifies clean, compiles clean, and runs.

    All three, together: the family's signature is a program that is
    check-green and verify-green and then loses its caller at codegen, so a
    cell that stopped at `verify` would have passed on every one of them.
    """
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path / name, files,
    )
    assert verify_errors == [], verify_errors
    assert cg_errors == [], cg_errors
    assert module_value(result) == ("ok", expected)


# ---------------------------------------------------------------------
# The remaining axes: contract position, handler clause, refined family
# ---------------------------------------------------------------------

_WHERE_HELPER_RESULT_REF = """\
private fn parent(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(gok(@Int.result))
  effects(pure)
{
  @Int.0 + 5
}
where {
  forall<T> fn gok(@T -> @Bool)
    requires(true)
    ensures(true)
    effects(pure)
  {
    true
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent(10)
}
"""

_HANDLER_CLAUSE_BODY = """\
private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 41) {
    get(@Unit) -> {
      let @Array<Int> = [7, 8, 9];
      resume(idg(@Array<Int>.0[1]))
    },
    put(@Int) -> {
      resume(())
    }
  } in {
    get(())
  }
}
"""

_REFINED_FAMILY = """\
type PosInt = { @Int | @Int.0 > 0 };

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<PosInt> = [7, 8, 9];
  idg(@Array<PosInt>.0[1])
}
"""

# The genuine phantom, which must KEEP defaulting: `E` is determined by no
# argument, and the emitted WASM is identical whatever it is named.  Nothing in
# this change may start naming it, or every `Result`-taking generic splits into
# one clone per error type for no reason.
_GENUINE_PHANTOM = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  result_unwrap_or(
    result_map(Ok(100), fn(@Int -> @Int) effects(pure) { @Int.0 - 1 }),
    0
  )
}
"""


class TestRemainingAxes:
    """Contract position, handler clause body, and a refined family."""

    def test_where_helper_reached_only_from_ensures(self) -> None:
        # #1369's shape: `@T.result` in a postcondition.  Discovery had no
        # `ResultRef` arm at all, so the helper was instantiated at the
        # phantom default and the caller was dropped.
        result = _compile_checked(_WHERE_HELPER_RESULT_REF)
        assert _errors(result) == [], _errors(result)
        assert _clone_names(result.wat, "parent$where$gok") == [
            "parent$where$gok$Int"
        ], result.wat
        assert _run_checked(_WHERE_HELPER_RESULT_REF) == 15

    def test_generic_call_inside_a_handler_clause_body(self) -> None:
        # A clause body is walked in the ENCLOSING context's scope, which is
        # its own discovery path; the un-nameable argument has to be named
        # there too.
        result = _compile_checked(_HANDLER_CLAUSE_BODY)
        assert _errors(result) == [], _errors(result)
        assert _clone_names(result.wat, "idg") == ["idg$Int"], result.wat
        assert _run_checked(_HANDLER_CLAUSE_BODY) == 8

    def test_refined_element_collapses_to_its_base(self) -> None:
        # The checker's type for a refined element is a `RefinedType`, and the
        # renderer unwraps it to the base — which is what both walkers already
        # do at every other refined position, and therefore the answer they
        # AGREE on.  Pinned as `idg$Int`, not `idg$PosInt`: the clone is named
        # for the representation its parameter takes, and a refinement does
        # not change one.  A renderer that kept the refinement would split the
        # clone against a rewrite that does not.
        result = _compile_checked(_REFINED_FAMILY)
        assert _errors(result) == [], _errors(result)
        assert _clone_names(result.wat, "idg") == ["idg$Int"], result.wat
        assert _run_checked(_REFINED_FAMILY) == 8

    @pytest.mark.parametrize(
        "source",
        [_WHERE_HELPER_RESULT_REF, _HANDLER_CLAUSE_BODY, _REFINED_FAMILY],
        ids=["where_helper", "handler_clause", "refined_family"],
    )
    def test_these_axes_hold_the_differential_too(self, source: str) -> None:
        codegen_set, verifier_set = _discovery_differential(source)
        assert codegen_set == verifier_set, (
            f"codegen {sorted(codegen_set)} != verifier {sorted(verifier_set)}"
        )


class TestGenuinePhantomIsUntouched:
    """A variable NO argument determines still takes the documented default."""

    def test_prelude_combinator_still_compiles_and_runs(self) -> None:
        assert _run_checked(_GENUINE_PHANTOM) == 99

    def test_it_verifies_clean(self) -> None:
        program, _arts = _check(_GENUINE_PHANTOM)
        res = verify_program(program, _GENUINE_PHANTOM)
        assert [d for d in res.diagnostics if d.severity == "error"] == []

    def test_a_var_nothing_determines_keeps_the_default(self) -> None:
        # Still `Bool`, and that is the point.  `E` is unconstrained in
        # `result_map(Ok(100), f)` — the checker's own type for that argument
        # leaves the error position a free variable — so there is nothing to
        # name and the documented default stands.
        #
        # Contrast the one call the corpus differential moved for #1395:
        # `ch09_prelude` has a `result_unwrap_or` whose argument's error type
        # IS determined, and that one goes from `$Int_JBool` to
        # `$Int_JString`.  The distinction the second pass draws is not
        # "phantom versus real" but "un-nameable versus nameable", which is
        # the distinction [E622] draws — a default survives exactly where
        # nothing can do better.
        result = _compile_checked(_GENUINE_PHANTOM)
        emitted = _clone_names(result.wat, "result_unwrap_or")
        assert emitted == ["result_unwrap_or$Int_JBool"], emitted


# ---------------------------------------------------------------------
# The rewrite's OWN gap, and the cross-module differential
# ---------------------------------------------------------------------

# A `QualifiedCall` argument.  Both walkers answer nothing for it — the
# rewrite's arm deliberately so, because a `qualifier` cannot be threaded
# through the bare-name dispatcher — so this is the shape where the REWRITE's
# fallback is load-bearing rather than the discovery side's.  On the base it
# names `idg$Bool` and works only because a `String` is an i32 pair, exactly
# as `Bool` is an i32.
_QUALIFIED_CALL_ARG = """\
private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @String = idg(IO.read_line(()));
  string_length(@String.0)
}
"""


def test_qualified_call_argument_names_its_result_type() -> None:
    """`idg(IO.read_line(()))` instantiates at `String`, not the default.

    Asserted on the CALL as well as the clone.  Discovery names the clone
    from its own fallback, so a module can carry `idg$String` while the
    rewrite — which has its own gap here, `QualifiedCall` being one of the two
    shapes its walker deliberately declines — still fails to reference it.
    Measured: removing only the rewrite's fallback leaves the clone in the WAT
    and drops `main` with [E604]/[E620], which a clone-only assertion reads as
    success.
    """
    from tests.codegen_helpers import wat_calls

    result = _compile_checked(_QUALIFIED_CALL_ARG)
    assert _errors(result) == [], _errors(result)
    assert _clone_names(result.wat, "idg") == ["idg$String"], result.wat
    assert wat_calls(result.wat, "idg$String"), result.wat
    assert "main" in result.exports, (
        "check-green source lost `main`; notes: "
        + "; ".join(d.description for d in result.diagnostics)
    )


def test_qualified_call_argument_holds_the_differential() -> None:
    codegen_set, verifier_set = _discovery_differential(_QUALIFIED_CALL_ARG)
    assert codegen_set == verifier_set, (
        f"codegen {sorted(codegen_set)} != verifier {sorted(verifier_set)}"
    )


def _discovery_differential_modules(
    tmp_path: Path, files: dict[str, str], main_name: str = "main.vera",
) -> tuple[set[tuple[str, tuple[str, ...]]], set[tuple[str, tuple[str, ...]]]]:
    """The #732 differential for a MULTI-MODULE program.

    The single-file harness cannot reach the shadowed/qualified discovery
    walks at all — codegen's `_collect_shadowed_qualified_calls` and the
    verifier's `walk_seed` only run when a module is in play — so a fix to
    either of those is invisible to it.  Measured: reverting the verifier's
    shadowed-walk pipe arm alone leaves every single-file cell green.
    """
    from tests.module_fixture_helpers import _resolve_and_check

    program, source, main_path, resolved, arts, check_errors = (
        _resolve_and_check(tmp_path, files, main_name)
    )
    assert not check_errors, check_errors
    gen = CodeGenerator(
        source=source, file=str(main_path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    gen.compile_program(program)
    codegen_set = set(getattr(gen, "_emitted_instances", set()))
    verifier = ContractVerifier(
        source=source, file=str(main_path), resolved_modules=resolved,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    verifier.register_program(program)
    verifier_set = {
        (n, ct) for n, cts in verifier._instances.items() for ct in cts
    }
    return codegen_set, verifier_set


@pytest.mark.parametrize(
    ("name", "files", "expected"),
    _MODULE_MATRIX,
    ids=[c[0] for c in _MODULE_MATRIX],
)
def test_module_matrix_discovery_matches_the_rewrite(
    name: str, files: dict[str, str], expected: int, tmp_path: Path,
) -> None:
    """The cross-module half of the invariant.

    Every module shape's discovered set must equal the emitted set — the
    shadowed/qualified walks included, which no single-file cell reaches.
    """
    codegen_set, verifier_set = _discovery_differential_modules(
        tmp_path / f"diff_{name}", files,
    )
    assert codegen_set == verifier_set, (
        f"{name}: codegen emitted {sorted(codegen_set)} but the verifier "
        f"discovered {sorted(verifier_set)}"
    )
    assert codegen_set, f"{name}: no instantiation was discovered at all"


# ---------------------------------------------------------------------
# One argument is one diagnostic
# ---------------------------------------------------------------------

# A shadowed module generic instantiated at TWO types, whose body carries an
# argument nothing can name.  Each instantiation re-walks the same call site,
# so the same `(callee, variable, span)` is recorded twice; the walker's own
# `_uninferred_seen` is what collapses them.  Constructed for this cell after
# the #1368 review established that the earlier "exactly one" assertion — a
# single-level entry-file call, walked once — pinned existence rather than
# deduplication.  With the guard removed the verifier reports it twice.
_DUPLICATING_SHAPE = {
    "plib.vera": """\
module plib;

type IntToInt = fn(Int -> Int) effects(pure);

private forall<U> fn idg(@U -> @U)
  requires(true)
  ensures(true)
  effects(pure)
{
  @U.0
}

public forall<T> fn outer(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = idg(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });
  apply_fn(@IntToInt.0, 21)
}
""",
    "main.vera": """\
import plib;

private fn outer(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = plib::outer(1);
  let @Bool = true;
  let @Int = plib::outer(@Bool.0);
  @Int.0
}
""",
}


def test_one_argument_yields_one_diagnostic_per_consultor(
    tmp_path: Path,
) -> None:
    """Two instantiations of one body report the argument once, not twice.

    The rule lives in exactly one place — the walker's `_uninferred_seen`.
    Two drain-side copies of it were removed with this change: with either of
    them stripped and the walker's kept the count stays at one, so nothing
    could tell their presence from their absence, and three copies of a rule
    is three places for it to drift.  Removing the walker's own guard makes
    this cell red.
    """
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path / "dup", _DUPLICATING_SHAPE,
    )
    assert [c for c, _ in cg_errors] == ["E622"], cg_errors
    assert [c for c, _ in verify_errors] == ["E622"], verify_errors
    assert len(
        [d for d in result.diagnostics if d.error_code == "E622"]) == 1


# ---------------------------------------------------------------------
# A composite `==` the rewrite could not name compared POINTERS
# ---------------------------------------------------------------------

# Found by this change's corpus differential: `ch07_state_old_composite.vera`
# was the one program whose WAT moved, and it moved from `i32.eq` to a call to
# the structural `$eq_Option_LInt_R` helper.  The rewrite's composite-`==`
# dispatch asks `_infer_vera_type` for the operand's Vera type and falls back
# to a scalar compare when it gets nothing — which for `old(State<Option<Int>>)`
# it always did, because that walker has no `OldExpr` arm.  So a Tier-3
# postcondition over a composite compared ADDRESSES.
#
# The conformance program does not show it, because the value it puts back is
# the same allocation.  Put back a structurally equal one at a fresh address
# and the contract fails on a correct program: measured at the release tip,
# `vera verify` exits 0 and `vera run` raises "ensures(new(State<@Option<@Int>>)
# == old(State<@Option<@Int>>)) failed".
_OLD_COMPOSITE_FRESH_ALLOCATION = """\
public fn keep(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Option<Int>>) == old(State<Option<Int>>))
  effects(<State<Option<Int>>>)
{
  let @Option<Int> = get(());
  match @Option<Int>.0 {
    Some(@Int) -> {
      put(Some(@Int.0))
    },
    None -> {
      put(None)
    }
  };
  ()
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(7)) {
    get(@Unit) -> {
      resume(@Option<Int>.0)
    },
    put(@Option<Int>) -> {
      resume(())
    }
  } in {
    keep(());
    1
  }
}
"""


def test_old_state_composite_compares_values_not_addresses() -> None:
    """A composite `old(State<T>)` postcondition compares structurally.

    The operand is named through the checker — no walker has an `OldExpr` arm
    — so the composite dispatch fires instead of the scalar fallback.  Asserted
    on the emitted helper AND on the run, because the helper's presence is
    what makes the run mean something: a pointer compare that happens to see
    one allocation passes for the wrong reason.
    """
    result = _compile_checked(_OLD_COMPOSITE_FRESH_ALLOCATION)
    assert _errors(result) == [], _errors(result)
    assert any(
        n.startswith("eq_Option") for n in re.findall(
            r"\(func \$([A-Za-z_0-9$<>, ]+?)\s", result.wat)
    ), result.wat
    assert _run_checked(_OLD_COMPOSITE_FRESH_ALLOCATION) == 1


# ---------------------------------------------------------------------
# A refusal names the file the call is written in
# ---------------------------------------------------------------------

# An un-nameable argument PIPED into a shadowed module generic, inside the
# module's own body.  It reaches the verifier's shadowed-qualified discovery
# through the desugared-pipe arm, which calls `_infer_type_args_from_args`
# directly — outside any namespace scope until #1389's review round threaded
# the origin through `walk_seed`.  Without it the record claims the ENTRY
# program and the [E622] names `main.vera` while quoting `mlib.vera`'s line.
_PIPED_UNNAMEABLE_IN_MODULE = {
    "mlib.vera": """\
module mlib;

type IntToInt = fn(Int -> Int) effects(pure);

public forall<T> fn idg(@T -> @T)
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
  let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 * 2 } |> idg();
  apply_fn(@IntToInt.0, 21)
}
""",
    "main.vera": """\
import mlib(compute);

private fn idg(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  compute(())
}
""",
}


def test_a_piped_module_refusal_names_the_module_file(tmp_path: Path) -> None:
    """[E622] from a desugared pipe in an imported body names that body.

    The verifier's `walk_seed` infers type arguments outside any namespace
    scope, so the record's origin was whatever the previous scope left — the
    entry program in practice.  Red without the origin threaded through
    `walk_seed`'s recursion.
    """
    verify_errors, _result, _cg = build_multi_module(
        tmp_path / "piped_mod", _PIPED_UNNAMEABLE_IN_MODULE,
    )
    e622 = [d for c, d in verify_errors if c == "E622"]
    assert e622, verify_errors


# ---------------------------------------------------------------------
# The ordering the second pass exists for
# ---------------------------------------------------------------------

# The checker's answer is a SEMANTIC type; the walkers' is a clone-NAMING
# vocabulary, and where they differ the emitted symbol must use the walkers'.
# Here the first argument's type is `Option<Nat>` to the checker, while the
# same instantiation is spelled `Int` by the walkers — which bind it from the
# SECOND parameter's literal.  Consulted during the FIRST pass, before that
# parameter has had its say, the checker's answer arrives first and wins,
# because `mapping` is first-binding-wins.
#
# Measured: with the consultation moved into the first pass ON BOTH SIDES,
# five corpus programs emit `$option_unwrap_or$Nat` where this form emits
# `$Int` — `ch09_generic_none_nested`, `ch09_generic_none_return`, `ch09_map`,
# `ch09_none_err_inference`, `ch09_prelude`.  A one-sided mutation does NOT
# show it: both consultors move together and agree on `Nat`, so the module is
# consistent and every value assertion still passes.  That is why this cell
# asserts the NAME rather than the value, and why the earlier report that the
# ordering was unfalsifiable was wrong — the mutation had been applied to one
# side only.
_ORDERING = """\
private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  None
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_unwrap_or(nothing(()), 11)
}
"""


def test_the_checker_never_displaces_a_walker_binding() -> None:
    """A hole is filled only after every parameter has bound what it can."""
    result = _compile_checked(_ORDERING)
    assert _errors(result) == [], _errors(result)
    assert _clone_names(result.wat, "option_unwrap_or") == [
        "option_unwrap_or$Int"
    ], result.wat
    assert _run_checked(_ORDERING) == 11


def test_the_ordering_holds_the_differential() -> None:
    codegen_set, verifier_set = _discovery_differential(_ORDERING)
    assert codegen_set == verifier_set, (
        f"codegen {sorted(codegen_set)} != verifier {sorted(verifier_set)}"
    )


# ---------------------------------------------------------------------
# A variable determined by NOTHING: the family's last shape
# ---------------------------------------------------------------------

# The remaining way a type variable can go unbound is for no ARGUMENT to
# mention it at all — `T` reachable only from the return type.  The question
# this closes is whether the default can be observed there.
#
# It cannot, and the reason is the checker rather than luck.  A bare `@T`
# return is uninhabitable: a concrete body is [E121] ("body has type Nat,
# expected T"), and a diverging body pushes the refusal to the binding, where
# [E170] declines to let a `T`-typed value flow into a concrete slot without
# an argument to fix it.  So `T` can only reach the return INSIDE a heap
# constructor's type argument — `Option<T>`, `Array<T>` — whose WASM
# representation is a pointer whatever `T` is, and whose clone body (`None`,
# `[]`) never reads it.
#
# Both shapes are therefore check-green, verify-clean, emit the `$Bool`
# default, and run correctly.  Pinned rather than fixed: if a future change
# makes a bare `@T` return inhabitable, or gives a parameterised return a
# `T`-dependent representation, these cells are what notices.
_RETURN_ONLY_OPTION = """\
private forall<T> fn mk(@Unit -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  None
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Int> = mk(());
  option_unwrap_or(@Option<Int>.0, 5)
}
"""

_RETURN_ONLY_ARRAY = """\
private forall<T> fn empty(@Unit -> @Array<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  []
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = array_append(empty(()), 1234);
  @Array<Int>.0[0]
}
"""


@pytest.mark.parametrize(
    ("source", "base", "expected"),
    [
        (_RETURN_ONLY_OPTION, "mk", 5),
        (_RETURN_ONLY_ARRAY, "empty", 1234),
    ],
    ids=["option_return", "array_return"],
)
def test_a_return_only_type_var_defaults_harmlessly(
    source: str, base: str, expected: int,
) -> None:
    """No argument mentions `T`, so the default stands — and is unobservable.

    Asserted on all three: the emitted clone IS the default, the differential
    holds, and the program runs correctly.  Naming the default explicitly is
    the point — a cell that only checked the value would pass just as well if
    the variable were inferred, and would not record that this shape is the
    one place a default still survives.
    """
    result = _compile_checked(source)
    assert _errors(result) == [], _errors(result)
    assert _clone_names(result.wat, base) == [f"{base}$Bool"], result.wat
    assert _run_checked(source) == expected
    codegen_set, verifier_set = _discovery_differential(source)
    assert codegen_set == verifier_set, (
        f"codegen {sorted(codegen_set)} != verifier {sorted(verifier_set)}"
    )
