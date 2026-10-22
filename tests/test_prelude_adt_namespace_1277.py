"""#1277: a module's data type named like a prelude type, after #1469.

The shape #1277 found — a module's `data Json` (or any prelude type's name)
contending with the prelude's for one layout slot in code generation — is
refused at check since #1469 reserved the prelude's type names (E158).  The
code generation rail that refused it later (E621) and the membership floor
that kept the prelude's type in other namespaces are gone with it (#1694):
a module's type is named by its link name, which no prelude type shares.

What stays here is what still holds of the shape: the CLI refuses it, the
control (a name the prelude does not reserve) compiles, and the set of the
prelude's data types the reservation reads is the set the prelude injects.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests import pipeline
from vera import ast
from vera.codegen.core import CodeGenerator
from vera.parser import parse_file
from vera.prelude import inject_prelude
from vera.transform import transform


# ---------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------

# A module-local `data Json` whose constructor is deliberately NOT one of
# the prelude's six, so "which layout is registered under `Json`" is
# answerable from the constructor names alone.
_JLIB_OWN_JSON = """
private data Json {
  JBlob(Int)
}

public fn blob_size(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match JBlob(@Int.0) {
    JBlob(@Int) -> @Int.0
  }
}
"""

# The entry program uses the PRELUDE's `Json` — `inject_prelude` is
# demand-driven off this file, so naming the type here is what makes the
# prelude inject `data Json` at all.
_MAIN_USES_PRELUDE_JSON = """
import jlib(blob_size);

public fn depth(@Json -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  json_array_length(@Json.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  blob_size(7)
}
"""

def _compile(tmp_path: Path, files: dict[str, str]) -> CodeGenerator:
    """Write *files*, compile ``main.vera``, hand back the generator."""
    main_path = pipeline.write_tree(tmp_path, files)
    checked = pipeline.check(main_path, root=tmp_path)
    _ = checked.program  # raises the parse or transform error
    compiled = pipeline.compile(
        main_path, modules=checked.resolved or [])
    result = compiled.result
    gen = compiled.generator
    assert gen is not None
    gen._result = result  # type: ignore[attr-defined]
    return gen


def test_the_cli_refuses_a_modules_prelude_named_type(tmp_path: Path) -> None:
    """`vera check` and `vera compile` exit non-zero on the contention shape.

    At the branch point every diagnostic in this program was a warning, so
    `cmd_compile` returned 0 over a module with the function silently
    missing.  The module's `data Json` takes a reserved prelude name
    (#1469), so the check refuses it now, before code generation runs.
    """
    from vera.cli import cmd_check, cmd_compile

    tmp_path.mkdir(parents=True, exist_ok=True)
    (tmp_path / "jlib.vera").write_text(_JLIB_OWN_JSON, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    main_path.write_text(_MAIN_USES_PRELUDE_JSON, encoding="utf-8")
    assert cmd_check(str(main_path), quiet=True) == 1
    assert cmd_compile(str(main_path), wat=True) == 1


_WIDGET_A = "private data Widget {\n  WA(Int)\n}"
_WIDGET_B = "private data Widget {\n  WB(Int)\n}"

_DECL_BODY = {
    _WIDGET_A: "match WA(@Int.0) {\n    WA(@Int) -> @Int.0\n  }",
    _WIDGET_B: "match WB(@Int.0) {\n    WB(@Int) -> @Int.0\n  }",
}


def _two_module_gen(
    tmp_path: Path, decl_a: str, decl_b: str, *,
    a_first: bool, uses_ordering: bool = True,
) -> CodeGenerator:
    """Compile two modules that each declare one name; hand back the generator.

    *a_first* decides which module the ENTRY imports first, so the two
    parametrizations really are two different programs.  That is the whole
    point of the cases below — the defect they pin was order-dependent, and
    a fixture with a fixed import order would run the same program twice
    and claim to have covered both.
    """
    def lib(fn: str, decl: str) -> str:
        return f"""{decl}

public fn {fn}(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {_DECL_BODY[decl]}
}}
"""
    first, second = ("alib", "blib") if a_first else ("blib", "alib")
    fn1, fn2 = ("afn", "bfn") if a_first else ("bfn", "afn")
    consume = """
public fn consume(@Ordering -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Ordering.0 {
    Less -> 0,
    Equal -> 1,
    Greater -> 2
  }
}
""" if uses_ordering else ""
    entry = f"""import {first}({fn1});
import {second}({fn2});
{consume}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {fn1}(1) + {fn2}(2)
}}
"""
    return _compile(tmp_path, {
        "alib.vera": lib("afn", decl_a),
        "blib.vera": lib("bfn", decl_b),
        "main.vera": entry,
    })


def _two_module_cell(
    tmp_path: Path, decl_a: str, decl_b: str, *,
    a_first: bool, uses_ordering: bool = True,
) -> tuple[list[str], list[str]]:
    """(codes, exports) for two modules that each declare one name."""
    gen = _two_module_gen(
        tmp_path, decl_a, decl_b,
        a_first=a_first, uses_ordering=uses_ordering,
    )
    result = gen._result  # type: ignore[attr-defined]
    return (
        sorted({d.error_code for d in result.diagnostics if d.error_code}),
        sorted(result.exports),
    )


@pytest.mark.parametrize("a_first", [True, False], ids=["alib1st", "blib1st"])
def test_two_modules_declaring_a_NON_prelude_name_are_admitted(
    tmp_path: Path, a_first: bool,
) -> None:
    """The control: two modules' differently-shaped `data Widget`.

    `Widget` is nobody's prelude type, so it is not reserved: each module's
    declaration is its own type, under `mod$<path>$Widget` (#1694), and the
    program compiles with every function in the exports.  The same shape
    under a prelude type's name is refused at check (E158).
    """
    codes, exports = _two_module_cell(
        tmp_path, _WIDGET_A, _WIDGET_B, a_first=a_first, uses_ordering=False)
    assert codes == [], codes
    assert exports == ["main"], exports


def test_prelude_adt_names_are_exactly_what_the_prelude_injects(
    tmp_path: Path,
) -> None:
    """`prelude_adt_names()` and `inject_prelude` cannot drift apart.

    The floor is only as complete as this set, and the set is only right
    if it names every ADT the injector can lay down.  So it is compared
    against the injector itself, run over a program that demands every
    conditional block — not against a list repeated in the test.
    """
    from vera.prelude import prelude_adt_names

    demands_everything = """
public fn everything(@Json, @HtmlNode, @Request -> @Response)
  requires(true)
  ensures(true)
  effects(pure)
{
  Response(200, map_new(), "")
}
"""
    program = transform(parse_file(str(_write(
        tmp_path, "all.vera", demands_everything))))
    inject_prelude(program)
    injected = frozenset(
        tld.decl.name for tld in program.declarations
        if isinstance(tld.decl, ast.DataDecl)
    )
    assert injected == prelude_adt_names(), (
        sorted(injected ^ prelude_adt_names()))
    # A tripwire on the set itself: the four beyond the Pass-0.5 built-in
    # snapshot are the ones the floor exists for.
    assert {"Json", "HtmlNode", "Request", "Response"} <= prelude_adt_names()


def _write(tmp_path: Path, name: str, text: str) -> Path:
    tmp_path.mkdir(parents=True, exist_ok=True)
    path = tmp_path / name
    path.write_text(text, encoding="utf-8")
    return path
