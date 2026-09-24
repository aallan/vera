"""#1513 — a check-stage warning is one whose program compiles and runs.

Eight checker diagnostics for a name that resolves to nothing were warnings
— E200, E210, E214, E220, E230, E233, E320 and E322 — so `vera check` exited
0 and code generation then refused the program: E602 for a constructor, the
guard rail's uncoded "is not defined in this module" for a function or a
module call, and a raw WAT assembly error for an effect-qualified call.
Check did not imply compile.

Each is now an error with a fix a reader can follow, except for the one
shape that compiled: a constructor of a data type the file does not import
(`paint(Green)`, with `Colour` reaching the entry only through `paint`'s
signature).  That compiled until #1454 scoped code generation's constructor
tables to the namespace that uses them; it compiles again, through a
fallback class in `_namespace_ctor_projection` that answers the question
the checker's `_stranger_constructor` answers, and E210/E214 stay warnings
for it — naming the module to import from.  A pattern on such a constructor
never compiled, so E320/E322 are errors there too.

The instrument:

- **Enumeration** (`TestTheEnumeration`): the codes come from the registry
  `vera errors --json` prints, and a code is a check-stage WARNING when a
  diagnostic site under ``vera/checker/`` gives it with
  ``severity="warning"`` — read off the source through the enumerator
  `check_diagnostic_fields.py` uses, since the registry records no
  severity.  Every such code, and each of the eight, must have cells here.
- **Cells** (`TestCells`): one or more programs per code.  Every cell is
  either an error at check that `vera run` refuses with the same code, or
  a warning whose program compiles and runs with the expected output — or,
  for W001 alone, the typed hole spec §4.17 designs to check and not
  compile (E614).
- **The fallback's conditions** (`TestTheStrangerFallback`): the cases
  where a constructor of an unimported type denotes no single declaration
  are errors, and the module-body case compiles by the same rule.
- **The fixes** (`TestTheFixesWork`): applying the fix a diagnostic gives
  makes the program check clean and run.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import sys
from pathlib import Path
from typing import Any, Callable, NamedTuple, cast

import pytest

ROOT = Path(__file__).parent.parent

# The eight codes #1513 names.
_ISSUE_CODES = frozenset(
    {"E200", "E210", "E214", "E220", "E230", "E233", "E320", "E322"})

_HDR = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _main(body: str, *, imports: str = "", ret: str = "Int",
          effects: str = "pure") -> str:
    hdr = _HDR.replace("effects(pure)", f"effects({effects})")
    return (f"{imports}public fn main(@Unit -> @{ret})\n{hdr}{{\n"
            f"  {body}\n}}\n")


# ---------------------------------------------------------------------------
# Module fixtures
# ---------------------------------------------------------------------------

_MB = """\
module mb;

public data Colour {
  Red,
  Green
}
"""

_MA = """\
module ma;

import mb(Colour);

public fn paint(@Colour -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Colour.0 {
    Red -> 1,
    Green -> 2
  }
}

public fn pick(@Int -> @Colour)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 == 0 then {
    Red
  } else {
    Green
  }
}
"""

_BOXB = """\
module boxb;

public data Box {
  MkBox(Int)
}
"""

_BOXA = """\
module boxa;

import boxb(Box);

public fn unbox(@Box -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Box.0 {
    MkBox(@Int) -> @Int.0
  }
}

public fn mkbox(@Int -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{
  MkBox(@Int.0)
}
"""

_GBOXB = """\
module gboxb;

public data GBox<T> {
  GMk(T)
}
"""

_GBOXA = """\
module gboxa;

import gboxb(GBox);

public fn gunbox(@GBox<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @GBox<Int>.0 {
    GMk(@Int) -> @Int.0
  }
}
"""

_LIB = """\
module lib;

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}
"""

_TBASE = """\
module tbase;

public fn wrap40(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 40
}
"""

_TMID = """\
module tmid;

import tbase(wrap40);

public fn via_mid(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrap40(@Int.0)
}
"""

_PAINT = {"ma.vera": _MA, "mb.vera": _MB}
_BOX = {"boxa.vera": _BOXA, "boxb.vera": _BOXB}


class Cell(NamedTuple):
    """One program and what `vera check` and `vera run` must do with it.

    ``expect`` is ``"error"`` (check fails with the code as an error, and
    `vera run` refuses with the same code), ``"runs"`` (check passes with
    the code as a warning, and `vera run` prints ``value``), or ``"hole"``
    (check passes with the warning, and `vera compile` refuses with E614).
    """

    name: str
    files: dict[str, str]
    expect: str
    value: int | None = None
    stdout: str = ""


def _cell(name: str, main: str, expect: str, modules: dict[str, str] | None = None,
          value: int | None = None, stdout: str = "") -> Cell:
    return Cell(name, {"main.vera": main, **(modules or {})}, expect, value,
                stdout)


# Every code a check-stage diagnostic gives as a warning, and each of #1513's
# eight, with its cells.
CELLS: dict[str, tuple[Cell, ...]] = {
    "E200": (
        _cell("bare_call", _main("no_such_fn(1)"), "error"),
        _cell("transitive_only", _main("wrap40(1)",
                                       imports="import tmid(via_mid);\n\n"),
              "error", {"tmid.vera": _TMID, "tbase.vera": _TBASE}),
    ),
    "E210": (
        _cell("unknown", _main("match MkNope(1) {\n    _ -> 0\n  }"), "error"),
        _cell("unimported_type_arg",
              _main("unbox(MkBox(7))", imports="import boxa(unbox);\n\n"),
              "runs", _BOX, value=7),
        _cell("unimported_generic_arg",
              _main("gunbox(GMk(9))", imports="import gboxa(gunbox);\n\n"),
              "runs", {"gboxa.vera": _GBOXA, "gboxb.vera": _GBOXB}, value=9),
    ),
    "E214": (
        _cell("unknown", _main("match Nope {\n    _ -> 0\n  }"), "error"),
        _cell("unimported_type_arg",
              _main("paint(Green)", imports="import ma(paint);\n\n"),
              "runs", _PAINT, value=2),
    ),
    "E220": (
        _cell("unknown_effect", _main("Qx.op(1)"), "error"),
    ),
    "E230": (
        _cell("no_module", _main("nomod::f(1)"), "error"),
        _cell("transitive_module",
              _main("tbase::wrap40(1)", imports="import tmid(via_mid);\n\n"),
              "error", {"tmid.vera": _TMID, "tbase.vera": _TBASE}),
    ),
    "E233": (
        _cell("no_function", _main("lib::nope(1)", imports="import lib;\n\n"),
              "error", {"lib.vera": _LIB}),
    ),
    "E320": (
        _cell("unknown", _main("match 1 {\n    MkNope(@Int) -> 0,\n    _ -> 1\n  }"),
              "error"),
        _cell("unimported_type",
              _main("match mkbox(3) {\n    MkBox(@Int) -> @Int.0\n  }",
                    imports="import boxa(mkbox);\n\n"),
              "error", _BOX),
    ),
    "E322": (
        _cell("unknown", _main("match 1 {\n    Nope -> 0,\n    _ -> 1\n  }"),
              "error"),
        _cell("unimported_type",
              _main("match pick(1) {\n    Red -> 10,\n    Green -> 20\n  }",
                    imports="import ma(pick);\n\n"),
              "error", _PAINT),
    ),
    "E310": (
        _cell("unreachable_arm", _main("match 3 {\n    _ -> 1,\n    3 -> 2\n  }"),
              "runs", value=1),
    ),
    "W001": (
        _cell("typed_hole", _main("?"), "hole"),
    ),
    "W002": (
        _cell("eager_async", """\
private fn shout(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("tick");
  @Int.0
}

""" + _main("await(async(shout(5)))", effects="<Async, IO>"),
              "runs", value=5, stdout="tick"),
    ),
}


# ---------------------------------------------------------------------------
# Running the CLI in process
# ---------------------------------------------------------------------------


def _write(tmp_path: Path, files: dict[str, str]) -> Path:
    for name, source in files.items():
        (tmp_path / name).write_text(source, encoding="utf-8")
    return tmp_path / "main.vera"


def _cli(command: str, path: Path) -> dict[str, Any]:
    """Run `vera <command> --json <path>` in process and parse its output."""
    from vera import cli

    fns: dict[str, Callable[..., int]] = {
        "check": cli.cmd_check, "run": cli.cmd_run,
        "compile": cli.cmd_compile}
    fn = fns[command]
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = fn(str(path), as_json=True)
    try:
        payload: dict[str, Any] = json.loads(out.getvalue())
    except json.JSONDecodeError:  # pragma: no cover - a failure report
        raise AssertionError(
            f"vera {command} --json printed no JSON: "
            f"{out.getvalue()!r} {err.getvalue()!r}") from None
    payload["_rc"] = rc
    return payload


def _pairs(payload: dict[str, Any], key: str) -> list[tuple[str, str]]:
    return [(d["severity"], d.get("error_code") or "")
            for d in payload.get(key, [])]


def _load_script(name: str) -> Any:
    key = f"_ws1513_{name}"
    if key in sys.modules:
        return sys.modules[key]
    spec = importlib.util.spec_from_file_location(
        key, ROOT / "scripts" / f"{name}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[key] = module
    spec.loader.exec_module(module)
    return module


def _registry_codes() -> set[str]:
    """Every code `vera errors --json` prints."""
    from vera.cli import cmd_errors

    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        rc = cmd_errors(as_json=True)
    assert rc == 0
    return {item["code"] for item in json.loads(out.getvalue())["items"]}


def _check_stage_warning_codes() -> set[str]:
    """Every code a diagnostic site under ``vera/checker/`` gives with
    ``severity="warning"``, read off the source."""
    import ast as pyast

    fields = _load_script("check_diagnostic_fields")
    codes: set[str] = set()
    for path in sorted((ROOT / "vera" / "checker").rglob("*.py")):
        src = path.read_text(encoding="utf-8")
        tree = pyast.parse(src)
        rel = path.relative_to(ROOT).as_posix()
        for call in fields._diagnostic_call_sites(src, rel, tree):
            kws = {kw.arg: kw.value for kw in call.keywords}
            severity = kws.get("severity")
            if not (isinstance(severity, pyast.Constant)
                    and severity.value == "warning"):
                continue
            code = kws.get("error_code")
            assert isinstance(code, pyast.Constant), (
                f"{rel}:{call.lineno}: a warning whose code is not a literal "
                f"cannot be enumerated")
            codes.add(str(code.value))
    return codes


# ---------------------------------------------------------------------------
# The enumeration
# ---------------------------------------------------------------------------


class TestTheEnumeration:
    """Which codes need cells is derived, not listed by hand."""

    def test_every_check_stage_warning_is_a_registered_code(self) -> None:
        warnings = _check_stage_warning_codes()
        assert warnings, "the scan found no warning site: it has gone blind"
        assert warnings <= _registry_codes()

    def test_every_check_stage_warning_and_every_issue_code_has_cells(
        self,
    ) -> None:
        needed = _check_stage_warning_codes() | _ISSUE_CODES
        assert needed <= _registry_codes()
        assert sorted(needed - set(CELLS)) == []

    def test_the_warning_set_is_the_one_this_fix_leaves(self) -> None:
        """The eight are warnings only where they compile: E210 and E214 for
        a constructor of an unimported type.  A code that becomes a warning
        again must bring a cell that compiles and runs (the matrix below)."""
        assert _check_stage_warning_codes() == {
            "E210", "E214", "E310", "W001", "W002"}


# ---------------------------------------------------------------------------
# The cells
# ---------------------------------------------------------------------------


_CELL_PARAMS = [
    pytest.param(code, cell, id=f"{code}-{cell.name}")
    for code, cells in sorted(CELLS.items()) for cell in cells
]


class TestCells:
    """Check implies compile, one code at a time."""

    @pytest.mark.parametrize(("code", "cell"), _CELL_PARAMS)
    def test_cell(self, code: str, cell: Cell, tmp_path: Path) -> None:
        path = _write(tmp_path, cell.files)
        check = _cli("check", path)
        if cell.expect == "error":
            assert check["ok"] is False, check
            assert ("error", code) in _pairs(check, "diagnostics"), check
            assert ("warning", code) not in _pairs(check, "warnings"), check
            refused = [d for d in check["diagnostics"]
                       if d.get("error_code") == code]
            assert all(d.get("fix") for d in refused), refused
            run = _cli("run", path)
            assert run["ok"] is False
            assert ("error", code) in _pairs(run, "diagnostics"), run
            return
        assert check["ok"] is True, check
        assert _pairs(check, "diagnostics") == []
        assert ("warning", code) in _pairs(check, "warnings"), check
        if cell.expect == "hole":
            compiled = _cli("compile", path)
            assert compiled["ok"] is False
            assert ("error", "E614") in _pairs(compiled, "diagnostics")
            return
        assert cell.expect == "runs"
        run = _cli("run", path)
        assert run["ok"] is True, run
        assert run["value"] == cell.value
        assert run["stdout"].strip() == cell.stdout


# ---------------------------------------------------------------------------
# The constructor fallback's conditions
# ---------------------------------------------------------------------------


_LIGHT = """\
module light;

public data Light {
  Amber
}

public fn amber(@Unit -> @Light)
  requires(true)
  ensures(true)
  effects(pure)
{
  Amber
}
"""

_MA_WITH_LIGHT = _MA.replace(
    "import mb(Colour);", "import mb(Colour);\nimport light(Light);")

_MC_GREEN = """\
module mc;

public data Hue {
  Green,
  Blue
}

public fn blue(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  3
}
"""

_MB_PRIVATE = _MB.replace("public data Colour", "private data Colour")

_MD_COLOUR = """\
module md;

private data Colour {
  Blue
}

public fn four(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  4
}
"""

# A module whose own body uses a constructor of a type it does not import.
_MX = """\
module mx;

import ma(paint);

public fn run_x(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  paint(Green)
}
"""


class TestTheStrangerFallback:
    """A constructor of an unimported type compiles only when it denotes one
    declaration, decided the same way on both sides."""

    def _check(self, tmp_path: Path, files: dict[str, str]) -> dict[str, Any]:
        return _cli("check", _write(tmp_path, files))

    def test_a_value_of_another_type_is_refused_not_passed(
        self, tmp_path: Path,
    ) -> None:
        """The constructor is typed by its own declaration, so it cannot be
        passed where another type is expected (a flat lookup would have
        handed `paint` a `Light`'s tag)."""
        files = {"main.vera": _main("paint(Amber)",
                                    imports="import ma(paint);\n\n"),
                 "ma.vera": _MA_WITH_LIGHT, "mb.vera": _MB,
                 "light.vera": _LIGHT}
        check = self._check(tmp_path, files)
        assert check["ok"] is False
        assert ("warning", "E214") in _pairs(check, "warnings")
        assert [c for s, c in _pairs(check, "diagnostics") if s == "error"]

    def test_a_name_two_modules_declare_is_an_error_naming_both(
        self, tmp_path: Path,
    ) -> None:
        files = {"main.vera": _main("paint(Green) + blue(())",
                                    imports="import ma(paint);\nimport mc(blue);\n\n"),
                 **_PAINT, "mc.vera": _MC_GREEN}
        check = self._check(tmp_path, files)
        assert ("error", "E214") in _pairs(check, "diagnostics")
        (e214,) = [d for d in check["diagnostics"]
                   if d.get("error_code") == "E214"]
        assert "'import mb(Colour);'" in e214["fix"]
        # `mc` is already imported for `blue`, so its line extends that list.
        assert "'import mc(Hue, blue);'" in e214["fix"]

    def test_a_private_type_is_not_a_candidate(self, tmp_path: Path) -> None:
        main = _main("four(())", imports="import md(four);\n\n")
        files = {"main.vera": main.replace("four(())", "match Blue {\n    _ -> four(())\n  }"),
                 "md.vera": _MD_COLOUR}
        check = self._check(tmp_path, files)
        assert ("error", "E214") in _pairs(check, "diagnostics")

    def test_a_type_name_bound_here_is_not_overridden(
        self, tmp_path: Path,
    ) -> None:
        """This file declares its own `Colour`, so `Colour` cannot also name
        `mb`'s here: the constructor is refused."""
        main = ("import ma(paint);\n\nprivate data Colour {\n  Blue\n}\n\n"
                + _main("paint(Green)"))
        check = self._check(tmp_path, {"main.vera": main, **_PAINT})
        assert ("error", "E214") in _pairs(check, "diagnostics")

    def test_a_type_name_two_modules_declare_is_refused(
        self, tmp_path: Path,
    ) -> None:
        """`md` declares a private `Colour` of its own.  `Green` is `mb`'s
        alone, but the type name it would be typed by is not."""
        files = {"main.vera": _main(
            "paint(Green) + four(())",
            imports="import ma(paint);\nimport md(four);\n\n"),
            **_PAINT, "md.vera": _MD_COLOUR}
        check = self._check(tmp_path, files)
        assert ("error", "E214") in _pairs(check, "diagnostics")

    def test_a_module_body_compiles_by_the_same_rule(
        self, tmp_path: Path,
    ) -> None:
        """`mx`'s own body uses `Green`, whose type `mx` does not import:
        the checker warns in `mx`, and code generation resolves it in
        `mx`'s namespace (E602 before this fix, as in the entry)."""
        files = {"main.vera": _main("run_x(())",
                                    imports="import mx(run_x);\n\n"),
                 "mx.vera": _MX, **_PAINT}
        path = _write(tmp_path, files)
        check = _cli("check", path)
        assert check["ok"] is True, check
        warned = [d for d in check["warnings"] if d.get("error_code") == "E214"]
        assert len(warned) == 1
        assert warned[0]["location"]["file"].endswith("mx.vera")
        run = _cli("run", path)
        assert run["ok"] is True, run
        assert run["value"] == 2

    def test_code_generation_asks_the_modules_the_checker_asks(
        self, tmp_path: Path,
    ) -> None:
        """The fallback resolves a module body's constructor among the
        modules that module's checker sees, so a declaration outside them
        cannot make a name ambiguous on one side alone.  Asserted as an
        equality of the two tables, namespace by namespace, on a chain
        where the entry reaches more than any module does."""
        from types import SimpleNamespace

        from vera.checker.core import TypeChecker
        from vera.codegen.modules import CrossModuleMixin
        from vera.parser import parse_to_ast
        from vera.resolver import ModuleResolver

        files = {"main.vera": _main(
            "run_x(()) + blue(())",
            imports="import mx(run_x);\nimport mc(blue);\n\n"),
            "mx.vera": _MX, **_PAINT, "mc.vera": _MC_GREEN}
        path = _write(tmp_path, files)
        program = parse_to_ast(path.read_text(encoding="utf-8"))
        resolved = ModuleResolver(_root=tmp_path).resolve_imports(
            program, path)
        checker = TypeChecker(resolved_modules=resolved)
        checker_view: dict[tuple[str, ...] | None,
                           frozenset[tuple[str, ...]]] = {
            mod.path: frozenset(m.path for m in checker._modules_visible_to(mod))
            for mod in resolved
        }
        checker_view[None] = frozenset(m.path for m in resolved)
        codegen_view = CrossModuleMixin._build_namespace_module_reach(
            cast(Any, SimpleNamespace(_resolved_modules=resolved)))
        assert codegen_view == checker_view
        assert codegen_view[("mx",)] == {("ma",), ("mb",)}
        assert ("mc",) in codegen_view[None]


# ---------------------------------------------------------------------------
# The fixes work
# ---------------------------------------------------------------------------


class TestTheFixesWork:
    """A diagnostic's fix is an instruction: following it must work."""

    def test_importing_the_type_clears_the_constructor_warning(
        self, tmp_path: Path,
    ) -> None:
        path = _write(tmp_path, {
            "main.vera": _main("paint(Green)", imports="import ma(paint);\n\n"),
            **_PAINT})
        (warning,) = _cli("check", path)["warnings"]
        assert warning["fix"] == "Add the import: 'import mb(Colour);'."
        assert "module 'mb'" in warning["description"]
        path.write_text(
            _main("paint(Green)",
                  imports="import ma(paint);\nimport mb(Colour);\n\n"),
            encoding="utf-8")
        check = _cli("check", path)
        assert check["ok"] is True and check["warnings"] == [], check
        run = _cli("run", path)
        assert run["ok"] is True and run["value"] == 2, run

    def test_the_fix_extends_an_existing_import_of_the_module(
        self, tmp_path: Path,
    ) -> None:
        """When the file already imports the module selectively, the fix
        names that import with the name added, so following it leaves one
        import of the module; for the constructor warning and for an
        unresolved call alike."""
        mb_seven = _MB + (
            "\npublic fn seven(@Unit -> @Int)\n" + _HDR + "{\n  7\n}\n"
            "\npublic fn eight(@Unit -> @Int)\n" + _HDR + "{\n  8\n}\n")
        path = _write(tmp_path, {
            "main.vera": _main(
                "paint(Green) + seven(())",
                imports="import ma(paint);\nimport mb(seven);\n\n"),
            "ma.vera": _MA, "mb.vera": mb_seven})
        (warning,) = _cli("check", path)["warnings"]
        assert warning["fix"] == (
            "Add 'Colour' to this file's import of 'mb': "
            "'import mb(Colour, seven);'.")
        path.write_text(_main(
            "paint(Green) + seven(())",
            imports="import ma(paint);\nimport mb(Colour, seven);\n\n"),
            encoding="utf-8")
        check = _cli("check", path)
        assert check["ok"] is True and check["warnings"] == [], check
        assert _cli("run", path)["value"] == 9

        path.write_text(_main(
            "seven(()) + eight(())", imports="import mb(seven);\n\n"),
            encoding="utf-8")
        (error,) = _cli("check", path)["diagnostics"]
        assert error["error_code"] == "E200"
        assert "'import mb(eight, seven);'" in error["fix"]
        path.write_text(_main(
            "seven(()) + eight(())", imports="import mb(eight, seven);\n\n"),
            encoding="utf-8")
        assert _cli("run", path)["value"] == 15

    def test_a_module_imported_on_two_lines_admits_both_lists(
        self, tmp_path: Path,
    ) -> None:
        """`import lib(f);` beside `import lib(g);` admits `f` and `g`.

        The checker kept only the LAST list, so `f` was an E200 — harmless
        while E200 was a warning, since code generation reads every
        declaration and the program ran (printing 5).  As an error it would
        have refused a working program; the filter is now the union."""
        lib = _LIB + (
            "\npublic fn g(@Int -> @Int)\n" + _HDR + "{\n  @Int.0 + 2\n}\n")
        path = _write(tmp_path, {
            "main.vera": _main("f(1) + g(1)",
                               imports="import lib(f);\nimport lib(g);\n\n"),
            "lib.vera": lib})
        check = _cli("check", path)
        assert check["ok"] is True and check["warnings"] == [], check
        run = _cli("run", path)
        assert run["ok"] is True and run["value"] == 5, run

    def test_a_pattern_on_an_unimported_type_names_the_import(
        self, tmp_path: Path,
    ) -> None:
        path = _write(tmp_path, {
            "main.vera": _main(
                "match pick(1) {\n    Red -> 10,\n    Green -> 20\n  }",
                imports="import ma(pick);\n\n"),
            **_PAINT})
        errors = _cli("check", path)["diagnostics"]
        assert [d["error_code"] for d in errors] == ["E322", "E322"]
        assert all("'import mb(Colour);'" in d["fix"] for d in errors)

    def test_importing_a_transitive_function_makes_it_callable(
        self, tmp_path: Path,
    ) -> None:
        files = {"main.vera": _main("wrap40(1)",
                                    imports="import tmid(via_mid);\n\n"),
                 "tmid.vera": _TMID, "tbase.vera": _TBASE}
        path = _write(tmp_path, files)
        (error,) = _cli("check", path)["diagnostics"]
        assert error["error_code"] == "E200"
        assert "'import tbase(wrap40);'" in error["fix"]
        path.write_text(
            _main("wrap40(1)",
                  imports="import tmid(via_mid);\nimport tbase(wrap40);\n\n"),
            encoding="utf-8")
        run = _cli("run", path)
        assert run["ok"] is True and run["value"] == 41, run
