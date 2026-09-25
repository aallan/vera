"""#1559 — an imported data type named like a prelude type.

A module that imports `a`'s `public data Json { MyK(Int), MyN }` could not
construct it: `MyK` was an unknown constructor.  On `main` that was an E210
*warning* and the program ran, because code generation admits the import's
constructors; #1513 made E210 an error.  The checker never admitted them:
its per-module harvest kept a module's data declarations by NAME, dropping
every one whose name is a built-in data type's, so a module's own `Json`
never reached the registry an importer's constructors are injected from —
nor the one the unimported-type fallback (#1513) searches, which on top of
that refused any type whose name was in scope, the prelude's included.

The rule, from spec §8.3.3 and §8.5.4 with §8.5.2.2: importing a data type
admits its constructors whatever the type's name.  The bare type name stays
with its incumbent — where the prelude declares a type of that name, the
prelude's, since an import never wins a name the prelude owns — and so does
any constructor name the prelude declares.  A constructor of such a type
reached only through a signature resolves as #1513's fallback resolves any
other: the prelude's own type of the name does not bar it, a type the file
declares or imports does.

The instrument:

- **The names** are derived from the checker's built-in registry: every
  built-in data type a declaration may take (`TypeEnv().data_types` less the
  names E158 reserves).
- **The matrix** (`TestTheMatrix`): for each name, a module declaring it is
  imported three ways — naming the type, by wildcard, and naming only the
  functions whose signatures carry it — by the entry and by a module.  One
  program per cell constructs it (with fields and nullary), matches it (with
  a wildcard and nested in `Some`) and, from a module that imports the
  type, annotates it (a `let`, a parameter, `Option<…>`).  Each cell is held
  to the same program with the type renamed to a name the prelude does not
  use: the same errors and warnings at check, and, where the prelude injects
  the name on demand, the same value at run (168 with the annotations, 153
  without).
- **The rule** (`TestTheRule`): the prelude keeps the bare type name and
  its constructor names, a private type of the name is not importable, and
  a type the file declares still bars the fallback.
"""

from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
from typing import Any, Callable

import pytest

from vera import ast
from vera.checker.core import TypeChecker
from vera.environment import TypeEnv
from vera.parser import parse_to_ast
from vera.prelude import inject_prelude, prelude_adt_names
from vera.types import PRIMITIVES


def _names() -> list[str]:
    """Every built-in data type a module may declare a type named after."""
    reserved = set(TypeChecker._SPECIAL_CASED_BUILTIN_ADTS) | set(PRIMITIVES)
    return sorted(set(TypeEnv().data_types) - reserved)


def _always_injected() -> frozenset[str]:
    """The prelude data types every program compiles, whatever it names."""
    program = parse_to_ast("")
    inject_prelude(program)
    return frozenset(tld.decl.name for tld in program.declarations
                     if isinstance(tld.decl, ast.DataDecl))


_NAMES = _names()
# The prelude injects these only when the entry program uses them, so a
# module's own declaration of one stands alone and compiles (spec §8.4.1);
# the rest contend with a declaration every program compiles (E621), or are
# built-in layouts, and do not compile under a module's differing shape.
_DEMAND_INJECTED = sorted(prelude_adt_names() - _always_injected())

_HDR = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _fn(sig: str, body: str, vis: str = "public") -> str:
    return f"{vis} fn {sig}\n{_HDR}{{\n  {body}\n}}\n"


def _module_a(name: str) -> str:
    return (
        f"module a;\n\npublic data {name} {{\n  MyK(Int),\n  MyN\n}}\n\n"
        + _fn(f"unwrap(@{name} -> @Int)",
              f"match @{name}.0 {{\n    MyK(@Int) -> @Int.0,\n"
              f"    MyN -> 100\n  }}")
        + "\n" + _fn(f"mk(@Int -> @{name})", "MyK(@Int.0)"))


# A construction with fields (41) and a nullary one (100), a match on the
# imported function's result with a wildcard (5), and one nested in `Some`
# (7): 153.  The entry names no type, since naming one of the on-demand
# prelude types there draws the prelude's own declaration in (E621).
_ENTRY_BODY = (
    "unwrap(MyK(@Int.0)) + unwrap(MyN)"
    " + match mk(5) {\n    MyK(@Int) -> @Int.0,\n    _ -> 0\n  }"
    " + match Some(mk(7)) {\n    Some(MyK(@Int)) -> @Int.0,\n    _ -> 0\n  }")


def _module_body(name: str) -> str:
    """The entry's four, plus a `let` of a construction (3), a parameter
    (2), a `let` of the function's result (6) and `Option<…>` (4): 168."""
    return (
        f"{_ENTRY_BODY}\n  + {{\n    let @{name} = MyK(3);\n"
        f"    unwrap(@{name}.0)\n  }}"
        " + unwrap(id2(mk(2)))"
        f" + {{\n    let @{name} = mk(6);\n    unwrap(@{name}.0)\n  }}"
        f" + match opt(4) {{\n    Some(@{name}) -> unwrap(@{name}.0),\n"
        "    None -> 0\n  }")


def _module_helpers(name: str) -> str:
    return (_fn(f"id2(@{name} -> @{name})", f"@{name}.0", vis="private")
            + "\n" + _fn(f"opt(@Int -> @Option<{name}>)", "Some(mk(@Int.0))",
                         vis="private"))


_IMPORTS = {
    "names_the_type": "import a({name}, unwrap, mk);",
    "wildcard": "import a;",
    "names_only_functions": "import a(unwrap, mk);",
}


def _write(root: Path, name: str, imports: str, placement: str) -> Path:
    root.mkdir(parents=True, exist_ok=True)
    (root / "a.vera").write_text(_module_a(name), encoding="utf-8")
    line = _IMPORTS[imports].format(name=name)
    main = _fn("main(@Unit -> @Int)", "val(41)")
    if placement == "entry":
        (root / "main.vera").write_text(
            f"{line}\n\n" + _fn("val(@Int -> @Int)", _ENTRY_BODY) + "\n" + main,
            encoding="utf-8")
    elif imports == "names_only_functions":
        # A file that does not import the type does not name it: under
        # another name that is a type out of scope, which code generation
        # cannot lay out, and under the prelude's name it is the prelude's.
        (root / "b.vera").write_text(
            f"module b;\n\n{line}\n\n"
            + _fn("val(@Int -> @Int)", _ENTRY_BODY), encoding="utf-8")
        (root / "main.vera").write_text("import b(val);\n\n" + main,
                                        encoding="utf-8")
    else:
        (root / "b.vera").write_text(
            f"module b;\n\n{line}\n\n" + _module_helpers(name) + "\n"
            + _fn("val(@Int -> @Int)", _module_body(name)), encoding="utf-8")
        (root / "main.vera").write_text("import b(val);\n\n" + main,
                                        encoding="utf-8")
    return root / "main.vera"


def _cli(command: str, path: Path) -> dict[str, Any]:
    """Run `vera <command> --json <path>` in process and parse its output."""
    from vera import cli

    fns: dict[str, Callable[..., int]] = {
        "check": cli.cmd_check, "run": cli.cmd_run}
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = fns[command](str(path), as_json=True)
    try:
        payload: dict[str, Any] = json.loads(out.getvalue())
    except json.JSONDecodeError:  # pragma: no cover - a failure report
        raise AssertionError(
            f"vera {command} --json printed no JSON: "
            f"{out.getvalue()!r} {err.getvalue()!r}") from None
    payload["_rc"] = rc
    return payload


def _said(payload: dict[str, Any]) -> str:
    """A failure message that leads with what the CLI reported."""
    diags = payload.get("diagnostics", []) + payload.get("warnings", [])
    return "; ".join(
        f"{d['severity']} {d.get('error_code') or '-'}: "
        f"{d['description'][:160]}" for d in diags) or repr(payload)[:400]


def _codes(payload: dict[str, Any], key: str) -> list[tuple[str, str]]:
    return [(d["severity"], d.get("error_code") or "")
            for d in payload.get(key, [])]


def _errors(payload: dict[str, Any]) -> list[str]:
    return [d.get("error_code") or "" for d in payload.get("diagnostics", [])
            if d["severity"] == "error"]


class TestTheNames:
    def test_the_derivation_holds_the_names_the_issue_names(self) -> None:
        assert {"Json", "HtmlNode", "Request", "Response"} <= set(
            _DEMAND_INJECTED)
        assert set(_DEMAND_INJECTED) <= set(_NAMES)
        # A name E158 reserves is no declaration's, so it is no cell's.
        assert "Future" not in _NAMES and "Int" not in _NAMES


class TestTheIssueProgram:
    def test_it_checks_clean_and_prints_41(self, tmp_path: Path) -> None:
        (tmp_path / "a.vera").write_text(
            "module a;\n\npublic data Json {\n  MyJ(Int)\n}\n\n"
            + _fn("unwrap(@Json -> @Int)",
                  "match @Json.0 {\n    MyJ(@Int) -> @Int.0\n  }"),
            encoding="utf-8")
        (tmp_path / "b.vera").write_text(
            "module b;\n\nimport a(Json, unwrap);\n\n"
            + _fn("val(@Int -> @Int)", "unwrap(MyJ(@Int.0))"),
            encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            "import b(val);\n\n" + _fn("main(@Unit -> @Int)", "val(41)"),
            encoding="utf-8")
        check = _cli("check", tmp_path / "main.vera")
        assert check["ok"] is True, _said(check)
        assert check["diagnostics"] == [] and check["warnings"] == [], _said(check)
        run = _cli("run", tmp_path / "main.vera")
        assert run["ok"] is True and run["value"] == 41, _said(run)


class TestTheMatrix:
    """A prelude-named type is imported as a type of any other name is."""

    @pytest.mark.parametrize("placement", ["entry", "module"])
    @pytest.mark.parametrize("imports", list(_IMPORTS))
    @pytest.mark.parametrize("name", _NAMES)
    def test_it_checks_and_runs_as_under_another_name(
        self, name: str, imports: str, placement: str, tmp_path: Path,
    ) -> None:
        cell = _write(tmp_path / "cell", name, imports, placement)
        control = _write(tmp_path / "control", f"Zq{name}", imports, placement)
        c_check, k_check = _cli("check", cell), _cli("check", control)
        assert _codes(c_check, "diagnostics") == [], _said(c_check)
        assert _codes(c_check, "diagnostics") == _codes(
            k_check, "diagnostics"), (c_check, k_check)
        assert _codes(c_check, "warnings") == _codes(
            k_check, "warnings"), (c_check, k_check)
        if name not in _DEMAND_INJECTED:
            return
        c_run, k_run = _cli("run", cell), _cli("run", control)
        annotated = placement == "module" and imports != "names_only_functions"
        expected = 168 if annotated else 153
        assert k_run["ok"] is True and k_run["value"] == expected, _said(k_run)
        assert c_run["ok"] is True and c_run["value"] == expected, _said(c_run)


class TestTheRule:
    """What the import binds, and what it leaves with the prelude."""

    def _b(self, tmp_path: Path, a_source: str, imports: str,
           body: str) -> Path:
        (tmp_path / "a.vera").write_text(a_source, encoding="utf-8")
        (tmp_path / "b.vera").write_text(
            f"module b;\n\n{imports}\n\n" + _fn("val(@Int -> @Int)", body),
            encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            "import b(val);\n\n" + _fn("main(@Unit -> @Int)", "val(41)"),
            encoding="utf-8")
        return tmp_path / "main.vera"

    def test_the_prelude_keeps_the_type_name(self, tmp_path: Path) -> None:
        """`b` imports `a`'s `Json`, and a match on `json_parse`'s result
        covering the prelude's six constructors is exhaustive there: the
        bare name `Json` is still the prelude's type (§8.5.2.2).  Were the
        import to take the name, the match would be judged against `a`'s
        two constructors and refused (E311)."""
        main = self._b(
            tmp_path, _module_a("Json"), "import a(Json, unwrap, mk);",
            "match json_parse(\"true\") {\n    Ok(@Json) -> match @Json.0 {\n"
            "      JNull -> 0,\n      JBool(@Bool) -> 1,\n"
            "      JNumber(@Float64) -> 2,\n      JString(@String) -> 3,\n"
            "      JArray(@Array<Json>) -> 4,\n"
            "      JObject(@Map<String, Json>) -> 5\n    },\n"
            "    Err(@String) -> 9\n  } + unwrap(MyK(@Int.0))")
        check = _cli("check", main)
        assert check["ok"] is True, _said(check)
        assert _codes(check, "diagnostics") == [], _said(check)

    def test_the_prelude_keeps_its_constructor_names(
        self, tmp_path: Path,
    ) -> None:
        """`a`'s `Json` declares a `JNull` of its own.  In `b`, which imports
        `a`'s `Json`, `JNull` is still the prelude's — `json_stringify`
        renders it "null" — while `MyK` is `a`'s: 4 + 41."""
        a_source = (
            "module a;\n\npublic data Json {\n  JNull,\n  MyK(Int)\n}\n\n"
            + _fn("unwrap(@Json -> @Int)",
                  "match @Json.0 {\n    JNull -> 7,\n    MyK(@Int) -> @Int.0\n"
                  "  }"))
        main = self._b(
            tmp_path, a_source, "import a(Json, unwrap);",
            "string_length(json_stringify(JNull)) + unwrap(MyK(@Int.0))")
        check = _cli("check", main)
        assert check["ok"] is True and _codes(check, "warnings") == [], _said(check)
        run = _cli("run", main)
        assert run["ok"] is True and run["value"] == 45, _said(run)

    def test_a_private_type_of_the_name_is_not_importable(
        self, tmp_path: Path,
    ) -> None:
        """Importing a private declaration is E150 (§8.3.2), whatever the
        declaration's name: the harvest dropped a prelude-named one, so the
        import was never checked against it."""
        main = self._b(
            tmp_path,
            _module_a("Json").replace("public data Json", "private data Json")
            .replace("public fn unwrap", "private fn unwrap")
            .replace("public fn mk", "private fn mk")
            + "\n" + _fn("ten(@Int -> @Int)", "10"),
            "import a(Json, ten);", "ten(@Int.0)")
        check = _cli("check", main)
        assert _errors(check) == ["E150"], _said(check)

    def test_a_type_the_file_declares_still_bars_the_fallback(
        self, tmp_path: Path,
    ) -> None:
        """`b` declares its own `Json` and reaches `a`'s only through `mk`'s
        signature: `MyK` is refused (E210), as #1513 refuses a constructor
        whose type name the file binds.  Only the prelude's own type of the
        name leaves the fallback open."""
        (tmp_path / "a.vera").write_text(_module_a("Json"), encoding="utf-8")
        (tmp_path / "b.vera").write_text(
            "module b;\n\nimport a(unwrap, mk);\n\n"
            "private data Json {\n  Own(Bool)\n}\n\n"
            + _fn("val(@Int -> @Int)", "unwrap(MyK(@Int.0))"),
            encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            "import b(val);\n\n" + _fn("main(@Unit -> @Int)", "val(41)"),
            encoding="utf-8")
        check = _cli("check", tmp_path / "main.vera")
        assert _errors(check) == ["E210"], _said(check)
