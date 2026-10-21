"""#1559 — an imported data type named like a prelude type, now reserved.

A module that imported `a`'s `public data Json { MyK(Int), MyN }` could not
construct it (#1559); the fix admitted an imported type's constructors
whatever the type's name.  #1469 then reserved every prelude type name: a
`data`, a `type` alias or a type parameter that takes one is refused at
check (E158), in the entry file and in a module alike, whatever its shape.
So every program this file once ran is refused at `a`'s declaration, and
the same program under a name the prelude does not use checks and runs as
it did.

The instrument:

- **The names** are derived from the checker's built-in registry: every
  built-in data type that is not a primitive or a built-in container
  (`TypeEnv().data_types` less those), which is the prelude's ADTs.
- **The matrix** (`TestTheMatrix`): for each name, a module declaring it is
  imported three ways — naming the type, by wildcard, and naming only the
  functions whose signatures carry it — by the entry and by a module.  Each
  cell is refused at check, and its first error is E158 at `a`'s
  declaration.  Each cell's control, the same program with the type
  renamed, checks clean, and where the prelude injects the name on demand
  it runs to the same value as before (168 with the annotations, 153
  without).
- **The rule** (`TestTheRule`): each shape the rule once decided (the bare
  name, the constructor names, a private declaration, a file's own
  declaration) is refused at its declaration the same way.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from vera import ast
from vera.checker.core import TypeChecker
from vera.environment import TypeEnv
from vera.prelude import inject_prelude, prelude_adt_names
from vera.types import PRIMITIVES
from tests import pipeline


def _names() -> list[str]:
    """Every built-in data type a module may declare a type named after."""
    reserved = set(TypeChecker._SPECIAL_CASED_BUILTIN_ADTS) | set(PRIMITIVES)
    return sorted(set(TypeEnv().data_types) - reserved)


def _always_injected() -> frozenset[str]:
    """The prelude data types every program compiles, whatever it names."""
    program = pipeline.parse("").program
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
    ran = pipeline.cli(command, "--json", path)
    try:
        payload: dict[str, Any] = ran.json()
    except json.JSONDecodeError:  # pragma: no cover - a failure report
        raise AssertionError(
            f"vera {command} --json printed no JSON: "
            f"{ran.stdout!r} {ran.stderr!r}") from None
    payload["_rc"] = ran.returncode
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


def _first_error(payload: dict[str, Any]) -> tuple[str, str, int]:
    """The first error's code, file name and line."""
    diag = next(d for d in payload.get("diagnostics", [])
                if d["severity"] == "error")
    return (diag.get("error_code") or "",
            Path(diag["location"]["file"]).name, diag["location"]["line"])


class TestTheIssueProgram:
    def test_it_is_refused_at_the_declaration(self, tmp_path: Path) -> None:
        """The issue's program: `a`'s `data Json` is refused (E158), and
        the same program with the type renamed checks clean and prints 41."""
        def write(root: Path, name: str) -> Path:
            root.mkdir()
            (root / "a.vera").write_text(
                f"module a;\n\npublic data {name} {{\n  MyJ(Int)\n}}\n\n"
                + _fn(f"unwrap(@{name} -> @Int)",
                      f"match @{name}.0 {{\n    MyJ(@Int) -> @Int.0\n  }}"),
                encoding="utf-8")
            (root / "b.vera").write_text(
                f"module b;\n\nimport a({name}, unwrap);\n\n"
                + _fn("val(@Int -> @Int)", "unwrap(MyJ(@Int.0))"),
                encoding="utf-8")
            (root / "main.vera").write_text(
                "import b(val);\n\n" + _fn("main(@Unit -> @Int)", "val(41)"),
                encoding="utf-8")
            return root / "main.vera"

        check = _cli("check", write(tmp_path / "cell", "Json"))
        assert check["ok"] is False, _said(check)
        assert _first_error(check) == ("E158", "a.vera", 3), _said(check)
        control = write(tmp_path / "control", "MyJson")
        check = _cli("check", control)
        assert check["ok"] is True, _said(check)
        assert check["diagnostics"] == [] and check["warnings"] == [], _said(check)
        run = _cli("run", control)
        assert run["ok"] is True and run["value"] == 41, _said(run)


class TestTheMatrix:
    """A prelude-named type is refused however it is imported."""

    @pytest.mark.parametrize("placement", ["entry", "module"])
    @pytest.mark.parametrize("imports", list(_IMPORTS))
    @pytest.mark.parametrize("name", _NAMES)
    def test_it_is_refused_where_another_name_runs(
        self, name: str, imports: str, placement: str, tmp_path: Path,
    ) -> None:
        cell = _write(tmp_path / "cell", name, imports, placement)
        control = _write(tmp_path / "control", f"Zq{name}", imports, placement)
        c_check, k_check = _cli("check", cell), _cli("check", control)
        assert c_check["ok"] is False, _said(c_check)
        assert _first_error(c_check) == ("E158", "a.vera", 3), _said(c_check)
        assert k_check["ok"] is True and _errors(k_check) == [], _said(k_check)
        if name not in _DEMAND_INJECTED:
            return
        k_run = _cli("run", control)
        annotated = placement == "module" and imports != "names_only_functions"
        expected = 168 if annotated else 153
        assert k_run["ok"] is True and k_run["value"] == expected, _said(k_run)


class TestTheRule:
    """Each shape the import rule once decided is refused at the
    declaration that takes the prelude's name."""

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
        """`b` imports `a`'s `Json` and matches `json_parse`'s result over
        the prelude's six constructors: `a`'s declaration is refused, and
        the match on the prelude's `Json` is not."""
        main = self._b(
            tmp_path, _module_a("Json"), "import a(Json, unwrap, mk);",
            "match json_parse(\"true\") {\n    Ok(@Json) -> match @Json.0 {\n"
            "      JNull -> 0,\n      JBool(@Bool) -> 1,\n"
            "      JNumber(@Float64) -> 2,\n      JString(@String) -> 3,\n"
            "      JArray(@Array<Json>) -> 4,\n"
            "      JObject(@Map<String, Json>) -> 5\n    },\n"
            "    Err(@String) -> 9\n  }")
        check = _cli("check", main)
        assert _errors(check) == ["E158"], _said(check)
        assert _first_error(check) == ("E158", "a.vera", 3), _said(check)

    def test_the_prelude_keeps_its_constructor_names(
        self, tmp_path: Path,
    ) -> None:
        """`a`'s `Json` declares a `JNull` of its own: the declaration is
        refused at check, where code generation once refused it (E621)."""
        a_source = (
            "module a;\n\npublic data Json {\n  JNull,\n  MyK(Int)\n}\n\n"
            + _fn("unwrap(@Json -> @Int)",
                  "match @Json.0 {\n    JNull -> 7,\n    _ -> 0\n"
                  "  }"))
        main = self._b(
            tmp_path, a_source, "import a(Json, unwrap);",
            "string_length(json_stringify(JNull))")
        check = _cli("check", main)
        assert _errors(check) == ["E158"], _said(check)
        assert _first_error(check) == ("E158", "a.vera", 3), _said(check)

    def test_a_private_type_of_the_name_is_refused(
        self, tmp_path: Path,
    ) -> None:
        """A private declaration of the name is refused as a public one is;
        the import that names it reports nothing further."""
        main = self._b(
            tmp_path,
            _module_a("Json").replace("public data Json", "private data Json")
            .replace("public fn unwrap", "private fn unwrap")
            .replace("public fn mk", "private fn mk")
            + "\n" + _fn("ten(@Int -> @Int)", "10"),
            "import a(Json, ten);", "ten(@Int.0)")
        check = _cli("check", main)
        assert _errors(check) == ["E158"], _said(check)
        assert _first_error(check) == ("E158", "a.vera", 3), _said(check)

    def test_a_type_the_file_declares_is_refused(
        self, tmp_path: Path,
    ) -> None:
        """`b`'s own `private data Json` is refused as `a`'s is."""
        (tmp_path / "a.vera").write_text(_module_a("Json"), encoding="utf-8")
        (tmp_path / "b.vera").write_text(
            "module b;\n\nimport a(unwrap, mk);\n\n"
            "private data Json {\n  Own(Bool)\n}\n\n"
            + _fn("val(@Int -> @Int)", "unwrap(mk(@Int.0))"),
            encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            "import b(val);\n\n" + _fn("main(@Unit -> @Int)", "val(41)"),
            encoding="utf-8")
        check = _cli("check", tmp_path / "main.vera")
        refused = sorted(
            (d.get("error_code"), Path(d["location"]["file"]).name)
            for d in check["diagnostics"] if d["severity"] == "error")
        assert refused == [("E158", "a.vera"), ("E158", "b.vera")], _said(check)
