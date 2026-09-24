"""A module is compiled in ITS OWN namespace, imports included (#1493, #1275).

Code generation registered each imported module's declarations in a
throwaway generator holding none of the module's imports, so a data type the
module imported — and returned, or took — had no WASM representation there:
``pick(@Int -> @Colour)`` registered as ``(['i64'], 'unsupported')``, and a
direct ``match`` on the call, in the importer or in the module's own bodies,
dropped the enclosing function (E602, then E620).  The same declarations
compiled as the ENTRY registered ``(['i64'], 'i32')``.

The registrar now sees what the module imports, from the one derivation the
checker's module registration reads (``vera.module_view``), and so does the
membership each module's bodies compile under — spelled through the module's
own #1317 renames, which rewrite a contended type's references but not the
import lists naming it.

* :class:`TestTheReportedPrograms` — #1493's reproduction.
* :class:`TestSignaturesDoNotDependOnTheEntry` — the differential the issue
  proposes: for every module of every multi-module program (the corpus's and
  a set of topologies), the WASM signatures its functions get when the
  module is IMPORTED equal the ones they get when it is the ENTRY.
* :class:`TestRegistrationIsMemoised` — #1275: each module's checker
  registration is built once per run, not once per checker.
* :class:`TestOneDerivation` — the shared derivation's own contract.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import pytest

from vera import ast
from vera.checker import typecheck, typecheck_with_artifacts
from vera.checker.core import TypeChecker
from vera.codegen.core import CodeGenerator
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver

from tests.test_check_implies_compile import (
    FLOW_CELLS,
    TOPOLOGIES,
    corpus_programs,
    pipeline,
    run_main,
)

_ROOT = Path(__file__).resolve().parent.parent
_CONTRACT = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

_MB = "module mb;\n\npublic data Colour {\n  Red,\n  Green\n}\n"
_MA = (
    "module ma;\n\nimport mb(Colour);\n\n"
    "public fn pick(@Int -> @Colour)\n" + _CONTRACT
    + "{\n  if @Int.0 > 0 then { Red } else { Green }\n}\n\n"
    "public fn which(@Int -> @Int)\n" + _CONTRACT
    + "{\n  match pick(@Int.0) {\n    Red -> 1,\n    Green -> 2\n  }\n}\n"
)


def _main(imports: str, body: str) -> str:
    return (imports + "\npublic fn main(@Unit -> @Int)\n" + _CONTRACT
            + "{\n  " + body + "\n}\n")


class TestTheReportedPrograms:
    """#1493's reproduction, in the importer and in the module's own body."""

    def test_a_direct_match_on_the_result(self, tmp_path: Path) -> None:
        out = pipeline(tmp_path, {
            "mb.vera": _MB, "ma.vera": _MA,
            "main.vera": _main("import ma(pick);\nimport mb(Colour);\n",
                               "match pick(1) {\n    Red -> 1,\n"
                               "    Green -> 2\n  }"),
        })
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", 1)

    def test_the_modules_own_body(self, tmp_path: Path) -> None:
        """`which` matches on `pick` inside `ma`, compiled as an import."""
        out = pipeline(tmp_path, {
            "mb.vera": _MB, "ma.vera": _MA,
            "main.vera": _main("import ma(which);\n", "which(1)"),
        })
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", 1)

    def test_a_contended_type_the_module_returns(
        self, tmp_path: Path,
    ) -> None:
        """#1317 renames `deep`'s `Shape` apart from `other`'s; `mid` names
        it through `import deep(Shape)` and returns it."""
        out = pipeline(tmp_path, {
            "deep.vera": "module deep;\n\npublic data Shape { Sq(Int) }\n",
            "mid.vera": (
                "module mid;\n\nimport deep(Shape);\n\n"
                "public fn mk(@Int -> @Shape)\n" + _CONTRACT
                + "{\n  Sq(@Int.0)\n}\n\npublic fn mone(@Int -> @Int)\n"
                + _CONTRACT + "{\n  match mk(@Int.0) {\n"
                "    Sq(@Int) -> @Int.0\n  }\n}\n"
            ),
            "other.vera": (
                "module other;\n\npublic data Shape { Cr(Bool) }\n\n"
                "public fn oone(@Int -> @Int)\n" + _CONTRACT
                + "{\n  match Cr(true) {\n    Cr(@Bool) -> if @Bool.0 then "
                "{ @Int.0 } else { 0 }\n  }\n}\n"
            ),
            "main.vera": _main("import mid(mone);\nimport other(oone);\n",
                               "mone(3) + oone(4)"),
        })
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", 7)

    def test_a_second_import_of_one_module_keeps_the_first_list(
        self, tmp_path: Path,
    ) -> None:
        """`import mb(Colour); import mb(Shade);` admits BOTH names — the
        union, in the checker and in code generation alike."""
        mb = _MB + "\npublic data Shade {\n  Dark\n}\n"
        out = pipeline(tmp_path, {
            "mb.vera": mb, "ma.vera": _MA,
            "main.vera": _main(
                "import ma(pick);\nimport mb(Colour);\nimport mb(Shade);\n",
                "let @Colour = pick(1);\n  match @Colour.0 {\n"
                "    Red -> 1,\n    Green -> 2\n  }"),
        })
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", 1)


# =====================================================================
# The differential: signatures do not depend on which file is the entry
# =====================================================================

def _generator(entry: Path) -> CodeGenerator:
    """The generator ``vera compile`` builds for *entry*, after compiling it.

    The whole pipeline, not a hand-picked prefix of its passes: a prefix
    stopped before the prelude injection, so a signature naming one of the
    prelude's demand-injected types (``Json``, ``HtmlNode``, ``Request``,
    ``Response``) read ``unsupported`` on BOTH sides and the differential
    could not see a module's measurement of it (PR #1508 review).  What is
    compared is what the compile leaves registered.
    """
    source = entry.read_text(encoding="utf-8")
    program = parse_to_ast(source)
    mods = ModuleResolver(_root=entry.parent).resolve_imports(program, entry)
    _, arts = typecheck_with_artifacts(
        program, source, file=str(entry), resolved_modules=mods,
        collect_module_artifacts=True,
    )
    gen = CodeGenerator(
        source=source, file=str(entry), resolved_modules=mods,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    gen.compile_program(program)
    return gen


def _own_functions(program: ast.Program) -> list[str]:
    return [
        tld.decl.name for tld in program.declarations
        if isinstance(tld.decl, ast.FnDecl) and not tld.decl.forall_vars
    ]


def signature_mismatches(entry: Path) -> list[str]:
    """Every module function whose imported signature differs from the one
    it has when its module is the entry.

    Compared over names that denote ONE declaration in the importer's
    registry: a name the entry also declares, or that two modules declare,
    is keyed by a rule of its own (#814, E608) and is not this question.
    """
    importer = _generator(entry)
    source = entry.read_text(encoding="utf-8")
    entry_names = set(_own_functions(parse_to_ast(source)))
    mods = importer._resolved_modules
    declared: dict[str, int] = {}
    for mod in mods:
        for name in _own_functions(mod.program):
            declared[name] = declared.get(name, 0) + 1
    out: list[str] = []
    for mod in mods:
        as_entry = _generator(mod.file_path)
        for name in _own_functions(mod.program):
            if name in entry_names or declared[name] > 1 or "$" in name:
                continue
            got = importer._fn_sigs.get(name)
            want = as_entry._fn_sigs.get(name)
            if got != want:
                out.append(f"{'.'.join(mod.path)}::{name}: imported {got}, "
                           f"as the entry {want}")
    return out


def _multi_module_corpus() -> list[Path]:
    found = []
    for path in corpus_programs():
        program = parse_to_ast(path.read_text(encoding="utf-8"))
        if program.imports:
            resolver = ModuleResolver(_root=path.parent)
            resolver.resolve_imports(program, path)
            if not resolver.errors:
                found.append(path)
    return found


class TestSignaturesDoNotDependOnTheEntry:
    """The differential #1493 proposes, over every module we have."""

    @pytest.mark.parametrize(
        "entry", _multi_module_corpus(),
        ids=lambda p: p.relative_to(_ROOT).as_posix(),
    )
    def test_corpus(self, entry: Path) -> None:
        assert not signature_mismatches(entry)

    @pytest.mark.parametrize("topology", TOPOLOGIES, ids=lambda t: t.label)
    def test_topologies(self, topology, tmp_path: Path) -> None:
        cell = next(c for c in FLOW_CELLS if c.label == "match scrutinee")
        for name, text in topology.files(cell.consumer(topology)).items():
            (tmp_path / name).write_text(text, encoding="utf-8")
        assert not signature_mismatches(tmp_path / "main.vera")

    @pytest.mark.parametrize("decl", (
        "public data Array {\n  MkArr(Int)\n}\n",
        "public data Decimal<T> {\n  Dec(T)\n}\n",
        "public data Map {\n  MkMap(Int)\n}\n",
    ), ids=("Array", "Decimal", "Map"))
    def test_an_import_named_like_a_builtin(
        self, decl: str, tmp_path: Path,
    ) -> None:
        """A module importing a user type named like a built-in container
        measured it as the CONTAINER in the registrar (`Array`: a pair)."""
        name = decl.split()[2].split("<")[0]
        spelled = f"{name}<Int>" if "<T>" in decl else name
        (tmp_path / "mb.vera").write_text(
            f"module mb;\n\n{decl}", encoding="utf-8")
        (tmp_path / "ma.vera").write_text(
            f"module ma;\n\nimport mb({name});\n\n"
            f"public fn keep(@{spelled} -> @{spelled})\n" + _CONTRACT
            + f"{{\n  @{spelled}.0\n}}\n", encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            _main("import ma(keep);\n", "1"), encoding="utf-8")
        assert not signature_mismatches(tmp_path / "main.vera")

    def test_the_differential_can_fail(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Not vacuous: a registrar with its imports taken away — the
        registrar this PR replaces — disagrees with the entry."""
        for name, text in (("mb.vera", _MB), ("ma.vera", _MA),
                           ("main.vera", _main("import ma(which);\n",
                                               "which(1)"))):
            (tmp_path / name).write_text(text, encoding="utf-8")

        def blind(self, mod, programs, renames):  # type: ignore[no-untyped-def]
            temp = CodeGenerator(source=mod.source, file=str(mod.file_path))
            temp._register_all(mod.program)
            return temp

        monkeypatch.setattr(CodeGenerator, "_module_registrar", blind)
        assert signature_mismatches(tmp_path / "main.vera")


# =====================================================================
# The prelude's demand-injected types, in a module (PR #1508 review)
# =====================================================================

@dataclass(frozen=True)
class PreludeType:
    """A data type the prelude injects only when a program uses it."""

    name: str
    #: ``mk``'s body: a value of the type, from ``@Int.0``.
    make: str
    #: A match on ``{X}`` producing an Int.
    use: str
    #: What ``use`` returns on ``mk(1)``.
    value: int


PRELUDE_TYPES: tuple[PreludeType, ...] = (
    PreludeType(
        "Json", "if @Int.0 > 0 then { JNumber(1.5) } else { JNull }",
        "match {X} {\n    JNull -> 1,\n    _ -> 2\n  }", 2),
    PreludeType(
        "HtmlNode", 'HtmlText("xyz")',
        "match {X} {\n    HtmlText(@String) -> string_length(@String.0),"
        "\n    _ -> 0\n  }", 3),
    PreludeType(
        "Request", 'Request("GET", "/p", map_new(), "abcd")',
        "match {X} {\n    Request(@String, @String, @Map<String, String>, "
        "@String) -> string_length(@String.0)\n  }", 4),
    PreludeType(
        "Response", 'Response(200 + @Int.0, map_new(), "ok")',
        "match {X} {\n    Response(@Int, @Map<String, String>, @String) "
        "-> @Int.0\n  }", 201),
)


def _prelude_files(ty: PreludeType, topology: str) -> dict[str, str]:
    """``ma`` returns a value of *ty*; *topology* says who matches on it."""
    mk = (f"public fn mk(@Int -> @{ty.name})\n" + _CONTRACT
          + f"{{\n  {ty.make}\n}}\n")

    def use(arg: str) -> str:
        return ("\npublic fn use(@Int -> @Int)\n" + _CONTRACT + "{\n  "
                + ty.use.replace("{X}", f"mk({arg})") + "\n}\n")

    # A private function of the entry whose signature names the type, so the
    # entry demands the prelude block itself.
    named = (f"\nprivate fn named(@{ty.name} -> @Bool)\n" + _CONTRACT
             + "{\n  true\n}\n")
    if topology == "entry consumes":
        return {"ma.vera": "module ma;\n\n" + mk,
                "main.vera": _main("import ma(mk);\n",
                                   ty.use.replace("{X}", "mk(1)"))}
    if topology == "own body consumes":
        return {"ma.vera": "module ma;\n\n" + mk + use("@Int.0"),
                "main.vera": _main("import ma(use);\n", "use(1)")}
    if topology == "module consumes":
        return {"ma.vera": "module ma;\n\n" + mk,
                "mc.vera": "module mc;\n\nimport ma(mk);\n" + use("@Int.0"),
                "main.vera": _main("import mc(use);\n", "use(1)")}
    if topology == "the entry names it too":
        return {"ma.vera": "module ma;\n\n" + mk + use("@Int.0"),
                "main.vera": _main("import ma(use);\n", "use(1)") + named}
    raise AssertionError(topology)


PRELUDE_TOPOLOGIES = ("entry consumes", "own body consumes",
                      "module consumes", "the entry names it too")

_PRELUDE_CELLS = [
    pytest.param(ty, topology, id=f"{ty.name}-{topology}")
    for ty in PRELUDE_TYPES for topology in PRELUDE_TOPOLOGIES
]


def _write(tmp_path: Path, files: dict[str, str]) -> Path:
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    return tmp_path / "main.vera"


class TestPreludeTypesInAModule:
    """A module using one of the prelude's demand-injected types compiles as
    it does as the entry file.

    Two things were missing.  The prelude's demand was read off the entry
    file alone, so a module that used ``Json`` in a program whose entry
    never named it compiled against no ``Json`` at all; and the registrar
    that measures a module's signatures had none of the four types in its
    namespace, so ``mk(@Int -> @Json)`` registered as ``unsupported`` and
    a direct match on the call dropped the function (E602, then E620).
    """

    @pytest.mark.parametrize(("ty", "topology"), _PRELUDE_CELLS)
    def test_runs(self, ty: PreludeType, topology: str,
                  tmp_path: Path) -> None:
        out = pipeline(tmp_path, _prelude_files(ty, topology))
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", ty.value)

    @pytest.mark.parametrize(("ty", "topology"), _PRELUDE_CELLS)
    def test_signatures_do_not_depend_on_the_entry(
        self, ty: PreludeType, topology: str, tmp_path: Path,
    ) -> None:
        assert not signature_mismatches(
            _write(tmp_path, _prelude_files(ty, topology)))

    def test_the_harness_sees_the_prelude(self, tmp_path: Path) -> None:
        """The module compiled as the entry measures ``mk`` as a pointer:
        the differential compares a real width, not ``unsupported`` on
        both sides."""
        _write(tmp_path, _prelude_files(PRELUDE_TYPES[0], "entry consumes"))
        assert _generator(tmp_path / "ma.vera")._fn_sigs["mk"] == (
            ["i64"], "i32")

    @pytest.mark.parametrize(("declared", "used"), (
        ("Request", "Response"), ("Response", "Request"),
    ))
    def test_a_module_declaring_one_http_type_uses_the_other(
        self, declared: str, used: str, tmp_path: Path,
    ) -> None:
        """The HttpServer block holds two types, and a module's demand is
        per type: one that declares its own ``Request`` still demands the
        prelude's ``Response`` (PR #1508 review).  Refusing the whole block
        left it compiled against no ``Response`` at all (E602, E620), on
        ``main`` as on the release branch."""
        ty = next(t for t in PRELUDE_TYPES if t.name == used)
        out = pipeline(tmp_path, {
            "ma.vera": (
                f"module ma;\n\npublic data {declared} {{\n  Mine(Int)\n}}\n\n"
                "public fn use(@Int -> @Int)\n" + _CONTRACT + "{\n  "
                + ty.use.replace("{X}", ty.make) + "\n}\n"),
            "main.vera": _main("import ma(use);\n", "use(1)"),
        })
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", ty.value)

    def test_every_block_reads_every_module(self) -> None:
        """The modules are read once per demand-injected block, so an
        iterator of them must reach the last block as well as the first
        (PR #1508 review)."""
        from vera.prelude import inject_prelude

        module = parse_to_ast(
            "module ma;\n\npublic fn t(@Int -> @Int)\n" + _CONTRACT
            + "{\n  match Response(200 + @Int.0, map_new(), \"ok\") {\n"
            "    Response(@Int, @Map<String, String>, @String) -> @Int.0\n"
            "  }\n}\n")
        entry_src = _main("import ma(t);\n", "t(1)")

        def data_names(modules: object) -> set[str]:
            entry = parse_to_ast(entry_src)
            inject_prelude(entry, modules)  # type: ignore[arg-type]
            return {tld.decl.name for tld in entry.declarations
                    if isinstance(tld.decl, ast.DataDecl)}

        listed = data_names((module,))
        assert "Response" in listed
        assert data_names(m for m in (module,)) == listed

    @pytest.mark.parametrize("ty", PRELUDE_TYPES, ids=lambda t: t.name)
    def test_the_differential_can_fail(
        self, ty: PreludeType, tmp_path: Path,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Not vacuous: a registrar with the prelude's types taken out of
        its namespace — the registrar before this fix — disagrees with the
        entry."""
        from vera.codegen import modules as codegen_modules

        monkeypatch.setattr(codegen_modules, "prelude_adt_names", frozenset)
        mismatches = signature_mismatches(
            _write(tmp_path, _prelude_files(ty, "own body consumes")))
        assert [m.split(": ")[0] for m in mismatches] == ["ma::mk"], mismatches


# =====================================================================
# #1275: one registration per module per run
# =====================================================================

def _chain(tmp_path: Path, n: int) -> Path:
    """``main -> m{n-1} -> ... -> m0``, each module importing the next's
    data type and returning it."""
    tmp_path.mkdir(parents=True, exist_ok=True)
    for i in range(n):
        imports = f"import m{i - 1}(T{i - 1});\n\n" if i else ""
        (tmp_path / f"m{i}.vera").write_text(
            f"module m{i};\n\n{imports}public data T{i} {{\n  C{i}\n}}\n\n"
            f"public fn f{i}(@Int -> @T{i})\n" + _CONTRACT
            + f"{{\n  C{i}\n}}\n", encoding="utf-8")
    (tmp_path / "main.vera").write_text(
        _main(f"import m{n - 1}(f{n - 1});\n", "1"), encoding="utf-8")
    return tmp_path / "main.vera"


def _constructions(entry: Path, monkeypatch: pytest.MonkeyPatch) -> int:
    counter = {"n": 0}
    original = TypeChecker.__init__

    def counting(self, *args, **kwargs):  # type: ignore[no-untyped-def]
        counter["n"] += 1
        original(self, *args, **kwargs)

    monkeypatch.setattr(TypeChecker, "__init__", counting)
    source = entry.read_text(encoding="utf-8")
    program = parse_to_ast(source)
    mods = ModuleResolver(_root=entry.parent).resolve_imports(program, entry)
    diags = typecheck(program, source, file=str(entry), resolved_modules=mods)
    assert not [d for d in diags if d.severity == "error"], diags
    monkeypatch.undo()
    return counter["n"]


class TestRegistrationIsMemoised:
    """#1275: registration was O(N²) — every checker registered every
    module it could see, and #1244 made one checker per module."""

    def test_checkers_grow_linearly_with_the_chain(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        small = _constructions(_chain(tmp_path / "a", 10), monkeypatch)
        large = _constructions(_chain(tmp_path / "b", 40), monkeypatch)
        # One body check and one registration per module, plus the entry:
        # linear.  Quadratic growth made 40 modules cost ~16x 10.
        assert small <= 2 * 10 + 2, small
        assert large <= 2 * 40 + 2, large

    def test_a_module_is_registered_once_for_the_whole_run(
        self, tmp_path: Path,
    ) -> None:
        entry = _chain(tmp_path, 6)
        source = entry.read_text(encoding="utf-8")
        program = parse_to_ast(source)
        mods = ModuleResolver(_root=entry.parent).resolve_imports(
            program, entry)
        checker = TypeChecker(source=source, file=str(entry),
                              resolved_modules=mods)
        checker.check_program(program)
        cache = checker._module_registration_cache
        assert cache is not None and set(cache) == {m.path for m in mods}
        # The nested body checks were handed the same cache.
        assert all(isinstance(v.checker, TypeChecker) for v in cache.values())

    def test_a_modules_exports_are_derived_once_and_shared(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """What a module EXPORTS is read off its registration once per run.

        A registration holds the whole built-in registry beside the module's
        own declarations, and every checker that could see a module re-read
        its export tables from it — per (checker, module) pair, so a chain
        paid it quadratically even with each registration built once.
        """
        built: list[TypeChecker] = []
        original = TypeChecker.__init__

        def recording(self, *args, **kwargs):  # type: ignore[no-untyped-def]
            original(self, *args, **kwargs)
            built.append(self)

        monkeypatch.setattr(TypeChecker, "__init__", recording)
        entry = _chain(tmp_path, 6)
        source = entry.read_text(encoding="utf-8")
        program = parse_to_ast(source)
        mods = ModuleResolver(_root=entry.parent).resolve_imports(
            program, entry)
        diags = typecheck(program, source, file=str(entry),
                          resolved_modules=mods)
        monkeypatch.undo()
        assert not [d for d in diags if d.severity == "error"], diags
        tables: dict[tuple[str, ...], list[object]] = {}
        for checker in built:
            for path, table in checker._module_functions.items():
                tables.setdefault(path, []).append(table)
        # `m0` is visible to every checker above it in the chain.
        assert len(tables[("m0",)]) > 2, tables.keys()
        for path, seen in tables.items():
            assert all(t is seen[0] for t in seen), path

    def test_the_ambiguity_scan_reads_only_the_namespaces_imports(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A namespace's #1304 clashes are between ITS imports, so the scan
        reads the modules it imports — not every module it can see, which
        made it one more per (checker, module) pass over the chain."""
        from vera.checker import modules as checker_modules

        scanned: list[int] = []
        real_fns = checker_modules.namespace_fn_names
        real_adts = checker_modules.namespace_adt_names

        def fns(entry, modules, **kwargs):  # type: ignore[no-untyped-def]
            modules = list(modules)
            scanned.append(len(modules))
            return real_fns(entry, modules, **kwargs)

        def adts(entry, modules, **kwargs):  # type: ignore[no-untyped-def]
            modules = list(modules)
            scanned.append(len(modules))
            return real_adts(entry, modules, **kwargs)

        monkeypatch.setattr(checker_modules, "namespace_fn_names", fns)
        monkeypatch.setattr(checker_modules, "namespace_adt_names", adts)
        entry = _chain(tmp_path, 8)
        source = entry.read_text(encoding="utf-8")
        program = parse_to_ast(source)
        mods = ModuleResolver(_root=entry.parent).resolve_imports(
            program, entry)
        diags = typecheck(program, source, file=str(entry),
                          resolved_modules=mods)
        monkeypatch.undo()
        assert not [d for d in diags if d.severity == "error"], diags
        # Every namespace in the chain imports one module (`m0` none).
        assert scanned and max(scanned) == 1, scanned


# =====================================================================
# The shared derivation
# =====================================================================

class TestOneDerivation:
    """`vera.module_view`: what one namespace can see through its imports."""

    def test_imported_data_types_lists_every_supplier(self) -> None:
        from vera.module_view import imported_data_types

        shape = "public data Shape {\n  S\n}\nprivate data Hidden {\n  H\n}\n"
        modules = {
            ("ma",): parse_to_ast("module ma;\n\n" + shape),
            ("mb",): parse_to_ast("module mb;\n\n" + shape),
            ("mc",): parse_to_ast(
                "module mc;\n\npublic data Unlisted {\n  U\n}\n"),
        }
        program = parse_to_ast(
            "import ma(Shape, Hidden);\nimport mb;\nimport mc(f);\n"
            "import gone(X);\n\n"
            "public fn f(@Int -> @Int)\n" + _CONTRACT + "{\n  1\n}\n")
        got = imported_data_types(program, modules)
        # Public only; filtered by the import list (`mc`'s names a function,
        # not `Unlisted`); both suppliers of `Shape` kept; an unresolved
        # import supplying nothing.
        assert got == {"Shape": (("ma",), ("mb",))}

    def test_visible_modules_are_re_scoped_and_ordered(self) -> None:
        from vera.module_view import modules_visible_to
        from vera.resolver import ResolvedModule

        root = parse_to_ast("module r;\n\nimport mid;\n")
        mids = parse_to_ast("module mid;\n\nimport deep;\n")
        deep = parse_to_ast("module deep;\n")
        resolved = [
            ResolvedModule(("deep",), Path("/x/deep.vera"), deep, "", True),
            ResolvedModule(("mid",), Path("/x/mid.vera"), mids, "", False),
        ]
        seen = modules_visible_to(root, resolved)
        assert [(m.path, m.direct) for m in seen] == [
            (("mid",), True), (("deep",), False)]
