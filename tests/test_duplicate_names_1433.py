"""#1433: a namespace holds one declaration of each name (spec §8.5.5).

Two ``where`` helpers of one name in one block were check-clean and
verify-clean, then failed codegen with wasm-tools' ``duplicate func
identifier`` against ``$f$where$h``, a mangled symbol the author never wrote.
That is one instance of a class: every namespace the checker registers a
declared name into was a table written last-wins with no duplicate check, so a
second declaration replaced the first, left it unreachable, and the program
failed later and elsewhere.  Measured at the base, beside the reported shape:
two top-level functions of one name died the same way (and inside a module
silently ran the second), two clauses for one operation ran the later one,
two ``data`` declarations of one name surfaced as an exhaustiveness error
about the wrong one, a constructor listed twice in one ``data`` compiled, and
a helper's ``forall<T>`` under a ``forall<T>`` parent was verify-clean and
then failed to load as WebAssembly.

Three instruments, each aimed at a different way the fix could be incomplete:

* **The wiring cell** enumerates the namespaces from the code that registers
  them: ``TypeEnv``'s tables keyed by a declared name, the name-keyed tables
  inside the records stored there, the AST's declaration classes, and the AST
  fields holding declared names.  Every one must be claimed by a row of
  :data:`NAMESPACES` (or excused, with the reason, in :data:`NOT_NAMESPACES`),
  and every claim must name something that exists — so a namespace added
  later without a row fails here rather than silently accepting duplicates.
* **The matrix** crosses each namespace with the spellings of a repeated name
  — the same scope, a nested scope, a sibling scope, across modules, against
  the prelude, and against another namespace — and asserts the check-time
  outcome of each: refused with its code (E184, or the code of the rule that
  owns that shape: E159, E155-E157, E151, E152), or legal, in which case the
  program must also verify, compile, and run to a value that could only come
  from the declaration the rule says wins.  A spelling the grammar cannot
  express is recorded in :data:`NOT_SPELLABLE`, and the claim is checked by
  parsing it.
* **The backstop cells** drive codegen's ``duplicate func identifier`` rail
  directly and through a compile that skips the checker, because no source
  that passes the checker reaches it.
"""

from __future__ import annotations

import dataclasses
import re
import types
import typing
from dataclasses import dataclass, field
from pathlib import Path

import pytest

from vera import ast
from vera.checker import typecheck
from vera.codegen import compile as codegen_compile
from vera.codegen.assembly import AssemblyMixin
from vera.environment import TypeEnv
from vera.errors import Diagnostic, VeraError
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.skip import CodegenInvariantError
from tests.module_fixture_helpers import build_multi_module, module_value

# ---------------------------------------------------------------------------
# Program builders
# ---------------------------------------------------------------------------

_C = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _fn(name: str, sig: str = "@Int -> @Int", body: str = "@Int.0", *,
        vis: str = "public ", forall: str = "", where: str = "") -> str:
    tail = f"\nwhere {{\n{where}}}" if where else ""
    return f"{vis}{forall}fn {name}({sig})\n{_C}{{\n  {body}\n}}{tail}\n"


def _helper(name: str, sig: str = "@Int -> @Int", body: str = "@Int.0", *,
            forall: str = "", where: str = "") -> str:
    tail = f"\n  where {{\n{where}  }}" if where else ""
    return (f"  {forall}fn {name}({sig})\n    requires(true)\n"
            f"    ensures(true)\n    effects(pure)\n  {{\n    {body}\n  }}"
            f"{tail}\n")


def _main(body: str) -> str:
    return _fn("main", "@Unit -> @Int", body)


def _module(name: str, *decls: str) -> str:
    return f"module {name};\n\n" + "\n".join(decls)


def _handle_state(clauses: str, body: str = "get(())") -> str:
    return (f"handle[State<Int>](@Int = 0) {{\n{clauses}\n  }} in {{\n"
            f"    {body}\n  }}")


_GET = "    get(@Unit) -> { resume(@Int.0) }"
_GET_PLUS_ONE = "    get(@Unit) -> { resume(@Int.0 + 1) }"
_PUT = "    put(@Int) -> { resume(()) }"

_LIBF = _module("libf", _fn("f", body="@Int.0 + 100"))
_LIBG = _module("libg", _fn("f", body="@Int.0 + 200"))


# ---------------------------------------------------------------------------
# The namespaces, and what each one claims in the code
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Namespace:
    """One namespace: what registration code holds it, and its rule."""

    claims: frozenset[str]
    one_per: str


NAMESPACES: dict[str, Namespace] = {
    "function": Namespace(
        frozenset({"TypeEnv.functions", "FnDecl"}), "file"),
    "where_helper": Namespace(
        frozenset({"FnDecl.where_fns"}), "`where` block"),
    "type": Namespace(
        frozenset({"TypeEnv.data_types", "TypeEnv.type_aliases",
                   "DataDecl", "TypeAliasDecl"}), "file"),
    "constructor": Namespace(
        frozenset({"TypeEnv.constructors", "AdtInfo.constructors",
                   "DataDecl.constructors"}), "file"),
    "effect": Namespace(
        frozenset({"TypeEnv.effects", "EffectDecl"}), "file"),
    "effect_operation": Namespace(
        frozenset({"EffectInfo.operations", "EffectDecl.operations"}),
        "effect"),
    "ability": Namespace(
        frozenset({"TypeEnv.abilities", "AbilityDecl"}), "file"),
    "ability_operation": Namespace(
        frozenset({"AbilityInfo.operations", "AbilityDecl.operations"}),
        "ability"),
    "handler_clause": Namespace(
        frozenset({"HandleExpr.clauses"}), "`handle` expression"),
    "type_parameter": Namespace(
        frozenset({"TypeEnv.type_params", "FnDecl.forall_vars",
                   "DataDecl.type_params", "TypeAliasDecl.type_params",
                   "EffectDecl.type_params", "AbilityDecl.type_params"}),
        "declaration, with the enclosing functions' `forall` lists"),
    "import": Namespace(
        frozenset({"ImportDecl.names"}), "(admits declarations, declares "
                                         "none)"),
}

#: Enumerated by the wiring cell, and not namespaces a declaration puts a
#: name in.  Each carries why.
NOT_NAMESPACES: dict[str, str] = {
    "ImportDecl.path": (
        "a module path names a FILE for the resolver (§8.6.1); it declares "
        "nothing"),
    "ModuleDecl.path": (
        "a file declares its own path once — the grammar admits one "
        "`module` declaration"),
    "ModuleCall.path": "a module-qualified call REFERENCES a path",
}


def _all_subclasses(cls: type) -> set[type]:
    out: set[type] = set()
    stack = [cls]
    while stack:
        for sub in stack.pop().__subclasses__():
            if sub not in out:
                out.add(sub)
                stack.append(sub)
    return out


def _hints(cls: type) -> dict[str, typing.Any]:
    """``typing.get_type_hints``, tolerating a name the module binds only
    under ``TYPE_CHECKING`` (stood in for by ``object``: no name-keyed table
    is typed by one)."""
    stand_ins: dict[str, typing.Any] = {}
    while True:
        try:
            return typing.get_type_hints(cls, localns=stand_ins)
        except NameError as exc:
            assert exc.name and exc.name not in stand_ins, exc
            stand_ins[exc.name] = object


def _name_keyed(tp: object) -> bool:
    return typing.get_origin(tp) is dict and typing.get_args(tp)[0] is str


def _tuple_element(tp: object) -> object | None:
    """``X`` for ``tuple[X, ...]``, or for ``tuple[X, ...] | None``."""
    union = typing.get_origin(tp) in (typing.Union, types.UnionType)
    for option in typing.get_args(tp) if union else (tp,):
        if typing.get_origin(option) is tuple:
            args = typing.get_args(option)
            if len(args) == 2 and args[1] is Ellipsis:
                return args[0]
    return None


def _declares_a_name(cls: object) -> bool:
    if not (isinstance(cls, type) and dataclasses.is_dataclass(cls)):
        return False
    names = {f.name for f in dataclasses.fields(cls)}
    return bool(names & {"name", "op_name"})


def enumerated_registrations() -> set[str]:
    """Every name-keyed registration the checker's code can hold.

    Read from the code, never listed: ``TypeEnv``'s tables keyed by a
    declared name; the name-keyed tables inside the records those hold; the
    AST's declaration classes; and every AST field that holds declarations
    carrying a name, or a list of names.
    """
    found: set[str] = set()
    env_hints = _hints(TypeEnv)
    for f in dataclasses.fields(TypeEnv):
        tp = env_hints[f.name]
        if not _name_keyed(tp):
            continue
        found.add(f"TypeEnv.{f.name}")
        record = typing.get_args(tp)[1]
        if isinstance(record, type) and dataclasses.is_dataclass(record):
            record_hints = _hints(record)
            for g in dataclasses.fields(record):
                if _name_keyed(record_hints[g.name]):
                    found.add(f"{record.__name__}.{g.name}")
    found.update(c.__name__ for c in _all_subclasses(ast.Decl))
    for cls in _all_subclasses(ast.Node):
        if not dataclasses.is_dataclass(cls):
            continue
        hints = _hints(cls)
        for f in dataclasses.fields(cls):
            element = _tuple_element(hints[f.name])
            if element is str or _declares_a_name(element):
                found.add(f"{cls.__name__}.{f.name}")
    return found


def test_every_registration_the_code_holds_is_claimed() -> None:
    """The wiring cell: the matrix's rows ARE the namespaces in the code.

    Both directions.  An enumerated registration no row claims is a namespace
    that could accept a duplicate unmeasured; a claim nothing enumerates is a
    row describing a namespace that no longer exists.
    """
    claimed: set[str] = set(NOT_NAMESPACES)
    for ns in NAMESPACES.values():
        overlap = claimed & ns.claims
        assert not overlap, f"claimed twice: {sorted(overlap)}"
        claimed |= ns.claims
    enumerated = enumerated_registrations()
    assert enumerated - claimed == set(), (
        f"registrations no namespace row claims — add a row (and its matrix "
        f"cells) or a NOT_NAMESPACES reason: {sorted(enumerated - claimed)}"
    )
    assert claimed - enumerated == set(), (
        f"claims nothing in the code holds any more: "
        f"{sorted(claimed - enumerated)}"
    )


# ---------------------------------------------------------------------------
# The matrix
# ---------------------------------------------------------------------------

SPELLINGS = ("same_scope", "nested_scope", "across_modules")


@dataclass(frozen=True)
class Cell:
    """One (namespace, spelling) program and its check-time outcome.

    ``expect`` is an error code, or ``"legal"`` — in which case the program
    must verify, compile and run, and ``main`` must return ``value``.
    ``surplus`` locates an E184's surplus declarations: every match of the
    pattern in that file after the first is one, the diagnostics must sit on
    their lines in order, and each rationale must name the first's line.
    With ``one_line`` — a type parameter repeated in one list — the pattern
    matches the declaration's one line, which holds both binders: every
    diagnostic sits there, and no rationale can name a separate line.
    """

    id: str
    namespace: str
    spelling: str
    files: dict[str, str]
    expect: str
    value: int | None = None
    count: int = 1
    surplus: tuple[str, str] | None = None
    one_line: bool = False
    notes: dict[str, str] = field(default_factory=dict)


def _c(id: str, namespace: str, spelling: str, main: str, expect: str,
       **kw: typing.Any) -> Cell:
    mods = kw.pop("modules", {})
    files = {"main.vera": main, **{f"{k}.vera": v for k, v in mods.items()}}
    return Cell(id=id, namespace=namespace, spelling=spelling, files=files,
                expect=expect, **kw)


_E_A = "effect E {\n  op a(Unit -> Int);\n}\n"
_E_B = "effect E {\n  op b(Unit -> Int);\n}\n"
_SZ_SIZE = "ability Sz {\n  op size(Int -> Int);\n}\n"
_SZ_LEN = "ability Sz {\n  op len(Int -> Int);\n}\n"

CELLS: list[Cell] = [
    # -- functions ---------------------------------------------------------
    _c("fn/twice", "function", "same_scope",
       _fn("f", body="@Int.0 + 1") + "\n" + _fn("f", body="@Int.0 + 2")
       + "\n" + _main("f(1)"),
       "E184", surplus=("main.vera", r"^public fn f\(")),
    # The first stays canonical: registered last-wins, the call `f(1)`
    # would also draw an E202 against the surplus's `@Bool`.
    _c("fn/twice-other-signature", "function", "same_scope",
       _fn("f", body="@Int.0 + 1") + "\n"
       + _fn("f", sig="@Bool -> @Int", body="7") + "\n" + _main("f(1)"),
       "E184", surplus=("main.vera", r"^public fn f\(")),
    # And the surplus body is not checked: its recursive `f(false)` would
    # resolve to the first `f(@Int)` and draw an E202 of its own.
    _c("fn/surplus-body-calls-itself", "function", "same_scope",
       _fn("f") + "\n"
       + _fn("f", sig="@Bool -> @Int",
             body="if @Bool.0 then { f(false) } else { 0 }")
       + "\n" + _main("f(1)"),
       "E184", surplus=("main.vera", r"^public fn f\(")),
    _c("fn/three-times", "function", "same_scope",
       _fn("f", body="1") + "\n" + _fn("f", body="2") + "\n"
       + _fn("f", body="3") + "\n" + _main("f(0)"),
       "E184", count=2, surplus=("main.vera", r"^public fn f\(")),
    _c("fn/public-and-private", "function", "same_scope",
       _fn("f", vis="private ", body="@Int.0 + 1") + "\n"
       + _fn("f", body="@Int.0 + 2") + "\n" + _main("f(1)"),
       "E184", surplus=("main.vera", r"^(public|private) fn f\(")),
    _c("fn/main-twice", "function", "same_scope",
       _main("1") + "\n" + _main("2"),
       "E184", surplus=("main.vera", r"^public fn main\(")),
    _c("fn/helper-shadows-top-level", "function", "nested_scope",
       _fn("g", body="@Int.0 + 1000") + "\n"
       + _fn("f", body="g(@Int.0)", where=_helper("g", body="@Int.0 + 1"))
       + "\n" + _main("f(1) + g(0)"),
       "legal", value=1002),
    _c("fn/helper-named-like-parent", "function", "nested_scope",
       _fn("f", body="f(@Int.0)", where=_helper("f", body="@Int.0 + 1"))
       + "\n" + _main("f(1)"),
       "legal", value=2),
    _c("fn/module-declares-twice", "function", "across_modules",
       "import libd;\n\n" + _main("f(1)"),
       "E184", surplus=("libd.vera", r"^public fn f\("),
       modules={"libd": _module("libd", _fn("f", body="@Int.0 + 1"),
                                _fn("f", body="@Int.0 + 2"))}),
    _c("fn/local-shadows-import", "function", "across_modules",
       "import libf;\n\n" + _fn("f", body="@Int.0 + 1") + "\n"
       + _main("f(1)"),
       "legal", value=2, modules={"libf": _LIBF}),
    _c("fn/two-imports-supply-one-name", "function", "across_modules",
       "import libf;\nimport libg;\n\n" + _main("f(1)"),
       "E155", modules={"libf": _LIBF, "libg": _LIBG}),
    _c("fn/shadows-prelude-combinator", "function", "prelude",
       _fn("option_unwrap_or", sig="@Option<Int>, @Int -> @Int", body="99")
       + "\n" + _main("option_unwrap_or(None, 5)"),
       "legal", value=99),
    _c("fn/redefines-built-in", "function", "prelude",
       _fn("string_length", sig="@String -> @Int", body="1") + "\n"
       + _main('string_length("ab")'),
       "E151"),

    # -- where helpers -----------------------------------------------------
    _c("where/twice", "where_helper", "same_scope",
       _fn("f", body="h(@Int.0)",
           where=_helper("h", body="@Int.0 + 1") + "\n"
           + _helper("h", body="@Int.0 + 2"))
       + "\n" + _main("f(1)"),
       "E184", surplus=("main.vera", r"^  fn h\(")),
    _c("where/three-times", "where_helper", "same_scope",
       _fn("f", body="h(@Int.0)",
           where=_helper("h") + "\n" + _helper("h", body="@Int.0 + 1")
           + "\n" + _helper("h", body="@Int.0 + 2"))
       + "\n" + _main("f(1)"),
       "E184", count=2, surplus=("main.vera", r"^  fn h\(")),
    _c("where/twice-other-signature", "where_helper", "same_scope",
       _fn("f", body="h(@Int.0)",
           where=_helper("h", body="@Int.0 + 1") + "\n"
           + _helper("h", sig="@Bool -> @Int", body="7"))
       + "\n" + _main("f(1)"),
       "E184", surplus=("main.vera", r"^  fn h\(")),
    # The surplus helper's body is not checked either: its `h(false)` would
    # resolve to the first `h(@Int)` and draw an E202 of its own.
    _c("where/surplus-body-calls-itself", "where_helper", "same_scope",
       _fn("f", body="h(@Int.0)",
           where=_helper("h") + "\n"
           + _helper("h", sig="@Bool -> @Int",
                     body="if @Bool.0 then { h(false) } else { 0 }"))
       + "\n" + _main("f(1)"),
       "E184", surplus=("main.vera", r"^  fn h\(")),
    _c("where/nested-block-reuses-name", "where_helper", "nested_scope",
       _fn("f", body="h(@Int.0)",
           where=_helper("h", body="k(@Int.0)",
                         where=_helper("k", body="@Int.0 + 10"))
           + "\n" + _helper("k", body="@Int.0 + 1"))
       + "\n" + _main("f(1)"),
       "legal", value=11),
    _c("where/twice-in-nested-block", "where_helper", "nested_scope",
       _fn("f", body="h(@Int.0)",
           where=_helper("h", body="k(@Int.0)",
                         where=_helper("k", body="@Int.0 + 1") + "\n"
                         + _helper("k", body="@Int.0 + 2")))
       + "\n" + _main("f(1)"),
       "E184", surplus=("main.vera", r"^  fn k\(")),
    _c("where/two-parents", "where_helper", "sibling_scope",
       _fn("f", body="h(@Int.0)", where=_helper("h", body="@Int.0 + 1"))
       + "\n"
       + _fn("g", body="h(@Int.0)", where=_helper("h", body="@Int.0 + 2"))
       + "\n" + _main("f(1) * 100 + g(1)"),
       "legal", value=203),
    _c("where/module-helper-twice", "where_helper", "across_modules",
       "import libw;\n\n" + _main("f(1)"),
       "E184", surplus=("libw.vera", r"^  fn h\("),
       modules={"libw": _module("libw", _fn(
           "f", body="h(@Int.0)",
           where=_helper("h", body="@Int.0 + 1") + "\n"
           + _helper("h", body="@Int.0 + 2")))}),

    # -- types (data and alias share one namespace) -------------------------
    _c("type/data-twice", "type", "same_scope",
       "public data Foo { A }\n\npublic data Foo { B }\n\n"
       + _main("match A { A -> 1 }"),
       "E184", surplus=("main.vera", r"^public data Foo\b")),
    # The shape E159 let through: the two share an OWNER name, so the
    # sibling-constructor rule read them as one declaration.
    _c("type/data-twice-identical", "type", "same_scope",
       "public data Foo { A }\n\npublic data Foo { A }\n\n"
       + _main("match A { A -> 1 }"),
       "E184", surplus=("main.vera", r"^public data Foo\b")),
    _c("type/alias-twice", "type", "same_scope",
       "type Foo = Int;\n\ntype Foo = Bool;\n\n"
       + _fn("f", sig="@Foo -> @Int", body="1") + "\n" + _main("f(1)"),
       "E184", surplus=("main.vera", r"^type Foo\b")),
    _c("type/alias-twice-same-target", "type", "same_scope",
       "type Foo = Int;\n\ntype Foo = Int;\n\n"
       + _fn("f", sig="@Foo -> @Int", body="1") + "\n" + _main("f(1)"),
       "E184", surplus=("main.vera", r"^type Foo\b")),
    _c("type/data-then-alias", "type", "same_scope",
       "public data Foo { A }\n\ntype Foo = Int;\n\n" + _main("1"),
       "E184", surplus=("main.vera", r"^(public data|type) Foo\b")),
    _c("type/alias-then-data", "type", "same_scope",
       "type Foo = Int;\n\npublic data Foo { A }\n\n" + _main("1"),
       "E184", surplus=("main.vera", r"^(public data|type) Foo\b")),
    # A surplus alias is out of the alias graph too, or its own body — which
    # names `Foo` — would draw an E132 cycle besides the E184.
    _c("type/alias-repeating-data-names-itself", "type", "same_scope",
       "public data Foo { A }\n\ntype Foo = Option<Foo>;\n\n" + _main("1"),
       "E184", surplus=("main.vera", r"^(public data|type) Foo\b")),
    _c("type/module-declares-twice", "type", "across_modules",
       "import libdd;\n\n" + _main("1"),
       "E184", surplus=("libdd.vera", r"^public data Foo\b"),
       modules={"libdd": _module("libdd", "public data Foo { A }\n",
                                 "public data Foo { B }\n")}),
    _c("type/local-shadows-import", "type", "across_modules",
       "import libdt;\n\npublic data Foo { A(Int) }\n\n"
       + _main("match A(7) { A(@Int) -> @Int.0 }"),
       "legal", value=7,
       modules={"libdt": _module("libdt", "public data Foo { A, B }\n")}),
    _c("type/two-imports-supply-one-name", "type", "across_modules",
       "import libx;\nimport liby;\n\n" + _main("1"),
       "E156",
       modules={"libx": _module("libx", "public data Foo { Xa }\n"),
                "liby": _module("liby", "public data Foo { Yb }\n")}),
    # Aliases are module-local (§8.4.1): the module's never meets the
    # entry's, and the entry's `Foo` is `Bool` here while the module's is
    # `Int` there.
    _c("type/alias-in-module-and-entry", "type", "across_modules",
       "import libt;\n\ntype Foo = Bool;\n\n"
       + _fn("f", sig="@Foo -> @Int", body="1") + "\n"
       + _main("f(true) + z(1)"),
       "legal", value=2,
       modules={"libt": _module("libt", "type Foo = Int;\n",
                                _fn("z", sig="@Foo -> @Int",
                                    body="@Foo.0"))}),
    _c("type/entry-restates-prelude-type", "type", "prelude",
       "public data Option<T> { None, Some(T) }\n\n"
       + _main("match Some(4) { Some(@Int) -> @Int.0, None -> 0 }"),
       "legal", value=4),

    # -- constructors ------------------------------------------------------
    _c("ctor/listed-twice-in-one-data", "constructor", "same_scope",
       "public data Foo {\n  A,\n  A\n}\n\n" + _main("match A { A -> 1 }"),
       "E184", surplus=("main.vera", r"^  A\b")),
    # #1425's rule, re-verified: two DECLARATIONS sharing a constructor.
    _c("ctor/two-data-share-one", "constructor", "same_scope",
       "public data Foo { A }\n\npublic data Bar { A }\n\n" + _main("1"),
       "E159"),
    _c("ctor/module-lists-twice", "constructor", "across_modules",
       "import libc2;\n\n" + _main("1"),
       "E184", surplus=("libc2.vera", r"^  A\b"),
       modules={"libc2": _module("libc2", "public data Foo {\n  A,\n  A\n}\n")}),
    _c("ctor/module-two-data-share-one", "constructor", "across_modules",
       "import libs;\n\n" + _main("1"),
       "E159",
       modules={"libs": _module("libs", "public data Foo { A }\n",
                                "public data Bar { A }\n")}),
    _c("ctor/local-shadows-imported", "constructor", "across_modules",
       "import libc;\n\npublic data Mine { A(Int) }\n\n"
       + _main("match A(7) { A(@Int) -> @Int.0 }"),
       "legal", value=7,
       modules={"libc": _module("libc", "public data Theirs { A, B }\n")}),
    _c("ctor/two-imports-supply-one-name", "constructor", "across_modules",
       "import libx;\nimport liby;\n\n" + _main("1"),
       "E157",
       modules={"libx": _module("libx", "public data Foo { Q }\n"),
                "liby": _module("liby", "public data Bar { Q }\n")}),
    # Only the entry's two-field `Some` can build `Some(5, 6)` — the
    # prelude's has one field.
    _c("ctor/shadows-prelude-constructor", "constructor", "prelude",
       "public data Pair { Some(Int, Int) }\n\n"
       + _main("match Some(5, 6) { Some(@Int, @Int) -> @Int.0 }"),
       "legal", value=6),
    _c("ctor/type-and-constructor-share-a-name", "constructor",
       "other_namespace",
       "public data Box { Box(Int) }\n\n"
       + _main("match Box(9) { Box(@Int) -> @Int.0 }"),
       "legal", value=9),

    # -- effects -----------------------------------------------------------
    _c("effect/twice", "effect", "same_scope",
       _E_A + "\n" + _E_B + "\n" + _main("1"),
       "E184", surplus=("main.vera", r"^effect E\b")),
    _c("effect/twice-identical", "effect", "same_scope",
       _E_A + "\n" + _E_A + "\n" + _main("1"),
       "E184", surplus=("main.vera", r"^effect E\b")),
    _c("effect/module-declares-twice", "effect", "across_modules",
       "import libe2;\n\n" + _main("1"),
       "E184", surplus=("libe2.vera", r"^effect E\b"),
       modules={"libe2": _module("libe2", _E_A, _E_B, _fn("z"))}),
    # Effects are module-local (§8.4.1).
    _c("effect/in-module-and-entry", "effect", "across_modules",
       "import libe;\n\n" + _E_B + "\n" + _main("z(1)"),
       "legal", value=1,
       modules={"libe": _module("libe", _E_A, _fn("z"))}),
    _c("effect/redeclares-built-in", "effect", "prelude",
       "effect IO {\n  op print(String -> Unit);\n}\n\n" + _main("1"),
       "E152"),
    _c("effect/effect-and-data-share-a-name", "effect", "other_namespace",
       "effect Foo {\n  op a(Unit -> Int);\n}\n\n"
       "public data Foo { MkFoo(Int) }\n\n"
       + _fn("g", sig="@Foo -> @Int",
             body="match @Foo.0 { MkFoo(@Int) -> @Int.0 }")
       + "\n" + _main("g(MkFoo(4))"),
       "legal", value=4),

    # -- effect operations ---------------------------------------------------
    _c("op/twice", "effect_operation", "same_scope",
       "effect E {\n  op a(Unit -> Int);\n  op a(Unit -> Bool);\n}\n\n"
       + _main("1"),
       "E184", surplus=("main.vera", r"^  op a\(")),
    _c("op/twice-and-handled", "effect_operation", "same_scope",
       "effect E {\n  op a(Unit -> Int);\n  op a(Unit -> Int);\n}\n\n"
       + _fn("g", sig="@Unit -> @Int",
             body="handle[E] {\n    a(@Unit) -> { resume(5) }\n  } in {\n"
                  "    a(())\n  }")
       + "\n" + _main("g(())"),
       "E184", surplus=("main.vera", r"^  op a\(")),
    _c("op/two-effects-share-a-name", "effect_operation", "sibling_scope",
       "effect E1 {\n  op a(Unit -> Int);\n}\n\n"
       "effect E2 {\n  op a(Unit -> Int);\n}\n\n" + _main("3"),
       "legal", value=3),
    _c("op/module-effect-twice", "effect_operation", "across_modules",
       "import libop;\n\n" + _main("1"),
       "E184", surplus=("libop.vera", r"^  op a\("),
       modules={"libop": _module(
           "libop", "effect E {\n  op a(Unit -> Int);\n"
                    "  op a(Unit -> Int);\n}\n", _fn("z"))}),

    # -- abilities -----------------------------------------------------------
    _c("ability/twice", "ability", "same_scope",
       _SZ_SIZE + "\n" + _SZ_LEN + "\n" + _main("1"),
       "E184", surplus=("main.vera", r"^ability Sz\b")),
    _c("ability/module-declares-twice", "ability", "across_modules",
       "import liba2;\n\n" + _main("1"),
       "E184", surplus=("liba2.vera", r"^ability Sz\b"),
       modules={"liba2": _module("liba2", _SZ_SIZE, _SZ_LEN, _fn("z"))}),
    # Abilities are not importable: the module's `Sz` never meets the
    # entry's.
    _c("ability/in-module-and-entry", "ability", "across_modules",
       "import liba;\n\n" + _SZ_LEN + "\n" + _main("z(1)"),
       "legal", value=1,
       modules={"liba": _module("liba", _SZ_SIZE, _fn("z"))}),
    _c("ability/ability-and-effect-share-a-name", "ability",
       "other_namespace",
       "effect Sz {\n  op a(Unit -> Int);\n}\n\n" + _SZ_SIZE + "\n"
       + _main("1"),
       "legal", value=1),

    # -- ability operations --------------------------------------------------
    _c("aop/twice", "ability_operation", "same_scope",
       "ability Sz {\n  op size(Int -> Int);\n  op size(Int -> Bool);\n}\n\n"
       + _main("1"),
       "E184", surplus=("main.vera", r"^  op size\(")),
    _c("aop/two-abilities-share-a-name", "ability_operation",
       "sibling_scope",
       "ability Sz {\n  op size(Int -> Int);\n}\n\n"
       "ability Len {\n  op size(Int -> Int);\n}\n\n" + _main("5"),
       "legal", value=5),
    _c("aop/module-ability-twice", "ability_operation", "across_modules",
       "import libaop;\n\n" + _main("1"),
       "E184", surplus=("libaop.vera", r"^  op size\("),
       modules={"libaop": _module(
           "libaop", "ability Sz {\n  op size(Int -> Int);\n"
                     "  op size(Int -> Int);\n}\n", _fn("z"))}),

    # -- handler clauses -----------------------------------------------------
    # At the base this RAN, and ran the later clause: `main` returned 1.
    _c("clause/twice", "handler_clause", "same_scope",
       _fn("g", sig="@Unit -> @Int",
           body=_handle_state(_GET + ",\n" + _GET_PLUS_ONE + ",\n" + _PUT))
       + "\n" + _main("g(())"),
       "E184", surplus=("main.vera", r"^    get\(@Unit\)")),
    _c("clause/nested-handler-for-the-same-effect", "handler_clause",
       "nested_scope",
       _fn("g", sig="@Unit -> @Int",
           body=_handle_state(
               _GET + ",\n" + _PUT,
               body="handle[State<Int>](@Int = 7) {\n  "
                    + _GET + ",\n  " + _PUT
                    + "\n    } in {\n      get(())\n    }"))
       + "\n" + _main("g(())"),
       "legal", value=7),
    _c("clause/module-handler-twice", "handler_clause", "across_modules",
       "import libh;\n\n" + _main("g(())"),
       "E184", surplus=("libh.vera", r"^    get\(@Unit\)"),
       modules={"libh": _module("libh", _fn(
           "g", sig="@Unit -> @Int",
           body=_handle_state(_GET + ",\n" + _GET_PLUS_ONE + ",\n"
                              + _PUT)))}),

    # -- type parameters -----------------------------------------------------
    _c("tparam/forall-twice", "type_parameter", "same_scope",
       _fn("idf", sig="@T -> @T", body="@T.0", forall="forall<T, T> ")
       + "\n" + _main("idf(1)"),
       "E184", surplus=("main.vera", r"^public forall<T, T> fn idf\("),
       one_line=True),
    _c("tparam/data-twice", "type_parameter", "same_scope",
       "public data Box<T, T> { B(T) }\n\n" + _main("1"),
       "E184", surplus=("main.vera", r"^public data Box\b"),
       one_line=True),
    _c("tparam/alias-twice", "type_parameter", "same_scope",
       "type P<T, T> = Array<T>;\n\n" + _main("1"),
       "E184", surplus=("main.vera", r"^type P\b"),
       one_line=True),
    _c("tparam/effect-twice", "type_parameter", "same_scope",
       "effect E<T, T> {\n  op a(Unit -> T);\n}\n\n" + _main("1"),
       "E184", surplus=("main.vera", r"^effect E\b"),
       one_line=True),
    _c("tparam/ability-twice", "type_parameter", "same_scope",
       "ability Sz<T, T> {\n  op size(T -> Int);\n}\n\n" + _main("1"),
       "E184", surplus=("main.vera", r"^ability Sz\b"),
       one_line=True),
    # At the base: check- and verify-clean, then `f$Bool` failed to load as
    # WebAssembly — the parent's T is Bool and the helper's is Int.
    _c("tparam/helper-rebinds-parent-parameter", "type_parameter",
       "nested_scope",
       _fn("f", sig="@T -> @Int", body="h(7)", forall="forall<T> ",
           where=_helper("h", sig="@T -> @Int", body="41",
                         forall="forall<T> "))
       + "\n" + _main("f(true)"),
       "E184", surplus=("main.vera", r"fn (f|h)\(")),
    _c("tparam/helper-own-parameter", "type_parameter", "nested_scope",
       _fn("f", sig="@T -> @Int", body="h(7)", forall="forall<T> ",
           where=_helper("h", sig="@U -> @Int", body="41",
                         forall="forall<U> "))
       + "\n" + _main("f(true)"),
       "legal", value=41),
    _c("tparam/sibling-helpers", "type_parameter", "sibling_scope",
       _fn("f", body="g(@Int.0) + k(true)",
           where=_helper("g", sig="@T -> @Int", body="10",
                         forall="forall<T> ") + "\n"
           + _helper("k", sig="@T -> @Int", body="20",
                     forall="forall<T> "))
       + "\n" + _main("f(1)"),
       "legal", value=30),
    # DE_BRUIJN.md §6.4: a type parameter shadows a module alias of its name
    # — two namespaces, the binder the nearer.  `Some(true)` only checks if
    # `T` is the type variable, and 5 only comes back if `@Option<Int>.0` is
    # the first parameter rather than a stack merged with the second.
    _c("tparam/shadows-a-type-alias", "type_parameter", "other_namespace",
       "type T = Int;\n\n"
       + _fn("pick", sig="@Option<Int>, @Option<T> -> @Int",
             body="match @Option<Int>.0 {\n    Some(@Int) -> @Int.0,\n"
                  "    None -> 0\n  }",
             forall="forall<T> ")
       + "\n" + _main("pick(Some(5), Some(true))"),
       "legal", value=5),
    _c("tparam/module-forall-twice", "type_parameter", "across_modules",
       "import libtp;\n\n" + _main("1"),
       "E184", surplus=("libtp.vera", r"^public forall<T, T> fn idf\("),
       one_line=True,
       modules={"libtp": _module("libtp", _fn(
           "idf", sig="@T -> @T", body="@T.0", forall="forall<T, T> "))}),

    # -- imports -------------------------------------------------------------
    _c("import/name-listed-twice", "import", "same_scope",
       "import libf(f, f);\n\n" + _main("f(1)"),
       "legal", value=101, modules={"libf": _LIBF}),
    _c("import/module-imported-twice", "import", "same_scope",
       "import libf;\nimport libf;\n\n" + _main("f(1)"),
       "legal", value=101, modules={"libf": _LIBF}),
]

#: (namespace, spelling) pairs the grammar cannot express, and why.  Where a
#: program is given, the claim is checked: it must fail to PARSE.
NOT_SPELLABLE: dict[tuple[str, str], tuple[str, str | None]] = {
    ("type", "nested_scope"): (
        "`data` and `type` declarations are top-level only",
        _fn("f") + "where {\n  public data Foo { A }\n}\n"),
    ("constructor", "nested_scope"): (
        "a constructor is declared only inside a top-level `data`",
        _fn("f") + "where {\n  public data Foo { A }\n}\n"),
    ("effect", "nested_scope"): (
        "`effect` declarations are top-level only",
        _fn("f") + "where {\n  effect E {\n    op a(Unit -> Int);\n  }\n}\n"),
    ("effect_operation", "nested_scope"): (
        "an effect's operations are one flat list",
        "effect E {\n  effect F {\n    op a(Unit -> Int);\n  }\n}\n"),
    ("ability", "nested_scope"): (
        "`ability` declarations are top-level only",
        _fn("f") + "where {\n  ability Sz {\n    op size(Int -> Int);\n"
                   "  }\n}\n"),
    ("ability_operation", "nested_scope"): (
        "an ability's operations are one flat list",
        "ability Sz {\n  ability Len {\n    op size(Int -> Int);\n  }\n}\n"),
    ("import", "nested_scope"): (
        "imports precede every declaration of a file",
        _fn("f") + "\nimport libf;\n"),
    ("import", "across_modules"): (
        "an import list belongs to one file; what two files' imports "
        "supplying one name means is the function, type and constructor "
        "rows' `across_modules` cells (E155, E156, E157)",
        None),
}


def test_the_matrix_covers_every_namespace_and_spelling() -> None:
    """Each namespace is crossed with each required spelling — a cell, or a
    recorded reason the grammar cannot spell it — and each cell's namespace
    is a real row, so the matrix cannot quietly thin out."""
    covered = {(c.namespace, c.spelling) for c in CELLS}
    for ns in NAMESPACES:
        for spelling in SPELLINGS:
            assert (ns, spelling) in covered or (ns, spelling) in NOT_SPELLABLE, (
                f"no cell and no recorded reason for {ns} x {spelling}"
            )
    assert {c.namespace for c in CELLS} <= set(NAMESPACES)
    assert {ns for ns, _ in NOT_SPELLABLE} <= set(NAMESPACES)
    ids = [c.id for c in CELLS]
    assert len(ids) == len(set(ids)), "duplicate cell ids"
    # Every namespace a declaration can repeat a name in is shown refusing
    # it in its own scope — the claim the fix makes.
    for ns in NAMESPACES:
        if ns == "import":
            continue
        assert any(c.namespace == ns and c.spelling == "same_scope"
                   and c.expect != "legal" for c in CELLS), ns


@pytest.mark.parametrize(
    "key", sorted(k for k, (_, prog) in NOT_SPELLABLE.items() if prog),
    ids=lambda k: f"{k[0]}-{k[1]}",
)
def test_an_unspellable_spelling_does_not_parse(key: tuple[str, str]) -> None:
    """The recorded reason is a fact about the grammar, so check it."""
    _, program = NOT_SPELLABLE[key]
    assert program is not None
    with pytest.raises(VeraError):
        parse_to_ast(program)


def _write(tmp_path: Path, files: dict[str, str]) -> Path:
    for name, src in files.items():
        (tmp_path / name).write_text(src, encoding="utf-8")
    return tmp_path / "main.vera"


def _check(tmp_path: Path, files: dict[str, str]) -> list[Diagnostic]:
    """Resolve and type-check ``main.vera`` exactly as ``vera check`` does."""
    main_path = _write(tmp_path, files)
    source = files["main.vera"]
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(program, main_path)
    assert not resolver.errors, [d.description for d in resolver.errors]
    return [d for d in typecheck(program, source, file=str(main_path),
                                 resolved_modules=resolved)
            if d.severity == "error"]


def _lines_of(pattern: str, source: str) -> list[int]:
    return [source.count("\n", 0, m.start()) + 1
            for m in re.finditer(pattern, source, re.MULTILINE)]


_REFUSED = [c for c in CELLS if c.expect != "legal"]
_LEGAL = [c for c in CELLS if c.expect == "legal"]


@pytest.mark.parametrize("cell", _REFUSED, ids=[c.id for c in _REFUSED])
def test_a_refused_spelling_is_refused_at_check(
    tmp_path: Path, cell: Cell,
) -> None:
    """Exactly the expected code, once per surplus declaration — no cascade.

    For an E184, each diagnostic sits on its surplus declaration, in the
    file that declares it, and its rationale names the line of the first:
    the earlier is the one a reader takes as intended, and the one every use
    resolves against, so no second error reports the program against the
    surplus.
    """
    errors = _check(tmp_path, cell.files)
    codes = [d.error_code for d in errors]
    assert codes == [cell.expect] * cell.count, (
        f"{cell.id}: expected {[cell.expect] * cell.count}, got {codes}: "
        f"{[d.description for d in errors]}"
    )
    if cell.surplus is None:
        return
    fname, pattern = cell.surplus
    lines = _lines_of(pattern, cell.files[fname])
    if cell.one_line:
        assert len(lines) == 1, (cell.id, lines)
        first, surplus = lines[0], lines * cell.count
    else:
        assert len(lines) == cell.count + 1, (cell.id, lines)
        first, surplus = lines[0], lines[1:]
    assert [d.location.line for d in errors] == surplus, (
        f"{cell.id}: the E184 should sit on the surplus declaration(s) at "
        f"{surplus}, got {[d.location.line for d in errors]}"
    )
    for d in errors:
        assert Path(d.location.file or "").name == fname, (cell.id, d.location)
        assert d.description.startswith("Duplicate "), d.description
        assert (f"at line {first}" in d.rationale) != cell.one_line, (
            cell.id, d.rationale)


@pytest.mark.parametrize("cell", _LEGAL, ids=[c.id for c in _LEGAL])
def test_a_legal_spelling_verifies_compiles_and_runs(
    tmp_path: Path, cell: Cell,
) -> None:
    """Not a duplicate — and the program works, with the declaration the
    rule says wins: each value could only come from that one."""
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, cell.files,
    )
    assert verify_errors == [], (cell.id, verify_errors)
    assert cg_errors == [], (cell.id, cg_errors)
    assert module_value(result) == ("ok", cell.value), cell.id


# ---------------------------------------------------------------------------
# The conformance fixture, and the diagnostic's own text
# ---------------------------------------------------------------------------

def test_the_where_helper_rationale_and_fix_are_instructions(
    tmp_path: Path,
) -> None:
    """The reported shape, read the way an author meets it."""
    cell = next(c for c in CELLS if c.id == "where/twice")
    (diag,) = _check(tmp_path, cell.files)
    assert diag.description == (
        "Duplicate 'where' helper 'h' in the 'where' block of 'f'."
    )
    assert "declared once per namespace" in diag.rationale
    assert diag.fix.startswith("Rename this 'where' helper")
    assert diag.spec_ref == (
        'Chapter 8, Section 8.5.5 "One Declaration per Name"'
    )


def test_a_type_name_repeated_across_kinds_says_what_the_first_was(
    tmp_path: Path,
) -> None:
    """``data`` and ``type`` share one namespace, so the surplus may be a
    different kind of declaration from the first — and the rationale has to
    say which, or 'already declared' reads as false to an author looking at
    two different keywords."""
    cell = next(c for c in CELLS if c.id == "type/alias-then-data")
    (diag,) = _check(tmp_path, cell.files)
    assert diag.description == "Duplicate data type 'Foo' in this file."
    assert "at line 1, as a type alias." in diag.rationale


def test_a_helper_rebinding_a_parent_parameter_names_the_parent(
    tmp_path: Path,
) -> None:
    """The enclosing ``forall`` is where the first binding is, so the
    rationale says so rather than pointing inside the helper."""
    cell = next(c for c in CELLS
                if c.id == "tparam/helper-rebinds-parent-parameter")
    (diag,) = _check(tmp_path, cell.files)
    assert diag.description == "Duplicate type parameter 'T' in function 'h'."
    assert "already declared in function 'f' at line 1" in diag.rationale
    assert "stay in scope in its 'where' helpers" in diag.rationale


# ---------------------------------------------------------------------------
# The codegen backstop
# ---------------------------------------------------------------------------

_DEF_H = "  (func $f$where$h (param $p0 i64) (result i64)\n    local.get $p0)"


def test_the_backstop_refuses_one_identifier_defined_twice() -> None:
    """The second rail, exercised directly: no source passing the checker
    reaches it, so it is asserted against hand-built modules rather than
    left an unmeasured comment.  It names the symbol, because the reader of
    an internal error is a compiler author."""
    wat = "\n".join(["(module", _DEF_H, "  (func $other (result i64)\n"
                     "    i64.const 0)", _DEF_H, ")"])
    with pytest.raises(CodegenInvariantError, match=r"\$f\$where\$h"):
        AssemblyMixin._assert_unique_func_names(wat)


def test_the_backstop_counts_a_function_import_as_a_binding() -> None:
    """An import and a definition share one function index space."""
    wat = "\n".join([
        "(module",
        '  (import "vera" "print" (func $vera.print (param i32 i32)))',
        "  (func $vera.print (param i32 i32))",
        ")",
    ])
    with pytest.raises(CodegenInvariantError, match=r"\$vera\.print"):
        AssemblyMixin._assert_unique_func_names(wat)


def test_the_backstop_does_not_count_references() -> None:
    """The control: an export, an ``elem`` entry, a type's ``func`` and a
    call REFERENCE an identifier.  Without this the backstop could refuse
    every module that exports what it defines and the cells above would
    still pass."""
    wat = "\n".join([
        "(module",
        '  (import "vera" "print" (func $vera.print (param i32 i32)))',
        "  (type $closure_sig_0 (func (param i32) (result i32)))",
        "  (table 1 funcref)",
        "  (elem (i32.const 0) func $f$where$h)",
        '  (export "f" (func $f))',
        _DEF_H,
        '  (func $f (export "f") (param $p0 i64) (result i64)',
        "    local.get $p0",
        "    call $f$where$h)",
        ")",
    ])
    AssemblyMixin._assert_unique_func_names(wat)  # must not raise


@pytest.mark.parametrize(
    "cell_id,symbol",
    [("fn/twice", r"\$f\b"), ("where/twice", r"\$f\$where\$h")],
)
def test_a_compile_that_skips_the_checker_ends_in_an_e699(
    cell_id: str, symbol: str,
) -> None:
    """End to end through the real code generator, with the checker skipped
    — the "future path that bypasses it" the backstop exists for.  The
    compile reports one E699 naming the symbol and produces no binary, and
    wasm-tools' own message never appears."""
    cell = next(c for c in CELLS if c.id == cell_id)
    source = cell.files["main.vera"]
    result = codegen_compile(parse_to_ast(source), source=source,
                             file="main.vera")
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert [d.error_code for d in errors] == ["E699"], [
        (d.error_code, d.description) for d in errors]
    assert re.search(symbol, errors[0].description), errors[0].description
    assert "duplicate func identifier" in errors[0].description
    assert "WAT compilation failed" not in errors[0].description
    assert result.wasm_bytes == b""
