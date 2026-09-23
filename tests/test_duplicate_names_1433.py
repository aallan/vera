"""#1433: a namespace holds one declaration of each name (spec §8.5.5).

Two ``where`` helpers of one name in one block were check-clean and
verify-clean, then failed codegen with wasm-tools' ``duplicate func
identifier`` against ``$f$where$h``, a mangled symbol the author never wrote.
That is one instance of a class: every namespace the checker registers a
declared name into was a table written last-wins with no duplicate check, so a
second declaration replaced the first, left it unreachable, and the program
failed later and elsewhere.  Measured at the base, beside the reported shape:
two top-level functions of one name died the same way (and inside a module
silently ran the first), two clauses for one operation ran the later one,
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
  program must also verify, compile, and run to its value — for a shadowing
  cell, one only the declaration the rule says wins can give.  A spelling
  the grammar cannot
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
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

import pytest

from vera import ast
import vera.checker as vera_checker_pkg
from vera.checker import typecheck
from vera.checker.core import TypeChecker
from vera.codegen import compile as codegen_compile
from vera.codegen.assembly import AssemblyMixin
from vera.environment import TypeEnv
from vera.errors import Diagnostic, VeraError
from vera.monomorphize import MonoContext, Monomorphizer
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.skip import CodegenInvariantError
from vera.verifier import verify
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

_LIBF = _module("libf", _fn("f", body="@Int.0 + 100"),
                _fn("g", body="@Int.0 + 200"))
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
        frozenset({"TypeEnv.functions", "FnDecl", "FnDecl.name",
                   "Program.declarations", "TypeChecker._ns_first_decls",
                   "TypeChecker._top_level_fn_infos",
                   "TypeChecker._module_functions",
                   "TypeChecker._module_all_functions"}), "file"),
    "where_helper": Namespace(
        frozenset({"FnDecl.where_fns", "FnDecl.name",
                   "TypeChecker._where_helper_parents"}), "`where` block"),
    "type": Namespace(
        frozenset({"TypeEnv.data_types", "TypeEnv.type_aliases",
                   "DataDecl", "TypeAliasDecl", "DataDecl.name",
                   "TypeAliasDecl.name", "Program.declarations",
                   "TypeChecker._ns_first_decls",
                   "TypeChecker._module_data_types",
                   "TypeChecker._module_all_data_types"}), "file"),
    "constructor": Namespace(
        frozenset({"TypeEnv.constructors", "AdtInfo.constructors",
                   "DataDecl.constructors", "Constructor.name",
                   "TypeChecker._ns_ctor_owners",
                   "TypeChecker._module_constructors"}), "file"),
    "effect": Namespace(
        frozenset({"TypeEnv.effects", "EffectDecl", "EffectDecl.name",
                   "Program.declarations",
                   "TypeChecker._ns_first_decls"}), "file"),
    "effect_operation": Namespace(
        frozenset({"EffectInfo.operations", "EffectDecl.operations",
                   "OpDecl.name"}), "effect"),
    "ability": Namespace(
        frozenset({"TypeEnv.abilities", "AbilityDecl", "AbilityDecl.name",
                   "Program.declarations",
                   "TypeChecker._ns_first_decls"}), "file"),
    "ability_operation": Namespace(
        frozenset({"AbilityInfo.operations", "AbilityDecl.operations",
                   "OpDecl.name", "TypeChecker._ns_ability_ops"}),
        "every ability in scope, the built-in ones included"),
    "handler_clause": Namespace(
        frozenset({"HandleExpr.clauses", "HandlerClause.op_name"}),
        "`handle` expression"),
    "type_parameter": Namespace(
        frozenset({"TypeEnv.type_params", "FnDecl.forall_vars",
                   "DataDecl.type_params", "TypeAliasDecl.type_params",
                   "EffectDecl.type_params", "AbilityDecl.type_params"}),
        "type-parameter list"),
    "import": Namespace(
        frozenset({"ImportDecl.names", "Program.imports",
                   "TypeChecker._import_names"}),
        "module path (the lists of one path are unioned)"),
}

#: Enumerated by the wiring cell, and not a namespace a declaration puts a
#: name in.  Each carries why.
NOT_NAMESPACES: dict[str, str] = {
    # -- names that REFER to a declaration made elsewhere --------------------
    "AbilityConstraint.ability_name": "a constraint refers to an ability",
    "AbilityConstraint.type_var": "a constraint refers to a type parameter",
    "FnDecl.forall_constraints": (
        "constraints refer to abilities and to the function's type "
        "parameters; they declare neither"),
    "ConstructorCall.name": "a construction refers to a constructor",
    "ConstructorPattern.name": "a pattern refers to a constructor",
    "NullaryConstructor.name": "a construction refers to a constructor",
    "NullaryConstructor.owner": "the resolved owner of a referenced constructor",
    "NullaryPattern.name": "a pattern refers to a constructor",
    "LetDestruct.constructor": "a destructuring `let` refers to a constructor",
    "EffectRef.name": "an effect row refers to an effect",
    "QualifiedEffectRef.module": "a qualified effect refers to a module",
    "QualifiedEffectRef.name": "a qualified effect refers to an effect",
    "FnCall.name": "a call refers to a function",
    "QualifiedCall.qualifier": "a qualified call refers to an effect or ability",
    "QualifiedCall.name": "a qualified call refers to an operation",
    "ModuleCall.name": "a module-qualified call refers to a function",
    "NamedType.name": "a type expression refers to a type",
    # -- module paths ------------------------------------------------------
    "ImportDecl.path": (
        "a module path names a FILE for the resolver (§8.6.1); what an "
        "import admits from it is `ImportDecl.names`, unioned per path"),
    "ModuleDecl.path": (
        "a file declares its own path once — the grammar admits one "
        "`module` declaration"),
    "ModuleCall.path": "a module-qualified call REFERENCES a path",
    "Program.module": "the file's own `module` declaration, one per file",
    # -- not names at all ---------------------------------------------------
    "SlotRef.type_name": "a slot reference names a TYPE and an index (§3)",
    "ResultRef.type_name": "a result reference names a TYPE (§6)",
    "StringLit.value": "literal text",
    "StringPattern.value": "literal text",
    "InterpolatedString.parts": "literal text and the expressions between it",
    "FnDecl.param_annotations": "annotation-comment labels (§1.3), not names",
    "FnDecl.return_annotation": "an annotation-comment label (§1.3)",
    "TopLevelDecl.visibility": "the `public` / `private` keyword",
    # -- checker tables not keyed by a declared name --------------------------
    "TypeChecker._scoped_fn_info_cache": (
        "keyed by a declaration's IDENTITY, a memo of `_fn_info_for_decl`"),
    "TypeChecker._literal_range_verdict": (
        "keyed by a literal's source span, a memo of the range check"),
    "TypeChecker.expr_types": "keyed by source span, the LSP's side table",
    "TypeChecker.expr_semantic_types": "keyed by source span, for the verifier",
    "TypeChecker.expr_target_types": "keyed by source span, for codegen",
}

_MAPPING_ORIGINS = ("dict", "Dict", "Mapping", "MutableMapping",
                    "defaultdict", "OrderedDict", "ChainMap", "Counter")


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
    under ``TYPE_CHECKING`` (stood in for by ``object``: no table is typed by
    one)."""
    stand_ins: dict[str, typing.Any] = {}
    while True:
        try:
            return typing.get_type_hints(cls, localns=stand_ins)
        except NameError as exc:
            assert exc.name and exc.name not in stand_ins, exc
            stand_ins[exc.name] = object


def _is_mapping_type(tp: object) -> bool:
    """Any mapping origin, through ``X | None``: ``dict``, ``Mapping``,
    ``defaultdict`` and the rest are one kind of table to a duplicate."""
    union = typing.get_origin(tp) in (typing.Union, types.UnionType)
    for option in typing.get_args(tp) if union else (tp,):
        origin = typing.get_origin(option) or option
        if isinstance(origin, type) and issubclass(origin, Mapping):
            return True
    return False


def _holds_str(tp: object) -> bool:
    """Whether a value of annotation *tp* can hold a ``str``, at any depth
    of ``X | None``, ``tuple[...]``, ``list[...]`` or a union."""
    if tp is str:
        return True
    return any(_holds_str(a) for a in typing.get_args(tp) if a is not Ellipsis)


def _node_elements(tp: object) -> list[type]:
    """The AST node classes a container annotation holds."""
    out: list[type] = []
    for a in typing.get_args(tp):
        if a is Ellipsis:
            continue
        if isinstance(a, type) and issubclass(a, ast.Node):
            out.append(a)
        else:
            out.extend(_node_elements(a))
    return out


def _declares_a_name(cls: type) -> bool:
    """Whether a node class carries a string field, whatever it is called."""
    if not dataclasses.is_dataclass(cls):
        return False
    hints = _hints(cls)
    return any(f.name != "span" and _holds_str(hints[f.name])
               for f in dataclasses.fields(cls))


_WIRING_FIXTURE = {
    "libw.vera": (
        "module libw;\n\npublic data Box { Bx(Int) }\n\n"
        "public fn lf(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  @Int.0\n}\n"),
    "main.vera": (
        "import libw(lf, Box);\nimport libw;\n\ntype Cnt = Int;\n\n"
        "effect Ping {\n  op ping(Unit -> Int);\n}\n\n"
        "ability Sz<T> {\n  op size(T -> Int);\n}\n\n"
        "public data Pair { Pr(Int, Int) }\n\n"
        "public forall<T> fn f(@T -> @Int)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n  h(1)\n}\nwhere {\n"
        "  fn h(@Int -> @Int)\n    requires(true)\n    ensures(true)\n"
        "    effects(pure)\n  {\n    @Int.0\n  }\n}\n\n"
        "public fn g(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  handle[State<Int>](@Int = 0) {\n"
        "    get(@Unit) -> { resume(@Int.0) },\n"
        "    put(@Int) -> { resume(()) }\n  } in {\n"
        "    get(()) + lf(1) + libw::lf(2)\n  }\n}\n"),
}


def _checker_after_a_check(tmp_path: Path) -> TypeChecker:
    """A checker that has checked a program exercising every registration
    path — modules, both import forms, helpers, an alias, an effect, an
    ability, a handler — so its tables hold what they hold in use."""
    main_path = _write(tmp_path, _WIRING_FIXTURE)
    source = _WIRING_FIXTURE["main.vera"]
    program = parse_to_ast(source)
    resolved = ModuleResolver(_root=tmp_path).resolve_imports(
        program, main_path)
    checker = TypeChecker(source=source, file=str(main_path),
                          resolved_modules=resolved)
    checker.check_program(program)
    assert not checker.errors, [e.description for e in checker.errors]
    return checker


def _annotated_checker_tables() -> set[str]:
    """``self.X`` attributes the checker's own source ANNOTATES as a mapping,
    or assigns a mapping literal — so a table that holds ``None`` until some
    path fills it is enumerated even when the fixture leaves it empty."""
    import ast as pyast
    found: set[str] = set()
    for path in sorted(Path(vera_checker_pkg.__file__).parent.glob("*.py")):
        tree = pyast.parse(path.read_text(encoding="utf-8"))
        for node in pyast.walk(tree):
            target, annotation, value = None, None, None
            if isinstance(node, pyast.AnnAssign):
                target, annotation, value = node.target, node.annotation, node.value
            elif isinstance(node, pyast.Assign) and len(node.targets) == 1:
                target, value = node.targets[0], node.value
            if not (isinstance(target, pyast.Attribute)
                    and isinstance(target.value, pyast.Name)
                    and target.value.id == "self"):
                continue
            text = pyast.unparse(annotation) if annotation is not None else ""
            literal = isinstance(value, pyast.Dict) or (
                isinstance(value, pyast.Call)
                and isinstance(value.func, pyast.Name)
                and value.func.id in _MAPPING_ORIGINS)
            if literal or any(o in text for o in _MAPPING_ORIGINS):
                found.add(f"TypeChecker.{target.attr}")
    return found


def enumerated_registrations(tmp_path: Path) -> set[str]:
    """Every table a declared name could be registered in, and every AST
    field that could hold one — read from the code, never listed.

    * the checker's and ``TypeEnv``'s attributes whose VALUE is a mapping
      after a check, plus the ones their source or dataclass annotation
      types as a mapping (through ``X | None``), so an ``Optional`` table
      the fixture leaves ``None`` still counts;
    * the mapping fields of the records ``TypeEnv``'s tables hold, by
      annotation and by value;
    * the AST's declaration classes, every AST field that can hold a
      ``str`` whatever it is called, and every AST field holding nodes that
      carry one.
    """
    found: set[str] = set()
    checker = _checker_after_a_check(tmp_path)
    for attr, value in vars(checker).items():
        if isinstance(value, Mapping):
            found.add(f"TypeChecker.{attr}")
    found |= _annotated_checker_tables()
    env = checker.env
    env_hints = _hints(TypeEnv)
    records: set[type] = set()
    for f in dataclasses.fields(TypeEnv):
        value = getattr(env, f.name)
        if isinstance(value, Mapping) or _is_mapping_type(env_hints[f.name]):
            found.add(f"TypeEnv.{f.name}")
        if isinstance(value, Mapping):
            records |= {type(v) for v in value.values()
                        if dataclasses.is_dataclass(v)}
    for record in sorted(records, key=lambda c: c.__name__):
        record_hints = _hints(record)
        for g in dataclasses.fields(record):
            if _is_mapping_type(record_hints[g.name]):
                found.add(f"{record.__name__}.{g.name}")
    found.update(c.__name__ for c in _all_subclasses(ast.Decl))
    for cls in _all_subclasses(ast.Node):
        if not dataclasses.is_dataclass(cls):
            continue
        hints = _hints(cls)
        for f in dataclasses.fields(cls):
            if f.name == "span":
                continue
            tp = hints[f.name]
            if _holds_str(tp) or any(
                    _declares_a_name(e) for e in _node_elements(tp)):
                found.add(f"{cls.__name__}.{f.name}")
    return found


def test_every_registration_the_code_holds_is_claimed(tmp_path: Path) -> None:
    """The wiring cell: the matrix's rows ARE the namespaces in the code.

    Both directions.  An enumerated table or name field no row claims is a
    namespace that could accept a duplicate unmeasured; a claim nothing
    enumerates is a row describing a namespace that no longer exists.
    """
    claimed: set[str] = set(NOT_NAMESPACES)
    for ns in NAMESPACES.values():
        claimed |= ns.claims
    assert not set(NOT_NAMESPACES) & set().union(
        *(ns.claims for ns in NAMESPACES.values())), "claimed and excused"
    enumerated = enumerated_registrations(tmp_path)
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

SPELLINGS = ("same_scope", "nested_scope", "across_modules", "builtin")


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
    ``pinned`` marks a legal cell that holds a KNOWN defect at today's
    value, naming the issue and the correct value: the day the issue is
    fixed the value changes and the cell fails, and it is flipped to the
    correct one.  A pin rather than an ``xfail`` because
    ``check_doc_counts.py`` gates TESTING.md's breakdown as passed +
    stress-deselected + skipped, with no term for an xfailed test — the
    convention ``test_binder_position_generator.py`` states.
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
    pinned: str | None = None


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
    _c("fn/shadows-prelude-combinator", "function", "builtin",
       _fn("option_unwrap_or", sig="@Option<Int>, @Int -> @Int", body="99")
       + "\n" + _main("option_unwrap_or(None, 5)"),
       "legal", value=99),
    _c("fn/redefines-built-in", "function", "builtin",
       _fn("string_length", sig="@String -> @Int", body="1") + "\n"
       + _main('string_length("ab")'),
       "E151"),
    # A prelude BODY calls the user's override: `json_get_string` reaches
    # this `json_get`, so the program returns 0 where the prelude's own
    # `json_get` gives 2.  Pinned at 0 until owner-qualified prelude
    # symbols (#1495) make it 2.
    _c("fn/prelude-body-calls-an-override", "function", "builtin",
       _fn("json_get", sig="@Json, @String -> @Option<Json>", body="None",
           vis="private ") + "\n"
       + _main('match json_parse("{\\"a\\": \\"bc\\"}") {\n'
               '    Ok(@Json) -> match json_get_string(@Json.0, "a") {\n'
               '      Some(@String) -> string_length(@String.0),\n'
               '      None -> 0\n    },\n'
               '    Err(@String) -> 0 - 1\n  }'),
       "legal", value=0,
       pinned="#1495: a prelude body binds to the program's override of a "
              "prelude function; the correct value is 2"),

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
    _c("where/helper-named-like-a-built-in", "where_helper", "builtin",
       _fn("f", body="string_length(\"ab\")",
           where=_helper("string_length", sig="@String -> @Int", body="1"))
       + "\n" + _main("f(1)"),
       "E151"),
    # Refused as E151 already, so neither holds the name for the other to
    # repeat: two E151s and no E184.
    _c("where/two-helpers-named-like-a-built-in", "where_helper", "builtin",
       _fn("f", body="1",
           where=_helper("string_length", sig="@String -> @Int", body="1")
           + "\n" + _helper("string_length", sig="@String -> @Int",
                             body="2"))
       + "\n" + _main("f(1)"),
       "E151", count=2),
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
    # #1497: a primitive's name resolves before any declaration, so these
    # could never be named.
    _c("type/data-named-after-a-primitive", "type", "builtin",
       "public data Int { I(Bool) }\n\n" + _main("1"),
       "E158"),
    _c("type/alias-named-after-a-primitive", "type", "builtin",
       "type Bool = Int;\n\n" + _main("1"),
       "E158"),
    _c("type/data-named-Tuple", "type", "builtin",
       "public data Tuple { T1(Int) }\n\n" + _main("1"),
       "E158"),
    _c("type/entry-restates-prelude-type", "type", "builtin",
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
    _c("ctor/named-Tuple", "constructor", "builtin",
       "public data Box { Tuple(Bool) }\n\n" + _main("1"),
       "E158"),
    _c("ctor/shadows-prelude-constructor", "constructor", "builtin",
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
    _c("effect/redeclares-built-in", "effect", "builtin",
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
    # A declared effect's `get` and `State`'s `get` are two effects'
    # operation lists; the handled body's bare `get` is `State`'s (§7.4).
    _c("op/shares-a-built-in-effects-op-name", "effect_operation",
       "builtin",
       "effect Counter {\n  op get(Unit -> Int);\n}\n\n"
       + _fn("g", sig="@Unit -> @Int",
             body=_handle_state(_GET + ",\n" + _PUT, body="get(())"))
       + "\n" + _main("g(()) + 7"),
       "legal", value=7),
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
    # E185: the built-in stays canonical; code generation compiles `eq`
    # against it whatever a declaration says.
    _c("ability/redeclares-a-built-in", "ability", "builtin",
       "ability Eq<T> {\n  op eq(T, T -> Bool);\n}\n\n"
       + _main("if eq(1, 2) then { 1 } else { 0 }"),
       "E185"),
    # The name alone is the refusal: `render` is not a built-in operation.
    _c("ability/redeclares-a-built-in-with-its-own-op", "ability", "builtin",
       "ability Show<T> {\n  op render(T -> String);\n}\n\n" + _main("1"),
       "E185"),
    _c("ability/module-redeclares-a-built-in", "ability", "across_modules",
       "import libab;\n\n" + _main("z(1)"),
       "E185",
       modules={"libab": _module(
           "libab", "ability Hash<T> {\n  op hash(T -> Int);\n}\n",
           _fn("z"))}),
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
       "ability Sz<T> {\n  op size(T -> Int);\n  op size(T -> Bool);\n}"
       "\n\n" + _main("size(1)"),
       "E184", surplus=("main.vera", r"^  op size\(")),
    # One namespace across abilities: a bare `size(1)` bound to whichever
    # ability came first in the file (#1488 review, finding 2).
    _c("aop/two-abilities-share-a-name", "ability_operation",
       "sibling_scope",
       "ability Sz<T> {\n  op size(T -> Int);\n}\n\n"
       "ability Len<T> {\n  op size(T -> Bool);\n}\n\n"
       + _main("size(1)"),
       "E184", surplus=("main.vera", r"^  op size\(")),
    # ...and the built-in abilities are in it: `eq(1, 1)` reached `Eq.eq`,
    # so `MyEq`'s operation could never be called.
    _c("aop/named-like-a-built-in-op", "ability_operation", "builtin",
       "ability MyEq<T> {\n  op eq(T, T -> Int);\n}\n\n"
       + _main("if eq(1, 1) then { 1 } else { 0 }"),
       "E185"),
    _c("aop/module-ability-twice", "ability_operation", "across_modules",
       "import libaop;\n\n" + _main("z(1)"),
       "E184", surplus=("libaop.vera", r"^  op size\("),
       modules={"libaop": _module(
           "libaop", "ability Sz<T> {\n  op size(T -> Int);\n"
                     "  op size(T -> Int);\n}\n",
           _fn("z", body="size(@Int.0)"))}),

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
    # Three binders, two surplus: each report names its binder's place in
    # the list, or the checker's exact-duplicate dedup would keep one.
    _c("tparam/forall-three-times", "type_parameter", "same_scope",
       _fn("idf", sig="@T -> @T", body="@T.0", forall="forall<T, T, T> ")
       + "\n" + _main("idf(1)"),
       "E184", count=2,
       surplus=("main.vera", r"^public forall<T, T, T> fn idf\("),
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
    # A helper's own `forall<T>` shadows its parent's inside the helper.
    # At the base the substitution for the parent reached through it, so a
    # parent at `Bool` cloned the helper at `Bool` whatever it was called
    # at: `h(7)` called an i32 clone with an i64 and `f$Bool` failed to load.
    _c("tparam/helper-rebinds-parent-parameter-other-type", "type_parameter",
       "nested_scope",
       _fn("f", sig="@T -> @Int", body="h(7)", forall="forall<T> ",
           where=_helper("h", sig="@T -> @Int", body="41",
                         forall="forall<T> "))
       + "\n" + _main("f(true)"),
       "legal", value=41),
    _c("tparam/helper-rebinds-parent-parameter-same-type", "type_parameter",
       "nested_scope",
       _fn("f", sig="@T -> @T", body="h(@T.0)", forall="forall<T> ",
           where=_helper("h", sig="@T -> @T", body="@T.0",
                         forall="forall<T> "))
       + "\n" + _main("f(41) + 1"),
       "legal", value=42),
    # The parent at `Int` collapses the helper's `@A` into `@Int` unless the
    # substitution stops at the helper's binder — and then `@Int.0` is
    # re-indexed to a binding the helper does not have.
    _c("tparam/helper-rebinds-parent-parameter-reindexed", "type_parameter",
       "nested_scope",
       _fn("f", sig="@A -> @Int", body="h(5, true)", forall="forall<A> ",
           where=_helper("h", sig="@Int, @A -> @Int", body="@Int.0",
                         forall="forall<A> "))
       + "\n" + _main("f(1)"),
       "legal", value=5),
    _c("tparam/helper-rebinds-parent-parameter-both-types", "type_parameter",
       "nested_scope",
       _fn("f", sig="@T -> @Int", body="h(@T.0) + h(7)",
           forall="forall<T> ",
           where=_helper("h", sig="@T -> @Int", body="20",
                         forall="forall<T> "))
       + "\n" + _main("f(true) + f(5) * 100"),
       "legal", value=4040),
    # The other half of capture: a helper binder NAMED LIKE a type the
    # parent is instantiated at.  The parent's `U -> Int` put an `Int` into
    # the helper, where its own `forall<Int>` bound it, so the helper's
    # later instantiation rewrote the parent's type as well — a load
    # failure, or, when the captured name sits inside a type argument, a
    # wrong answer from a structural `eq` read at the wrong width.
    _c("tparam/helper-binder-named-like-the-parent-instance", "type_parameter",
       "nested_scope",
       _fn("f", sig="@U -> @U", body="h(true, @U.0)", forall="forall<U> ",
           where=_helper("h", sig="@Int, @U -> @U", body="@U.0",
                         forall="forall<Int> "))
       + "\n" + _main("f(5)"),
       "legal", value=5),
    _c("tparam/helper-binder-named-like-the-parent-instance-own-slot",
       "type_parameter", "nested_scope",
       _fn("f", sig="@U -> @Int",
           body="if h(true, @U.0) then { 11 } else { 22 }",
           forall="forall<U> ",
           where=_helper("h", sig="@Int, @U -> @Int", body="@Int.0",
                         forall="forall<Int> "))
       + "\n" + _main("f(5)"),
       "legal", value=11),
    # Called at the captured type itself: the helper's own `Int` and the
    # parent's merge in the helper's clone, and `@Int.0` must still name
    # the helper's own parameter.
    _c("tparam/helper-binder-named-like-the-parent-instance-called-at-it",
       "type_parameter", "nested_scope",
       _fn("f", sig="@U -> @Int", body="h(7, @U.0)", forall="forall<U> ",
           where=_helper("h", sig="@Int, @U -> @Int", body="@Int.0",
                         forall="forall<Int> "))
       + "\n" + _main("f(5)"),
       "legal", value=7),
    # The binder's ability constraint is renamed with it.
    _c("tparam/helper-binder-named-like-the-parent-instance-constrained",
       "type_parameter", "nested_scope",
       _fn("f", sig="@U -> @Int",
           body="if h(true, true, @U.0) then { 1 } else { 0 }",
           forall="forall<U> ",
           where=_helper("h", sig="@Int, @Int, @U -> @Bool",
                         body="eq(@Int.1, @Int.0)",
                         forall="forall<Int where Eq<Int>> "))
       + "\n" + _main("f(5)"),
       "legal", value=1),
    _c("tparam/helper-binder-named-like-an-adt-instance", "type_parameter",
       "nested_scope",
       "public data Box {\n  B(Int)\n}\n\n"
       + _fn("f", sig="@U -> @U", body="h(1, @U.0)", forall="forall<U> ",
             where=_helper("h", sig="@Box, @U -> @U", body="@U.0",
                           forall="forall<Box> "))
       + "\n" + _main("match f(B(7)) {\n    B(@Int) -> @Int.0\n  }"),
       "legal", value=7),
    _c("tparam/helper-binder-captures-a-type-argument", "type_parameter",
       "nested_scope",
       _fn("f", sig="@U, @U -> @Bool", body="h(true, @U.1, @U.0)",
           forall="forall<U where Eq<U>> ",
           where=_helper("h", sig="@Int, @U, @U -> @Bool",
                         body="eq(@U.1, @U.0)", forall="forall<Int> "))
       + "\n"
       + _main("if f(Some(1), Some(4294967297)) then { 1 } else { 0 }"),
       "legal", value=0),
    _c("tparam/nested-helper-binder-named-like-the-parent-instance",
       "type_parameter", "nested_scope",
       _fn("f", sig="@U -> @U", body="g(@U.0)", forall="forall<U> ",
           where=_helper("g", sig="@U -> @U", body="h(true, @U.0)",
                         where="".join(
                             "  " + line + "\n" for line in _helper(
                                 "h", sig="@Int, @U -> @U", body="@U.0",
                                 forall="forall<Int> ",
                             ).splitlines())))
       + "\n" + _main("f(5)"),
       "legal", value=5),
    # The renamed binder is a type VARIABLE: a sibling generic called at it
    # is not an instantiation, any more than one called at a source binder.
    _c("tparam/helper-binder-named-like-the-parent-instance-calls-a-sibling",
       "type_parameter", "nested_scope",
       _fn("f", sig="@U -> @U", body="h(true, @U.0)", forall="forall<U> ",
           where=_helper("h", sig="@Int, @U -> @U", body="k(@Int.0, @U.0)",
                         forall="forall<Int> ") + "\n"
           + _helper("k", sig="@W, @U -> @U", body="@U.0",
                     forall="forall<W> "))
       + "\n" + _main("f(5)"),
       "legal", value=5),
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
    # A binder named after a primitive shadows it inside its function.
    _c("tparam/named-like-a-built-in-type", "type_parameter", "builtin",
       _fn("f", sig="@Int -> @Int", body="@Int.0", forall="forall<Int> ")
       + "\n" + _main('string_length(f("abc"))'),
       "legal", value=3),
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
    # Two lists for one module admit their union (§8.5.5).  At the base the
    # checker, the verifier and codegen each kept the LAST list: the bare
    # calls ran and `libf::f` was refused with E231.
    _c("import/two-lists-qualified", "import", "same_scope",
       "import libf(f);\nimport libf(g);\n\n"
       + _main("libf::f(1) * 1000 + libf::g(1)"),
       "legal", value=101201, modules={"libf": _LIBF}),
    _c("import/two-lists-bare", "import", "same_scope",
       "import libf(f);\nimport libf(g);\n\n"
       + _main("f(1) * 1000 + g(1)"),
       "legal", value=101201, modules={"libf": _LIBF}),
    _c("import/two-lists-generic-bare", "import", "same_scope",
       "import libgen(gid);\nimport libgen(g);\n\n"
       + _main("gid(5) + g(1)"),
       "legal", value=6,
       modules={"libgen": _module(
           "libgen", _fn("g"),
           _fn("gid", sig="@T -> @T", body="@T.0", forall="forall<T> "))}),
    # A whole-module import subsumes a selective one, in either order.
    _c("import/whole-then-selective", "import", "same_scope",
       "import libf;\nimport libf(f);\n\n"
       + _main("libf::g(1) * 1000 + g(2)"),
       "legal", value=201202, modules={"libf": _LIBF}),
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
        "imports are file-level, before every declaration",
        _fn("f") + "where {\n  import libf;\n}\n"),
    ("handler_clause", "builtin"): (
        "a clause names an operation of the effect its handler handles, "
        "built-in or declared; clauses of different handlers never share a "
        "namespace, so there is no built-in clause to collide with",
        None),
    ("import", "builtin"): (
        "the built-ins and the prelude are in scope without an import "
        "(§8.4.1); no import list can name or repeat them",
        None),
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
    """Not a duplicate — and the program works.  For a shadowing cell the
    value is one only the declaration the rule says wins can give."""
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, cell.files,
    )
    assert verify_errors == [], (cell.id, verify_errors)
    assert cg_errors == [], (cell.id, cg_errors)
    assert module_value(result) == ("ok", cell.value), (
        cell.id if cell.pinned is None else
        f"{cell.id} is pinned at a known defect — {cell.pinned}.  If the "
        f"value moved to the correct one, the issue is fixed: flip the cell")


_CAPTURE = [c for c in _LEGAL if "-binder-" in c.id]


@pytest.mark.parametrize("cell", _CAPTURE, ids=[c.id for c in _CAPTURE])
def test_a_helper_binder_renamed_apart_leaves_no_trace(
    tmp_path: Path, cell: Cell,
) -> None:
    """The renaming that stops a parent's substitution capturing a helper
    binder is internal to the monomorphiser.  No clone is minted at the
    renamed binder, which is a type variable and not an instantiation, so
    no function symbol carries it and no skip warning names one."""
    _, result, _ = build_multi_module(tmp_path, cell.files)
    assert "shadowed" not in result.wat, (cell.id, re.findall(
        r"\(func \$(\S*shadowed\S*)", result.wat))
    skips = [(d.error_code, d.description) for d in result.diagnostics
             if d.error_code in {"E602", "E604", "E605"}]
    assert skips == [], (cell.id, skips)


def test_a_renamed_binder_takes_its_constraint_with_it() -> None:
    """A constraint names a binder of its own function, the rule the
    checker enforces as E181, and a clone keeps to it: the ability gate and
    the constrained-variable inference both look the constraint's variable
    up among the helper's binders.  Renaming the binder without its
    constraint leaves the constraint naming nothing."""
    cell = next(c for c in CELLS if c.id == (
        "tparam/helper-binder-named-like-the-parent-instance-constrained"))
    program = parse_to_ast(cell.files["main.vera"])
    parent = next(tld.decl for tld in program.declarations
                  if isinstance(tld.decl, ast.FnDecl) and tld.decl.name == "f")
    ctx = MonoContext(
        generic_decls={}, ctor_to_adt={}, ctor_tp_indices={},
        adt_tp_counts={}, type_aliases={}, type_alias_params={},
        fn_ret_types={},
    )
    clone = Monomorphizer(ctx).monomorphize_fn(parent, ("Int",))
    (helper,) = clone.where_fns or ()
    assert helper.forall_vars is not None
    assert helper.forall_vars != ("Int",), helper.forall_vars
    assert [c.type_var for c in helper.forall_constraints or ()] == list(
        helper.forall_vars), (helper.forall_vars, helper.forall_constraints)


# Registration refuses a member — an operation or a constructor — and the
# check phase must not then type its signature, or a refused member reports
# a second error the program does not owe.  Each refused member below
# carries a refinement predicate that is not Bool, so checking it would add
# an E126 beside the refusal.
_NOT_BOOL = "{ @Int | 5 }"
_REFUSED_MEMBER_CASES = {
    "effect-operation-twice": (
        f"effect E {{\n  op a(Int -> Int);\n  op a({_NOT_BOOL} -> Int);\n}}",
        "E184"),
    "ability-operation-twice": (
        f"ability Sz<T> {{\n  op size(T -> Int);\n"
        f"  op size({_NOT_BOOL} -> Int);\n}}",
        "E184"),
    "operation-in-two-abilities": (
        f"ability Aa<T> {{\n  op sz(T -> Int);\n}}\n\n"
        f"ability Bb<T> {{\n  op sz({_NOT_BOOL} -> Int);\n}}",
        "E184"),
    "operation-named-like-a-built-in": (
        f"ability Mine<T> {{\n  op eq({_NOT_BOOL}, T -> Bool);\n}}",
        "E185"),
    "constructor-twice": (
        f"public data D {{\n  A(Int),\n  A({_NOT_BOOL})\n}}",
        "E184"),
    "constructor-named-like-a-special-cased-type": (
        f"public data D {{\n  Tuple({_NOT_BOOL})\n}}",
        "E158"),
    "built-in-effect-redeclared": (
        f"effect IO {{\n  op print({_NOT_BOOL} -> Unit);\n}}",
        "E152"),
}


@pytest.mark.parametrize("case", sorted(_REFUSED_MEMBER_CASES))
def test_the_check_phase_skips_what_registration_refused(
    tmp_path: Path, case: str,
) -> None:
    decls, code = _REFUSED_MEMBER_CASES[case]
    errors = _check(tmp_path, {"main.vera": decls + "\n\n" + _main("1")})
    assert [d.error_code for d in errors] == [code], (
        case, [(d.error_code, d.location.line, d.description)
               for d in errors])


# A helper whose OWN name is a built-in's is refused (E151) and holds no
# name.  A function that merely CONTAINS one is registered under its own
# name: only its body goes unchecked, since a call to the stripped helper
# would resolve against the built-in (#815).  Each program below must report
# the E151 and exactly the E184 it owes, and nothing else: no E178 for a
# call to the containing helper, and no type error from checking a body that
# calls its refused helper, whose signature differs from the built-in's.
_NESTED_E151 = _helper("string_length", sig="@String -> @Int", body="1")
_NESTED_E151_OTHER_SIG = _helper("string_length", body="@Int.0")
_CONTAINING_HELPER_CASES = {
    "repeats-the-containing-helper": (
        _fn("f", body="h(@Int.0)",
            where=_helper("h", where=_NESTED_E151) + "\n"
            + _helper("h", body="@Int.0 + 1"))
        + "\n" + _main("f(1)"),
        [("E151", r"^  fn string_length\("), ("E184", r"^  fn h\(")],
    ),
    "repeats-inside-the-containing-helper": (
        _fn("f", body="h(@Int.0)",
            where=_helper("h", body="k(@Int.0)", where=_NESTED_E151 + "\n"
                          + _helper("k") + "\n"
                          + _helper("k", body="@Int.0 + 1")))
        + "\n" + _main("f(1)"),
        [("E151", r"^  fn string_length\("), ("E184", r"^  fn k\(")],
    ),
    "calls-the-containing-helper": (
        _fn("f", body="h(@Int.0, true)",
            where=_helper("h", sig="@Int, @Bool -> @Int",
                          where=_NESTED_E151))
        + "\n" + _main("f(1)"),
        [("E151", r"^  fn string_length\(")],
    ),
    "a-helper-calls-its-refused-helper": (
        _fn("f", body="h(@Int.0)",
            where=_helper("h", body="string_length(@Int.0)",
                          where=_NESTED_E151_OTHER_SIG))
        + "\n" + _main("f(1)"),
        [("E151", r"^  fn string_length\(")],
    ),
    "a-function-calls-its-refused-helper": (
        _fn("f", body="string_length(@Int.0)",
            where=_NESTED_E151_OTHER_SIG)
        + "\n" + _main("f(1)"),
        [("E151", r"^  fn string_length\(")],
    ),
}


@pytest.mark.parametrize("case", sorted(_CONTAINING_HELPER_CASES))
def test_a_helper_containing_a_refused_helper_keeps_its_name(
    tmp_path: Path, case: str,
) -> None:
    """Each expected diagnostic sits on the LAST match of its pattern: the
    one E151 on the nested helper, and each E184 on the surplus."""
    source, expected = _CONTAINING_HELPER_CASES[case]
    errors = _check(tmp_path, {"main.vera": source})
    got = sorted((d.error_code, d.location.line) for d in errors)
    want = sorted((code, _lines_of(pattern, source)[-1])
                  for code, pattern in expected)
    assert got == want, (case, [(d.error_code, d.location.line,
                                 d.description) for d in errors])


def test_the_verifier_obligates_a_call_the_first_list_admits(
    tmp_path: Path,
) -> None:
    """Two lists for one module, and a call only the FIRST admits that
    violates its callee's precondition.  At the base the verifier kept the
    last list, never injected `f`, and so never obligated the call:
    `verify` passed a program that breaks `f`'s contract.  The one
    derivation gives the verifier the same union the checker reads."""
    files = {
        "libp.vera": _module("libp", _fn("f", body="@Int.0").replace(
            "  requires(true)\n", "  requires(@Int.0 > 0)\n", 1),
            _fn("g")),
        "main.vera": "import libp(f);\nimport libp(g);\n\n"
                     + _main("f(0) + g(1)"),
    }
    assert _check(tmp_path, files) == []
    main_path = tmp_path / "main.vera"
    program = parse_to_ast(files["main.vera"])
    resolved = ModuleResolver(_root=tmp_path).resolve_imports(
        program, main_path)
    result = verify(program, files["main.vera"], file=str(main_path),
                    resolved_modules=resolved)
    codes = [d.error_code for d in result.diagnostics
             if d.severity == "error"]
    assert codes == ["E501"], codes


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


def test_a_repeated_type_parameter_names_its_place_in_the_list(
    tmp_path: Path,
) -> None:
    """Binders in one list share a line, so the place in the list is what
    tells the two surplus reports apart — and what an author needs to find
    them."""
    cell = next(c for c in CELLS if c.id == "tparam/forall-three-times")
    first, second = _check(tmp_path, cell.files)
    assert first.description == (
        "Duplicate type parameter 'T' in function 'idf' (position 2 of its "
        "list)."
    )
    assert second.description == (
        "Duplicate type parameter 'T' in function 'idf' (position 3 of its "
        "list)."
    )
    assert first.rationale.startswith(
        "'T' is already declared in function 'idf' (position 1)."
    )


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
