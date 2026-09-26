"""#1277: a module's ADT name must not evict the prelude's from other scopes.

Two defects with one root — codegen keeps ONE flat `_adt_layouts` map and
ONE flat constructor namespace, while the checker gives every namespace
the prelude's data types from the start (`vera/environment.py` registers
`Option`, `Result`, `Ordering`, `UrlParts`, `Json`, `HtmlNode`,
`Request` and `Response` in every `TypeEnv`, unconditionally).

**Membership.**  `_adt_members_in_scope` recovers global infrastructure by
SUBTRACTING what the namespaces declare from the registered layouts.  The
subtraction is only sound while "declared by a namespace" and "global
infrastructure" are disjoint, and §8.4.1 makes them overlap on purpose:
the prelude's data types are ordinary public declarations a program names
and shadows.  So one file's `data Json` removed `Json` from every OTHER
namespace's member set.  The Pass-0.5 built-in snapshot unioned in as a
floor does not cover the four demand-injected prelude ADTs, because it is
taken before Pass 1.2 injects them.

**Contention.**  When the declaration is a MODULE's and the entry program
uses the prelude's type of that name, the two contend for the one layout
slot and the module wins: the prelude's own ADT is never registered, its
combinators hit `unknown constructor`, and every function that touches
the type is dropped — with the diagnostic pointing into `<prelude>` and
nothing naming the declaration that caused it.

Membership is asserted on `AliasEnv.data_types` / the member set itself
rather than on a rendering, for the reason
`test_adt_membership_scope_1253` states: that map changes an answer in
exactly one place (`naming._resolve_named`) and only for `Decimal` and
the single `REMOVED_ALIASES` entry `Float`, so no rendering can
distinguish a missing `Json`.  What is guarded is the set being
FACTUALLY right, against the checker's own answer as the oracle.

The two fixes are pinned separately and by different cases, so a
regression in either is attributable: the contention rail by the E621
cases, the membership floor by the two cases that never reach it.
"""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path

import pytest

from vera import ast, naming
from vera.checker.core import TypeChecker
from vera.codegen.core import CodeGenerator
from vera.errors import ERROR_CODES
from vera.parser import parse_file
from vera.prelude import inject_prelude
from vera.resolver import ModuleResolver
from vera.transform import transform

# `prelude_adt_names` is imported inside the one case that needs it, not
# at module scope: every other case here states a RED/GREEN claim about
# the state BEFORE this fix, and a module-level import of a symbol the
# fix introduces would make them un-runnable at that baseline (the
# collection error, not the assertion, would be the result).  Same
# discipline as `test_adt_membership_scope_1253`.

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

# The control for the rail: the same module declaration, and an entry that
# never names `Json`.  Nothing is injected, nothing contends, and §8.4.1
# says this must keep working.
_MAIN_IGNORES_JSON = """
import jlib(blob_size);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  blob_size(7)
}
"""

_PLIB_USES_JSON = """
public fn tally(@Json, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""

# The sanctioned §8.4.1 shadow: the ENTRY file declares `data Json`, so
# `inject_prelude` skips its own and one declaration serves the program.
_MAIN_DECLARES_JSON = """
import plib(tally);

public data Json {
  JNull,
  JBool(Bool),
  JNumber(Float64),
  JString(String),
  JArray(Array<Json>),
  JObject(Map<String, Json>)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  tally(JNull, 3)
}
"""


def _compile(tmp_path: Path, files: dict[str, str]) -> CodeGenerator:
    """Write *files*, compile ``main.vera``, hand back the generator."""
    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    program = transform(parse_file(str(main_path)))
    mods = ModuleResolver(tmp_path).resolve_imports(program, main_path)
    gen = CodeGenerator(
        source=main_path.read_text(encoding="utf-8"), file=str(main_path),
    )
    gen._resolved_modules = mods
    gen._result = gen.compile_program(program)  # type: ignore[attr-defined]
    return gen


def _checker_data_types(
    tmp_path: Path, module: str,
) -> frozenset[str]:
    """The names the CHECKER treats as data types inside *module*.

    The oracle for every membership claim below.  Built the way
    `_collect_module_artifacts` has since #987 — the module checked as
    ITSELF, with `direct` re-derived against it, because §8.6.4
    visibility is the importer's property.
    """
    main_path = tmp_path / "main.vera"
    program = transform(parse_file(str(main_path)))
    mods = ModuleResolver(tmp_path).resolve_imports(program, main_path)
    mod = next(m for m in mods if m.path == (module,))
    mod_direct = {imp.path for imp in mod.program.imports}
    scoped = TypeChecker(
        source=mod.source, file=str(mod.file_path),
        resolved_modules=[
            replace(other, direct=other.path in mod_direct)
            for other in mods if other.path != mod.path
        ],
    )
    scoped.check_program(mod.program)
    return frozenset(naming.alias_env_from_environment(scoped.env).data_types)


# ---------------------------------------------------------------------
# The contention rail (E621)
# ---------------------------------------------------------------------

def test_module_adt_contending_with_a_demanded_prelude_adt_is_loud(
    tmp_path: Path,
) -> None:
    """The dropped-everything shape reports at the declaration that caused it.

    At the branch point this program is `vera check`-green and then
    compiles with only WARNINGS — an E602 for `unknown constructor
    'JNull'` inside the prelude's own combinator and an E620 cascade
    behind it, every one of them located in `<prelude>` — while `depth`
    silently vanishes from the exports.  The assertions below are the
    three things that were wrong: the severity, the file, and whether
    anything names `Json`.
    """
    gen = _compile(
        tmp_path,
        {"jlib.vera": _JLIB_OWN_JSON, "main.vera": _MAIN_USES_PRELUDE_JSON},
    )
    result = gen._result  # type: ignore[attr-defined]
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert len(errors) == 1, [
        (d.severity, d.error_code, d.description) for d in result.diagnostics
    ]
    err = errors[0]
    assert err.error_code == "E621", err.error_code
    # It must point at the USER's declaration, in the module's own file —
    # `jlib.vera` line 2, where `private data Json` is written.
    assert Path(err.location.file).name == "jlib.vera", err.location.file
    assert err.location.line == 2, (err.location.line, err.source_line)
    assert "data Json" in err.source_line, err.source_line
    assert "Json" in err.description and "jlib" in err.description, (
        err.description)
    assert err.fix and err.rationale and err.spec_ref
    # And it refuses to emit rather than emitting a module missing `depth`.
    assert result.exports == [], result.exports


def test_the_rail_makes_the_cli_fail(tmp_path: Path) -> None:
    """`vera compile` exits non-zero on the contention shape.

    The whole point of the rail is the exit code: at the branch point
    every diagnostic in this program is a warning, so `cmd_compile`
    returned 0 over a module with the function silently missing.
    """
    from vera.cli import cmd_check, cmd_compile

    tmp_path.mkdir(parents=True, exist_ok=True)
    (tmp_path / "jlib.vera").write_text(_JLIB_OWN_JSON, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    main_path.write_text(_MAIN_USES_PRELUDE_JSON, encoding="utf-8")
    # `vera check` stays green: this is a codegen-namespace collision, not
    # a type error, and the checker gives both namespaces their own view.
    assert cmd_check(str(main_path), quiet=True) == 0
    assert cmd_compile(str(main_path), wat=True) == 1


def test_a_module_owning_its_prelude_named_adt_alone_still_compiles(
    tmp_path: Path,
) -> None:
    """Within-namespace shadowing is untouched — §8.4.1 permits it.

    Green before and after.  This is what separates "refuse a contention"
    from "reserve the prelude's names", which the spec forbids: nothing
    demands the prelude's `Json` here, so nothing contends, and the
    module's own type must keep working.
    """
    gen = _compile(
        tmp_path,
        {"jlib.vera": _JLIB_OWN_JSON, "main.vera": _MAIN_IGNORES_JSON},
    )
    result = gen._result  # type: ignore[attr-defined]
    assert [d for d in result.diagnostics if d.severity == "error"] == []
    assert result.exports == ["main"], result.exports
    # The module's own layout is the registered one, unchallenged.
    assert sorted(gen._adt_layouts["Json"]) == ["JBlob"]


def test_an_entry_file_shadow_is_not_a_contention(tmp_path: Path) -> None:
    """The entry file's own `data Json` serves the whole program.

    Green before and after — the second half of the same separation.
    `inject_prelude` skips its `data Json` here, so there is one
    declaration and one layout, and the rail must not fire.
    """
    gen = _compile(
        tmp_path,
        {"plib.vera": _PLIB_USES_JSON, "main.vera": _MAIN_DECLARES_JSON},
    )
    result = gen._result  # type: ignore[attr-defined]
    assert [d for d in result.diagnostics if d.severity == "error"] == []
    assert result.exports == ["main"], result.exports


def test_e621_is_registered(tmp_path: Path) -> None:
    """The code the rail emits exists in the registry `vera errors` reads."""
    assert "E621" in ERROR_CODES
    assert ERROR_CODES["E621"]


# ---------------------------------------------------------------------
# The membership floor
# ---------------------------------------------------------------------

def test_prelude_adt_stays_a_member_of_a_module_namespace(
    tmp_path: Path,
) -> None:
    """One file's `data Json` must not empty `Json` out of another namespace.

    A check-green, compile-green, error-free program: the ENTRY declares
    `data Json` (the sanctioned §8.4.1 shadow) and module `plib` takes a
    `@Json` parameter.  The checker gives `plib` the type; at the branch
    point codegen did not, because the entry's declaration was subtracted
    from the infrastructure set of every namespace including `plib`'s.

    Stated as a differential against the checker rather than against a
    literal, so "both sides agree on the wrong answer" cannot satisfy it.
    """
    gen = _compile(
        tmp_path,
        {"plib.vera": _PLIB_USES_JSON, "main.vera": _MAIN_DECLARES_JSON},
    )
    result = gen._result  # type: ignore[attr-defined]
    assert [d for d in result.diagnostics if d.severity == "error"] == []
    # There IS a layout to be a member of — otherwise the claim is vacuous.
    assert "Json" in gen._adt_layouts
    checker = _checker_data_types(tmp_path, "plib")
    assert "Json" in checker, "the checker's own answer moved"
    with gen._module_alias_scope(("plib",)):
        codegen = frozenset(gen._alias_env.data_types)
    assert "Json" in codegen, (
        f"checker sees Json in plib's namespace, codegen does not: "
        f"{sorted(codegen)}"
    )


def test_entry_namespace_keeps_the_prelude_adt_a_module_declares(
    tmp_path: Path,
) -> None:
    """The issue's measured shape: `members[None]` must not lose `Json`.

    Pinned independently of the E621 rail that now also refuses this
    program, so the membership rule is guarded on its own terms: if the
    rail is ever narrowed, the entry program's namespace still holds the
    prelude type it legitimately sees.  Read off `_adt_members_in_scope`,
    which is the set every consumer's `data_types` is filtered through.
    """
    gen = _compile(
        tmp_path,
        {"jlib.vera": _JLIB_OWN_JSON, "main.vera": _MAIN_USES_PRELUDE_JSON},
    )
    assert gen._active_module_path is None
    members = gen._adt_members_in_scope()
    assert members is not None, "no module structure — fixture is wrong"
    # The declaration IS in the subtracted set: that is the mechanism, and
    # pinning it here keeps the case honest if the bookkeeping is renamed.
    assert "Json" in gen._namespace_declared_adts
    assert "Json" in members, (
        f"the entry namespace lost the prelude's Json because module jlib "
        f"declared that name; members = {sorted(members)}"
    )


# ---------------------------------------------------------------------
# The rail covers all EIGHT prelude ADTs, and only real contentions
# ---------------------------------------------------------------------

_PRELUDE_ADTS = (
    "Option", "Result", "Ordering", "UrlParts",
    "Json", "HtmlNode", "Request", "Response",
)

# Entry bodies that use the PRELUDE's type of each name.  Written out
# rather than generated, because a generated body that failed to type-check
# would make a cell vacuous instead of failing.
_ENTRY_USE: dict[str, tuple[str, str]] = {
    "Option": ("@Option<Int>",
               "match @Option<Int>.0 {\n    Some(@Int) -> @Int.0,\n"
               "    None -> 0\n  }"),
    "Result": ("@Result<Int, Int>",
               "match @Result<Int, Int>.0 {\n    Ok(@Int) -> @Int.0,\n"
               "    Err(@Int) -> 0\n  }"),
    "Ordering": ("@Ordering",
                 "match @Ordering.0 {\n    Less -> 0,\n    Equal -> 1,\n"
                 "    Greater -> 2\n  }"),
    "UrlParts": ("@UrlParts",
                 "match @UrlParts.0 {\n    UrlParts(@String, @String,"
                 " @String, @String, @String) -> string_length(@String.0)\n"
                 "  }"),
    "Json": ("@Json", "json_array_length(@Json.0)"),
    "HtmlNode": ("@HtmlNode",
                 "match @HtmlNode.0 {\n    HtmlElement(@String,"
                 " @Map<String, String>, @Array<HtmlNode>) -> 1,\n"
                 "    HtmlText(@String) -> 2,\n"
                 "    HtmlComment(@String) -> 3\n  }"),
    "Request": ("@Request",
                "match @Request.0 {\n    Request(@String, @String,"
                " @Map<String, String>, @String) -> string_length(@String.0)\n"
                "  }"),
    "Response": ("@Response",
                 "match @Response.0 {\n    Response(@Int,"
                 " @Map<String, String>, @String) -> @Int.0\n  }"),
}

# A module declaration of each name that RESTATES the prelude's own shape.
# These are the legal shapes the rail must not fire on: one registered
# layout serves both declarations, which is why they compile and run.
_IDENTICAL_DECL: dict[str, str] = {
    "Option": "private data Option<T> {\n  None,\n  Some(T)\n}",
    "Result": "private data Result<T, E> {\n  Ok(T),\n  Err(E)\n}",
    "Ordering": "private data Ordering {\n  Less,\n  Equal,\n  Greater\n}",
    "UrlParts": ("private data UrlParts {\n  UrlParts(String, String,"
                 " String, String, String)\n}"),
    "Json": ("private data Json {\n  JNull,\n  JBool(Bool),\n"
             "  JNumber(Float64),\n  JString(String),\n"
             "  JArray(Array<Json>),\n  JObject(Map<String, Json>)\n}"),
    "HtmlNode": ("private data HtmlNode {\n  HtmlElement(String,"
                 " Map<String, String>, Array<HtmlNode>),\n"
                 "  HtmlText(String),\n  HtmlComment(String)\n}"),
    "Request": ("private data Request {\n  Request(String, String,"
                " Map<String, String>, String)\n}"),
    "Response": ("private data Response {\n  Response(Int,"
                 " Map<String, String>, String)\n}"),
}


def _blib(name: str, *, identical: bool) -> str:
    decl = (
        _IDENTICAL_DECL[name] if identical
        else f"private data {name} {{\n  B{name}(Int)\n}}"
    )
    return f"""{decl}

public fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @Int.0
}}
"""


def _entry(name: str, *, demands: bool) -> str:
    head = "import blib(probe);\n"
    tail = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(7)
}
"""
    if not demands:
        return head + tail
    slot, body = _ENTRY_USE[name]
    return head + f"""
public fn consume({slot} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}
""" + tail


def _acceptance_cell(
    tmp_path: Path, name: str, *, demands: bool, identical: bool = False,
) -> tuple[list[str], list[str]]:
    """(diagnostic codes, exports) for one battery cell."""
    gen = _compile(tmp_path, {
        "blib.vera": _blib(name, identical=identical),
        "main.vera": _entry(name, demands=demands),
    })
    result = gen._result  # type: ignore[attr-defined]
    return (
        sorted({d.error_code for d in result.diagnostics if d.error_code}),
        sorted(result.exports),
    )


@pytest.mark.parametrize("name", _PRELUDE_ADTS)
@pytest.mark.parametrize("demands", [False, True], ids=["alone", "demands"])
def test_every_cell_is_clean_or_one_e621(
    tmp_path: Path, name: str, demands: bool,
) -> None:
    """Every module-declares cell: clean-green, or a single E621. Never noise.

    The acceptance battery.  At the branch point every one of these
    sixteen cells was `vera check`-green and then either an E602/E620
    cascade located in `<prelude>` or — worse — a zero-exit compile with
    a user function silently missing from the exports.  Two properties
    are asserted, and neither hard-codes which names fall where, so the
    four-vs-four coverage split the rail started with cannot return
    silently:

    * no cell reports E602 or E620 — the wreckage diagnostics are gone,
      not merely joined by a better one;
    * a cell that reports E621 emits nothing, and a cell that does not
      emits every public function the entry declares.  That is the
      silent-drop check: a zero-exit compile missing a function fails
      here whichever name produced it.
    """
    codes, exports = _acceptance_cell(tmp_path, name, demands=demands)
    assert set(codes) <= {"E621"}, (
        f"{name} ({'demands' if demands else 'alone'}): expected at most "
        f"E621, got {codes}"
    )
    expected = ["consume", "main"] if demands else ["main"]
    if codes == ["E621"]:
        assert exports == [], f"{name}: refused, yet emitted {exports}"
    else:
        assert exports == expected, (
            f"{name}: zero-exit compile dropped "
            f"{sorted(set(expected) - set(exports))}"
        )


#: §8.4.1's two halves of the prelude's data types.  Every program compiles
#: the first four, so a differently-shaped module declaration of one of them
#: "always contends"; the other four are injected only when the entry program
#: uses them, so the module's declaration "stands alone until it does".
_ALWAYS_COMPILED = ("Option", "Result", "Ordering", "UrlParts")
_DEMAND_INJECTED = ("Json", "HtmlNode", "Request", "Response")


def test_the_two_halves_partition_the_prelude_adts() -> None:
    """Neither half may drift from `_PRELUDE_ADTS`.

    The cell below reads its expected answer off these lists, so a name
    added to the battery and to neither list — or to both — would be
    asserted against nothing, or against two answers.
    """
    assert set(_ALWAYS_COMPILED) | set(_DEMAND_INJECTED) == set(_PRELUDE_ADTS)
    assert not set(_ALWAYS_COMPILED) & set(_DEMAND_INJECTED)


@pytest.mark.parametrize("name", _PRELUDE_ADTS)
def test_the_alone_half_follows_the_injection_split(
    tmp_path: Path, name: str,
) -> None:
    """An entry that never names the type: §8.4.1 decides by which half.

    `test_every_cell_is_clean_or_one_e621` accepts either answer for these
    eight cells (`set(codes) <= {"E621"}`), deliberately, so that the rail's
    four-vs-four coverage split cannot return silently.  That looseness is
    about which names the rail COVERS; it leaves the alone half unpinned in
    the other direction, and a rail that stopped reporting a differing
    `Ordering` declaration in an entry that never mentions `Ordering` would
    keep the whole suite green.  §8.4.1 decides the question: measured
    E621-with-no-exports for the four every program compiles, and
    clean-with-`main`-exported for the four injected on demand.
    """
    codes, exports = _acceptance_cell(tmp_path, name, demands=False)
    if name in _ALWAYS_COMPILED:
        assert codes == ["E621"], (
            f"{name} is compiled into every program, so a differing module "
            f"declaration contends whether or not the entry names it; got "
            f"{codes}"
        )
        assert exports == [], f"{name}: refused, yet emitted {exports}"
    else:
        assert codes == [], (
            f"{name} is injected only on demand, so nothing contends when "
            f"the entry never names it; got {codes}"
        )
        assert exports == ["main"], exports


@pytest.mark.parametrize("name", _PRELUDE_ADTS)
def test_a_differing_module_declaration_contends_for_every_name(
    tmp_path: Path, name: str,
) -> None:
    """All EIGHT, not the four the layout map happens to record.

    `_register_modules` skips a built-in ADT name in the layout harvest
    (the throwaway registrar holds `Option`, `Result`, `Ordering` and
    `UrlParts` for every module, declared or not, so the layouts cannot
    tell a declaration from the built-in), which left
    `_adt_layout_owners` recording only `Json`, `HtmlNode`, `Request`
    and `Response`.  Keying the rail on it covered four of the eight
    names while §8.4.1 and §11.16 claim all of them.  The rail now reads
    the DECLARATIONS.
    """
    codes, exports = _acceptance_cell(tmp_path, name, demands=True)
    assert codes == ["E621"], f"{name}: {codes}"
    assert exports == []


@pytest.mark.parametrize("name", _PRELUDE_ADTS)
def test_restating_the_prelude_shape_is_not_a_contention(
    tmp_path: Path, name: str,
) -> None:
    """A module may restate the prelude's own type — measured legal, kept legal.

    One registered layout is correct for both declarations, so these
    programs compile and run at the branch point and must keep doing so.
    This is what stops the rail from becoming the reservation §8.4.1
    forbids, and it is a real regression guard rather than a hypothetical
    twice over: the rail's first form refused four of these, and the shape
    ships in the repository — `examples/vera/collections.vera` declares
    `public data Option<T> { None, Some(T) }`, which `examples/modules.vera`
    imports, so a rail without the structural test refuses a shipped
    example (measured: `vera compile` on `examples/modules.vera` returns
    E621, which `scripts/check_e602_clean.py` reports as a COMPILE_ERROR —
    `check_examples.py` runs only `check` and `verify` and stays green).
    """
    codes, exports = _acceptance_cell(
        tmp_path, name, demands=True, identical=True)
    assert codes == [], f"{name}: restating the prelude's shape reported {codes}"
    assert exports == ["consume", "main"], exports


# ---------------------------------------------------------------------
# TWO declaring modules — the rail must examine every one of them
# ---------------------------------------------------------------------

_ORD_RESTATE = "private data Ordering {\n  Less,\n  Equal,\n  Greater\n}"
_ORD_DIFFER = "private data Ordering {\n  Odd(Int)\n}"
_ORD_DIFFER2 = "private data Ordering {\n  Even(Int)\n}"
_WIDGET_A = "private data Widget {\n  WA(Int)\n}"
_WIDGET_B = "private data Widget {\n  WB(Int)\n}"

_DECL_BODY = {
    _ORD_RESTATE: "match Less {\n    Less -> @Int.0,\n    Equal -> 1,\n"
                  "    Greater -> 2\n  }",
    _ORD_DIFFER: "match Odd(@Int.0) {\n    Odd(@Int) -> @Int.0\n  }",
    _ORD_DIFFER2: "match Even(@Int.0) {\n    Even(@Int) -> @Int.0\n  }",
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
def test_a_second_module_declaration_is_examined_too(
    tmp_path: Path, a_first: bool,
) -> None:
    """The rail asks EVERY declaring module, not whichever declared first.

    `alib` restates the prelude's `Ordering` and `blib` declares a
    different one.  Keyed on a first-wins owner map the rail compared the
    prelude against `alib`'s identical shape, found no contention, and
    never looked at `blib` — so with `alib` imported first the program was
    `vera check`-green, compiled with exit 0 and only `[E602]`/`[E620]`
    warnings, and `main` was silently missing from the exports; with the
    imports the other way round the same pair was caught.  An
    order-dependent rail is not a rail.

    E609 cannot cover this either: the layout harvest exempts a built-in
    name before the provenance check, so two modules declaring `Ordering`
    never reach it.
    """
    codes, exports = _two_module_cell(
        tmp_path, _ORD_RESTATE, _ORD_DIFFER, a_first=a_first)
    assert codes == ["E621"], (
        f"{'alib' if a_first else 'blib'} first: expected the differing "
        f"declaration to be reported, got {codes} with exports {exports}"
    )
    assert exports == []


@pytest.mark.parametrize("a_first", [True, False], ids=["alib1st", "blib1st"])
def test_two_differing_module_declarations_are_both_reported(
    tmp_path: Path, a_first: bool,
) -> None:
    """Each differing declaration is its own problem, and gets its own report.

    Both parametrizations are genuinely different programs — the entry's
    import order follows *a_first* — because the rule under test is that
    the rail examines every declarer rather than whichever came first.
    The report ORDER is asserted against the import order too: it is the
    one observable that distinguishes the two ids, so without it a fixture
    that lost its order-sensitivity again would still pass both.
    """
    gen = _two_module_gen(
        tmp_path, _ORD_DIFFER, _ORD_DIFFER2,
        a_first=a_first, uses_ordering=False,
    )
    result = gen._result  # type: ignore[attr-defined]
    e621 = [d for d in result.diagnostics if d.error_code == "E621"]
    assert len(e621) == 2, [
        (d.error_code, d.location.file) for d in result.diagnostics]
    reported = [Path(d.location.file).name for d in e621]
    assert set(reported) == {"alib.vera", "blib.vera"}, reported
    expected = ["alib.vera", "blib.vera"] if a_first else [
        "blib.vera", "alib.vera"]
    assert reported == expected, (
        f"reported {reported}; the rail walks the declarers in resolution "
        f"order, which follows the entry's import order"
    )
    assert sorted(result.exports) == []


@pytest.mark.parametrize("a_first", [True, False], ids=["alib1st", "blib1st"])
def test_two_modules_both_restating_the_prelude_are_legal(
    tmp_path: Path, a_first: bool,
) -> None:
    """Two restatements share the one layout — green before and after."""
    codes, exports = _two_module_cell(
        tmp_path, _ORD_RESTATE, _ORD_RESTATE, a_first=a_first)
    assert codes == [], codes
    assert exports == ["consume", "main"], exports


@pytest.mark.parametrize("a_first", [True, False], ids=["alib1st", "blib1st"])
def test_two_modules_declaring_a_NON_prelude_name_are_admitted(
    tmp_path: Path, a_first: bool,
) -> None:
    """The control that keeps the two rails apart, and isolates R7.

    `Widget` is nobody's prelude type, so no prelude declaration is
    injected and nothing reaches the Pass-1.2 rail.  What is left is the
    module-versus-module pair, which is E609's — and since #1317 that rail
    admits two PRIVATE, differently-shaped declarations no namespace can
    reach, compiling each under `mod$<path>$Widget`.

    Read against `test_a_differing_module_declaration_contends_for_every_name`
    above, which is the SAME shape under a prelude name and still reports
    E621 with no exports, this cell is what shows the prelude reservation
    is doing the work there rather than the declarations' shapes.
    """
    codes, exports = _two_module_cell(
        tmp_path, _WIDGET_A, _WIDGET_B, a_first=a_first, uses_ordering=False)
    assert codes == [], codes
    assert exports == ["main"], exports


# A restatement of the prelude's `UrlParts` spelled through the module's own
# alias.  Structurally the prelude's type; syntactically nothing like it.
_ALIAS_RESTATE = """
type Payload = String;

private data UrlParts {
  UrlParts(Payload, Payload, Payload, Payload, Payload)
}

public fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match UrlParts("a", "b", "c", "d", "e") {
    UrlParts(@String, @String, @String, @String, @String) -> @Int.0
  }
}
"""

# The reverse: a module alias named after something the PRELUDE's own
# declaration spells, hiding a layout that does not fit behind identical
# syntax.  `Array<Json>` here is the module's `Int`.
_ALIAS_HIDDEN_MISMATCH = """
type Array<T> = Int;

private data Json {
  JNull,
  JBool(Bool),
  JNumber(Float64),
  JString(String),
  JArray(Array<Json>),
  JObject(Map<String, Json>)
}

public fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match JNull {
    JNull -> @Int.0,
    JBool(@Bool) -> 1,
    JNumber(@Float64) -> 2,
    JString(@String) -> 3,
    JArray(@Array<Json>) -> 4,
    JObject(@Map<String, Json>) -> 5
  }
}
"""

_MAIN_USES_URLPARTS = """import alib(probe);

public fn consume(@UrlParts -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @UrlParts.0 {
    UrlParts(@String, @String, @String, @String, @String) ->
      string_length(@String.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(7)
}
"""

_MAIN_USES_PRELUDE_JSON_VIA_ALIB = """import alib(probe);

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
  probe(7)
}
"""


def test_an_alias_spelled_restatement_is_still_a_restatement(
    tmp_path: Path,
) -> None:
    """A module may write the prelude's type through its own alias.

    `type Payload = String;` and a `UrlParts` whose five fields are
    `Payload` describes exactly the prelude's layout, so it shares the one
    slot and must compile — but the two declarations have nothing in
    common syntactically, and a shape key over raw spellings refused it
    (measured: E621 on a `vera check`-green program §8.4.1 permits).  The
    module's declaration is canonicalized through the MODULE's own alias
    maps, which §8.4.1 makes the only ones that may answer for it.
    """
    gen = _compile(tmp_path, {
        "alib.vera": _ALIAS_RESTATE,
        "main.vera": _MAIN_USES_URLPARTS,
    })
    result = gen._result  # type: ignore[attr-defined]
    codes = sorted({d.error_code for d in result.diagnostics if d.error_code})
    assert codes == [], codes
    assert sorted(result.exports) == ["consume", "main"], result.exports


def test_an_alias_cannot_hide_a_layout_that_does_not_fit(
    tmp_path: Path,
) -> None:
    """The other direction, and the reason only ONE side is resolved.

    `type Array<T> = Int;` makes the module's `JArray(Array<Json>)` an
    `Int` field while the prelude's is a real array.  The two spellings
    are identical, so a raw-syntax key called them the same layout and
    the program compiled with the module's `Json` in the slot and the
    entry's `json_array_length` reading it — no diagnostic at all
    (measured: `ok: true`, `exports == ['depth', 'main']`).  Resolving
    the module's side alone separates them; resolving the PRELUDE's side
    through the same maps would collapse them again, which is what makes
    this the control for that mutation.
    """
    gen = _compile(tmp_path, {
        "alib.vera": _ALIAS_HIDDEN_MISMATCH,
        "main.vera": _MAIN_USES_PRELUDE_JSON_VIA_ALIB,
    })
    result = gen._result  # type: ignore[attr-defined]
    codes = sorted({d.error_code for d in result.diagnostics if d.error_code})
    assert codes == ["E621"], codes
    assert result.exports == []


def test_the_shape_key_resolves_only_the_namespace_it_is_given() -> None:
    """`data_decl_shape`'s alias argument, at the unit level.

    Two direct properties, because the rail depends on both: an alias
    substitution makes a differently-spelled declaration key EQUAL to the
    prelude's, and a type PARAMETER of the same name as an alias shadows
    it (`_resolve_named`'s branch order) rather than being substituted.
    """
    from vera.parser import parse_to_ast
    from vera.prelude import data_decl_shape, prelude_data_decls

    prelude = prelude_data_decls()
    decl = parse_to_ast(
        "private data UrlParts {\n"
        "  UrlParts(Payload, Payload, Payload, Payload, Payload)\n}"
    ).declarations[0].decl
    aliases = {"Payload": parse_to_ast(
        "type Payload = String;").declarations[0].decl.type_expr}
    assert data_decl_shape(decl) != data_decl_shape(prelude["UrlParts"])
    assert data_decl_shape(decl, aliases, {}) == (
        data_decl_shape(prelude["UrlParts"]))

    # `T` is the declaration's own parameter, so an alias named `T` must
    # not reach it — the shape stays positional (`#0`), not `Int`.
    generic = parse_to_ast(
        "private data Option<T> { None, Some(T) }").declarations[0].decl
    shadow = {"T": parse_to_ast(
        "type T = Int;").declarations[0].decl.type_expr}
    assert data_decl_shape(generic, shadow, {}) == (
        data_decl_shape(prelude["Option"]))


def test_the_shape_key_ignores_parameter_names_and_not_tag_order() -> None:
    """`data_decl_shape` models the layout: positions, not spellings.

    Renaming a type parameter changes no layout, so `data Option<A> {
    None, Some(A) }` must key equal to the prelude's.  Reordering the
    constructors DOES change the layout — the tag is the position — so it
    must not, which is where this test is stronger than the
    `_has_standard_json` family's set comparison it sits beside.
    """
    from vera.parser import parse_to_ast
    from vera.prelude import data_decl_shape, prelude_data_decls

    def shape(src: str) -> object:
        decl = parse_to_ast(src).declarations[0].decl
        return data_decl_shape(decl)

    prelude = prelude_data_decls()
    assert shape("private data Option<A> { None, Some(A) }") == (
        data_decl_shape(prelude["Option"]))
    assert shape("private data Ordering { Less, Equal, Greater }") == (
        data_decl_shape(prelude["Ordering"]))
    assert shape("private data Ordering { Equal, Less, Greater }") != (
        data_decl_shape(prelude["Ordering"]))
    assert shape("private data Option<A> { None, Some(Int) }") != (
        data_decl_shape(prelude["Option"]))


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
