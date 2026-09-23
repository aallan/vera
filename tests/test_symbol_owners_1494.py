"""Every emitted function symbol has exactly one owner (#1494, #1495, #1498).

Code generation emits every function into ONE flat WebAssembly function
namespace.  Four kinds of owner put functions there: the entry file, each
imported module, the prelude, and the compiler's own runtime (the allocator
and collector, the structural helpers it derives per type, the lifted
closures).  When two owners use one name, either the module fails to assemble
(``duplicate func identifier``, #1494; E608 on spec-legal cross-module
shapes, #1498) or a call silently binds to the other owner's body (#1495,
and a transitive module's function captured by the entry's namesake).

The instrument is an OWNER-COLLISION MATRIX.  For every ordered pair of
owners it declares a same-named function on both sides, calls it from each
side, compiles, runs, and asserts each side's own result, one export per
side so a failure names the side that went wrong:

* **runtime** names are ENUMERATED from the code-generation modules — every
  WAT function the modules under ``vera/codegen`` and ``vera/wasm`` define,
  read from their string templates — and every enumerated name must be
  claimed by a trigger program that makes code generation emit it;
* **prelude** names are enumerated from the prelude source, and each must be
  claimed by a snippet that calls it; the prelude's own internal calls (a
  prelude body calling another prelude function by bare name) are read off
  the injected bodies;
* **module** pairs cross the four ways §11.16 says a declaration does not
  own the importing namespace's bare name — private, outside the import
  filter, shadowed by a local declaration, reached only transitively — with
  zero and one owner, generic and non-generic, in both import orders, and
  two modules' declarations of each prelude function's name meet in one
  namespace's imports;
* the #1498 shapes, the #1495 table and the #1494 table are cells of their
  own, named after the issue.

The PUBLIC interface keeps source names: the last cells compile programs
full of colliding names and assert that every public function is exported
under its source name and resolves exactly as before, under the wasmtime
runner, the browser runtime, and both wasi-p2 worlds.
"""

from __future__ import annotations

import ast as pyast
import dataclasses
import json
import re
import shutil
import subprocess
from collections.abc import Iterator
from functools import cache
from pathlib import Path

import pytest

import vera
from tests.codegen_helpers import wat_fn_names
from tests.module_fixture_helpers import (
    build_multi_module,
    build_multi_module_past_check,
    module_value,
)
from vera import ast
from vera.codegen import execute
from vera.codegen.api import CompileResult
from vera.parser import parse_to_ast
from vera.prelude import (
    inject_prelude,
    overridable_builtin_names,
    prelude_symbol,
)

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Source builders
# ---------------------------------------------------------------------------


def _fn(
    vis: str, name: str, body: str, sig: str = "@Int -> @Int",
    *, forall: str = "",
) -> str:
    """One function declaration with trivial contracts."""
    head = f"{vis} forall<{forall}> fn" if forall else f"{vis} fn"
    return (
        f"{head} {name}({sig})\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  {body}\n}}\n\n"
    )


def _probe(name: str, body: str) -> str:
    """A zero-argument public export the cell runs by name."""
    return _fn("public", name, body, sig="-> @Int")


def _run_cell(
    tmp_path: Path, files: dict[str, str], expected: dict[str, object],
) -> None:
    """Check, verify, compile and run *files*; assert every export's value.

    One compile, one run per export, so a cell asserts each SIDE of the pair
    separately.  Verify is asserted too: a clean verify beside a wrong value
    is the false-Tier-1 shape a collision produces when the two bodies share
    a WAT type.
    """
    verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
    assert not cg_errors, f"compile refused a check-clean program: {cg_errors}"
    assert result.wasm_bytes, "no module was produced"
    assert not verify_errors, f"verify errors: {verify_errors}"
    got = {fn: module_value(result, fn) for fn in expected}
    want = {fn: ("ok", value) for fn, value in expected.items()}
    assert got == want


# ---------------------------------------------------------------------------
# Enumeration: the runtime's function symbols, from the code-generation modules
# ---------------------------------------------------------------------------

_VERA_PKG = Path(vera.__file__).resolve().parent
_CODEGEN_DIRS = (_VERA_PKG / "codegen", _VERA_PKG / "wasm")
# The wasi-p2 emitter builds a SECOND core module (the adapter) whose
# functions live in that module's own namespace.  Only what it adds to the
# Vera core module shares the user's namespace, and those additions are
# exactly what it defines AND exports from that module (`$rt.cabi_realloc`,
# `$rt.wasi_run`, the `$rt.wasi_tbl` table and the `$rt.wasi_arena_ptr`
# global); an adapter item is never exported that way.
_WASI_EMITTER = _VERA_PKG / "codegen" / "wasi.py"

# A runtime symbol is spelled `$rt.<name>` (before #1494, `$<name>`).  The
# `rt.` namespace is outside every name a Vera declaration can produce: `.`
# is not an identifier character, and no mangling inserts one.
_RT = r"(?:rt\.)?"
# `(func $name` — a definition under a literal name.
_FIXED_DEF = re.compile(
    r"\(func \$(" + _RT + r"[A-Za-z_][A-Za-z0-9_]*)(?=[\s)]|$)",
)
# `$prefix{…}` — a whole template that BUILDS a family member's name.
_FAMILY_BUILDER = re.compile(r"^\$(" + _RT + r"[a-z][A-Za-z0-9_]*_)\{\}$")
# `${…}_{…}` — a builder whose PREFIX is computed, so not enumerable.
_DYNAMIC_BUILDER = re.compile(r"^\$" + _RT + r"\{\}")
# wasi-p2 additions to the core module: anything it defines AND exports
# from that module — `(func $name (export "…")`, and the table and global
# it adds the same way.  The adapter module never exports that way.  An item
# the core module already defines (the emitter rewrites `$heap_ptr` in
# place) is not an addition, and is subtracted.
_CORE_DEF = re.compile(
    r"\((?:func|table|global) \$(" + _RT + r"[A-Za-z_][A-Za-z0-9_]*)",
)
_WASI_MAIN_DEF = re.compile(
    r"\((?:func|table|global) \$(" + _RT + r"[A-Za-z_][A-Za-z0-9_]*) "
    r"\(export \"",
)

# Builders the scan finds that do NOT name a function.  Each lives in another
# WAT index space, so it can never collide with a function symbol.  A new
# `$prefix{…}` builder must be claimed by a runtime family (and a trigger
# below) or excused here with the space it belongs to.
NON_FUNCTION_BUILDERS: dict[str, str] = {
    "closure_sig_": "type index space: a closure's call_indirect signature",
    "exn_": "tag index space: an Exn<E> exception tag",
    "hd_": "label: a handler's done block",
    "hc_": "label: a handler's catch block",
    "qbreak_": "label: a quantifier loop's break block",
    "qloop_": "label: a quantifier loop",
}


def _code_templates(path: Path) -> Iterator[str]:
    """Every string template in *path*'s CODE, docstrings excluded.

    An f-string becomes its literal text with each interpolation replaced by
    ``{}``, so a builder reads as ``$anon_{}``.  Implicitly concatenated
    literals are one node already; ``+``-joined pieces are scanned apiece.
    """
    tree = pyast.parse(path.read_text(encoding="utf-8"))
    docstrings: set[int] = set()
    fstring_parts: set[int] = set()
    for node in pyast.walk(tree):
        if isinstance(
            node,
            (pyast.Module, pyast.ClassDef, pyast.FunctionDef,
             pyast.AsyncFunctionDef),
        ) and node.body:
            first = node.body[0]
            if (isinstance(first, pyast.Expr)
                    and isinstance(first.value, pyast.Constant)
                    and isinstance(first.value.value, str)):
                docstrings.add(id(first.value))
        if isinstance(node, pyast.JoinedStr):
            fstring_parts.update(id(v) for v in node.values)
    for node in pyast.walk(tree):
        if isinstance(node, pyast.JoinedStr):
            yield "".join(
                str(v.value) if isinstance(v, pyast.Constant) else "{}"
                for v in node.values
            )
        elif (isinstance(node, pyast.Constant)
                and isinstance(node.value, str)
                and id(node) not in docstrings
                and id(node) not in fstring_parts):
            yield node.value


@dataclasses.dataclass(frozen=True)
class RuntimeSymbols:
    """What the code-generation modules define, read from their templates."""

    fixed: frozenset[str]          # `rt.alloc` (or `alloc` before #1494)
    families: frozenset[str]       # `rt.anon_`, …
    wasi_main: frozenset[str]      # `rt.cabi_realloc`, …
    dynamic_builders: tuple[str, ...]


@cache
def runtime_symbols() -> RuntimeSymbols:
    fixed: set[str] = set()
    families: set[str] = set()
    wasi_main: set[str] = set()
    core_defs: set[str] = set()
    dynamic: list[str] = []
    for directory in _CODEGEN_DIRS:
        for path in sorted(directory.glob("*.py")):
            for tpl in _code_templates(path):
                if path == _WASI_EMITTER:
                    wasi_main.update(_WASI_MAIN_DEF.findall(tpl))
                    continue
                fixed.update(_FIXED_DEF.findall(tpl))
                core_defs.update(_CORE_DEF.findall(tpl))
                m = _FAMILY_BUILDER.match(tpl)
                if m:
                    families.add(m.group(1))
                if _DYNAMIC_BUILDER.match(tpl):
                    dynamic.append(f"{path.name}: {tpl!r}")
    functions = {
        fam for fam in families
        if fam.removeprefix("rt.") not in NON_FUNCTION_BUILDERS
    }
    return RuntimeSymbols(
        fixed=frozenset(fixed),
        families=frozenset(functions),
        wasi_main=frozenset(wasi_main - core_defs),
        dynamic_builders=tuple(dynamic),
    )


def _bare(sym: str) -> str:
    return sym.removeprefix("rt.")


def _vera_spellable(name: str) -> bool:
    return re.fullmatch(r"[a-z][A-Za-z0-9_]*", name) is not None


# ---------------------------------------------------------------------------
# Triggers: a program fragment that makes code generation emit each symbol
# ---------------------------------------------------------------------------

_LIST = "private data List { Nil, Cons(Int, List) }\n\n"
_LEN = (
    "private fn len(@List -> @Int)\n  requires(true)\n  ensures(true)\n"
    "  decreases(@List.0)\n  effects(pure)\n{\n  match @List.0 {\n"
    "    Nil -> 0,\n    Cons(@Int, @List) -> 1 + len(@List.0)\n  }\n}\n\n"
)
_HEAP = 'string_length(string_concat(int_to_string(12), "ab"))'
_MAP = 'map_size(map_insert(map_new(), "k", 1))'


@dataclasses.dataclass(frozen=True)
class Trigger:
    """How to make code generation emit one runtime symbol."""

    member: str          # the concrete symbol, without the `rt.` namespace
    decls: str           # declarations the trigger needs
    expr: str            # an Int expression whose evaluation uses the helper
    value: int           # what that expression returns
    env: tuple[tuple[str, str], ...] = ()  # compile-time flags it needs


# Keyed by the enumerated symbol — a fixed name, or a family prefix — with
# the `rt.` namespace stripped.  Every enumerated symbol must be claimed here
# (`test_every_runtime_symbol_is_claimed`), so a helper added to code
# generation without a cell turns this file red rather than going unmeasured.
TRIGGERS: dict[str, Trigger] = {
    "alloc": Trigger("alloc", "", _HEAP, 4),
    "gc_collect": Trigger("gc_collect", "", _HEAP, 4),
    "gc_set_base": Trigger("gc_set_base", "", _HEAP, 4),
    "gc_is_base": Trigger("gc_is_base", "", _HEAP, 4),
    "gc_assert_base": Trigger(
        "gc_assert_base", "", _HEAP, 4,
        env=(("VERA_GC_CHECK_MARKS", "1"),),
    ),
    "register_wrapper": Trigger("register_wrapper", "", _MAP, 1),
    "eq_String": Trigger(
        "eq_String", "",
        'match string_concat("a", "b") { "ab" -> 1, _ -> 0 }', 1,
    ),
    "cmp_String": Trigger(
        "cmp_String", "",
        'if string_concat("a", "b") < "b" then { 1 } else { 0 }', 1,
    ),
    "anon_": Trigger(
        "anon_0", "",
        "array_length(array_map([1, 2, 3], "
        "fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }))", 3,
    ),
    "eq_": Trigger(
        "eq_List", _LIST,
        "if eq(Cons(1, Nil), Cons(1, Nil)) then { 1 } else { 0 }", 1,
    ),
    "show_": Trigger(
        "show_List", _LIST, "string_length(show(Cons(1, Nil)))",
        len("Cons(1, Nil)"),
    ),
    "hash_": Trigger(
        "hash_List", _LIST,
        "if hash(Cons(1, Nil)) == hash(Cons(1, Nil)) then { 1 } else { 0 }", 1,
    ),
    "dec_size_": Trigger(
        "dec_size_List", _LIST + _LEN, "len(Cons(1, Cons(2, Nil)))", 2,
    ),
}

# wasi-p2 adds these to the core module; each needs a cell under that
# target (`test_wasi_user_fn_named_after_a_core_addition`).  A name a Vera
# identifier cannot spell (the pre-#1494 `__wasi_run`) needs none.
WASI_TRIGGERS = frozenset({
    "cabi_realloc", "wasi_run", "wasi_tbl", "wasi_arena_ptr",
})


class TestRuntimeEnumeration:
    """The enumeration is read from the code, and every symbol is claimed."""

    def test_enumeration_is_read_from_the_code(self) -> None:
        syms = runtime_symbols()
        # A scan that found nothing would make every cell below vacuous.
        assert {_bare(s) for s in syms.fixed} >= {"alloc", "gc_collect"}
        assert {_bare(s) for s in syms.families} >= {"anon_", "eq_"}
        assert {_bare(s) for s in syms.wasi_main} >= {"cabi_realloc"}

    def test_no_builder_computes_its_prefix(self) -> None:
        """A family whose prefix is computed cannot be enumerated."""
        assert runtime_symbols().dynamic_builders == ()

    def test_every_runtime_symbol_is_claimed(self) -> None:
        syms = runtime_symbols()
        enumerated = {_bare(s) for s in syms.fixed | syms.families}
        assert enumerated == set(TRIGGERS), (
            f"unclaimed: {sorted(enumerated - set(TRIGGERS))}; "
            f"claims for nothing: {sorted(set(TRIGGERS) - enumerated)}"
        )
        wasi = {
            _bare(s) for s in syms.wasi_main if _vera_spellable(_bare(s))
        }
        assert wasi == WASI_TRIGGERS

    def test_every_runtime_symbol_is_outside_the_user_namespace(self) -> None:
        """No runtime symbol can be spelled by a Vera declaration.

        The class fix, stated over the enumeration: a runtime function that
        a user function, a module function, a prelude function, a clone or a
        helper could also be called is a collision waiting for its program.
        """
        syms = runtime_symbols()
        spellable = sorted(
            s for s in syms.fixed | syms.families | syms.wasi_main
            if not s.startswith("rt.")
        )
        assert spellable == []

    @pytest.mark.parametrize("key", sorted(TRIGGERS))
    def test_trigger_emits_its_symbol(
        self, key: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Each trigger really makes code generation emit the symbol.

        Without this a trigger could drift away from its helper, and every
        cell built on it would pass without the runtime ever defining the
        name it claims to collide with.
        """
        trig = TRIGGERS[key]
        for var, value in trig.env:
            monkeypatch.setenv(var, value)
        files = {"main.vera": trig.decls + _probe("main", trig.expr)}
        _, result, cg_errors = build_multi_module(tmp_path, files)
        assert not cg_errors
        names = set(wat_fn_names(result.wat))
        assert names & {trig.member, f"rt.{trig.member}"}, sorted(names)
        assert module_value(result, "main") == ("ok", trig.value)


# ---------------------------------------------------------------------------
# (entry, runtime) and (module, runtime)
# ---------------------------------------------------------------------------

_USER_TAG = 40


@pytest.mark.parametrize("key", sorted(TRIGGERS))
@pytest.mark.parametrize("owner,vis", [
    ("entry", "private"), ("module", "private"), ("module", "public"),
])
def test_user_fn_named_after_runtime_symbol(
    key: str, owner: str, vis: str,
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """#1494: a user function and a runtime helper of one name coexist.

    The runtime side is the trigger's own value; the user side is the user
    function's.  A public entry function of a runtime export's name is the
    export-namespace question, asserted separately below.
    """
    trig = TRIGGERS[key]
    for var, value in trig.env:
        monkeypatch.setenv(var, value)
    user = _fn(vis, trig.member, f"@Int.0 + {_USER_TAG}")
    runtime_side = _probe("side_runtime", trig.expr)
    if owner == "entry":
        files = {
            "main.vera": trig.decls + user
            + _probe("side_user", f"{trig.member}(1)") + runtime_side,
        }
    else:
        files = {
            "liba.vera": "module liba;\n\n" + user
            + _fn("public", "pa", f"{trig.member}(@Int.0)"),
            "main.vera": "import liba(pa);\n\n" + trig.decls
            + _probe("side_user", "pa(1)") + runtime_side,
        }
    _run_cell(tmp_path, files, {
        "side_user": 1 + _USER_TAG, "side_runtime": trig.value,
    })


# The runtime's host-facing EXPORT names, read from the templates.  An export
# is a PUBLIC surface: a `public fn` of one of these names would contend for
# the export itself, not for an internal symbol, so the runtime's own exports
# live in the `vera.` namespace (#1494) and every user export keeps its
# source name.  The user-function emitter interpolates the declaration's
# name (`(export "{}")`) and is not a runtime export.
_EXPORT_NAME = re.compile(r'\(export "([^"{}]+)"')


@cache
def runtime_export_names() -> frozenset[str]:
    out: set[str] = set()
    for directory in _CODEGEN_DIRS:
        for path in sorted(directory.glob("*.py")):
            if path == _WASI_EMITTER:
                continue
            for tpl in _code_templates(path):
                out.update(_EXPORT_NAME.findall(tpl))
    return frozenset(out)


# How to make the runtime emit each export: an Int expression and its value.
# Keyed by the export's name with the `vera.` namespace stripped, which is
# what a user function of that name is called.
EXPORT_TRIGGERS: dict[str, tuple[str, int]] = {
    "memory": (_HEAP, 4),
    "alloc": (_HEAP, 4),
    "heap_ptr": (_HEAP, 4),
    "gc_sp": (_HEAP, 4),
    "gc_stack_limit": (_HEAP, 4),
    "register_wrapper": (_MAP, 1),
}


def test_every_runtime_export_is_claimed() -> None:
    names = runtime_export_names()
    assert {n.removeprefix("vera.") for n in names} == set(EXPORT_TRIGGERS)


def test_every_runtime_export_is_outside_the_user_namespace() -> None:
    """No runtime export can be spelled by a Vera identifier (spec §12.2.1,
    the `vera.` export namespace): a user `public fn` of any name is exported
    under its source name and cannot displace the runtime's host interface."""
    assert sorted(n for n in runtime_export_names() if _vera_spellable(n)) == []


@pytest.mark.parametrize("name", sorted(EXPORT_TRIGGERS))
def test_public_fn_named_after_runtime_export(
    name: str, tmp_path: Path,
) -> None:
    """A `public fn` named after a host-ABI export, in a program that makes
    the runtime emit that export: the user's export keeps its source name
    and the runtime keeps working."""
    expr, value = EXPORT_TRIGGERS[name]
    main = (
        _fn("public", name, f"@Int.0 + {_USER_TAG}")
        + _probe("side_runtime", expr)
    )
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"main.vera": main},
    )
    assert not cg_errors, cg_errors
    assert not verify_errors, verify_errors
    assert name in result.exports
    assert module_value(result, "side_runtime") == ("ok", value)
    assert execute(result, fn_name=name, args=[1]).value == 1 + _USER_TAG


# ---------------------------------------------------------------------------
# The prelude: names, signatures and internal calls, from the prelude source
# ---------------------------------------------------------------------------

PRELUDE_FNS: frozenset[str] = overridable_builtin_names()


@cache
def _injected_prelude_fns() -> dict[str, ast.FnDecl]:
    """Every prelude function, as `inject_prelude` lays it down.

    The anchor mentions every demand-driven prelude family (Json, HtmlNode),
    so every block is injected.
    """
    program = parse_to_ast(
        "private fn anchor(@Json, @HtmlNode -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n  0\n}\n"
    )
    inject_prelude(program)
    return {
        tld.decl.name: tld.decl
        for tld in program.declarations
        if isinstance(tld.decl, ast.FnDecl) and tld.decl.name in PRELUDE_FNS
    }


@cache
def prelude_internal_callers() -> dict[str, frozenset[str]]:
    """Prelude function -> the prelude functions whose bodies call it."""
    callers: dict[str, set[str]] = {}

    def walk(node: object, owner: str) -> None:
        if isinstance(node, ast.FnCall) and node.name in PRELUDE_FNS:
            if node.name != owner:
                callers.setdefault(node.name, set()).add(owner)
        if dataclasses.is_dataclass(node):
            for f in dataclasses.fields(node):
                val = getattr(node, f.name)
                items = val if isinstance(val, (list, tuple)) else (val,)
                for item in items:
                    if dataclasses.is_dataclass(item):
                        walk(item, owner)

    for name, decl in _injected_prelude_fns().items():
        walk(decl.body, name)
    return {k: frozenset(v) for k, v in callers.items()}


def _type_src(te: ast.TypeExpr) -> str:
    return ast.format_type_expr(te).replace("@", "")


_DOC = (
    '{\\"a\\": \\"bc\\", \\"n\\": 2.5, \\"i\\": 7, \\"b\\": true, '
    '\\"xs\\": [1, 2, 3]}'
)


def _with_doc(expr: str) -> str:
    return (
        f'match json_parse("{_DOC}") {{ Ok(@Json) -> {expr}, '
        "Err(@String) -> 0 - 1 }"
    )


def _field(key: str, inner: str) -> str:
    return (
        f'match json_get(@Json.0, "{key}") {{ Some(@Json) -> {inner}, '
        "None -> 0 - 2 }"
    )


# Each prelude function, called with arguments that make it return a known
# Int.  Keyed by the enumerated name; `test_every_prelude_fn_is_claimed`
# holds the key set to the enumeration.
PRELUDE_SNIPPETS: dict[str, tuple[str, int]] = {
    "option_unwrap_or": ("option_unwrap_or(Some(5), 0)", 5),
    "option_map": (
        "option_unwrap_or(option_map(Some(5), "
        "fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }), 0)", 6,
    ),
    "option_and_then": (
        "option_unwrap_or(option_and_then(Some(5), "
        "fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0 + 2) }), 0)", 7,
    ),
    "result_unwrap_or": ('result_unwrap_or(parse_int("8"), 0)', 8),
    # Bound through a `let`: a module body that nests `result_map` straight
    # inside `result_unwrap_or` is dropped at compile whatever this change
    # does — discovery binds `E` to the phantom default there, and the call
    # site names another clone.  A separate defect, reported with this one.
    "result_map": (
        'let @Result<Int, String> = result_map(parse_int("8"), '
        "fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }); "
        "result_unwrap_or(@Result<Int, String>.0, 0)", 9,
    ),
    "json_get": (_with_doc(_field("i", "1")), 1),
    "json_array_get": (_with_doc(_field(
        "xs",
        "match json_array_get(@Json.0, 2) { Some(@Json) -> 1, None -> 0 }",
    )), 1),
    "json_array_length": (
        _with_doc(_field("xs", "json_array_length(@Json.0)")), 3,
    ),
    "json_keys": (_with_doc("array_length(json_keys(@Json.0))"), 5),
    "json_has_field": (
        _with_doc('if json_has_field(@Json.0, "b") then { 1 } else { 0 }'), 1,
    ),
    "json_type": (_with_doc("string_length(json_type(@Json.0))"), 6),
    "json_as_string": (_with_doc(_field(
        "a", "match json_as_string(@Json.0) { Some(@String) -> "
        "string_length(@String.0), None -> 0 }",
    )), 2),
    "json_as_number": (_with_doc(_field(
        "n", "match json_as_number(@Json.0) { Some(@Float64) -> "
        "if @Float64.0 == 2.5 then { 1 } else { 0 }, None -> 0 }",
    )), 1),
    "json_as_bool": (_with_doc(_field(
        "b", "match json_as_bool(@Json.0) { Some(@Bool) -> "
        "if @Bool.0 then { 1 } else { 0 }, None -> 0 }",
    )), 1),
    "json_as_int": (_with_doc(_field(
        "i", "match json_as_int(@Json.0) { Some(@Int) -> @Int.0, None -> 0 }",
    )), 7),
    "json_as_array": (_with_doc(_field(
        "xs", "match json_as_array(@Json.0) { Some(@Array<Json>) -> "
        "array_length(@Array<Json>.0), None -> 0 }",
    )), 3),
    "json_as_object": (_with_doc(
        "match json_as_object(@Json.0) { Some(@Map<String, Json>) -> "
        "map_size(@Map<String, Json>.0), None -> 0 }",
    ), 5),
    "json_get_string": (_with_doc(
        'match json_get_string(@Json.0, "a") { Some(@String) -> '
        "string_length(@String.0), None -> 0 }",
    ), 2),
    "json_get_number": (_with_doc(
        'match json_get_number(@Json.0, "n") { Some(@Float64) -> '
        "if @Float64.0 == 2.5 then { 1 } else { 0 }, None -> 0 }",
    ), 1),
    "json_get_int": (_with_doc(
        'match json_get_int(@Json.0, "i") { Some(@Int) -> @Int.0, '
        "None -> 0 }",
    ), 7),
    "json_get_bool": (_with_doc(
        'match json_get_bool(@Json.0, "b") { Some(@Bool) -> '
        "if @Bool.0 then { 1 } else { 0 }, None -> 0 }",
    ), 1),
    "json_get_array": (_with_doc(
        'match json_get_array(@Json.0, "xs") { Some(@Array<Json>) -> '
        "array_length(@Array<Json>.0), None -> 0 }",
    ), 3),
    "html_attr": (
        'match html_parse("<a href=\\"xyz\\">t</a>") { Ok(@HtmlNode) -> '
        'match html_attr(@HtmlNode.0, "href") { Some(@String) -> '
        "string_length(@String.0), None -> 0 }, Err(@String) -> 0 - 1 }", 3,
    ),
}

# A body of each non-generic prelude function's own return type that the
# prelude's body never returns for its snippet's input.
_SAME_SIG_BODY: dict[str, str] = {
    "Int": "0 - 5",
    "Bool": "false",
    "String": '"z"',
    "Array<String>": "[]",
}
# What a snippet evaluates to when its function is that replacement body:
# `None` makes every Option-returning snippet take its `0` arm, except the
# field lookup, whose own `None` arm is `0 - 2`.
_SAME_SIG_VALUE: dict[str, int] = {
    "json_get": -2, "json_array_length": -5, "json_type": 1,
}


def _same_sig_decl(name: str) -> tuple[str, int]:
    """Redeclare a non-generic prelude function with its own signature."""
    decl = _injected_prelude_fns()[name]
    ret = _type_src(decl.return_type)
    body = "None" if ret.startswith("Option<") else _SAME_SIG_BODY[ret]
    sig = ", ".join(f"@{_type_src(p)}" for p in decl.params)
    return (
        _fn("private", name, body, sig=f"{sig} -> @{ret}"),
        _SAME_SIG_VALUE.get(name, 0),
    )


class TestPreludeEnumeration:
    def test_every_prelude_fn_is_claimed(self) -> None:
        assert set(PRELUDE_SNIPPETS) == set(PRELUDE_FNS)
        assert set(_injected_prelude_fns()) == set(PRELUDE_FNS)

    def test_internal_calls_are_found(self) -> None:
        """The #1495 edges exist: five callers over six callees."""
        callers = prelude_internal_callers()
        assert callers.get("json_get") == frozenset({
            "json_get_string", "json_get_number", "json_get_int",
            "json_get_bool", "json_get_array",
        })
        assert callers.get("json_as_string") == frozenset({"json_get_string"})
        assert sum(len(v) for v in callers.values()) == 10


class TestPreludeIdentity:
    """The injection keeps an overridden prelude function under its own
    identity, and the prelude's bodies call it there (#1495)."""

    @staticmethod
    def _injected(decl: str) -> dict[str, ast.FnDecl]:
        program = parse_to_ast(decl + _probe("main", _JSON_CONTROL))
        inject_prelude(program)
        return {
            tld.decl.name: tld.decl for tld in program.declarations
            if isinstance(tld.decl, ast.FnDecl)
        }

    def test_an_overridden_function_keeps_its_own_symbol(self) -> None:
        fns = self._injected(_fn("private", "json_get", "@Int.0"))
        assert prelude_symbol("json_get") in fns
        # The program's own declaration keeps the bare name.
        assert fns["json_get"].params == (
            ast.NamedType(name="Int", type_args=None),
        )

    def test_the_prelude_bodies_call_the_prelude_function(self) -> None:
        fns = self._injected(_fn("private", "json_get", "@Int.0"))
        names: set[str] = set()

        def walk(node: object) -> None:
            if isinstance(node, ast.FnCall):
                names.add(node.name)
            if dataclasses.is_dataclass(node):
                for f in dataclasses.fields(node):
                    val = getattr(node, f.name)
                    items = val if isinstance(val, (list, tuple)) else (val,)
                    for item in items:
                        if dataclasses.is_dataclass(item):
                            walk(item)

        walk(fns["json_get_string"].body)
        assert prelude_symbol("json_get") in names
        assert "json_get" not in names

    def test_the_prelude_symbol_is_the_module_qualified_spelling(self) -> None:
        """One spelling: codegen's module-qualified name over the prelude's
        namespace token is exactly `prelude_symbol`."""
        from vera.codegen.modules import CrossModuleMixin
        from vera.prelude import PRELUDE_NAMESPACE

        assert CrossModuleMixin._module_qualified_wasm_name(
            PRELUDE_NAMESPACE, "json_get",
        ) == prelude_symbol("json_get")


def _prelude_side(name: str) -> tuple[dict[str, str], str, str, dict[str, object]]:
    """Files, imports, exports and values that exercise the PRELUDE's `name`.

    Two routes, both from namespaces that resolve `name` to the prelude:
    every prelude function whose body calls it, called from the entry; and a
    module that does not declare `name`, calling it by bare name.
    """
    decls = ""
    expected: dict[str, object] = {}
    for caller in sorted(prelude_internal_callers().get(name, ())):
        snippet, value = PRELUDE_SNIPPETS[caller]
        decls += _probe(f"side_prelude_{caller}", snippet)
        expected[f"side_prelude_{caller}"] = value
    snippet, value = PRELUDE_SNIPPETS[name]
    files = {"libp.vera": "module libp;\n\n" + _probe("pp", snippet)}
    decls += _probe("side_prelude_via_module", "pp()")
    expected["side_prelude_via_module"] = value
    return files, "import libp(pp);\n\n", decls, expected


def _entry_prelude_variants() -> Iterator[object]:
    generic = {n for n, d in _injected_prelude_fns().items() if d.forall_vars}
    for name in sorted(PRELUDE_FNS):
        yield pytest.param(name, "int_sig", id=f"{name}-int_sig")
        variant = "generic" if name in generic else "prelude_sig"
        yield pytest.param(name, variant, id=f"{name}-{variant}")


@pytest.mark.parametrize("name,variant", list(_entry_prelude_variants()))
def test_entry_fn_named_after_prelude_fn(
    name: str, variant: str, tmp_path: Path,
) -> None:
    """#1495: an entry function shadowing a prelude function.

    The entry's bare calls reach the entry's function (the #815 override
    stays legal); the prelude's own bodies, and a module whose namespace
    resolves the name to the prelude, still reach the prelude's.  Three
    shapes of override: a different signature; the prelude's own signature
    with a different body; and, for a generic prelude function, a generic of
    the same arity, whose clones share the prelude clones' name space.
    """
    if variant == "int_sig":
        decl = _fn("private", name, f"@Int.0 + {_USER_TAG}")
        own = _probe("side_user", f"{name}(1)")
        expected: dict[str, object] = {"side_user": 1 + _USER_TAG}
    elif variant == "generic":
        decl = _fn(
            "private", name, str(_USER_TAG), sig="@A, @B -> @Int",
            forall="A, B",
        )
        own = _probe("side_user", f"{name}(1, 2)")
        expected = {"side_user": _USER_TAG}
    else:
        decl, own_value = _same_sig_decl(name)
        own = _probe("side_user", PRELUDE_SNIPPETS[name][0])
        expected = {"side_user": own_value}
    files, imports, prelude_decls, prelude_expected = _prelude_side(name)
    files["main.vera"] = imports + decl + own + prelude_decls
    _run_cell(tmp_path, files, {**expected, **prelude_expected})


@pytest.mark.parametrize("name", sorted(PRELUDE_FNS))
@pytest.mark.parametrize("vis", ["private", "public"])
def test_module_fn_named_after_prelude_fn(
    name: str, vis: str, tmp_path: Path,
) -> None:
    """A module declares a prelude name.  The module's bare calls reach its
    own; the entry (whose bare name the prelude holds, §8.5.2.2) and the
    prelude's own bodies reach the prelude's."""
    lib = "module liba;\n\n" + _fn(vis, name, "@Int.0 + 100") + _fn(
        "public", "pa", f"{name}(@Int.0)",
    )
    snippet, value = PRELUDE_SNIPPETS[name]
    files, imports, prelude_decls, prelude_expected = _prelude_side(name)
    files["liba.vera"] = lib
    files["main.vera"] = (
        "import liba;\n" + imports + _probe("side_module", "pa(1)")
        + _probe("side_prelude", snippet) + prelude_decls
    )
    _run_cell(tmp_path, files, {
        "side_module": 101, "side_prelude": value, **prelude_expected,
    })


@pytest.mark.parametrize("name", sorted(PRELUDE_FNS))
@pytest.mark.parametrize("route", ["entry", "hub"])
@pytest.mark.parametrize("vis", ["private", "public"])
def test_two_modules_declare_a_prelude_name(
    name: str, route: str, vis: str, tmp_path: Path,
) -> None:
    """Two modules each declare a prelude function's name, and one
    namespace imports both.

    The prelude holds the bare name in every namespace (§8.5.2.2), so
    neither declaration owns it and no namespace's bare call can mean
    either: each module's call reaches its own declaration, and the
    importer's bare call reaches the prelude's.  The checker accepts the
    shape, and code generation's E608 rail agrees with it only because it
    removes the prelude-held names from its ambiguity set.  ``route`` is
    where the two imports meet: in the entry, or in a module the entry
    imports.
    """
    files = {
        f"lib{key}.vera": (
            f"module lib{key};\n\n" + _fn(vis, name, f"@Int.0 + {tag}")
            + _fn("public", f"p{key}", f"{name}(@Int.0)")
        )
        for key, tag in (("a", 100), ("b", 200))
    }
    snippet, value = PRELUDE_SNIPPETS[name]
    expected: dict[str, object] = {
        "side_a": 101, "side_b": 201, "side_prelude": value,
    }
    probes = (
        _probe("side_prelude", snippet)
        + _probe("side_a", "pa(1)") + _probe("side_b", "pb(1)")
    )
    if route == "entry":
        imports = "import liba;\nimport libb;\n\n"
    else:
        files["hub.vera"] = (
            "module hub;\n\nimport liba;\nimport libb;\n\n"
            + _probe("hh", snippet)
        )
        imports = "import hub(hh);\nimport liba(pa);\nimport libb(pb);\n\n"
        # The entry calls the prelude function as well, as every cell of
        # `_prelude_side` does: a prelude data type that only a module uses
        # is not injected at all, a separate defect this cell must not
        # depend on.  The two imports still meet only in `hub`.
        probes += _probe("side_hub", "hh()")
        expected["side_hub"] = value
    files["main.vera"] = imports + probes
    _run_cell(tmp_path, files, expected)


# ---------------------------------------------------------------------------
# Module pairs: the four non-ownership reasons of §11.16
# ---------------------------------------------------------------------------

_STATUSES = ("owner", "private", "filtered", "transitive")
_TAGS = {"a": 100, "b": 200}


def _f_decl(vis: str, tag: int, generic: bool) -> str:
    if generic:
        return _fn(vis, "f", f"@Int.0 + {tag}", sig="@T, @Int -> @Int",
                   forall="T")
    return _fn(vis, "f", f"@Int.0 + {tag}")


def _f_call(generic: bool, arg: str) -> str:
    return f"f(true, {arg})" if generic else f"f({arg})"


def _pair_files(
    status: dict[str, str], generic: dict[str, bool], order: tuple[str, ...],
    *, entry_local: bool,
) -> tuple[dict[str, str], dict[str, object]]:
    """Two modules each declaring `f`, in the given ownership statuses.

    Each module's `f` returns ``arg + tag``; each side's export reaches `f`
    through a bare call in the namespace that owns it, so each export's value
    names the body that ran.
    """
    files: dict[str, str] = {}
    imports: list[str] = []
    expected: dict[str, object] = {}
    probes = ""
    for key in order:
        st, gen, tag = status[key], generic[key], _TAGS[key]
        vis = "private" if st == "private" else "public"
        files[f"lib{key}.vera"] = (
            f"module lib{key};\n\n" + _f_decl(vis, tag, gen)
            + _fn("public", f"p{key}", _f_call(gen, "@Int.0"))
        )
        if st == "transitive":
            # The hub's own bare `f` is lib<key>'s (a public import): the
            # call a same-named entry declaration must not capture.
            files[f"hub{key}.vera"] = (
                f"module hub{key};\n\nimport lib{key};\n\n"
                + _fn("public", f"h{key}", _f_call(gen, "@Int.0"))
            )
            imports.append(f"import hub{key}(h{key});")
            probes += _probe(f"side_{key}", f"h{key}(1)")
        elif st == "owner":
            imports.append(f"import lib{key}(p{key}, f);")
            probes += _probe(f"side_{key}", f"p{key}(1)")
            if not entry_local:
                probes += _probe("side_entry_bare", _f_call(gen, "1"))
                expected["side_entry_bare"] = 1 + tag
        else:
            # Each status isolates its own reason.  A PRIVATE `f` is imported
            # by a wildcard, so its visibility alone keeps it out of the
            # entry's namespace; a FILTERED one is public and left out of a
            # selective import.  A selective import for both would let the
            # filter answer for visibility, and ownership that ignored
            # visibility would pass every private cell.
            imports.append(
                f"import lib{key};" if st == "private"
                else f"import lib{key}(p{key});"
            )
            probes += _probe(f"side_{key}", f"p{key}(1)")
        expected[f"side_{key}"] = 1 + tag
    main = "\n".join(imports) + "\n\n"
    if entry_local:
        main += _fn("private", "f", "@Int.0 + 7")
        probes += _probe("side_entry", "f(1)")
        expected["side_entry"] = 8
    files["main.vera"] = main + probes
    return files, expected


def _pair_cases() -> Iterator[object]:
    for sa in _STATUSES:
        for sb in _STATUSES:
            for gen in ("nn", "gg", "gn"):
                for order in (("a", "b"), ("b", "a")):
                    for local in (False, True):
                        if sa == sb == "owner" and not local:
                            continue  # two owners: E155, the cell below
                        yield pytest.param(
                            sa, sb, gen, order, local,
                            id=f"{sa}-{sb}-{gen}-{''.join(order)}"
                               f"{'-local' if local else ''}",
                        )


@pytest.mark.parametrize("sa,sb,gen,order,local", list(_pair_cases()))
def test_module_pair(
    sa: str, sb: str, gen: str, order: tuple[str, ...], local: bool,
    tmp_path: Path,
) -> None:
    """#1498: two modules' `f` in every ownership combination.

    With ``local`` the entry declares `f` too, so an "owner" status becomes
    a shadowed one (§8.5.2) and every module's `f` is qualified-only.
    """
    files, expected = _pair_files(
        {"a": sa, "b": sb},
        {"a": gen[0] == "g", "b": gen[1] == "g"},
        order, entry_local=local,
    )
    _run_cell(tmp_path, files, expected)


def test_two_owners_stays_refused(tmp_path: Path) -> None:
    """E608 remains exactly for the ambiguity §8.5.2.2 refuses (E155)."""
    files, _ = _pair_files(
        {"a": "owner", "b": "owner"}, {"a": False, "b": False},
        ("a", "b"), entry_local=False,
    )
    check_errors, _, cg_errors = build_multi_module_past_check(
        tmp_path, files,
    )
    assert [c for c, _ in check_errors] == ["E155"]
    assert [c for c, _ in cg_errors] == ["E608"]


# ---------------------------------------------------------------------------
# The issues' own shapes
# ---------------------------------------------------------------------------


def test_1498_selective_import_other_module_uses_its_own(
    tmp_path: Path,
) -> None:
    files = {
        "liba.vera": _fn("public", "f", "@Int.0 + 100"),
        "libb.vera": _fn("public", "f", "@Int.0 + 200")
        + _fn("public", "g", "f(@Int.0)"),
        "main.vera": "import liba(f);\nimport libb(g);\n\n"
        + _probe("main", "f(1) * 1000 + g(1)"),
    }
    _run_cell(tmp_path, files, {"main": 101201})


def test_1498_module_shadows_its_import(tmp_path: Path) -> None:
    files = {
        "deep.vera": _fn("public", "f", "@Int.0 + 100"),
        "mid.vera": "import deep;\n\n"
        + _fn("public", "f", "deep::f(@Int.0) + 10"),
        "main.vera": "import mid;\n\n" + _probe("main", "f(1)"),
    }
    _run_cell(tmp_path, files, {"main": 111})


def test_1498_two_private_helpers(tmp_path: Path) -> None:
    files = {
        "liba.vera": _fn("private", "h", "@Int.0 + 100")
        + _fn("public", "x", "h(@Int.0)"),
        "libb.vera": _fn("private", "h", "@Int.0 + 200")
        + _fn("public", "y", "h(@Int.0)"),
        "main.vera": "import liba(x);\nimport libb(y);\n\n"
        + _probe("main", "x(1) * 1000 + y(1)"),
    }
    _run_cell(tmp_path, files, {"main": 101201})


def test_transitive_call_is_not_captured_by_the_entry(tmp_path: Path) -> None:
    """`mid` calls `deep`'s `h`; the entry declares its own `h`."""
    files = {
        "deep.vera": _fn("public", "h", "@Int.0 + 100"),
        "mid.vera": "import deep;\n\n" + _fn("public", "m", "h(@Int.0)"),
        "main.vera": "import mid;\n\n" + _fn("private", "h", "@Int.0 + 7")
        + _probe("main", "h(1) * 1000 + m(1)"),
    }
    _run_cell(tmp_path, files, {"main": 8101})


def test_a_repeated_import_admits_the_union_of_its_lists(
    tmp_path: Path,
) -> None:
    """`import liba(f, gen); import liba(g);` admits all three, as the checker
    reads it.  The code generator took the LAST list alone, so the generic
    `gen` read as qualified-only and the entry's bare call to it had no
    target: check and verify clean, then `not defined` at compile."""
    lib = (
        "module liba;\n\n" + _fn("public", "f", "@Int.0 + 100")
        + _fn("public", "g", "@Int.0 + 200")
        + _fn("public", "gen", "@Int.0 + 300", sig="@T, @Int -> @Int",
              forall="T")
    )
    main = (
        "import liba(f, gen);\nimport liba(g);\n\n"
        + _probe("main", "f(1) * 1000000 + g(1) * 1000 + gen(true, 1)")
    )
    _run_cell(
        tmp_path, {"liba.vera": lib, "main.vera": main}, {"main": 101201301},
    )


_WHERE = (
    "{vis} fn x(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
    "  effects(pure)\n{{\n  h(@Int.0)\n}}\nwhere {{\n"
    "  fn h(@Int -> @Int)\n    requires(true)\n    ensures(true)\n"
    "    effects(pure)\n  {{\n    @Int.0 + {tag}\n  }}\n}}\n\n"
)


@pytest.mark.parametrize("entry_x", [False, True], ids=["modules", "entry"])
def test_where_helpers_under_same_named_parents(
    entry_x: bool, tmp_path: Path,
) -> None:
    """Two modules' private `x`, each with a helper `h` (and the entry's).

    A hoisted helper's symbol is derived from its parent's, so two parents
    of one name put two helpers of one name in the namespace unless the
    helper follows its parent's owner.
    """
    main = "import liba(ax);\nimport libb(bx);\n\n"
    expr, value = "ax(1) * 1000 + bx(1)", 101201
    if entry_x:
        main += _WHERE.format(vis="private", tag=7)
        expr, value = "x(1) * 1000000 + " + expr, 8000000 + value
    files = {
        "liba.vera": _WHERE.format(vis="private", tag=100)
        + _fn("public", "ax", "x(@Int.0)"),
        "libb.vera": _WHERE.format(vis="private", tag=200)
        + _fn("public", "bx", "x(@Int.0)"),
        "main.vera": main + _probe("main", expr),
    }
    _run_cell(tmp_path, files, {"main": value})


@pytest.mark.parametrize("parent", ["owner", "private"])
def test_a_where_helper_takes_its_parents_symbol(
    parent: str, tmp_path: Path,
) -> None:
    """A hoisted helper's symbol is its parent's, extended (spec §8.9.1).

    ``liba``'s ``x`` either owns the entry's bare name (public, imported by
    name) or does not (private, reached through ``ax``), and its helper
    ``h`` is emitted as ``<x's symbol>$where$h`` either way: ``x$where$h``
    beside a bare ``x``, ``mod$liba$x$where$h`` beside ``mod$liba$x``.
    Behaviour cannot tell the two spellings apart, because the parent's body
    reaches its helper through its module's own renames whichever it is, so
    the symbols are asserted directly.
    """
    vis, imports = (
        ("public", "import liba(ax, x);\n\n") if parent == "owner"
        else ("private", "import liba(ax);\n\n")
    )
    files = {
        "liba.vera": _WHERE.format(vis=vis, tag=100)
        + _fn("public", "ax", "x(@Int.0)"),
        "main.vera": imports + _probe("main", "ax(1)"),
    }
    verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
    assert not cg_errors and not verify_errors, (cg_errors, verify_errors)
    parent_symbol = "x" if parent == "owner" else "mod$liba$x"
    names = wat_fn_names(result.wat)
    assert parent_symbol in names, names
    assert f"{parent_symbol}$where$h" in names, names
    assert module_value(result, "main") == ("ok", 101)


_JSON_CONTROL = (
    'match json_parse("{\\"a\\": \\"bc\\"}") {\n'
    '    Ok(@Json) -> match json_get_string(@Json.0, "a") {\n'
    "      Some(@String) -> string_length(@String.0),\n"
    "      None -> 0\n    },\n    Err(@String) -> 0 - 1\n  }"
)


@pytest.mark.parametrize("decl", [
    "",
    _fn("private", "json_get", "@Int.0"),
    _fn("private", "json_as_string", "@Int.0"),
    _fn("private", "json_get", "None", sig="@Json, @String -> @Option<Json>"),
], ids=["control", "json_get-int", "json_as_string-int", "json_get-same-sig"])
def test_1495_table(decl: str, tmp_path: Path) -> None:
    _run_cell(
        tmp_path, {"main.vera": decl + _probe("main", _JSON_CONTROL)},
        {"main": 2},
    )


@pytest.mark.parametrize("name", ["alloc", "gc_collect", "anon_0"])
def test_1494_table(name: str, tmp_path: Path) -> None:
    """The issue's repro, run as `vera run --fn main -- 3`: a `public fn`
    named after a runtime helper beside a program that makes the runtime
    emit it (the heap for `alloc`/`gc_collect`, a closure for `anon_0`)."""
    closure = TRIGGERS["anon_"].expr if name == "anon_0" else "0"
    main = _fn("public", name, "@Int.0 + 1") + (
        "public fn main(@Int -> @String)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  string_concat(int_to_string("
        f"{name}(@Int.0) + {closure}), \"!\")\n}}\n"
    )
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"main.vera": main},
    )
    assert not cg_errors, cg_errors
    run = execute(result, fn_name="main", raw_args=["3"])
    assert run.value == f"{4 + (3 if name == 'anon_0' else 0)}!"


# ---------------------------------------------------------------------------
# The public interface: source names on every target
# ---------------------------------------------------------------------------

# A program dense with owner collisions: user functions named after runtime
# helpers and a prelude function, beside the code that makes the runtime and
# the prelude emit theirs.
_INTERFACE = (
    _LIST
    + _fn("private", "alloc", "@Int.0 + 1")
    + _fn("private", "show_List", "@Int.0 + 2")
    + _fn("private", "anon_0", "@Int.0 + 3")
    + _fn("private", "json_get", "@Int.0 + 4")
    + _fn("public", "twice", "@Int.0 * 2")
    + "public fn main(-> @Int)\n  requires(true)\n  ensures(true)\n"
    "  effects(pure)\n{\n  alloc(0) + show_List(0) + anon_0(0) + json_get(0)"
    " + string_length(show(Cons(1, Nil)))"
    " + array_length(array_map([1, 2], fn(@Int -> @Int) effects(pure)"
    " { @Int.0 }))\n}\n"
)
_INTERFACE_MAIN = 1 + 2 + 3 + 4 + len("Cons(1, Nil)") + 2


def _interface_result(tmp_path: Path) -> CompileResult:
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"main.vera": _INTERFACE},
    )
    assert not cg_errors, cg_errors
    return result


def test_interface_exports_keep_source_names(tmp_path: Path) -> None:
    result = _interface_result(tmp_path)
    assert result.exports == ["twice", "main"]
    assert module_value(result, "main") == ("ok", _INTERFACE_MAIN)
    assert execute(result, fn_name="twice", args=[21]).value == 42


_NODE = shutil.which("node")
_HARNESS = ROOT / "vera" / "browser" / "harness.mjs"


def _node_supports_exnref() -> bool:
    """The same probe `tests/test_browser.py` gates its module on."""
    if _NODE is None:
        return False
    try:
        proc = subprocess.run(
            [_NODE, "--experimental-wasm-exnref", "-e", "0"],
            capture_output=True, timeout=5, check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return False
    return proc.returncode == 0


@pytest.mark.skipif(
    not _node_supports_exnref(),
    reason="Node.js not available or lacks --experimental-wasm-exnref support",
)
def test_interface_browser(tmp_path: Path) -> None:
    result = _interface_result(tmp_path)
    wasm = tmp_path / "m.wasm"
    wasm.write_bytes(result.wasm_bytes)
    outs = {}
    for fn, args in (("main", []), ("twice", ["21"])):
        proc = subprocess.run(
            [_NODE or "node", "--experimental-wasm-exnref", str(_HARNESS),
             str(wasm), "--fn", fn, "--", *args],
            capture_output=True, text=True, encoding="utf-8", timeout=60,
            check=False,
        )
        assert proc.returncode == 0, proc.stderr
        outs[fn] = json.loads(proc.stdout)
    assert int(outs["main"]["value"]) == _INTERFACE_MAIN
    assert int(outs["twice"]["value"]) == 42
    assert set(outs["main"]["exports"]) >= {"main", "twice"}


def _run_wasi_cli(result: CompileResult) -> object:
    import wasmtime
    from wasmtime.component import Component, Linker

    from vera.codegen.wasi import emit_wasi_component

    engine = wasmtime.Engine()
    linker = Linker(engine)
    linker.add_wasip2()
    store = wasmtime.Store(engine)
    store.set_wasi(wasmtime.WasiConfig())
    instance = linker.instantiate(
        store, Component(engine, emit_wasi_component(result)),
    )
    func = instance.get_func(store, "main")
    assert func is not None
    value = func(store)
    func.post_return(store)
    return value


def test_interface_wasi_cli(tmp_path: Path) -> None:
    """The cli world supports IO and Random only, so the Json-using prelude
    collision is left out; every runtime collision stays in."""
    src = _INTERFACE.replace(" + json_get(0)", "").replace(
        _fn("private", "json_get", "@Int.0 + 4"), "",
    )
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"main.vera": src},
    )
    assert not cg_errors, cg_errors
    assert result.exports == ["twice", "main"]
    assert _run_wasi_cli(result) == _INTERFACE_MAIN - 4


@pytest.mark.parametrize("name", sorted(WASI_TRIGGERS))
@pytest.mark.parametrize("vis", ["private", "public"])
def test_wasi_user_fn_named_after_a_core_addition(
    name: str, vis: str, tmp_path: Path,
) -> None:
    """A user function named after what wasi-p2 adds to the core module
    (its realloc, entry wrapper, dispatch table and arena pointer), under
    the target that adds it.  Before #1494 the emitter refused every such
    program with a raw `ValueError`, including the table and global names,
    whose index spaces a function never shares."""
    src = _fn(vis, name, "@Int.0 + 40") + (
        "public fn main(-> @Int)\n  requires(true)\n  ensures(true)\n"
        f"  effects(pure)\n{{\n  {name}(1) + {_HEAP}\n}}\n"
    )
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"main.vera": src},
    )
    assert not cg_errors
    assert module_value(result, "main") == ("ok", 45)
    assert _run_wasi_cli(result) == 45


_HANDLER = (
    _fn("private", "alloc", "@Int.0 + 1")
    + _fn("private", "cabi_realloc", "@Int.0 + 2")
    + "public fn handle(@Request -> @Response)\n  requires(true)\n"
    "  ensures(true)\n  effects(<HttpServer>)\n{\n"
    "  Response(200, map_new(), int_to_string(alloc(1) + cabi_realloc(1)))\n}\n"
)


def test_interface_wasi_server(tmp_path: Path) -> None:
    import wasmtime
    from wasmtime.component import Component

    from vera.codegen.api import HttpRequestData
    from vera.codegen.wasi import emit_wasi_component

    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"main.vera": _HANDLER},
    )
    assert not cg_errors, cg_errors
    assert result.exports == ["handle"]
    Component(wasmtime.Engine(), emit_wasi_component(result, world="server"))
    er = execute(
        result, fn_name="handle",
        http_request=HttpRequestData(
            method="GET", path="/", headers={}, body="",
        ),
    )
    assert er.http_response is not None
    assert er.http_response["body"] == "5"
