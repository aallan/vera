"""Every runtime trap names its cause (#1479).

A trap reaches its reader as a ``trap_kind``, a message and a Fix paragraph,
on three hosts: wasmtime (``vera run``), the browser runtime
(``vera/browser/runtime.mjs``) and the WASI 0.2 host (``--target wasi-p2``).
Every check code generation emits either signals its own kind first —
``vera.trap`` with a kind code, or ``vera.contract_fail`` for a contract — or
traps natively with an instruction whose own trap message names it, or is an
internal trap on the roster the generic ``unreachable`` Fix paragraph is
derived from.  :mod:`vera.trap_registry` states all of that once; these cells
hold it to the backend and to the hosts.

* **The static scan** enumerates the code-generation package (the module
  enumeration :mod:`tests.guard_emitter_scan` derives, so there is one) and
  finds every ``unreachable`` and every natively trapping instruction the
  WAT text holds.  Each must sit at a registered site — a signal's own
  implementation, a roster entry with its cause, a registered native trap,
  or a native instruction that cannot trap there — and every call to the
  emission path must name its own registry row.  A new bare trap is a
  failure here until it is named or rostered.
* **The roster and the paragraph** — the generic paragraph names exactly the
  causes the roster's entries give, and the browser runtime carries the same
  kind table byte for byte.
* **The runtime matrix** — each named kind, on each host, from a violating
  program: the kind, the message, and the Fix.
* **The fan-in cells** — a module whose only such check sits in a closure, a
  ``where`` helper, or a postcondition still instantiates on every host,
  because the flag that declares the signal's import is merged at that seam.
* **Heap exhaustion** runs in a subprocess under a wasmtime store memory
  limit, so no cell can exhaust the machine running the suite.
"""
from __future__ import annotations

import ast as pyast
import gc
import inspect
import json
import os
import re
import subprocess
import sys
import threading
import time
import weakref
from collections import Counter
from pathlib import Path

import pytest

from tests.guard_emitter_scan import codegen_sources
from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen.api import CompileResult, execute
from vera.parser import parse_to_ast
from vera.runtime.traps import WasmTrapError
from vera.trap_registry import (
    INTERNAL_TRAPS,
    KNOWN_TRAP_DEFECTS,
    NATIVE_TRAP_OPCODES,
    NATIVE_TRAP_SITES,
    NATIVE_TRAPPING_INSTRUCTIONS,
    SAFE_NATIVE_SITES,
    SIGNAL_SITES,
    THROW_SITES,
    TRAP_EMITTERS,
    WRAP_TABLE_VALUES,
    TRAP_KINDS,
    UNREACHABLE_CAUSES,
    NativeTrapCondition,
    browser_trap_table,
    native_trap_conditions,
    unreachable_fix_paragraph,
)

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# The static scan
# ---------------------------------------------------------------------------

_UNREACHABLE = re.compile(r"(?<![\w$.])unreachable(?![\w])")
#: A WAT ``throw``: the instruction with its tag, or an f-string's constant
#: part ending where the tag is substituted — never the effect operation's
#: bare name, which the lowering compares ``call.name`` against.  ``throw_ref``
#: counts too, with or without an operand.
_THROW = re.compile(r"(?<![\w$.])(throw(?= +(?:\$|$))|throw_ref(?![\w]))")
_NATIVE = re.compile(
    r"(?<![\w$.])(" + "|".join(
        re.escape(i) for i in sorted(NATIVE_TRAPPING_INSTRUCTIONS)) + r")(?![\w.])")

#: The calls through which a check is emitted or recorded; each names its
#: key or kind as its first argument.
_EMISSION_CALLS = ("_emit_trap", "_record_check", "signal_instructions")


def _rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT / "vera").as_posix()


def _docstring_ids(tree: pyast.AST) -> set[int]:
    ids: set[int] = set()
    for node in pyast.walk(tree):
        if isinstance(node, (pyast.Module, pyast.ClassDef, pyast.FunctionDef,
                             pyast.AsyncFunctionDef)):
            body = node.body
            if (body and isinstance(body[0], pyast.Expr)
                    and isinstance(body[0].value, pyast.Constant)
                    and isinstance(body[0].value.value, str)):
                ids.add(id(body[0].value))
    return ids


def _owner_map(tree: pyast.AST) -> dict[int, str]:
    """``id(node) -> owner`` for every node: the innermost function it sits
    in, or — at module or class level — the name the enclosing assignment
    binds (a WAT template or an operator table)."""
    owner: dict[int, str] = {}

    def visit(node: pyast.AST, current: str) -> None:
        for child in pyast.iter_child_nodes(node):
            here = current
            if isinstance(child, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
                here = child.name
            elif (isinstance(child, (pyast.Assign, pyast.AnnAssign))
                    and current in ("<module>", "<class>")):
                targets = (child.targets if isinstance(child, pyast.Assign)
                           else [child.target])
                names = [t.id for t in targets if isinstance(t, pyast.Name)]
                here = names[0] if names else current
            elif isinstance(child, pyast.ClassDef):
                here = "<class>"
            owner[id(child)] = here
            visit(child, here)

    visit(tree, "<module>")
    return owner


def literal_sites_for_tree(
    tree: pyast.AST, rel: str,
) -> Counter[tuple[str, str]]:
    """``(site, token) -> count`` for every trap the module's WAT text holds.

    Reads string constants, not source lines: a WAT template, a list of
    instructions and an f-string are all constants in the tree, and a
    docstring or a Python comment that merely MENTIONS ``unreachable`` is
    not.  WAT's own ``;;`` comments are stripped line by line first, so a
    template explaining its trap does not count as one.
    """
    docstrings = _docstring_ids(tree)
    owner = _owner_map(tree)
    found: Counter[tuple[str, str]] = Counter()
    for node in pyast.walk(tree):
        if not (isinstance(node, pyast.Constant)
                and isinstance(node.value, str)) or id(node) in docstrings:
            continue
        site = f"{rel}:{owner.get(id(node), '<module>')}"
        for line in node.value.split("\n"):
            code = line.split(";;")[0]
            for _ in _UNREACHABLE.finditer(code):
                found[(site, "unreachable")] += 1
            for match in _NATIVE.finditer(code):
                found[(site, match.group(1))] += 1
            for match in _THROW.finditer(code):
                found[(site, match.group(1))] += 1
    return found


def literal_sites() -> Counter[tuple[str, str]]:
    found: Counter[tuple[str, str]] = Counter()
    for path in codegen_sources():
        tree = pyast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        found.update(literal_sites_for_tree(tree, _rel(path)))
    return found


def emission_calls_for_tree(
    tree: pyast.AST, rel: str,
) -> list[tuple[str, str, str | None]]:
    """``(call, site, first argument if a string literal)`` for every call to
    the emission path in one module."""
    owner = _owner_map(tree)
    out: list[tuple[str, str, str | None]] = []
    for node in pyast.walk(tree):
        if not isinstance(node, pyast.Call):
            continue
        func = node.func
        name = (func.attr if isinstance(func, pyast.Attribute)
                else func.id if isinstance(func, pyast.Name) else None)
        if name not in _EMISSION_CALLS:
            continue
        arg = node.args[0] if node.args else None
        literal = (arg.value if isinstance(arg, pyast.Constant)
                   and isinstance(arg.value, str) else None)
        out.append((name, f"{rel}:{owner.get(id(node), '<module>')}", literal))
    return out


def emission_calls() -> list[tuple[str, str, str | None]]:
    out: list[tuple[str, str, str | None]] = []
    for path in codegen_sources():
        tree = pyast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        out.extend(emission_calls_for_tree(tree, _rel(path)))
    return out


def _expected_sites() -> Counter[tuple[str, str]]:
    expected: Counter[tuple[str, str]] = Counter()
    for entry in INTERNAL_TRAPS:
        expected[(entry.site, "unreachable")] += entry.count
    for site, count in SIGNAL_SITES:
        expected[(site, "unreachable")] += count
    for native in (*NATIVE_TRAP_SITES, *SAFE_NATIVE_SITES, *KNOWN_TRAP_DEFECTS,
                   *THROW_SITES):
        expected[(native.site, native.instruction)] += native.count
    return expected


def _diff(actual: Counter[tuple[str, str]],
          expected: Counter[tuple[str, str]]) -> str:
    extra = actual - expected
    missing = expected - actual
    return (
        "trap sites the code emits but the registry does not account for "
        f"(name each through the emission path or roster it): {dict(extra)}; "
        f"registry entries the code no longer holds: {dict(missing)}"
    )


def test_every_trap_the_codegen_emits_is_accounted_for() -> None:
    """Every `unreachable` and every natively trapping instruction in the
    code-generation package sits at a registered site, and every registered
    site still holds exactly what the registry says."""
    actual = literal_sites()
    expected = _expected_sites()
    assert actual == expected, _diff(actual, expected)


def test_the_enumeration_contains_the_emitters() -> None:
    """The scan reads the modules the emitters live in — a fact about today,
    asserted to lie inside the enumeration rather than being it."""
    modules = {_rel(p) for p in codegen_sources()}
    registered = {key.split(":")[0] for key in TRAP_EMITTERS}
    registered |= {e.site.split(":")[0] for e in INTERNAL_TRAPS}
    assert registered <= modules, registered - modules


#: The emission path itself, whose own calls pass the caller's key through.
_THE_PATH = "wasm/context.py:_emit_trap"


def test_every_emission_names_its_own_row() -> None:
    """A call to the emission path names the registry row of the function it
    sits in — so an emitter cannot raise a kind its row does not state, and a
    row cannot be satisfied by a call made somewhere else."""
    problems: list[str] = []
    for call, site, literal in emission_calls():
        if site == _THE_PATH:
            continue
        if call == "signal_instructions":
            row = TRAP_EMITTERS.get(site)
            if row is None or row.per_site or literal != row.kind:
                problems.append(f"{site}: renders {literal!r} directly")
            continue
        if literal is None:
            problems.append(f"{site}: {call} with a non-literal key")
            continue
        row = TRAP_EMITTERS.get(literal)
        if row is None:
            problems.append(f"{site}: {literal!r} is not a registry row")
        elif literal != site:
            problems.append(f"{site}: {call}({literal!r}) names another row")
        elif call == "_emit_trap" and row.via not in ("signal", "contract"):
            problems.append(f"{site}: a {row.via} row emits a signal")
        elif call == "_record_check" and not row.via.startswith("native:"):
            problems.append(f"{site}: a signalling row records by hand")
    assert not problems, problems


def test_every_registry_row_is_emitted() -> None:
    """Every row names a function that emits — no row outlives its emitter."""
    calls = emission_calls()
    keyed = {literal for call, _site, literal in calls
             if call in ("_emit_trap", "_record_check")}
    rendered = {site for call, site, _ in calls
                if call == "signal_instructions"}
    missing = [
        key for key, row in TRAP_EMITTERS.items()
        if (key not in keyed if row.per_site else key not in rendered)
    ]
    assert not missing, missing


def test_the_scan_sees_a_planted_bare_trap() -> None:
    """The seam the scan reads through reports a bare `unreachable`, a
    natively trapping instruction, a WAT `throw` and an unregistered
    emission — and not a WAT comment, a docstring that merely mentions one,
    or the effect operation's bare name."""
    tree = pyast.parse(
        'def emit():\n'
        '    """Traps with ``unreachable`` when the index is bad."""\n'
        '    return ["i32.eqz", "if", "  unreachable", "end",\n'
        '            "i64.div_s ;; trap on zero", ";; unreachable here"]\n'
        'def other(self):\n'
        '    return self._emit_trap("wasm/x.py:elsewhere", at=None)\n'
        'def raise_it(call, tag):\n'
        '    if call.name == "throw":\n'
        '        return [f"throw {tag}", "throw $exn_Int", "a throw payload"]\n'
    )
    sites = literal_sites_for_tree(tree, "wasm/x.py")
    assert sites == Counter({("wasm/x.py:emit", "unreachable"): 1,
                             ("wasm/x.py:emit", "i64.div_s"): 1,
                             ("wasm/x.py:raise_it", "throw"): 2}), sites
    calls = emission_calls_for_tree(tree, "wasm/x.py")
    assert calls == [("_emit_trap", "wasm/x.py:other", "wasm/x.py:elsewhere")]


# ---------------------------------------------------------------------------
# The roster, the paragraph, and the browser's copy
# ---------------------------------------------------------------------------

def test_the_generic_paragraph_names_exactly_the_rosters_causes() -> None:
    """The causes the roster's entries give are the causes the paragraph
    names — no cause without a site, no site without a cause — and the
    paragraph a host prints IS the derivation, not a hand-kept copy."""
    used = {entry.cause for entry in INTERNAL_TRAPS}
    named = [cause.key for cause in UNREACHABLE_CAUSES]
    assert len(named) == len(set(named))
    assert used == set(named), (used ^ set(named))
    paragraph = TRAP_KINDS["unreachable"].fix
    assert paragraph == unreachable_fix_paragraph()
    for number, cause in enumerate(UNREACHABLE_CAUSES, start=1):
        assert paragraph.count(cause.text) == 1, cause.key
        assert f"({number}) {cause.text}" in paragraph


#: An English count word, and the number it names — independent of the
#: registry's own table, so a derivation that picks the wrong word is seen.
_COUNT = {"One": 1, "Two": 2, "Three": 3, "Four": 4, "Five": 5, "Six": 6,
          "Seven": 7, "Eight": 8, "Nine": 9}


def test_the_generic_paragraph_counts_its_causes_right() -> None:
    """The paragraph opens with how many causes reach the trap, and that word
    is the number of causes it goes on to list."""
    paragraph = unreachable_fix_paragraph()
    word = paragraph.split(" ", 1)[0]
    listed = re.findall(r"\((\d+)\) ", paragraph)
    assert _COUNT.get(word) == len(UNREACHABLE_CAUSES) == len(listed), (
        word, len(UNREACHABLE_CAUSES), listed)
    assert listed == [str(n) for n in range(1, len(listed) + 1)]


def test_the_cause_texts_state_the_limits_the_code_sets() -> None:
    """Each capacity a cause names is the one `vera/codegen/assembly.py`
    sets: 4-byte shadow-stack roots and worklist entries, 16-byte wrapper
    table entries."""
    from vera.codegen.assembly import (
        GC_STACK_SIZE, GC_WORKLIST_SIZE, GC_WRAPTABLE_ENTRY_SIZE,
        GC_WRAPTABLE_SIZE,
    )
    texts = {cause.key: cause.text for cause in UNREACHABLE_CAUSES}

    def spelled(n: int) -> str:
        return f"{n:,}".replace(",", " ")

    assert spelled(GC_STACK_SIZE // 4) in texts["shadow_stack_overflow"]
    assert f"{GC_STACK_SIZE // 1024} KiB" in texts["shadow_stack_overflow"]
    assert spelled(GC_WORKLIST_SIZE // 4) in texts["gc_worklist_overflow"]
    assert spelled(GC_WRAPTABLE_SIZE // GC_WRAPTABLE_ENTRY_SIZE) in texts[
        "wrap_table_overflow"]


def test_the_runtime_chapter_states_the_regions_the_code_sets() -> None:
    """Spec §12.5.1's layout — its text version, its prose and its diagram —
    gives each GC region the size `vera/codegen/assembly.py` sets, and the
    heap the start those sizes add up to."""
    from vera.codegen.assembly import (
        GC_STACK_SIZE, GC_WORKLIST_SIZE, GC_WRAPTABLE_ENTRY_SIZE,
        GC_WRAPTABLE_SIZE,
    )
    chapter = (ROOT / "spec" / "12-runtime.md").read_text(encoding="utf-8")
    start = chapter.index("### 12.5.1 Linear Memory Layout")
    section = chapter[start:chapter.index("### 12.5.2", start)]
    diagram = (ROOT / "assets" / "diagrams" / "memory-layout.svg").read_text(
        encoding="utf-8")
    heap = GC_STACK_SIZE + GC_WORKLIST_SIZE
    for text in (f"GC shadow stack ({GC_STACK_SIZE} bytes)",
                 f"GC mark worklist ({GC_WORKLIST_SIZE} bytes)",
                 f"GC wrapper table ({GC_WRAPTABLE_SIZE} bytes)",
                 f"data_end + {GC_STACK_SIZE}\n", f"data_end + {heap}\n",
                 f"data_end + {heap + GC_WRAPTABLE_SIZE}\n",
                 f"{GC_STACK_SIZE} bytes, {GC_STACK_SIZE // 4} roots",
                 f"{GC_WORKLIST_SIZE} bytes, {GC_WORKLIST_SIZE // 4} entries",
                 f"{GC_WRAPTABLE_SIZE} bytes, "
                 f"{GC_WRAPTABLE_SIZE // GC_WRAPTABLE_ENTRY_SIZE} entries of "
                 f"{GC_WRAPTABLE_ENTRY_SIZE} bytes",
                 f"`data_end + {heap}`, or `data_end + "
                 f"{heap + GC_WRAPTABLE_SIZE}` with the wrapper table"):
        assert text in section, text

    def spelled(n: int) -> str:
        return f"{n:,}".replace(",", " ")

    for text in (f"{spelled(GC_STACK_SIZE)} bytes · "
                 f"{spelled(GC_STACK_SIZE // 4)} roots",
                 f"{spelled(GC_WORKLIST_SIZE)} bytes · "
                 f"{spelled(GC_WORKLIST_SIZE // 4)} entries",
                 f"{spelled(GC_WRAPTABLE_SIZE)} bytes · only with",
                 f"data_end + {spelled(GC_STACK_SIZE)}<",
                 f"data_end + {spelled(heap)}<",
                 f"data_end + {spelled(heap + GC_WRAPTABLE_SIZE)} = "):
        assert text in diagram, text


def _wrap_kinds_registered() -> set[str]:
    """Every wrap kind a registration with the collector's wrapper table is
    made with: the first argument of code generation's `_emit_wrap_handle`,
    and the second of the host's `_wrap_handle`."""
    positions = {"_emit_wrap_handle": 0, "_wrap_handle": 1}
    kinds: set[str] = set()
    for package in ("wasm", "codegen", "runtime"):
        for path in sorted((ROOT / "vera" / package).rglob("*.py")):
            tree = pyast.parse(path.read_text(encoding="utf-8"))
            for node in pyast.walk(tree):
                if not isinstance(node, pyast.Call):
                    continue
                func = node.func
                name = (func.attr if isinstance(func, pyast.Attribute)
                        else func.id if isinstance(func, pyast.Name) else None)
                position = positions.get(name or "")
                if position is None or len(node.args) <= position:
                    continue
                arg = node.args[position]
                kinds.add(arg.id if isinstance(arg, pyast.Name)
                          else pyast.dump(arg))
    return kinds


def test_the_wrapper_table_cause_names_what_the_table_holds() -> None:
    """The cause names the values that enter the wrapper table, derived from
    the kinds every registration passes — and no other: a `Map` or `Set` is
    a plain heap object and cannot fill it."""
    assert _wrap_kinds_registered() == set(WRAP_TABLE_VALUES)
    text = next(cause.text for cause in UNREACHABLE_CAUSES
                if cause.key == "wrap_table_overflow")
    for value in WRAP_TABLE_VALUES.values():
        assert value in text, value
    for absent in ("`Map`", "`Set`", "JSON", "HTML", "container"):
        assert absent not in text, absent


def test_every_wrapper_registration_goes_through_the_two_wrappers() -> None:
    """The table is reached only through the two functions the kinds above
    are read from: the WAT `call $register_wrapper` sits in
    `_emit_wrap_handle`, and the host's `_call_register_wrapper` is called
    only from `_wrap_handle`."""
    wat_sites: set[str] = set()
    for path in codegen_sources():
        tree = pyast.parse(path.read_text(encoding="utf-8"))
        owner = _owner_map(tree)
        for node in pyast.walk(tree):
            if (isinstance(node, pyast.Constant) and isinstance(node.value, str)
                    and "call $register_wrapper" in node.value):
                wat_sites.add(f"{_rel(path)}:{owner.get(id(node), '<module>')}")
    assert wat_sites == {"wasm/calls_containers.py:_emit_wrap_handle"}, wat_sites
    heap = ROOT / "vera" / "runtime" / "heap.py"
    tree = pyast.parse(heap.read_text(encoding="utf-8"))
    owner = _owner_map(tree)
    callers = {owner.get(id(node), "<module>") for node in pyast.walk(tree)
               if isinstance(node, pyast.Call)
               and isinstance(node.func, pyast.Name)
               and node.func.id == "_call_register_wrapper"}
    assert callers == {"_wrap_handle"}, callers


#: A non-tail recursion holding heap values: every frame roots its four
#: `String`s, so the shadow stack's bound is reached long before any
#: engine's own call stack is — V8's included — the commonest way to the
#: generic kind.
_SHADOW_STACK_DEEP = (
    "private fn deep(@Nat, @String, @String, @String, @String -> @String)\n"
    "  requires(true) ensures(true) decreases(@Nat.0) effects(pure)\n"
    "{\n  if @Nat.0 == 0 then { @String.0 } else {\n"
    "    string_concat(deep(@Nat.0 - 1, @String.3, @String.2, @String.1,"
    " @String.0), @String.3)\n  }\n}\n"
    "public fn main(-> @Nat)\n"
    "  requires(true) ensures(true) effects(pure)\n"
    '{\n  string_length(deep(20000, "a", "b", "c", "d"))\n}\n')


@pytest.mark.parametrize("host", ["wasmtime", "wasi", "browser"])
def test_every_host_prints_the_derived_generic_paragraph(
    host: str, tmp_path: Path,
) -> None:
    """A trap that reaches the generic kind carries, on every host, exactly
    the paragraph the registry derives — not a copy of it."""
    result = _compile(_SHADOW_STACK_DEEP)
    if host == "wasmtime":
        with pytest.raises(WasmTrapError) as info:
            execute(result, fn_name="main")
        kind, fix = info.value.kind, info.value.fix
    elif host == "wasi":
        from vera.runtime.wasi_host import execute_wasi_p2
        with pytest.raises(WasmTrapError) as info:
            execute_wasi_p2(result)
        kind, fix = info.value.kind, info.value.fix
    else:
        if _NODE is None:
            pytest.skip("Node.js not available or lacks exnref support")
        wasm = tmp_path / "deep.wasm"
        wasm.write_bytes(result.wasm_bytes)
        out = _NODE(wasm, fn="main")
        kind, fix = out["trapKind"], out["fix"]
    assert kind == "unreachable", kind
    assert fix == unreachable_fix_paragraph()


def test_no_check_on_a_program_value_reaches_the_generic_kind() -> None:
    """No registry emitter's kind is the generic one, and no roster entry
    sits in an emitter of a per-site check: a check on a value the program
    computed always reports its own kind, and the generic paragraph's causes
    are only the runtime's own.  (A runtime function may hold both: the
    WASI arena names its exhaustion when the component has the signal, and
    is unreachable by construction when it does not.)"""
    assert all(row.kind != "unreachable" for row in TRAP_EMITTERS.values())
    roster_sites = {entry.site for entry in INTERNAL_TRAPS}
    shared = {site for site in roster_sites & set(TRAP_EMITTERS)
              if TRAP_EMITTERS[site].per_site}
    assert not shared, shared


_TABLE_BLOCK = re.compile(
    r"// BEGIN GENERATED TRAP TABLE.*?\nconst TRAP_TABLE = (\{.*?\});\n"
    r"// END GENERATED TRAP TABLE", re.S)


def test_the_browser_runtime_carries_the_same_kind_table() -> None:
    """runtime.mjs names every trap from the registry's own table, so the
    three hosts cannot give one kind two descriptions or two remedies."""
    text = (ROOT / "vera" / "browser" / "runtime.mjs").read_text(
        encoding="utf-8")
    match = _TABLE_BLOCK.search(text)
    assert match is not None, "runtime.mjs lost its generated trap table"
    expected = json.dumps(browser_trap_table(), indent=2, ensure_ascii=True)
    assert match.group(1) == expected, (
        "runtime.mjs's TRAP_TABLE is stale; replace the block's JSON with:\n"
        + expected)


def test_every_signalled_kind_has_a_wasi_trap_function() -> None:
    """The WASI adapter traps a named kind inside a function named for it —
    the one channel a component has — so every signalled kind needs one."""
    from vera.codegen.wasi import _Layout, _op_trap
    text = _op_trap(_Layout(
        arena_base=0, bump_start=0, arena_end=0, has_alloc=False,
        statics={}, errtab=0, main_results=()))
    for kind in TRAP_KINDS.values():
        if kind.code:
            assert f"(func $trap_kind_{kind.name} unreachable)" in text
            assert f"i32.const {kind.code}\n" in text


# ---------------------------------------------------------------------------
# The runtime matrix
# ---------------------------------------------------------------------------

_HEAD = "  requires(true) ensures(true) effects(pure)\n"


def _prog(helper: str, call: str, ret: str = "@Int") -> str:
    return (helper + f"public fn main(-> {ret})\n" + _HEAD
            + "{\n  " + call + "\n}\n")


#: One violating program per named kind: ``(source, message fragments)``.
#: Each is a zero-argument `main`, which is what the WASI world runs.
KIND_CASES: dict[str, tuple[str, tuple[str, ...]]] = {
    "nat_underflow": (_prog(
        "private fn sub(@Nat, @Nat -> @Nat)\n" + _HEAD
        + "{\n  @Nat.1 - @Nat.0\n}\n", "sub(3, 4)", "@Nat"),
        ("`@Nat.1 - @Nat.0` would be negative", "(line 4)",
         "requires(@Nat.1 >= @Nat.0)")),
    "assertion_failed": (_prog(
        "private fn chk(@Int -> @Int)\n" + _HEAD
        + "{\n  assert(@Int.0 > 0);\n  @Int.0\n}\n", "chk(0 - 1)"),
        ("Assertion failed (line 4)", "assert(@Int.0 > 0)")),
    "index_out_of_bounds": (_prog(
        "private fn at(@Int -> @Int)\n" + _HEAD
        + "{\n  let @Array<Int> = [10, 20, 30];\n"
        "  @Array<Int>.0[@Int.0]\n}\n", "at(5)"),
        ("Array index out of bounds (line 5)", "0 <= @Int.0",
         "< array_length(")),
    "string_index_out_of_bounds": (_prog(
        "private fn code(@Int -> @Nat)\n" + _HEAD
        + '{\n  string_char_code("abc", @Int.0)\n}\n', "code(7)", "@Nat"),
        ("String index out of bounds (line 4)",
         'string_length("abc")', "length in bytes")),
    "float_conversion": (_prog(
        "private fn fl(@Float64 -> @Int)\n" + _HEAD
        + "{\n  floor(@Float64.0)\n}\n", "fl(nan())"),
        ("Float64 to Int conversion out of range (line 4)",
         "`floor(@Float64.0)`", "[-2^63, 2^63)")),
    "overflow": (_prog(
        "private fn add(@Int, @Int -> @Int)\n" + _HEAD
        + "{\n  @Int.1 + @Int.0\n}\n", "add(9223372036854775807, 1)"),
        ("Integer overflow",)),
    "nat_guard": (_prog(
        "private fn nb(@Int -> @Nat)\n" + _HEAD
        + "{\n  let @Nat = @Int.0;\n  @Nat.0\n}\n", "nb(0 - 5)", "@Nat"),
        ("Negative value bound into a @Nat slot",)),
    "widen_guard": (_prog(
        "private fn wid(@Nat -> @Int)\n" + _HEAD + "{\n  @Nat.0\n}\n",
        "wid(18446744073709551615)"),
        ("widened into an @Int slot",)),
    "divide_by_zero": (_prog(
        "private fn div(@Int, @Int -> @Int)\n" + _HEAD
        + "{\n  @Int.1 / @Int.0\n}\n", "div(1, 0)"),
        ("Integer division by zero",)),
    "contract_violation": (_prog(
        "private fn pos(@Int -> @Int)\n"
        "  requires(@Int.0 > 0) ensures(true) effects(pure)\n"
        "{\n  @Int.0\n}\n", "pos(0 - 1)"),
        ("Precondition violation", "requires(@Int.0 > 0) failed")),
    "uncaught_exception": (
        "private fn fail(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(<Exn<Int>>)\n"
        "{\n  throw(0 - @Int.0)\n}\n"
        "public fn main(-> @Int)\n"
        "  requires(true) ensures(true) effects(<Exn<Int>>)\n"
        "{\n  fail(9223372036854775807) - 1\n}\n",
        ("An `Exn<Int>` escaped `main`", "no `handle[Exn<Int>]` caught it",
         "the value thrown was -9223372036854775807")),
}


def _compile(source: str, file: str = "trap.vera") -> CompileResult:
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source, file=file)
    errors = [d.description for d in diags if d.severity == "error"]
    assert not errors, errors
    result = codegen_compile(
        program, source=source, file=file,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    assert result.ok, [d.description for d in result.diagnostics]
    return result


def test_every_signalled_and_native_kind_has_a_case() -> None:
    """The matrix covers every kind a check can raise — each signalled kind,
    the contract channel, and the native division trap; heap exhaustion is
    covered by the capped cells below, where no regression can make it
    allocate for real."""
    raised = {row.kind for row in TRAP_EMITTERS.values()}
    covered = set(KIND_CASES) | {"heap_exhausted"}
    assert raised <= covered, raised - covered


def _assert_named(kind: str, trap_kind: str, message: str, fix: str) -> None:
    assert trap_kind == kind, (trap_kind, message)
    for fragment in KIND_CASES[kind][1]:
        assert fragment in message, (fragment, message)
    assert fix == TRAP_KINDS[kind].fix


@pytest.mark.parametrize("kind", sorted(KIND_CASES))
def test_wasmtime_names_the_trap(kind: str) -> None:
    result = _compile(KIND_CASES[kind][0])
    with pytest.raises(WasmTrapError) as info:
        execute(result, fn_name="main")
    _assert_named(kind, info.value.kind, str(info.value), info.value.fix)


@pytest.mark.parametrize("kind", sorted(KIND_CASES))
def test_the_wasi_host_names_the_trap(kind: str) -> None:
    from vera.runtime.wasi_host import execute_wasi_p2
    result = _compile(KIND_CASES[kind][0])
    with pytest.raises(WasmTrapError) as info:
        execute_wasi_p2(result)
    _assert_named(kind, info.value.kind, str(info.value), info.value.fix)
    # The message travelled on stderr and was taken back off it: the
    # program's own stderr transcript does not carry it.
    assert KIND_CASES[kind][1][0] not in info.value.stderr


@pytest.mark.parametrize("kind", sorted(KIND_CASES))
def test_vera_run_wasi_p2_names_the_trap(kind: str, tmp_path: Path) -> None:
    """The WASI 0.2 leg as a user meets it: `vera run --target wasi-p2
    --json`, whose envelope carries the kind, the message and the Fix."""
    source = tmp_path / "trap.vera"
    source.write_text(KIND_CASES[kind][0], encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "-m", "vera.cli", "run", "--target", "wasi-p2",
         "--json", str(source)],
        capture_output=True, text=True, encoding="utf-8", timeout=300,
        check=False, cwd=tmp_path,
    )
    assert proc.returncode == 1, (proc.returncode, proc.stderr[-800:])
    envelope = json.loads(proc.stdout)
    [diag] = envelope["diagnostics"]
    _assert_named(kind, diag["trap_kind"], diag["description"], diag["fix"])



# --- A message longer than one write reaches the WASI host whole -----------
#
# A component can send a trap's message only on stderr, 4096 bytes a write.
# The adapter marks where the message starts with a write of its own, and
# the host takes everything after that mark — so a message quoting a long
# literal arrives whole, as on wasmtime, and the program's own stderr
# (a lone newline included, the mark's own byte) stays the program's.

_LONG = "x" * 5000

#: A trap whose message is longer than one write, on each message channel:
#: the kinds whose sites carry their own message, and the contract channel.
LONG_MESSAGES: dict[str, str] = {
    "assertion_failed": (
        "public fn main(-> @Int)\n"
        "  requires(true) ensures(true) effects(<IO>)\n"
        '{\n  IO.stderr("before\\n");\n  IO.stderr("\\n");\n'
        '  assert(string_length("' + _LONG + '") == 0);\n  1\n}\n'),
    "string_index_out_of_bounds": (
        "public fn main(-> @Nat)\n"
        "  requires(true) ensures(true) effects(<IO>)\n"
        '{\n  IO.stderr("before\\n");\n  IO.stderr("\\n");\n'
        '  string_char_code("' + _LONG + '", 9000)\n}\n'),
    "contract_violation": (
        "private fn p(@String -> @Int)\n"
        '  requires(@String.0 != "' + _LONG + '") ensures(true) effects(pure)\n'
        "{\n  0\n}\n"
        "public fn main(-> @Int)\n"
        "  requires(true) ensures(true) effects(<IO>)\n"
        '{\n  IO.stderr("before\\n");\n  IO.stderr("\\n");\n'
        '  p("' + _LONG + '")\n}\n'),
}


@pytest.mark.parametrize("kind", sorted(LONG_MESSAGES))
def test_the_wasi_host_takes_a_long_message_whole(kind: str) -> None:
    from vera.runtime.wasi_host import execute_wasi_p2
    result = _compile(LONG_MESSAGES[kind])
    with pytest.raises(WasmTrapError) as native:
        execute(result, fn_name="main")
    with pytest.raises(WasmTrapError) as wasi:
        execute_wasi_p2(result)
    assert len(str(native.value).encode("utf-8")) > 4096
    assert (wasi.value.kind, str(wasi.value)) == (kind, str(native.value))
    assert wasi.value.stderr == "before\n\n"


def test_the_mark_is_the_last_lone_one_that_more_writes_follow() -> None:
    """The host reads the mark from the write boundaries: a program's own
    newline writes come before it, every chunk of the message but the last
    is a full 4096 bytes, and a last chunk that is itself a lone newline
    has nothing after it."""
    from vera.runtime.wasi_host import message_mark

    def mark(*chunks: bytes) -> int | None:
        buf, writes = bytearray(), []
        for chunk in chunks:
            writes.append((len(buf), len(chunk)))
            buf += chunk
        return message_mark(buf, writes)

    msg = b"m" * 4096
    assert mark(b"out\n", b"\n", b"\n", b"short message") == 5
    assert mark(b"\n", msg, msg, b"tail") == 0
    assert mark(b"\n", b"\n", msg, b"\n") == 1
    assert mark(b"\n", b"\n") == 0
    assert mark(b"no mark here", b"message") is None
    assert mark(b"\n") is None
    assert mark(b"\n", b"x" * 100, b"tail") is None


# --- The WASI host lets go of its store before it returns ------------------
#
# wasmtime drops a component's stdout / stderr stream on whichever thread
# holds it last — a stream the program wrote to belongs to a tokio worker —
# and the drop calls back into Python to release the output callback.  A
# Python callback from a foreign thread while the interpreter shuts down ends
# that thread with `pthread_exit`, whose forced unwind cannot cross wasmtime's
# Rust frames: the process aborts (SIGABRT, "panic in a function that cannot
# unwind") after printing a correct envelope, which `vera run --target
# wasi-p2` did on Linux.  A trap made that the usual order of events:
# the error wasmtime-py raises keeps its own frame alive in a reference cycle,
# that frame holds the store, and the store was left to the cycle collector —
# which, in a process about to exit, runs at interpreter shutdown.

_WROTE_STDERR = (
    "public fn main(-> @Int)\n"
    "  requires(true) ensures(true) effects(<IO>)\n"
    '{\n  IO.stderr("note\\n");\n  7\n}\n'
)


def _live_output_callbacks() -> list[str]:
    """The output callbacks `execute_wasi_p2` created that are still alive."""
    return [
        obj.__qualname__ for obj in gc.get_objects()
        if inspect.isfunction(obj)
        and obj.__module__ == "vera.runtime.wasi_host"
        and obj.__name__ in ("_on_stdout", "_on_stderr")
    ]


@pytest.mark.parametrize(
    "case", ["float_conversion", "contract_violation", "overflow", "returns"])
def test_a_wasi_run_releases_its_output_callbacks(case: str) -> None:
    """When `execute_wasi_p2` returns or raises, nothing holds an output
    callback of its — wasmtime included, so no wasmtime thread can call
    into Python afterwards.  Measured with the cycle collector off: the
    collector is what a process that exits next may never run in time.
    Cells: a trap that writes its message to stderr, a contract violation
    (the same write on the contract channel), a trap with no message, and a
    normal return after a stderr write."""
    from vera.runtime.wasi_host import execute_wasi_p2
    source = _WROTE_STDERR if case == "returns" else KIND_CASES[case][0]
    result = _compile(source)
    gc.collect()
    assert not _live_output_callbacks()
    gc.disable()
    try:
        if case == "returns":
            assert execute_wasi_p2(result).value == 7
        else:
            with pytest.raises(WasmTrapError):
                execute_wasi_p2(result)
        live = _live_output_callbacks()
    finally:
        gc.enable()
        gc.collect()
    assert not live, live


def test_a_wasi_run_that_fails_before_the_store_takes_its_config(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A run that fails while the config is still being built — before the
    store owns it — releases the callbacks too, and at once: the config is
    closed, so the wait for them does not run to its bound."""
    import wasmtime
    from vera.runtime.wasi_host import execute_wasi_p2

    def refuse(self: object, path: str, guest_path: str) -> None:
        raise RuntimeError("preopen refused")

    monkeypatch.setattr(wasmtime.WasiConfig, "preopen_dir", refuse)
    result = _compile(_WROTE_STDERR)
    gc.collect()
    gc.disable()
    try:
        start = time.monotonic()
        with pytest.raises(RuntimeError, match="preopen refused"):
            execute_wasi_p2(result)
        elapsed = time.monotonic() - start
        live = _live_output_callbacks()
    finally:
        gc.enable()
        gc.collect()
    assert not live, live
    assert elapsed < 1.0, elapsed


class _ClosingStore:
    """A store whose release, like wasmtime's tokio worker, lets go of a
    callback on another thread some time after `close()` returns."""

    def __init__(self, holder: list[object], delay: float) -> None:
        self.holder = holder
        self.delay = delay

    def close(self) -> None:
        threading.Timer(self.delay, self.holder.clear).start()


def test_releasing_the_store_waits_for_a_callback_freed_elsewhere() -> None:
    from vera.runtime.wasi_host import _release_store

    def sink(chunk: bytes) -> None:  # pragma: no cover — never called
        del chunk

    released = threading.Event()
    weakref.finalize(sink, released.set)
    holder: list[object] = [sink]
    del sink
    start = time.monotonic()
    assert _release_store(_ClosingStore(holder, 0.05), [released]) is True
    assert released.is_set()
    assert time.monotonic() - start >= 0.04


def test_releasing_the_store_is_bounded() -> None:
    from vera.runtime.wasi_host import _release_store
    start = time.monotonic()
    assert _release_store(
        _ClosingStore([], 0.0), [threading.Event()], timeout=0.05) is False
    assert time.monotonic() - start < 2.0


_NODE = None
try:
    from tests.test_browser import _HAS_EXNREF, _run_node
    if _HAS_EXNREF:
        _NODE = _run_node
except ImportError:  # pragma: no cover — the browser harness module moved
    _NODE = None

browser = pytest.mark.skipif(
    _NODE is None,
    reason="Node.js not available or lacks --experimental-wasm-exnref support",
)


@browser
@pytest.mark.parametrize("kind", sorted(KIND_CASES))
def test_the_browser_runtime_names_the_trap(
    kind: str, tmp_path: Path,
) -> None:
    result = _compile(KIND_CASES[kind][0])
    wasm = tmp_path / "trap.wasm"
    wasm.write_bytes(result.wasm_bytes)
    assert _NODE is not None
    out = _NODE(wasm, fn="main")
    assert out["error"], out
    _assert_named(kind, out["trapKind"], out["error"], out["fix"])


# ---------------------------------------------------------------------------
# Native traps: derived from the emitted sites and the engines' own messages
# ---------------------------------------------------------------------------
#
# A trap the WASM engine raises itself is named from the engine's reason and,
# where a host can read it, the instruction that trapped.  So the matrix is
# DERIVED, not listed: every natively trapping instruction the static scan
# finds in the code generator, every way WebAssembly says it traps
# (`native_trap_conditions`), run on each engine for the reason the engine
# really gives.  A NaN truncation reported `unknown` because a hand list of
# one program per kind never ran one; a new trapping site joins this matrix
# with no edit here.


def native_trap_matrix(
    sites: Counter[tuple[str, str]],
) -> list[NativeTrapCondition]:
    """Every trap condition of every natively trapping instruction *sites*
    holds, in a stable order."""
    instructions = sorted({token for (_site, token) in sites
                           if token in NATIVE_TRAPPING_INSTRUCTIONS})
    return [cell for instruction in instructions
            for cell in native_trap_conditions(instruction)]


NATIVE_MATRIX = native_trap_matrix(literal_sites())


def _cell_id(cell: NativeTrapCondition) -> str:
    return f"{cell.instruction}: {cell.condition}"


def _cell_module(cell: NativeTrapCondition) -> str:
    result = cell.instruction.split(".")[0]
    body = " ".join((*cell.operands, cell.instruction))
    return f'(module (func (export "t") (result {result}) {body}))'


def _cell_component(cell: NativeTrapCondition) -> bytes:
    """The cell's function inside a component, lifted — the shape the WASI
    host meets a trap in, and the binary its backtrace offsets index."""
    import wasmtime
    result = cell.instruction.split(".")[0]
    lifted = {"i32": "s32", "i64": "s64"}[result]
    body = " ".join((*cell.operands, cell.instruction))
    return bytes(wasmtime.wat2wasm(
        "(component\n"
        f'  (core module $M (func (export "t") (result {result}) {body}))\n'
        "  (core instance $m (instantiate $M))\n"
        f'  (func (export "t") (result {lifted}) '
        '(canon lift (core func $m "t")))\n'
        ")\n"))


def _wasmtime_kind(cell: NativeTrapCondition) -> str:
    """What `execute()` reports for the cell's trap."""
    import wasmtime
    wat = _cell_module(cell)
    result = CompileResult(
        wat=wat, wasm_bytes=bytes(wasmtime.wat2wasm(wat)), exports=["t"],
        diagnostics=[])
    with pytest.raises(WasmTrapError) as info:
        execute(result, fn_name="t")
    return info.value.kind


def _wasi_kind(cell: NativeTrapCondition) -> str:
    """What the WASI 0.2 host reports for the cell's trap in a component."""
    import wasmtime
    from wasmtime.component import Component, Linker
    from vera.runtime.wasi_host import _component_trap_error
    binary = _cell_component(cell)
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    try:
        instance = Linker(engine).instantiate(
            store, Component(engine, binary))
        func = instance.get_func(store, "t")
        assert func is not None
        with pytest.raises(wasmtime.WasmtimeError) as info:
            func(store)
        return _component_trap_error(
            info.value, bytearray(), bytearray(), None, binary).kind
    finally:
        store.close()


def _browser_kind(cell: NativeTrapCondition, tmp_path: Path) -> str:
    """What the browser runtime reports for the cell's trap under V8."""
    import wasmtime
    wasm = tmp_path / "cell.wasm"
    wasm.write_bytes(bytes(wasmtime.wat2wasm(_cell_module(cell))))
    assert _NODE is not None
    out = _NODE(wasm, fn="t")
    assert out["error"], out
    return str(out["trapKind"])


def test_every_emitted_native_instruction_is_in_the_matrix() -> None:
    """The derivation reaches every natively trapping instruction the code
    generator emits, each with at least one condition — the zero-divisor
    cell of the `/` every program can write among them."""
    emitted = {token for (_site, token) in literal_sites()
               if token in NATIVE_TRAPPING_INSTRUCTIONS}
    assert emitted == {cell.instruction for cell in NATIVE_MATRIX}
    assert "i64.div_s: a zero divisor" in {_cell_id(c) for c in NATIVE_MATRIX}


def test_the_opcode_table_is_the_encoders() -> None:
    """`NATIVE_TRAP_OPCODES` is what the assembler emits: each instruction,
    assembled as the last one in a function, sits just before its `end`."""
    import wasmtime
    for instruction in sorted(NATIVE_TRAPPING_INSTRUCTIONS):
        cell = native_trap_conditions(instruction)[0]
        binary = bytes(wasmtime.wat2wasm(_cell_module(cell)))
        assert binary[-1] == 0x0B, instruction
        assert NATIVE_TRAP_OPCODES.get(binary[-2]) == instruction, (
            instruction, hex(binary[-2]))


@pytest.mark.parametrize("cell", NATIVE_MATRIX, ids=_cell_id)
def test_wasmtime_names_every_native_trap(cell: NativeTrapCondition) -> None:
    assert _wasmtime_kind(cell) == cell.kind


@pytest.mark.parametrize("cell", NATIVE_MATRIX, ids=_cell_id)
def test_the_wasi_host_names_every_native_trap(
    cell: NativeTrapCondition,
) -> None:
    assert _wasi_kind(cell) == cell.kind


@browser
@pytest.mark.parametrize("cell", NATIVE_MATRIX, ids=_cell_id)
def test_the_browser_names_every_native_trap(
    cell: NativeTrapCondition, tmp_path: Path,
) -> None:
    assert _browser_kind(cell, tmp_path) == cell.kind


def test_a_nan_truncation_is_named_from_its_reason_alone() -> None:
    """Where no instruction can be read — no frame, or bytes that are not
    the module's — wasmtime's own reason for a NaN truncation still names
    it, since no other trap shares that reason."""
    from vera.runtime.traps import _classify_trap

    class _Reason(Exception):
        pass

    kind, _description, fix = _classify_trap(
        _Reason("wasm trap: invalid conversion to integer"), [])
    assert kind == "float_conversion"
    assert fix == TRAP_KINDS["float_conversion"].fix


def test_a_trap_wrapped_in_another_error_still_names_its_instruction() -> None:
    """Some call paths raise an error whose cause is the `Trap` holding the
    frames; the instruction is read through that chain, as the backtrace
    is, so a truncation inside it is not taken for `INT_MIN / -1`."""
    import wasmtime
    from vera.runtime.traps import _classify_trap, trapping_instruction
    cell = native_trap_conditions("i64.trunc_f64_s")[2]
    binary = bytes(wasmtime.wat2wasm(_cell_module(cell)))
    store = wasmtime.Store()
    instance = wasmtime.Instance(store, wasmtime.Module(store.engine, binary), [])
    with pytest.raises(wasmtime.Trap) as info:
        instance.exports(store)["t"](store)

    class _Wrapped(Exception):
        pass

    wrapped = _Wrapped("wasm trap: integer overflow")
    wrapped.__cause__ = info.value
    instruction = trapping_instruction(wrapped, binary)
    assert instruction == "i64.trunc_f64_s"
    assert _classify_trap(wrapped, [], instruction=instruction)[0] == (
        "float_conversion")


#: A trapping instruction no emitter uses today, planted as a new site.
_PLANTED_SITE = pyast.parse(
    'def emit_planted():\n'
    '    return ["f32.const 1", "i32.trunc_f32_u", "drop"]\n')


@pytest.mark.parametrize("host", ["wasmtime", "wasi", "browser"])
def test_a_planted_native_site_joins_the_matrix_and_is_named(
    host: str, tmp_path: Path,
) -> None:
    """A site the scan has never seen is derived into the matrix with no
    edit here, and every host names each way it traps."""
    if host == "browser" and _NODE is None:
        pytest.skip("Node.js not available or lacks exnref support")
    planted = native_trap_matrix(
        literal_sites_for_tree(_PLANTED_SITE, "wasm/planted.py"))
    assert [c.condition for c in planted] == [
        "NaN", "an infinity", "a finite value past its range"]
    for cell in planted:
        kind = (_wasmtime_kind(cell) if host == "wasmtime"
                else _wasi_kind(cell) if host == "wasi"
                else _browser_kind(cell, tmp_path))
        assert kind == cell.kind, (_cell_id(cell), kind)


# ---------------------------------------------------------------------------
# A program's own names cannot decide the kind
# ---------------------------------------------------------------------------
#
# A host that names a trap from text must read only text no program can
# write: the engine's reason, and the frames of the adapter's own functions
# (`Adapter!op_contract_fail`, `Adapter!trap_kind_<kind>`).  A backtrace also
# names every program function on the stack, so a function called
# `contract_fail`, `trap_kind_<kind>` or `unreachable` — each a string a host
# once searched the whole text for (#1518) — holds a DIFFERENT trap here, and
# every host must report that trap.

#: Every name a host has read a trap's cause from — and ones that merely
#: contain such a name, as a backtrace line does.
_HOST_READ_NAMES = ["contract_fail", "check_contract_fail", "unreachable",
                    "unreachable_div",
                    *(f"trap_kind_{kind}" for kind in sorted(TRAP_KINDS))]

#: The traps planted inside a function of each name: two the engine raises
#: itself — one whose reason a host's table matches before `unreachable`,
#: one after it — and one a named check signals.
_INNER_TRAPS: dict[str, tuple[str, str, str]] = {
    "divide_by_zero": ("@Int, @Int", "@Int.1 / @Int.0", "7, 0"),
    "overflow": ("@Int, @Int", "@Int.1 / @Int.0",
                 "0 - 9223372036854775807 - 1, 0 - 1"),
    "index_out_of_bounds": (
        "@Int, @Int", "let @Array<Int> = [1, 2, 3];\n  @Array<Int>.0[@Int.1]",
        "7, 0"),
}


def _forged_name_program(name: str, inner: str) -> str:
    params, body, args = _INNER_TRAPS[inner]
    return (
        f"private fn {name}({params} -> @Int)\n" + _HEAD
        + "{\n  " + body + "\n}\n"
        + "public fn main(-> @Int)\n" + _HEAD
        + "{\n  " + f"{name}({args})" + "\n}\n")


def test_the_core_host_reads_the_trap_code_and_not_the_text() -> None:
    """Where wasmtime gives a structured trap code, the core host reads it
    and nothing else: here the text claims an `unreachable`, the code says
    division by zero, and the code wins; a code no row names is `unknown`
    rather than whatever the text suggests."""
    from types import SimpleNamespace
    from vera.runtime.traps import _classify_trap

    class _Coded(Exception):
        def __init__(self, code: str) -> None:
            super().__init__(
                "error while executing at wasm backtrace:\n"
                "    0:     0x2c - <unknown>!f\n\nCaused by:\n"
                "    wasm trap: wasm `unreachable` instruction executed\n")
            self.trap_code = SimpleNamespace(name=code)

    assert _classify_trap(_Coded("INTEGER_DIVISION_BY_ZERO"), [])[0] == (
        "divide_by_zero")
    assert _classify_trap(_Coded("TABLE_OUT_OF_BOUNDS"), [])[0] == "unknown"


_FORGED_CELLS = [
    (name, inner) for name in _HOST_READ_NAMES for inner in _INNER_TRAPS
    if name != f"trap_kind_{inner}"
]


@pytest.mark.parametrize("host", ["wasmtime", "wasi", "browser"])
@pytest.mark.parametrize(("name", "inner"), _FORGED_CELLS,
                         ids=[f"{n}-holds-{i}" for n, i in _FORGED_CELLS])
def test_a_function_named_like_a_host_read_frame_cannot_forge_the_kind(
    name: str, inner: str, host: str, tmp_path: Path,
) -> None:
    result = _compile(_forged_name_program(name, inner))
    if host == "wasmtime":
        with pytest.raises(WasmTrapError) as info:
            execute(result, fn_name="main")
        kind = info.value.kind
    elif host == "wasi":
        from vera.runtime.wasi_host import execute_wasi_p2
        with pytest.raises(WasmTrapError) as info:
            execute_wasi_p2(result)
        kind = info.value.kind
    else:
        if _NODE is None:
            pytest.skip("Node.js not available or lacks exnref support")
        wasm = tmp_path / "forged.wasm"
        wasm.write_bytes(result.wasm_bytes)
        out = _NODE(wasm, fn="main")
        assert out["error"], out
        kind = str(out["trapKind"])
    assert kind == inner, (name, inner, host, kind)


# ---------------------------------------------------------------------------
# `vera test` reads the kind, not the message
# ---------------------------------------------------------------------------

def test_vera_test_classifies_a_trial_by_its_trap_kind() -> None:
    """A trial fails only on a broken contract.  A site message quotes the
    program's text, so a message that reads "contract" is not one: an index
    into the string "contract" is an `error`, whatever its message says."""
    from vera.tester import test as run_trials
    source = (
        "public fn code(@Int -> @Nat)\n"
        "  requires(true) ensures(@Nat.result < 256) effects(pure)\n"
        '{\n  string_char_code("contract", @Int.0)\n}\n')
    program = parse_to_ast(source)
    diags, _ = typecheck_with_artifacts(program, source)
    assert not [d for d in diags if d.severity == "error"]
    result = run_trials(program, source=source, file="t.vera", trials=40)
    [function] = [f for f in result.functions if f.fn_name == "code"]
    statuses = {failure.status for failure in function.failures}
    assert statuses == {"error"}, [
        (f.status, f.message[:80]) for f in function.failures]
    assert any("contract" in f.message for f in function.failures)


# ---------------------------------------------------------------------------
# An exception leaving an entry point
# ---------------------------------------------------------------------------
#
# An export whose effect row declares `Exn<T>` is called through a boundary
# that catches what leaves it and signals `uncaught_exception`, naming the
# exception's type and, where printable, the value thrown — at every entry
# point: `main`, a `vera run --fn` target, a `vera serve` handler and a
# `vera test` trial.  The engine alone says only that an exception was
# thrown, which every host reported as `unknown` with no Fix.

def _escape_program(payload: str, throw: str) -> str:
    """`g` throws; the entry points `f` (a `--fn` target, taking the
    argument) and `main` reach it without a handler."""
    row = f"  requires(true) ensures(true) effects(<Exn<{payload}>>)\n"
    return ("type Pos = { @Int | @Int.0 > 0 };\n"
            "private fn g(@Int -> @Int)\n" + row + "{\n  " + throw + "\n}\n"
            "public fn f(@Int -> @Int)\n" + row + "{\n  g(@Int.0)\n}\n"
            "public fn main(-> @Int)\n" + row + "{\n  f(ARG)\n}\n")


def _escaped(payload: str, entry: str, value: str | None) -> str:
    stated = (f"An `Exn<{payload}>` escaped `{entry}`: no "
              f"`handle[Exn<{payload}>]` caught it before the call returned")
    return stated + (f", and the value thrown was {value}"
                     if value is not None else ".")


#: One escape per payload shape the boundary formats:
#: ``(payload type, the throw, the argument, the value as quoted)``.
ESCAPES: dict[str, tuple[str, str, int, str | None]] = {
    "Int": ("Int", "throw(0 - @Int.0 - 1)", 9223372036854775807,
            "-9223372036854775808"),
    "Nat": ("Nat", "throw(18446744073709551615)", 0, "18446744073709551615"),
    "Byte": ("Byte", "match int_to_byte(@Int.0) {\n"
             "    Some(@Byte) -> throw(@Byte.0),\n    None -> 0\n  }",
             200, "200"),
    "Bool": ("Bool", "throw(@Int.0 > 0)", 1, "true"),
    "String": ("String", 'throw("disk full")', 0, '"disk full"'),
    "long String": ("String", 'throw(string_repeat("ab", 40))', 0,
                    '"' + "ab" * 32 + '…"'),
    "Float64": ("Float64", "throw(1.5)", 0, None),
    "Tuple": ("Tuple<Int, Int>", "throw(Tuple(@Int.0, 2))", 1, None),
    # Named as the row spells it, not as the refinement it resolves to, so
    # the `handle[Exn<Pos>]` the Fix asks for is one the reader can write.
    "refined alias": ("Pos", "throw(@Int.0 + 1)", 6, "7"),
}


def _escape_source(case: str) -> str:
    payload, throw, arg, _ = ESCAPES[case]
    return _escape_program(payload, throw).replace("ARG", str(arg))


def _assert_escape(case: str, entry: str, kind: str, message: str,
                   fix: str) -> None:
    payload, _throw, _arg, value = ESCAPES[case]
    assert (kind, message) == (
        "uncaught_exception", _escaped(payload, entry, value))
    assert fix == TRAP_KINDS["uncaught_exception"].fix


@pytest.mark.parametrize("entry", ["main", "f"])
@pytest.mark.parametrize("case", sorted(ESCAPES))
def test_wasmtime_names_an_exception_leaving_an_entry_point(
    case: str, entry: str,
) -> None:
    result = _compile(_escape_source(case))
    args = [ESCAPES[case][2]] if entry == "f" else None
    with pytest.raises(WasmTrapError) as info:
        execute(result, fn_name=entry, args=args)
    _assert_escape(case, entry, info.value.kind, str(info.value),
                   info.value.fix)


@pytest.mark.parametrize("case", sorted(ESCAPES))
def test_the_wasi_host_names_an_exception_leaving_main(case: str) -> None:
    from vera.runtime.wasi_host import execute_wasi_p2
    result = _compile(_escape_source(case))
    with pytest.raises(WasmTrapError) as info:
        execute_wasi_p2(result)
    _assert_escape(case, "main", info.value.kind, str(info.value),
                   info.value.fix)
    assert "escaped" not in info.value.stderr


@browser
@pytest.mark.parametrize("entry", ["main", "f"])
@pytest.mark.parametrize("case", sorted(ESCAPES))
def test_the_browser_names_an_exception_leaving_an_entry_point(
    case: str, entry: str, tmp_path: Path,
) -> None:
    result = _compile(_escape_source(case))
    wasm = tmp_path / "escape.wasm"
    wasm.write_bytes(result.wasm_bytes)
    assert _NODE is not None
    out = _NODE(wasm, fn=entry,
                fn_args=[str(ESCAPES[case][2])] if entry == "f" else None)
    _assert_escape(case, entry, out["trapKind"], out["error"], out["fix"])


def test_a_handled_exception_still_reaches_its_handler() -> None:
    """The boundary wraps the export only: a `handle[Exn<T>]` below the
    entry point catches as it did, on the direct call the handler's body
    makes."""
    source = (
        "private fn g(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(<Exn<Int>>)\n"
        "{\n  throw(@Int.0 + 1)\n}\n"
        "public fn f(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(<Exn<Int>>)\n"
        "{\n  g(@Int.0)\n}\n"
        "public fn main(-> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{\n  handle[Exn<Int>] {\n    throw(@Int) -> @Int.0 * 10\n"
        "  } in {\n    f(4)\n  }\n}\n")
    result = _compile(source)
    assert execute(result, fn_name="main").value == 50


def test_vera_serve_answers_an_escaped_exception_with_its_kind() -> None:
    """A `vera serve` handler is an entry point too: the 500 it answers
    carries the kind and the message naming the exception."""
    import urllib.error
    import urllib.request
    from vera.runtime.server import make_server
    source = (
        "public fn handle(@Request -> @Response)\n"
        "  requires(true) ensures(true) effects(<HttpServer, Exn<String>>)\n"
        "{\n  match @Request.0 {\n"
        "    Request(@String, @String, @Map<String, String>, @String) ->\n"
        "      throw(@String.1)\n  }\n}\n")
    httpd = make_server(_compile(source), host="127.0.0.1", port=0)
    thread = threading.Thread(target=httpd.serve_forever, daemon=True)
    thread.start()
    try:
        url = f"http://127.0.0.1:{httpd.server_address[1]}/no/such/page"
        with pytest.raises(urllib.error.HTTPError) as info:
            urllib.request.urlopen(url, timeout=30)
        payload = json.loads(info.value.read().decode("utf-8"))
    finally:
        httpd.shutdown()
        httpd.server_close()
    assert info.value.code == 500
    assert payload["trap_kind"] == "uncaught_exception"
    assert payload["error"] == (
        "An `Exn<String>` escaped `handle`: no `handle[Exn<String>]` caught it "
        'before the call returned, and the value thrown was "/no/such/page"')


def test_vera_test_names_an_exception_a_trial_leaves_by() -> None:
    """A `vera test` trial calls the function through its export, so an
    exception its inputs provoke is the trial's `error`, named — and
    `vera test --json` carries the kind beside the message."""
    source = (
        "public fn picky(@Int -> @Int)\n"
        "  requires(true) ensures(true) decreases(0) effects(<Exn<Int>>)\n"
        "{\n  if @Int.0 > 3 then {\n    throw(@Int.0)\n  } else {\n"
        "    @Int.0\n  }\n}\n")
    from vera.tester import test as run_trials
    program = parse_to_ast(source)
    diags, _ = typecheck_with_artifacts(program, source)
    assert not [d for d in diags if d.severity == "error"]
    result = run_trials(program, source=source, file="t.vera", trials=40)
    [function] = [f for f in result.functions if f.fn_name == "picky"]
    assert function.failures, function
    for failure in function.failures:
        assert failure.status == "error", failure
        assert failure.trap_kind == "uncaught_exception", failure
        [value] = failure.args.values()
        assert failure.message == _escaped("Int", "picky", str(value))


# --- The hosts name an exception no boundary catches ------------------------
#
# Every export a module compiled from Vera declares its `Exn<T>` and has a
# boundary.  A module built another way can still let one out, and each host
# names it from what the engine itself reports rather than `unknown`: the
# reason wasmtime gives it (it carries no trap code), and the
# `WebAssembly.Exception` V8 raises.

_BARE_THROW = (
    '(module (tag $t (param i64)) (func (export "t") (result i64) '
    "i64.const 5 throw $t))")


def test_wasmtime_names_an_exception_no_boundary_catches() -> None:
    import wasmtime
    result = CompileResult(
        wat=_BARE_THROW, wasm_bytes=bytes(wasmtime.wat2wasm(_BARE_THROW)),
        exports=["t"], diagnostics=[])
    with pytest.raises(WasmTrapError) as info:
        execute(result, fn_name="t")
    assert info.value.kind == "uncaught_exception"
    assert info.value.fix == TRAP_KINDS["uncaught_exception"].fix


def test_the_wasi_host_names_an_exception_no_boundary_catches() -> None:
    import wasmtime
    from wasmtime.component import Component, Linker
    from vera.runtime.wasi_host import _component_trap_error
    binary = bytes(wasmtime.wat2wasm(
        "(component\n"
        "  (core module $M (tag $t (param i64)) (func (export \"t\") "
        "(result i64) i64.const 5 throw $t))\n"
        "  (core instance $m (instantiate $M))\n"
        '  (func (export "t") (result s64) (canon lift (core func $m "t")))\n'
        ")\n"))
    config = wasmtime.Config()
    config.wasm_exceptions = True
    engine = wasmtime.Engine(config)
    store = wasmtime.Store(engine)
    try:
        instance = Linker(engine).instantiate(
            store, Component(engine, binary))
        func = instance.get_func(store, "t")
        assert func is not None
        with pytest.raises(wasmtime.WasmtimeError) as info:
            func(store)
        error = _component_trap_error(
            info.value, bytearray(), bytearray(), None, binary)
    finally:
        store.close()
    assert error.kind == "uncaught_exception", str(error)


@browser
def test_the_browser_names_an_exception_no_boundary_catches(
    tmp_path: Path,
) -> None:
    import wasmtime
    wasm = tmp_path / "bare.wasm"
    wasm.write_bytes(bytes(wasmtime.wat2wasm(_BARE_THROW)))
    assert _NODE is not None
    out = _NODE(wasm, fn="t")
    assert out["trapKind"] == "uncaught_exception", out
    assert out["fix"] == TRAP_KINDS["uncaught_exception"].fix


@browser
def test_the_browser_names_a_host_bindings_refusal(tmp_path: Path) -> None:
    """A host binding that refuses (here `json_stringify` of a non-finite
    number) leaves `call()` as `host_error` with the binding's own message,
    as it does on wasmtime — not as the binding's bare `Error`."""
    source = (
        "public fn main(-> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{\n  string_length(json_stringify(JNumber(nan())))\n}\n")
    result = _compile(source)
    with pytest.raises(WasmTrapError) as native:
        execute(result, fn_name="main")
    wasm = tmp_path / "host.wasm"
    wasm.write_bytes(result.wasm_bytes)
    assert _NODE is not None
    out = _NODE(wasm, fn="main")
    assert native.value.kind == "host_error"
    assert out["trapKind"] == "host_error", out
    assert out["error"] and out["fix"] == ""


# ---------------------------------------------------------------------------
# The fan-in cells
# ---------------------------------------------------------------------------

#: A module whose ONLY check of a signal's kind sits in one per-scope seam.
#: None of them allocates except the closure's (a closure environment is a
#: heap object), so the `vera.trap` import is declared only if the seam's
#: flag reached the module; the closure's check is a CONTRACT check, whose
#: import no allocation declares.
FAN_IN_CELLS: dict[str, tuple[str, int, str]] = {
    "postcondition": (
        "public fn main(-> @Int)\n"
        "  requires(true) ensures(@Int.result + 1 > 0) effects(pure)\n"
        "{\n  7\n}\n", 7, "trap"),
    "where helper": (
        "public fn main(-> @Int)\n" + _HEAD
        + "{\n  half(8)\n}\nwhere {\n"
        "  fn half(@Int -> @Int)\n" + _HEAD
        + "  {\n    assert(@Int.0 > 0);\n    @Int.0\n  }\n}\n", 8, "trap"),
    "closure": (
        "type Pos = { @Int | @Int.0 > 0 };\n"
        "public fn main(-> @Int)\n" + _HEAD
        + "{\n  apply_fn(fn(@Pos -> @Int) effects(pure) { @Pos.0 }, 9)\n}\n",
        9, "contract_fail"),
}


@pytest.mark.parametrize("scope", sorted(FAN_IN_CELLS))
def test_a_check_only_in_one_scope_still_links(scope: str) -> None:
    source, value, signal = FAN_IN_CELLS[scope]
    result = _compile(source)
    assert f'(import "vera" "{signal}"' in result.wat, (
        f"the {scope} cell's signal import is not declared")
    assert execute(result, fn_name="main").value == value


@pytest.mark.parametrize("scope", sorted(FAN_IN_CELLS))
def test_a_check_only_in_one_scope_links_under_wasi(scope: str) -> None:
    from vera.runtime.wasi_host import execute_wasi_p2
    source, value, _signal = FAN_IN_CELLS[scope]
    assert execute_wasi_p2(_compile(source)).value == value


@browser
@pytest.mark.parametrize("scope", sorted(FAN_IN_CELLS))
def test_a_check_only_in_one_scope_links_in_the_browser(
    scope: str, tmp_path: Path,
) -> None:
    source, value, _signal = FAN_IN_CELLS[scope]
    wasm = tmp_path / "fan_in.wasm"
    wasm.write_bytes(_compile(source).wasm_bytes)
    assert _NODE is not None
    out = _NODE(wasm, fn="main")
    assert out["error"] is None, out
    assert out["value"] == value


# ---------------------------------------------------------------------------
# Heap exhaustion under a memory cap
# ---------------------------------------------------------------------------

#: Run in a SUBPROCESS whose wasmtime stores are capped at 64 MiB, so no
#: regression in the allocator's checks can make a cell allocate gigabytes
#: on the machine running the suite.
_CAPPED_RUN = r'''
import sys, wasmtime
# The parent decodes UTF-8; a Windows pipe would otherwise carry the locale's
# code page, and a Fix paragraph's em dash would not survive the trip.
sys.stdout.reconfigure(encoding="utf-8")
_Store = wasmtime.Store
class _Capped(_Store):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.set_limits(memory_size=64 * 1024 * 1024)
wasmtime.Store = _Capped

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen.api import execute
from vera.parser import parse_to_ast
from vera.runtime.traps import WasmTrapError

source = sys.stdin.read()
program = parse_to_ast(source)
_d, arts = typecheck_with_artifacts(program, source)
result = codegen_compile(
    program, source=source,
    expr_semantic_types=arts.expr_semantic_types,
    expr_target_types=arts.expr_target_types)
host = sys.argv[1]
if host == "wasm-bytes":
    sys.stdout.buffer.write(result.wasm_bytes)
    raise SystemExit(0)
try:
    if host == "wasi":
        from vera.runtime.wasi_host import execute_wasi_p2
        execute_wasi_p2(result)
    else:
        execute(result, fn_name="main")
    print("NO TRAP")
except WasmTrapError as exc:
    print(exc.kind)
    print(exc.fix)
    print(str(exc))
'''

#: The allocator's two ways to run out: one request of 2 GiB or more (the
#: size-header check, before any memory is touched), and a heap that keeps
#: every value it builds until the host refuses `memory.grow` at the cap.
HEAP_CASES: dict[str, str] = {
    "a single request of 2 GiB or more": _prog(
        "private fn big(@Nat -> @String)\n" + _HEAD
        + '{\n  string_repeat("a", @Nat.0)\n}\n',
        "string_length(big(3000000000))", "@Nat"),
    "growth refused at the cap": (
        "private fn grow(@Nat, @Array<String> -> @Nat)\n"
        "  requires(true) ensures(true) decreases(@Nat.0) effects(pure)\n"
        "{\n"
        "  if @Nat.0 == 0 then { array_length(@Array<String>.0) } else {\n"
        "    grow(@Nat.0 - 1, array_append(@Array<String>.0,"
        ' string_repeat("x", 1048576)))\n'
        "  }\n"
        "}\n"
        "public fn main(-> @Nat)\n" + _HEAD
        + "{\n  grow(1000, [])\n}\n"),
}


def _capped(
    host: str, source: str, *, io_encoding: str | None = None,
) -> subprocess.CompletedProcess[str]:
    env = {**os.environ, "PYTHONPATH": str(ROOT)}
    if io_encoding is not None:
        env["PYTHONIOENCODING"] = io_encoding
    return subprocess.run(
        [sys.executable, "-c", _CAPPED_RUN, host],
        input=source, capture_output=True, text=True, encoding="utf-8",
        timeout=300, check=False, cwd=ROOT, env=env,
    )


def test_the_capped_harness_writes_utf8_under_any_locale() -> None:
    """A Windows pipe carries the locale's code page unless the child says
    otherwise, and `heap_exhausted`'s Fix holds an em dash: a cp1252 child
    handed the parent a byte its UTF-8 decoder refused, and the result's
    `stdout` came back empty.  So the harness writes UTF-8 itself — asserted
    here under a cp1252 stream encoding, on every platform."""
    proc = _capped("wasmtime", HEAP_CASES["a single request of 2 GiB or more"],
                   io_encoding="cp1252")
    assert proc.returncode == 0, proc.stderr[-2000:]
    assert proc.stdout is not None
    assert proc.stdout.splitlines()[0] == "heap_exhausted", proc.stdout[:300]
    assert TRAP_KINDS["heap_exhausted"].fix in proc.stdout


@pytest.mark.parametrize("host", ["wasmtime", "wasi"])
@pytest.mark.parametrize("case", sorted(HEAP_CASES))
def test_heap_exhaustion_is_named_under_a_memory_cap(
    case: str, host: str,
) -> None:
    """Both ways out of heap trap as `heap_exhausted` with its Fix, in a
    subprocess under a 64 MiB store limit."""
    proc = _capped(host, HEAP_CASES[case])
    assert proc.returncode == 0, proc.stderr[-2000:]
    lines = proc.stdout.splitlines()
    assert lines and lines[0] == "heap_exhausted", proc.stdout[-2000:]
    assert TRAP_KINDS["heap_exhausted"].fix in proc.stdout
    assert "Heap exhausted" in proc.stdout


@browser
@pytest.mark.parametrize("case", sorted(HEAP_CASES))
def test_heap_exhaustion_is_named_in_the_browser_under_a_memory_cap(
    case: str, tmp_path: Path,
) -> None:
    """The same, in Node, whose wasm memories are capped at 64 MiB by V8's
    own page limit."""
    build = subprocess.run(
        [sys.executable, "-c", _CAPPED_RUN, "wasm-bytes"],
        input=HEAP_CASES[case].encode("utf-8"), capture_output=True,
        timeout=300,
        check=False, cwd=ROOT, env={**os.environ, "PYTHONPATH": str(ROOT)},
    )
    assert build.returncode == 0, build.stderr[-2000:]
    wasm = tmp_path / "heap.wasm"
    wasm.write_bytes(build.stdout)
    from tests.test_browser import HARNESS, NODE
    proc = subprocess.run(
        [NODE or "node", "--experimental-wasm-exnref",
         "--wasm-max-mem-pages=1024", str(HARNESS), str(wasm),
         "--fn", "main"],
        capture_output=True, text=True, encoding="utf-8", timeout=300,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr[-2000:]
    out = json.loads(proc.stdout)
    assert out["trapKind"] == "heap_exhausted", out
    assert out["error"] == "Heap exhausted"
    assert out["fix"] == TRAP_KINDS["heap_exhausted"].fix


# ---------------------------------------------------------------------------
# The record against the module, across the corpus
# ---------------------------------------------------------------------------

_SIGNAL_CALL = re.compile(
    r"i32\.const (\d+)\s+i32\.const \d+\s+i32\.const \d+\s+call \$vera\.trap\b")
_CONTRACT_CALL = re.compile(r"call \$vera\.contract_fail\b")
_FUNC = re.compile(r"^  \(func \$([^\s()]+)", re.M)

#: Runtime functions, emitted once per module and belonging to no source
#: site, so their signals are not per-site checks.
_RUNTIME_FUNCTIONS = {"alloc", "gc_collect"}


def _signals_by_function(wat: str) -> Counter[tuple[str, str]]:
    kinds = {k.code: k.name for k in TRAP_KINDS.values() if k.code}
    starts = [(m.start(), m.group(1)) for m in _FUNC.finditer(wat)]
    found: Counter[tuple[str, str]] = Counter()
    for n, (pos, name) in enumerate(starts):
        if name in _RUNTIME_FUNCTIONS:
            continue
        end = starts[n + 1][0] if n + 1 < len(starts) else len(wat)
        body = wat[pos:end]
        for match in _SIGNAL_CALL.finditer(body):
            found[(name, kinds[int(match.group(1))])] += 1
        for _ in _CONTRACT_CALL.finditer(body):
            found[(name, "contract_violation")] += 1
    return found


def _corpus() -> list[Path]:
    return sorted([*(ROOT / "examples").glob("*.vera"),
                   *(ROOT / "tests" / "conformance").glob("*.vera")])


def test_the_record_matches_every_signal_the_corpus_emits() -> None:
    """For every example and conformance program that compiles, and every
    function in it, the record lists exactly as many checks of each
    signalled kind as the module calls that kind's signal: one check, one
    signal, one entry.  A phantom entry (a translation thrown away), a
    missed one (a merge that dropped it), or an emitter that bypassed the
    path shows up as a count that differs."""
    from vera.resolver import ModuleResolver

    mismatches: list[str] = []
    compiled = 0
    for path in _corpus():
        source = path.read_text(encoding="utf-8")
        try:
            program = parse_to_ast(source)
        except Exception:  # noqa: BLE001 — a negative fixture may not parse
            continue
        resolver = ModuleResolver(_root=path.parent)
        resolved = resolver.resolve_imports(program, path)
        diags, arts = typecheck_with_artifacts(
            program, source, file=str(path), resolved_modules=resolved,
            collect_module_artifacts=True)
        if any(d.severity == "error" for d in diags) or resolver.errors:
            continue
        result = codegen_compile(
            program, source=source, file=str(path), resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
            module_artifacts=arts.module_artifacts)
        if not result.ok:
            continue
        compiled += 1
        recorded = Counter(
            (c.function, c.kind) for c in result.emitted_checks
            if not TRAP_EMITTERS[c.emitter].via.startswith("native:"))
        emitted = _signals_by_function(result.wat)
        if recorded != emitted:
            mismatches.append(
                f"{path.relative_to(ROOT).as_posix()}: recorded-only "
                f"{dict(recorded - emitted)}, emitted-only "
                f"{dict(emitted - recorded)}")
    assert compiled > 200, compiled
    assert not mismatches, mismatches


# ---------------------------------------------------------------------------
# The checks' boundaries
# ---------------------------------------------------------------------------

_INDEX = (
    "public fn at(@Int -> @Int)\n" + _HEAD
    + "{\n  let @Array<Int> = [10, 20, 30];\n  @Array<Int>.0[@Int.0]\n}\n")
_CHAR_CODE = (
    "public fn code(@Int -> @Nat)\n" + _HEAD
    + '{\n  string_char_code("abc", @Int.0)\n}\n')
_FLOOR = (
    "public fn fl(@Float64 -> @Int)\n" + _HEAD
    + "{\n  floor(@Float64.0)\n}\n")


def _outcome(source: str, fn: str, arg: int | float) -> object:
    try:
        return execute(_compile(source), fn_name=fn, args=[arg]).value
    except WasmTrapError as exc:
        return exc.kind


@pytest.mark.parametrize(("arg", "expected"), [
    (0, 10), (2, 30),
    (3, "index_out_of_bounds"),
    (-1, "index_out_of_bounds"),
    # 2^32 + 1 narrows to 1 as an i32, so a check made after the narrowing
    # passed it and read element 1; the check is made on the i64.
    (4294967297, "index_out_of_bounds"),
    (4294967296, "index_out_of_bounds"),
])
def test_an_array_index_is_checked_before_it_is_narrowed(
    arg: int, expected: object,
) -> None:
    assert _outcome(_INDEX, "at", arg) == expected


_NAT_SUB = (
    "public fn sub(@Nat, @Nat -> @Nat)\n" + _HEAD + "{\n  @Nat.1 - @Nat.0\n}\n")


@pytest.mark.parametrize(("lhs", "rhs", "expected"), [
    (5, 3, 2),
    (3, 5, "nat_underflow"),
    # Past i64.MAX: a `@Nat` is a u64, so the guard compares unsigned.  A
    # signed compare read 2^63 as negative, trapping the first with a
    # message saying the right operand was larger and passing the second.
    (2 ** 63, 1, 2 ** 63 - 1),
    (1, 2 ** 63, "nat_underflow"),
    (2 ** 64 - 1, 2 ** 64 - 1, 0),
])
def test_a_nat_subtraction_is_checked_unsigned(
    lhs: int, rhs: int, expected: object,
) -> None:
    try:
        outcome: object = execute(
            _compile(_NAT_SUB), fn_name="sub", args=[lhs, rhs]).value
    except WasmTrapError as exc:
        outcome = exc.kind
    assert outcome == expected, (lhs, rhs, outcome)


@pytest.mark.parametrize(("arg", "expected"), [
    (0, 97), (2, 99),
    (3, "string_index_out_of_bounds"),
    (-1, "string_index_out_of_bounds"),
    (4294967297, "string_index_out_of_bounds"),
])
def test_a_char_code_index_is_one_check_on_both_ends(
    arg: int, expected: object,
) -> None:
    assert _outcome(_CHAR_CODE, "code", arg) == expected


@pytest.mark.parametrize(("arg", "expected"), [
    (1.5, 1), (-1.5, -2),
    # Both ends of [-2^63, 2^63): the low bound is exact and converts, the
    # high bound is the first value that cannot.
    (-9223372036854775808.0, -9223372036854775808),
    (9223372036854775808.0, "float_conversion"),
    (1.0e19, "float_conversion"),
    (-1.0e19, "float_conversion"),
    (float("inf"), "float_conversion"),
    (float("-inf"), "float_conversion"),
    (float("nan"), "float_conversion"),
])
def test_a_float_conversion_names_every_value_outside_its_domain(
    arg: float, expected: object,
) -> None:
    assert _outcome(_FLOOR, "fl", arg) == expected
