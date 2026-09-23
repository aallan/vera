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
    TRAP_EMITTERS,
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
    for native in (*NATIVE_TRAP_SITES, *SAFE_NATIVE_SITES, *KNOWN_TRAP_DEFECTS):
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
    natively trapping instruction and an unregistered emission — and not a
    WAT comment or a docstring that merely mentions one."""
    tree = pyast.parse(
        'def emit():\n'
        '    """Traps with ``unreachable`` when the index is bad."""\n'
        '    return ["i32.eqz", "if", "  unreachable", "end",\n'
        '            "i64.div_s ;; trap on zero", ";; unreachable here"]\n'
        'def other(self):\n'
        '    return self._emit_trap("wasm/x.py:elsewhere", at=None)\n'
    )
    sites = literal_sites_for_tree(tree, "wasm/x.py")
    assert sites == Counter({("wasm/x.py:emit", "unreachable"): 1,
                             ("wasm/x.py:emit", "i64.div_s"): 1}), sites
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
    from vera.codegen.wasi import _op_trap
    text = _op_trap(None)  # type: ignore[arg-type]  # uses no layout field
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
            info.value, bytearray(), bytearray(), b"", binary).kind
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
