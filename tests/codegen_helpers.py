"""Shared helpers for the test_codegen_*.py suite (split from tests/test_codegen.py, #419).

The established pattern:
    _compile(source) -> CompileResult
    _compile_ok(source) -> CompileResult (assert no errors)
    _run(source, fn, args) -> int result
    _run_io(source, fn, args) -> captured stdout string
    _run_trap(source, fn, args) -> assert WASM trap
(plus _run_float / _run_refine_trap / _run_state / _compile_with_generator
and the WAT/GC assertion helpers further down).  The drivers compile through
``tests/pipeline.py``'s unchecked ``compile`` (``checked=False``: the parsed
program alone, no type check and none of the checker's tables, which is what
these suites were written against) and run through its ``run``.
"""
from __future__ import annotations

import re
import wasmtime
from collections.abc import Callable
from pathlib import Path

import pytest

from tests import pipeline
from tests.pipeline import CALL_INDIRECT_RE as _CALL_INDIRECT_RE
from tests.pipeline import TABLE_DECL_RE as _TABLE_DECL_RE
from vera.codegen import (
    CodeGenerator,
    CompileResult,
    ExecuteResult,
)
from vera.codegen.api import WasmTrapError


# =====================================================================
# Helpers
# =====================================================================


# Characters that may continue a WAT symbol name in emitted Vera output:
# identifiers, the `$` of a mangled clone suffix, and the `.` of a host
# import (`$vera.state_get_Int`).
_WAT_NAME_TAIL = r"(?![0-9A-Za-z_$.])"


def wat_calls(wat: str, symbol: str) -> bool:
    """Does *wat* contain a call to EXACTLY ``$symbol``?

    A plain ``"call $get" in wat`` is a prefix test, so it also accepts
    ``call $getx`` — and, worse, ``call $get$Int``, which is what a
    monomorphized clone of a same-named generic would emit.  In the
    positive direction that is a false PASS: the assertion says "the user's
    function was called" while the module called something else whose name
    merely starts the same way.  Anchoring on a name-character boundary
    makes the assertion mean what it reads as.

    Matches the tail-call spelling too: ``return_call $get`` contains
    ``call $get``, and both are calls to the same target, so a test that
    pins a dispatch target must not go red just because TCO fired.
    """
    return re.search(
        rf"call \${re.escape(symbol)}{_WAT_NAME_TAIL}", wat,
    ) is not None


def wat_fn_body(wat: str, name: str) -> str:
    """The emitted ``(func $name …)`` block, alone.

    :func:`wat_calls` over a whole module answers "does ANY body call this?",
    which is the wrong question whenever the property under test is
    per-function — a scope rule, most obviously (#1299): a module's own body
    may legitimately call its private ``$get`` in the same WAT where the
    importer's body must not.  A module-wide assertion cannot separate those
    two, and reads as if it had.

    Raises rather than returning ``""`` for an absent function: an empty
    string makes every ``not wat_calls(...)`` assertion pass vacuously, which
    is precisely the failure this helper exists to prevent.
    """
    match = re.search(
        rf"(?m)^\s*\(func \${re.escape(name)}{_WAT_NAME_TAIL}", wat,
    )
    if match is None:
        raise AssertionError(
            f"no `(func ${name} …)` in the emitted WAT — the function was "
            f"never emitted, so an assertion about its body would be vacuous"
        )
    rest = wat[match.end():]
    nxt = re.search(r"(?m)^\s*\(func \$", rest)
    return wat[match.start():match.end() + (nxt.start() if nxt else len(rest))]


def wat_fn_names(wat: str) -> list[str]:
    """Every function symbol the module DEFINES, sorted.

    Membership against this list is exact, where ``"(func $f" in wat`` is a
    prefix test that a longer mangled symbol satisfies — ``$gsib$Int`` is
    matched by a check for ``$gsib``, and ``$gen$Bool`` by one for ``$gen``,
    which is precisely how a monomorphized clone impersonates another.  It
    also makes a failure message useful: the assertion can print what WAS
    emitted instead of only what was missing.

    Imports are excluded — ``(import … (func $vera.x …))`` is not a
    definition, and a test asking "did we emit this?" never means the host's.
    """
    return sorted(
        m.group(1)
        for m in re.finditer(r"(?m)^\s*\(func \$([^\s()]+)", wat)
    )


def instantiate_with_trap_signal(
    store: wasmtime.Store, module: wasmtime.Module,
) -> wasmtime.Instance:
    """Instantiate a compiled module whose one host import is ``vera.trap``.

    An allocating module imports the trap signal whatever else it does,
    because its allocator names heap exhaustion through it (#1479) — so a
    harness that drives ``$alloc`` or ``$gc_collect`` directly links that
    one import and nothing else.  The stub records nothing: a signalled
    trap ends the call at the ``unreachable`` that follows it, so the test
    sees the trap either way.  Any OTHER import fails to link here, which
    keeps the harness's "no host imports" premise honest.
    """
    linker = wasmtime.Linker(store.engine)
    linker.define_func(
        "vera", "trap",
        wasmtime.FuncType(
            [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
             wasmtime.ValType.i32()], []),
        lambda _code, _ptr, _len: None,
    )
    return linker.instantiate(store, module)


def exceptions_engine() -> wasmtime.Engine:
    """A wasmtime engine configured the way ``execute()`` configures its own.

    ``vera/codegen/api.py`` enables ``wasm_exceptions`` explicitly, and the
    SUPPORTED wasmtime range includes versions where the proposal is not on by
    default (PR #1192 review).  A test that loads or validates emitted WAT has
    to configure it the same way, or on those versions it rejects every valid
    ``Exn`` module and is measuring the runner's wasmtime build rather than
    the compiler.

    That is a claim about the range, not about today's runner: on current
    wasmtime releases (measured at 48.0.0) exceptions default ON, so a bare
    ``wasmtime.Engine()`` currently loads the whole corpus.  What the proposal
    being off costs is measured directly instead — at wasmtime 48.0.0, 12 of the
    39 handler-bearing modules ``test_state_exn_registration`` validates fail to
    load with ``wasm_exceptions=False``, which is what a supported older runner
    sees.
    """
    config = wasmtime.Config()
    config.wasm_exceptions = True
    return wasmtime.Engine(config)


#: #1185: every emitted ``call_indirect`` has a table to dispatch on.  Asserted
#: on every module ``tests/pipeline.py``'s ``compile`` builds, and so on every
#: ``_compile`` here; ``pipeline.assert_no_orphan_call_indirect`` says why only
#: this direction is universal.
_assert_no_orphan_call_indirect = pipeline.assert_no_orphan_call_indirect


def _assert_call_indirect_iff_table(wat: str) -> None:
    """#1185, both directions — for fixtures where the table's presence is
    itself the thing under test (see ``_assert_no_orphan_call_indirect``
    for why only one direction is a universal invariant)."""
    has_indirect = _CALL_INDIRECT_RE.search(wat) is not None
    has_table = _TABLE_DECL_RE.search(wat) is not None
    assert has_indirect == has_table, (
        "#1185 invariant violated: emitted WAT has "
        f"call_indirect={has_indirect} but table={has_table}"
    )


#: The file a fixture's source text is compiled as.  Code generation labels
#: what it reports with it, as it labels a program compiled from a file.
_SOURCE_FILE = "fixture.vera"


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM, unchecked, as ``fixture.vera``.

    A parse or transform error is raised, and the #1185 invariant is
    asserted on the module, by ``tests/pipeline.py``'s ``compile``.
    """
    return pipeline.compile(source, file=_SOURCE_FILE, checked=False).result


def _compile_ok(source: str) -> CompileResult:
    """Compile and assert no errors."""
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected errors: {errors}"
    return result


def _compile_example(name: str) -> CompileResult:
    """Compile a .vera file from examples/ by name, unchecked, labelled with
    its path, as the file-based pipeline labels it."""
    path = Path(__file__).parent.parent / "examples" / name
    return pipeline.compile(path, checked=False).result


def _run(source: str, fn: str | None = None, args: list[int] | None = None) -> int:
    """Compile, execute, and return the integer result."""
    result = _compile_ok(source)
    exec_result = pipeline.run(
        result, fn, args, capture_stderr=False).execution
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _run_float(
    source: str, fn: str | None = None, args: list[int | float] | None = None
) -> float:
    """Compile, execute, and return the float result."""
    result = _compile_ok(source)
    exec_result = pipeline.run(
        result, fn, args, capture_stderr=False).execution
    assert exec_result.value is not None, "Expected a return value"
    assert isinstance(exec_result.value, float), (
        f"Expected float, got {type(exec_result.value).__name__}"
    )
    return exec_result.value


def _run_io(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> str:
    """Compile, execute, and return captured stdout."""
    result = _compile_ok(source)
    exec_result = pipeline.run(
        result, fn, args, capture_stderr=False).execution
    return exec_result.stdout


def _run_trap(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> None:
    """Compile, execute, and assert a WASM trap.

    ``execute()`` normalises every WASM trap to ``WasmTrapError`` (a
    ``RuntimeError`` subclass), so asserting the specific type rejects
    unrelated failures the old broad tuple would have accepted."""
    result = _compile_ok(source)
    with pytest.raises(WasmTrapError):
        _ = pipeline.run(result, fn, args, capture_stderr=False).execution


def _run_refine_trap(
    source: str, fn: str | None = None, args: list[object] | None = None
) -> None:
    """Compile, execute, and assert a *refinement-guard* trap specifically — a
    `$vera.contract_fail` ``RuntimeError`` carrying 'Refinement violation', not
    merely *some* runtime trap (which an unrelated fault — e.g. an
    out-of-bounds index — could also raise).  Use this for refinement
    runtime-guard tests so they prove the guard fired, not just that the
    program trapped for any reason."""
    result = _compile_ok(source)
    with pytest.raises(RuntimeError, match="Refinement violation"):
        _ = pipeline.run(result, fn, args, capture_stderr=False).execution


# =====================================================================
# The checked pipeline
# =====================================================================
# The helpers above compile unchecked.  A test about a code-generation rule
# that reads the checker's tables (the overflow and widening classifiers, the
# target-type widths, monomorphization) compiles through these instead, which
# check the program first and hand code generation the checker's tables, as
# `vera compile` and `vera run` do.  Their programs must type-check.


def _compile_checked(source: str) -> CompileResult:
    """Check *source* (which must pass), then compile it with the checker's
    tables, as ``fixture.vera``."""
    compiled = pipeline.compile(source, file=_SOURCE_FILE)
    assert compiled.checked is not None
    _ = compiled.parsed.program  # raises the parse or transform error, if any
    errors = compiled.checked.errors
    assert not errors, f"typecheck errors: {[d.description for d in errors]}"
    return compiled.result


def _compile_checked_ok(source: str) -> CompileResult:
    """:func:`_compile_checked`, asserting code generation reports no error."""
    result = _compile_checked(source)
    errs = [d for d in result.diagnostics if d.severity == "error"]
    assert not errs, f"codegen errors: {[d.description for d in errs]}"
    return result


def _run_checked(
    source: str, fn: str | None = None, args: list[int] | None = None,
) -> int:
    """Compile through the checked pipeline, execute, and return the result."""
    result = _compile_checked_ok(source)
    exec_result = pipeline.run(
        result, fn, args, capture_stderr=False).execution
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _run_checked_trap(source: str, fn: str, args: list[int]) -> None:
    """Compile through the checked pipeline, execute, and assert the call
    fails at the WASM level (a trap, or any other runtime fault)."""
    result = _compile_checked_ok(source)
    with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
        _ = pipeline.run(result, fn, args, capture_stderr=False).execution


# =====================================================================
# 6d: State<T> host imports
# =====================================================================

def _run_state(
    source: str,
    fn: str | None = None,
    args: list[int | float] | None = None,
    initial_state: dict[str, int | float] | None = None,
) -> ExecuteResult:
    """Compile, execute, and return the full ExecuteResult."""
    result = _compile_ok(source)
    return pipeline.run(
        result, fn, args, initial_state=initial_state, capture_stderr=False,
    ).execution


# =====================================================================
# 6e: Bump allocator infrastructure
# =====================================================================


def _compile_with_generator(source: str) -> tuple[CompileResult, CodeGenerator]:
    """Compile, unchecked, and return both result and CodeGenerator for
    metadata inspection."""
    compiled = pipeline.compile(source, file=_SOURCE_FILE, checked=False)
    result = compiled.result
    assert compiled.generator is not None
    return result, compiled.generator


_INLINE_BUILTIN_NAMES = (
    # #471 — character classifiers + first-byte case conversion
    "is_digit", "is_alpha", "is_alphanumeric", "is_whitespace",
    "is_upper", "is_lower", "char_to_upper", "char_to_lower",
    # #470 — string utilities
    "string_chars", "string_lines", "string_words",
    "string_reverse", "string_trim_start", "string_trim_end",
    "string_pad_start", "string_pad_end",
)


def _assert_no_host_imports_for_inline_builtins(wat: str) -> None:
    """Assert the compiled WAT has no host imports for the 16 inline
    built-ins added by #470 + #471.

    These functions are documented as being implemented entirely
    inline in WAT (no host imports — bit-identical Python/browser
    output by construction).  If a future refactor accidentally
    routes one through a host import, the import would appear as
    ``(import "vera" "<name>" ...)`` in the module's import section
    and this assertion would catch it.

    The check tolerates other unrelated imports (`IO.print`,
    `gc_collect` host helpers, etc.) — it scans only for our 16
    names.
    """
    for name in _INLINE_BUILTIN_NAMES:
        marker = f'(import "vera" "{name}"'
        assert marker not in wat, (
            f"Expected no host import for inline built-in {name!r}, "
            f"but found {marker!r} in the WAT.  This contradicts the "
            f"#470/#471 design contract."
        )


# =====================================================================
# Reclamation of transient Map / Set / Decimal values
# =====================================================================
# Historically (#573) every map_new / map_insert / map_remove
# allocated an entry in `_map_store` (in `vera/codegen/api.py`) that a
# Phase-2c `$gc_collect` walk evicted via `host_decref_handle` once the
# owning wrapper was unmarked.
#
# Since #706 Map and Set hold no Python store at all, and since #1676
# each is a trie in the module's heap: an update copies the branches on
# its key's path, and the transient copies are reclaimed by ordinary
# mark-sweep.  `ExecuteResult.peak_heap_bytes` (the exported `$heap_ptr`
# high-water mark) is the leak signal, read over a chain whose live set
# stays fixed (`_assert_chain_reclaims`).  Decimal alone still uses a
# Python store, so `ExecuteResult.host_store_sizes` keeps reporting its
# post-execution population.
# =====================================================================


def _assert_chain_reclaims(
    chain: Callable[[int], str],  # builds the chain source for a given size
    small_n: int,
    large_n: int,
    small_val: int,
    large_val: int,
    ratio: int = 40,
) -> None:
    """#706/#1676: run a chain at two sizes and assert the heap
    high-water mark grows far less than the number of steps, proving the
    transients each step leaves are reclaimed by mark-sweep.

    A chain keeps a fixed live set, so only reclamation bounds its peak.
    Over 1,000 and 100,000 steps of the Map and Set chains, a working
    collector grows the peak 13x and 14x (not 1x: the first-fit free list
    fragments, and #1718's stale tails keep some dead blocks marked); a
    collector that reclaims nothing grows it 73x and 85x.  A chain whose
    live set grows with it cannot separate the two, because a trie's
    insert leaves O(log N) bytes behind: the growing Map chain measured
    9.4x against 10.7x over a 10x step.  The bound sits between them.
    """
    small = pipeline.run(
        _compile_ok(chain(small_n)), capture_stderr=False).execution
    large = pipeline.run(
        _compile_ok(chain(large_n)), capture_stderr=False).execution
    assert small.value == small_val, (
        f"chain(n={small_n}) returned {small.value}, expected {small_val}"
    )
    assert large.value == large_val, (
        f"chain(n={large_n}) returned {large.value}, expected {large_val}"
    )
    assert large.peak_heap_bytes < small.peak_heap_bytes * ratio, (
        f"reclamation regression (#706/#1676): peak heap for n={large_n} "
        f"({large.peak_heap_bytes:,} bytes) exceeds {ratio}x the n="
        f"{small_n} peak ({small.peak_heap_bytes:,} bytes).  The chain's "
        f"live set is fixed, so a peak that grows with the steps means "
        f"its transient Map/Set blocks are not being reclaimed."
    )


def _assert_no_raw_wat_error(result: CompileResult) -> None:
    """The #1100 acceptance bar: no raw wasmtime/WAT text ever surfaces.

    #1185 hardened this: assembling is not the bar, *loading* is.  The
    original helper checked the diagnostics plus a non-empty
    ``wasm_bytes`` and never handed the module to wasmtime, so it passed
    on a module that assembled cleanly and then failed the instant any
    export was called — the orphan-``call_indirect`` case, where the
    ``(table)`` section was suppressed but a surviving carrier's indirect
    call was not.  Loading the module through the same
    ``wasmtime.Module`` construction ``execute()`` performs makes this
    helper catch that class itself: a raw ``WasmtimeError`` here is the
    exact error a user would have seen at ``vera run``.

    PR #1192 review round 4 hardened it once more: validation is not the
    bar either — element/data segments are bounds-checked only at
    INSTANTIATION (an ``(elem)`` targeting a slot past the table's
    minimum validates cleanly and traps at instantiate), and
    instantiation is the first thing ``execute()`` does.  The helper
    therefore also instantiates, resolving each host import with a
    zero-returning stub of the imported signature.  The stub linker is
    deliberate scope: ``execute()``'s production linker is ~200 lines of
    per-run host registration (output buffers, per-instance stores,
    conditional op families) that every ``execute()``-based test already
    exercises end to end; what THIS helper owns is module-shape failure,
    and the stubs let the real instantiation checks run without
    duplicating the runtime.
    """
    for d in result.diagnostics:
        assert "WAT compilation failed" not in d.description, (
            f"raw wasmtime error leaked to the user: {d.description}"
        )
        assert "unknown func" not in d.description, (
            f"raw WAT symbol dump leaked to the user: {d.description}"
        )
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"expected a warning-only drop, got errors: {errors}"
    assert result.wasm_bytes, "module must still assemble (minus the subgraph)"
    try:
        # Mirror execute()'s engine configuration (vera/codegen/api.py) —
        # see `exceptions_engine`, shared with every other test that hands
        # emitted WAT to wasmtime.
        engine = exceptions_engine()
        module = wasmtime.Module(engine, result.wat)
        linker = wasmtime.Linker(engine)
        store = wasmtime.Store(engine)
        zeros = {"i32": 0, "i64": 0, "f32": 0.0, "f64": 0.0}
        for imp in module.imports:
            ty = imp.type
            if not isinstance(ty, wasmtime.FuncType):  # pragma: no cover
                raise AssertionError(
                    f"unexpected non-function import "
                    f"{imp.module}.{imp.name}: {ty!r} — Vera codegen "
                    f"emits only function imports"
                )
            unsupported = [
                str(t) for t in ty.results if str(t) not in zeros
            ]
            if unsupported:  # pragma: no cover
                raise AssertionError(
                    f"unsupported import result type(s) "
                    f"{unsupported} on {imp.module}.{imp.name} — the "
                    f"zero-stub only covers numeric results; extend "
                    f"`zeros` if Vera codegen starts importing "
                    f"reference-typed results"
                )
            rvals = [zeros[str(t)] for t in ty.results]

            def _make_stub(rv: list[float | int]) -> object:
                def _stub(*_args: object) -> object:
                    if not rv:
                        return None
                    if len(rv) == 1:
                        return rv[0]
                    return rv
                return _stub

            linker.define_func(imp.module, imp.name, ty, _make_stub(rvals))
        linker.instantiate(store, module)
    except AssertionError:
        raise
    except Exception as exc:  # any load failure is the bug under test
        raise AssertionError(
            f"the emitted module does not load — a raw {type(exc).__name__} "
            f"is what the user gets on the next `vera run`, with no Vera "
            f"diagnostic to act on: {exc}"
        ) from exc
