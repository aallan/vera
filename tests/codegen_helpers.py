"""Shared helpers for the test_codegen_*.py suite (split from tests/test_codegen.py, #419).

The established pattern:
    _compile(source) -> CompileResult
    _compile_ok(source) -> CompileResult (assert no errors)
    _run(source, fn, args) -> int result
    _run_io(source, fn, args) -> captured stdout string
    _run_trap(source, fn, args) -> assert WASM trap
(plus _run_float / _run_refine_trap / _run_state / _compile_with_generator
and the WAT/GC assertion helpers further down).
"""
from __future__ import annotations

import re
import wasmtime
from collections.abc import Callable
from pathlib import Path

import pytest

from vera.codegen import (
    CodeGenerator,
    compile,
    CompileResult,
    execute,
    ExecuteResult,
)
from vera.codegen.api import WasmTrapError
from vera.parser import parse_file
from vera.transform import transform


# =====================================================================
# Helpers
# =====================================================================


_CALL_INDIRECT_RE = re.compile(r"(?m)^\s*call_indirect\b")
_TABLE_DECL_RE = re.compile(r"(?m)^\s*\(table\b")


def _assert_no_orphan_call_indirect(wat: str) -> None:
    """#1185: every emitted ``call_indirect`` has a table to dispatch on.

    A ``call_indirect`` names no symbol, so the #1100 caller-drop pass
    (which scans the WAT for ``call $f``) cannot see it.  When an [E602]
    skip swallowed a module's only closure the lift rolled back, module
    assembly suppressed the ``(table)``/``(elem)`` sections, and any
    surviving ``apply_fn`` / ``array_map`` carrier kept an indirect call
    into a table that no longer existed — an uninstantiable module
    emitted with no diagnostics, which raised a raw ``WasmtimeError:
    unknown table 0`` the moment ANY export ran.

    This is a *differential* over the two sides that must agree (the
    instruction stream and the table section), not a unit assertion on
    either — a green codegen suite hid the desync between them for the
    whole #1100 cycle.  Asserted on every ``_compile`` here, and on the
    local ``_compile`` in ``tests/test_codegen_closures.py``, so the
    property holds across the codegen suite rather than only in the
    #1185 fixtures.

    Only this direction is universally true.  The converse — a table with
    no indirect call — is inert (the module loads and runs; the table is
    simply unreferenced) and happens legitimately whenever a lift
    succeeds but the sole carrier is dropped for an unrelated reason, as
    in the [E616] fixture in ``tests/test_codegen_interpolation.py``.
    The #1185 fixtures pin the full biconditional via
    ``_assert_call_indirect_iff_table``, where both sides are meaningful.
    """
    if _CALL_INDIRECT_RE.search(wat) and not _TABLE_DECL_RE.search(wat):
        raise AssertionError(
            "#1185: emitted WAT contains `call_indirect` but declares no "
            "function table — the module cannot be instantiated, and the "
            "user gets a raw `unknown table 0` from wasmtime instead of a "
            "located diagnostic.  The carrier must be dropped instead."
        )


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


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    # Write to a temp source and parse.  delete=False + close-then-read
    # is the Windows-safe pattern (an open NamedTemporaryFile can't be
    # reopened there); the try/finally encloses everything from creation,
    # so the temp file is unlinked even when the write itself raises.
    import tempfile

    f = tempfile.NamedTemporaryFile(  # noqa: SIM115 — Windows fixture; closed + unlinked below
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    )
    try:
        with f:
            f.write(source)
        tree = parse_file(f.name)
        ast = transform(tree)
        result = compile(ast, source=source, file=f.name)
        _assert_no_orphan_call_indirect(result.wat)
        return result
    finally:
        Path(f.name).unlink(missing_ok=True)


def _compile_ok(source: str) -> CompileResult:
    """Compile and assert no errors."""
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected errors: {errors}"
    return result


def _compile_example(name: str) -> CompileResult:
    """Compile a .vera file from examples/ by name, mirroring the real
    file-based pipeline (read_text, parse_file, transform, compile)."""
    path = Path(__file__).parent.parent / "examples" / name
    source = path.read_text(encoding="utf-8")
    tree = parse_file(str(path))
    program = transform(tree)
    return compile(program, source=source, file=str(path))


def _run(source: str, fn: str | None = None, args: list[int] | None = None) -> int:
    """Compile, execute, and return the integer result."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _run_float(
    source: str, fn: str | None = None, args: list[int | float] | None = None
) -> float:
    """Compile, execute, and return the float result."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
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
    exec_result = execute(result, fn_name=fn, args=args)
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
        execute(result, fn_name=fn, args=args)


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
        execute(result, fn_name=fn, args=args)


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
    return execute(result, fn_name=fn, args=args, initial_state=initial_state)


# =====================================================================
# 6e: Bump allocator infrastructure
# =====================================================================


def _compile_with_generator(source: str) -> tuple[CompileResult, CodeGenerator]:
    """Compile and return both result and CodeGenerator for metadata inspection."""
    import tempfile

    f = tempfile.NamedTemporaryFile(  # noqa: SIM115 — Windows fixture; closed + unlinked below
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    )
    try:
        with f:
            f.write(source)
        tree = parse_file(f.name)
        program = transform(tree)
        gen = CodeGenerator(source=source, file=f.name)
        result = gen.compile_program(program)
        return result, gen
    finally:
        Path(f.name).unlink(missing_ok=True)


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
# Post-#706 (bucket-as-truth): Map and Set hold no Python store at all
# — each op builds a fresh wrapper whose `bucket_ptr` (+8) owns the
# data, and transient wrappers + buckets are reclaimed by ordinary
# mark-sweep.  `ExecuteResult.peak_heap_bytes` (the exported `$heap_ptr`
# high-water mark) is the leak signal: a working reclaimer keeps it
# ~O(N) across an insert chain; a leak grows it ~O(N^2).  Decimal alone
# still uses a Python store, so `ExecuteResult.host_store_sizes` keeps
# reporting its post-execution population.
# =====================================================================


def _assert_chain_reclaims(
    chain: Callable[[int], str],  # builds the chain source for a given size
    small_n: int,
    large_n: int,
    small_val: int,
    large_val: int,
    ratio: int = 30,
) -> None:
    """#706: run an insert/add chain at two sizes and assert the heap
    high-water mark grows ~O(N), proving transient wrappers + buckets
    are reclaimed by mark-sweep.

    With power-of-two bucket sizing a working reclaimer reuses freed
    same-size buckets, so 10x the inserts gives only ~6x the peak heap.
    A leak (transients never freed) grows ~O(N^2) → ~100x.  The bound
    sits well between the two.
    """
    small = execute(_compile_ok(chain(small_n)))
    large = execute(_compile_ok(chain(large_n)))
    assert small.value == small_val, (
        f"chain(n={small_n}) returned {small.value}, expected {small_val}"
    )
    assert large.value == large_val, (
        f"chain(n={large_n}) returned {large.value}, expected {large_val}"
    )
    assert large.peak_heap_bytes < small.peak_heap_bytes * ratio, (
        f"#706 reclamation regression: peak heap for n={large_n} "
        f"({large.peak_heap_bytes:,} bytes) exceeds {ratio}x the n="
        f"{small_n} peak ({small.peak_heap_bytes:,} bytes).  Transient "
        f"Map/Set wrappers + buckets are not being reclaimed — O(N^2) "
        f"high-water growth indicates a leak, vs the ~O(N) expected from "
        f"mark-sweep plus power-of-two bucket sizing."
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
        # Mirror execute()'s engine configuration (vera/codegen/api.py):
        # it enables wasm_exceptions, and the supported wasmtime range
        # includes versions where exceptions are not on by default — a
        # default engine would spuriously fail valid Exn modules here
        # (PR #1192 review).
        config = wasmtime.Config()
        config.wasm_exceptions = True
        engine = wasmtime.Engine(config)
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
