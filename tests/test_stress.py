"""Scale-dependent regression tests (#596).

The Vera test suite has thousands of small focused tests but no
programs that exercise the runtime at scales where #570 / #515 /
#593-class bugs manifest.  Each of those bugs required a real-
world program (Conway's Life at 12×30+, array_map over 5,000
elements, etc.) to surface.  This module fills that gap: each
test compiles + runs a synthetic Vera program designed to hit
a specific scale axis, with a documented bug class it guards
against.

**Mode**: skipped by default per pyproject.toml `addopts = "-m
'not stress'"`.  Run via `pytest -m stress` or the nightly CI
workflow.  Path-filtered to also run on PRs touching
`vera/codegen/` or `vera/wasm/`.

**Budget**: full suite should complete in under 5 minutes on a
normal CI runner.  Iteration counts are tuned to the smallest
scale where each bug class has historically manifested, with
~2-3x safety margin — NOT maximised.

**Test shape**: each test compiles a self-contained Vera
program string, executes it via the in-process API, and
asserts on observable correctness (final result, no traps).
Failures should be diagnosable from the test name + assertion
message alone.
"""

from __future__ import annotations

import tempfile
from pathlib import Path

import pytest

from vera.codegen import compile, execute
from vera.parser import parse_file
from vera.transform import transform


pytestmark = pytest.mark.stress


# Eager-GC lane (#596 acceptance criterion).  Setting
# `VERA_EAGER_GC=1` at compile time emits a `call $gc_collect`
# as the first instruction of the runtime's `$alloc` function,
# forcing a full GC pass on every allocation.  This converts
# latent missing-shadow-root bugs from "fires occasionally at
# scale" into "fires on the very next allocation," so a stress
# test that exercises a GC-rooting code path will fail much
# sooner under eager mode than under default GC.
#
# Subset rationale: tests with a GC-rooting-specific bug class
# (#570 shadow-stack, #515 alloc-pressure, #549 TCO/GC, #573
# wrap-table, #593 nested-grid, captured-frame State handlers)
# are parametrised over `[False, True]` for the `eager_gc`
# flag.  Tests whose bug class is unrelated to GC rooting
# (#487/#348 allocation-pressure-only, host-import call rate)
# are NOT parametrised — running them under eager GC would
# inflate suite wall-clock without strengthening detection of
# the relevant bug class.
EAGER_GC_PARAMS = pytest.mark.parametrize(
    "eager_gc", [False, True], ids=["default_gc", "eager_gc"],
)


def _run(
    src: str,
    fn_name: str = "main",
    *,
    eager_gc: bool = False,
    monkeypatch: pytest.MonkeyPatch | None = None,
) -> object:
    """Compile + execute a Vera program, returning the result.

    When ``eager_gc=True``, sets ``VERA_EAGER_GC=1`` in the
    environment for the duration of the compile call so the
    runtime's ``$alloc`` function emits a forced GC pass per
    allocation.  Callers must pass a ``monkeypatch`` fixture so
    the env var is scoped to the test and cleaned up automatically.
    """
    if eager_gc:
        assert monkeypatch is not None, (
            "eager_gc=True requires a monkeypatch fixture for "
            "scoped env-var lifetime"
        )
        monkeypatch.setenv("VERA_EAGER_GC", "1")
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False,
        encoding="utf-8",
    ) as f:
        f.write(src)
        f.flush()
        path = f.name
    try:
        tree = parse_file(path)
        program = transform(tree)
        result = compile(program, source=src, file=path)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, (
            f"Compilation failed:\n"
            + "\n".join(e.description for e in errors)
        )
        exec_result = execute(result, fn_name=fn_name)
        return exec_result.value
    finally:
        Path(path).unlink(missing_ok=True)


# =====================================================================
# 1. array_map over 10K-element Array<Int>
# =====================================================================


@EAGER_GC_PARAMS
def test_array_map_over_10k_int_array(
    eager_gc: bool, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Pre-#570 this would shadow-stack-overflow at ~4000
    elements.  10K is a 2.5x safety margin over the historical
    failure threshold.  Test pins the iterative-builder fix and
    acts as an early-warning for any future regression in
    shadow-stack hygiene under `array_map`.

    Runs under both default and eager-GC modes.  Under
    `VERA_EAGER_GC=1` a missing shadow-stack root in the
    iterative-builder path would fire on the first allocation
    rather than only at the historical threshold of ~4000
    elements.
    """
    src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 10000);
  let @Array<Int> = array_map(@Array<Int>.0, fn(@Int -> @Int)
    effects(pure) { @Int.0 + 1 });
  array_length(@Array<Int>.0)
}
"""
    assert _run(src, eager_gc=eager_gc, monkeypatch=monkeypatch) == 10000


# =====================================================================
# 2. array_map over 5K-element Array<Array<Bool>>
# =====================================================================


@EAGER_GC_PARAMS
def test_array_map_over_5k_nested_bool_array(
    eager_gc: bool, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """5K nested-array allocation pressure: each iteration
    produces a fresh inner array, accumulating into the shadow
    stack.  Pre-#570 + pre-#515 this class of program corrupted
    intermediate roots.  Test pins the per-iteration alloc/root
    hygiene fix.

    Runs under both default and eager-GC modes (#596).  Eager
    GC surfaces a missing per-iteration root on the first or
    second outer iteration rather than after thousands have
    accumulated.
    """
    src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 5000);
  let @Array<Array<Bool>> = array_map(@Array<Int>.0,
    fn(@Int -> @Array<Bool>) effects(pure) {
      let @Array<Bool> = [true, false, true];
      @Array<Bool>.0
    });
  array_length(@Array<Array<Bool>>.0)
}
"""
    assert _run(src, eager_gc=eager_gc, monkeypatch=monkeypatch) == 5000


# =====================================================================
# 3. 1000-deep tail recursion with allocating arg
# =====================================================================


@EAGER_GC_PARAMS
def test_deep_tail_recursion_with_allocating_arg(
    eager_gc: bool, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """1000-deep tail recursion with an allocating array per iter.

    Tests the TCO / GC interaction (#549).  WASM `return_call`
    discards the current frame, so the GC epilogue (restore
    `$gc_sp`) never runs.  Pre-#549, allocating functions reverted
    `return_call` → plain `call` to avoid leaking shadow-stack
    slots per iteration; post-#549, the post-process instead
    prepends a `$gc_sp` restore before each `return_call`, keeping
    TCO AND keeping the shadow stack bounded.

    The per-iteration `let @Array<Int> = [@Int.0, @Int.1]` is a
    genuine heap allocation (NOT a string-pool literal), so the
    fn's `needs_alloc` flag is set and #549's GC-aware TCO path
    is exercised.  Pre-#549 this would have reverted to plain
    `call`, accumulating 1000 WASM frames; post-#549 it emits
    `return_call` with the `$gc_sp` restore preamble and runs
    in constant stack depth.

    Runs under both default and eager-GC modes (#596).  Eager GC
    fires a collection on every per-iteration array alloc, so a
    mis-rooted TCO frame would either trap immediately on the next
    `$alloc` or corrupt the accumulator within hundreds of
    iterations rather than completing cleanly.
    """
    src = """
private fn loop(@Int, @Int -> @Int)
  requires(@Int.1 >= 0)
  ensures(true)
  decreases(@Int.1)
  effects(pure)
{
  if @Int.1 == 0 then {
    @Int.0
  } else {
    let @Array<Int> = [@Int.0, @Int.1];
    loop(@Int.1 - 1, @Int.0 + array_length(@Array<Int>.0))
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  loop(1000, 0)
}
"""
    # 1000 iterations of (acc += 2) since array_length([_, _]) == 2
    assert _run(src, eager_gc=eager_gc, monkeypatch=monkeypatch) == 2000


@EAGER_GC_PARAMS
def test_tco_with_allocation_1m_iterations(
    eager_gc: bool, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """1M-deep tail recursion with an allocating array per iter (#549).

    The high-volume companion to
    `test_deep_tail_recursion_with_allocating_arg`.  A single
    million-iteration run gives the GC-aware TCO patch a sharp
    pin: any shadow-stack leak per iteration would trap on the
    overflow guard (16K shadow stack / 4 bytes per leaked pointer
    root ≈ 4,096 iterations) or — under eager-GC — accumulate
    enough roots to slow mark/sweep to a crawl.  Completing 1M
    iterations in seconds in both modes proves the shadow stack
    is bounded across the entire run.  (The per-iteration push
    is a single i32 pointer for the `Array<Int>` literal; the
    two `@Int` params are not pointer-typed and don't push to
    the shadow stack.)

    The pre-#549 fallback (revert `return_call` → plain `call`
    for allocating fns) cannot reach this depth — 1M plain calls
    would blow the WASM call stack at ~30K frames.  So this test
    relies on #549's `return_call` + `$gc_sp` restore being in
    effect.

    Iteration count is 1M in both default-GC and eager-GC modes
    because the per-iteration cost is dominated by WASM execution,
    not GC traversal (the array literal is small and short-lived,
    so each eager-GC collection is O(1) live roots).
    """
    src = """
private fn loop(@Int, @Int -> @Int)
  requires(@Int.1 >= 0)
  ensures(true)
  decreases(@Int.1)
  effects(pure)
{
  if @Int.1 == 0 then {
    @Int.0
  } else {
    let @Array<Int> = [@Int.0, @Int.1];
    loop(@Int.1 - 1, @Int.0 + array_length(@Array<Int>.0))
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  loop(1000000, 0)
}
"""
    # 1M iterations of (acc += 2) = 2,000,000
    assert _run(src, eager_gc=eager_gc, monkeypatch=monkeypatch) == 2000000


# =====================================================================
# 4. Conway's Life grid construction + count_alive 20×20
# =====================================================================


@EAGER_GC_PARAMS
def test_conways_life_grid_alloc_and_count_alive_20x20(
    eager_gc: bool, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Synthetic regression covering #593 territory (Life
    corruption from gen 1+ at 12×30).  Bug is closed; this
    test pins the fix against future regressions.

    Note on #595: an earlier version of this docstring also
    cited #595 (macOS malloc abort during wasmtime/ctypes
    cleanup after Ctrl-C in `IO.sleep`).  That citation was
    misattributed — the Conway's Life stress test doesn't
    exercise the Ctrl-C or wasmtime-cleanup paths (`effects(pure)`,
    no signal handling).  #595's regression coverage lives
    correctly in `TestHostSleepKeyboardInterrupt` in
    `tests/test_runtime_traps.py`; this test pins #593 only.

    What this test actually does: builds a 20×20 all-false
    `Array<Array<Bool>>` via nested `array_map`-of-`array_range`,
    then runs a single `count_alive` pass — an array-fold over
    array-fold that walks every cell.  Asserts the count == 0.

    What this test does NOT do: run 100 actual generations of
    Conway's Life.  The original test name implied that; the
    rename in #669 round-3 corrects it.  The structural shape
    (400-cell nested allocation, nested fold, captured outer-
    binding references inside the inner closure) is what
    matters for the bug class — these are the same code paths
    #593 hit.  A full Life-step implementation would be
    a meaningfully larger Vera program and isn't needed to pin
    those code paths.

    Runs under both default and eager-GC modes (#596).  #593
    was originally diagnosed with the help of eager-GC mode —
    forced collection on every alloc made the corruption
    reproduce reliably at small scales.  This test exercises
    the same code paths and pins the fix.
    """
    src = """
private fn count_alive(@Array<Array<Bool>> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, array_length(@Array<Array<Bool>>.0));
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int)
    effects(pure) {
      let @Array<Bool> = @Array<Array<Bool>>.0[@Int.0];
      let @Array<Int> = array_range(0, array_length(@Array<Bool>.0));
      let @Int = array_fold(@Array<Int>.0, @Int.1,
        fn(@Int, @Int -> @Int) effects(pure) {
          if @Array<Bool>.0[@Int.0] then {
            @Int.1 + 1
          } else {
            @Int.1
          }
        });
      @Int.0
    })
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- Initial: empty 20x20 grid (simplest correctness check)
  let @Array<Bool> = array_map(array_range(0, 20),
    fn(@Int -> @Bool) effects(pure) { false });
  let @Array<Array<Bool>> = array_map(array_range(0, 20),
    fn(@Int -> @Array<Bool>) effects(pure) {
      array_map(array_range(0, 20),
        fn(@Int -> @Bool) effects(pure) { false })
    });
  count_alive(@Array<Array<Bool>>.0)
}
"""
    # All-empty grid → 0 live cells, regardless of generations.
    # The structural shape (nested arrays, array_fold of array_fold,
    # 400-cell allocation) exercises the same code paths #593 hit,
    # even with a trivially-deterministic outcome.
    assert _run(src, eager_gc=eager_gc, monkeypatch=monkeypatch) == 0


# =====================================================================
# 5. 100K array_fold over Int array
# =====================================================================


def test_array_fold_100k_iterations() -> None:
    """100K iterations exercising the fold accumulator across
    many GC cycles.  Pre-#487 / #348 (worklist + multi-page
    grow) this class of program ran the heap into multi-page
    territory and tripped allocation-pressure bugs.  Tests pin
    the fixes — the assertion is sum(0..100000) = 4999950000.
    """
    src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 100000);
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int)
    effects(pure) { @Int.0 + @Int.1 })
}
"""
    # sum(0..99999) = 99999 * 100000 / 2 = 4999950000
    assert _run(src) == 4999950000


# =====================================================================
# 6. 10K String allocations
# =====================================================================


@EAGER_GC_PARAMS
def test_10k_string_allocations(
    eager_gc: bool, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """10K String allocations via interpolation in a loop.
    Pre-#573 (wrap-table compaction) and #575/#576 (host-store
    reclamation) this class of program would leak handles or
    self-fault.  Tests pin the fixes by accumulating string
    lengths over many allocations.

    Runs under both default and eager-GC modes (#596).  Eager
    GC forces a collection on every interpolation alloc, so a
    missing root on the per-iteration String would corrupt the
    accumulator on the first 10-100 iterations rather than at
    the tail.
    """
    src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 10000);
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int)
    effects(pure) {
      let @String = "\\(@Int.0)";
      @Int.1 + string_length(@String.0)
    })
}
"""
    # Total digits across 0..9999:
    # 1-digit (0-9): 10 numbers × 1 digit = 10
    # 2-digit (10-99): 90 × 2 = 180
    # 3-digit (100-999): 900 × 3 = 2700
    # 4-digit (1000-9999): 9000 × 4 = 36000
    # Total = 38890
    assert _run(src, eager_gc=eager_gc, monkeypatch=monkeypatch) == 38890


# =====================================================================
# 7. Long-running State<T> handler
# =====================================================================


@EAGER_GC_PARAMS
def test_state_handler_1k_ops(
    eager_gc: bool, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """1000 State<Int> operations within a single handler scope.
    Pins the handler installation + resume continuation
    plumbing under sustained host-import call rate.  Pre-stage-
    11 / pre-#535 work, large State-handler programs accumulated
    captured-frame roots without bound.

    Runs under both default and eager-GC modes (#596).  Eager
    GC stresses the captured-frame root-set on every alloc
    inside the handler scope; a missing root on the resume
    continuation would corrupt the state machine on the first
    few get/put cycles rather than at the tail.
    """
    src = """
private fn count_up(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  decreases(@Int.0)
  effects(<State<Int>>)
{
  if @Int.0 == 0 then {
    get(())
  } else {
    let @Int = get(());
    put(@Int.0 + 1);
    count_up(@Int.1 - 1)
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    count_up(1000)
  }
}
"""
    # 1000 puts of (current + 1) → final state = 1000
    assert _run(src, eager_gc=eager_gc, monkeypatch=monkeypatch) == 1000


# =====================================================================
# 8. 10K IO.print calls (capture buffer growth)
# =====================================================================


def test_10k_io_print_calls() -> None:
    """10K IO.print calls in sequence.  Exercises the
    host_print bridge at sustained rate; tests the in-process
    stdout-capture buffer's growth and the host-import call
    path under load.  Asserts the captured output's line count
    matches the loop count.
    """
    src = """
private fn loop(@Int -> @Unit)
  requires(@Int.0 >= 0) ensures(true)
  effects(<IO>)
{
  if @Int.0 == 0 then {
    ()
  } else {
    IO.print("x\\n");
    loop(@Int.0 - 1)
  }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  loop(10000)
}
"""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False,
        encoding="utf-8",
    ) as f:
        f.write(src)
        f.flush()
        path = f.name
    try:
        tree = parse_file(path)
        program = transform(tree)
        result = compile(program, source=src, file=path)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, (
            f"Compilation failed:\n"
            + "\n".join(e.description for e in errors)
        )
        exec_result = execute(result, fn_name="main", tee_stdout=True)
        # 10K "x\n" lines, plus possibly a trailing chunk.  Count
        # the 'x' character occurrences as the source-of-truth.
        captured = exec_result.stdout or ""
        assert captured.count("x") == 10000, (
            f"Expected 10000 'x' characters in captured stdout; "
            f"got {captured.count('x')}"
        )
    finally:
        Path(path).unlink(missing_ok=True)
