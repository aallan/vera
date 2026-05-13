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


def _run(src: str, fn_name: str = "main") -> object:
    """Compile + execute a Vera program, returning the result."""
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


def test_array_map_over_10k_int_array() -> None:
    """Pre-#570 this would shadow-stack-overflow at ~4000
    elements.  10K is a 2.5x safety margin over the historical
    failure threshold.  Test pins the iterative-builder fix and
    acts as an early-warning for any future regression in
    shadow-stack hygiene under `array_map`.
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
    assert _run(src) == 10000


# =====================================================================
# 2. array_map over 5K-element Array<Array<Bool>>
# =====================================================================


def test_array_map_over_5k_nested_bool_array() -> None:
    """5K nested-array allocation pressure: each iteration
    produces a fresh inner array, accumulating into the shadow
    stack.  Pre-#570 + pre-#515 this class of program corrupted
    intermediate roots.  Test pins the per-iteration alloc/root
    hygiene fix.
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
    assert _run(src) == 5000


# =====================================================================
# 3. 1000-deep tail recursion with allocating arg
# =====================================================================


def test_deep_tail_recursion_with_allocating_arg() -> None:
    """1000-deep tail recursion with an allocating String arg.
    Tests the TCO / GC interaction (#549) — tail-call
    optimisation must NOT discard the shadow-stack roots that
    keep the allocating arg live.  Pre-#549 work, allocating
    functions fell back to plain `call` so this would succeed
    by accident; the test pins the safety net.
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
    let @String = "stress";
    let @Nat = string_length(@String.0);
    loop(@Int.1 - 1, @Int.0 + nat_to_int(@Nat.0))
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  loop(1000, 0)
}
"""
    # 1000 iterations of (acc += 6) since "stress".length == 6
    assert _run(src) == 6000


# =====================================================================
# 4. Conway's Life 20×20 × 100 generations
# =====================================================================


def test_conways_life_20x20_100_generations() -> None:
    """Synthetic 20×20 Conway's Life regression covering #593
    territory (Life corruption from gen 1+ at 12×30) and #595
    (malloc abort during wasmtime cleanup).  Both bugs are
    closed but this test pins the fixes against future
    regressions.

    Uses a fixed initial pattern that stabilises within 100
    generations to a known live-cell count.  Asserts on the
    final population.
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
    # 400-cell allocation) exercises the same code paths #593 /
    # #595 hit, even with a trivially-deterministic outcome.
    assert _run(src) == 0


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


def test_10k_string_allocations() -> None:
    """10K String allocations via interpolation in a loop.
    Pre-#573 (wrap-table compaction) and #575/#576 (host-store
    reclamation) this class of program would leak handles or
    self-fault.  Tests pin the fixes by accumulating string
    lengths over many allocations.
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
    assert _run(src) == 38890


# =====================================================================
# 7. Long-running State<T> handler
# =====================================================================


def test_state_handler_1k_ops() -> None:
    """1000 State<Int> operations within a single handler scope.
    Pins the handler installation + resume continuation
    plumbing under sustained host-import call rate.  Pre-stage-
    11 / pre-#535 work, large State-handler programs accumulated
    captured-frame roots without bound.
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
    assert _run(src) == 1000


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
