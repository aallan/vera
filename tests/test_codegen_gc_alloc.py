"""Tests for vera.codegen — gc_alloc (layout helpers, bump allocator, GC core, shadow-stack overflow, multi-page grow, worklist overflow).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re

from vera.codegen import (
    _align_up,
    _wasm_type_align,
    _wasm_type_size,
)

from tests.codegen_helpers import (
    _compile_ok,
    _run,
    _run_io,
    _run_trap,
)


class TestLayoutHelpers:
    """Unit tests for ADT memory layout helper functions."""

    def test_align_up_already_aligned(self) -> None:
        assert _align_up(8, 8) == 8

    def test_align_up_needs_padding(self) -> None:
        assert _align_up(5, 8) == 8

    def test_align_up_zero(self) -> None:
        assert _align_up(0, 8) == 0

    def test_align_up_to_four(self) -> None:
        assert _align_up(5, 4) == 8

    def test_align_up_one(self) -> None:
        assert _align_up(1, 8) == 8

    def test_wasm_type_size_i32(self) -> None:
        assert _wasm_type_size("i32") == 4

    def test_wasm_type_size_i64(self) -> None:
        assert _wasm_type_size("i64") == 8

    def test_wasm_type_size_f64(self) -> None:
        assert _wasm_type_size("f64") == 8

    def test_wasm_type_align_i32(self) -> None:
        assert _wasm_type_align("i32") == 4

    def test_wasm_type_align_i64(self) -> None:
        assert _wasm_type_align("i64") == 8

    def test_wasm_type_align_f64(self) -> None:
        assert _wasm_type_align("f64") == 8


class TestHeapAllocation:
    """Test heap infrastructure emission in WAT output."""

    def test_heap_ptr_global_emitted(self) -> None:
        """When ADTs are declared, $heap_ptr global appears in WAT."""
        source = """\
private data Color { Red, Green, Blue }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "global $heap_ptr" in result.wat
        assert 'export "heap_ptr"' in result.wat

    def test_alloc_function_emitted(self) -> None:
        """When ADTs are declared, $alloc function appears in WAT."""
        source = """\
private data Color { Red, Green, Blue }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "func $alloc" in result.wat
        assert "global.get $heap_ptr" in result.wat
        assert "global.set $heap_ptr" in result.wat

    def test_no_alloc_without_adt(self) -> None:
        """Pure programs without ADTs should NOT emit allocator."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "heap_ptr" not in result.wat
        assert "$alloc" not in result.wat

    def test_heap_ptr_starts_after_strings(self) -> None:
        """Heap pointer initial value should be after string data + GC regions."""
        source = """\
private data Color { Red, Green, Blue }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello") }
"""
        result = _compile_ok(source)
        # "hello" is 5 bytes; GC adds 81920 (16K shadow stack + 64K
        # worklist after #348's quadrupling of the worklist), so
        # heap_ptr should start at 5 + 81920 = 81925.  Match the
        # declaration and its initializer in a single substring so a
        # stale `i32.const 81925` elsewhere in the WAT (e.g. a future
        # constant in $alloc that happens to land on the same value)
        # can't satisfy the assertion on its own.
        assert (
            '(global $heap_ptr (export "heap_ptr") (mut i32) (i32.const 81925))'
            in result.wat
        )

    def test_heap_ptr_zero_without_strings(self) -> None:
        """Without strings, heap starts at GC offset 81920 (16K stack + 64K worklist)."""
        source = """\
private data Flag { On, Off }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        # Combined declaration + initializer match (see
        # test_heap_ptr_starts_after_strings for the rationale).
        assert (
            '(global $heap_ptr (export "heap_ptr") (mut i32) (i32.const 81920))'
            in result.wat
        )

    def test_alloc_alignment_logic(self) -> None:
        """Alloc function contains 8-byte alignment rounding."""
        source = """\
private data Bit { Zero, One }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "i32.const 7" in result.wat
        assert "i32.const -8" in result.wat

    def test_memory_emitted_with_adt(self) -> None:
        """ADTs cause memory to be declared even without strings."""
        source = """\
private data Flag { On, Off }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "(memory" in result.wat


class TestGarbageCollection:
    """Test GC infrastructure emission and behavior."""

    def test_gc_globals_emitted(self) -> None:
        """Programs with ADTs emit GC globals: gc_sp, gc_stack_base, etc."""
        source = """\
private data Flag { On, Off }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "global $gc_sp" in result.wat
        assert "global $gc_stack_base" in result.wat
        assert "global $gc_heap_start" in result.wat
        assert "global $gc_free_head" in result.wat

    def test_gc_collect_emitted(self) -> None:
        """Programs with ADTs emit the $gc_collect function."""
        source = """\
private data Flag { On, Off }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "func $gc_collect" in result.wat

    def test_gc_no_overhead_without_alloc(self) -> None:
        """Pure programs without ADTs emit no GC infrastructure."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "gc_sp" not in result.wat
        assert "gc_collect" not in result.wat
        assert "gc_stack_base" not in result.wat
        assert "$alloc" not in result.wat

    def test_gc_shadow_push_after_constructor(self) -> None:
        """Constructor allocation is followed by shadow stack push."""
        source = """\
private data Box { MkBox(Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match MkBox(42) {
    MkBox(@Int) -> @Int.0
  }
}
"""
        result = _compile_ok(source)
        # Shadow stack push: global.get $gc_sp / local.get N / i32.store
        assert "global.get $gc_sp" in result.wat
        assert "global.set $gc_sp" in result.wat

    def test_gc_prologue_saves_gc_sp(self) -> None:
        """Functions that allocate save/restore $gc_sp."""
        source = """\
private data Box { MkBox(Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match MkBox(42) {
    MkBox(@Int) -> @Int.0
  }
}
"""
        result = _compile_ok(source)
        wat = result.wat
        # Prologue saves gc_sp
        assert "global.get $gc_sp" in wat
        # Epilogue restores gc_sp
        assert "global.set $gc_sp" in wat

    def test_gc_preserves_live_data(self) -> None:
        """ADT data survives allocation pressure — correct result after many allocs."""
        source = """\
private data Box { MkBox(Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box = MkBox(100);
  let @Box = MkBox(200);
  let @Box = MkBox(300);
  match @Box.0 {
    MkBox(@Int) -> @Int.0
  }
}
"""
        assert _run(source) == 300

    def test_gc_string_concat_pressure(self) -> None:
        """String concat exercises allocation and GC shadow stack."""
        source = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("hello world")
}
"""
        assert _run_io(source) == "hello world"

    def test_gc_adt_across_function_calls(self) -> None:
        """ADT values survive across function call boundaries."""
        source = """\
private data Pair { MkPair(Int, Int) }

public fn sum_pair(@Pair -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Pair.0 {
    MkPair(@Int, @Int) -> @Int.0 + @Int.1
  }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  sum_pair(MkPair(17, 25))
}
"""
        assert _run(source, fn="f") == 42

    def test_gc_nested_adt_construction(self) -> None:
        """Nested ADT construction — inner alloc must survive outer alloc."""
        source = """\
private data Box { MkBox(Int) }
private data Wrapper { Wrap(Box) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match Wrap(MkBox(99)) {
    Wrap(@Box) -> match @Box.0 {
      MkBox(@Int) -> @Int.0
    }
  }
}
"""
        assert _run(source) == 99

    def test_gc_recursive_adt(self) -> None:
        """Recursive ADT (list) survives GC — sum elements."""
        source = """\
private data List { Nil, Cons(Int, List) }

public fn sum(@List -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @List.0 {
    Nil -> 0,
    Cons(@Int, @List) -> @Int.0 + sum(@List.0)
  }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  sum(Cons(1, Cons(2, Cons(3, Nil))))
}
"""
        assert _run(source, fn="f") == 6

    def test_gc_closure_survives(self) -> None:
        """Closure allocation survives across apply_fn."""
        source = """\
type Fn1 = fn(Int -> Int) effects(pure);

public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Fn1 = fn(@Int -> @Int) effects(pure) { @Int.0 + 10 };
  apply_fn(@Fn1.0, 32)
}
"""
        assert _run(source, fn="f") == 42

    def test_gc_collect_bounds_check_against_heap_ptr(self) -> None:
        """Regression for #515: $gc_collect must bound the conservative
        scan against $heap_ptr.

        The conservative-GC worklist push in Phase 2 accepts a shadow
        stack value as a heap pointer based on three guards (in heap
        range, properly aligned, below $heap_ptr).  None of those
        guards prove the word at val-4 is an actual object header.  A
        non-pointer i32 in payload data (e.g. a bit-packed Nat row in
        Conway-style code) can satisfy all three, in which case the
        marker reads garbage as obj_size and walks $obj_ptr+scan_ptr
        past $heap_ptr, trapping at the linear-memory boundary inside
        $gc_collect itself.

        Two layers of defence are now emitted:
          - Layer 2 (early skip): before marking or scanning, verify
            obj_ptr + obj_size <= heap_ptr.
          - Layer 1 (per-iter): each scan-loop iteration also checks
            obj_ptr + scan_ptr + 4 <= heap_ptr before issuing the
            i32.load.

        This test asserts both bounds checks survive in the emitted
        WAT.  A behavioural reproducer for #515 is heavily layout-
        sensitive (string-pool offsets, allocation order); the
        structural assertion is the durable regression guard.

        The assertions look for the actual opcode pattern that
        implements each bound check, not just the marker comment.
        Otherwise a refactor that left the comment in place but
        deleted the underlying check would silently pass — the
        comment is a discoverability anchor, the opcodes are the
        contract.
        """
        source = """\
private data Box { MkBox(Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match MkBox(42) { MkBox(@Int) -> @Int.0 }
}
"""
        result = _compile_ok(source)
        wat = result.wat
        assert "func $gc_collect" in wat

        # Helper: extract the next N non-comment, non-blank tokens of
        # WAT after `marker_text`.  Comments start with `;;` (line) or
        # `(;` (block) — only line comments appear in the GC code.
        # Joining tokens with single spaces gives us a normalised
        # pattern that's stable against whitespace changes in the
        # emitter but fails fast if any opcode is missing or out of
        # order.
        def _opcodes_after(text: str, marker: str, n: int) -> str:
            i = text.find(marker)
            assert i >= 0, f"Marker {marker!r} not found in WAT"
            # The marker sits inside a `;;` comment — the rest of its
            # line is comment text, not WAT.  Advance to the start of
            # the line after the marker so we tokenise only emitted
            # opcodes, never comment prose.
            line_end = text.find("\n", i)
            tail = text[line_end + 1:] if line_end >= 0 else ""
            tokens: list[str] = []
            for raw_line in tail.splitlines():
                stripped = raw_line.strip()
                if not stripped or stripped.startswith(";;"):
                    continue
                # Strip trailing inline comments if any (defensive).
                code = stripped.split(";;", 1)[0].strip()
                if not code:
                    continue
                tokens.extend(code.split())
                if len(tokens) >= n:
                    break
            return " ".join(tokens[:n])

        # Layer 2: the bound-check pattern is —
        #   local.get $obj_ptr ; local.get $obj_size ; i32.add ;
        #   global.get $heap_ptr ; i32.gt_u ; if ; br $m_loop
        # which is 11 whitespace-split tokens (each `local.get $foo`
        # splits into two: opcode + identifier).
        layer2_expected = (
            "local.get $obj_ptr local.get $obj_size i32.add "
            "global.get $heap_ptr i32.gt_u if br $m_loop"
        )
        layer2 = _opcodes_after(
            wat, "Layer 2 (issue #515)", len(layer2_expected.split()),
        )
        assert layer2 == layer2_expected, (
            f"Layer 2 opcode pattern drifted: {layer2!r}"
        )

        # Layer 1: the per-iter check pattern is —
        #   local.get $obj_ptr ; local.get $scan_ptr ; i32.add ;
        #   i32.const 4 ; i32.add ; global.get $heap_ptr ;
        #   i32.gt_u ; br_if $sc_done
        # which is 13 whitespace-split tokens.  The `br_if` (no `if`
        # block) is the cheap variant — exits the surrounding
        # `block $sc_done` directly without an if/end pair.
        layer1_expected = (
            "local.get $obj_ptr local.get $scan_ptr i32.add "
            "i32.const 4 i32.add global.get $heap_ptr "
            "i32.gt_u br_if $sc_done"
        )
        layer1 = _opcodes_after(
            wat, "Layer 1 (issue #515)", len(layer1_expected.split()),
        )
        assert layer1 == layer1_expected, (
            f"Layer 1 opcode pattern drifted: {layer1!r}"
        )


class TestGCShadowStackOverflow:
    """Regression tests for #464: deep recursive array accumulation
    overflowing the GC shadow stack into the worklist region.

    With a 4K shadow stack, build_acc (2 Array<Bool> params + 1 array_append
    dst = 12 bytes/frame) overflows at ~341 frames.  The overflow corrupted
    the GC worklist, causing incorrect mark/sweep and silent data corruption
    in the first few array elements.

    Fixed by increasing the shadow stack to 16K and adding an overflow guard.
    """

    def test_deep_array_accumulation_bool(self) -> None:
        """450-deep recursion with Array<Bool> accumulator."""
        src = """
private fn build_acc(@Array<Bool>, @Array<Bool>, @Int -> @Array<Bool>)
  requires(@Int.0 >= 0)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  if @Int.0 <= 0 then { @Array<Bool>.0 }
  else {
    build_acc(
      @Array<Bool>.1,
      array_append(@Array<Bool>.0, false),
      @Int.0 - 1
    )
  }
}

private fn first_bool(@Array<Bool> -> @Int)
  requires(array_length(@Array<Bool>.0) > 0)
  ensures(true)
  effects(pure)
{
  if @Array<Bool>.0[0] then { 1 } else { 0 }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  first_bool(build_acc([false], [false, false, false], 450))
}
"""
        assert _run(src) == 0  # first element must be false

    def test_shadow_stack_overflow_traps(self) -> None:
        """Overflow guard traps instead of silently corrupting memory.

        Uses a NON-tail-recursive shape so each iteration stacks a
        WASM frame and a fresh window of shadow-stack roots.

        #549 made tail-recursive allocating functions safe (per-
        iteration `$gc_sp` restore before each `return_call` keeps
        shadow-stack usage flat regardless of iteration count).
        Pre-#549 this test used a tail-recursive form that would
        leak shadow-stack slots; post-#549 such a form runs cleanly
        forever and no longer exercises the overflow guard.

        To still exercise the guard, this test wraps the recursive
        call in `array_append`, which moves it OUT of tail position.
        The non-tail call stacks WASM frames, each frame's shadow-
        stack roots survive across iterations, and at sufficient
        depth the overflow guard trips.

        Two-step assertion:
        1. Structural — the WAT for `overflow` contains the shadow-
           stack-overflow guard sequence (`global.get $gc_sp;
           global.get $gc_stack_limit; i32.ge_u; if; unreachable;
           end`).  Without this, a regression that silently drops
           the guard could still pass `_run_trap` via an unrelated
           trap class (e.g. heap exhaustion at a different scale).
        2. Behavioural — `_run_trap` confirms the program actually
           traps at the chosen 2000-iteration depth.

        Iteration count calibration: the 16K shadow stack holds
        ~4096 pointer slots (4 bytes each).  Each `overflow` frame
        pushes 2 `@Array<Bool>` params (8 bytes) + 1 array_append
        tmp root (4 bytes) = 12 bytes/frame, so the guard trips at
        ~1,365 frames.  2000 chosen with ~1.5× safety margin so
        the trap fires reliably even if per-frame size shrinks by
        a slot in a future optimisation.
        """
        src = """
private fn overflow(@Array<Bool>, @Array<Bool>, @Int -> @Array<Bool>)
  requires(@Int.0 >= 0)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  if @Int.0 <= 0 then { @Array<Bool>.0 }
  else {
    -- Wrapping the recursive call in array_append puts it out of
    -- tail position, so the call site emits plain `call` (not
    -- `return_call`) and each iteration genuinely stacks a frame.
    array_append(
      overflow(
        @Array<Bool>.1,
        array_append(@Array<Bool>.0, false),
        @Int.0 - 1
      ),
      true
    )
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(overflow([false], [false], 2000))
}
"""
        # Structural check: the WAT for `overflow` must contain
        # the shadow-stack overflow guard.  The distinctive token
        # is `global.get $gc_stack_limit`, which is only used by
        # this guard in the entire emission surface.
        #
        # Boundary-safe extraction (\b after `$overflow`) so a
        # future symbol like `$overflow_helper` couldn't false-
        # match the function-start search.
        compiled = _compile_ok(src)
        overflow_match = re.search(r"\(func \$overflow\b", compiled.wat)
        assert overflow_match is not None, (
            "`$overflow` function not found in emitted WAT"
        )
        overflow_start = overflow_match.start()
        next_fn = re.search(
            r"\(func \$", compiled.wat[overflow_start + 1:]
        )
        overflow_end = (
            overflow_start + 1 + next_fn.start()
            if next_fn is not None
            else len(compiled.wat)
        )
        overflow_body = compiled.wat[overflow_start:overflow_end]
        # The guard sequence emitted by `gc_shadow_push` in
        # `vera/wasm/helpers.py` is:
        #     global.get $gc_sp
        #     global.get $gc_stack_limit
        #     i32.ge_u
        #     if
        #       unreachable
        #     end
        # Check the distinctive parts as a substring; whitespace
        # between lines may vary depending on emission context.
        assert "global.get $gc_stack_limit" in overflow_body, (
            f"Shadow-stack overflow guard missing from `$overflow` "
            f"body — codegen must emit `global.get $gc_stack_limit` "
            f"as part of every shadow-stack push.  Without the "
            f"guard, _run_trap below could still pass via an "
            f"unrelated trap class.  Body:\n{overflow_body[:2000]}"
        )
        # Behavioural check: the program actually traps.
        _run_trap(src)

    def test_deep_array_accumulation_preserves_length(self) -> None:
        """Verify array length is correct after deep single-param accumulation."""
        src = """
private fn build_acc(@Array<Bool>, @Int -> @Array<Bool>)
  requires(@Int.0 >= 0)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  if @Int.0 <= 0 then { @Array<Bool>.0 }
  else {
    build_acc(array_append(@Array<Bool>.0, false), @Int.0 - 1)
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(build_acc([], 500))
}
"""
        assert _run(src) == 500


# =====================================================================
# GC infrastructure: $alloc multi-page grow (#487) + worklist (#348)
# =====================================================================


class TestLargeAllocGrow487:
    """`#487`: `$alloc` grows by enough pages, not just 1.

    Pre-fix, when `heap_ptr + total > memory.size * 65536`, `$alloc`
    unconditionally called `memory.grow 1` regardless of how many
    pages were actually needed.  A single allocation request more
    than ~64 KB past the current memory boundary fell through to
    the bump-allocate and trapped on out-of-bounds memory access.

    Post-fix, `$alloc` computes
    `pages_needed = ceil(shortage / 65536)` and grows by that many
    pages in a single call, so allocations of any practical size
    succeed (subject to `memory.grow` returning a valid value).
    """

    def test_50k_int_array_alloc_succeeds(self) -> None:
        """`array_range(0, 50_000)` allocates ~400 KB; pre-fix trapped.

        Two arrays of 50 K i64s (~800 KB total).  The default initial
        memory is 1 page (64 KB); the second `array_range` would
        need to grow by ~7 pages but pre-fix only grew by 1 page
        and then bump-allocated past memory.size, causing a WASM
        OOB-memory-access trap.  Post-fix: the multi-page grow
        provides enough memory and the access at index 49999 reads
        cleanly.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 50000);
  let @Array<Int> = array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 + 1 });
  @Array<Int>.0[49999]
}
"""
        # array_range(0, 50000) = [0..49999]; mapped to [+1] = [1..50000];
        # index 49999 = 50000.
        assert _run(src) == 50000

    def test_single_large_alloc_smaller_than_old_limit(self) -> None:
        """Smaller allocations (well within 1 page) must keep working.

        Regression pin: the multi-page grow math for the small case
        (shortage ≤ 65535 → pages_needed = 1) reduces to the same
        behaviour as the pre-fix single-page grow.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 1000);
  @Array<Int>.0[999]
}
"""
        assert _run(src) == 999

    def test_page_boundary_alloc_rounding(self) -> None:
        """Allocations that span the 64 KiB page boundary work cleanly.

        Pins the `pages_needed = (shortage + 65535) >> 16` ceiling
        math against off-by-one regressions at the 64 KiB boundary:

          - shortage = 65535 → 1 page  (just under)
          - shortage = 65536 → 1 page  (exactly fits)
          - shortage = 65537 → 2 pages (1 byte over → must round up)

        Each `array_range(0, N)` allocates `8 * N` payload bytes
        plus a small header.  The exact shortage at runtime depends
        on prior heap state, but the array sizes below straddle the
        single-page allocation boundary (8192 i64s = 65536 bytes ≈
        1 page).  If the rounding math regresses, one of these
        sizes will trap on out-of-bounds memory access at the index
        read.  Each test allocates fresh; we read the last element
        to force the access to actually land in the new memory.
        """
        # 8192 elements = 65536 bytes payload — exactly 1 page
        src_8192 = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 8192);
  @Array<Int>.0[8191]
}
"""
        assert _run(src_8192) == 8191

        # 8193 elements = 65544 bytes payload — 1 page + 8 bytes
        # (shortage just over 64 KiB, must round up to 2 pages)
        src_8193 = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 8193);
  @Array<Int>.0[8192]
}
"""
        assert _run(src_8193) == 8192

        # 16384 elements = 131072 bytes payload — exactly 2 pages
        src_16384 = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 16384);
  @Array<Int>.0[16383]
}
"""
        assert _run(src_16384) == 16383


class TestWorklistOverflow348:
    """`#348`: GC worklist overflow trap (was: silent use-after-free).

    The mark-phase worklist sits between the shadow stack and the
    heap.  Pre-fix: 16 KiB capacity (4 096 entries); when full, the
    push branches in Phase 2 (seed) and Phase 2b (mark scan) silently
    skipped — leaving reachable objects unmarked, which the sweep
    phase then freed as garbage (a real use-after-free hole for
    programs with object graphs holding more than ~4 K pointers
    reachable from a single root).

    Post-fix:
      - Worklist quadrupled to 64 KiB (16 384 entries).  Reasonable
        program shapes don't reach the cap.
      - Both push branches now `unreachable` on overflow rather than
        silently dropping.  Any residual overflow is a clean WASM
        trap, not silent corruption.

    Note: the obvious "wide-graph" runtime test (e.g. an
    `array_map`-built `Array<Box>` of 5 000+ elements) is blocked by
    a separate pre-existing shadow-stack-overflow issue inside
    `array_map`'s per-element allocation pattern, which trips at
    around 4 000 elements regardless of GC worklist size.  The
    wide-graph runtime regression is therefore covered by a
    moderate-size case (which exercises the mark loop without
    tripping the shadow-stack issue) plus structural pins on the
    WAT.
    """

    def test_moderate_graph_with_gc_pressure(self) -> None:
        """ADT graph + heap pressure exercises the post-fix mark loop.

        Builds a 1 000-element `Array<Box>` (well within the
        shadow-stack budget) and forces several `$gc_collect`
        cycles via additional allocations before reading.  The
        Box pointers in the array's payload are pushed onto the
        worklist during the mark phase — exercising the same code
        path that overflowed pre-fix on larger graphs.
        """
        src = """
private data Box { MkBox(Int) }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Box> = array_map(
    array_range(0, 1000),
    fn(@Int -> @Box) effects(pure) { MkBox(@Int.0) }
  );
  array_fold(
    @Array<Box>.0,
    0,
    fn(@Int, @Box -> @Int) effects(pure) {
      @Int.0 + match @Box.0 { MkBox(@Int) -> @Int.0 }
    }
  )
}
"""
        # 0+1+...+999 = 499_500
        assert _run(src) == 499_500

    def test_worklist_size_quadrupled_in_wat(self) -> None:
        """Structural pin: the GC region reflects the 64 KiB worklist.

        Pre-fix, `gc_heap_start = stack_base + 16 KiB stack + 16 KiB
        worklist = 32 768`.  Post-fix the worklist is 64 KiB so
        `gc_heap_start = 16 384 + 65 536 = 81 920`.  Pinning the
        constant against the WAT catches accidental size regressions.
        """
        source = """\
private data Box { MkBox(Int) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ match MkBox(42) { MkBox(@Int) -> @Int.0 } }
"""
        result = _compile_ok(source)
        # gc_stack_limit = 16384 (16 KiB shadow stack)
        # gc_heap_start  = 81920 (16 KiB stack + 64 KiB worklist)
        # #692: $gc_stack_limit is now exported so host walkers
        # can check shadow-stack overflow before pushing.
        assert (
            '(global $gc_stack_limit (export "gc_stack_limit") '
            'i32 (i32.const 16384))'
        ) in result.wat
        assert "(global $gc_heap_start i32 (i32.const 81920))" in result.wat

    def test_worklist_overflow_traps_in_wat(self) -> None:
        """Structural pin: both worklist push branches trap on overflow.

        Pre-fix, the seed (Phase 2) and mark-scan (Phase 2b) push
        branches both used `i32.lt_u` followed by a guarded push,
        silently dropping pushes when the worklist was full.
        Post-fix, both use `i32.ge_u` followed by `unreachable` —
        any overflow is a clean trap rather than silent corruption.
        """
        source = """\
private data Box { MkBox(Int) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ match MkBox(42) { MkBox(@Int) -> @Int.0 } }
"""
        result = _compile_ok(source)
        wat = result.wat
        # Extract the $gc_collect function body for inspection.
        gc_start = wat.index("(func $gc_collect")
        gc_end = wat.index("\n  (func ", gc_start + 1) if "\n  (func " in wat[gc_start + 1 :] else len(wat)
        gc_collect = wat[gc_start:gc_end]
        # Match the exact overflow-guard opcode sequence:
        #   local.get $wl_ptr
        #   local.get $wl_end
        #   i32.ge_u
        #   if
        #     unreachable
        # (with arbitrary indentation between lines).  Pre-fix the
        # corresponding sequence used `i32.lt_u` followed by a push,
        # so this regex would match zero times against a regressed
        # file even if `i32.ge_u` continued to appear elsewhere.
        # The two matches correspond to:
        #   - Phase 2 seed: scan_ptr loop, push of root pointers
        #   - Phase 2b mark-scan: per-payload-word push of children
        pattern = re.compile(
            r"local\.get \$wl_ptr\s*"
            r"local\.get \$wl_end\s*"
            r"i32\.ge_u\s*"
            r"if\s*"
            r"unreachable",
            re.MULTILINE,
        )
        matches = pattern.findall(gc_collect)
        assert len(matches) >= 2, (
            f"Expected ≥2 worklist-overflow guard sequences in $gc_collect "
            f"(Phase 2 seed + Phase 2b scan), found {len(matches)}.  "
            f"Pre-fix shape used `i32.lt_u` + push; post-fix uses "
            f"`i32.ge_u` + `unreachable` — a regression here would "
            f"mean one or both push branches reverted to silent-drop."
        )
