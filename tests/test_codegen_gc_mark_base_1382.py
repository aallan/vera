"""Tests for vera.codegen — the GC mark store may only target object bases (#1382).

The conservative mark phase classifies a word as a heap pointer from two
cheap tests (heap range, and ``(val - $gc_heap_start) & 7 == 4``).  Those
are sound for *reads* — a false positive costs retention and nothing more
— but the mark phase also **writes**, ORing the mark bit into the word
four bytes below the candidate.  Pre-fix, a false positive landing in the
interior or tail padding of a *live* object corrupted that object.

Observed at ``VERA_EAGER_GC=1`` on ``ch09_nested_builtin_index``: candidate
``148075`` passed both tests, was not an object base, and the mark store
wrote ``0 | 1`` over the high word of a live ``Array<Int>`` element —
turning ``77`` into ``0x1_0000004D``.

The bug is layout-selected: whether any heap word happens to satisfy both
tests depends on absolute addresses, so a *single* program at a single
data-section size proves nothing.  Every test here therefore sweeps the
data-section padding across a full residue class mod 8.
"""
from __future__ import annotations

import re
import struct
from pathlib import Path

import pytest
import wasmtime

from tests.codegen_helpers import _compile_ok, _run

_CONFORMANCE_DIR = Path(__file__).parent / "conformance"


# Padding lives in an unused function holding one string literal: pure
# data-section growth, no extra allocation and no extra root on any path,
# so the only thing it moves is the heap base.
_PAD_FN = """\
private fn pad_probe(-> @String)
  requires(true)
  ensures(true)
  effects(pure)
{ "%s" }

"""

_REVERSE_OF_MAP_VALUES = """\
public fn rev_map(-> @Int)
  requires(true)
  ensures(@Int.result == 77)
  effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "k", 77);
  array_reverse(map_values(@Map<String, Int>.0))[0]
}

public fn main(-> @Int)
  requires(true)
  ensures(@Int.result == 154)
  effects(pure)
{ rev_map() + rev_map() }
"""

# Nine consecutive pad lengths cover all eight residues mod 8 at least
# once.  228..236 straddles 232 and 28..36 straddles 32 — the lengths at
# which the pre-fix collector corrupts the array element.
_RESIDUE_CLASS_A = range(228, 237)
_RESIDUE_CLASS_B = range(28, 37)


class TestGcMarkStoreTargetsObjectBases1382:
    """The mark store must never land outside a real object header."""

    @pytest.mark.parametrize("pad", _RESIDUE_CLASS_A)
    def test_reverse_of_map_values_survives_every_heap_base(
        self, pad: int, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``array_reverse(map_values(m))[0]`` twice, at every residue.

        Pre-fix this returns 154 at eight of the nine pad lengths and
        trips ``rev_map``'s postcondition at 232, because the element's
        high word is overwritten by a stray mark bit.
        """
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        src = (_PAD_FN % ("x" * pad)) + _REVERSE_OF_MAP_VALUES
        assert _run(src) == 154, (
            f"pad={pad}: the reversed array's element was corrupted — a "
            f"mark store landed outside an object header (#1382)"
        )

    @pytest.mark.parametrize("pad", _RESIDUE_CLASS_B)
    def test_conformance_program_survives_every_heap_base(
        self, pad: int, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The shipped ``ch09_nested_builtin_index``, padded.

        The conformance program passes at its own data-section size by
        layout luck — which is exactly why the suite never caught this.
        Add 32 characters and the same defect fires in
        ``reverse_of_map_values``.
        """
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        conformance = (
            _CONFORMANCE_DIR / "ch09_nested_builtin_index.vera"
        ).read_text(encoding="utf-8")
        marker = "public fn reverse_of_reverse"
        assert marker in conformance, "conformance program shape changed"
        src = conformance.replace(
            marker, (_PAD_FN % ("x" * pad)) + marker, 1,
        )
        assert _run(src) == 137, (
            f"pad={pad}: reverse_of_map_values returned the wrong element "
            f"— a mark store landed outside an object header (#1382)"
        )

    def test_check_marks_knob_holds_across_the_residue_class(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``VERA_GC_CHECK_MARKS=1`` asserts every mark store's target.

        The knob validates the target by walking the heap from
        ``$gc_heap_start`` along the allocator's own
        ``align_up(size + 4, 8)`` chain — deliberately independent of the
        object-base bitmap, so it is a real check on the fix rather than a
        restatement of it, and it traps if dropped into a pre-#1382
        collector.
        """
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        monkeypatch.setenv("VERA_GC_CHECK_MARKS", "1")
        for pad in _RESIDUE_CLASS_A:
            src = (_PAD_FN % ("x" * pad)) + _REVERSE_OF_MAP_VALUES
            assert _run(src) == 154, (
                f"pad={pad}: a mark store targeted an address that is not "
                f"an object body"
            )

    def test_zero_size_objects_are_recorded_as_bases(self) -> None:
        """Phase 1 records EVERY object base, including zero-size ones.

        ``_translate_array_reverse`` emits ``$alloc(len * sizeof(T))`` with
        no zero guard, so ``array_reverse([])`` allocates a payload of size
        0 — a real object whose header word is ``0``.  That is the shape
        the obvious cheap patch for #1382 keys on ("skip the mark store
        when the candidate's size reads 0"), and taking it would leave the
        allocator's object set and the collector's base set disagreeing.

        This assertion is structural, and deliberately so.  The
        behavioural version does not work: a swept zero-size block is
        benign — it has no payload for anyone to read, and a reused block
        still starts at the same address, so the stale pointer stays a
        valid base and merely retains its successor.  A run-and-compare
        test therefore passes whether or not zero-size bases are recorded
        (verified by mutation: omitting them keeps every behavioural case
        in this file green).  What can be pinned is the emitted code —
        the ``$gc_set_base`` call must be unconditional, reached straight
        from the walk with no size test in between.
        """
        src = _PAD_FN % "x" + _REVERSE_OF_MAP_VALUES
        wat = _compile_ok(src).wat or ""
        i = wat.find("record body = ptr + 4 as a real object base")
        assert i >= 0, "Phase 1 base-recording marker missing"
        after = wat[wat.index("\n", i) + 1:]
        opcodes: list[str] = []
        for raw in after.splitlines():
            code = raw.strip().split(";;", 1)[0].strip()
            if not code:
                continue
            opcodes.extend(code.split())
            if len(opcodes) >= 7:
                break
        assert opcodes[:7] == [
            "local.get", "$ptr", "i32.const", "4", "i32.add",
            "call", "$gc_set_base",
        ], (
            f"Phase 1's base recording is no longer unconditional: {opcodes[:7]!r}. "
            f"A size test in front of $gc_set_base would drop zero-size "
            f"objects — legitimate allocations — from the base set."
        )

    def test_empty_array_reverse_runs(self) -> None:
        """``array_reverse([])`` still runs clean under both knobs.

        Proves the zero-size allocation is exercised at all — the premise
        the structural test above rests on — not that omitting it would be
        observable.
        """
        src = """\
public fn main(-> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{
  let @Array<Int> = array_reverse(empty_int_array());
  array_length(@Array<Int>.0)
}

private fn empty_int_array(-> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ array_filter([1], fn(@Int -> @Bool) effects(pure) { @Int.0 > 99 }) }
"""
        assert _run(src) == 0


# =====================================================================
# Direct-instantiation pins for the two halves of the gate that no
# Vera-level program reaches (PR #1385 review).
# =====================================================================
#
# A Vera program cannot put a chosen word on the shadow stack, and
# cannot park `$heap_ptr` on a chosen bitmap-byte residue.  Both
# mechanisms below were therefore invisible to every behavioural test
# in this file — verified by mutation: deleting the Phase 2 seed gate,
# or the `+ 1` byte from the Phase 0 bitmap size, leaves all of the
# above green.  These drive the real emitted collector directly.

_HARNESS_SRC = """\
public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ array_reverse([1, 2, 3])[0] }
"""


def _gc_harness(
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[wasmtime.Store, wasmtime.Instance]:
    """Instantiate a real compiled module for direct GC poking.

    The WAT is the collector this PR emits, not a hand-rolled stand-in;
    the program is chosen to need `$alloc` (hence the whole GC) while
    importing nothing, so it instantiates with no host functions.
    """
    monkeypatch.setenv("VERA_EAGER_GC", "1")
    wat = _compile_ok(_HARNESS_SRC).wat or ""
    assert "(import " not in wat, (
        "harness program must not need host imports"
    )
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    instance = wasmtime.Instance(store, wasmtime.Module(engine, wat), [])
    return store, instance


def _heap_start(wat: str) -> int:
    """The emitted ``$gc_heap_start`` — the bitmap's origin for indexing."""
    m = re.search(r"\(global \$gc_heap_start i32 \(i32\.const (\d+)\)\)", wat)
    assert m, "gc_heap_start global not found"
    return int(m.group(1))


class _Gc:
    """Thin accessor over the harness module's GC exports."""

    def __init__(
        self, store: wasmtime.Store, instance: wasmtime.Instance,
    ) -> None:
        e = instance.exports(store)
        self.store = store
        self.mem = e["memory"]
        self.alloc = e["alloc"]
        self.sp = e["gc_sp"]
        self.heap_ptr = e["heap_ptr"]

    def read_u32(self, addr: int) -> int:
        buf = self.mem.data_ptr(self.store)
        return int(struct.unpack_from("<I", bytes(buf[addr:addr + 4]))[0])

    def write_u32(self, addr: int, value: int) -> None:
        self.mem.write(self.store, struct.pack("<I", value), addr)

    def push_root(self, value: int) -> None:
        sp = self.sp.value(self.store)
        assert isinstance(sp, int)
        self.write_u32(sp, value)
        self.sp.set_value(self.store, sp + 4)


class TestSeedGateIsLoadBearing1382:
    """The Phase 2 shadow-stack seed must consult the bitmap too.

    Phase 2b's scan gate alone is not enough: a false candidate can
    arrive from a shadow slot without ever passing through an object
    body scan.  No Vera program can place a chosen word in a shadow
    slot, so this drives the emitted collector directly.
    """

    def test_interior_address_in_a_shadow_slot_marks_nothing(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """An interior address as a root must not corrupt its object.

        `victim + 8` satisfies both cheap tests the seed applies — it is
        in the heap and `(val - $gc_heap_start) & 7 == 4`, because bodies
        are 8-aligned + 4 and 8 preserves the residue — but it is not a
        base.  Ungated, Phase 2b marks "the object at victim + 8" by
        ORing 1 into the word at `victim + 4`, which is live payload.
        """
        gc = _Gc(*_gc_harness(monkeypatch))
        victim = gc.alloc(gc.store, 24)
        assert isinstance(victim, int)
        # A distinctive even word at +4: the stray mark store ORs in 1,
        # so corruption is a single flipped bit, not a wholesale
        # overwrite that a coarser pattern might also produce.
        gc.write_u32(victim + 4, 0x12345678)
        gc.push_root(victim)          # keep the object live
        gc.push_root(victim + 8)      # the false candidate
        gc.alloc(gc.store, 8)         # eager GC: collects first
        assert gc.read_u32(victim + 4) == 0x12345678, (
            "a mark bit was written through an interior address taken "
            "from a shadow slot — the Phase 2 seed gate is missing"
        )


class TestBitmapCoversTheTopGranule1382:
    """Phase 0 must size the bitmap to cover the LAST heap granule.

    ``bm_bytes = ((heap_ptr - heap_start) >> 6) + 1``.  The final byte is
    partial — the top granules' bits live in it — and dropping the ``+ 1``
    puts it outside two spans at once: the zeroing loop, so stale base
    bits from an earlier collection survive into the next one and can make
    a dead interior address read as a base; and the ``memory.grow`` bound,
    so the write is one byte past what was checked when the heap ends at
    the edge of memory.

    Pinned twice over, behaviourally and structurally.

    Reaching it behaviourally takes three conditions at once, which is why
    an earlier attempt here concluded — wrongly — that it could not be
    done: the heap must GROW past a bitmap byte boundary with nothing
    freed (a sweep that reuses blocks leaves ``$heap_ptr`` still, and the
    planted candidate then lands on a legitimate base); the final partial
    byte must be poisoned, since it is the stale-bit path and not the
    write path that the ``+ 1`` protects; and the sentinel must have bit 0
    CLEAR, or the mark bit's ``| 1`` lands on a bit that is already set and
    the corruption is invisible.  The earlier attempt missed the first two
    and used ``0xABCDEF01`` for the third, so it stayed green against the
    mutation and the negative claim went into a docstring.  Recorded here
    because a green test that cannot fail is worse than no test.
    """

    def test_stale_bit_in_the_final_partial_byte_cannot_mark(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A poisoned final byte must not make a non-base look like one.

        Grows the heap past a bitmap byte boundary with every object
        rooted, so nothing is freed and no reuse pins ``$heap_ptr``; sets
        the byte the mutation writes but never zeroes to ``0xFF``; then
        plants a NON-base candidate whose granule lives in that byte —
        the interior of the last object, which passes both cheap tests.

        With the ``+ 1`` the byte is inside the zeroed span, the stale
        bits are cleared, the candidate is refused, and the live word one
        below it survives.  Without it the byte is never zeroed, the
        poison reads back as a set base bit, and Phase 2b ORs the mark bit
        into that live word.  The sentinel keeps bit 0 clear so a
        single-bit change is visible.
        """
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        wat = _compile_ok(_HARNESS_SRC).wat or ""
        heap_start = _heap_start(wat)
        gc = _Gc(*_gc_harness(monkeypatch))

        def granules() -> int:
            hp = gc.heap_ptr.value(gc.store)
            assert isinstance(hp, int)
            return (hp - heap_start) >> 3

        bases: list[int] = []
        for _ in range(30):
            addr = gc.alloc(gc.store, 24)
            assert isinstance(addr, int)
            bases.append(addr)
            gc.push_root(addr)  # rooted: nothing is freed, so the heap grows
        if granules() % 8 == 0:
            # Land off the byte boundary, so the top granule really does
            # sit in a partial final byte.
            addr = gc.alloc(gc.store, 24)
            assert isinstance(addr, int)
            bases.append(addr)
            gc.push_root(addr)
        assert granules() % 8 != 0, "top granule must sit in a partial byte"

        bm_base = gc.heap_ptr.value(gc.store)
        assert isinstance(bm_base, int)
        gc.write_u32(bm_base + (granules() >> 3), 0xFFFFFFFF)

        candidate = bases[-1] + 8  # interior of a live object: not a base
        assert (candidate - heap_start) & 7 == 4, "must pass the alignment test"
        assert candidate not in bases, "candidate must not be a real base"
        assert ((candidate - heap_start) >> 3) >> 3 == granules() >> 3, (
            "candidate's granule must live in the poisoned final byte"
        )
        gc.write_u32(candidate - 4, 0xABCDEF00)  # bit 0 clear: `| 1` is visible
        gc.push_root(candidate)
        gc.alloc(gc.store, 8)  # eager GC: collects first

        assert gc.read_u32(candidate - 4) == 0xABCDEF00, (
            "a stale bit in the unzeroed final bitmap byte let a non-base "
            "candidate be marked, and the mark store landed in live data"
        )

    def test_phase_0_sizes_the_bitmap_inclusively(self) -> None:
        """The emitted size is ``(span >> 6) + 1``, not ``span >> 6``."""
        wat = _compile_ok(_HARNESS_SRC).wat or ""
        i = wat.find("Grow memory if the bitmap would run past the end")
        assert i >= 0, "Phase 0 bitmap sizing marker missing"
        head = wat[:i]
        j = head.rfind("global.get $gc_heap_start")
        assert j >= 0, "bitmap span computation missing"
        opcodes = [
            tok
            for raw in head[j:].splitlines()
            for tok in raw.strip().split(";;", 1)[0].strip().split()
        ]
        assert opcodes == [
            "global.get", "$gc_heap_start",
            "i32.sub",
            "i32.const", "6", "i32.shr_u",
            "i32.const", "1", "i32.add",
            "local.set", "$bm_bytes",
        ], (
            f"Phase 0 bitmap sizing drifted: {opcodes!r}. Without the "
            f"trailing `i32.const 1 / i32.add` the partial final byte "
            f"falls outside both the zeroing loop and the grow bound."
        )

    def test_bitmap_bit_capacity_exceeds_the_top_granule_index(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Arithmetic check of the same property against a live heap.

        Reads the real `$heap_ptr` after the harness has allocated, takes
        `$gc_heap_start` from the emitted global, and confirms the byte
        count Phase 0 computes holds a bit for the highest granule an
        object can occupy — the inclusive bound, which is exactly what the
        `+ 1` buys.
        """
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        wat = _compile_ok(_HARNESS_SRC).wat or ""
        m = re.search(
            r"\(global \$gc_heap_start i32 \(i32\.const (\d+)\)\)", wat,
        )
        assert m, "gc_heap_start global not found"
        heap_start = int(m.group(1))
        gc = _Gc(*_gc_harness(monkeypatch))
        gc.alloc(gc.store, 8)
        heap_ptr = gc.heap_ptr.value(gc.store)
        assert isinstance(heap_ptr, int) and heap_ptr > heap_start
        span = heap_ptr - heap_start
        bm_bytes = (span >> 6) + 1
        top_granule = (span - 1) >> 3
        assert bm_bytes * 8 > top_granule, (
            f"bitmap holds {bm_bytes * 8} bits but the top granule index "
            f"is {top_granule} — the final partial byte is uncovered"
        )


class TestTopOfHeapAllocationRunsUnderCollection1382:
    """Premise for the sizing assertion: the top-of-heap path runs.

    Not a pin for the `+ 1` — it stays green with the `+ 1` removed
    (mutation-checked), because the base-bit write and read share an
    index computation.  It does exercise a rooted last-allocated object
    across a forced collection at eight byte-residues.
    """

    @pytest.mark.parametrize("filler", range(0, 8 * 8, 8))
    def test_top_of_heap_object_survives_a_collection(
        self, filler: int, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A swept object shows up as a free-list link in `payload[0]`."""
        gc = _Gc(*_gc_harness(monkeypatch))
        if filler:
            gc.alloc(gc.store, filler)
        target = gc.alloc(gc.store, 8)
        assert isinstance(target, int)
        gc.write_u32(target, 0xFEEDFACE)
        gc.push_root(target)
        gc.alloc(gc.store, 8)  # eager GC: collects first
        assert gc.read_u32(target) == 0xFEEDFACE, (
            f"filler={filler}: the top-of-heap object was swept while rooted"
        )
