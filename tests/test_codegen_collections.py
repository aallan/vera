"""Tests for vera.codegen — collections (Map and Set collections, wrapper-handle bit-31 tagging).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re

import pytest

from tests.codegen_helpers import (
    _IO_PRELUDE,
    _compile_ok,
    _run,
    _run_io,
)


# =====================================================================
# Map<K, V> collection (#62)
# =====================================================================

class TestMapCollection:
    """Map built-in operations: map_new, map_insert, map_get, map_contains,
    map_remove, map_size, map_keys, map_values."""

    def test_map_empty_size(self) -> None:
        """Empty map (via insert + remove) has size 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_remove(map_insert(map_new(), "x", 0), "x")) }
"""
        assert _run(source) == 0

    def test_map_insert_size(self) -> None:
        """Insert two entries, size is 2."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_insert(map_new(), "a", 1), "b", 2)) }
"""
        assert _run(source) == 2

    def test_map_contains_present(self) -> None:
        """map_contains returns true for inserted key."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if map_contains(map_insert(map_new(), "hello", 42), "hello") then { 1 } else { 0 } }
"""
        assert _run(source) == 1

    def test_map_contains_absent(self) -> None:
        """map_contains returns false for missing key."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if map_contains(map_insert(map_new(), "hello", 42), "world") then { 1 } else { 0 } }
"""
        assert _run(source) == 0

    def test_map_get_present(self) -> None:
        """map_get returns Some(value) for inserted key."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ option_unwrap_or(map_get(map_insert(map_new(), "hello", 42), "hello"), 0) }
"""
        assert _run(source) == 42

    def test_map_get_absent(self) -> None:
        """map_get returns None for missing key."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ option_unwrap_or(map_get(map_insert(map_new(), "hello", 42), "world"), -1) }
"""
        assert _run(source) == -1

    def test_map_remove(self) -> None:
        """map_remove removes the key."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_remove(map_insert(map_insert(map_new(), "a", 1), "b", 2), "a");
  map_size(@Map<String, Nat>.0)
}
"""
        assert _run(source) == 1

    def test_map_insert_overwrites(self) -> None:
        """Inserting same key twice overwrites the value."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_insert(map_insert(map_new(), "k", 10), "k", 20);
  option_unwrap_or(map_get(@Map<String, Nat>.0, "k"), 0)
}
"""
        assert _run(source) == 20

    def test_map_int_keys(self) -> None:
        """Map with Int keys works."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), 1, 100)) }
"""
        assert _run(source) == 1

    def test_map_keys_length(self) -> None:
        """map_keys returns an array with the right length."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_keys(map_insert(map_insert(map_new(), "a", 1), "b", 2))) }
"""
        assert _run(source) == 2

    def test_map_values_length(self) -> None:
        """map_values returns an array with the right length."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_values(map_insert(map_insert(map_new(), "a", 1), "b", 2))) }
"""
        assert _run(source) == 2

    def test_map_functional_semantics(self) -> None:
        """map_insert does not mutate the original map."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_insert(map_new(), "a", 1);
  let @Map<String, Nat> = map_insert(@Map<String, Nat>.0, "b", 2);
  map_size(@Map<String, Nat>.1)
}
"""
        assert _run(source) == 1  # original map still has size 1

    def test_map_size_verifier(self) -> None:
        """map_size >= 0 is verifiable (uninterpreted function)."""
        source = """
public fn main(-> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ map_size(map_insert(map_new(), "k", 1)) }
"""
        _compile_ok(source)

    def test_map_empty_keys(self) -> None:
        """map_keys on an empty map returns empty array."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_keys(map_remove(map_insert(map_new(), "x", 0), "x"))) }
"""
        assert _run(source) == 0

    def test_map_empty_values(self) -> None:
        """map_values on an empty map returns empty array."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_values(map_remove(map_insert(map_new(), "x", 0), "x"))) }
"""
        assert _run(source) == 0

    def test_map_get_after_remove(self) -> None:
        """map_get after map_remove returns None."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_remove(map_insert(map_new(), "k", 42), "k");
  option_unwrap_or(map_get(@Map<String, Nat>.0, "k"), -1)
}
"""
        assert _run(source) == -1

    def test_map_string_values(self) -> None:
        """Map with String values (pair-ABI value type)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), 1, "hello")) }
"""
        assert _run(source) == 1

    def test_map_get_string_value(self) -> None:
        """map_get with String values returns correct Option<String>."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<String> = map_get(map_insert(map_new(), 1, "hello"), 1);
  match @Option<String>.0 {
    None -> 0,
    Some(@String) -> string_length(@String.0)
  }
}
"""
        assert _run(source) == 5

    def test_map_bool_keys(self) -> None:
        """Map with Bool keys (i32 key type)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_insert(map_new(), true, 1), false, 2)) }
"""
        assert _run(source) == 2

    def test_map_contains_int_key(self) -> None:
        """map_contains with Int keys."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if map_contains(map_insert(map_new(), 42, "x"), 42) then { 1 } else { 0 } }
"""
        assert _run(source) == 1

    def test_map_remove_int_key(self) -> None:
        """map_remove with Int keys."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_remove(map_insert(map_new(), 42, "x"), 42)) }
"""
        assert _run(source) == 0

    def test_map_string_key_string_value(self) -> None:
        """Map<String, String> — both key and value are pair-ABI."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), "key", "value")) }
"""
        assert _run(source) == 1

    def test_map_keys_string(self) -> None:
        """map_keys with String keys returns correct array."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_keys(map_insert(map_new(), "only", 1))) }
"""
        assert _run(source) == 1

    def test_map_values_int(self) -> None:
        """map_values with Int values returns correct array."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_values(map_insert(map_new(), "k", 99))) }
"""
        assert _run(source) == 1


class TestSetCollection:
    """Set built-in operations: set_new, set_add, set_contains,
    set_remove, set_size, set_to_array."""

    def test_set_empty_size(self) -> None:
        """set_size(set_new()) returns 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_remove(set_add(set_new(), 1), 1)) }
"""
        assert _run(source) == 0

    def test_set_add_and_size(self) -> None:
        """Adding 2 elements gives size 2."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_add(set_new(), 1), 2)) }
"""
        assert _run(source) == 2

    def test_set_add_duplicate(self) -> None:
        """Adding same element twice gives size 1."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_add(set_new(), 42), 42)) }
"""
        assert _run(source) == 1

    def test_set_contains_present(self) -> None:
        """Returns 1 for present element."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if set_contains(set_add(set_new(), 7), 7) then { 1 } else { 0 } }
"""
        assert _run(source) == 1

    def test_set_contains_absent(self) -> None:
        """Returns 0 for absent element."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if set_contains(set_add(set_new(), 7), 99) then { 1 } else { 0 } }
"""
        assert _run(source) == 0

    def test_set_remove(self) -> None:
        """Removing element reduces size."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_add(set_new(), 1), 2);
  set_size(set_remove(@Set<Int>.0, 1))
}
"""
        assert _run(source) == 1

    def test_set_to_array_length(self) -> None:
        """set_to_array returns array with correct length."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(set_to_array(set_add(set_add(set_new(), 10), 20))) }
"""
        assert _run(source) == 2

    def test_set_string_elements(self) -> None:
        """Set<String> works."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_add(set_new(), "hello"), "world")) }
"""
        assert _run(source) == 2

    def test_set_int_elements(self) -> None:
        """Set<Int> works."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_new(), 99)) }
"""
        assert _run(source) == 1

    def test_set_add_immutability(self) -> None:
        """set_add returns a new set; the original is unchanged."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_new(), 1);
  let @Set<Int> = set_add(@Set<Int>.0, 2);
  set_size(@Set<Int>.1) + set_size(@Set<Int>.0)
}
"""
        # @Set<Int>.1 = original (size 1), @Set<Int>.0 = new (size 2)
        assert _run(source) == 3

    def test_set_remove_immutability(self) -> None:
        """set_remove returns a new set; the original is unchanged."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_add(set_new(), 1), 2);
  let @Set<Int> = set_remove(@Set<Int>.0, 1);
  set_size(@Set<Int>.1) + set_size(@Set<Int>.0)
}
"""
        # @Set<Int>.1 = original (size 2), @Set<Int>.0 = after remove (size 1)
        assert _run(source) == 3

    def test_set_remove_absent_element(self) -> None:
        """Removing a non-member doesn't change the set."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_new(), 42);
  set_size(set_remove(@Set<Int>.0, 999))
}
"""
        assert _run(source) == 1

    def test_set_empty_contains(self) -> None:
        """Contains on empty set returns false."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if set_contains(set_new(), 1) then { 1 } else { 0 }
}
"""
        assert _run(source) == 0

    def test_set_empty_to_array(self) -> None:
        """set_to_array on empty set returns empty array."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(set_to_array(set_new())) }
"""
        assert _run(source) == 0

    def test_set_bool_elements(self) -> None:
        """Set<Bool> exercises the 'b' (i32) type tag branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Bool> = set_add(set_add(set_new(), true), false);
  let @Int = set_size(@Set<Bool>.0);
  let @Bool = set_contains(@Set<Bool>.0, true);
  let @Set<Bool> = set_remove(@Set<Bool>.0, true);
  if @Bool.0 then { @Int.0 + set_size(@Set<Bool>.0) } else { -1 }
}
"""
        # size=2, contains=true, after remove size=1 → 2+1=3
        assert _run(source) == 3

    def test_set_float64_elements(self) -> None:
        """Set<Float64> exercises the 'f' (f64) type tag branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Float64> = set_add(set_add(set_new(), 1.5), 2.5);
  let @Int = set_size(@Set<Float64>.0);
  let @Bool = set_contains(@Set<Float64>.0, 1.5);
  let @Set<Float64> = set_remove(@Set<Float64>.0, 1.5);
  if @Bool.0 then { @Int.0 + set_size(@Set<Float64>.0) } else { -1 }
}
"""
        # size=2, contains=true, after remove size=1 → 2+1=3
        assert _run(source) == 3

    def test_set_to_array_int(self) -> None:
        """set_to_array with Int elements exercises the 'i' to_array branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_add(set_new(), 10), 20);
  array_length(set_to_array(@Set<Int>.0))
}
"""
        assert _run(source) == 2

    def test_set_string_contains_and_remove(self) -> None:
        """set_contains and set_remove with String elements."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<String> = set_add(set_add(set_new(), "a"), "b");
  let @Bool = set_contains(@Set<String>.0, "a");
  let @Set<String> = set_remove(@Set<String>.0, "a");
  if @Bool.0 then { set_size(@Set<String>.0) } else { -1 }
}
"""
        # contains "a" = true, after remove size = 1
        assert _run(source) == 1

    def test_set_to_array_string(self) -> None:
        """set_to_array with String elements exercises the 's' to_array branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<String> = set_add(set_add(set_new(), "a"), "b");
  array_length(set_to_array(@Set<String>.0))
}
"""
        assert _run(source) == 2

    def test_set_to_array_float64(self) -> None:
        """set_to_array with Float64 elements exercises the 'f' to_array branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Float64> = set_add(set_add(set_new(), 1.0), 2.0);
  array_length(set_to_array(@Set<Float64>.0))
}
"""
        assert _run(source) == 2

    def test_set_to_array_bool(self) -> None:
        """set_to_array with Bool elements exercises the 'b' to_array branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Bool> = set_add(set_add(set_new(), true), false);
  array_length(set_to_array(@Set<Bool>.0))
}
"""
        assert _run(source) == 2

    def test_set_remove_from_empty(self) -> None:
        """Removing from an empty set leaves size 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_remove(set_new(), 5)) }
"""
        assert _run(source) == 0

    def test_set_zero_value_element(self) -> None:
        """Zero (0) is a valid element, not confused with empty/absent."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_new(), 0);
  let @Bool = set_contains(@Set<Int>.0, 0);
  let @Int = set_size(@Set<Int>.0);
  let @Set<Int> = set_remove(@Set<Int>.0, 0);
  if @Bool.0 then { @Int.0 + set_size(@Set<Int>.0) } else { -1 }
}
"""
        # contains(0)=true, size=1, after remove size=0 → 1+0=1
        assert _run(source) == 1


# =====================================================================
# Wrapper-handle bit-31 tagging (#578)
# =====================================================================

class TestWrapperHandleTagging578:
    """Regression tests for #578: wrapper-handle field bit-31 tagging.

    Surfaced by CodeRabbit on PR #577 (#573 phase 1-3).  After
    #573, every `Map<K, V>` / `Set<T>` / `Decimal` value is a
    pointer to an 8-byte wrapper ADT on the GC heap: tag (i32) at
    offset 0, handle (i32) at offset 4.  Phase 2b of `$gc_collect`
    does a conservative word-by-word scan of every reachable
    object's payload, checking whether each i32 word looks like a
    heap pointer (in heap range, 8-byte aligned).

    Pre-#578 the raw host handle (a small positive integer) was
    stored at offset 4.  For typical programs the handle stays
    below `gc_heap_start` (~144 KiB above the data section, so
    roughly 144 KiB plus the string-pool size) so the heap-range check
    rejects it.  But for very-long-running programs allocating
    >100K host handles per `execute()`, the handle counter could
    exceed `gc_heap_start` and (with the right alignment) be
    falsely classified as a heap pointer — silently retaining an
    unrelated heap object.  A *retention* issue, not a correctness
    one (no use-after-free, no corruption), but unbounded
    retention for long sessions.

    Post-#578 the handle is stored as `handle | 0x80000000` so
    the in-heap field is always >= 2 GiB, structurally outside
    any heap-range check (the `$alloc` heap-ceiling guard
    enforces `heap_ptr < 0x80000000`).  The unwrap site ANDs
    with 0x7FFFFFFF to recover the raw handle.

    #706: `Map` / `Set` are now bucket-as-truth — their wrappers
    carry no host handle (the +4 field is vestigial), so they no
    longer wrap/unwrap.  `Decimal` keeps the value-typed Python
    store and is the remaining type exercising the bit-31 tagging,
    so these codegen tests use a Decimal program.
    """

    def test_wrap_emits_tag_or(self) -> None:
        """Wrap site emits `i32.const 0x80000000; i32.or; i32.store offset=4`.

        Pin the FULL 3-instruction wrap-site sequence — not just
        the `const`/`or` pair.  The header-mark path also has an
        `i32.or` and the heap-ceiling guard also has the constant;
        only the wrap site emits all three with `i32.store
        offset=4` (the wrapper-body handle field).  Including the
        store in the regex pins the SEMANTIC intent (tagging
        immediately precedes the field store) rather than the
        accidental fact that the const-or pair happens to be
        unique today.  Symmetric with `test_unwrap_emits_mask_and`
        which already pins the full 3-instruction unwrap sequence.
        """
        source = """\
public fn main(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{
  decimal_add(decimal_from_int(1), decimal_from_int(2))
}
"""
        result = _compile_ok(source)
        # `\s+` matches newlines + indentation between adjacent
        # WAT instructions.
        assert re.search(
            r"i32\.const 0x80000000\s+i32\.or\s+i32\.store offset=4",
            result.wat,
        ), (
            "Expected adjacent `i32.const 0x80000000; i32.or; "
            "i32.store offset=4` sequence (the wrap-site tag "
            "emission immediately followed by the wrapper-field "
            "store).  Without #578, the wrap site stores the raw "
            "handle and this sequence never appears."
        )

    def test_unwrap_emits_mask_and(self) -> None:
        """Unwrap site emits adjacent load-const-and sequence."""
        source = """\
public fn main(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{
  decimal_add(decimal_from_int(1), decimal_from_int(2))
}
"""
        result = _compile_ok(source)
        # Pin the exact 3-instruction sequence the unwrap helper
        # emits: load offset=4, const 0x7FFFFFFF, and.  Loose
        # substring `0x7FFFFFFF in wat` would survive a future
        # unrelated use of the mask constant; this won't.
        assert re.search(
            r"i32\.load\s+offset=4"
            r"\s+i32\.const 0x7FFFFFFF"
            r"\s+i32\.and",
            result.wat,
        ), (
            "Expected adjacent unwrap sequence "
            "`i32.load offset=4; i32.const 0x7FFFFFFF; i32.and`. "
            "Without #578, the unwrap reads the tagged value "
            "raw and `map_store` lookups would fail."
        )

    def test_alloc_emits_heap_ceiling_guard(self) -> None:
        """$alloc traps if heap_ptr + total would exceed 0x80000000.

        The structural counterpart to the wrap-site tag: the
        guard ensures `heap_ptr < 0x80000000` always, so tagged
        handles (>= 2 GiB) and heap pointers (< 2 GiB) are
        guaranteed disjoint.  Without this guard a 3+ GiB heap
        could produce real pointers in the tagged-handle range,
        reintroducing the spurious-retention bug.

        The guard is overflow-safe: it rejects allocations with
        `total >= 2 GiB` first, then checks
        `heap_ptr >= 0x80000000 - total` via SUBTRACTION.  An
        `i32.add` form could wrap on overflow (`heap_ptr =
        0xFFFFFFFF, total = 10` wraps to `0x09`, below the
        ceiling, silent bypass).  Upstream `memory.grow` makes
        the wraparound unreachable in practice but the algebraic
        gap is real.

        Pin both ordered sequences — not just constant presence.
        """
        source = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_insert(map_new(), 1, 100);
  option_unwrap_or(map_get(@Map<Int, Int>.0, 1), 0)
}
"""
        result = _compile_ok(source)
        # Locate $alloc via boundary-safe regex (not `find()`,
        # which could false-match an `$alloc_xxx` symbol).
        alloc_match = re.search(r"\(func \$alloc\b", result.wat)
        assert alloc_match is not None, (
            "`$alloc` function not found in WAT"
        )
        alloc_start = alloc_match.start()
        next_fn = re.search(
            r"\(func \$", result.wat[alloc_start + 1:],
        )
        alloc_end = (
            alloc_start + 1 + next_fn.start()
            if next_fn is not None
            else len(result.wat)
        )
        alloc_body = result.wat[alloc_start:alloc_end]
        # Step 1: total < 2 GiB precheck (rejects pathologically
        # large single allocations and prevents underflow in
        # step 2's subtraction).
        step1 = re.search(
            r"local\.get \$total"
            r"\s+i32\.const 0x80000000"
            r"\s+i32\.ge_u"
            r"\s+if"
            r"\s+unreachable"
            r"\s+end",
            alloc_body,
            re.DOTALL,
        )
        assert step1 is not None, (
            f"Heap-ceiling step 1 (total < 2 GiB precheck) not "
            f"found in $alloc body.  Without it, step 2's "
            f"`i32.sub` could underflow on a pathological total. "
            f"$alloc body:\n{alloc_body[:2000]}"
        )
        # Step 2: heap_ptr >= 0x80000000 - total → trap.  Pinned
        # AFTER step 1 by anchoring the search from step 1's end.
        rest = alloc_body[step1.end():]
        step2 = re.search(
            r"global\.get \$heap_ptr"
            r"\s+i32\.const 0x80000000"
            r"\s+local\.get \$total"
            r"\s+i32\.sub"
            r"\s+i32\.ge_u"
            r"\s+if"
            r"\s+unreachable"
            r"\s+end",
            rest,
            re.DOTALL,
        )
        assert step2 is not None, (
            f"Heap-ceiling step 2 (overflow-safe subtraction "
            f"check) not found after step 1 in $alloc body.  An "
            f"`i32.add` form would be vulnerable to wraparound "
            f"(heap_ptr=0xFFFFFFFF, total=10 wraps to 0x09, below "
            f"the ceiling, silent bypass).  Step 2 must use "
            f"`i32.sub` for overflow safety.  $alloc body:\n"
            f"{alloc_body[:2000]}"
        )

    def test_wrap_unwrap_round_trip_preserves_handle(self) -> None:
        """Behavioural: wrap-then-unwrap recovers the original handle.

        End-to-end smoke test that the tag+mask combination
        round-trips correctly for a real Map operation.  A bug
        in either direction (wrong mask, wrong constant, wrong
        order of operations) would produce a corrupted handle
        and the `map_get` lookup would either trap or return
        a wrong value.
        """
        source = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_insert(map_new(), 42, 12345);
  let @Map<Int, Int> = map_insert(@Map<Int, Int>.0, 100, 67890);
  let @Int = option_unwrap_or(map_get(@Map<Int, Int>.0, 42), -1);
  let @Int = option_unwrap_or(map_get(@Map<Int, Int>.0, 100), -1);
  @Int.0 + @Int.1
}
"""
        # Expected: 42 -> 12345, 100 -> 67890. Sum = 80235.
        # If the wrap/unwrap round-trip is broken, this either
        # traps on host-side `map_store[bad_handle]` lookup or
        # returns -1 + -1 = -2.
        assert _run(source) == 80235

    def test_html_round_trip_uses_host_side_mask(self) -> None:
        """Host-side reader applies the 0x7FFFFFFF mask.

        `vera/wasm/html_serde.py::read_html` reads
        `wrapper_ptr + 4` directly (via wasmtime memory access)
        rather than going through the WAT `_emit_unwrap_handle`
        helper.  Post-#578 that read sees the TAGGED value and
        must AND with 0x7FFFFFFF before looking up the host-side
        `map_store`.  Without the mask the lookup would miss and
        `html_to_string` would emit an element with empty
        attributes.

        Pin the EXACT serialized output (not just length) so a
        hypothetical bug that produced wrong content with the
        right length (e.g. `<p title="WRONG"></p>` — also 21
        chars) would still fail.  `IO.print` + `_run_io` captures
        the rendered output for direct string comparison.
        """
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<String, String> = map_insert(map_new(), "title", "hello");
  IO.print(html_to_string(HtmlElement("p", @Map<String, String>.0, [])))
}
"""
        # Exact rendered output.  Without the host-side mask the
        # attribute dict would be empty and the output would be
        # `<p></p>` instead.
        assert _run_io(source, fn="main") == '<p title="hello"></p>'

    def test_json_round_trip_uses_host_side_mask(self) -> None:
        """Host-side JSON reader applies the 0x7FFFFFFF mask.

        Sibling of `test_html_round_trip_uses_host_side_mask`.
        `vera/wasm/json_serde.py::read_json` reads
        `wrapper_ptr + 4` directly (via wasmtime memory access)
        rather than going through the WAT `_emit_unwrap_handle`
        helper.  Post-#578 that read sees the TAGGED value and
        must AND with 0x7FFFFFFF before looking up the host-side
        `map_store`.  Without the mask the lookup would miss,
        `read_json` would fall through to the "unknown JObject
        handle" warning + empty-dict path, and `json_stringify`
        would emit `{}` instead of the object.

        Pin the EXACT serialized output (not just length) so a
        hypothetical bug that produced wrong content with the
        right length (e.g. `{"name": "BB"}` — also 14 chars)
        would still fail.
        """
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Json = JObject(map_insert(map_new(), "name", JString("hi")));
  IO.print(json_stringify(@Json.0))
}
"""
        # Exact rendered output.  Python's json.dumps default
        # separators include a space after the colon, so the
        # form is `{"name": "hi"}` (NOT the compact `{"name":"hi"}`).
        # Without the host-side mask json_stringify would emit
        # `{}` instead.
        assert _run_io(source, fn="main") == '{"name": "hi"}'

    # --- Unit tests for the _validate_wrap_handle helper ---
    #
    # The validator is module-scope in `vera/codegen/api.py` so it
    # can be tested directly without standing up a wasmtime
    # instance.  `_wrap_handle` (nested inside `execute()`) calls
    # this helper.  These tests pin all 5 failure modes the
    # validator rejects.

    def test_validate_wrap_handle_accepts_valid_range(self) -> None:
        """[0, 0x80000000) is the accepted range — no raise."""
        from vera.runtime.heap import _validate_wrap_handle
        # Boundary lo, mid, boundary hi (last valid).
        for raw in (0, 1, 12345, 0x7FFFFFFE, 0x7FFFFFFF):
            _validate_wrap_handle(raw, kind=1, body_ptr=0x1000)

    def test_validate_wrap_handle_rejects_negative(self) -> None:
        """Negative ints have bit 31 set in two's complement."""
        from vera.runtime.heap import _validate_wrap_handle
        with pytest.raises(RuntimeError, match="#578.*outside the valid"):
            _validate_wrap_handle(-1, kind=1, body_ptr=0x1000)
        with pytest.raises(RuntimeError, match="#578"):
            _validate_wrap_handle(-12345, kind=2, body_ptr=0x2000)

    def test_validate_wrap_handle_rejects_at_2gb_boundary(self) -> None:
        """0x80000000 is the FIRST invalid value (range is half-open)."""
        from vera.runtime.heap import _validate_wrap_handle
        with pytest.raises(RuntimeError, match="0x80000000"):
            _validate_wrap_handle(0x80000000, kind=1, body_ptr=0x1000)

    def test_validate_wrap_handle_rejects_above_32bit(self) -> None:
        """Values >= 2^32 truncate on _write_i32 — must be caught here.

        The pre-tightening (round 1) bit-31-only check let these
        through: `0x100000001 & 0x80000000 == 0`, so the check
        passed, but `_write_i32` would truncate to `0x00000001`
        and the unwrap mask would return that — a silent wrong
        handle.
        """
        from vera.runtime.heap import _validate_wrap_handle
        with pytest.raises(RuntimeError, match="#578"):
            _validate_wrap_handle(0x100000000, kind=1, body_ptr=0x1000)
        with pytest.raises(RuntimeError, match="#578"):
            _validate_wrap_handle(0x100000001, kind=1, body_ptr=0x1000)

    def test_validate_wrap_handle_rejects_non_int(self) -> None:
        """Non-int sentinels surface here, not deeper in the stack.

        Without the type check, `None` / `"5"` / etc. would
        raise `TypeError` from the bitwise `&` operation in the
        old check, producing a less actionable error.
        """
        from vera.runtime.heap import _validate_wrap_handle
        for bad in (None, "5", 1.5, [1], {}):
            with pytest.raises(RuntimeError, match="#578"):
                _validate_wrap_handle(bad, kind=1, body_ptr=0x1000)

    def test_validate_wrap_handle_rejects_bool(self) -> None:
        """bool is rejected despite Python's bool-subclasses-int rule.

        `isinstance(True, int)` is `True` because `bool` is a
        subclass of `int` in Python.  An `isinstance`-only check
        would let `True` / `False` slip through and silently alias
        to handles 1 and 0 respectively — exactly the silent-
        corruption class #578 sought to eliminate.  The validator
        uses `type(raw_handle) is int` rather than `isinstance`,
        which rejects bool while still accepting plain int.
        """
        from vera.runtime.heap import _validate_wrap_handle
        with pytest.raises(RuntimeError, match="#578"):
            _validate_wrap_handle(True, kind=1, body_ptr=0x1000)
        with pytest.raises(RuntimeError, match="#578"):
            _validate_wrap_handle(False, kind=1, body_ptr=0x1000)
