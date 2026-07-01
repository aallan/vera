"""Tests for vera.codegen — gc_reclamation (transient Map/Set/Decimal reclamation, bucket occupancy, host-handle reclamation).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re

import pytest

from vera.codegen import (
    execute,
)

from tests.codegen_helpers import (
    _assert_chain_reclaims,
    _compile_ok,
    _run,
)


class TestBucketOccupancy706:
    """#706: the 20-byte bucket slot carries an explicit occupancy flag,
    so an empty-string key (``(ptr, len) == (0, 0)``) and an Int ``0``
    key are distinguished from a genuinely empty slot — closing the
    sentinel collision the old write-only mirror left latent (#707
    review).
    """

    def test_empty_string_key_round_trips(self) -> None:
        """A "" key is found, not mistaken for an empty slot."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "", 42);
  match map_get(@Map<String, Int>.0, "") {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == 42

    def test_empty_string_key_miss_returns_none(self) -> None:
        """A different key still misses when only "" is present."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "", 42);
  match map_get(@Map<String, Int>.0, "x") {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == -1

    def test_int_zero_key_round_trips(self) -> None:
        """An Int 0 key is found, not mistaken for an empty slot."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_insert(map_new(), 0, 99);
  match map_get(@Map<Int, Int>.0, 0) {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == 99

    def test_empty_string_element_in_set(self) -> None:
        """A "" element round-trips through Set (occupancy flag)."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<String> = set_add(set_new(), "");
  if set_contains(@Set<String>.0, "") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_empty_string_key_contains(self) -> None:
        """map_contains finds the "" key via the occupancy flag."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "", 42);
  if map_contains(@Map<String, Int>.0, "") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_empty_string_key_counts_in_size(self) -> None:
        """A "" key occupies a slot, so map_size counts it (not skipped
        as an empty slot)."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "", 42);
  nat_to_int(map_size(@Map<String, Int>.0))
}
"""
        assert _run(src) == 1

    def test_empty_string_key_removed(self) -> None:
        """map_remove("") clears the slot; a later lookup then misses,
        confirming the structural rebuild honours the sentinel key."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "", 42);
  let @Map<String, Int> = map_remove(@Map<String, Int>.0, "");
  match map_get(@Map<String, Int>.0, "") {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == -1


class TestSameValueZeroKeys743:
    """PR #743 (folded into #706): Float64 Map keys / Set elements compare
    under SameValueZero, so a NaN key/element round-trips (NaN equals NaN).

    Pre-existing: the CLI Python dict / the browser ``decodeColumn`` list
    use ``==`` / ``===``, which treat NaN as unequal to itself, so a NaN
    key could never be found, removed, or deduped.  ``0.0 / 0.0`` verifies
    and runs to NaN, so this is reachable.  Surfaced by the CodeRabbit
    review of #706.
    """

    def test_nan_map_key_found(self) -> None:
        """A NaN ``Float64`` map key is found by ``map_contains`` /
        ``map_get`` (pre-fix: not found → -1)."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = 0.0 / 0.0;
  let @Map<Float64, Int> = map_insert(map_new(), @Float64.0, 42);
  if map_contains(@Map<Float64, Int>.0, @Float64.0) then {
    match map_get(@Map<Float64, Int>.0, @Float64.0) {
      Some(@Int) -> @Int.0,
      None -> -2
    }
  } else { -1 }
}
"""
        assert _run(src) == 42

    def test_nan_map_key_dedups_and_removes(self) -> None:
        """Inserting a NaN key twice dedups to one entry; ``map_remove``
        then clears it (pre-fix: dedup and removal both failed)."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = 0.0 / 0.0;
  let @Map<Float64, Int> = map_insert(map_insert(map_new(), @Float64.0, 1), @Float64.0, 99);
  let @Int = nat_to_int(map_size(@Map<Float64, Int>.0));
  let @Map<Float64, Int> = map_remove(@Map<Float64, Int>.0, @Float64.0);
  let @Int = nat_to_int(map_size(@Map<Float64, Int>.0));
  @Int.1 * 100 + @Int.0
}
"""
        # size 1 after dedup, size 0 after remove → 100.
        assert _run(src) == 100

    def test_nan_set_element_round_trips(self) -> None:
        """A NaN ``Float64`` Set element dedups and is found by
        ``set_contains`` (pre-fix: duplicated and not found)."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = 0.0 / 0.0;
  let @Set<Float64> = set_add(set_add(set_new(), @Float64.0), @Float64.0);
  if set_contains(@Set<Float64>.0, @Float64.0) then {
    nat_to_int(set_size(@Set<Float64>.0))
  } else { -1 }
}
"""
        # deduped to size 1; contains finds NaN → 1.
        assert _run(src) == 1

    def test_nan_set_element_removed(self) -> None:
        """``set_remove`` finds and drops a NaN element (SameValueZero in
        the structural rebuild); the later size is 0."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = 0.0 / 0.0;
  let @Set<Float64> = set_add(set_new(), @Float64.0);
  let @Set<Float64> = set_remove(@Set<Float64>.0, @Float64.0);
  nat_to_int(set_size(@Set<Float64>.0))
}
"""
        assert _run(src) == 0


# #738: this trio compiles and runs full GC-reclamation programs at scale
# (~minutes locally), so it is marked `stress` and deselected from the
# default per-PR pytest run.  Run via `pytest -m stress` or nightly CI.
@pytest.mark.stress
class TestHostHandleReclamation573:
    """Reclamation regressions originally for the heap-wrap-as-ADT
    migration of Map (#573), Set (#575), and Decimal (#576), updated
    for the #706 bucket-as-truth move.

    After #706 Map and Set hold no Python store: each op builds a fresh
    wrapper + bucket and the transients are reclaimed by ordinary
    mark-sweep (no Phase 2c destructor).  Decimal alone still uses a
    Python store, reclaimed via ``host_decref_handle``.

    Covers:

    * **chain reclaims transients** — a 1K/10K-iter ``array_fold``
      chain keeps only the final Map / Set reachable; ``peak_heap_bytes``
      grows ~O(N) (a leak would grow ~O(N^2)).  The Decimal chain still
      asserts a bounded host-store residual.
    * **value correct after pressure** — repeated lookups against the
      live final value across heavy GC cadence prove reclamation never
      evicts live entries.
    * **JObject bucket path at scale** — the JSON parser's internal
      ``Map<String, Json>`` allocations round-trip through the bucket
      codec thousands of times without corruption.
    * **wrap-table machinery present** — Map / Set / JSON / HTML /
      Decimal modules emit the ``host_decref_handle`` import,
      ``$register_wrapper`` (with its #579 compaction slow path), and
      export.  Post-#706 only Decimal actually registers; the infra is
      still gated on the broad ops predicate, so it is emitted (but
      unused) for non-Decimal modules too — conservative and
      correctness-neutral.
    """

    def test_map_chain_reclaims_transients(self) -> None:
        """#706: a long ``array_fold`` over ``map_insert`` keeps only the
        final Map reachable; every transient wrapper + bucket is
        reclaimed by ordinary mark-sweep (no Python store to evict).

        Measured via ``peak_heap_bytes`` (the bump high-water mark): with
        reclamation the heap grows ~O(N) across the chain (≈6x for 10x
        the inserts); a leak would grow ~O(N^2) (≈100x).
        """
        def chain(n: int) -> str:
            return f"""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{{
  let @Map<Int, Int> = map_new();
  let @Map<Int, Int> = array_fold(
    array_range(1, {n + 1}),
    @Map<Int, Int>.0,
    fn(@Map<Int, Int>, @Int -> @Map<Int, Int>) effects(pure) {{
      map_insert(@Map<Int, Int>.0, @Int.0, @Int.0)
    }}
  );
  match map_get(@Map<Int, Int>.0, {n // 2}) {{
    Some(@Int) -> @Int.0,
    None -> -1
  }}
}}
"""
        _assert_chain_reclaims(chain, 1000, 10000, 500, 5000)

    def test_json_object_map_bucket_path_at_scale(self) -> None:
        """#706: JSON's internal ``Map<String, Json>`` for each JObject is
        a bucket-as-truth wrapper (``_alloc_map_wrapper``).  Parse 5 000
        transient JObjects in an iterative ``array_fold`` and read a field
        back out of each, round-tripping every one through the bucket
        *encode* (``_alloc_map_wrapper``) and *decode* (``_decode_map``
        via ``map_get``, reached through ``json_get_int``) paths at scale
        without corruption.

        This is a functional round-trip check, not a leak check.  Each
        JObject is a constant-size single-key map, so even total
        reclamation failure grows the heap only ~O(N) — the same order as
        the live ``array_range(0, N)`` input array — and a
        ``peak_heap_bytes`` ratio cannot separate the two (that signal
        needs healthy O(N) vs leaked O(N^2), which holds for the Map/Set
        chains above but never for constant-size transients).  Reclamation
        of these JObject wrappers is covered there — the chains leak
        O(N^2) through the same ``_alloc_map_wrapper`` encode path — and
        their value reachability by ``TestMapHostStoreGCReachability695``
        under ``VERA_EAGER_GC=1``.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 0;
  array_fold(
    array_range(0, 5000),
    @Int.0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match json_parse("{\\"k\\": 7}") {
        Ok(@Json) ->
          match json_get_int(@Json.0, "k") {
            Some(@Int) -> @Int.2 + @Int.0,
            None -> @Int.1
          },
        Err(@String) -> @Int.1
      }
    }
  )
}
"""
        # 5 000 round-trips, each reading "k" = 7 back out → 5000 * 7.
        assert _run(src) == 35000

    def test_map_value_lookup_after_gc_pressure(self) -> None:
        """Functional integrity after heavy reclamation pressure.

        Pre-#573 the wrap-table walk wasn't running, so this would
        return the right answer trivially.  Post-#573 the destructor
        hook is firing on every transient — if it had a bug
        (off-by-one in compaction, wrong handle stored, etc.) the
        live Map's host store entry could be evicted by mistake
        and ``map_get`` would return None or trap.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_new();
  let @Map<Int, Int> = array_fold(
    array_range(0, 1000),
    @Map<Int, Int>.0,
    fn(@Map<Int, Int>, @Int -> @Map<Int, Int>) effects(pure) {
      map_insert(@Map<Int, Int>.0, @Int.0, @Int.0 * 7)
    }
  );
  --Look up several keys to force the live Map's entry to be
  --consulted multiple times across GC events.
  match map_get(@Map<Int, Int>.0, 0) {
    Some(@Int) -> match map_get(@Map<Int, Int>.0, 500) {
      Some(@Int) -> match map_get(@Map<Int, Int>.0, 999) {
        Some(@Int) -> @Int.0,
        None -> -1
      },
      None -> -2
    },
    None -> -3
  }
}
"""
        # 999 * 7 = 6993
        assert _run(src) == 6993

    def test_set_chain_reclaims_transients(self) -> None:
        """#706: a long ``array_fold`` over ``set_add`` keeps only the
        final Set reachable; transients are reclaimed by mark-sweep.

        Same ``peak_heap_bytes`` ~O(N) signal as the Map chain.
        """
        def chain(n: int) -> str:
            return f"""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{{
  let @Set<Int> = set_new();
  let @Set<Int> = array_fold(
    array_range(1, {n + 1}),
    @Set<Int>.0,
    fn(@Set<Int>, @Int -> @Set<Int>) effects(pure) {{
      set_add(@Set<Int>.0, @Int.0)
    }}
  );
  if set_contains(@Set<Int>.0, {n // 2}) then {{ 1 }} else {{ 0 }}
}}
"""
        _assert_chain_reclaims(chain, 1000, 10000, 1, 1)

    def test_set_value_correct_after_gc_pressure(self) -> None:
        """Functional integrity for Set under GC pressure.

        Symmetric to the Map / Decimal lookup-after-pressure tests:
        if the Set destructor mechanism had a bug evicting live
        wrappers, ``set_contains`` would return false for elements
        that ARE in the live Set, or trap on a missing host-store
        entry.  Exercises 1 000 set_adds + multiple ``set_contains``
        and ``set_size`` calls on the live Set.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_new();
  let @Set<Int> = array_fold(
    array_range(0, 1000),
    @Set<Int>.0,
    fn(@Set<Int>, @Int -> @Set<Int>) effects(pure) {
      set_add(@Set<Int>.0, @Int.0)
    }
  );
  --Three lookups + size, all on the same live Set across GC events.
  if set_contains(@Set<Int>.0, 0) then {
    if set_contains(@Set<Int>.0, 500) then {
      if set_contains(@Set<Int>.0, 999) then {
        nat_to_int(set_size(@Set<Int>.0))
      } else { -1 }
    } else { -2 }
  } else { -3 }
}
"""
        # 1000 distinct elements in [0, 1000) → size 1000.
        assert _run(src) == 1000

    def test_decimal_chain_reclaims_transients(self) -> None:
        """A 5 000-iteration ``array_fold`` over ``decimal_add``
        reclaims transients (#573 phase 3).

        Each iteration constructs a new Decimal handle via
        ``decimal_add`` (host_decimal_add allocates a fresh
        PyDecimal in ``_decimal_store``); the closure return is
        consumed by the next iteration.  Pre-fix store size was
        ~5 000+ (each intermediate plus per-iteration
        ``decimal_from_int(@Int.0)`` for the second arg).  Post-
        fix Phase 2c walks the wrap table and fires
        ``host_decref_handle(DECIMAL, handle)`` for every
        unmarked wrapper.

        Smaller iteration count than the Map test because
        ``decimal_add`` is more expensive per iteration (Python
        ``Decimal`` arithmetic vs. dict insertion).
        """
        src = """
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = array_fold(
    array_range(0, 5000),
    decimal_from_int(0),
    fn(@Decimal, @Int -> @Decimal) effects(pure) {
      decimal_add(@Decimal.0, decimal_from_int(@Int.0))
    }
  );
  --Sum 0 + 1 + ... + 4999 = 12 497 500.
  decimal_eq(@Decimal.0, decimal_from_int(12497500))
}
"""
        result = _compile_ok(src)
        exec_result = execute(result)
        assert exec_result.value == 1, (
            f"Decimal sum should equal 12 497 500; "
            f"got {exec_result.value}"
        )
        store_size = exec_result.host_store_sizes.get("decimal", 0)
        # Decimal accumulates ~2 entries per iteration pre-GC
        # (the old accumulator + the from_int(idx)) plus the
        # final decimal_eq pair.  Bound is more generous than
        # Map because the arithmetic path is denser.
        assert store_size < 1500, (
            f"#573 phase 3 regression: _decimal_store has "
            f"{store_size} entries after 5 000 decimal_add "
            f"iterations.  Pre-fix this was monotonic at "
            f"~10 000+; post-fix Phase 2c reclaims unreachable "
            f"Decimal wrappers via `kind == 3` in "
            f"host_decref_handle.  A size > 1 500 indicates "
            f"reclamation isn't keeping pace with allocation."
        )

    def test_json_only_module_includes_wrap_table(self) -> None:
        """A module that uses ONLY ``json_parse`` (no user-level
        ``map_*`` ops) still emits the wrap-table infrastructure
        (``host_decref_handle`` import, ``$register_wrapper``, export).

        The ``_decref_used`` / ``_needs_wrap_table`` predicates flip on
        ``_json_ops_used`` / ``_html_ops_used`` (this was #573 finding
        5: JSON / HTML modules must not trap at instantiation when the
        host accesses the ``register_wrapper`` export).  Post-#706
        ``write_json``'s JObject branch builds its ``Map<String, Json>``
        as a bucket-as-truth wrapper, which does NOT register — so this
        infra is conservatively emitted but unused for a JSON-only
        module (Decimal is the only registerer post-#706).  This
        structural test pins that the emission + instantiation path
        stays present and trap-free.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"a\\": 1}");
  match @Result<Json, String>.0 {
    Ok(@Json) -> 1,
    Err(@String) -> 0
  }
}
"""
        wat = _compile_ok(src).wat
        assert (
            'import "vera" "host_decref_handle"' in wat
        ), (
            "#573 finding 5 regression: JSON-only program is "
            "missing the host_decref_handle import (gated on "
            "_json_ops_used so the wrap-table machinery is present)."
        )
        assert "$register_wrapper" in wat, (
            "#573 finding 5 regression: JSON-only program is "
            "missing the $register_wrapper helper; the host must not "
            "trap at instantiation reaching for the export."
        )
        assert '(export "register_wrapper"' in wat, (
            "#573 finding 5 regression: JSON-only program is "
            "missing the register_wrapper export."
        )
        # Functional check too: the program runs and returns 1.
        assert _run(src) == 1

    def test_html_only_module_includes_wrap_table(self) -> None:
        """An HTML-using program emits the wrap-table machinery
        (mirror of ``test_json_only_module_includes_wrap_table``).

        ``write_html``'s HtmlElement attrs branch builds its
        ``Map<String, String>`` as a bucket-as-truth wrapper exactly
        like ``write_json``'s JObject branch — neither registers
        post-#706, so the infra is emitted (gated on ``_html_ops_used``)
        but unused here.  Compiling ``html_parse`` typically also pulls
        in the prelude's ``html_attr`` (which dispatches to
        ``map_get``), so ``_map_ops_used`` is set anyway in practice —
        but the ``_html_ops_used`` gating is the load-bearing one if
        that prelude transitivity ever changes.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match html_parse("<p>hello</p>") {
    Ok(@HtmlNode) -> 1,
    Err(@String) -> 0
  }
}
"""
        wat = _compile_ok(src).wat
        assert (
            'import "vera" "host_decref_handle"' in wat
        ), (
            "#573 finding 5 regression (HTML): missing "
            "host_decref_handle import (gated on _html_ops_used so "
            "the wrap-table machinery is present)."
        )
        assert "$register_wrapper" in wat, (
            "#573 finding 5 regression (HTML): missing "
            "$register_wrapper helper."
        )
        assert '(export "register_wrapper"' in wat, (
            "#573 finding 5 regression (HTML): missing "
            "register_wrapper export."
        )
        assert _run(src) == 1

    def test_register_wrapper_has_compaction_slow_path(self) -> None:
        """``$register_wrapper`` triggers ``$gc_collect`` on
        overflow before trapping (#579).

        Pre-#579 the function trapped with ``unreachable`` the
        moment ``$gc_wrap_ptr >= $gc_wrap_end`` — even if
        compaction would have freed thousands of dead entries.
        Post-fix the slow path roots the in-flight wrapper on
        the shadow stack, calls ``$gc_collect`` (which runs
        Phase 2c compaction), pops the root, and re-checks; only
        if the table is still full does it trap.

        This is a structural test rather than functional because
        triggering the slow path under a real workload is hard:
        every wrapper IS also a heap allocation, so wrap-table-
        full and heap-full happen at similar cadences and
        ``$alloc`` triggers GC first under normal conditions.
        Asserting the slow-path WAT is present pins that the
        emitter wired up the compaction call correctly; if a
        future refactor reverts to the unconditional trap, this
        test catches it.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_new();
  match map_get(@Map<Int, Int>.0, 1) {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
"""
        wat = _compile_ok(src).wat
        # Locate the $register_wrapper function body.
        fn_match = re.search(
            r"\(func \$register_wrapper\b.*?(?=\n  \(func |\n\s*\)\s*$)",
            wat, re.DOTALL,
        )
        assert fn_match is not None, (
            "$register_wrapper not emitted in WAT — wrap-table "
            "infrastructure may be missing despite a Map op being "
            "used"
        )
        body = fn_match.group(0)
        # Slow path must call $gc_collect.
        assert "call $gc_collect" in body, (
            "#579 regression: $register_wrapper has no "
            "$gc_collect call in its overflow path.  Pre-#579 it "
            "trapped unconditionally; post-fix it must compact "
            "first.  Without the slow path, programs hitting the "
            "wrap-table ceiling trap even when most entries are "
            "dead and would be reclaimed by Phase 2c."
        )
        # Slow path must shadow-push the in-flight wrapper before
        # the collect (otherwise GC frees the just-allocated
        # wrapper body and we append to a dangling pointer).
        # The push idiom: global.get $gc_sp; local.get $ptr;
        # i32.store; ...; global.set $gc_sp.
        push_before_collect = re.search(
            r"global\.get \$gc_sp\s+"
            r"local\.get \$ptr\s+"
            r"i32\.store\s+"
            r"global\.get \$gc_sp\s+"
            r"i32\.const 4\s+"
            r"i32\.add\s+"
            r"global\.set \$gc_sp.*?"
            r"call \$gc_collect",
            body, re.DOTALL,
        )
        assert push_before_collect is not None, (
            "#579 regression: $register_wrapper calls "
            "$gc_collect but doesn't shadow-push $ptr first.  "
            "Without rooting, Phase 2b marks the in-flight "
            "wrapper unreachable, Phase 3 frees it, and the "
            "post-collect append writes to a freed object."
        )
        # And there should be a re-check after the collect — two
        # `i32.ge_u` operations (the initial overflow check, and
        # the post-compaction re-check).
        assert body.count("i32.ge_u") >= 2, (
            "#579 regression: $register_wrapper has fewer than 2 "
            "`i32.ge_u` ops; the post-compaction re-check is "
            "likely missing."
        )
        # Shadow-stack must be balanced on the trap path.  The
        # pop of the temporary root must appear BEFORE the
        # re-check guard — if the trap fires, the pop has
        # already executed and the shadow stack is balanced.
        # Pop idiom: ``global.get $gc_sp; i32.const 4; i32.sub;
        # global.set $gc_sp``.  Re-check idiom: ``global.get
        # $gc_wrap_ptr; global.get $gc_wrap_end; i32.ge_u``.
        # Match both with the pop strictly preceding the
        # re-check (in the same slow-path region).
        balance_pattern = re.search(
            r"call \$gc_collect.*?"
            r"global\.get \$gc_sp\s+"
            r"i32\.const 4\s+"
            r"i32\.sub\s+"
            r"global\.set \$gc_sp.*?"
            r"global\.get \$gc_wrap_ptr\s+"
            r"global\.get \$gc_wrap_end\s+"
            r"i32\.ge_u",
            body, re.DOTALL,
        )
        assert balance_pattern is not None, (
            "#579 regression: shadow-stack imbalance on trap "
            "path.  The pop of the temporary root must appear "
            "between $gc_collect and the post-compaction "
            "re-check guard — otherwise the trap leaves $gc_sp "
            "one slot above its caller-entry level.  Today the "
            "trap is `unreachable` and the WASM module aborts, "
            "so the imbalance has no observable effect, but "
            "treating WAT shadow-stack discipline as a hard "
            "invariant catches regressions before any future "
            "change makes the trap recoverable."
        )

    def test_decimal_value_correct_after_gc_pressure(self) -> None:
        """Functional integrity for Decimal under GC pressure.

        Same shape as ``test_map_value_lookup_after_gc_pressure``:
        if the Decimal destructor mechanism had a bug that evicted
        live wrappers, ``decimal_eq`` would either return false or
        trap on a missing host-store entry.
        """
        src = """
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = array_fold(
    array_range(1, 1001),
    decimal_from_int(0),
    fn(@Decimal, @Int -> @Decimal) effects(pure) {
      decimal_add(
        @Decimal.0,
        decimal_mul(decimal_from_int(@Int.0), decimal_from_int(2))
      )
    }
  );
  --Sum 2*(1+2+...+1000) = 2 * 500 500 = 1 001 000.
  decimal_eq(@Decimal.0, decimal_from_int(1001000))
}
"""
        assert _run(src) == 1
