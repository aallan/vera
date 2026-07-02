"""Tests for vera.codegen — gc_rooting (opaque-handle and host-walker GC-rooting hygiene).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re
from pathlib import Path

import pytest

from vera.codegen import (
    compile,
    execute,
)

from tests.codegen_helpers import (
    _compile_ok,
    _run,
    _run_io,
)


# =====================================================================
# Opaque-handle GC-rooting hygiene (#347 + #490)
# =====================================================================


class TestOpaqueHandleParamRooting347:
    """`#347`: opaque host handles (Map / Set / Decimal) MUST NOT be
    pushed to the GC shadow stack as roots when they appear as
    function parameters.

    Pre-fix, the gc_pointer_params loop in
    `vera/codegen/functions.py` excluded only `Bool` and `Byte`,
    so a `Map<K, V>` / `Set<T>` / `Decimal` parameter (i32 handle
    index) was treated as a heap pointer and pushed onto the
    shadow stack.  Wasted shadow-stack space and a handle value
    that happened to land in the heap-pointer range with valid
    alignment would have caused the conservative mark phase to
    spuriously mark an unrelated heap object as live (memory
    retention, not corruption).

    Post-fix, the new `_is_host_handle_type` classifier in
    `vera/wasm/helpers.py` is consulted at the rooting decision
    site to exclude these opaque handle types.  We pin the fix
    structurally via WAT inspection: a function taking a
    `Map<K, V>` parameter and needing GC alloc should NOT contain
    the `local.get $p0; i32.store` shadow-push idiom.
    """

    @staticmethod
    def _assert_param0_not_shadow_pushed(
        src: str, fn_name: str, type_label: str,
    ) -> None:
        """Shared helper for the per-handle-type assertion.

        Compiles `src`, finds `$fn_name`, and verifies:

          1. The function's GC prologue WAS emitted (otherwise the
             test is vacuous — a function with no allocator activity
             trivially has no shadow-pushes regardless of whether
             the exclusion fires).
          2. The canonical param-0 shadow-push idiom is NOT present.

        The push regex accepts both numeric (`local.get 0`) and
        named (`local.get $p0`, `local.get $name`) forms — codegen
        currently emits numeric, but future renames shouldn't make
        this test silently pass.

        `type_label` surfaces in failure messages so each call site
        reports which handle type regressed.
        """
        result = _compile_ok(src)
        fn_marker = f"(func ${fn_name}"
        fn_start = result.wat.index(fn_marker)
        if "\n  (func " in result.wat[fn_start + 1:]:
            fn_end = result.wat.index("\n  (func ", fn_start + 1)
        else:
            fn_end = len(result.wat)
        fn_body = result.wat[fn_start:fn_end]

        # Non-vacuity check: confirm the GC prologue WAS emitted for
        # this function.  The prologue's signature is
        # `global.get $gc_sp` followed by a `local.set` (saving the
        # restore point).  Without this, the absence of param-0
        # pushes below is meaningless — there's no shadow-stack
        # activity in the function at all.
        prologue_pattern = re.compile(
            r"global\.get \$gc_sp\s+local\.set\b",
        )
        assert prologue_pattern.search(fn_body), (
            f"${fn_name} has no GC prologue — the test is vacuous "
            f"because no shadow-push activity was emitted.  Adjust "
            f"the test source so the function body forces an "
            f"allocation (e.g. via `option_unwrap_or` or an ADT "
            f"constructor) before the assertion below can pin the "
            f"opaque-handle exclusion."
        )

        # The push idiom we're guarding against — both numeric and
        # named forms of `local.get`.  Numeric is what codegen emits
        # today; named (`$p0`, `$name`) is matched defensively in
        # case codegen is later updated to use param names.
        push_pattern = re.compile(
            r"global\.get \$gc_sp\s+"
            r"local\.get (?:0\b|\$\S+)\s+"
            r"i32\.store",
            re.MULTILINE,
        )
        # Filter to pushes that target param 0 specifically.  Named
        # form `$p0` is the canonical first-param name; numeric `0`
        # also targets the first local.  Other locals (`local.get 1`,
        # `local.get $l2`, etc.) aren't relevant to the param-0
        # exclusion check.
        for match in push_pattern.finditer(fn_body):
            text = match.group(0)
            if "local.get 0" in text or "local.get $p0" in text:
                raise AssertionError(
                    f"Found a shadow_push of param 0 (the "
                    f"{type_label} handle) in ${fn_name} — the "
                    f"opaque-handle exclusion (#347) isn't being "
                    f"applied.  Map / Set / Decimal handles are "
                    f"i32 indices into Python-side stores, not "
                    f"Vera-heap pointers; rooting them wastes "
                    f"shadow-stack space and could cause spurious "
                    f"heap-object retention via the conservative "
                    f"GC's heap-range check.\n\nMatched WAT "
                    f"sequence: {text!r}"
                )

    def test_map_param_shadow_pushed_after_573(self) -> None:
        """A `Map<Nat, Nat>` parameter MUST appear in a
        gc_shadow_push sequence after #573.

        Pre-#573 (v0.0.132): Map values lowered to raw i32 host
        handles, so the #347 classifier excluded them from
        rooting.  Post-#573 (v0.0.134): Map values are pointers
        to GC-managed wrapper ADTs — real Vera-heap pointers
        that the conservative GC must trace, so the exclusion
        is dropped and the canonical shadow-push idiom
        ``global.get $gc_sp; local.get 0; i32.store`` reappears.
        Without rooting, a Map captured across an allocating
        call (e.g. ``map_get`` returning ``Option<V>``) would
        get freed mid-call and the host store entry would be
        decref'd before the surrounding code finishes using it.
        """
        from vera.parser import parse_to_ast
        src = """
public fn lookup_or_zero(@Map<Nat, Nat>, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(map_get(@Map<Nat, Nat>.0, @Nat.0), 0)
}
"""
        result = compile(parse_to_ast(src), source=src)
        wat = result.wat
        # Find $lookup_or_zero's body.
        fn_match = re.search(
            r"\(func \$lookup_or_zero\b.*?(?=\n  \(func |\n\s*\)\s*$)",
            wat, re.DOTALL,
        )
        assert fn_match is not None, (
            f"Could not find $lookup_or_zero in WAT: {wat[:500]}"
        )
        fn_body = fn_match.group(0)
        # The full ``gc_shadow_push`` idiom is push + advance:
        #   global.get $gc_sp; local.get N; i32.store      (push)
        #   global.get $gc_sp; i32.const 4; i32.add;
        #   global.set $gc_sp                              (advance)
        # Match BOTH halves in order — without the advance, every
        # subsequent push overwrites the same shadow-stack slot,
        # so the test must fail if the advance is missing.
        push_pattern = re.compile(
            r"global\.get \$gc_sp\s+"
            r"local\.get (?:0\b|\$p?0\b)\s+"
            r"i32\.store\s+"
            r"global\.get \$gc_sp\s+"
            r"i32\.const 4\s+"
            r"i32\.add\s+"
            r"global\.set \$gc_sp",
            re.MULTILINE,
        )
        assert push_pattern.search(fn_body) is not None, (
            "#573 regression: Map<Nat, Nat> param 0 was NOT "
            "shadow-pushed (with sp advance) in $lookup_or_zero. "
            "Post-#573, Map values are GC-managed wrapper-ADT "
            "pointers and MUST be rooted across allocating calls; "
            "without the full push+advance idiom the wrapper can "
            "be freed mid-call OR the next push overwrites it.\n\n"
            f"Function body excerpt:\n{fn_body[:800]}"
        )

    def test_set_param_shadow_pushed_after_573(self) -> None:
        """A `Set<Nat>` parameter MUST appear in a
        gc_shadow_push sequence after #573 phase 2.

        Same flip as Map (`test_map_param_shadow_pushed_after_573`):
        post-#573 the Set value lowers to a wrapper-ADT pointer
        (real Vera-heap pointer), so the conservative GC must
        trace it.  Without rooting, a Set captured across an
        allocating call (e.g. `set_contains` returning Bool but
        the surrounding ``option_unwrap_or(Some(...), ...)`` does
        an Option allocation) could be freed mid-call and the
        host-store entry decref'd before subsequent code finishes
        using it.
        """
        from vera.parser import parse_to_ast
        src = """
public fn contains_or_false(@Set<Nat>, @Nat -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if set_contains(@Set<Nat>.0, @Nat.0) then {
    option_unwrap_or(Some(true), false)
  } else {
    option_unwrap_or(Some(false), false)
  }
}
"""
        result = compile(parse_to_ast(src), source=src)
        wat = result.wat
        fn_match = re.search(
            r"\(func \$contains_or_false\b.*?(?=\n  \(func |\n\s*\)\s*$)",
            wat, re.DOTALL,
        )
        assert fn_match is not None
        fn_body = fn_match.group(0)
        # Full push+advance idiom — see Map test for rationale.
        push_pattern = re.compile(
            r"global\.get \$gc_sp\s+"
            r"local\.get (?:0\b|\$p?0\b)\s+"
            r"i32\.store\s+"
            r"global\.get \$gc_sp\s+"
            r"i32\.const 4\s+"
            r"i32\.add\s+"
            r"global\.set \$gc_sp",
            re.MULTILINE,
        )
        assert push_pattern.search(fn_body) is not None, (
            "#573 phase 2 regression: Set<Nat> param 0 was NOT "
            "shadow-pushed (with sp advance) in $contains_or_false. "
            "Post-#573 phase 2, Set values are GC-managed "
            "wrapper-ADT pointers and MUST be rooted with the full "
            "push+advance idiom across allocating calls.\n\n"
            f"Function body excerpt:\n{fn_body[:800]}"
        )

    def test_decimal_param_shadow_pushed_after_573(self) -> None:
        """A `Decimal` parameter MUST appear in a gc_shadow_push
        sequence after #573 phase 3.

        Same flip as Map and Set: Decimal values are now wrapper-
        ADT pointers and need rooting.
        """
        from vera.parser import parse_to_ast
        src = """
public fn is_positive_or_false(@Decimal -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if decimal_eq(@Decimal.0, decimal_from_int(0)) then {
    option_unwrap_or(Some(false), false)
  } else {
    option_unwrap_or(Some(true), false)
  }
}
"""
        result = compile(parse_to_ast(src), source=src)
        wat = result.wat
        fn_match = re.search(
            r"\(func \$is_positive_or_false\b.*?(?=\n  \(func |\n\s*\)\s*$)",
            wat, re.DOTALL,
        )
        assert fn_match is not None
        fn_body = fn_match.group(0)
        # Full push+advance idiom — see Map test for rationale.
        push_pattern = re.compile(
            r"global\.get \$gc_sp\s+"
            r"local\.get (?:0\b|\$p?0\b)\s+"
            r"i32\.store\s+"
            r"global\.get \$gc_sp\s+"
            r"i32\.const 4\s+"
            r"i32\.add\s+"
            r"global\.set \$gc_sp",
            re.MULTILINE,
        )
        assert push_pattern.search(fn_body) is not None, (
            "#573 phase 3 regression: Decimal param 0 was NOT "
            "shadow-pushed (with sp advance) in "
            "$is_positive_or_false.  Post-#573 phase 3, Decimal "
            "values are GC-managed wrapper-ADT pointers and MUST "
            "be rooted with the full push+advance idiom across "
            "allocating calls.\n\n"
            f"Function body excerpt:\n{fn_body[:800]}"
        )


class TestArrayFoldHandleRooting490:
    """`#490` (pre-#573) and `#573 phase 3` (post-): array_fold /
    array_map handle-rooting policy for ``Decimal`` accumulators
    and elements.

    Pre-#490 (v0.0.131): ADT-rooting heuristic over-rooted
    Decimal accumulators / elements as if they were heap pointers,
    even though Decimal lowered to a raw i32 host handle.

    Post-#490 (v0.0.132): the ``_is_host_handle_type`` classifier
    excluded Decimal so the rooting was suppressed (no waste, no
    spurious retention).

    Post-#573 phase 3 (v0.0.134): Decimal MIGRATED to heap-wrap-
    as-ADT.  Decimal values are now wrapper-ADT pointers — real
    Vera-heap pointers — so they MUST be rooted again.  This
    test class flips its assertion to enforce the new policy:
    Decimal accumulators / elements emit MORE shadow-pushes than
    the Int reference (the wrapper allocation rooting + the
    accumulator slot push).  Without rooting, a wrapper could be
    reclaimed mid-fold and the host_decref_handle path would
    evict the live Decimal entry from the host store.
    """

    @staticmethod
    def _count_main_pushes(wat: str) -> int:
        """Count `global.set $gc_sp` idioms inside `$main`'s body.

        Each `gc_shadow_push` emits exactly one `global.set $gc_sp`
        (the sp-advance step at the end of the idiom).  Higher
        count for Decimal vs. Int reference indicates Decimal IS
        being rooted — which post-#573 phase 3 is the correct
        behaviour.
        """
        fn_start = wat.index("(func $main")
        if "\n  (func " in wat[fn_start + 1:]:
            fn_end = wat.index("\n  (func ", fn_start + 1)
        else:
            fn_end = len(wat)
        return wat[fn_start:fn_end].count("global.set $gc_sp")

    def _assert_handle_extra_rooted_after_573(
        self,
        int_src: str,
        decimal_src: str,
        builder_name: str,
        accumulator_label: str,
    ) -> None:
        """Compile `int_src` (Int reference) and `decimal_src`
        (Decimal handle wrapper), then assert the Decimal version
        emits MORE shadow-pushes than the Int version.

        Pre-#573 this asserted the opposite (Decimal must equal
        Int).  Post-#573 phase 3 Decimal is wrapper-rooted, so
        the count rises by at least one (the accumulator's
        wrapper-pointer push) plus any per-iteration alloc roots
        from the wrap operation itself.
        """
        int_wat = _compile_ok(int_src).wat
        decimal_wat = _compile_ok(decimal_src).wat
        int_count = self._count_main_pushes(int_wat)
        decimal_count = self._count_main_pushes(decimal_wat)

        # Non-vacuity: int_count > 0 ensures we're measuring real
        # shadow-stack activity, not a degenerate empty slice.
        assert int_count > 0, (
            f"Int reference for {builder_name} emitted 0 "
            f"`global.set $gc_sp` idioms in $main — the helper "
            f"isn't measuring real shadow-stack activity, so the "
            f"comparison below would pass trivially."
        )

        # Strictly-greater: Decimal MUST add roots.  Pre-#573 this
        # was equality; post-#573 phase 3 the wrapper migration
        # adds wrapper-allocation rooting + accumulator-slot push.
        assert decimal_count > int_count, (
            f"`{builder_name}` with a Decimal {accumulator_label} "
            f"emits {decimal_count} `global.set $gc_sp` idioms in "
            f"$main vs. {int_count} for an Int reference.  Post-"
            f"#573 phase 3 the Decimal version must emit MORE — "
            f"Decimal is now a GC-managed wrapper-ADT pointer, "
            f"not a raw handle, so the wrapper allocation and "
            f"accumulator slot both need rooting.  An equal or "
            f"smaller count means `_is_host_handle_type` is "
            f"still excluding Decimal."
        )

    def test_decimal_accumulator_rooted_after_573(self) -> None:
        """`array_fold` over a `Decimal` accumulator MUST root the
        wrapper pointer (post-#573 phase 3).

        Pre-#573 phase 3 this asserted the opposite — the
        ``u_is_adt`` heuristic excluded Decimal because raw i32
        handles aren't heap pointers.  Post-#573 Decimal IS a
        heap pointer (wrapper ADT) and must be rooted to survive
        per-iteration GC pressure (every iteration's
        ``decimal_add`` allocates a new wrapper).
        """
        int_src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 5),
    0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
  )
}
"""
        decimal_src = """
public fn main(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 5),
    decimal_from_int(0),
    fn(@Decimal, @Int -> @Decimal) effects(pure) {
      decimal_add(@Decimal.0, decimal_from_int(@Int.0))
    }
  )
}
"""
        self._assert_handle_extra_rooted_after_573(
            int_src, decimal_src, "array_fold", "accumulator",
        )

    def test_decimal_mapper_rooted_after_573(self) -> None:
        """`array_map` producing `Decimal` elements MUST root the
        wrapper pointer (post-#573 phase 3).

        Mirror of ``test_decimal_accumulator_rooted_after_573``
        for ``array_map``'s element-rooting heuristic
        (``t_is_adt``).
        """
        int_src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_map(
    array_range(0, 5),
    fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }
  ))
}
"""
        decimal_src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_map(
    array_range(0, 5),
    fn(@Int -> @Decimal) effects(pure) { decimal_from_int(@Int.0) }
  ))
}
"""
        self._assert_handle_extra_rooted_after_573(
            int_src, decimal_src, "array_map", "element",
        )

    def test_array_fold_with_decimal_runs_correctly(self) -> None:
        """Functional pin: the fold over Decimal still produces the
        right result.  Pre- and post-fix this works (the
        conservative GC's heap-range check rejects small handle
        values either way), so this test passes in both states —
        but it pins that the structural optimisation didn't break
        anything.

        Sum 0+1+2+3+4 = 10; comparing to `decimal_from_int(10)`
        via `decimal_eq` returns 1.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = array_fold(
    array_range(0, 5),
    decimal_from_int(0),
    fn(@Decimal, @Int -> @Decimal) effects(pure) {
      decimal_add(@Decimal.0, decimal_from_int(@Int.0))
    }
  );
  if decimal_eq(@Decimal.0, decimal_from_int(10)) then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_array_map_with_decimal_runs_correctly(self) -> None:
        """Functional pin for the array_map case: produce an array
        of Decimal handles and verify the round-trip through
        `array_fold(decimal_add)` returns the right total.

        Pre- and post-fix this works (same conservative-GC
        argument as the fold case), but pinning prevents a
        future array_map regression from silently breaking the
        `Decimal` element path.

        `array_map([0..5), fn(i) { decimal_from_int(i*2) })`
        produces `[0, 2, 4, 6, 8]` as Decimal handles; folding
        with `decimal_add` gives 20.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Decimal> = array_map(
    array_range(0, 5),
    fn(@Int -> @Decimal) effects(pure) {
      decimal_from_int(@Int.0 * 2)
    }
  );
  let @Decimal = array_fold(
    @Array<Decimal>.0,
    decimal_from_int(0),
    fn(@Decimal, @Decimal -> @Decimal) effects(pure) {
      decimal_add(@Decimal.0, @Decimal.1)
    }
  );
  if decimal_eq(@Decimal.0, decimal_from_int(20)) then { 1 } else { 0 }
}
"""
        # 0 + 2 + 4 + 6 + 8 = 20
        assert _run(src) == 1


# =====================================================================
# #692: host-walker GC rooting regression
# =====================================================================


class TestHostWalkerGCRooting692:
    """Pin the #692 fix: host-side tree walkers (``write_html`` /
    ``write_json`` / ``write_md_block``) must root intermediate
    WASM heap pointers on the shadow stack across recursion, so a
    ``$gc_collect`` triggered by sub-allocs does not reclaim them
    and corrupt the free list.

    The bug was reported externally with the current `FAQ.md`
    body (~25 KB) as the trigger.  These tests use a checked-in
    fixture path so the regression survives FAQ edits.

    Cousin tests for the WAT-side shadow-stack class:
    ``TestArrayMapGCRooting570``, ``TestFoldAccumulator515``,
    ``TestClosureReturnShadowAsymmetry593``.
    """

    def test_html_parse_500_element_siblings(self) -> None:
        """500 ``<a>x</a>`` siblings — exercises ``write_html``'s
        element branch (arr_ptr, name_ptr, wrapper_ptr) across
        500 iterations.  Heap grows from 1 page to ~3 pages,
        firing multiple ``$gc_collect`` cycles during the walk.
        Pre-#692-fix this trapped with ``Out-of-bounds memory
        access`` at ``0xfffffffd`` from inside ``$alloc``."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_repeat("<a>x</a>", 500);
  match html_parse(@String.0) {
    Ok(_) -> IO.print("ok"),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(src) == "ok"

    def test_json_parse_1000_number_array(self) -> None:
        """1000-element JArray of JNumbers — exercises
        ``write_json``'s JArray branch (arr_ptr rooting across
        1000 sub-allocs).  Each JNumber is 16 bytes of heap so
        the array alone produces ~16 KB of allocations on top of
        the input string."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_concat(
    "[", string_concat(string_repeat("1,", 999), "1]")
  );
  match json_parse(@String.0) {
    Ok(_) -> IO.print("ok"),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(src) == "ok"

    def test_json_parse_500_string_array(self) -> None:
        """500-element JArray of JStrings — exercises BOTH the
        JArray arr_ptr rooting AND the JString fields-first-then-
        body convention.  Each iteration allocates a string body
        and a 16-byte JString wrapper, doubling the alloc count
        per element vs the JNumber test above."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_concat(
    "[",
    string_concat(string_repeat("\\"hello world\\",", 499), "\\"end\\"]")
  );
  match json_parse(@String.0) {
    Ok(_) -> IO.print("ok"),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(src) == "ok"

    def test_md_parse_200_headings(self) -> None:
        """200 H1 + paragraph blocks — exercises ``write_md_block``
        and ``write_md_inline`` walkers, including the
        ``_write_inline_array`` / ``_write_block_array`` backing
        rooting."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_repeat("# heading\\n\\nparagraph text\\n\\n", 200);
  match md_parse(@String.0) {
    Ok(_) -> IO.print("ok"),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(src) == "ok"

    def test_html_query_30_matches(self) -> None:
        """``html_query`` over 30 matches — exercises the
        ``host_html_query`` `_ShadowGuard` path that also gained
        rooting in #692.  Without the guard, ``arr_ptr`` for the
        match-array would be reclaimed when recursive
        ``write_html`` calls grow the heap mid-walk.  Per the
        pr-review-toolkit pr-test-analyzer review on #693.

        Sized conservatively (30 vs the 500 used by html_parse
        tests above): ``host_html_query`` re-walks every matched
        subtree via ``write_html`` within a single guard window,
        accumulating pushes across all iterations.  The
        shadow-stack budget per match in practice (including the
        ``_alloc_map_wrapper`` and ``_register_wrapper`` calls
        and the WAT-side ``$alloc`` accounting) is materially
        higher than the four nominal pushes (name, wrapper, arr,
        s_ptr) of write_html element-branch — 100 matches
        empirically overflowed the 4096-entry stack.  30 still
        triggers GC during the walk while staying comfortable
        under the limit."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_concat(
    "<root>",
    string_concat(string_repeat("<p>x</p>", 30), "</root>")
  );
  match html_parse(@String.0) {
    Ok(@HtmlNode) -> {
      let @Array<HtmlNode> = html_query(@HtmlNode.0, "p");
      IO.print("ok")
    },
    Err(_) -> IO.print("parse_err")
  }
}
"""
        assert _run_io(src) == "ok"

    def test_json_parse_500_key_object(self) -> None:
        """500-key flat JObject — exercises the JObject branch of
        ``write_json`` (val_ptr push per iteration, wrapper_ptr
        push, then body alloc).  Pre-fix, the val_ptrs held in
        ``map_dict`` as Python ints were invisible to the
        conservative GC scan; a sub-walk's GC could free them.
        Per the pr-review-toolkit pr-test-analyzer review on #693."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_concat(
    "{",
    string_concat(
      string_repeat("\\"k\\":0,", 499),
      "\\"last\\":0}"
    )
  );
  match json_parse(@String.0) {
    Ok(_) -> IO.print("ok"),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(src) == "ok"


class TestMapHostStoreGCReachability695:
    """Regression suite for #695 / #705 — pre-fix, ``Map<K, T_heap>``
    and ``Set<T_heap>`` values stored in Python-side ``_map_store`` /
    ``_set_store`` were invisible to the conservative GC scan, so a
    ``$gc_collect`` between map / set construction and value access
    reclaimed the heap blocks pointed to from the dict.

    Empirically pre-fix: with ``VERA_EAGER_GC=1`` (forces a
    ``$gc_collect`` on every alloc), the reproducer printed ``0``
    instead of the JArray's actual length ``10`` — silent
    use-after-free, no trap.  The ``0`` came from the free-list's
    next-pointer overwriting the freed block's first word, which
    ``json_array_length`` then read as a length.

    Post-fix (#706 bucket-as-truth): every Map / Set wrapper carries a
    ``bucket_ptr`` at body offset +8 pointing to a WASM-resident bucket
    that IS the map / set — there is no ``_map_store`` / ``_set_store``
    anymore.  The conservative scan reaches the values via shadow stack
    → wrapper → bucket → val_ptr, so a ``Json`` value held only inside a
    Set or JObject stays reachable across the synchronous host call.

    Each test in this class drives the reproducer under
    ``VERA_EAGER_GC=1`` and asserts the post-fix value (e.g. ``10``)
    is observed.  A regression that breaks bucket reachability — the
    encode-time shadow-rooting of the new wrapper + bucket in
    ``_encode_entries`` / ``_alloc_map_wrapper``, or the match-arm /
    let-binding shadow-rooting in ``vera/wasm/data.py`` /
    ``vera/wasm/context.py`` — flips the assertion back to ``0``.
    """

    def test_eager_gc_set_of_json_post_walk_uaf(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Regression for the Set sibling bug (#705).

        Builds a ``Set<Json>`` inside a helper function so the
        original ``@Json`` local goes out of scope when the helper
        returns.  After that, the JArray's heap pointer is held
        only via ``_set_store[handle]`` (Python, invisible to GC)
        — without the bucket-array fix, ``VERA_EAGER_GC=1``
        reclaims the JArray block during ``set_to_array``'s alloc
        and ``json_array_length`` reads from freed memory,
        returning 0.

        Sister test to ``test_eager_gc_json_object_with_array_
        child_post_walk_uaf``: same bug class (host-store values
        invisible to conservative scan), different container.
        """
        src = """
effect IO { op print(String -> Unit); }

private fn build_set(-> @Set<Json>)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse(
    "[1,2,3,4,5,6,7,8,9,10]"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> set_add(set_new(), @Json.0),
    Err(@String) -> set_new()
  }
}

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Set<Json> = build_set();
  let @Array<Json> = set_to_array(@Set<Json>.0);
  let @Int = array_fold(@Array<Json>.0, 0, fn(@Int, @Json -> @Int) effects(pure) {
    json_array_length(@Json.0) + @Int.0
  });
  IO.print(int_to_string(@Int.0))
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run_io(src) == "10"

    def test_eager_gc_json_object_with_array_child_post_walk_uaf(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``json_parse`` builds ``Map<String, Json>`` where the
        "key" entry is a JArray heap block.  The block is held only
        via ``_map_store[handle]["key"]`` — a Python int the
        conservative scan never visits.

        With ``VERA_EAGER_GC=1`` the ``Option`` alloc inside
        ``json_get`` triggers ``$gc_collect`` between ``json_parse``
        returning and the array length being read, freeing the
        JArray block.  ``json_array_length`` reads from the freed
        block and returns 0 instead of 10.

        Post-fix (this PR, "mirror" approach): the JArray pointer is
        also written to the bucket array at slot+8 by
        ``_alloc_map_wrapper`` / ``_attach_bucket_from_dict``, so
        the conservative scan reaches it via wrapper → bucket → slot.
        ``json_get`` retrieves the still-live block and the assertion
        observes ``10``.  The architectural follow-up — move ``_map_store``
        reads into the bucket array and delete the Python store entirely
        — is tracked as #706.
        """
        src = """
effect IO { op print(String -> Unit); }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Json, String> = json_parse(
    "{\\"key\\": [1,2,3,4,5,6,7,8,9,10]}"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> {
      let @Option<Json> = json_get(@Json.0, "key");
      match @Option<Json>.0 {
        Some(@Json) -> {
          let @Int = json_array_length(@Json.0);
          IO.print(int_to_string(@Int.0))
        },
        None -> IO.print("none")
      }
    },
    Err(@String) -> IO.print("err")
  }
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run_io(src) == "10"

    def test_eager_gc_map_of_json_user_level_post_walk_uaf(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Regression for the user-level ``Map<String, T_heap>`` path.

        Where ``test_eager_gc_json_object_with_array_child_post_walk_uaf``
        exercises the JSON parser's internal ``Map<String, Json>``
        construction (via ``_alloc_map_wrapper`` / ``json_parse``),
        this test exercises the user-level path: a Vera program
        explicitly calling ``map_insert`` on a ``Json`` value
        returned from ``json_parse``.  Same bug class but a
        different alloc / wrap entry point — without the bucket
        array mirror, the JArray's heap pointer is held only via
        ``_map_store[handle]["arr"]`` (a Python int) until the
        ``map_get`` retrieves it; ``VERA_EAGER_GC=1`` triggers a
        ``$gc_collect`` during the intervening Option / Json
        accessor allocs and reclaims the JArray block.

        Closes the scope gap discussed on #705: the user-level
        wrapper path was tested for Set but not yet for Map.
        """
        src = """
effect IO { op print(String -> Unit); }

private fn build_map(-> @Map<String, Json>)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse(
    "[1,2,3,4,5,6,7,8,9,10]"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> map_insert(map_new(), "arr", @Json.0),
    Err(@String) -> map_new()
  }
}

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<String, Json> = build_map();
  let @Option<Json> = map_get(@Map<String, Json>.0, "arr");
  match @Option<Json>.0 {
    Some(@Json) -> {
      let @Int = json_array_length(@Json.0);
      IO.print(int_to_string(@Int.0))
    },
    None -> IO.print("none")
  }
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run_io(src) == "10"

    def test_eager_gc_let_destruct_with_json_field_post_walk_uaf(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Regression for the ``let Ctor(@T_heap, ...) = ...`` path.

        PR #707 review (pr-test-analyzer I1): the round-2 fix in
        ``vera/wasm/data.py::_translate_let_destruct`` and the
        round-3 pair-type extension there had NO regression test
        — a refactor that drops the ``self.needs_alloc = True;
        gc_shadow_push(local_idx)`` block would silently pass CI.

        This test:
          1. ``let Tuple<@Json, @String> = Tuple(json_ptr, "tag");``
             extracts BOTH an ``i32`` heap-pointer field (`@Json`)
             and a pair-type field (`@String`).
          2. ``json_array_length(@Json.0)`` then allocates inside
             the EAGER_GC window — without the shadow-push fix on
             either rooting site, the Json buffer would be reclaimed
             between the extraction and the access.

        Asserts ``10`` (the JArray length).  A regression would
        print ``0`` from a freed-block-misread.
        """
        src = """
effect IO { op print(String -> Unit); }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Json, String> = json_parse(
    "[1,2,3,4,5,6,7,8,9,10]"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> {
      let Tuple<@Json, @String> = Tuple(@Json.0, "tag");
      let @Int = json_array_length(@Json.0);
      IO.print(int_to_string(@Int.0))
    },
    Err(@String) -> IO.print("err")
  }
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run_io(src) == "10"

    def test_eager_gc_match_binding_pattern_heap_pointer_post_walk_uaf(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Regression for the ``match expr { @T_heap -> ... }`` path.

        PR #707 review (pr-test-analyzer I2): the round-1 fix in
        ``vera/wasm/data.py`` ``ast.BindingPattern`` handler (the
        ``match @Json.0 { @Json -> ... }`` shape) was unexercised.
        All three existing regression tests use the
        ``ConstructorPattern`` shape (`Ok(@Json) ->`), which goes
        through ``_extract_constructor_fields`` — a different code
        path.  Dropping the ``gc_shadow_push(local_idx)`` block in
        the ``BindingPattern`` branch left no test to catch it.

        This test exercises the bare ``@Json`` binding-pattern with
        an intervening allocation (``set_add(set_new(), @Json.0)``)
        between binding and the final array-length probe.  A
        regression would reclaim the bound Json buffer mid-set-add
        and the assertion would observe ``0``.
        """
        src = """
effect IO { op print(String -> Unit); }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Json, String> = json_parse("[10,20,30]");
  match @Result<Json, String>.0 {
    Ok(@Json) -> match @Json.0 {
      @Json -> {
        let @Set<Json> = set_add(set_new(), @Json.0);
        IO.print(int_to_string(json_array_length(@Json.0)))
      }
    },
    Err(@String) -> IO.print("err")
  }
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run_io(src) == "3"


class TestAdtBuilderRooting743:
    """PR #743 (folded into #706): host-side ADT result builders root a
    freshly-allocated string / backing-array block across the enclosing
    struct/array alloc.

    The CLI ``_alloc_option_some_string`` / ``_alloc_result_*_string`` /
    ``_alloc_array_of_strings`` and the browser ``mapAllocOption`` /
    ``mapAllocArrayOfStrings`` / ``allocResult*String`` allocate a string,
    then allocate the wrapping struct/array — a GC fired by the second
    alloc would sweep the still-host-local string pointer and store a
    dangling reference.  Pre-existing (the #692/#695 work hardened the
    JSON/HTML walkers but not these simpler builders); surfaced by the
    CodeRabbit review of #706.  Reproduces only under ``VERA_EAGER_GC=1``
    / heap pressure.
    """

    def test_map_get_string_value_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """500 ``map_get`` calls on a ``Map<Int, String>`` under eager GC
        each return the live string.  Pre-fix returned 0: the string block
        was swept during the ``Option<String>`` struct alloc and
        ``string_contains`` read reclaimed memory."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, String> = map_insert(map_new(), 1, "alphabet_soup_xyz");
  array_fold(
    array_range(0, 500),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match map_get(@Map<Int, String>.0, 1) {
        Some(@String) ->
          if string_contains(@String.0, "soup") then { @Int.1 + 1 }
          else { @Int.1 },
        None -> @Int.1
      }
    }
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(src) == 500

    def test_map_keys_string_backing_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``map_keys`` on a ``Map<String, Int>`` builds an
        ``Array<String>`` backing under eager GC, and this folds over that
        array reading each key's bytes via ``string_contains`` — so a
        backing (or key string) swept mid-fill reads garbage and misses
        the substring (or traps).  ``_alloc_array_of_strings`` roots the
        backing across the per-element string allocs; the outer fold
        rebuilds the keys array 200x to force free-block reuse.  ``array_fold``
        is the element accessor (``array_length`` reads the host-pushed
        count and would NOT dereference a swept backing)."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_insert(map_new(), "alpha_k", 1), "beta_k", 2);
  array_fold(
    array_range(0, 200),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      let @Array<String> = map_keys(@Map<String, Int>.0);
      @Int.1 + array_fold(
        @Array<String>.0,
        0,
        fn(@Int, @String -> @Int) effects(pure) {
          if string_contains(@String.0, "_k") then { @Int.0 + 1 }
          else { @Int.0 }
        }
      )
    }
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        # 200 outer x 2 keys (both contain "_k") = 400; a swept/corrupted
        # backing reads garbage bytes (miss) or traps.
        assert _run(src) == 400

    def test_regex_find_result_payload_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``regex_find`` wraps a freshly-built ``Option<String>`` in
        ``Result.Ok``; ``_alloc_result_ok_i32`` roots the payload across
        the struct alloc.  300x under eager GC the matched substring reads
        back intact — pre-fix the Option block was swept during the
        ``Result.Ok`` alloc.  (Same builder roots the Json / HtmlNode
        payloads of ``json_parse`` / ``html_parse``.)"""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 300),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match regex_find("alphabet_soup_xyz", "soup") {
        Ok(@Option<String>) ->
          match @Option<String>.0 {
            Some(@String) ->
              if string_contains(@String.0, "soup") then { @Int.1 + 1 }
              else { @Int.1 },
            None -> @Int.1
          },
        Err(@String) -> @Int.1
      }
    }
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(src) == 300

    def test_decimal_from_string_wrapper_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``decimal_from_string`` builds a Decimal wrapper, then wraps it
        in ``Option.Some`` via ``_alloc_option_some_i32``; the helper roots
        the wrapper across the struct alloc.  300x under eager GC the
        Decimal reads back as "3.14" — pre-fix the wrapper could be swept /
        Phase-2c-decref'd before the ``Some`` payload stored it."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 300),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match decimal_from_string("3.14") {
        Some(@Decimal) ->
          if string_contains(decimal_to_string(@Decimal.0), "3.14")
          then { @Int.1 + 1 } else { @Int.1 },
        None -> @Int.1
      }
    }
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(src) == 300

    def test_regex_find_err_payload_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``regex_find`` with an invalid pattern returns ``Result.Err``
        via ``_alloc_result_err_string``; 300x under eager GC the error
        string reads back intact (the Err-path string builder roots its
        payload across the struct alloc)."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 300),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match regex_find("x", "[") {
        Ok(@Option<String>) -> @Int.1,
        Err(@String) ->
          if string_contains(@String.0, "regex") then { @Int.1 + 1 }
          else { @Int.1 }
      }
    }
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(src) == 300

class TestFutureHandleGCRooting841:
    """#841: the fused-async Future wrapper (kind 4) follows the full
    #573/#578 opaque-handle GC contract — shadow-rooted at the async
    site so eager GC can't sweep a pending future before its await,
    and reclaimed via Phase 2c ``host_decref_handle(4, handle)`` when
    a fire-and-forget future's wrapper becomes unreachable.

    All fixtures use ``ftp://`` URLs: the fetch halves reject non-
    HTTP(S) schemes locally (#789), so the worker resolves to Err
    instantly and no test ever touches the network.
    """

    def test_future_wrapper_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A pending future stays awaitable across an intervening
        allocation under eager GC — the kind-4 wrapper is shadow-
        pushed at the async site, so the string_concat sweep can't
        evict its host store entry (#570/#692 UAF class)."""
        src = """
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Future<Result<String, String>> = async(Http.get("ftp://blocked.invalid/a"));
  let @String = string_concat("force", "gc");
  let @Result<String, String> = await(@Future<Result<String, String>>.0);
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(src) == 1

    def test_unawaited_future_store_reclaimed(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Fire-and-forget futures are reclaimed by Phase 2c.

        Each ``fire_and_forget`` frame allocates a kind-4 wrapper and
        returns without awaiting; the wrap-time shadow push clears at
        the frame's epilogue, so under eager GC the next iteration's
        allocation sweeps the previous wrapper and fires
        ``host_decref_handle(4, handle)`` — evicting (and cancelling)
        the store entry.  Pre-#841-decref this store would end at
        200 entries; post-fix it ends near zero (a couple of trailing
        entries whose sweep hasn't run are allowed)."""
        src = """
public fn fire_and_forget(@Unit -> @Int)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Future<Result<String, String>> = async(Http.get("ftp://reclaim.invalid/x"));
  1
}

public fn spin(@Int -> @Int)
  requires(true) ensures(true) effects(<Http, Async>)
{
  if @Int.0 <= 0 then { 0 } else {
    let @Int = fire_and_forget(());
    spin(@Int.1 - 1)
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(<Http, Async>)
{ spin(200) }
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        result = _compile_ok(src)
        exec_result = execute(result)
        assert exec_result.value == 0
        store_size = exec_result.host_store_sizes.get("future", 0)
        assert store_size <= 2, (
            f"#841 regression: _future_store has {store_size} entries "
            f"after 200 fire-and-forget futures.  Phase 2c should fire "
            f"host_decref_handle(kind=4) for each unreachable wrapper; "
            f"a large residue means the kind-4 eviction (or the wrap-"
            f"table registration) is broken."
        )

    def test_future_wrapper_survives_operand_stack_window(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The wrap-site shadow push protects the operand-stack window:
        in ``both(async(A), async(B))`` the first wrapper sits on the
        operand stack while the second async's wrapper allocation runs
        — under eager GC that alloc collects, and an unrooted first
        wrapper is swept + Phase-2c-decref'd (its address is then
        typically reused for the second wrapper, aliasing the two
        futures).  The get/post pair makes the failure observable
        without a network: each future's Err text names its own op, so
        an aliased or reclaimed first future answers "Http.post:" or
        "already reclaimed" instead of "Http.get:".  This is the same
        #570/#692 operand-stack hazard the Decimal wrap push closes."""
        src = """
public fn both(@Future<Result<String, String>>, @Future<Result<String, String>> -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Result<String, String> = await(@Future<Result<String, String>>.1);
  let @Result<String, String> = await(@Future<Result<String, String>>.0);
  match @Result<String, String>.1 {
    Err(@String) -> if string_contains(@String.0, "Http.get:") then {
      match @Result<String, String>.0 {
        Err(@String) -> string_contains(@String.0, "Http.post:"),
        Ok(@String) -> false
      }
    } else { false },
    Ok(@String) -> false
  }
}

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  both(
    async(Http.get("ftp://a.invalid/1")),
    async(Http.post("ftp://b.invalid/2", "{}"))
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(src) == 1

    def test_repeated_await_of_same_future(self) -> None:
        """Awaiting the same future twice returns the same value both
        times (Future.result() memoizes; each await rebuilds a fresh
        Result ADT) — matching eager-await semantics."""
        src = """
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Future<Result<String, String>> = async(Http.get("ftp://twice.invalid/x"));
  let @Result<String, String> = await(@Future<Result<String, String>>.0);
  let @Result<String, String> = await(@Future<Result<String, String>>.0);
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> match @Result<String, String>.1 {
      Ok(@String) -> false,
      Err(@String) -> @String.0 == @String.1
    }
  }
}
"""
        assert _run(src) == 1


class TestHostImportPairLetRooting:
    """The plain-``let`` **pair-type** branch (String / Array<T> →
    (ptr, len) locals) in ``translate_block`` never shadow-pushed its
    pointer local — the last unrooted sibling of the #705 scalar-i32
    let fix and the #707 let-destruct pair fix (whose comment in
    ``vera/wasm/data.py`` already flagged this exact gap class).

    The hole is only observable for pairs a host import returns
    (``IO.args`` → Array<String>, ``IO.read_line`` → String): every
    Vera-side pair producer (array literal, string builtin) shadow-
    pushes its freshly-allocated ``dst`` during construction, and that
    push survives until the function epilogue, accidentally rooting the
    let.  A host import roots the block only host-side (``_ShadowGuard``
    in ``vera/runtime/heap.py``, popped on return), so after the
    ``local.set`` pair the block is invisible to the conservative scan.
    The next Vera-side alloc (``nat_to_string`` below) collects it, the
    free list overwrites the payload's first words, and reads through
    the still-live locals see corruption — pre-fix the args reproducer
    printed ``2::++2@`` instead of ``2:aa+bb``.  Found stress-testing
    #237 under ``VERA_EAGER_GC=1``; no WASI code involved.

    ``VERA_EAGER_GC`` is read at COMPILE time (``AssemblyMixin.
    _emit_alloc``), so ``monkeypatch.setenv`` before ``_compile_ok``
    bakes a collect into every ``$alloc``.
    """

    def test_eager_gc_io_args_let_survives_intervening_alloc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Primary reproducer: ``let @Array<String> = IO.args(())``
        followed by an allocating call.  Pre-fix the backing array is
        swept during ``nat_to_string``'s alloc — the free-list next-
        pointer lands in element 0's (ptr, len) slot and both element
        reads print reclaimed bytes."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  IO.print(nat_to_string(array_length(@Array<String>.0)));
  IO.print(":");
  IO.print(@Array<String>.0[0]);
  IO.print("+");
  IO.print(@Array<String>.0[1])
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="main", cli_args=["aa", "bb"])
        assert exec_result.stdout == "2:aa+bb"

    def test_eager_gc_io_args_string_join_after_intervening_alloc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``string_join`` over the swept backing array chases element
        (ptr, len) pairs that the free list has overwritten — pre-fix
        this printed separator-glued garbage like ``+\\x05+\\x1d@``."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  IO.print(nat_to_string(array_length(@Array<String>.0)));
  IO.print(string_join(@Array<String>.0, "+"))
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="main", cli_args=["aa", "bb"])
        assert exec_result.stdout == "2aa+bb"

    def test_eager_gc_read_line_let_survives_intervening_alloc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """String sibling of the args reproducer: ``IO.read_line``
        returns a host-allocated (ptr, len) pair let-bound through the
        same unrooted branch.  ``string_length`` reads only the len
        local, so the corruption window is purely ``nat_to_string``'s
        digit-string alloc sweeping the line's payload bytes."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(nat_to_string(string_length(@String.0)));
  IO.print(":");
  IO.print(@String.0)
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="main", stdin="hello\n")
        assert exec_result.stdout == "5:hello"

    def test_eager_gc_read_file_result_payload_survives_intervening_alloc(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        """Confirmation test for the neighbouring *rooted* paths: a
        ``Result<String, String>`` from ``IO.read_file`` is a scalar-i32
        ADT let (rooted by #705), and the ``Ok(@String)`` match-arm
        extraction is pair-rooted by the #707-era match/destructure
        fixes.  Green before and after the pair-let fix — pins the
        host-import ADT path the #237 stress testing already exercised."""
        target = tmp_path / "payload.txt"
        target.write_text("abc", encoding="utf-8")
        src = f"""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  let @Result<String, String> = IO.read_file("{target.as_posix()}");
  match @Result<String, String>.0 {{
    Ok(@String) -> {{
      IO.print(nat_to_string(string_length(@String.0)));
      IO.print(":");
      IO.print(@String.0)
    }},
    Err(@String) -> IO.print(@String.0)
  }}
}}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "3:abc"

    def test_eager_gc_get_env_option_payload_survives_intervening_alloc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Confirmation test, ``Option<String>`` shape: ``IO.get_env``
        allocates Some(String) host-side; the ADT let is #705-rooted and
        the ``Some(@String)`` payload extraction is match-arm rooted.
        Green before and after the pair-let fix."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<String> = IO.get_env("VERA_ROOTING_PROBE");
  match @Option<String>.0 {
    Some(@String) -> {
      IO.print(nat_to_string(string_length(@String.0)));
      IO.print(":");
      IO.print(@String.0)
    },
    None -> IO.print("unset")
  }
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        result = _compile_ok(src)
        exec_result = execute(
            result, fn_name="main",
            env_vars={"VERA_ROOTING_PROBE": "wombat"},
        )
        assert exec_result.stdout == "6:wombat"
