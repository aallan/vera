"""#1322 — a `match` cost GC shadow roots for the whole FRAME.

``_translate_match`` rooted the scrutinee copy and every pattern binding on
the GC shadow stack, and nothing popped them: the only reclamation was the
function epilogue's ``$gc_sp`` restore, which runs once, at frame exit.  With
the shadow stack at 4 096 roots (``GC_STACK_SIZE`` / 4) that showed up as a
recursion ceiling, and overflow is a bare ``unreachable`` from
``gc_shadow_push``'s bound check — no diagnostic, no location, on a program
``check`` and ``verify`` both pass.

Two independent causes, both measured at the branch point:

1. **Duplicate roots.**  A pair (``String`` / ``Array<T>``) scrutinee was
   copied into a local and rooted, then the arm's binding copied *that* local
   and rooted it again — two extra roots for an address the producer had
   already rooted (a parameter in the prologue, an allocation at its
   ``$alloc``, a call's result in the callee's epilogue).  The shadow stack
   roots ADDRESSES, so the copies bought the mark phase nothing.  The issue's
   pair repro — ``match @String.0 { @String -> … }`` recursing inside the arm,
   allocating nothing at all — cost three roots per frame and trapped past
   depth **1 364**.

2. **Frame lifetime for arm-scoped roots.**  Everything a match rooted stayed
   rooted for the rest of the frame, so K *dead* sequential matches held K
   times the roots of one.  Measured over Int-valued matches on a pair
   scrutinee: no trap to 4 200 at K=0, then 1 365 at K=1, 819 at K=2, 455 at
   K=4 — two permanent roots per match.  Over a constructor FIELD binding,
   whose root IS load-bearing (#705/#707: the address lives in no other
   local) and is kept: 2 047 at K=1, 1 364 at K=2, 818 at K=4 — one per
   match.

The fix pairs the two: the duplicate pushes are gone, and what a match still
roots (a constructor field load, an allocation inside an arm body, the
scrutinee's own allocation) is now wrapped in the same ``$gc_sp`` save /
restore / re-root discipline the function epilogue applies (``gc_prologue`` /
``gc_epilogue`` in ``vera/codegen/functions.py``).

A match's net shadow cost is zero **when its result is not a heap pointer**,
which is the arm the K-axis cells below measure.  It is NOT zero when the
result IS one: the re-root that keeps that result alive is itself
frame-lifetime, so a pointer-valued match still costs one root, and K of them
still cost K — 2 047 / 1 365 / 819 at K = 1 / 2 / 4, against 1 023 / 585 / 315
before.  Three roots per match down to one is the whole of what this fix
claims there.  That residual is not a match defect at all: EVERY expression
that produces a heap pointer leaves a frame-lifetime root, because the
producer roots it and only the function epilogue ever pops.  It is tracked as
[#1371](https://github.com/aallan/vera/issues/1371), whose fix is this same
discipline applied per block statement — under which the block's own restore
reclaims the match's result and the per-match re-root becomes redundant.
``test_pointer_result_match_still_costs_one_root_each`` pins the residual so
that change is a visible flip rather than a silent one.

The proving instrument is the K axis, not one absolute depth: a single-depth
test passes on a fix that merely makes each match cheaper.  The K-axis
programs deliberately avoid ``let``-binding the match result — a ``let``'s
root is *correctly* frame-scoped (the binding is live to the end of its
block), so K lets cost K roots on any correct implementation and would mask
the axis being measured.
"""
from __future__ import annotations

import pytest

from vera.codegen import execute
from vera.codegen.assembly import GC_STACK_SIZE

from tests.codegen_helpers import _compile_ok


# Roots the shadow stack holds: four bytes each.
_SHADOW_ROOTS = GC_STACK_SIZE // 4

# One root per frame is the floor for these programs: the pointer parameter,
# rooted by the function prologue and live for the whole frame.
_FLOOR_DEPTH = _SHADOW_ROOTS - 2

# Above the floor, so "no trap in range" is distinguishable from "traps at the
# floor" without the probe itself running out of shadow stack.
_CEILING = _SHADOW_ROOTS + 104


def _runs(source: str) -> bool:
    """Whether the program executes to completion (no shadow-stack trap)."""
    try:
        execute(_compile_ok(source), fn_name="main", args=[])
    except Exception:  # noqa: BLE001 - any trap counts as "did not run"
        return False
    return True


def _max_depth(make_source, ceiling: int = _CEILING) -> int:
    """Greatest recursion depth at which *make_source(depth)* still runs."""
    if _runs(make_source(ceiling)):
        return ceiling
    lo, hi = 1, ceiling
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if _runs(make_source(mid)):
            lo = mid
        else:
            hi = mid - 1
    return lo


def _roots_per_frame(make_source) -> int:
    """Shadow roots one recursive frame holds, from its trap depth.

    The physical quantity, rather than the depth itself.  A frame holding
    *r* roots exhausts a 4 096-root stack at 4 096 / *r* levels, so the
    depth also carries a small CONSTANT — the roots the outermost frame
    holds, which do not repeat — and comparing raw depths would read that
    constant as slope: the allocating-scrutinee family measures 4 095 at
    K=1 and 4 093 at K=4, both of which are one root per frame.  Rounding
    the ratio drops the constant and keeps the slope, which is the thing
    the defect moved (1 → 4 → 7 → 13).
    """
    return round(_SHADOW_ROOTS / _max_depth(make_source))


def _int_valued_matches(k: int):
    """K matches per frame whose results are Ints — no let, no pointer result.

    Isolates the roots the MATCH holds from roots a ``let`` binding or a
    pointer-valued result legitimately holds.
    """
    terms = " + ".join(
        "match @String.0 { @String -> string_length(@String.0) }"
        for _ in range(k)
    ) or "0"

    def make(depth: int) -> str:
        return f"""private fn depth(@String, @Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result >= 0)
  decreases(@Int.0)
  effects(pure)
{{
  if @Int.0 <= 0 then {{ 0 }} else {{ {terms} + depth(@String.0, @Int.0 - 1) }}
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  depth("x", {depth})
}}
"""
    return make


def _allocating_scrutinee_matches(k: int):
    """K matches per frame whose SCRUTINEE allocates.

    The shape that makes the snapshot's placement load-bearing: taken
    before the scrutinee, the scrutinee's own allocation is reclaimed with
    the arm; taken after it, that allocation would keep its frame-lifetime
    root and this family would still fall with K.  Both other families use
    non-allocating scrutinees and cannot tell the two placements apart.
    """
    terms = " + ".join(
        'match string_concat(@String.0, "!") '
        "{ @String -> string_length(@String.0) }"
        for _ in range(k)
    ) or "0"

    def make(depth: int) -> str:
        return f"""private fn depth(@String, @Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result >= 0)
  decreases(@Int.0)
  effects(pure)
{{
  if @Int.0 <= 0 then {{ 0 }} else {{ {terms} + depth(@String.0, @Int.0 - 1) }}
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  depth("x", {depth})
}}
"""
    return make


def _pointer_result_matches(k: int):
    """K matches per frame whose RESULT is a heap pointer.

    Written against #1322's head as the arm where the cost was NOT zero: the
    re-root carrying the result past the match was itself frame-lifetime, so
    each match left one root behind (2 / 3 / 5 roots per frame at K = 1 / 2 /
    4, from 4 / 7 / 13 before that fix).  #1371 generalises the same
    discipline to every expression and every block statement, so the
    enclosing scope now reclaims that result and this shape is flat at one —
    the frame's own parameter root — like the three beside it.  It joins the
    family list for that reason, and keeps its own cell because the flip is
    the point.
    """
    terms = " + ".join(
        'string_length(match @String.0 '
        '{ @String -> string_concat(@String.0, "!") })'
        for _ in range(k)
    ) or "0"

    def make(depth: int) -> str:
        return f"""private fn depth(@String, @Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result >= 0)
  decreases(@Int.0)
  effects(pure)
{{
  if @Int.0 <= 0 then {{ 0 }} else {{ {terms} + depth(@String.0, @Int.0 - 1) }}
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  depth("x", {depth})
}}
"""
    return make


def _pair_scrutinee_recursion(depth: int) -> str:
    """The issue's pair-scrutinee repro: recursion INSIDE the arm.

    Allocates nothing — every root in the frame is a root the match itself
    put there.  Trapped past depth 1 364 at the branch point.
    """
    return f"""private fn depth(@String, @Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result >= 0)
  decreases(@Int.0)
  effects(pure)
{{
  match @String.0 {{
    @String -> if @Int.0 <= 0 then {{ 0 }} else {{ 1 + depth(@String.0, @Int.0 - 1) }}
  }}
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  depth("x", {depth})
}}
"""


def _adt_field_matches(k: int):
    """K matches per frame binding a constructor's ``String`` FIELD.

    A different push from the pair scrutinee's, and one this fix KEEPS: a
    field load produces an address that lives in no other local, so #705/#707
    are load-bearing there.  What changes is its lifetime — arm, not frame.
    """
    terms = " + ".join(
        "match @Wrap.0 { MkWrap(@String) -> string_length(@String.0) }"
        for _ in range(k)
    ) or "0"

    def make(depth: int) -> str:
        return f"""private data Wrap {{
  MkWrap(String)
}}

private fn depth(@Wrap, @Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result >= 0)
  decreases(@Int.0)
  effects(pure)
{{
  if @Int.0 <= 0 then {{ 0 }} else {{ {terms} + depth(@Wrap.0, @Int.0 - 1) }}
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  depth(MkWrap("x"), {depth})
}}
"""
    return make


class TestMatchCostsNoShadowRoots1322:
    """A match's net shadow-stack cost, measured rather than inferred."""

    @pytest.mark.parametrize("k", [2, 3, 4])
    @pytest.mark.parametrize(
        "shape",
        [
            _int_valued_matches,
            _adt_field_matches,
            _allocating_scrutinee_matches,
            _pointer_result_matches,
        ],
        ids=["pair-scrutinee", "adt-field-binding", "allocating-scrutinee",
             "pointer-result"],
    )
    def test_frame_cost_does_not_rise_with_the_match_count(
        self, shape, k: int
    ) -> None:
        """K dead matches per frame must cost what one match costs.

        The differential the issue turns on.  At the branch point the three
        shapes went 1 365 → 819 → 455, 2 047 → 1 364 → 818 and
        1 023 → 585 → 315 across K = 1, 2, 4 — every additional dead match
        cost permanent roots.  Comparing against K=1 (rather than pinning
        an absolute depth) keeps the assertion insensitive to how many
        roots the frame legitimately needs, and roots-per-frame rather than
        depth drops the outermost frame's own constant.

        The four shapes exercise four different roots.  The pair
        scrutinee's copies are DELETED by this fix; the constructor field
        binding's root is load-bearing (#705/#707) and is KEPT, only
        re-scoped; the allocating scrutinee's own allocation is what makes
        the snapshot's placement before the scrutinee load-bearing; and the
        pointer RESULT's re-root, which #1322 left frame-lifetime, is
        reclaimed by the enclosing scope under #1371.
        """
        one = _roots_per_frame(shape(1))
        assert _roots_per_frame(shape(k)) == one, (
            f"{k} matches per frame cost more than one match does "
            f"({one} root(s) per frame): a match still holds its shadow "
            "roots for the whole frame (#1322)"
        )

    @pytest.mark.parametrize("k", [1, 2, 4])
    def test_a_pointer_valued_match_no_longer_costs_a_root(
        self, k: int
    ) -> None:
        """The residual #1322 left behind, now gone — the #1371 flip.

        This cell was written against #1322's head as a MEASUREMENT of what
        that fix did not reach: the re-root carrying an arm's result past
        the match was itself frame-lifetime, so K pointer-valued matches
        left K roots (4 → 7 → 13 roots per frame at the branch point,
        2 → 3 → 5 after #1322).  #1371 generalises the same discipline to
        every expression and every block statement, so the enclosing scope
        reclaims that result and the count is flat at one — the frame's own
        parameter root — like every other family above.

        Kept as its own cell rather than folded into the family list it now
        joins, because it is the one whose flip is the point.
        """
        assert _roots_per_frame(_pointer_result_matches(k)) == 1, (
            "a pointer-valued match still leaves a frame-lifetime root at "
            f"K={k}: #1371's block-statement scoping should reclaim it"
        )

    def test_issue_repro_pair_scrutinee_passes_its_measured_ceiling(
        self,
    ) -> None:
        """``match @String.0`` recursing inside the arm, allocating nothing.

        Three roots per frame at the branch point (the prologue's parameter
        root plus the scrutinee copy and the binder copy) → 1 364.  With
        the duplicate roots gone it is the parameter root alone.
        """
        depth = _max_depth(_pair_scrutinee_recursion)
        assert depth >= _FLOOR_DEPTH, (
            f"a pair-scrutinee match that allocates nothing still traps at "
            f"depth {depth}, short of the {_FLOOR_DEPTH} its one live root "
            "allows (#1322)"
        )

    def test_a_field_binding_frame_reaches_the_shadow_stack_bound(
        self,
    ) -> None:
        """One field-binding match per frame costs only the parameter root.

        2 047 at the branch point — the parameter root plus the field's,
        both held for the frame.  The field's root is still emitted; it is
        reclaimed at arm exit.
        """
        depth = _max_depth(_adt_field_matches(1))
        assert depth >= _FLOOR_DEPTH, (
            f"a field-binding match still traps at depth {depth}, short of "
            f"the {_FLOOR_DEPTH} its one live root allows (#1322)"
        )


class TestMatchResultReRootIsLoadBearing1322:
    """The re-root the restore adds back is LOAD-BEARING, shown by mutation.

    Two pushes were deleted in this fix for being duplicates and one was
    added; the two claims need different evidence, and only this class
    carries the second.  Delete the ``gc_shadow_push`` from the restore in
    ``_scope_match_shadow_roots`` and every cell below reads back a
    freed-and-REUSED block:

        'aabbccddaabbccdd'                       for 'seed-armaabbccdd'
        '\x00\x00\x00\x00-arm1001200110022002…'   for 'seed-arm1001…'
        '"@\x01\x00-x100520051006…'              for 'held-x1005…'

    Three properties make them discriminating where the suite's other GC
    cells are not.

    * The match's result is NOT `let`-bound.  A `let` roots what it binds,
      so any cell that binds the result first has a second root and cannot
      see the missing one — which is why the result-survival cells in
      `TestMatchScopeKeepsResultsRooted1322` stay green under the mutation.
    * A SIBLING argument allocates after the match result is on the operand
      stack, where the conservative scan cannot see it.  `VERA_EAGER_GC=1`
      turns that allocation into a collection.
    * The assertion is on CONTENT, not length.  A freed block whose bytes
      nothing has overwritten yet still reads back correctly, so a length
      or a numeric check passes on a genuine use-after-free; these force
      reuse with same-sized allocations of different content, so the wrong
      bytes are the ones that come back.
    """

    @pytest.mark.parametrize(
        ("source", "expected"),
        [
            # One allocating sibling argument.
            (
                """public fn f(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(match "seed" { @String -> string_concat(@String.0, "-arm") },
                string_concat("aabb", "ccdd"))
}
""",
                "seed-armaabbccdd",
            ),
            # Several same-sized allocations, to force reuse of the block.
            (
                """private fn churn(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(int_to_string(@Int.0 + 1000), int_to_string(@Int.0 + 2000))
}

public fn f(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(match "seed" { @String -> string_concat(@String.0, "-arm") },
                string_concat(string_concat(churn(1), churn(2)),
                              string_concat(churn(3), churn(4))))
}
""",
                "seed-arm10012001100220021003200310042004",
            ),
            # An ADT pointer result, read back through a field after the
            # allocations — the i32 half of the restore's re-root.
            (
                """private data Wrap {
  MkWrap(String)
}

private fn churn(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(int_to_string(@Int.0 + 1000), int_to_string(@Int.0 + 2000))
}

private fn shown(@Wrap, @String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Wrap.0 { MkWrap(@String) -> string_concat(@String.0, @String.1) }
}

public fn f(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  shown(match MkWrap("held") {
          MkWrap(@String) -> MkWrap(string_concat(@String.0, "-x"))
        },
        string_concat(string_concat(churn(5), churn(6)), churn(7)))
}
""",
                "held-x100520051006200610072007",
            ),
        ],
        ids=["one-sibling-alloc", "forced-block-reuse", "adt-result"],
    )
    def test_result_content_survives_an_allocating_sibling_argument(
        self, source: str, expected: str, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert execute(_compile_ok(source), fn_name="f", args=[]).value == (
            expected
        )


class TestMatchScopeKeepsResultsRooted1322:
    """Reclaiming the match's roots must not un-root what the match RETURNS."""

    @pytest.mark.parametrize(
        ("source", "expected"),
        [
            # A pair (ptr, len) result built inside the arm, then allocated
            # over before it is read: the restore must re-root the pointer
            # half.
            (
                """public fn f(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @String = match "seed" { @String -> string_concat(@String.0, "-arm") };
  string_concat(@String.0, string_concat("a", "b"))
}
""",
                "seed-armab",
            ),
            # An ADT pointer result built inside the arm, then allocated over
            # before it is read back.
            (
                """private data Box {
  MkBox(Int)
}

private fn unbox(@Box -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Box.0 {
    MkBox(@Int) -> @Int.0
  }
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Box = match MkBox(41) { MkBox(@Int) -> MkBox(@Int.0 + 1) };
  let @String = string_concat("filler", "-alloc");
  unbox(@Box.0) + string_length(@String.0)
}
""",
                42 + 12,
            ),
            # A pointer bound by a constructor FIELD load — the push #705/#707
            # added, which is load-bearing (the address lives in no other
            # local) and must survive an allocation inside the same arm.
            (
                """private data Wrap {
  MkWrap(String)
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match MkWrap(string_concat("held", "-value")) {
    MkWrap(@String) ->
      string_length(string_concat("pressure", "-alloc"))
        + string_length(@String.0)
  }
}
""",
                len("pressure-alloc") + len("held-value"),
            ),
            # A nested match: the inner match's restore must not reclaim the
            # outer arm's bindings.
            (
                """private data Wrap {
  MkWrap(String)
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match MkWrap(string_concat("outer", "-held")) {
    MkWrap(@String) ->
      match string_concat("inner", "-held") {
        @String -> string_length(@String.0) + string_length(@String.1)
      }
  }
}
""",
                len("inner-held") + len("outer-held"),
            ),
        ],
        ids=["pair-result", "adt-result", "field-binding", "nested-match"],
    )
    def test_value_survives_an_allocation_in_the_same_frame(
        self, source: str, expected: object
    ) -> None:
        assert execute(_compile_ok(source), fn_name="f", args=[]).value == (
            expected
        )
