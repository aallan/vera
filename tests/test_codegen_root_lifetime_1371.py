"""#1371 — GC shadow roots lived for the FRAME, not for their value.

Every root a lowering made was reclaimed by one thing: the function
epilogue's ``$gc_sp`` restore, which runs once, on the way out.  So a frame
held a root for every heap pointer its body produced along the way, whether
or not any of them were still live — ``string_length(string_concat(s, "!"))``
repeated K times cost K permanent roots for K values that died immediately.
With the shadow stack at 4 096 roots (``GC_STACK_SIZE`` / 4) the depth a
recursion could reach became a function of how much its body allocated on
the way past, and overflow is a bare ``unreachable``: no diagnostic, no
location, on a program ``check`` and ``verify`` both pass.

#1322 was this defect in its match-shaped form and fixed it there.  This is
the same discipline generalised: an expression's roots live exactly as long
as the expression is forming its value, and a statement's live exactly as
long as the statement — after which what survives is what the statement
BOUND.  ``_scope_match_shadow_roots`` is gone; the match is now an ordinary
case of ``_scope_shadow_roots``.

The oracle is ROOTS PER FRAME across a K axis, in every syntactic position a
pointer-producing call can occupy.  Roots per frame rather than trap depth
because a frame holding *r* roots exhausts the stack at 4 096 / *r* levels,
so a raw depth also carries the outermost frame's own constant and would
read that constant as slope.  Two baselines, because #1322 landed between
them and already scoped one of these positions:

    position              pre-#1322    this PR's base    head
                          K=1/2/4      K=1/2/4           K=1/2/4
    block statements       2 / 3 / 5     2 / 3 / 5       1 / 1 / 1
    let right-hand side    2 / 3 / 5     2 / 3 / 5       1 / 1 / 1
    call arguments         3 / 5 / 9     3 / 5 / 9       1 / 1 / 1
    match arm bodies       4 / 7 / 13    1 / 1 / 1       1 / 1 / 1
    where-helper call      1 / 1 / 1     1 / 1 / 1       1 / 1 / 1
    handler clause body    1 / 1 / 1     1 / 1 / 1       1 / 1 / 1

Twelve of these cells are red at this PR's base and green at its head.

The bottom three rows are CONTROLS and they matter.  Match arm bodies are
#1322's own family, already flat at this base — kept because the general
discipline must not undo the special case it subsumes.  A helper call and a
handler clause each already scoped their roots through the callee's own
epilogue, so a family that MOVED there would mean this fix had reached
something that was not broken.  The one remaining root everywhere is the
frame's pointer parameter, which is genuinely live for the frame.
"""
from __future__ import annotations

import pytest

from vera.codegen import execute
from vera.codegen.assembly import GC_STACK_SIZE

from tests.codegen_helpers import _compile_ok


_SHADOW_ROOTS = GC_STACK_SIZE // 4

# Above the shadow-stack capacity, so "no trap in range" is distinguishable
# from "traps at one root per frame".
_CEILING = _SHADOW_ROOTS + 104

# A pointer-producing call whose value dies immediately: the String the
# concat allocates is consumed by `string_length` and is dead from there on.
_CALL = 'string_length(string_concat(@String.0, "!"))'


def _runs(source: str) -> bool:
    try:
        execute(_compile_ok(source), fn_name="main", args=[])
    except Exception:  # noqa: BLE001 - any trap counts as "did not run"
        return False
    return True


def _max_depth(make_source) -> int:
    if _runs(make_source(_CEILING)):
        return _CEILING
    lo, hi = 1, _CEILING
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if _runs(make_source(mid)):
            lo = mid
        else:
            hi = mid - 1
    return lo


def _roots_per_frame(make_source) -> int:
    """Shadow roots one recursive frame holds, from its trap depth.

    The physical quantity: a frame holding *r* roots traps at 4 096 / *r*
    levels.  The depth also carries the outermost frame's own constant,
    which does not repeat and which comparing raw depths would read as
    slope; rounding the ratio drops it and keeps the slope, which is what
    the defect moved.
    """
    return round(_SHADOW_ROOTS / _max_depth(make_source))


def _program(body: str, extra: str = ""):
    def make(depth: int) -> str:
        return f"""{extra}private fn depth(@String, @Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result >= 0)
  decreases(@Int.0)
  effects(pure)
{{
{body}
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


def _tail(inner: str) -> str:
    return (f"  if @Int.0 <= 0 then {{ 0 }} else {{ {inner}"
            "depth(@String.0, @Int.0 - 1) }")


def _block_statements(k: int):
    """K expression statements whose value is produced, then dropped."""
    return _program("\n".join(f"  {_CALL};" for _ in range(k))
                    + "\n" + _tail(""))


def _let_rhs(k: int):
    """K `let` right-hand sides that allocate to compute a scalar.

    The binding is `@Bool`, not `@Int`: a `let @Int` would shadow the
    parameter under De Bruijn indexing and the recursion below would read
    the binding instead of the counter.
    """
    return _program("\n".join(f"  let @Bool = {_CALL} > 0;" for _ in range(k))
                    + "\n" + _tail(""))


def _arguments(k: int):
    """K pointer-producing calls in ARGUMENT position of another call."""
    terms = " + ".join(
        ['string_length(string_concat(string_concat(@String.0, "!"), "y"))'] * k
    ) or "0"
    return _program(_tail(f"{terms} + "))


def _arm_bodies(k: int):
    """K match ARM bodies that allocate — #1322's family, re-measured."""
    terms = " + ".join([f"match @String.0 {{ @String -> {_CALL} }}"] * k) or "0"
    return _program(_tail(f"{terms} + "))


def _where_helper_call(k: int):
    """CONTROL: K calls to a helper that allocates internally.

    Already scoped before this change, by the callee's own epilogue.  A
    family that moved here would mean the fix had reached something that
    was not broken.
    """
    extra = f"""private fn helper(@String -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  {_CALL}
}}

"""
    terms = " + ".join(["helper(@String.0)"] * k) or "0"
    return _program(_tail(f"{terms} + "), extra)


def _handler_clause(k: int):
    """CONTROL: K pointer-producing calls inside a handler CLAUSE body."""
    terms = " + ".join([_CALL] * k) or "0"
    extra = f"""private fn clause_work(@String -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  handle[State<Int>](@Int = 0) {{
    get(@Unit) -> {{ resume({terms} + 0) }},
    put(@Int) -> {{ resume(()) }}
  }} in {{
    get(())
  }}
}}

"""
    return _program(_tail("clause_work(@String.0) + "), extra)


_MOVERS = [
    pytest.param(_block_statements, id="block-statements"),
    pytest.param(_let_rhs, id="let-rhs"),
    pytest.param(_arguments, id="call-arguments"),
    pytest.param(_arm_bodies, id="match-arm-bodies"),
]
_CONTROLS = [
    pytest.param(_where_helper_call, id="where-helper-call"),
    pytest.param(_handler_clause, id="handler-clause-body"),
]


class TestRootLifetimeIsScoped1371:
    """A frame's shadow cost must not grow with what its body produces."""

    @pytest.mark.parametrize("k", [2, 3, 4])
    @pytest.mark.parametrize("shape", _MOVERS + _CONTROLS)
    def test_frame_cost_does_not_rise_with_the_call_count(
        self, shape, k: int
    ) -> None:
        """K dead pointer-producing calls must cost what one costs.

        The differential the issue turns on.  At the branch point the four
        moving positions went 2 → 3 → 5, 2 → 3 → 5, 3 → 5 → 9 and
        4 → 7 → 13 roots per frame across K = 1, 2, 4.  Comparing against
        K=1 rather than pinning an absolute number keeps the assertion
        insensitive to how many roots the frame legitimately needs.
        """
        one = _roots_per_frame(shape(1))
        assert _roots_per_frame(shape(k)) == one, (
            f"{k} pointer-producing calls per frame cost more than one does "
            f"({one} root(s) per frame): a value's root still outlives the "
            "value (#1371)"
        )

    @pytest.mark.parametrize("shape", _MOVERS + _CONTROLS)
    def test_one_call_costs_only_the_parameter_root(self, shape) -> None:
        """The absolute floor, beside the differential.

        Equality across K also holds if every K cost the same WRONG number,
        which is what a fix that scoped nothing but made each call dearer
        would produce.  One root is the frame's pointer parameter, and
        nothing else survives.
        """
        assert _roots_per_frame(shape(1)) == 1, (
            "a frame holding one dead pointer-producing call keeps more "
            "than its parameter's root (#1371)"
        )


class TestScopedRestoreKeepsLiveValuesRooted1371:
    """The canary: a restore placed too eagerly is a use-after-free.

    These are #1322's three-property cells, carried forward because they are
    the instrument that fails when a scope reclaims something still live.
    Each needs all three of a value that is NOT `let`-bound (a `let` roots
    what it binds and would supply the missing root), a sibling argument that
    allocates while the value sits on the operand stack, and an assertion on
    CONTENT — a freed block nothing has overwritten yet still reads back
    correctly, so a length check passes on a genuine use-after-free.
    """

    @pytest.mark.parametrize(
        ("source", "expected"),
        [
            # A call result crossing an allocating sibling argument.
            (
                """public fn f(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(string_concat("seed", "-call"),
                string_concat("aabb", "ccdd"))
}
""",
                "seed-callaabbccdd",
            ),
            # Same, with several same-sized allocations forcing block reuse.
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
  string_concat(string_concat("seed", "-call"),
                string_concat(string_concat(churn(1), churn(2)),
                              string_concat(churn(3), churn(4))))
}
""",
                "seed-call10012001100220021003200310042004",
            ),
            # A `let` binding must survive allocations LATER in its block —
            # the statement scope re-roots it after reclaiming the
            # temporaries its right-hand side made.
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
  let @String = string_concat(string_concat("held", "-in"), "-let");
  let @Bool = string_length(string_concat(churn(5), churn(6))) > 0;
  string_concat(@String.0, string_concat(churn(7), churn(8)))
}
""",
                "held-in-let10072007" + "10082008",
            ),
            # An ADT pointer bound by a `let`, read back through a field
            # after further allocation.
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

private fn shown(@Wrap -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Wrap.0 { MkWrap(@String) -> @String.0 }
}

public fn f(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Wrap = MkWrap(string_concat("held", "-adt"));
  let @Bool = string_length(string_concat(churn(9), churn(1))) > 0;
  string_concat(shown(@Wrap.0), churn(2))
}
""",
                "held-adt10022002",
            ),
        ],
        ids=["call-result", "forced-block-reuse", "let-across-allocs",
             "adt-let-across-allocs"],
    )
    def test_value_content_survives_under_eager_gc(
        self, source: str, expected: str, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert execute(_compile_ok(source), fn_name="f", args=[]).value == (
            expected
        )
