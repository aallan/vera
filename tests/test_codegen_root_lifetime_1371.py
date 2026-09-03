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


class TestCallResultsAreRootedWhereTheyLand1379:
    """The other half of the rule: a root must EXIST from the moment a value
    lands, not merely die when the value does.

    A call's result arrives on the operand stack, where the conservative scan
    cannot see it, so whatever is evaluated NEXT can allocate over it.  A Vera
    function's epilogue re-roots its return into the caller's shadow stack, so
    user calls were covered; a HOST import has no epilogue and was not.  In
    the emitted WAT the gap is literal: `call $vera.decimal_from_string`
    followed directly by the sibling argument's `call $alloc`, with no push
    between.

    Four Decimal builtins returned host-allocated heap results with a bare
    `call` and no root — `decimal_from_string` and `decimal_div` (an
    `Option<Decimal>` pointer), `decimal_compare` (an `Ordering` pointer) and
    `decimal_to_string`, whose result is a **(ptr, len) pair**.  The pair is
    why the rule reads its shape from `_stack_shape_of` rather than testing
    for "one i32": a rule keyed on the scalar case roots three of the four and
    silently misses the String.

    Every claim here is a PAD SWEEP, never a single layout.  #1382 showed a
    single-layout observation can inverate its own meaning, and two of these
    cells were green at one layout while being wrong at all of them — the
    earlier `decimal_to_string` cell passed only because it read the LENGTH,
    which survives a use-after-free that corrupts the bytes.  Measured over
    pad lengths 0..95, at this PR's base and at its head:

        cell                                base failing   head failing
        decimal_from_string (Option ptr)        96 / 96         0 / 96
        decimal_div (Option ptr)                96 / 96         0 / 96
        decimal_to_string (String pair)         96 / 96         0 / 96
        decimal_compare (Ordering ptr)           0 / 96         0 / 96

    `decimal_compare` is named by the audit and covered by the rule, but no
    cell reaching it could be constructed: its `Ordering` arms carry no heap
    payload to lose.  It stays as a control rather than as a claim.

    Six migrated Map / Set builtins (`map_new`, `map_insert`, `map_remove`,
    `set_new`, `set_add`, `set_remove`) carried a per-site `_emit_root_result`
    push for the same reason; the rule retires all six.  That it really covers
    them is shown by MUTATION, because the existing suites do not
    discriminate: with `_root_landed_value` disabled and the per-site pushes
    removed, `test_codegen_gc_rooting`, `test_codegen_gc_reclamation`,
    `test_codegen_gc_alloc` and `test_db_marshalling` stay green (123 tests)
    while three of the Map cells below die with a **bus error** — an unrooted
    wrapper corrupting memory outright rather than returning a wrong number.
    """

    @pytest.mark.parametrize(
        ("source", "expected"),
        [
            # #1379's own shape: an Option<Decimal> landing from a host
            # import while the sibling argument allocates.  Wrong at all 96
            # pad lengths at base.  The expected value is 1 against a
            # fallback of 0, and the fallback is what the defect produces.
            (
                """public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Decimal = option_unwrap_or(decimal_from_string("7"), decimal_from_int(0));
  if decimal_eq(@Decimal.0, decimal_from_int(7)) then { 1 } else { 0 }
}
""",
                1,
            ),
            # The same for `decimal_div`, whose Option is built by a
            # different host import.
            (
                """public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Decimal = option_unwrap_or(
      decimal_div(decimal_from_int(84), decimal_from_int(2)),
      decimal_from_int(0));
  if decimal_eq(@Decimal.0, decimal_from_int(42)) then { 1 } else { 0 }
}
""",
                1,
            ),
            # THE PAIR CELL.  `decimal_to_string` returns (ptr, len); only
            # the pointer half is a reference.  Asserted on CONTENT, with
            # same-sized churn allocations forcing block reuse — at base
            # this reads back '\x00\x00\x00\x005…' for '12345…', which a
            # length assertion would not have noticed.
            (
                """private fn churn(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(int_to_string(@Int.0 + 1000), int_to_string(@Int.0 + 2000))
}

""" + """public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(decimal_to_string(decimal_from_int(12345)),
                string_concat(string_concat(churn(1), churn(2)),
                              string_concat(churn(3), churn(4))))
}
""",
                "1234510012001100220021003200310042004",
            ),
            # A Map wrapper landing from a host import, the sibling key
            # allocating over it.  Bus error when unrooted.
            (
                """public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  map_size(map_insert(map_insert(map_new(), "a", 1),
                      string_concat("b", "c"), 2))
}
""",
                2,
            ),
            # The same wrapper read back through `map_get`, whose own key
            # argument allocates.
            (
                """public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match map_get(map_insert(map_new(), "k", 77), string_concat("k", "")) {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
""",
                77,
            ),
            # A landed wrapper consumed by a builtin that allocates its own
            # backing array.
            (
                """public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(map_values(map_insert(map_insert(map_new(), "a", 1),
                                     string_concat("b", "c"), 2)))
}
""",
                2,
            ),
            # CONTROL: a Vera function's result in the same position.  Its
            # epilogue already re-roots into the caller, so this holds with
            # or without the rule — it shows the rule did not have to change
            # the user-function path to cover the host one.
            (
                """private fn g(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{ string_concat("g", int_to_string(@Int.0)) }

private fn h(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{ string_concat("h", int_to_string(@Int.0)) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ string_length(string_concat(g(1), h(2))) }
""",
                4,
            ),
            # CONTROL: `decimal_compare`'s Ordering, which the audit names
            # but which carries no heap payload to lose.
            (
                """private fn churn(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(int_to_string(@Int.0 + 1000), int_to_string(@Int.0 + 2000))
}

""" + """public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match decimal_compare(decimal_from_int(1), decimal_from_int(2)) {
    Less -> string_concat("LT", string_concat(churn(1), churn(2))),
    Equal -> string_concat("EQ", churn(3)),
    Greater -> string_concat("GT", churn(4))
  }
}
""",
                "LT1001200110022002",
            ),
            # CONTROL: a Set wrapper chain — passes under both settings, so
            # it pins the shape without claiming to discriminate.
            (
                """public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  set_size(set_add(set_add(set_new(), string_concat("a", "1")),
                   string_concat("b", "2")))
}
""",
                2,
            ),
        ],
        ids=["decimal-from-string-1379", "decimal-div-1379",
             "decimal-to-string-pair", "map-insert-sibling-alloc",
             "map-get-sibling-alloc", "map-values-of-landed-wrapper",
             "control-user-fn-result", "control-decimal-compare",
             "control-set-add-chain"],
    )
    def test_a_landed_call_result_survives_a_sibling_allocation(
        self, source: str, expected: object, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert execute(_compile_ok(source), fn_name="main", args=[]).value == (
            expected
        )
