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

import functools
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

from vera.codegen import execute
from vera.codegen.assembly import GC_STACK_SIZE
from vera.environment import TypeEnv
from vera.types import AdtType, PrimitiveType

from tests.codegen_helpers import _compile_ok


# Data-section padding: an unused function holding one string literal, which
# moves `gc_heap_start` without adding an allocation or a root.  #1382 is
# selected by the heap BASE, so a GC claim measured at ONE layout can invert
# its own meaning; every load-bearing cell below is swept across these.
# Eight lengths covering every residue mod 8 — the alignment classes the heap
# layout can land in — rather than one arbitrary length.  (Development sweeps
# ran 0..95; these eight are what ships, to keep the suite's runtime sane.)
_PADS = (0, 1, 2, 3, 4, 5, 6, 7)


def _with_pad(source: str, pad: int) -> str:
    if not pad:
        return source
    return source + (
        "\npublic fn pad(-> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        f'  string_length("{"q" * pad}")\n'
        "}\n"
    )


def _run_in_subprocess(source: str, tmp_path: Path) -> tuple[int, str]:
    """Run *source* under `vera run` in a CHILD process, returning (rc, out).

    Some rooting failures are not wrong VALUES but memory corruption: an
    unrooted Map wrapper takes the interpreter down with SIGBUS.  In-process
    `execute()` would kill the pytest worker — under `-n auto` that reads as
    a lost worker rather than as a failed assertion, and the run reports
    nothing about which cell died.  A child process turns the same crash
    into a non-zero return code that an ordinary assertion can name.
    """
    src = tmp_path / "cell.vera"
    src.write_text(source, encoding="utf-8")
    # EXTEND the inherited environment rather than replacing it: a bare
    # replacement drops SYSTEMROOT, which Windows needs before Python even
    # starts, and the failure would then read as an unrooted wrapper.
    env = dict(os.environ)
    env["VERA_EAGER_GC"] = "1"
    env["PYTHONPATH"] = str(Path(__file__).resolve().parents[1])
    proc = subprocess.run(
        [sys.executable, "-m", "vera.cli", "run", str(src)],
        check=False,  # a crash IS the observation; the caller asserts on rc
        capture_output=True, text=True, encoding="utf-8", env=env,
    )
    return proc.returncode, (proc.stdout or "").strip()


_SHADOW_ROOTS = GC_STACK_SIZE // 4

# Above the shadow-stack capacity, so "no trap in range" is distinguishable
# from "traps at one root per frame".
_CEILING = _SHADOW_ROOTS + 104

# A pointer-producing call whose value dies immediately: the String the
# concat allocates is consumed by `string_length` and is dead from there on.
_CALL = 'string_length(string_concat(@String.0, "!"))'


def _runs(source: str) -> bool:
    """Whether the program executes to completion (no shadow-stack trap).

    The compile step is deliberately OUTSIDE the guard: `_compile_ok` raises
    `AssertionError` for a compile error, and swallowing that would report a
    program that stopped compiling as one that "costs more than one root per
    frame" — a measurement failure disguised as a measurement.
    """
    compiled = _compile_ok(source)
    try:
        execute(compiled, fn_name="main", args=[])
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


@functools.lru_cache(maxsize=None)
def _roots_per_frame_cached(key: object, make_source) -> int:
    return round(_SHADOW_ROOTS / _max_depth(make_source))


def _roots_per_frame(make_source) -> int:
    """Shadow roots one recursive frame holds, from its trap depth.

    The physical quantity: a frame holding *r* roots traps at 4 096 / *r*
    levels.  The depth also carries the outermost frame's own constant,
    which does not repeat and which comparing raw depths would read as
    slope; rounding the ratio drops it and keeps the slope, which is what
    the defect moved.
    """
    return _roots_per_frame_cached(
        getattr(make_source, "__cache_key__", make_source), make_source)


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
    single-layout observation can invert its own meaning, and one of these
    cells was green at one layout while being wrong at all of them — the
    earlier `decimal_to_string` cell passed only because it read the LENGTH,
    which survives a use-after-free that corrupts the bytes.

    WHICH HALF EACH CELL DISCRIMINATES.  Being red at the base is not the
    same as discriminating the LANDING half, because the base had neither
    half.  Disabling `_root_landed_value` alone and re-sweeping separates
    them, and most of the Decimal cells turn out to pin the STATEMENT /
    BINDING half — their results are `let`-bound, so the binding scope roots
    them even with landing rooting gone:

        cell                          base    landing-half OFF   head
        decimal_from_string           96/96        96/96         0/96
        decimal_div                   96/96         0/96         0/96
        decimal_to_string (pair)      96/96         0/96         0/96
        nested host call              96/96          —           0/96
        decimal_compare (control)      0/96          —           0/96

    So the LANDING half is carried by `decimal_from_string`, by the nested
    host-call cell (whose intermediate is never bound), by the three Map
    cells below, and above all by `TestEveryHeapReturningHostCallIsRooted`,
    which is structural and cannot crash.  `decimal_div` and
    `decimal_to_string` remain valuable — they pin the binding half over
    host-call results — but they are not evidence for the landing rule, and
    labelling them as such would have made the retirement of the six
    per-site pushes rest on cells that do not test it.

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
            # NESTED host calls: the `decimal_div` Option and the
            # `option_unwrap_or` Decimal are both intermediates that are
            # never bound, so only the LANDING rule can root them.  96/96
            # red at base, 0/96 at head.
            (
                """private fn churn(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(int_to_string(@Int.0 + 1000), int_to_string(@Int.0 + 2000))
}

public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(
    decimal_to_string(option_unwrap_or(
      decimal_div(decimal_from_int(84), decimal_from_int(2)),
      decimal_from_int(0))),
    string_concat(string_concat(churn(1), churn(2)), churn(3)))
}
""",
                "42100120011002200210032003",
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
             "decimal-to-string-pair", "nested-host-calls",
             "control-user-fn-result", "control-decimal-compare",
             "control-set-add-chain"],
    )
    @pytest.mark.parametrize("pad", _PADS)
    def test_a_landed_call_result_survives_a_sibling_allocation(
        self, source: str, expected: object, pad: int,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        result = execute(
            _compile_ok(_with_pad(source, pad)), fn_name="main", args=[])
        assert result.value == expected


class TestCrashingCellsRunOutOfProcess1379:
    """Cells whose failure mode is memory corruption, not a wrong value.

    An unrooted Map wrapper does not return the wrong number — it takes the
    process down with SIGBUS.  Run in-process that would kill the pytest
    worker, which under `-n auto` reports as a lost worker rather than as a
    named failing cell, so these go through a child `vera run`: the same
    crash becomes a non-zero return code an ordinary assertion can report.

    These three are also the cells that carry the LANDING half for the Map /
    Set family, so losing them to a crash would quietly remove the evidence
    that retiring the six per-site `_emit_root_result` pushes is safe.
    """

    @pytest.mark.parametrize(
        ("source", "expected"),
        [
            # A Map wrapper landing from a host import, the sibling key
            # allocating over it.
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
                "2",
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
                "77",
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
                "2",
            ),
        ],
        ids=["map-insert-sibling-alloc", "map-get-sibling-alloc",
             "map-values-of-landed-wrapper"],
    )
    @pytest.mark.parametrize("pad", _PADS)
    def test_a_landed_wrapper_survives_out_of_process(
        self, source: str, expected: str, pad: int, tmp_path: Path,
    ) -> None:
        rc, out = _run_in_subprocess(_with_pad(source, pad), tmp_path)
        assert rc == 0, (
            f"`vera run` exited {rc} (a negative code is a signal: an "
            f"unrooted wrapper corrupts memory rather than returning a wrong "
            f"value).  stdout: {out!r}"
        )
        assert out == expected, f"got {out!r}, want {expected!r}"


# The scalar primitives, whose returns are values rather than references.
_SCALAR_RETURNS = frozenset({"Int", "Nat", "Bool", "Byte", "Float64", "Unit"})

# The wrapper families whose host calls this pin MUST observe.  Derived from
# the registry rather than written out, so a heap-returning builtin added to
# one of them fails here until the fixture exercises it.
_WRAPPER_FAMILIES = ("decimal", "map", "set")

_PUSH_OF = re.compile(r"global\.get \$gc_sp\s+local\.get (\d+)\s+i32\.store")
# Map / Set host imports are type-specialised — `map_values$vi`,
# `map_insert$si` — so the builtin name is the part before the `$`.
_HOST_CALL = re.compile(r"call \$vera\.([A-Za-z0-9_]+)(?:\$[A-Za-z0-9_]+)?")


def _heap_returning_builtins() -> set[str]:
    """Builtins whose declared return type is heap-represented.

    From `TypeEnv`, not a hand list: a hand list is exactly what the six
    per-site `_emit_root_result` pushes were, and what let the Decimal
    siblings beside them go unrooted for as long as they did.
    """
    out: set[str] = set()
    for name, info in TypeEnv().functions.items():
        ret = info.return_type
        if isinstance(ret, PrimitiveType) and ret.name not in _SCALAR_RETURNS:
            out.add(name)
        elif isinstance(ret, AdtType):
            out.add(name)
    return out


# Every heap-returning host call below sits in ARGUMENT position, never as a
# `let` right-hand side: a bound result is rooted by the statement scope, so
# a `let`-shaped fixture stays green with the landing rule disabled and pins
# nothing.  Measured — as `let`s this fixture reports zero unrooted sites
# either way; as arguments it reports seven with the rule off.
_HOST_CALL_FIXTURE = """\
public fn exercise(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_length(decimal_to_string(decimal_round(decimal_abs(decimal_neg(
    decimal_mul(decimal_sub(decimal_add(decimal_from_int(7),
      decimal_from_float(2.5)), decimal_from_int(1)), decimal_from_int(3)))), 2)))
  + option_map_len(decimal_from_string("1.5"))
  + option_map_len(decimal_div(decimal_from_int(8), decimal_from_int(2)))
  + ordering_code(decimal_compare(decimal_from_int(1), decimal_from_int(2)))
  + map_size(map_remove(map_insert(map_new(), "k", 1), "k"))
  + opt_int(map_get(map_insert(map_new(), "j", 5), "j"))
  + array_length(map_keys(map_insert(map_new(), "a", 1)))
  + array_length(map_values(map_insert(map_new(), "b", 2)))
  + set_size(set_remove(set_add(set_new(), 1), 1))
  + array_length(set_to_array(set_add(set_new(), 9)))
}

private fn option_map_len(@Option<Decimal> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Option<Decimal>.0 {
    Some(@Decimal) -> string_length(decimal_to_string(@Decimal.0)),
    None -> 0
  }
}

private fn ordering_code(@Ordering -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Ordering.0 { Less -> 1, Equal -> 2, Greater -> 3 }
}

private fn opt_int(@Option<Int> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> 0 }
}
"""


def _audit_host_call_rooting(wat: str) -> tuple[set[str], list[tuple[str, str]]]:
    """Every heap-returning host call in *wat*, and those left unrooted.

    A call site is rooted when its result is captured into a local and that
    local is shadow-pushed within the window before the next allocation —
    OR, for the #573 wrap/unwrap builtins, when the raw HANDLE the host
    returned is consumed by a `$register_wrapper` sequence whose wrapper
    pointer is pushed instead.  That second case is not an exemption: the
    handle is not a heap pointer, and rooting it would root the wrong thing.
    """
    names = _heap_returning_builtins()
    lines = [line.strip() for line in wat.splitlines()]
    observed: set[str] = set()
    unrooted: list[tuple[str, str]] = []
    for i, line in enumerate(lines):
        match = _HOST_CALL.fullmatch(line)
        if not match or match.group(1) not in names:
            continue
        name = match.group(1)
        observed.add(name)
        window = lines[i + 1:i + 41]
        # Truncate at the first allocation that could collect this result.
        # The rule is that the result is rooted BEFORE anything can collect
        # it, so a push emitted after an intervening `call $alloc` is the
        # defect this pins and an untruncated window would accept it.
        #
        # The #573 wrap/unwrap builtins need the boundary one allocation
        # later: the host returned a raw HANDLE, and the `$alloc` right after
        # the call IS the wrapping — it is what BUILDS the value to be
        # rooted, not something that can collect it.  So when the window
        # wraps, the boundary is the first allocation AFTER
        # `$register_wrapper`.  Truncating at the wrap's own `$alloc`
        # reported all twelve Decimal call sites as unrooted.
        wrap_at = next(
            (n for n, e in enumerate(window)
             if e.startswith("call $register_wrapper")), None)
        first = 0 if wrap_at is None else wrap_at + 1
        for stop in range(first, len(window)):
            if window[stop].startswith("call $alloc"):
                window = window[:stop]
                break
        captured: list[int] = []
        for entry in window:
            set_match = re.fullmatch(r"local\.set (\d+)", entry)
            if not set_match:
                break
            captured.append(int(set_match.group(1)))
        if not captured:
            unrooted.append((name, "result not captured into a local"))
            continue
        # A pair pops its length first, so the pointer half is set last.
        ptr_local = captured[-1]
        text = "\n".join(window)
        pushed = {int(x) for x in _PUSH_OF.findall(text)}
        if ptr_local in pushed:
            continue
        if "call $register_wrapper" in text and pushed:
            continue
        unrooted.append((name, f"local {ptr_local} is never pushed"))
    return observed, unrooted


class TestEveryHeapReturningHostCallIsRooted1379:
    """The structural pin: no host call may leave a heap result unrooted.

    The behavioural cells above each exercise one builtin, and three of them
    can only fail by crashing.  This one asks the emitted WAT the general
    question instead, over a set derived from `TypeEnv` rather than written
    by hand — so it cannot crash, and a heap-returning builtin added later
    is covered without anyone remembering to add a cell.

    Validated by mutation: with `_root_landed_value` disabled it reports
    seven unrooted sites (`decimal_from_string`, four `map_new`, two
    `set_new`); with the rule on, zero.
    """

    def test_no_heap_returning_host_call_is_left_unrooted(self) -> None:
        wat = _compile_ok(_HOST_CALL_FIXTURE).wat
        _observed, unrooted = _audit_host_call_rooting(wat)
        assert not unrooted, (
            "heap-returning host calls whose result is never rooted, so the "
            "next allocation can sweep it: "
            + "; ".join(f"{n} ({why})" for n, why in unrooted)
        )

    def test_the_fixture_exercises_every_wrapper_family_builtin(self) -> None:
        """Non-vacuity, and a gate on new builtins.

        The assertion above holds trivially over a fixture that calls
        nothing.  The wrapper families are where the per-site pushes lived
        and where the Decimal gap was, so every heap-returning builtin in
        them must appear — a new one fails here until the fixture calls it.
        """
        expected = {
            name for name in _heap_returning_builtins()
            if name.split("_")[0] in _WRAPPER_FAMILIES
        }
        observed, _unrooted = _audit_host_call_rooting(
            _compile_ok(_HOST_CALL_FIXTURE).wat)
        missing = expected - observed
        assert not missing, (
            f"the fixture does not exercise {sorted(missing)}, so the pin "
            "says nothing about them"
        )
        assert len(expected) >= 20, (
            f"only {len(expected)} wrapper-family builtins return a heap "
            "value; the registry derivation has probably broken"
        )


# Functions that emit `gc_shadow_push` without assigning `needs_alloc`, and
# are correct anyway.  Each is guarded by construction, not by remembering:
_NEEDS_ALLOC_EXEMPT = {
    # Both emit their pushes inside an `if ctx.needs_alloc:` block — the
    # flag is the precondition for the prologue existing at all.
    "vera/codegen/functions.py:_compile_fn",
    "vera/codegen/closures.py:_compile_lifted_closure",
    # The scoping wrapper only runs when the lowering it wraps ALREADY
    # pushed, and it raises `CodegenInvariantError` if the flag is unset.
    "vera/wasm/context.py:_scope_shadow_roots",
}


def _push_sites_without_needs_alloc() -> list[str]:
    """Every function emitting `gc_shadow_push` that never sets the flag."""
    import ast

    root = Path(__file__).resolve().parents[1]
    offenders: list[str] = []
    for path in sorted((root / "vera").rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            pushes = [
                n for n in ast.walk(node)
                if isinstance(n, ast.Call)
                and getattr(n.func, "id", "") == "gc_shadow_push"
            ]
            if not pushes:
                continue
            sets_flag = any(
                isinstance(n, ast.Assign)
                and any(isinstance(t, ast.Attribute)
                        and t.attr == "needs_alloc" for t in n.targets)
                for n in ast.walk(node)
            )
            if not sets_flag:
                rel = path.relative_to(root).as_posix()
                offenders.append(f"{rel}:{node.name}")
    return offenders


class TestEveryPushSiteDeclaresTheGlobal1376:
    """`needs_alloc` is what declares `$gc_sp`; a push without it is a bug.

    #1376 was one instance — five `show`/`hash` sites pushed without setting
    the flag, so `hash(@Tuple<Int, Int>.0)` in a module whose only
    GC-touching lowering was that hash emitted a reference to an undeclared
    global and failed to compile.  Review then found four more of the same
    shape (`array_fold`, `array_any`/`array_all`, the Decimal wrap, the
    show/hash helper frame).  Nine sites over two rounds is a discipline no
    one can hold by hand, so it is checked instead of remembered.

    A structural sweep rather than a behavioural probe, because a site's
    reachability depends on whether anything ELSE in the module allocates —
    which is exactly what made #1376 invisible until a module was small
    enough to have nothing else.
    """

    def test_no_push_site_omits_needs_alloc(self) -> None:
        offenders = set(_push_sites_without_needs_alloc()) - _NEEDS_ALLOC_EXEMPT
        assert not offenders, (
            "these emit `gc_shadow_push` without setting `needs_alloc`, so a "
            "module whose only GC-touching lowering is one of them references "
            f"an undeclared `$gc_sp`: {sorted(offenders)}"
        )

    def test_the_exemptions_still_exist(self) -> None:
        """A stale exemption would silently re-admit its site.

        If one of these is renamed or gains a flag assignment, the entry
        stops describing anything and the sweep quietly narrows.
        """
        live = set(_push_sites_without_needs_alloc())
        stale = _NEEDS_ALLOC_EXEMPT - live
        assert not stale, (
            f"exemptions that no longer describe a real site: {sorted(stale)}"
        )
