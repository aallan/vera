"""#1212: a `@Byte` literal inside a value-position join lowers at i32.

`@Byte` is i32 (spec §11) while an int literal defaults to `i64.const`, so
every write into a Byte boundary needs the literal coerced.  #865 and #1092
coerced a literal that WAS the written value — a top-level `IntLit` and
nothing else.  The checker's bidirectional coercion is happy to type a
BRANCH literal as `@Byte` too, so each of

    let @Byte = if c then { 1 } else { 2 }
    handle[State<Byte>](@Byte = if c then { 1 } else { 2 }) …
    put(if c then { 1 } else { 2 })
    resume(if c then { 1 } else { 2 })     -- the E602 skip message's advice
    … with @Byte = if c then { 1 } else { 2 }
    byte_id(if c then { 1 } else { 2 })
    MkB(if c then { 200 } else { 3 })      -- at Box<Byte>
    let @Byte = match … { Some(@Byte) -> @Byte.0, None -> 0 }
    apply_fn(fn(@Bool -> @Byte) { 207 }, b)   -- the closure's own RETURN
    fn g(@Byte -> @Byte) { if p then { @Byte.0 } else { 8 } }  -- hetero join

was a check-green program that failed WASM validation with `type mismatch:
expected i32, found i64`.  Loud at run, never silent corruption.

The last two are worth separating from the rest.  The closure RETURN was a
missing MIRROR, not a missing mark: a named function's `@Byte` return has
been coerced at the return boundary since #865 and the lifted-closure path
simply had no such step.  The heterogeneous join is a COMPOSITION of two
defects — the return boundary marked no leaves at all (its coercion was a
whole-body `i32.wrap_i64`) and `_infer_block_result_type` reads the
then-branch / first arm only — so a join whose read arm was already i32 and
whose sibling was a bare literal got an annotation from one arm and arms
lowered at their own widths, with ARM ORDER deciding which way it failed.
The return is now a MARKING boundary on both paths, which makes the join
agree with itself whichever arm inference happens to read.

The fix is ONE branch descent — `WasmContext._mark_byte_literal_leaves`,
driven through `_mark_byte_write_value` — marking the literal LEAVES of a
join before the value is translated, so the `IntLit` lowering and the two
join result-type deciders (`_infer_block_result_type`,
`_infer_match_result_type` via `_infer_expr_wasm_type`) all read the same
marks and the `(result i32)` annotation agrees with its arms.  Marking
before translation, rather than overwriting an already-translated i64
lowering, is also what keeps each written value translated exactly once.

**What is and is not claimed.**  The list above is the set of boundaries
this suite proves, each with a run-asserting oracle — not a proof that no
further one exists.  The checker has exactly ONE Byte coercion
(`_synth_expr` on an `IntLit` whose `expected` resolves to `BYTE`,
`vera/checker/expressions.py`), so the true enumeration is "every position
that propagates a Byte expectation", and that is a property of the
checker's bidirectional propagation which nothing enumerates in one place.
Each round of review has found the list to be one longer, so it is stated
here as measured coverage rather than as a closed class.

Every test carries a VALUE oracle, not merely "it runs": an i32/i64 width
defect that happened to validate would still read back the wrong number.
The controls are the load-bearing half — a plain `@Int` join must stay i64
(asserted on a value above 2^32, which an i32 lowering cannot represent),
and a Byte join with no literal arm must keep working untouched.
"""

from __future__ import annotations

import pytest

from tests.checker_helpers import _check_ok
from tests.codegen_helpers import _run

# =====================================================================
# The write boundaries this suite proves (see the module docstring
# on why that is measured coverage, not a closed class)
# =====================================================================

_LET_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Byte = if @Bool.0 then { 200 } else { 3 };
  byte_to_int(@Byte.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

# The Block-tail leg of the descent: the branch is not the literal, it
# CONTAINS the literal as its trailing expression.
_LET_IF_BLOCK_TAIL = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Byte = if @Bool.0 then {
    let @Int = 1;
    200
  } else {
    3
  };
  byte_to_int(@Byte.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

# The multi-arm MATCH leg: `@Byte.0` in the first arm is already i32, and
# the literal in the second is what used to be i64 — a mixed join, which is
# why the arms and the `(result …)` annotation have to be decided together.
# This is the shape of the `p4a_int_in_byte` review probe.
_LET_MATCH_ARM = """
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Byte = match int_to_byte(@Int.0) {
    Some(@Byte) -> @Byte.0,
    None -> 0
  };
  byte_to_int(@Byte.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(200)
}
"""

_STATE_INIT_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Byte>](@Byte = if @Bool.0 then { 200 } else { 3 }) {
    get(@Unit) -> { resume(@Byte.0) },
    put(@Byte) -> { resume(()) }
  } in {
    byte_to_int(get(()))
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

_PUT_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Byte>](@Byte = 7) {
    get(@Unit) -> { resume(@Byte.0) },
    put(@Byte) -> { resume(()) }
  } in {
    put(if @Bool.0 then { 200 } else { 3 });
    byte_to_int(get(()))
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

# The bare-dispatch twin of `_PUT_IF`: no `put` clause, so the write goes
# through the host intrinsic rather than an inlined clause body.
_BARE_PUT_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Byte>](@Byte = 7) {
    get(@Unit) -> { resume(@Byte.0) }
  } in {
    put(if @Bool.0 then { 200 } else { 3 });
    byte_to_int(get(()))
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

_RESUME_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Byte>](@Byte = 7) {
    get(@Unit) -> { resume(if @Bool.0 then { 200 } else { 3 }) },
    put(@Byte) -> { resume(()) }
  } in {
    byte_to_int(get(()))
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

_WITH_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Byte>](@Byte = 7) {
    get(@Unit) -> { resume(@Byte.0) },
    put(@Byte) -> { resume(()) } with @Byte = if @Bool.0 then { 200 } else { 3 }
  } in {
    put(1);
    byte_to_int(get(()))
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

_CALL_ARG_IF = """
public fn byte_id(@Byte -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Byte.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(byte_id(if true then { 200 } else { 3 }))
}
"""

# The NINTH boundary (PR #1250 review): a closure's own RETURN.  A named
# function's `@Byte` return has always been coerced at the return boundary
# (`_compile_fn`: `i32.wrap_i64` when the body infers i64 into an i32
# result); the lifted-closure path had no such step, so `fn(@Bool -> @Byte)`
# behind an `apply_fn` emitted `i64.const` into an `(result i32)` and
# `$rt.anon_0` failed WASM validation on a check-green program — while its
# named twin ran.  Both the bare literal and the join spelling reach it.
_CLOSURE_RETURN_LIT = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(apply_fn(fn(@Bool -> @Byte) effects(pure) {
    207
  }, @Bool.0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

_CLOSURE_RETURN_JOIN = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(apply_fn(fn(@Bool -> @Byte) effects(pure) {
    if @Bool.0 then { 207 } else { 8 }
  }, @Bool.0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

# The TENTH shape (PR #1250 round 3): a HETEROGENEOUS join at a `@Byte`
# return, where the arm the result-type decider reads is already i32 and a
# SIBLING arm is a bare literal.  Two defects compose:
#
#   * the return boundary marked no literal leaves at all — the coercion
#     there was a whole-body `i32.wrap_i64`, which fires only when the
#     decider calls the WHOLE body i64;
#   * `_infer_block_result_type` reads the then-branch / first arm only.
#
# So the join is annotated from ONE arm while its siblings lower at their
# own widths, and which way it fails is decided by arm ORDER — the two
# fixtures below are the same defect mirrored, and their WASM errors are
# mirrored too (`expected i32, found i64` and `expected i64, found i32`).
# Both paths have it: the named function and the lifted closure alike.
#
# The fix has to be the MARKING, not the decider: teaching the decider to
# read every arm would pick a type for the annotation while the literal arm
# still emitted `i64.const`, which is the second fixture verbatim.  Marking
# the leaves makes every arm i32, after which whichever arm the decider
# reads gives the same answer — sufficient as well as necessary, and it
# keeps the ONE derivation (`_mark_byte_write_value`) as the only place a
# Byte write width is decided.
_RETURN_HETERO_JOIN_SLOT_FIRST = """
private fn g(@Byte -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  if byte_to_int(@Byte.0) > 0 then { @Byte.0 } else { 8 }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(g(207))
}
"""

# The same join with the arms swapped: now the decider reads the LITERAL,
# calls the body i64, and the `@Byte` slot arm is the one that mismatches.
_RETURN_HETERO_JOIN_LITERAL_FIRST = """
private fn g(@Byte -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  if byte_to_int(@Byte.0) > 0 then { 8 } else { @Byte.0 }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(g(207))
}
"""

# The `match` spelling, whose arm-0-only inference is the same rule one
# node type over — and the reviewer's original repro.
_RETURN_HETERO_MATCH_NAMED = """
private fn g(@Int -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  match int_to_byte(@Int.0) {
    Some(@Byte) -> @Byte.0,
    None -> 0
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(g(207))
}
"""

# Its closure twin: the same body behind an `apply_fn`.
_RETURN_HETERO_MATCH_CLOSURE = """
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(apply_fn(fn(@Int -> @Byte) effects(pure) {
    match int_to_byte(@Int.0) {
      Some(@Byte) -> @Byte.0,
      None -> 0
    }
  }, @Int.0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(207)
}
"""

# A refined-Byte alias return, so the marking has to resolve the alias
# chain rather than match the syntactic head.
_RETURN_HETERO_REFINED_ALIAS = """
type SmallByte = { @Byte | byte_to_int(@Byte.0) < 250 };

private fn g(@Byte -> @SmallByte)
  requires(byte_to_int(@Byte.0) < 250)
  ensures(true)
  effects(pure)
{
  if byte_to_int(@Byte.0) > 0 then { @Byte.0 } else { 8 }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(g(207))
}
"""

# The named twin of the closure return — the path that already worked, and
# the oracle the closure one is held to.
_NAMED_RETURN_JOIN = """
private fn g(@Bool -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Bool.0 then { 207 } else { 8 }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(g(true))
}
"""


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        pytest.param(_LET_IF, 200, id="let_if"),
        pytest.param(_LET_IF_BLOCK_TAIL, 200, id="let_if_block_tail"),
        pytest.param(_LET_MATCH_ARM, 200, id="let_match_arm"),
        pytest.param(_STATE_INIT_IF, 200, id="state_init_if"),
        pytest.param(_PUT_IF, 200, id="put_if"),
        pytest.param(_BARE_PUT_IF, 200, id="bare_put_if"),
        pytest.param(_RESUME_IF, 200, id="resume_if"),
        pytest.param(_WITH_IF, 200, id="with_update_if"),
        pytest.param(_CALL_ARG_IF, 200, id="call_arg_if"),
        pytest.param(_CLOSURE_RETURN_LIT, 207, id="closure_return_lit"),
        pytest.param(_CLOSURE_RETURN_JOIN, 207, id="closure_return_join"),
    ],
)
def test_a_byte_literal_in_a_join_reaches_the_boundary(
    source: str, expected: int,
) -> None:
    """Each #865 arm, spelled with the literal inside a branch.

    200 rather than a small number on purpose: it is representable in a
    Byte and distinguishable from every other constant in the fixture, so a
    wrong branch or a truncated store shows up as a wrong VALUE and not just
    as a validation failure.
    """
    _check_ok(source)
    assert _run(source) == expected


def test_the_other_branch_is_reachable_and_also_a_byte() -> None:
    """The join is a real join: the else arm's literal is coerced too.

    A fix that marked only the `then` branch would validate (the `if`'s
    result type is read off `then`) and then push an i64 from `else`.
    """
    assert _run(_LET_IF.replace("f(true)", "f(false)")) == 3
    assert _run(_PUT_IF.replace("f(true)", "f(false)")) == 3
    assert _run(_RESUME_IF.replace("f(true)", "f(false)")) == 3


# =====================================================================
# Controls — the marking must not spread
# =====================================================================

# Above 2^32, so an i32 lowering cannot represent it: if a plain `@Int`
# join were ever marked at the Byte width, this returns a truncated number
# rather than merely failing to validate.
_INT_JOIN_STAYS_I64 = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = if @Bool.0 then { 5000000000 } else { 3 };
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

# A Byte join with NO literal arm was already correct — both arms are i32
# Byte values — and must stay so: the marking claims nothing about it.
_BYTE_JOIN_WITHOUT_LITERALS = """
public fn f(@Bool, @Byte, @Byte -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Byte = if @Bool.0 then { @Byte.1 } else { @Byte.0 };
  byte_to_int(@Byte.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true, 200, 3)
}
"""

# A Byte-RETURNING function whose body is a literal join: the return path
# has its own #865 coercion (`_infer_block_result_type` + `i32.wrap_i64`),
# which must keep working whichever width the body settles on.
_BYTE_RETURN_JOIN = """
public fn pick(@Bool -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Bool.0 then { 200 } else { 3 }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(pick(true))
}
"""


def test_an_int_join_still_lowers_at_i64() -> None:
    """The value cannot survive an i32 store, so this is not a mere
    validation check."""
    assert _run(_INT_JOIN_STAYS_I64) == 5000000000


def test_a_byte_join_with_no_literal_arm_is_untouched() -> None:
    assert _run(_BYTE_JOIN_WITHOUT_LITERALS) == 200
    assert _run(
        _BYTE_JOIN_WITHOUT_LITERALS.replace(
            "f(true, 200, 3)", "f(false, 200, 3)")) == 3


def test_a_byte_returning_literal_join_still_runs() -> None:
    assert _run(_BYTE_RETURN_JOIN) == 200
    assert _run(_BYTE_RETURN_JOIN.replace("pick(true)", "pick(false)")) == 3


def test_the_named_return_control_was_always_correct() -> None:
    """The oracle the closure-return coercion mirrors.

    A named `@Byte` return has been coerced at the return boundary since
    #865; the closure path is now the same code in the same position, so
    this control is what says the ninth boundary was a MISSING mirror
    rather than a new rule.
    """
    assert _run(_NAMED_RETURN_JOIN) == 207
    assert _run(_NAMED_RETURN_JOIN.replace("g(true)", "g(false)")) == 8


def test_the_closure_return_reaches_its_other_branch_too() -> None:
    """The else arm of the ninth boundary, so it is a real join."""
    assert _run(_CLOSURE_RETURN_JOIN.replace("f(true)", "f(false)")) == 8


# =====================================================================
# The tenth shape: a heterogeneous join AT the return boundary
# =====================================================================


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        pytest.param(
            _RETURN_HETERO_JOIN_SLOT_FIRST, 207, id="if_slot_arm_first"),
        pytest.param(
            _RETURN_HETERO_JOIN_LITERAL_FIRST, 8, id="if_literal_arm_first"),
        pytest.param(
            _RETURN_HETERO_MATCH_NAMED, 207, id="match_named"),
        pytest.param(
            _RETURN_HETERO_MATCH_CLOSURE, 207, id="match_closure"),
        pytest.param(
            _RETURN_HETERO_REFINED_ALIAS, 207, id="refined_alias_return"),
    ],
)
def test_a_heterogeneous_join_at_a_byte_return_agrees_with_itself(
    source: str, expected: int,
) -> None:
    """Every arm of a `@Byte`-returning join lowers at the same width.

    The oracles differ per fixture on purpose: 207 where the `@Byte` slot
    arm is taken and 8 where the literal arm is, so a fix that made both
    arms i32 but wired the wrong one would still be caught.
    """
    _check_ok(source)
    assert _run(source) == expected


def test_the_match_return_joins_reach_their_literal_arm() -> None:
    """The `None` arm — the one the marking fix exists for.

    Both match fixtures above drive an in-range value, so `int_to_byte`
    returns `Some` and only the i32 `@Byte`-slot arm ever executes.  300 is
    out of range, so `int_to_byte` returns `None` and the arm taken is the
    bare literal `0` at the `@Byte` return boundary — the value whose width
    the marking decides.
    """
    assert _run(_RETURN_HETERO_MATCH_NAMED.replace("g(207)", "g(300)")) == 0
    assert _run(_RETURN_HETERO_MATCH_CLOSURE.replace("f(207)", "f(300)")) == 0


def test_both_arm_orders_of_the_return_join_are_fixed() -> None:
    """Arm ORDER decided which way it failed, so both orders are pinned.

    Slot-first reported `expected i32, found i64` and literal-first
    `expected i64, found i32` — the same defect read from either end, which
    is what says the annotation and the arms were derived separately.
    """
    assert _run(
        _RETURN_HETERO_JOIN_SLOT_FIRST.replace("g(207)", "g(0)")) == 8
    assert _run(
        _RETURN_HETERO_JOIN_LITERAL_FIRST.replace("g(207)", "g(0)")) == 0


# =====================================================================
# The constructor-field arm (#1092), which needs the checker's tables
# =====================================================================

_CTOR_FIELD_IF = """\
private data Box<T> { MkB(T) }

public fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Byte> = MkB(if @Bool.0 then { 200 } else { 3 });
  match @Box<Byte>.0 {
    MkB(@Byte) -> byte_to_int(@Byte.0)
  }
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  f(true)
}
"""


def _run_checked(source: str, fn: str | None = None) -> int:
    """Compile through the REAL pipeline (checker tables threaded) and run.

    The #1092 constructor-field width keys on the checker-recorded TARGET
    type (`_target_codegen_type_full`, the #820 side-table), so this arm is
    only observable when those artifacts are threaded — exactly as the CLI
    threads them.  Mirrors the helper of the same name in
    `tests/test_codegen_alias_of_adt_eq_show_1085.py`, which pins the
    top-level-literal half of the same boundary.
    """
    import tempfile
    from pathlib import Path

    from vera.checker import typecheck_with_artifacts
    from vera.codegen import compile as codegen_compile, execute
    from vera.parser import parse_file
    from vera.transform import transform

    f = tempfile.NamedTemporaryFile(  # noqa: SIM115 — Windows fixture; closed + unlinked below
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    )
    try:
        with f:
            f.write(source)
        tree = parse_file(f.name)
        program = transform(tree)
        diags, arts = typecheck_with_artifacts(
            program, source=source, file=f.name,
        )
        errors = [d for d in diags if d.severity == "error"]
        assert not errors, f"check errors: {errors}"
        result = codegen_compile(
            program, source=source, file=f.name,
            expr_semantic_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        cerrors = [d for d in result.diagnostics if d.severity == "error"]
        assert not cerrors, f"compile errors: {cerrors}"
        exec_result = execute(result, fn_name=fn)
        assert exec_result.value is not None, "Expected a return value"
        return exec_result.value
    finally:
        Path(f.name).unlink(missing_ok=True)


def test_a_byte_field_literal_inside_a_join_is_stored_at_i32() -> None:
    """The #1092 boundary, spelled with the literal in a branch.

    200 is the discriminating value: the field is read back through the
    match, which sizes it from the INSTANTIATED type (Byte -> i32), so an
    i64 store reads back a different number rather than merely failing.
    """
    assert _run_checked(_CTOR_FIELD_IF) == 200
    assert _run_checked(_CTOR_FIELD_IF.replace("f(true)", "f(false)")) == 3
