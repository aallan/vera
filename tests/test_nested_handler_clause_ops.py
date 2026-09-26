"""#1211: a clause body's bare op belongs to the ENCLOSING context.

A handler clause is not part of the body it refines.  The checker says so
structurally — clauses are checked *before* the handled effect joins the
effect row (``vera/checker/control.py``), so a bare ``get``/``put`` written
in a clause body resolves against whatever encloses the ``handle``
expression, exactly like an outer slot reference in a clause body resolves
against the handler-declaration scope (§7.5.2).

Codegen used to disagree.  ``_translate_state_clause_op`` cleared the clause
registry before inlining a clause body — enough to stop a clause re-entering
itself — but left ``_effect_ops`` pointing at the handler's OWN host-cell
imports.  With two nested handlers over different cell families, a bare op in
the inner handler's clause body read and wrote the INNER cell while the
checker had typed it against the outer one: check-green, verify-clean, valid
WASM, silently wrong value.

Every expected value below is derived from the CHECKER's story, never from
what codegen happens to emit.  Each case is asserted on all three
components — the checker accepts it, the verifier discharges it cleanly, and
the compiled program produces the checker's value — so a future regression in
any one of them shows up as a disagreement rather than as a quietly shifted
oracle.  The `pre_fix` value on each case is what codegen actually produced
before the alignment; it is asserted to be *different*, so a case that stops
distinguishing the two semantics fails loudly instead of passing vacuously.

Four groups follow the matrix.  The ENCLOSING context is not always another
handler: it can be the function's declared effect row (the only route that
reads the restored op registry) or nothing at all (E122).  Because the
outward-routed operation is an operation SITE of the enclosing body, the
enclosing handler's own clause runs on it.  Host-imported builtins written in
a clause body must have their imports registered like any other code.  And
two shapes are refused rather than lowered: SAME-family nesting, where the
host intrinsics cannot address the outer cell (#1233), and nesting past the
outward-re-entry depth cap, whose expansion is exponential.  The checker
refuses both (E339), and code generation's gate stays as the backstop.
"""

from __future__ import annotations

import pytest

from tests.codegen_helpers import _compile, _run, _run_io
from tests.checker_helpers import _check_ok, _errors
from tests.verifier_helpers import _verify_ok
from vera.skip import STATE_CLAUSE_INLINE_DEPTH_CAP

# `probe` holds the shape; `main` just calls it, so every case shares one
# entry point and the compiled value is the shape's own.
_MAIN = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(())
}
"""

# --- depth 2, bare `put` inside the inner PUT clause ------------------
# Outer State<Int> = 111, inner State<Nat> = 7.
#   put(3)      -> inner put clause: stores 3 into the Nat cell, then its
#                  body's bare put(1000) targets the ENCLOSING State<Int>.
#   get(())     -> 3 (the Nat cell)
#   outer get   -> 1000
# => 3 * 100000 + 1000 = 301000.  Routing the clause-body put to the inner
# cell instead gives 1000 * 100000 + 111 = 100000111.
_PUT_IN_PUT_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 111) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 7) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { put(1000); resume(()) }
    } in {
      put(3);
      get(())
    };
    nat_to_int(@Nat.0) * 100000 + get(())
  }
}
"""

# --- depth 2, bare `put` inside the inner GET clause ------------------
# Outer State<Int> = 5, inner State<Nat> = 9.  The get clause captures the
# pre-read Nat state (9) and its body's put(77) targets the outer Int cell.
# => 9 * 1000 + 77 = 9077 (inner routing leaves the outer at 5: 9005).
_PUT_IN_GET_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 9) {
      get(@Unit) -> { put(77); resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    };
    nat_to_int(@Nat.0) * 1000 + get(())
  }
}
"""

# --- depth 2, bare `get` inside a `with` state-update expression ------
# The `with` expression is clause scope too, so its bare get(()) reads the
# ENCLOSING State<Nat> (4), overriding the Int cell with 40 rather than with
# ten times the value just stored (70).  => 40 * 100 + 4 = 4004 (vs 7004).
# It also pins the inference mirror: `nat_to_int(get(()))` only type-checks
# in WASM if the op's result type came from the outer cell.
_GET_IN_WITH_EXPR = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 4) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    let @Int = handle[State<Int>](@Int = 1) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) } with @Int = nat_to_int(get(())) * 10
    } in {
      put(7);
      get(())
    };
    @Int.0 * 100 + nat_to_int(get(()))
  }
}
"""

# --- depth 3: the IMMEDIATELY enclosing handler, not the outermost ----
# Bool (outer) / Nat (middle) / Int (inner).  The inner get clause's bare
# put(33) must land in the MIDDLE Nat cell — proving the rule walks out one
# level, not all the way.  The Nat cell's initial 20 is read into the result
# BEFORE that overwrite, so every constant here is load-bearing:
# => 20 * 100000 + 33 * 1000 + 7 = 2033007.  Inner routing leaves the Nat cell
# at 20 for the second term too: 2020007.  The Bool cell stays false
# throughout, which the final `if` reads.
_DEPTH_THREE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Bool>](@Bool = false) {
    get(@Unit) -> { resume(@Bool.0) },
    put(@Bool) -> { resume(()) }
  } in {
    let @Int = handle[State<Nat>](@Nat = 20) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      let @Nat = get(());
      let @Int = handle[State<Int>](@Int = 7) {
        get(@Unit) -> { put(33); resume(@Int.0) },
        put(@Int) -> { resume(()) }
      } in {
        get(())
      };
      nat_to_int(@Nat.0) * 100000 + nat_to_int(get(())) * 1000 + @Int.0
    };
    if get(()) then {
      0 - 1
    } else {
      @Int.0
    }
  }
}
"""

# --- the qualified spelling must agree with the bare one --------------
# `State.put(...)` delegates to the same dispatcher (PR #1202 round 4), so
# the enclosing-context rule has to hold for it too: same 301000.
_QUALIFIED_IN_CLAUSE = _PUT_IN_PUT_CLAUSE.replace(
    "put(@Nat) -> { put(1000); resume(()) }",
    "put(@Nat) -> { State.put(1000); resume(()) }",
)
assert _QUALIFIED_IN_CLAUSE != _PUT_IN_PUT_CLAUSE, (
    "the qualified-spelling fixture no longer derives from the bare one — "
    "the bare clause body's spelling changed"
)

# --- a nested handle expression INSIDE a clause body -----------------
# The nested handle owns its own registries: its body's get(()) reads ITS
# fresh Int cell (30), and when it pops, the clause's own bare put must be
# back on the DECLARATION-time registries — the enclosing State<Int> — not
# on the Nat handler's.  Same family as the outer handler on purpose: the
# fresh cell is pushed and popped, so a leak in either direction shows.
#   nested cell 30 -> put(32) into the OUTER Int cell; inner Nat stays 8
# => 8 * 1000 + 32 = 8032.  Restoring to the Nat handler instead writes 32
# into the Nat cell and leaves the outer at 111: 8111.
_HANDLE_INSIDE_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 111) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 8) {
      get(@Unit) -> {
        let @Int = handle[State<Int>](@Int = 30) {
          get(@Unit) -> { resume(@Int.0) },
          put(@Int) -> { resume(()) }
        } in {
          get(())
        };
        put(@Int.0 + 2);
        resume(@Nat.0)
      },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    };
    nat_to_int(@Nat.0) * 1000 + get(())
  }
}
"""

# --- the op's RESULT TYPE mirrors follow the enclosing cell too -------
# `_effect_op_result_wt` types a bare get(()) in match-scrutinee position
# (#914 A2).  Outer cell is Option<Int> (an i32 pointer), inner is Nat (i64),
# so leaving that mirror at the inner handler emits an i64 scrutinee for an
# i32 value — invalid WASM, on a check-green program.
#   put(3)  -> Nat cell 3; clause body matches the OUTER Some(9) and writes
#              Some(10) back to it
# => 3 * 100 + 10 = 310.  (Pre-fix the whole clause body targeted the Nat
# cell: `match get(())` read an i64 as an Option pointer.)
_MATCH_SCRUTINEE_IN_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(9)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 7) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> {
        let @Int = match get(()) {
          Some(@Int) -> { @Int.0 },
          None -> { 0 }
        };
        put(Some(@Int.0 + 1));
        resume(())
      }
    } in {
      put(3);
      get(())
    };
    match get(()) {
      Some(@Int) -> { nat_to_int(@Nat.0) * 100 + @Int.0 },
      None -> { 0 - 1 }
    }
  }
}
"""

# The Vera-name twin: `_effect_op_result_vera` picks an array literal's
# ELEMENT layout (#1006), which the layout-ambiguous WAT type cannot.  Same
# nesting; the clause body wraps the outer cell's value in an array and puts
# it straight back, so the outer stays Some(9).  => 3 * 100 + 9 = 309.
_ARRAY_ELEMENT_IN_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(9)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 7) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> {
        let @Array<Option<Int>> = [get(())];
        put(@Array<Option<Int>>.0[0]);
        resume(())
      }
    } in {
      put(3);
      get(())
    };
    match get(()) {
      Some(@Int) -> { nat_to_int(@Nat.0) * 100 + @Int.0 },
      None -> { 0 - 1 }
    }
  }
}
"""

# (case id, source, checker-derived value, value codegen produced pre-fix)
# `pre_fix = None` marks a shape that did not COMPILE before the alignment
# (invalid WASM from a check-green program) — distinguishing by construction.
_CASES = [
    ("put_in_put_clause", _PUT_IN_PUT_CLAUSE, 301000, 100000111),
    ("put_in_get_clause", _PUT_IN_GET_CLAUSE, 9077, 9005),
    ("get_in_with_expr", _GET_IN_WITH_EXPR, 4004, 7004),
    ("depth_three", _DEPTH_THREE, 2033007, 2020007),
    ("qualified_in_clause", _QUALIFIED_IN_CLAUSE, 301000, 100000111),
    ("handle_inside_clause", _HANDLE_INSIDE_CLAUSE, 8032, 8111),
    ("match_scrutinee_in_clause", _MATCH_SCRUTINEE_IN_CLAUSE, 310, None),
    ("array_element_in_clause", _ARRAY_ELEMENT_IN_CLAUSE, 309, None),
]


@pytest.mark.parametrize(
    ("source", "expected", "pre_fix"),
    [pytest.param(s, e, p, id=i) for i, s, e, p in _CASES],
)
def test_clause_body_op_targets_the_enclosing_cell(
    source: str, expected: int, pre_fix: int | None,
) -> None:
    """checker = codegen = verifier on every nested clause-body op shape.

    All three legs are asserted together on purpose: the defect this pins
    was check-green AND verify-clean, so either leg alone would have passed
    while the compiled program returned the wrong number.
    """
    program = source + _MAIN
    _check_ok(program)
    _verify_ok(program)
    assert _run(program) == expected


def test_every_case_distinguishes_the_two_semantics() -> None:
    """A case whose pre-fix and post-fix values coincide proves nothing.

    Each shape has to separate enclosing-cell routing from inner-cell
    routing — either by returning a different number (`pre_fix` is that
    number) or by not compiling at all under the old routing (`pre_fix` is
    None) — or it has quietly stopped being a regression test.  The two
    `pre_fix = None` cases are the ones whose old lowering emitted a
    type-invalid module: at the pre-fix base both raised `WasmtimeError` at
    instantiation (an i64 read as an `Option` pointer, and an array element
    laid out from the wrong Vera type), which is why they carry no number.
    (The control that the alignment does not move anything ELSE is the corpus
    differential run for this change: over the `.vera` programs in
    `examples/`, `tests/conformance/`, and `tests/probes/`, exactly the two
    nested-clause-body programs moved.)
    """
    for case_id, _src, expected, pre_fix in _CASES:
        assert expected != pre_fix, (
            f"{case_id} no longer distinguishes enclosing-cell routing "
            f"from inner-cell routing (both {expected})"
        )


# =====================================================================
# The ENCLOSING context is not always another handler
# =====================================================================

# The clause-body op resolves to the function's DECLARED effect row: `inner`
# declares `effects(<State<Int>>)` and contains no enclosing handler, so the
# bare `put(1000)` in the Nat handler's put clause is the DECLARED row's op
# and reaches the host cell `main`'s handler established.  This is the only
# route that consults the restored `_effect_ops` registry — every case above
# has an enclosing HANDLER, so it resolves through `_state_clause_ops`
# instead, leaving the `_effect_ops = dict(entry.decl_effect_ops)` restore
# untested.  Values are the same derivation as `_PUT_IN_PUT_CLAUSE`:
#   put(3) -> Nat cell 3, clause body's put(1000) -> the caller's Int cell
# => 3 * 100000 + 1000 = 301000 (inner routing: 1000 * 100000 + 111).
_DECLARED_ROW_IN_CLAUSE = """
private fn inner(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  let @Nat = handle[State<Nat>](@Nat = 7) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { put(1000); resume(()) }
  } in {
    put(3);
    get(())
  };
  nat_to_int(@Nat.0) * 100000 + get(())
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 111) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    inner(())
  }
}
"""

# The OUTERMOST handler in a `pure` function: the enclosing context has no
# State effect at all, so there is nothing for the clause-body op to resolve
# to and the CHECKER rejects it (E122) before codegen ever sees it.  The
# complement of the case above — together they cover both dispositions of an
# empty `decl_effect_ops`.
_OUTERMOST_CLAUSE_OP = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 7) {
    get(@Unit) -> { put(999); resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""


def test_clause_body_op_reaches_the_declared_effect_row() -> None:
    """A clause-body op with no enclosing HANDLER binds the declared row.

    Reverting the `_effect_ops` half of the #1211 restore (leaving only the
    clause-registry clear) sends the clause body's `put` back to the
    handler's OWN Nat cell — which produced 100000111 before the #1233 gate
    and is a loud E602 skip after it — while every enclosing-handler case
    above stays green, because those resolve through the clause registry.
    Either way this is the only case in the file that goes red for it.
    """
    _check_ok(_DECLARED_ROW_IN_CLAUSE)
    _verify_ok(_DECLARED_ROW_IN_CLAUSE)
    assert _run(_DECLARED_ROW_IN_CLAUSE) == 301000


def test_outermost_handler_clause_op_is_a_checker_error() -> None:
    """No enclosing context to resolve to is E122, not a silent inner write.

    The rule sends the op outwards; in a `pure` function there is nothing
    outwards, so the program is rejected at check rather than compiled into
    a write the checker never typed.
    """
    errs = _errors(_OUTERMOST_CLAUSE_OP + _MAIN)
    assert "E122" in {e.error_code for e in errs}, (
        f"expected E122, got: {[(e.error_code, e.description) for e in errs]}"
    )


# =====================================================================
# The op SITE belongs to the enclosing body — so its clause runs
# =====================================================================

# The enclosing handler has a TRANSFORMING put clause (`with` doubles what is
# stored).  The inner Nat handler's put clause performs a bare put(50), which
# §7.5.2 makes an operation site of the ENCLOSING handled body — so the outer
# put clause runs on it and the Int cell ends at 100, not 50.
#   put(3) -> Nat cell 3; clause body's put(50) -> outer put clause -> 50*2
# => 3 * 100000 + 100 = 300100.  Routing it to the outer handler's bare
# INTRINSIC instead (the reading the old "clauses are lexical" bullet
# suggested) gives 300050.
_ENCLOSING_CLAUSE_TRANSFORMS = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 111) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.1 * 2
  } in {
    let @Nat = handle[State<Nat>](@Nat = 7) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { put(50); resume(()) }
    } in {
      put(3);
      get(())
    };
    nat_to_int(@Nat.0) * 100000 + get(())
  }
}
"""


def test_clause_body_op_runs_the_enclosing_handlers_clause() -> None:
    """The outward-routed op is an op SITE of the enclosing body (§7.5.2).

    Spec §7.5.2 used to carry both readings at once — one bullet said an
    operation inside a clause body performs the INTRINSIC operation, the next
    said it is the enclosing context's operation.  They disagree exactly when
    the enclosing handler declares a clause for it, which is what this pins:
    the enclosing clause runs, so the doubling `with` applies (300100), where
    the intrinsic reading gives 300050.  Restoring only the imports and not
    the enclosing clause registry produces the latter.
    """
    _check_ok(_ENCLOSING_CLAUSE_TRANSFORMS + _MAIN)
    _verify_ok(_ENCLOSING_CLAUSE_TRANSFORMS + _MAIN)
    assert _run(_ENCLOSING_CLAUSE_TRANSFORMS + _MAIN) == 300100


# =====================================================================
# Host-imported builtins inside a clause body
# =====================================================================

# A clause body is ordinary code, so a host-imported operation written in one
# needs its import declared like any other.  `IO.print` in a `State` get
# clause emitted `call $vera.print` against no import until the #1210 walk
# covered the handler's clause bodies.
_IO_IN_CLAUSE_BODY = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { IO.print("in clause"); resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""


def test_io_op_inside_a_clause_body_is_compiled_and_run() -> None:
    """`IO.print` in a clause body: check-green must mean runnable.

    The clause body is inlined at the op call site, so its `IO.print` is
    emitted into the function — but the import pre-scan descended a handler's
    BODY only, so nothing registered `print` and the module failed to compile
    with `unknown func $vera.print`.  Reverting the `HandleExpr` legs of
    `_scan_io_ops` restores exactly that.
    """
    _check_ok(_IO_IN_CLAUSE_BODY)
    assert "in clause" in _run_io(_IO_IN_CLAUSE_BODY)


# =====================================================================
# Same-family nesting: loudly refused, not silently hybrid (#1233)
# =====================================================================

# Outer and inner are BOTH `State<Int>`.  The rule routes the inner get
# clause's bare put(42) to the outer handler, but the host intrinsics address
# only the innermost cell of a family, so the store would land in the inner
# cell (the probe returned 5100 where the rule says 5042).
_SAME_FAMILY_NESTING = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 100) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Int = handle[State<Int>](@Int = 5) {
      get(@Unit) -> { put(42); resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      get(())
    };
    @Int.0 * 1000 + get(())
  }
}
"""

# Same family, but the bare op is in the clause's `with` expression — clause
# scope too, so the same refusal must cover it.
_SAME_FAMILY_WITH_EXPR = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 100) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Int = handle[State<Int>](@Int = 5) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) } with @Int = get(()) + 1000
    } in {
      put(9);
      get(())
    };
    @Int.0 * 10000 + get(())
  }
}
"""

# Same family reached through the DECLARED ROW rather than a handler: the
# function declares `effects(<State<Int>>)` and its own `handle[State<Int>]`
# clause performs a bare put.  The intrinsic would still hit the handler's
# own cell, so this is the same limitation by another route.
_SAME_FAMILY_DECLARED_ROW = """
private fn inner(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { put(42); resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 100) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    inner(())
  }
}
"""

# The QUALIFIED spelling of the same clause-body operation.  `State.put(x)`
# is routed through `_translate_call` exactly like the bare `put(x)`, so one
# gate covers both — but the matrix had no qualified case, which left the
# claim in `calls.py`'s comment ("and so is the qualified `State.get` /
# `State.put` spelling, which delegates here") untested.
_SAME_FAMILY_QUALIFIED = _SAME_FAMILY_NESTING.replace(
    "get(@Unit) -> { put(42); resume(@Int.0) }",
    "get(@Unit) -> { State.put(42); resume(@Int.0) }",
)
assert _SAME_FAMILY_QUALIFIED != _SAME_FAMILY_NESTING, (
    "the qualified-spelling fixture no longer derives from the bare one — "
    "the bare clause body's spelling changed"
)

# A COMPOSITE cell of the same family, both handlers declaring clauses — the
# gate's clause-registry branch, where both sides of the comparison are the
# canonical family name.
_SAME_FAMILY_COMPOSITE_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(100)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    let @Option<Int> = handle[State<Option<Int>>](@Option<Int> = Some(5)) {
      get(@Unit) -> { put(Some(42)); resume(@Option<Int>.0) },
      put(@Option<Int>) -> { resume(()) }
    } in {
      get(())
    };
    match @Option<Int>.0 {
      Some(@Int) -> @Int.0 * 1000 + (match get(()) {
        Some(@Int) -> @Int.0,
        None -> 0
      }),
      None -> 0 - 1
    }
  }
}
"""

# The same composite nest with NO `put` clause on the outer handler, so the
# outward-routed `put` resolves to the outer handler's BARE INTRINSIC and the
# gate reads its family off the IMPORT NAME — which is mangled
# (`Option_LInt_R`) where the pushed-cell stack is canonical (`Option<Int>`).
# Mangling is not idempotent, so re-mangling the already-mangled side made
# every composite family compare unequal to itself: this program compiled and
# ran, returning 5100 where the enclosing-context rule says 5042 (round-5
# review).  Its scalar twin (`Int`, whose mangling IS a fixed point) was
# refused correctly the whole time, which is why nothing caught it.
_SAME_FAMILY_COMPOSITE_IMPORT = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(100)) {
    get(@Unit) -> { resume(@Option<Int>.0) }
  } in {
    let @Option<Int> = handle[State<Option<Int>>](@Option<Int> = Some(5)) {
      get(@Unit) -> { put(Some(42)); resume(@Option<Int>.0) },
      put(@Option<Int>) -> { resume(()) }
    } in {
      get(())
    };
    match @Option<Int>.0 {
      Some(@Int) -> @Int.0 * 1000 + (match get(()) {
        Some(@Int) -> @Int.0,
        None -> 0
      }),
      None -> 0 - 1
    }
  }
}
"""

# Its scalar twin, which takes the same import-name branch and was always
# refused — the differential that localises the bug to the mangling, not to
# the branch.
_SAME_FAMILY_SCALAR_IMPORT = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 100) {
    get(@Unit) -> { resume(@Int.0) }
  } in {
    let @Int = handle[State<Int>](@Int = 5) {
      get(@Unit) -> { put(42); resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      get(())
    };
    @Int.0 * 1000 + get(())
  }
}
"""

# Four levels, alternating Int / Nat / Int / Nat.  The innermost `put(40)`
# runs the FOURTH handler's put clause, whose own bare `put(300)` is an
# operation of the THIRD (Int, unshadowed — so far so good) and inlines its
# clause; the `put(30)` written THERE is an operation of the SECOND (Nat),
# and the cell that shadows it is the FOURTH's, two levels in.  The
# shadowing cell is not the adjacent one — the at-a-distance claim
# `KNOWN_ISSUES.md`'s #1233 row makes, pinned here rather than asserted.
_SAME_FAMILY_AT_A_DISTANCE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Int = handle[State<Nat>](@Nat = 2) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      let @Int = handle[State<Int>](@Int = 3) {
        get(@Unit) -> { resume(@Int.0) },
        put(@Int) -> { put(30); resume(()) }
      } in {
        let @Int = handle[State<Nat>](@Nat = 4) {
          get(@Unit) -> { resume(@Nat.0) },
          put(@Nat) -> { put(300); resume(()) }
        } in {
          put(40);
          nat_to_int(get(()))
        };
        put(3000);
        @Int.0 + get(())
      };
      @Int.0 + nat_to_int(get(()))
    };
    @Int.0 + get(())
  }
}
"""

_SAME_FAMILY_CASES = [
    ("nested_get_clause", _SAME_FAMILY_NESTING + _MAIN),
    ("nested_with_expr", _SAME_FAMILY_WITH_EXPR + _MAIN),
    ("declared_row", _SAME_FAMILY_DECLARED_ROW),
    ("qualified_spelling", _SAME_FAMILY_QUALIFIED + _MAIN),
    ("composite_clause_branch", _SAME_FAMILY_COMPOSITE_CLAUSE + _MAIN),
    ("composite_import_branch", _SAME_FAMILY_COMPOSITE_IMPORT + _MAIN),
    ("scalar_import_branch", _SAME_FAMILY_SCALAR_IMPORT + _MAIN),
    ("at_a_distance", _SAME_FAMILY_AT_A_DISTANCE + _MAIN),
]

# A composite cell nested under a DIFFERENT family: the gate must not fire,
# and the enclosing-context rule must produce its own value — the inner
# clause's `put(Some(42))` writes the OUTER `Option<Int>` cell, so the outer
# `get` reads 42.  The negative control for the composite rows above.
_DIFFERENT_FAMILY_COMPOSITE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(100)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 5) {
      get(@Unit) -> { put(Some(42)); resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    };
    nat_to_int(@Nat.0) * 1000 + (match get(()) {
      Some(@Int) -> @Int.0,
      None -> 0
    })
  }
}
"""


@pytest.mark.parametrize(
    "source",
    [pytest.param(s, id=i) for i, s in _SAME_FAMILY_CASES],
)
def test_same_family_clause_body_op_is_refused(source: str) -> None:
    """Same-family nesting is refused, not a silently hybrid lowering (#1233).

    The clause TRANSFORM half routes outward correctly; the CELL half cannot,
    because `state_put_Int` addresses only the innermost `Int` cell.  The
    checker refuses the operation where it is written (E339), and code
    generation's own gate — the backstop for a program that reaches it
    without the checker — skips the function (E602).  Without them each of
    these programs compiles to a value the spec rule does not describe.
    """
    errors = _errors(source)
    assert errors and {d.error_code for d in errors} == {"E339"}, [
        (d.error_code, d.description[:90]) for d in errors
    ]
    assert all("shadows it" in d.description for d in errors), errors
    assert all("1233" in d.rationale for d in errors), errors
    result = _compile(source)
    codes = {d.error_code for d in result.diagnostics}
    assert "E602" in codes, (
        "expected the same-family codegen skip, got: "
        f"{[(d.error_code, d.description[:90]) for d in result.diagnostics]}"
    )
    joined = " ".join(d.description for d in result.diagnostics)
    assert "1233" in joined, joined


def test_different_family_nesting_is_untouched_by_the_same_family_gate() -> None:
    """The gate keys on the FAMILY, not on "a clause body performed an op".

    Its negative control is the whole matrix above — but this states the
    contract directly: the identical shape over two families compiles and
    produces the checker's value.
    """
    assert _run(_PUT_IN_GET_CLAUSE + _MAIN) == 9077


def test_a_composite_cell_under_a_different_family_still_lowers() -> None:
    """The composite rows' negative control, with a value only the rule gives.

    Round 5's mangling fix normalises both sides of the family comparison, so
    it could in principle have gone the other way and started refusing every
    composite nest.  Here the two families differ, so the gate must stay
    silent AND the enclosing-context rule must hold: the inner `Nat` clause's
    `put(Some(42))` is an operation of the ENCLOSING context, so it writes the
    outer `Option<Int>` cell and the outer `get` reads 42, not the initial
    100.  5 * 1000 + 42.
    """
    assert _run(_DIFFERENT_FAMILY_COMPOSITE + _MAIN) == 5042


# =====================================================================
# The outward re-entry is bounded
# =====================================================================

def _deep_nest(depth: int, ops: int = 2) -> str:
    """A `depth`-deep handler nest whose clauses each perform `ops` bare ops.

    One ADT per level, so every cell family is DISTINCT — repeating a family
    would shadow the outer cell and hit the #1233 refusal above, and the point
    here is the legal case.  Each clause body's ops re-enter the enclosing
    clause, so the emitted code is `ops ** depth`: with two, measured 850 /
    1,582 / 4,330 / 15,143 WAT lines at depths 2 / 4 / 6 / 8.
    """
    decls = "\n".join(
        f"private data C{i} {{ K{i}(Int) }}" for i in range(1, depth + 1)
    )
    open_levels = []
    for i in range(1, depth + 1):
        body = "".join(
            f"put(K{i - 1}({i + 100 * j})); " for j in range(ops)
        ) if i > 1 else ""
        open_levels.append(
            f"handle[State<C{i}>](@C{i} = K{i}(1)) {{\n"
            f"  get(@Unit) -> {{ resume(@C{i}.0) }},\n"
            f"  put(@C{i}) -> {{ {body}resume(()) }}\n"
            f"}} in {{"
        )
    inner = (
        f"put(K{depth}(7));\n"
        f"match get(()) {{\n  K{depth}(@Int) -> {{ @Int.0 }}\n}}"
    )
    nest = "\n".join(open_levels) + "\n" + inner + "\n" + "}\n" * depth
    return (
        f"{decls}\n\n"
        "private fn probe(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n{nest}}}\n" + _MAIN
    )


def test_the_checkers_walk_is_linear_in_the_nest() -> None:
    """The checker follows code generation's inlining without its blow-up.

    Deciding E339 means walking each clause body where an operation inlines
    it, and a nest whose clauses each perform `ops` operations has
    `ops ** depth` such paths.  One clause inlined under the same cells at
    the same depth reaches the same operations every time, so the walk
    visits it once: doubling the operations per clause at most roughly
    doubles the walk, where following every path multiplies it by `2 ** 7`
    at the cap.
    """
    from unittest.mock import patch

    from vera.checker.core import TypeChecker

    walked = 0
    real = TypeChecker._clause_op_walk

    def counting(self: TypeChecker, *args: object) -> None:
        nonlocal walked
        walked += 1
        real(self, *args)  # type: ignore[arg-type]

    counts = []
    with patch.object(TypeChecker, "_clause_op_walk", counting):
        for ops in (2, 4):
            walked = 0
            _check_ok(_deep_nest(STATE_CLAUSE_INLINE_DEPTH_CAP, ops))
            counts.append(walked)
    narrow, wide = counts
    assert narrow and wide < 3 * narrow, counts


def test_bounded_outward_reentry_still_compiles_and_runs() -> None:
    """Well below the cap the nest lowers normally, several levels deep."""
    source = _deep_nest(4)
    _check_ok(source)
    assert _run(source) == 7


def test_outward_reentry_at_the_cap_emits_a_bounded_module() -> None:
    """AT the cap the program still compiles, and the WAT stays sane.

    The bound is what makes the cap a real limit rather than a formality: an
    unbounded `2 ** depth` expansion is what it exists to stop, so the module
    emitted at the deepest ACCEPTED nesting has to be a size a compiler can
    reasonably produce.
    """
    source = _deep_nest(STATE_CLAUSE_INLINE_DEPTH_CAP)
    _check_ok(source)
    result = _compile(source)
    assert not [d for d in result.diagnostics if d.error_code == "E602"], (
        "the cap must not fire at the cap: "
        f"{[d.description[:100] for d in result.diagnostics]}"
    )
    assert result.wat
    lines = len(result.wat.splitlines())
    assert lines < 40_000, (
        f"{lines} WAT lines at depth {STATE_CLAUSE_INLINE_DEPTH_CAP} — the "
        "expansion is meant to be bounded well below this"
    )


def test_outward_reentry_one_past_the_cap_is_the_first_refusal() -> None:
    """CAP + 1 is the boundary: the first depth the cap actually rejects.

    The pair below pinned CAP (accepted) and CAP + 2 (refused), leaving the
    exact transition unpinned — an off-by-one in the comparison would move
    the boundary by one level and both of those would still pass.  The
    checker refuses the operations that re-enter too deep (E339), at the
    depth code generation does.  This also pins the CALLER's fate in code
    generation's backstop: the dropped `probe` takes `main` with it, so the
    program surfaces E602 **and** the E620 dropped-caller diagnostic rather
    than silently exporting a `main` that cannot run.
    """
    source = _deep_nest(STATE_CLAUSE_INLINE_DEPTH_CAP + 1)
    errors = _errors(source)
    assert errors and {d.error_code for d in errors} == {"E339"}, [
        (d.error_code, d.description[:90]) for d in errors
    ]
    assert all(
        str(STATE_CLAUSE_INLINE_DEPTH_CAP) in d.description for d in errors
    ), errors
    result = _compile(source)
    codes = {d.error_code for d in result.diagnostics}
    assert {"E602", "E620"} <= codes, (
        f"expected the depth-cap skip AND the dropped-caller diagnostic at "
        f"depth {STATE_CLAUSE_INLINE_DEPTH_CAP + 1}, got: "
        f"{[(d.error_code, d.description[:90]) for d in result.diagnostics]}"
    )
    joined = " ".join(d.description for d in result.diagnostics)
    assert str(STATE_CLAUSE_INLINE_DEPTH_CAP) in joined, joined
    assert "exponential" in joined, joined


def test_outward_reentry_past_the_cap_is_refused() -> None:
    """Past the cap the checker refuses it, and code generation drops it.

    Without the bound, an 18-deep nest of 106 source lines expanded to ~2M
    lines of WAT — the runaway this turns into a diagnostic: E339 where the
    operations are written, and code generation's located E602 naming the
    function as the backstop.
    """
    source = _deep_nest(STATE_CLAUSE_INLINE_DEPTH_CAP + 2)
    errors = _errors(source)
    assert errors and {d.error_code for d in errors} == {"E339"}, [
        (d.error_code, d.description[:90]) for d in errors
    ]
    result = _compile(source)
    codes = {d.error_code for d in result.diagnostics}
    assert "E602" in codes, (
        f"expected the depth-cap skip, got: "
        f"{[(d.error_code, d.description[:90]) for d in result.diagnostics]}"
    )
    joined = " ".join(d.description for d in result.diagnostics)
    assert str(STATE_CLAUSE_INLINE_DEPTH_CAP) in joined, joined
    assert "exponential" in joined, joined
