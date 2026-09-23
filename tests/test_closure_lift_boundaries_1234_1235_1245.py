"""Closure lifting at refinement boundaries: #1234, #1245, #1235.

Three defects of one seam — the lifted-closure path in
`vera/codegen/closures.py` and the order `_compile_fn` drives it in.

* **#1245** — `_lift_pending_closures` ran BEFORE `_compile_postconditions`,
  so any closure created while lowering a refined RETURN guard, a tuple
  return's component guards, or an `ensures(...)` predicate was registered
  on the context and then never lifted.  The module's function table stayed
  empty, the `call_indirect` the closure's own construction emitted was
  orphaned, and the #1185 drop-propagation pass dropped the function and
  every caller: a check-green, verify-clean program compiled to ZERO
  exports.  Loud, but total.
* **#1234** — the lift worklist fed itself.  A refinement whose predicate
  contains a closure refined by the SAME type (`type R = { @Int | …
  fn(@R -> @Int) … }`, used in a signature) has each lifted closure's
  refined-formal guard lower a predicate containing that same `AnonFn`,
  which queues another closure, for ever.  `vera compile` never returned.
  The registration pre-scan has been cycle-guarded since #1232 round 7;
  this is the lift loop's own guard.
* **#1235** — the closure path emitted TOP-LEVEL formal / return refinement
  guards only.  A named function with a `Tuple<PosInt, Int>` formal gets
  per-component #746 boundary guards; a closure with the same formal
  crossed unguarded, so a violating component reaching an `AnonFn` through
  `apply_fn` was never checked where the named path checks it.

The three are tested together because they share one fix surface and one
invariant: what the closure path LOWERS must equal what the registration
derivation (`_signature_refinement_predicates`) ENUMERATES.  #1235's fix
flips that derivation's `FnDecl`-only component leg on for closures, and
the co-extension pin in `tests/test_state_exn_registration.py`
(`test_a_closure_tuple_formal_registers_what_it_now_lowers`) flipped with
it, from "nothing spurious is registered" to "what is lowered is declared".
"""

from __future__ import annotations

import threading

import pytest

from tests.checker_helpers import _check_ok
from tests.codegen_helpers import (
    _assert_call_indirect_iff_table,
    _compile,
    _run,
    _run_refine_trap,
)
from tests.verifier_helpers import _verify_ok

# =====================================================================
# #1245 — a closure created by a RETURN-position guard must be lifted
# =====================================================================

# The characterization fixture from PR #1239's review, promoted to an
# executable oracle.  `array_range(18, 21)` is [18, 19, 20]: every element
# satisfies the predicate, so the return guard passes and the length is 3 —
# a value that cannot coincide with the zero-exports failure (which
# produces no value at all) nor with an empty-array vacuous truth.
_CLOSURE_IN_RETURN_REFINEMENT = """
type Grown = { @Array<Nat> | array_all(@Array<Nat>.0, fn(@Nat -> @Bool)
  effects(pure) { @Nat.0 >= 18 }) };

private fn mk(@Array<Nat> -> @Grown)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<Nat>.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(mk(array_range(18, 21)))
}
"""

# The same predicate in PARAMETER position — lowered by `_compile_fn`
# BEFORE the lift, so it always worked.  Its presence is what makes the
# return-position failure a lift-ORDERING defect rather than a
# closure-in-a-predicate limitation.
_CLOSURE_IN_PARAM_REFINEMENT = """
type Grown = { @Array<Nat> | array_all(@Array<Nat>.0, fn(@Nat -> @Bool)
  effects(pure) { @Nat.0 >= 18 }) };

private fn take(@Grown -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@Grown.0)
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  take(array_range(18, 21))
}
"""

# The `ensures(...)` twin: the SAME ordering bug reached without any
# refinement at all, found while root-causing #1245.  A closure in a
# postcondition predicate is lowered by `_compile_postconditions` and was
# equally never lifted.
_CLOSURE_IN_ENSURES = """
public fn main(@Unit -> @Nat)
  requires(true)
  ensures(array_all(array_range(18, 21), fn(@Nat -> @Bool)
    effects(pure) { @Nat.0 >= 18 }))
  effects(pure)
{
  array_length(array_range(18, 21))
}
"""

# The guard must also ENFORCE, not merely exist: a body whose result
# violates the closure-bearing predicate traps at the return boundary.
_CLOSURE_IN_RETURN_REFINEMENT_VIOLATED = """
type Grown = { @Array<Nat> | array_all(@Array<Nat>.0, fn(@Nat -> @Bool)
  effects(pure) { @Nat.0 >= 18 }) };

private fn mk(@Array<Nat> -> @Grown)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<Nat>.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(mk(array_range(1, 4)))
}
"""


# The case the TWO passes have to agree about.  A closure struct stores its
# `closure_id` as `func_table_idx` and the table index is its position in
# `_closure_table`, so the second pass has to resume from the counter the
# first left.
#
# The BODY closure must itself contain a NESTED one, which is what makes
# this distinguishing: a nested closure's id is allocated inside
# `_compile_lifted_closure`'s own context during the first pass, so the
# outer function context never sees it.  Without the hand-back the
# return-refinement's closure reuses that id — mutation-measured as
# `duplicate func identifier $rt.anon_1` at whole-module WAT.  A body closure
# with NO nesting does not distinguish: the outer context allocated that id
# itself and is already past it, so the test would pass either way.
#
# 18 + array_length(array_map(array_range(0, 5), …)) = 18 + 5 = 23 at [0];
# the mapped array still satisfies `Grown`, so the return guard passes.
_TWO_CLOSURES_ONE_FUNCTION = """
type Grown = { @Array<Nat> | array_all(@Array<Nat>.0, fn(@Nat -> @Bool)
  effects(pure) { @Nat.0 >= 18 }) };

private fn mk(@Array<Nat> -> @Grown)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Nat>.0, fn(@Nat -> @Nat) effects(pure) {
    @Nat.0 + array_length(array_map(array_range(0, 5), fn(@Nat -> @Nat)
      effects(pure) { @Nat.0 * 2 }))
  })
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Nat> = mk(array_range(18, 21));
  @Array<Nat>.0[0]
}
"""


class TestAClosureInAReturnPositionPredicateIsLifted:
    """#1245: check-green + verify-clean must mean a runnable module."""

    def test_the_return_refinement_program_runs(self) -> None:
        _check_ok(_CLOSURE_IN_RETURN_REFINEMENT)
        _verify_ok(_CLOSURE_IN_RETURN_REFINEMENT)
        assert _run(_CLOSURE_IN_RETURN_REFINEMENT) == 3

    def test_the_param_position_control_still_runs(self) -> None:
        """The always-worked half — pins that the fix changed the right one."""
        assert _run(_CLOSURE_IN_PARAM_REFINEMENT) == 3

    def test_an_ensures_clause_closure_runs(self) -> None:
        """The same ordering defect with no refinement in sight."""
        _check_ok(_CLOSURE_IN_ENSURES)
        assert _run(_CLOSURE_IN_ENSURES) == 3

    def test_the_module_exports_and_holds_its_table(self) -> None:
        """The observable the issue names: exports, and a table for the
        `call_indirect` the predicate's closure construction emits."""
        result = _compile(_CLOSURE_IN_RETURN_REFINEMENT)
        wat = result.wat or ""
        assert 'call_indirect' in wat, wat[:400]
        _assert_call_indirect_iff_table(wat)
        assert 'export "main"' in wat, wat[:400]

    def test_the_lifted_guard_actually_enforces(self) -> None:
        """A violating return traps — the guard is emitted, not just lifted."""
        _run_refine_trap(_CLOSURE_IN_RETURN_REFINEMENT_VIOLATED)

    def test_both_passes_share_one_closure_id_space(self) -> None:
        """A NESTED body closure and a return-guard closure, one function.

        The second pass has to resume from the id the first left.  Measured
        against the mutant that drops the hand-back: `duplicate func
        identifier $rt.anon_1` at whole-module WAT, because the nested closure's
        id was allocated inside the first pass's own context and the outer
        one never saw it.  Three distinct lifted functions and a value of 23
        are the two halves of the assertion — a crossed id is either a
        duplicate identifier or a wrong dispatch, and both show here.
        """
        _check_ok(_TWO_CLOSURES_ONE_FUNCTION)
        assert _run(_TWO_CLOSURES_ONE_FUNCTION) == 23
        wat = _compile(_TWO_CLOSURES_ONE_FUNCTION).wat or ""
        names = sorted(
            line.split()[1] for line in wat.splitlines()
            if line.strip().startswith("(func $rt.anon_")
        )
        assert names == ["$rt.anon_0", "$rt.anon_1", "$rt.anon_2"], names
        _assert_call_indirect_iff_table(wat)


# =====================================================================
# #1234 — the lift worklist must not feed itself
# =====================================================================

_SELF_REFERENTIAL_IN_A_SIGNATURE = """
type SelfRef = { @Int | @Int.0 > 0 && apply_fn(fn(@SelfRef -> @Int)
  effects(pure) { @SelfRef.0 }, 3) > 0 };

private fn f(@SelfRef -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @SelfRef.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(7)
}
"""

# The control the guard must NOT catch: a refinement whose predicate
# contains a closure refined by a DIFFERENT refinement, which itself
# contains a closure over an unrefined base.  Two distinct `AnonFn` nodes,
# a finite chain — the lift must walk it and the program must run.  `Inner`
# holds for 4 (`4 > 0`), so `g(9)` returns 9: a value that coincides with
# neither 0 nor the argument of any predicate.
_NESTED_NON_CYCLIC_REFINEMENT = """
type Inner = { @Int | @Int.0 > 0 };

type Outer = { @Int | @Int.0 > 0 && apply_fn(fn(@Inner -> @Int)
  effects(pure) { @Inner.0 }, 4) > 0 };

private fn g(@Outer -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Outer.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(9)
}
"""

# --- cycles longer than one hop ---------------------------------------
# The guard is keyed on the lift CHAIN, so it catches a cycle of any
# length, not only a type refined through itself.  Both of these HANG the
# compiler without it — a termination regression here would present in CI
# as a job that never finishes, which is why they are pinned under the
# wall-clock harness rather than merely compiled.

# A -> B -> A.  Neither type's predicate contains its OWN closure, so the
# one-hop reading of the guard would miss this entirely.
_MUTUAL_CYCLE = """
type A = { @Int | @Int.0 > 0 && apply_fn(fn(@B -> @Int)
  effects(pure) { @B.0 }, 3) > 0 };

type B = { @Int | @Int.0 > 0 && apply_fn(fn(@A -> @Int)
  effects(pure) { @A.0 }, 3) > 0 };

private fn f(@A -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @A.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(7)
}
"""

# P -> Q -> R -> P.  Three hops: an ancestry depth of one or two would
# still run for ever here.
_THREE_CYCLE = """
type P = { @Int | @Int.0 > 0 && apply_fn(fn(@Q -> @Int)
  effects(pure) { @Q.0 }, 3) > 0 };

type Q = { @Int | @Int.0 > 0 && apply_fn(fn(@R -> @Int)
  effects(pure) { @R.0 }, 3) > 0 };

type R = { @Int | @Int.0 > 0 && apply_fn(fn(@P -> @Int)
  effects(pure) { @P.0 }, 3) > 0 };

private fn f(@P -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @P.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(7)
}
"""

# --- the two shapes a module-wide seen-set breaks ----------------------
# The guard is a CHAIN, not a set of everything already lifted.  These two
# programs are the difference: each legitimately lifts ONE predicate's
# closure more than once, from positions that are not each other's
# ancestors, so a seen-set refuses the second lift, drops the enclosing
# function and produces zero exports.  Measured: with the seen-set mutant
# both go red here and NOTHING else in the suite does.

# The code comment's own worked example: two refined formals of one type.
# `R`'s predicate holds a single `AnonFn` node, and each formal's boundary
# guard lifts it — twice, siblings rather than ancestor and descendant.
# The operands are WEIGHTED, not summed: `@R.0` is the most recent binding
# (the SECOND parameter, 4) and `@R.1` the first (9), so `f(9, 4)` = 17 and
# a slot-order regression reads 22 rather than hiding behind `9 + 4 = 4 + 9`.
_TWO_REFINED_FORMALS_OF_ONE_TYPE = """
type R = { @Int | @Int.0 > 0 && apply_fn(fn(@Int -> @Int)
  effects(pure) { @Int.0 }, 4) > 0 };

private fn f(@R, @R -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @R.0 * 2 + @R.1
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(9, 4)
}
"""

# A diamond: `Outer`'s predicate closure is refined by `Inner`, and the
# same function ALSO takes an `@Inner` formal directly — so `Inner`'s
# closure is reached by two routes, once as a descendant of `Outer`'s lift
# and once at the top of its own.  Finite, and it must run.  Weighted like
# the fixture above — and by a DIFFERENT factor, so neither fixture can
# pass the other's oracle: the two slots here bind two different refined
# types, so a swap would also swap which boundary guard sees which value,
# and `g(9, 4)` = 94 where a swap reads 49.
_DIAMOND_ANCESTRY = """
type Inner = { @Int | @Int.0 > 0 && apply_fn(fn(@Int -> @Int)
  effects(pure) { @Int.0 }, 4) > 0 };

type Outer = { @Int | @Int.0 > 0 && apply_fn(fn(@Inner -> @Int)
  effects(pure) { @Inner.0 }, 5) > 0 };

private fn g(@Outer, @Inner -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Outer.0 * 10 + @Inner.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(9, 4)
}
"""


def _compile_within(source: str, budget_s: float) -> object:
    """Compile *source* on a daemon thread, failing if it outlives *budget_s*.

    A non-terminating lift must not hang the suite: the worker is a daemon,
    so an unfixed compiler leaves a live thread that never blocks
    interpreter exit while this assertion fails immediately.  ``pytest.fail``
    rather than ``assert`` so the message survives ``python -O``.

    **The leaked thread is accepted, deliberately** (PR #1250's closeout
    left the question open; this is the answer).  When the guard holds — the
    only state the suite is ever green in — the compile finishes in
    milliseconds, the thread is joined, and nothing leaks.  A leak requires
    the guard to be BROKEN, in which case the run is already failing and its
    only remaining job is to report why rather than hang CI until the job
    timeout.  A leaked daemon thread spinning in the compiler for the rest
    of a red run costs CPU and nothing else: it holds no lock the main
    thread waits on, and daemon threads do not block interpreter exit.

    A subprocess would remove even that, and was considered and rejected:
    the worker returns a ``CompileResult`` the caller inspects, so a
    subprocess must either serialize it — it holds ``Diagnostic`` objects
    carrying AST nodes, so no safe format round-trips it as-is — or
    re-derive every assertion from process output, and Windows' spawn start
    method would re-import this fixture module in the child.  That is real
    machinery, load-bearing only in runs that are already failing, which is
    the wrong trade.
    """
    box: list[object] = []
    err: list[BaseException] = []

    def _work() -> None:
        try:
            box.append(_compile(source))
        except BaseException as exc:  # noqa: BLE001 — re-raised on the main thread
            err.append(exc)

    t = threading.Thread(target=_work, daemon=True)
    t.start()
    # `join` returns either when the worker dies or after the budget, so
    # `is_alive()` IS the hang verdict.  A second `elapsed < budget_s`
    # assertion after it could never catch a hang this misses — it is
    # reachable only once the worker has completed — and could only ever go
    # red on the race where the worker finishes between `join` returning at
    # the budget and this check, reporting a bare float instead of the
    # message below (PR #1283 review).
    t.join(budget_s)
    if t.is_alive():
        pytest.fail(
            f"compile did not terminate within {budget_s}s (#1234: the "
            "closure-lift worklist is feeding itself)"
        )
    if err:
        raise err[0]
    return box[0]


class TestTheLiftQueueIsCycleGuarded:
    """#1234: a cyclic refinement in a signature must terminate.

    Three properties, and each needs its own shape.  That the guard FIRES
    is pinned by the self-reference; that it fires on cycles of ANY LENGTH
    by the mutual and three-type cycles (a one-hop reading of it misses
    both, and the symptom is a CI job that never ends); and that it is
    keyed on the lift CHAIN rather than on everything already lifted by the
    two shapes below, which legitimately lift one predicate's closure more
    than once.

    Mutation-measured, replacing the chain key with a seen set scoped to one
    lift run (`if id(anon_fn) in seen` over a set accumulated across the
    worklist): `test_two_refined_formals_of_one_type_both_lift` and
    `test_a_diamond_reaches_one_refinement_by_two_routes` go RED — the
    enclosing function is dropped and the module exports nothing — and they
    are the ONLY two tests in the suite that move.  Nothing in the corpus
    lifts one `AnonFn` node twice (`ch09_prelude`, the closest candidate,
    lifts four distinct nodes exactly once each), so no corpus program can
    stand in for these: without them the distinction between a chain and a
    seen set is untested, which is what it was.
    """

    @pytest.mark.parametrize(
        ("source", "closure_sig"),
        [
            pytest.param(
                _SELF_REFERENTIAL_IN_A_SIGNATURE,
                "fn(@SelfRef -> @Int)", id="self_reference"),
            pytest.param(
                _MUTUAL_CYCLE, "fn(@B -> @Int)", id="mutual_two_cycle"),
            pytest.param(
                _THREE_CYCLE, "fn(@Q -> @Int)", id="three_cycle"),
        ],
    )
    def test_it_terminates_with_a_loud_skip(
        self, source: str, closure_sig: str,
    ) -> None:
        """Bounded termination, and the skip names the closure it refused.

        The wall-clock budget is the assertion that matters: every one of
        these ran for ever before the guard, so a regression is a hang, and
        a hang in CI is a job that has to be killed rather than a red test.
        """
        _check_ok(source)
        result = _compile_within(source, 60.0)
        diags = getattr(result, "diagnostics", [])
        codes = [d.error_code for d in diags]
        assert "E602" in codes, [(d.error_code, d.description) for d in diags]
        said = " ".join(
            d.description for d in diags if d.error_code == "E602")
        # The skip must NAME the closure it refused and say WHY, not merely
        # say "skipped".  "cyclic" rather than "self-referential": the guard
        # catches a cycle of any length, and two of these three are not
        # self-references at all.
        assert closure_sig in said, said
        assert "cyclic refinement" in said.lower(), said

    def test_a_finite_nested_refinement_chain_still_lifts_and_runs(
        self,
    ) -> None:
        """The control: the guard must fire on a CYCLE, not on nesting."""
        _check_ok(_NESTED_NON_CYCLIC_REFINEMENT)
        assert _run(_NESTED_NON_CYCLIC_REFINEMENT) == 9

    def test_two_refined_formals_of_one_type_both_lift(self) -> None:
        """The code comment's own worked example, as an executable claim.

        `fn f(@R, @R -> @Int)` guards two formals of one refined type, so
        `R`'s single `AnonFn` node is lifted twice — as siblings, neither
        one an ancestor of the other.  A module-wide seen-set refuses the
        second and drops `f`; the chain key does not.  The oracle is
        weighted (`@R.0 * 2 + @R.1`), so it pins WHICH slot each guard saw
        as well as that both lifts happened.
        """
        _check_ok(_TWO_REFINED_FORMALS_OF_ONE_TYPE)
        assert _run(_TWO_REFINED_FORMALS_OF_ONE_TYPE) == 17

    def test_a_diamond_reaches_one_refinement_by_two_routes(self) -> None:
        """`Inner` is reached under `Outer`'s lift AND at the top of its own.

        The second reach is a descendant of the first in one route and a
        root in the other — finite either way, and a seen-set cannot tell
        that from a cycle.  Weighted (`@Outer.0 * 10 + @Inner.0`) because
        the two slots bind two DIFFERENT refined types here: a swap would
        also swap which boundary guard saw which value.
        """
        _check_ok(_DIAMOND_ANCESTRY)
        assert _run(_DIAMOND_ANCESTRY) == 94


# =====================================================================
# #1235 — closure boundaries get the tuple-COMPONENT guards too
# =====================================================================

# The boundary under test is the FORMAL, so neither body reads the tuple:
# the guard has to fire on the value crossing, not on anything the callee
# does with it.  `probe` scales the result so the passing oracle (70) is a
# constant no default or dropped-function path produces.
_CLOSURE_TUPLE_COMPONENT = """
type PosInt = { @Int | @Int.0 > 0 };
type PairToInt = fn(Tuple<PosInt, Int> -> Int) effects(pure);

private fn make(@Unit -> @PairToInt)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Tuple<PosInt, Int> -> @Int) effects(pure) { 7 }
}

private fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @PairToInt = make(());
  apply_fn(@PairToInt.0, Tuple(@Int.0, 2)) * 10
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(FIRST)
}
"""

# The NAMED twin of the same boundary, so the two paths are compared on one
# program shape rather than on the closure path alone.
_NAMED_TUPLE_COMPONENT = """
type PosInt = { @Int | @Int.0 > 0 };

private fn takes(@Tuple<PosInt, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

private fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  takes(Tuple(@Int.0, 2)) * 10
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(FIRST)
}
"""


def _at(source: str, first: str) -> str:
    return source.replace("FIRST", first)


class TestAClosureTupleFormalIsComponentGuarded:
    """#1235: the closure path enforces what the named path enforces."""

    def test_the_closure_traps_on_a_violating_component(self) -> None:
        """`0 - 5` violates `PosInt` in component 0 — it must not cross."""
        _run_refine_trap(_at(_CLOSURE_TUPLE_COMPONENT, "0 - 5"))

    def test_the_named_path_traps_identically(self) -> None:
        """The oracle the closure path is being held to."""
        _run_refine_trap(_at(_NAMED_TUPLE_COMPONENT, "0 - 5"))

    def test_the_passing_path_still_runs(self) -> None:
        """7 satisfies `PosInt`: 70 through both paths, not a trap."""
        assert _run(_at(_CLOSURE_TUPLE_COMPONENT, "7")) == 70
        assert _run(_at(_NAMED_TUPLE_COMPONENT, "7")) == 70


# The RETURN side of the same boundary (PR #1250 review).  The class above
# pins the FORMAL only, so `ret_has_components` and the scalar return-guard
# leg in `_compile_lifted_closure` were reached by no test at all: forcing
# `ret_has_components` to False leaves that class green.
#
# The components are deliberately ASYMMETRIC — component 0 is the refined
# `PosInt` and component 1 is the constant 2, which SATISFIES `> 0`.  An
# emitter that read the wrong component's offset would therefore check `2 >
# 0`, pass, and let the violating value through: the index is pinned by the
# violating case rather than assumed.
_CLOSURE_TUPLE_RETURN = """
type PosInt = { @Int | @Int.0 > 0 };
type IntToPair = fn(Int -> Tuple<PosInt, Int>) effects(pure);

private fn make(@Unit -> @IntToPair)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Tuple<PosInt, Int>) effects(pure) { Tuple(@Int.0, 2) }
}

private fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToPair = make(());
  let @Tuple<PosInt, Int> = apply_fn(@IntToPair.0, @Int.0);
  match @Tuple<PosInt, Int>.0 {
    Tuple(@PosInt, @Int) -> @PosInt.0 * 10
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(FIRST)
}
"""

# Its named twin, built from the same components, as the oracle.
_NAMED_TUPLE_RETURN = """
type PosInt = { @Int | @Int.0 > 0 };

private fn mkpair(@Int -> @Tuple<PosInt, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Int.0, 2)
}

private fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<PosInt, Int> = mkpair(@Int.0);
  match @Tuple<PosInt, Int>.0 {
    Tuple(@PosInt, @Int) -> @PosInt.0 * 10
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(FIRST)
}
"""


class TestAClosureTupleReturnIsComponentGuarded:
    """#1235's return half — `ret_has_components` and the epilogue it gates.

    Mutation-measured: forcing `ret_has_components` to False in
    `_compile_lifted_closure` turns `test_the_closure_return_traps_on_a_
    violating_component` RED and leaves the formal class above green, which
    is why this exists as its own fixture rather than as another parameter
    of the formal one.
    """

    def test_the_closure_return_traps_on_a_violating_component(self) -> None:
        """A closure RETURNING `Tuple(-5, 2)` must not hand it back."""
        _run_refine_trap(_at(_CLOSURE_TUPLE_RETURN, "0 - 5"))

    def test_the_named_return_traps_identically(self) -> None:
        """The oracle the closure return is being held to."""
        _run_refine_trap(_at(_NAMED_TUPLE_RETURN, "0 - 5"))

    def test_the_passing_return_still_runs(self) -> None:
        """7 satisfies `PosInt`: 70 through both paths, not a trap."""
        assert _run(_at(_CLOSURE_TUPLE_RETURN, "7")) == 70
        assert _run(_at(_NAMED_TUPLE_RETURN, "7")) == 70
