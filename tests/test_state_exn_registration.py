"""#1210: State/Exn host-import registration must cover the whole handler.

Codegen registers a `State<T>` host-cell import quadruple and an `Exn<E>`
WASM tag by walking each function for `handle` expressions.  The walk
descended a `HandleExpr`'s BODY only — not its clause bodies, not a clause's
`with` state-update expression, and not the handler's own state-init
expression.  A family reached only through one of those went unregistered
while the lowering happily emitted its calls, so a check-green, verify-clean
program died at whole-module WAT compilation with `unknown func
$vera.state_push_Nat` / `unknown tag $exn_Int`.

It also stopped at the function BODY, so a handler in a lowered CONTRACT —
a `requires` / `ensures` predicate, an `assert`, or a `decreases` measure —
was never registered while its calls were emitted.

The same walk skipped an `i32_pair` cell type in silence, where the
declared-effect path rejects it loudly (`E607`): `handle[State<String>]`
inside a `pure` function registered nothing and emitted the calls anyway.
Its Exn twin discarded the registration verdict outright, so
`handle[Exn<Unit>]` in a `pure` function compiled to a `throw` against an
undeclared tag where the declared-row spelling was a clean `E612`.

Round 5 found three more positions of the same shape, none of which the
corpus contained: a destructuring `let`'s value (`LetDestruct` was absent
from the `Block` dispatch of BOTH walkers), a module call's ARGUMENTS
(`ModuleCall` was dismissed as the imported module's business — true of the
callee, false of the args), and a signature refinement predicate (reached
through the alias table, so nothing structural finds it).  The first also
disarmed the round-3 uncompilable-payload gate: `handle[Exn<Unit>]` in a
destructuring let compiled to `unknown tag` where its `LetStmt` twin is a
clean E612 drop.

Two kinds of test here.  The shape tests pin each gap on a program whose
value is derived from the language rules, so a fix that registers the
family but lowers it wrongly still fails.  The differential is the
cross-component invariant itself — for every corpus program that compiles,
every `state_*` / `exn_*` symbol the emitted WAT REFERENCES has a matching
import or tag DECLARATION, and every HANDLER-BEARING module validates —
which is the shape of check this bug class needs: a green unit suite cannot
see a desync between the registration pass and the lowering pass, only
running both and comparing can.  The validation leg exists because the name
comparison alone is blind to a symbol declared at the WRONG TYPE, which is
invalid WASM the set difference reports as perfectly balanced.  Its scope
and its two limits are stated on the test itself; the walkers' own
completeness is the fold's (`vera/fold.py`, held to the AST by
`tests/test_expr_fold.py`), because a corpus-anchored differential cannot
flag a position no corpus program contains.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

import pytest
import wasmtime

from tests.codegen_helpers import _compile, _run, exceptions_engine
from tests.checker_helpers import _check_ok
from tests.verifier_helpers import _verify_ok
from vera import ast
from vera.errors import VeraError
from vera.parser import parse_file, parse_to_ast
from vera.resolver import ResolvedModule
from vera.transform import transform
from vera.codegen import CodeGenerator, compile as codegen_compile, execute
from tests import pipeline

_MAIN = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(())
}
"""

# --- a nested handler inside a CLAUSE BODY ---------------------------
# `State<Bool>` is reached only from the Nat handler's get clause, so the
# walk never saw it: `unknown func $vera.state_push_Bool`.
#   get(()) -> Nat clause captures 8, the nested Bool cell reads true,
#              resume(8); outer Int cell is untouched at 111
# => 8 + 111 = 119.
_HANDLE_IN_CLAUSE_BODY = """
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
        let @Bool = handle[State<Bool>](@Bool = true) {
          get(@Unit) -> { resume(@Bool.0) },
          put(@Bool) -> { resume(()) }
        } in {
          get(())
        };
        resume(if @Bool.0 then { @Nat.0 } else { 0 })
      },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    };
    nat_to_int(@Nat.0) + get(())
  }
}
"""

# --- a nested handler inside the STATE INIT expression ----------------
# `State<Nat>` is reached only from the outer handler's init expression.
#   nested: init 4, get clause doubles it -> 8; outer init = 8 + 1 = 9
# => 9.
_HANDLE_IN_STATE_INIT = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = nat_to_int(handle[State<Nat>](@Nat = 4) {
    get(@Unit) -> { resume(@Nat.0 + @Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  }) + 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""

# --- a nested handler inside a clause's `with` state update -----------
# `State<Nat>` is reached only from the put clause's `with` expression.
#   put(10)  -> stores 10, then `with` overrides with 10 + 5 = 15
# => 15.
_HANDLE_IN_WITH_EXPR = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.1 + nat_to_int(handle[State<Nat>](@Nat = 5) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    })
  } in {
    put(10);
    get(())
  }
}
"""

# --- an Exn handler inside a clause body ------------------------------
# The `$exn_Int` TAG is reached only from the State get clause's body:
# `unknown tag $exn_Int`.
#   get(()) -> captures state 5; the nested Exn handler catches throw(2)
#              and returns 42; resume(42 + 5)
# => 47.
_EXN_IN_CLAUSE_BODY = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> {
      let @Int = handle[Exn<Int>] {
        throw(@Int) -> { @Int.0 + 40 }
      } in {
        throw(2);
        999
      };
      resume(@Int.0 + @Int.1)
    },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""

# --- a handler inside a DESTRUCTURING let's value ---------------------
# `LetDestruct` was absent from both walkers entirely (round 5): the `Block`
# branch dispatched `LetStmt` and `ExprStmt` only, so a destructuring let's
# value was never walked while codegen lowered it like any other statement.
#   the nested handler's get clause resumes 3 + 100 = 103; pairn(103) is
#   Tuple(103, 4), and `@Nat.1` is the FIRST-bound component (De Bruijn)
# => 103.
_HANDLE_IN_LETDESTRUCT = """
private fn pairn(@Nat -> @Tuple<Nat, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Nat.0, 4)
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = pairn(handle[State<Nat>](@Nat = 3) {
    get(@Unit) -> { resume(@Nat.0 + 100) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  });
  nat_to_int(@Nat.1)
}
"""

# The Exn twin of the same position: `unknown tag $exn_Int`.
#   the handler catches throw(2) and returns 2 + 40 = 42; pair(42) is
#   Tuple(42, 4), and `@Int.1` is the first-bound component
# => 42.
_EXN_IN_LETDESTRUCT = """
private fn pair(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Int.0, 4)
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = pair(handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 + 40 }
  } in {
    throw(2);
    999
  });
  @Int.1
}
"""

# --- a handler inside a SIGNATURE REFINEMENT predicate ----------------
# The third position (round 5): a `{ @Base | P }` parameter or return type has
# `P` emitted as a boundary guard in this function's prologue/epilogue, so a
# handler written in `P` is lowered here.  The predicate is reached through
# the ALIAS table, not structurally from the body, so no amount of walking
# the AST from `decl.body` finds it — `unknown func $vera.state_push_Nat`.
#   the guard runs, the handler resumes 3 > 0 holds, `refined(10)` returns 10
# => 10.
_HANDLE_IN_PARAM_REFINEMENT = """
type Big = { @Int | nat_to_int(handle[State<Nat>](@Nat = 3) {
  get(@Unit) -> { resume(@Nat.0) },
  put(@Nat) -> { resume(()) }
} in {
  get(())
}) > 0 && @Int.0 > 5 };

private fn refined(@Big -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Big.0
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  refined(10)
}
"""

# The RETURN-type half of the same position — a different emission site
# (epilogue rather than prologue) reached from the same enumeration.
_HANDLE_IN_RETURN_REFINEMENT = """
type Big = { @Int | nat_to_int(handle[State<Nat>](@Nat = 3) {
  get(@Unit) -> { resume(@Nat.0) },
  put(@Nat) -> { resume(()) }
} in {
  get(())
}) > 0 && @Int.0 > 5 };

private fn refined(@Unit -> @Big)
  requires(true)
  ensures(true)
  effects(pure)
{
  10
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  refined(())
}
"""

# --- the same predicate, reached through a TUPLE COMPONENT --------------
# Round 5 enumerated a named function's own params and return.  A tuple
# parameter carries no top-level refinement, so `Big` is reached only by
# DECOMPOSING it — `_emit_component_refinement_guards` lowers the same
# predicate per component, and nothing registered it.
#   the component guard runs, 3 > 0 and 10 > 5 hold, the component is 10
# => 10.
_HANDLE_IN_TUPLE_PARAM_COMPONENT = """
type Big = { @Int | nat_to_int(handle[State<Nat>](@Nat = 3) {
  get(@Unit) -> { resume(@Nat.0) },
  put(@Nat) -> { resume(()) }
} in {
  get(())
}) > 0 && @Int.0 > 5 };

private fn refined(@Tuple<Big, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Big, @Int> = @Tuple<Big, Int>.0;
  @Big.0
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  refined(Tuple(10, 2))
}
"""

# The RETURN half of the component decomposition — a different emission site
# (`_compile_postconditions`) reached from the same enumeration.
_HANDLE_IN_TUPLE_RETURN_COMPONENT = """
type Big = { @Int | nat_to_int(handle[State<Nat>](@Nat = 3) {
  get(@Unit) -> { resume(@Nat.0) },
  put(@Nat) -> { resume(()) }
} in {
  get(())
}) > 0 && @Int.0 > 5 };

private fn refined(@Unit -> @Tuple<Big, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(10, 2)
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Big, @Int> = refined(());
  @Big.0
}
"""

# --- and through a CLOSURE's signature ---------------------------------
# `closures.py` guards a refined formal in the lifted body's prologue.  The
# walkers descend an AnonFn's BODY (#597) but not its signature, so this
# predicate was lowered into a lifted closure with nothing registering it.
#   the formal guard runs, `@Big.0 * 2` with 10 => 20.
_HANDLE_IN_CLOSURE_PARAM_REFINEMENT = """
type Big = { @Int | nat_to_int(handle[State<Nat>](@Nat = 3) {
  get(@Unit) -> { resume(@Nat.0) },
  put(@Nat) -> { resume(()) }
} in {
  get(())
}) > 0 && @Int.0 > 5 };

type BigToInt = fn(Big -> Int) effects(pure);

private fn make(@Unit -> @BigToInt)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Big -> @Int) effects(pure) { @Big.0 * 2 }
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @BigToInt = make(());
  apply_fn(@BigToInt.0, 10)
}
"""

# The closure RETURN half — the #1032 refined-return guard, appended to the
# lifted body rather than emitted in its prologue.
_HANDLE_IN_CLOSURE_RETURN_REFINEMENT = """
type Big = { @Int | nat_to_int(handle[State<Nat>](@Nat = 3) {
  get(@Unit) -> { resume(@Nat.0) },
  put(@Nat) -> { resume(()) }
} in {
  get(())
}) > 0 && @Int.0 > 5 };

type IntToBig = fn(Int -> Big) effects(pure);

private fn make(@Unit -> @IntToBig)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Big) effects(pure) { @Int.0 * 2 }
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToBig = make(());
  apply_fn(@IntToBig.0, 10)
}
"""

_SHAPES = [
    ("handle_in_clause_body", _HANDLE_IN_CLAUSE_BODY, 119),
    ("handle_in_state_init", _HANDLE_IN_STATE_INIT, 9),
    ("handle_in_with_expr", _HANDLE_IN_WITH_EXPR, 15),
    ("exn_in_clause_body", _EXN_IN_CLAUSE_BODY, 47),
    ("handle_in_letdestruct", _HANDLE_IN_LETDESTRUCT, 103),
    ("exn_in_letdestruct", _EXN_IN_LETDESTRUCT, 42),
    ("handle_in_param_refinement", _HANDLE_IN_PARAM_REFINEMENT, 10),
    ("handle_in_return_refinement", _HANDLE_IN_RETURN_REFINEMENT, 10),
    ("handle_in_tuple_param_component",
     _HANDLE_IN_TUPLE_PARAM_COMPONENT, 10),
    ("handle_in_tuple_return_component",
     _HANDLE_IN_TUPLE_RETURN_COMPONENT, 10),
    ("handle_in_closure_param_refinement",
     _HANDLE_IN_CLOSURE_PARAM_REFINEMENT, 20),
    ("handle_in_closure_return_refinement",
     _HANDLE_IN_CLOSURE_RETURN_REFINEMENT, 20),
]

# --- the i32_pair cell the walk skipped in silence --------------------
# The handler discharges the effect, so the declared-effect E607 gate never
# runs on `probe` — the body walk is the only thing that sees this cell, and
# it refused to register it without saying so while the lowering emitted
# `state_push_String`.  Must be the same loud diagnostic the declared path
# gives, not invalid WASM.
_STATE_STRING_IN_PURE_FN = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<String>](@String = "hi") {
    get(@Unit) -> { resume(@String.0) },
    put(@String) -> { resume(()) }
  } in {
    string_length(get(()))
  }
}
"""


@pytest.mark.parametrize(
    ("source", "expected"),
    [pytest.param(s, e, id=i) for i, s, e in _SHAPES],
)
def test_handler_family_reached_only_off_the_body_is_registered(
    source: str, expected: int,
) -> None:
    """Each scan gap: check-green and verify-clean must mean compilable.

    Pre-fix every one of these died at whole-module WAT compilation with an
    unknown func / unknown tag, which is the loudest possible way to say the
    registration pass and the lowering pass disagreed.
    """
    program = source + _MAIN
    _check_ok(program)
    _verify_ok(program)
    assert _run(program) == expected


# =====================================================================
# Registration EQUALS emission (#1210 round 7)
# =====================================================================
#
# The shapes above pin the under-registration direction: a predicate that is
# lowered must be registered.  The tests below pin the other one — a
# predicate that is NOT lowered must NOT be registered, because an import
# declared for a guard nobody emits is a host obligation nothing calls.  Both
# directions come off ONE derivation
# (`ContractsMixin._signature_refinement_predicates`), so they are properties
# of a single function rather than of two that happen to agree.

# A closure formal typed as a refined TUPLE.  This fixture pinned the
# over-registration direction for as long as the closure path emitted
# top-level formal / return guards only: `Big`'s predicate was lowered
# NOWHERE, so declaring its `State<Nat>` family would have been four host
# obligations nothing calls (measured: exactly 4 spurious state imports).
# #1235 flipped the emitter — `_compile_lifted_closure` now consumes the same
# `_tuple_component_guard_sites` decomposition the named path consumes — so
# the predicate IS lowered here and the family MUST be declared.  The
# fixture's job is unchanged: registration equals emission.  Which side of
# the equality it pins moved with the emitter, exactly as this test's
# docstring said it would.
_CLOSURE_TUPLE_FORMAL = """
type Big = { @Int | nat_to_int(handle[State<Nat>](@Nat = 3) {
  get(@Unit) -> { resume(@Nat.0) },
  put(@Nat) -> { resume(()) }
} in {
  get(())
}) > 0 && @Int.0 > 5 };

type BigPair = Tuple<Big, Int>;
type PairToInt = fn(BigPair -> Int) effects(pure);

private fn make(@Unit -> @PairToInt)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@BigPair -> @Int) effects(pure) { 1 }
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @PairToInt = make(());
  apply_fn(@PairToInt.0, Tuple(10, 2))
}
"""

# The two bails the derivation inherits from `_refinement_guard_parts`, each
# with a handler in the predicate so an over-registration would show.  A
# nested refinement base is an E618 with NO guard; an erased (`@Unit`) base
# emits no guard either.  Both were `continue`s in the round-5 enumeration
# and are now the emitter's own decisions, reached through the same helper —
# this pins that the behaviour did not move.
_NESTED_REFINEMENT_BASE = """
type Inner = { @Int | @Int.0 > 0 };
type Outer = { @Inner | nat_to_int(handle[State<Nat>](@Nat = 3) {
  get(@Unit) -> { resume(@Nat.0) },
  put(@Nat) -> { resume(()) }
} in {
  get(())
}) > 0 };

private fn probe(@Outer -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Outer.0
}
"""

_ERASED_REFINEMENT_BASE = """
type BigU = { @Unit | nat_to_int(handle[State<Nat>](@Nat = 3) {
  get(@Unit) -> { resume(@Nat.0) },
  put(@Nat) -> { resume(()) }
} in {
  get(())
}) > 0 };

private fn refined(@BigU -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  refined(())
}
"""


def test_a_closure_tuple_formal_registers_what_it_now_lowers() -> None:
    """Component decomposition covers a closure signature, both halves.

    Component decomposition was a `FnDecl`-only leg of the derivation because
    it was a `FnDecl`-only leg of the EMITTERS: enumerating a closure's tuple
    components while nothing lowered them would have declared a `State<Nat>`
    import quadruple that no instruction in the module ever calls.  #1235
    made `_compile_lifted_closure` consume the same
    `_tuple_component_guard_sites` decomposition the named path consumes, so
    the leg is unconditional and this fixture pins the OTHER direction of the
    same equality — the predicate is lowered into the lifted closure's
    prologue, so its family must be declared, and the module must run rather
    than dying at whole-module WAT with `unknown func $vera.state_push_Nat`.
    """
    program = _CLOSURE_TUPLE_FORMAL + _MAIN
    _check_ok(program)
    assert _run(program) == 1
    wat = _compile(program).wat or ""
    assert sorted(set(_STATE_DECL.findall(wat))) == [
        "$vera.state_get_Nat",
        "$vera.state_pop_Nat",
        "$vera.state_push_Nat",
        "$vera.state_put_Nat",
    ], (
        "the closure's component guard lowers `Big`'s predicate, so its "
        "State family must be declared: "
        f"{sorted(set(_STATE_DECL.findall(wat)))}"
    )


def test_the_nested_refinement_bail_registers_nothing() -> None:
    """E618 rejects the guard, so nothing about it may be registered."""
    result = _compile(_NESTED_REFINEMENT_BASE + _MAIN)
    codes = [d.error_code for d in result.diagnostics if d.severity == "error"]
    assert "E618" in codes, (
        f"expected the nested-refinement rejection, got: {result.diagnostics}"
    )
    assert not _STATE_DECL.findall(result.wat or ""), (
        "a rejected guard emits no calls, so it must declare no imports"
    )


def test_the_erased_base_bail_registers_nothing() -> None:
    """A `@Unit`-based refinement has no local to check, so no guard, so no
    import — and the program still runs."""
    program = _ERASED_REFINEMENT_BASE + _MAIN
    _check_ok(program)
    _verify_ok(program)
    assert _run(program) == 7
    assert not _STATE_DECL.findall(_compile(program).wat or ""), (
        "an erased base emits no guard, so it must declare no imports"
    )


_SELF_REFERENTIAL_REFINEMENT = """
type SelfRef = { @Int | @Int.0 > 0 && apply_fn(fn(@SelfRef -> @Int)
  effects(pure) { @SelfRef.0 }, 3) > 0 };

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""


def test_the_closure_signature_leg_is_cycle_guarded() -> None:
    """A refinement whose predicate contains a closure refined by ITSELF.

    `type SelfRef = { @Int | … fn(@SelfRef -> @Int) … }` type-checks, and the
    signature leg added in round 7 walks that closure's formals — which
    resolve back to `SelfRef`, whose predicate contains the same closure.
    Unguarded, the pre-scan walks that cycle until the interpreter stops it,
    turning a check-green program into a raw `RecursionError` traceback.

    Both halves are asserted: the walk TERMINATES, and the guard is what
    terminates it (with the stack neutered, the same walk blows the Python
    recursion limit).  A cycle-guard test that only asserts termination
    passes just as well when the cycle was never reachable.
    """
    gen = CodeGenerator(
        source=_SELF_REFERENTIAL_REFINEMENT, file="<cycle>")
    gen.compile_program(parse_to_ast(_SELF_REFERENTIAL_REFINEMENT))
    parts = gen._refinement_guard_parts(
        ast.NamedType(name="SelfRef", type_args=None))
    assert parts is not None, (
        "the fixture must resolve to a refinement, or the cycle is not "
        "reachable and this test is vacuous"
    )
    predicate = parts[0]

    gen._unregistrable_state_cells = []
    gen._unregistrable_exn_tags = []
    gen._scan_expr_for_handlers(predicate)  # must terminate

    class _NoGuard(set):  # type: ignore[type-arg]
        """The cycle-guard stack, neutered: nothing is ever recorded."""

        def add(self, value: object) -> None:
            pass

    gen._anon_sig_scan_stack = _NoGuard()
    with pytest.raises(RecursionError):
        gen._scan_expr_for_handlers(predicate)


def test_uncompilable_cell_type_in_a_handled_body_is_loud() -> None:
    """An `i32_pair` State cell reached only from a body is E607, not silence.

    The declared-effect path already rejects `State<String>` with E607; the
    body walk must agree rather than skipping registration and leaving the
    lowering to emit calls to imports that were never declared.
    """
    result = _compile(_STATE_STRING_IN_PURE_FN + _MAIN)
    codes = {d.error_code for d in result.diagnostics}
    assert "E607" in codes, (
        "expected the E607 unsupported-State-cell diagnostic, got: "
        f"{[(d.error_code, d.description[:80]) for d in result.diagnostics]}"
    )
    # And specifically NOT the symptom it used to produce.
    joined = " ".join(d.description for d in result.diagnostics)
    assert "state_push_String" not in joined, joined


# --- the Exn twin of the i32_pair cell --------------------------------
# `Exn<Unit>` has no WAT payload type, so the tag cannot be declared.  The
# DECLARED-row spelling has always been a clean E612 function drop; the
# handler-walk spelling registered nothing, DISCARDED the verdict, and let
# the function compile — `unknown tag $exn_Unit` at whole-module WAT.  The
# two paths must reach the same verdict on the same payload type.
_EXN_UNIT_IN_PURE_FN = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Unit>] {
    throw(@Unit) -> { 0 - 1 }
  } in {
    throw(());
    5
  }
}
"""

# Its declared-row twin: the same payload type reached by the gate instead.
_EXN_UNIT_DECLARED_ROW = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Unit>>)
{
  throw(());
  5
}
"""

# And the round-5 bypass: the identical payload in a DESTRUCTURING let's
# value.  The gate is driven by the same walk, so an unwalked position does
# not merely miss a registration — it silently disarms the gate too, and
# `handle[Exn<Unit>]` here compiled to `unknown tag $exn_Unit` where its
# `LetStmt` twin (above) is a clean E612 function drop.
_EXN_UNIT_IN_LETDESTRUCT = """
private fn pair(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Int.0, 4)
}

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = pair(handle[Exn<Unit>] {
    throw(@Unit) -> { 0 - 1 }
  } in {
    7
  });
  @Int.1
}
"""


@pytest.mark.parametrize(
    "source",
    [
        pytest.param(_EXN_UNIT_IN_PURE_FN, id="handler_walk"),
        pytest.param(_EXN_UNIT_DECLARED_ROW, id="declared_row"),
        pytest.param(_EXN_UNIT_IN_LETDESTRUCT, id="letdestruct_value"),
    ],
)
def test_uncompilable_exn_payload_is_the_same_verdict_either_way(
    source: str,
) -> None:
    """An unregistrable `Exn<E>` is E612 whichever path reaches it.

    The handler walk used to call the shared registration helper and throw
    the boolean away, so only the State arm could drop a function — the Exn
    arm registered nothing and compiled the calls anyway.
    """
    result = _compile(source + _MAIN)
    codes = {d.error_code for d in result.diagnostics}
    assert "E612" in codes, (
        "expected the E612 unsupported-Exn-payload diagnostic, got: "
        f"{[(d.error_code, d.description[:80]) for d in result.diagnostics]}"
    )
    # The tag is never declared, so it must never be referenced either.
    assert "$exn_Unit" not in (result.wat or "")


# --- handlers in a MODULE CALL's arguments -----------------------------
# `ModuleCall` sat in both walkers' "intentionally ignored" list with the
# rationale "tracked by the imported module's own scan" — true of the CALLEE
# and false of the ARGUMENTS, which are this module's expressions and are
# lowered into this module's body.  Needs a real resolved module: the shape
# under test is a genuine cross-module call, not a qualified spelling that
# falls back to a local function.
_MODULE_LIB = """\
public fn identn(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.0)
  effects(pure)
{ @Nat.0 }

public fn identi(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }
"""

_MODULECALL_STATE = """\
import lib(identn);
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(lib::identn(handle[State<Nat>](@Nat = 3) {
    get(@Unit) -> { resume(@Nat.0 + 100) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  }))
}
"""

_MODULECALL_EXN = """\
import lib(identi);
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  lib::identi(handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 + 40 }
  } in {
    throw(2);
    999
  })
}
"""


def _lib_module() -> ResolvedModule:
    """A resolved `lib` module with one identity function per family."""
    return ResolvedModule(
        path=("lib",),
        file_path=Path("/fake/lib.vera"),
        program=pipeline.parse(_MODULE_LIB).program,
        source=_MODULE_LIB,
    )


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        pytest.param(_MODULECALL_STATE, 103, id="state"),
        pytest.param(_MODULECALL_EXN, 42, id="exn"),
    ],
)
def test_handler_in_a_module_call_argument_is_registered(
    source: str, expected: int,
) -> None:
    """A module call's ARGUMENTS are this module's code, so they are walked.

    Pre-fix: `unknown func $vera.state_push_Nat` / `unknown tag $exn_Int` at
    whole-module WAT compilation, from a check-green program — the handler was
    lowered here while the walk dismissed the whole `ModuleCall` node as the
    imported module's business.  The values are derived from the language
    rules (the get clause resumes 3 + 100; the Exn handler catches throw(2)
    and returns 2 + 40), so a fix that registers the family but lowers the
    argument wrongly still fails.
    """
    result = codegen_compile(
        parse_to_ast(source), source=source,
        resolved_modules=[_lib_module()],
    )
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, [d.description for d in errors]
    assert execute(result, fn_name="main", args=[]).value == expected


# --- handlers in CONTRACT predicates ----------------------------------
# A contract is lowered code: `requires`/`ensures` become runtime checks and
# `decreases` becomes the termination guard's measure.  A handler written in
# one is emitted like any other, but the registration walk saw `decl.body`
# alone, so the module called `$vera.state_push_Nat` against no import.
_HANDLER_IN_REQUIRES = """
private fn probe(@Int -> @Int)
  requires(handle[State<Nat>](@Nat = 3) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  } > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(5)
}
"""

_HANDLER_IN_ENSURES = """
private fn probe(@Int -> @Int)
  requires(true)
  ensures(handle[State<Nat>](@Nat = 3) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  } > 0)
  effects(pure)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(5)
}
"""

# `assert` sits in the BODY, but the walker's case split declared a contract
# predicate structurally handler-free ("no handle in pred") and refused to
# descend — so this one was missed by the body walk itself.
_HANDLER_IN_ASSERT = """
private fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  assert(handle[State<Nat>](@Nat = 3) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  } > 0);
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(5)
}
"""

# `decreases` carries `exprs`, not `expr` — the attribute-name shortcut the
# IO scan used skipped it entirely, so it needs its own case.
_HANDLER_IN_DECREASES = """
private fn countdown(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0 + handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  })
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    countdown(@Nat.0 - 1)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(countdown(3))
}
"""

_CONTRACT_SHAPES = [
    ("requires", _HANDLER_IN_REQUIRES, 5),
    ("ensures", _HANDLER_IN_ENSURES, 5),
    ("assert", _HANDLER_IN_ASSERT, 5),
    ("decreases", _HANDLER_IN_DECREASES, 0),
]


@pytest.mark.parametrize(
    ("source", "expected"),
    [pytest.param(s, e, id=i) for i, s, e in _CONTRACT_SHAPES],
)
def test_handler_in_a_contract_predicate_is_registered(
    source: str, expected: int,
) -> None:
    """A handler in a contract predicate is lowered, so it must be declared.

    All four were check-green and verify-clean and died at whole-module WAT
    compilation with `unknown func $vera.state_push_Nat`.
    """
    _check_ok(source)
    _verify_ok(source)
    assert _run(source) == expected


# =====================================================================
# Registration-completeness differential
# =====================================================================

_CORPUS_DIRS = ("examples", "tests/conformance")

# `call $vera.state_get_Int`, `call $vera.state_push_Option$LT$Int$GT$`, …
_STATE_REF = re.compile(r"call\s+(\$vera\.state_(?:get|put|push|pop)_[^\s)]+)")
# `(import "vera" "state_push_Int" (func $vera.state_push_Int))` — the
# zero-argument push/pop imports close immediately after the name, so the
# terminator is whitespace OR the closing paren.
_STATE_DECL = re.compile(
    r"\(import\s+\"vera\"\s+\"state_[^\"]+\"\s+\(func\s+"
    r"(\$vera\.state_[^\s)]+)")
# `catch $exn_Int $hc_0` / `throw $exn_Int`
_EXN_REF = re.compile(r"(?:catch|throw)\s+(\$exn_[^\s)]+)")
# `(tag $exn_Int (param i64))`
_EXN_DECL = re.compile(r"\(tag\s+(\$exn_[^\s)]+)")


def _conformance_negatives() -> frozenset[str]:
    """File names of the conformance suite's DELIBERATE negatives.

    A manifest entry carrying `expected_error` is a fixture written to FAIL
    `vera check`, so the toolchain never reaches codegen for it and its
    emitted WAT is not a thing any user can obtain.  Feeding one to a
    registration-invariant sweep measures the compiler on input it is
    contractually not compiling: three of them produce modules that do not
    even load (round-5 review measured `ch06_quantifier_array_domain_rejected`
    and `ch09_builtin_effect_redefinition_rejected` among them), which is
    correct behaviour for a rejected program and noise here.
    """
    root = Path(__file__).parent.parent
    manifest = json.loads(
        (root / "tests" / "conformance" / "manifest.json").read_text(
            encoding="utf-8"))
    return frozenset(
        entry["file"] for entry in manifest if entry.get("expected_error"))


def _corpus_programs() -> list[Path]:
    """Every corpus program the toolchain is expected to compile.

    The conformance suite's negatives are filtered out (see
    `_conformance_negatives`) — they never reach codegen through `vera
    check`, so they are not part of any registration invariant.
    """
    root = Path(__file__).parent.parent
    negatives = _conformance_negatives()
    files: list[Path] = []
    for d in _CORPUS_DIRS:
        files.extend(
            p for p in sorted((root / d).glob("*.vera"))
            if p.name not in negatives
        )
    return files


def test_every_referenced_state_exn_symbol_is_declared() -> None:
    """The cross-component invariant: registration ⊇ lowering, and TYPED.

    Codegen decides which host-cell imports and exception tags a module
    declares in one pass (`_scan_body_for_state_handlers` /
    `_check_state_type`) and which ones it CALLS in another (the handler
    lowering).  A unit test on either pass cannot see them drift apart; only
    running both over real programs and comparing can, which is exactly what
    #1210 was — a family emitted but never declared.

    Two legs, because the name comparison alone is not the invariant.  The
    symbol-set leg catches an UNDECLARED symbol, over every program in the
    sweep.  The validation leg — handing the HANDLER-BEARING modules (the
    ones that reference a `state_*` / `exn_*` symbol at all; the distinct-symbol
    floor below counts SYMBOLS, not modules) to
    `wasmtime.Module`, which type-checks the whole thing — catches a symbol
    declared at the WRONG TYPE, which the name comparison reports as
    perfectly balanced: the #1231 shape declared `state_get_Bool` (i32) for a
    call the checker had typed `Int` (i64), and a Byte-literal-into-an-`Int`-
    cell shape declared the right names with mismatched value types.  Both
    passed a name-only differential while being invalid WASM.  The engine is
    `exceptions_engine()`, not a default one: at wasmtime 48.0.0, 12 of those
    39 modules fail to load when `wasm_exceptions` is off, which is a supported
    wasmtime configuration (see that helper for why the current runner, where the
    proposal defaults on, does not settle the question).

    TWO LIMITS, stated rather than implied.  First, this builds each module
    through `transform` → `codegen_compile` — a CHECKER-LESS shortcut.  The
    real toolchain threads the resolver and the checker's artifacts
    (`expr_semantic_types`, `expr_target_types`, `module_artifacts`), and the
    WAT it produces is not always the same text: a substantial minority of the
    corpus differs between the two builds (de-counted for the same reason as
    the floors below — the proportion moves with every corpus addition and
    nothing here is gated on it).  The invariant under test (registration ⊇ lowering) is a property
    of the codegen pass both share, but a divergence in the shortcut's favour
    is possible in principle and this sweep would not see it.  Second, it is
    anchored, not exploratory: it holds the invariant over the programs the
    suite deliberately PLANTS in `examples/` and `tests/conformance/`, a
    corpus we curate, not an independent search for new violations — the two
    positions round 5 closed (`LetDestruct.value`, `ModuleCall.args`) had no
    corpus instance at all, which is why the shape tests above exist and why
    the walkers are now `vera.fold.walk`, which reaches every field by
    construction (`tests/test_expr_fold.py`).

    The conformance suite's deliberate negatives are FILTERED OUT rather than
    swept-and-ignored (`_corpus_programs`): a program written to fail `vera
    check` never reaches codegen through the toolchain, so its emitted WAT is
    not a thing this invariant is about.
    """
    programs = _corpus_programs()
    assert programs, "corpus is empty — the sweep would pass vacuously"

    engine = exceptions_engine()
    swept = 0
    validated = 0
    symbol_refs = 0
    distinct_symbols: set[str] = set()
    failures: list[str] = []
    invalid: list[str] = []
    for path in programs:
        source = path.read_text(encoding="utf-8")
        # DECLARED failures only.  `parse_file` raises `ParseError` and
        # `transform` raises `TransformError` — both `VeraError` — for the
        # conformance suite's deliberate negatives, and those are not this
        # test's subject.  Anything else (a `TypeError`, an `AttributeError`,
        # a `RecursionError` out of codegen) is a real fault and PROPAGATES:
        # a broad `except Exception` here would silently drop the program
        # from the sweep and shrink the differential's coverage in exactly
        # the situation that most deserves a failure.
        try:
            program = transform(parse_file(str(path)))
        except VeraError:
            continue
        result = codegen_compile(program, source=source, file=str(path))
        wat = result.wat
        if not wat:
            continue
        swept += 1
        declared = set(_STATE_DECL.findall(wat)) | set(_EXN_DECL.findall(wat))
        referenced = set(_STATE_REF.findall(wat)) | set(_EXN_REF.findall(wat))
        symbol_refs += len(referenced)
        distinct_symbols |= referenced
        missing = referenced - declared
        if missing:
            failures.append(f"{path.name}: {sorted(missing)}")
        if not referenced:
            continue
        validated += 1
        try:
            wasmtime.Module(engine, wat)
        except Exception as exc:  # noqa: BLE001 — any validation failure is the finding
            invalid.append(f"{path.name}: {exc}")

    assert not failures, (
        "emitted WAT references State/Exn symbols the module never "
        "declares:\n" + "\n".join(failures)
    )
    assert not invalid, (
        "emitted WAT declares its State/Exn symbols but does not "
        "validate — a declared-at-the-wrong-type import the name "
        "comparison cannot see:\n" + "\n".join(invalid)
    )
    # Floors, so corpus decay or a silent emptying of the regexes cannot
    # turn this into a vacuous pass.  `symbol_refs` SUMS the per-program
    # reference counts (a program using one family in three functions
    # contributes once per distinct symbol, per program); the number of
    # globally distinct symbols across the corpus is much smaller, and both
    # are floored so neither reading can be quietly gamed.
    #
    # The floors sit far below the live measurement and far above zero, so
    # ordinary corpus churn never trips one while an emptied regex or a
    # vanished corpus does.  The live values are deliberately NOT restated
    # here: they move with every corpus addition, and a quadruple of them in a
    # comment is stale the moment it is written — each assertion below prints
    # its own live value in the failure message, which is where a reader who
    # needs the number is already looking.
    assert swept >= 150, f"only {swept} programs compiled — sweep too small"
    assert symbol_refs >= 90, (
        f"only {symbol_refs} state/exn symbol references summed across "
        "programs — the extraction regexes are probably no longer matching "
        "the emitted WAT"
    )
    assert len(distinct_symbols) >= 22, (
        f"only {len(distinct_symbols)} globally distinct state/exn symbols "
        "— the corpus has stopped covering the families"
    )
    assert validated >= 22, (
        f"only {validated} handler-bearing modules validated — the "
        "wrong-type leg is nearly vacuous"
    )


@pytest.mark.parametrize(
    ("source", "ref_re", "decl_re", "strip_prefix"),
    [
        pytest.param(
            _HANDLE_IN_STATE_INIT, _STATE_REF, _STATE_DECL,
            '(import "vera" "state_', id="state",
        ),
        pytest.param(
            _EXN_IN_CLAUSE_BODY, _EXN_REF, _EXN_DECL, "(tag $exn_", id="exn",
        ),
    ],
)
def test_the_differential_can_go_red(
    source: str, ref_re: re.Pattern[str], decl_re: re.Pattern[str],
    strip_prefix: str,
) -> None:
    """Prove the extraction actually distinguishes declared from referenced.

    Without this, a regex that silently stopped matching would leave the
    sweep above green forever.  A handler program's WAT with its declaration
    lines stripped must be reported as missing exactly those symbols — run
    for BOTH halves, because the `state_*` imports and the `exn_*` tags are
    extracted by different regexes and either could rot alone.
    """
    result = _compile(source + _MAIN)
    wat = result.wat
    assert wat, "fixture produced no WAT"
    referenced = set(ref_re.findall(wat))
    assert referenced, "fixture references no symbols of this kind"
    assert referenced <= set(decl_re.findall(wat)), "fixture is unbalanced"
    stripped = "\n".join(
        line for line in wat.splitlines()
        if not line.lstrip().startswith(strip_prefix)
    )
    assert set(ref_re.findall(stripped)) - set(decl_re.findall(stripped)) == referenced


def test_the_validation_leg_can_go_red() -> None:
    """Prove the `wasmtime.Module` leg catches a WRONG-TYPE declaration.

    The symbol-set comparison sees only names, so a module that declares
    every symbol it calls — but declares one of them with the wrong value
    type — is reported as balanced.  Retyping one `state_get_*` import from
    i64 to i32 in an otherwise-good module must fail the new leg while the
    name comparison stays green.

    Uses the same `exceptions_engine()` the leg itself uses, so the red-proof
    and the thing it proves red cannot disagree about what a valid module is.
    """
    result = _compile(_HANDLE_IN_STATE_INIT + _MAIN)
    wat = result.wat
    assert wat, "fixture produced no WAT"
    engine = exceptions_engine()
    wasmtime.Module(engine, wat)  # the unmutated fixture validates

    mutated = wat.replace(
        '(import "vera" "state_get_Int" (func $vera.state_get_Int '
        '(result i64)))',
        '(import "vera" "state_get_Int" (func $vera.state_get_Int '
        '(result i32)))',
    )
    assert mutated != wat, (
        "the planted mutation did not apply — the import spelling changed"
    )
    # The NAME comparison still sees a perfectly balanced module …
    referenced = set(_STATE_REF.findall(mutated))
    declared = set(_STATE_DECL.findall(mutated))
    assert referenced and not (referenced - declared)
    # … while the module is not valid WASM.
    with pytest.raises(wasmtime.WasmtimeError):
        wasmtime.Module(engine, mutated)
