"""Regression tests for #912 — a composite (ADT / Option / Tuple) equality in
``ensures`` position must lower its RUNTIME check to STRUCTURAL equality, so a
postcondition ``vera verify`` proves at Tier 1 does not spuriously TRAP at run.

The bug (SEVERE — a proved postcondition traps on itself):

    private data Box { MkBox(Int) }
    private fn mk(@Int -> @Box)
      requires(true) ensures(@Box.result == MkBox(@Int.0)) effects(pure)
    { MkBox(@Int.0) }

``vera check`` OK; ``vera verify`` OK ("verified (Tier 1)"); ``vera run`` → exit
1 ``Postcondition violation in mk``.  The postcondition is TRUE — the result IS
``MkBox(@Int.0)`` — and Z3 proves it structurally, but codegen lowered the
composite ``==`` in the runtime postcondition check to a raw ``i32.eq`` (a
*pointer* compare).  The freshly-built ``MkBox(@Int.0)`` return value and the
freshly-built ``MkBox(@Int.0)`` contract operand are structurally equal but live
at different heap addresses, so ``i32.eq`` returns false → a spurious trap on a
proved contract.

Root cause: the ``ResultRef`` operand of ``==`` (``@Box.result``) resolved to a
``None`` Vera type via ``_infer_vera_type`` (it was in that walker's
"cannot occur" set), so the ADT-structural-``==`` dispatch in
``vera/wasm/operators.py`` was skipped (its ``lv is not None and lv_base in
adt_type_names`` guard) and the code fell through to the scalar ``i32.eq``
default.  ``_infer_expr_wasm_type`` already handled ``ResultRef`` (#891), so the
*width* was right (i32 vs i32) — only the *Vera-type* dispatch was missing.

Fix: ``_infer_vera_type`` resolves a ``ResultRef`` to its declared ``@Type``
(reusing the ``SlotRef`` logic), so a composite ``@T.result == ctor``
postcondition routes through the SAME structural-``==`` codegen that ``eq(a, b)``
and ``ctor == ctor`` already use — which recurses fields and works at runtime.

Written test-first: every RED test below TRAPS on the pre-fix compiler with a
``Postcondition violation`` and passes after the fix.  The NEGATIVE-CONTROL
tests pin the soundness invariant: a genuinely-FALSE composite postcondition
must STILL be rejected by ``vera verify`` (E500) AND trap at runtime — the fix
must make true composite postconditions pass, never false ones.
"""

from __future__ import annotations

import re
import tempfile

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen import CompileResult, compile as codegen_compile, execute
from vera.codegen.api import WasmTrapError
from vera.parser import parse_file, parse_to_ast
from vera.transform import transform
from vera.verifier import VerifyResult, verify


# ---------------------------------------------------------------------
# Helpers (mirror tests/test_eq_contract_874.py)
# ---------------------------------------------------------------------

def _compile(source: str) -> CompileResult:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    tree = parse_file(path)
    ast = transform(tree)
    return codegen_compile(ast, source=source, file=path)


def _run(source: str, fn: str | None = None) -> int:
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected compile errors: {errors}"
    exec_result = execute(result, fn_name=fn)
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _verify(source: str) -> VerifyResult:
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast, source)
    return verify(
        ast, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


def _error_codes(source: str) -> list[str]:
    """Error-severity diagnostic codes from a compile (no exception raised)."""
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "error"]


# Program bodies -------------------------------------------------------

_BOX = """
private data Box {{ MkBox(Int) }}
private fn mk(@Int -> @Box)
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  MkBox(@Int.0)
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(5) {{ MkBox(@Int) -> @Int.0 }}
}}
"""

_OPTION = """
private fn mk(@Int -> @Option<Int>)
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  Some(@Int.0)
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(5) {{ Some(@Int) -> @Int.0, None -> 0 }}
}}
"""

# NB: no `Tuple` case here.  `Tuple` is intentionally NOT `Eq`-derivable
# (spec §9.8 / std-lib §"Eq": Array/Map/handle/tuple fields are non-derivable,
# rejected with E613), so a `Tuple<...> == Tuple<...>` postcondition is an
# invalid program the checker *should* reject — a distinct, pre-existing gap
# (the E613 Eq-derivability gate is not enforced in contract position; a
# `Tuple` `==` in an `ensures` therefore reaches codegen and raises an uncaught
# `AdtEqNotDerivableError`, on the base compiler too).  That is out of scope for
# #912, which is about *Eq-derivable* composites (user ADTs, Option, nested)
# trapping despite being provable.

_NESTED = """
private data Inner {{ MkInner(Int) }}
private data Outer {{ MkOuter(Inner) }}
private fn mk(@Int -> @Outer)
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  MkOuter(MkInner(@Int.0))
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(5) {{ MkOuter(@Inner) -> match @Inner.0 {{ MkInner(@Int) -> @Int.0 }} }}
}}
"""


# =====================================================================
# RED: a TRUE composite postcondition must run without a spurious trap
# =====================================================================

class TestCompositePostconditionRuns912:
    def test_adt_result_eq_ctor_runs(self) -> None:
        # The canonical #912 repro: `@Box.result == MkBox(@Int.0)`.  TRUE (the
        # result IS MkBox(5)); pre-fix it trapped on `i32.eq` (pointer compare).
        src = _BOX.format(ensures="@Box.result == MkBox(@Int.0)")
        assert _run(src, fn="main") == 5

    def test_adt_ctor_eq_result_runs_reversed_order(self) -> None:
        # Operand order flipped: `MkBox(@Int.0) == @Box.result`.  The left
        # operand is a ConstructorCall (already type-resolvable), so this order
        # worked pre-fix — pin it so the fix keeps BOTH orders green.
        src = _BOX.format(ensures="MkBox(@Int.0) == @Box.result")
        assert _run(src, fn="main") == 5

    def test_adt_result_neq_ctor_runs(self) -> None:
        # `!=` on composites must also lower structurally: `@Box.result !=
        # MkBox(@Int.0 + 1)` is TRUE (MkBox(5) != MkBox(6)); pre-fix `i32.ne`
        # of two distinct pointers was *accidentally* true here, but the fix
        # must keep it true via structural inequality, not pointer luck.
        src = _BOX.format(ensures="@Box.result != MkBox(@Int.0 + 1)")
        assert _run(src, fn="main") == 5

    def test_option_result_eq_ctor_runs(self) -> None:
        # `@Option<Int>.result == Some(@Int.0)` — the built-in Option ADT.
        src = _OPTION.format(ensures="@Option<Int>.result == Some(@Int.0)")
        assert _run(src, fn="main") == 5

    def test_nested_adt_result_eq_ctor_runs(self) -> None:
        # Nested user ADT: `@Outer.result == MkOuter(MkInner(@Int.0))`.  The
        # structural eq must recurse through Outer's field into Inner.
        src = _NESTED.format(ensures="@Outer.result == MkOuter(MkInner(@Int.0))")
        assert _run(src, fn="main") == 5


# =====================================================================
# NEGATIVE CONTROL (soundness): a FALSE composite postcondition must be
# rejected by verify AND trap at runtime — the fix must not let it pass.
# =====================================================================

class TestFalseCompositePostconditionRejected912:
    def test_false_adt_ensures_rejected_by_verify(self) -> None:
        # `@Box.result == MkBox(0)` while the body returns MkBox(@Int.0): FALSE
        # for any input != 0.  Must be a Tier-1 counterexample (E500), never a
        # silent pass — the structural-eq codegen fix must not weaken this.
        src = _BOX.format(ensures="@Box.result == MkBox(0)")
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, (
            "A false composite postcondition must fail Tier-1 verification"
        )
        assert any(d.error_code == "E500" for d in errors), (
            f"Expected E500 postcondition counterexample, got {errors}"
        )

    def test_false_adt_ensures_traps_at_runtime(self) -> None:
        # The runtime check must still ENFORCE a false composite postcondition:
        # structural `MkBox(5) == MkBox(0)` is false → trap.  (A structural-eq
        # regression that returned true for unequal ADTs would make this pass —
        # this is the soundness half of the differential.)
        src = _BOX.format(ensures="@Box.result == MkBox(0)")
        result = _compile(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, f"Unexpected compile errors: {errors}"
        with pytest.raises(WasmTrapError, match="Postcondition violation") as exc:
            execute(result, fn_name="main")
        assert exc.value.kind == "contract_violation"

    def test_false_option_ensures_rejected_by_verify(self) -> None:
        # Sibling built-in: `@Option<Int>.result == Some(0)` is false for input
        # != 0.  Must be an E500 counterexample.
        src = _OPTION.format(ensures="@Option<Int>.result == Some(0)")
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(d.error_code == "E500" for d in errors), (
            f"Expected E500 for false Option postcondition, got {errors}"
        )

    def test_false_nested_ensures_traps_at_runtime(self) -> None:
        # Nested: `@Outer.result == MkOuter(MkInner(0))` false for input != 0.
        # Structural eq must recurse and return false → trap.
        src = _NESTED.format(ensures="@Outer.result == MkOuter(MkInner(0))")
        result = _compile(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, f"Unexpected compile errors: {errors}"
        with pytest.raises(WasmTrapError, match="Postcondition violation"):
            execute(result, fn_name="main")


# =====================================================================
# Verify: the TRUE composite postcondition proves at Tier 1 (no false
# Tier-1, no spurious deferral for the user-ADT case).
# =====================================================================

class TestCompositePostconditionVerifies912:
    def test_true_adt_ensures_verified_tier1(self) -> None:
        # `@Box.result == MkBox(@Int.0)` must prove at Tier 1 (it did pre-fix —
        # the bug was purely in the runtime lowering, not the verifier).  Pin it
        # so the codegen fix does not accidentally perturb the proof path.
        src = _BOX.format(ensures="@Box.result == MkBox(@Int.0)")
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Unexpected verify errors: {errors}"
        assert result.summary.tier1_verified >= 1


# =====================================================================
# Generic over a PARAMETERIZED ADT: `fn(@Box<T> -> @Box<T>)` with a
# slot-vs-slot postcondition `@Box<T>.result == @Box<T>.0`.
#
# The #912 fix's `ResultRef` arm resolves `@Box<T>.result` to `lv = "Box<T>"`.
# Round-1 both lost-arg guards bypassed a name containing `<` (`"<" in lv`), so
# dispatch routed `"Box<T>"` (the BASE generic clone) to `_translate_adt_eq`,
# whose derivability gate raised an UNCAUGHT `AdtEqNotDerivableError` — a codegen
# crash on a `check`-green/`verify`-green program that ran fine on base (a
# PR-introduced regression).  The `Box<T>` operand carries an UNRESOLVED type
# variable `T` (the monomorphizer does not specialize the base clone), which is
# non-dispatchable for structural Eq, so the base clone's composite `==` falls
# back to the pre-#912 scalar lowering instead of crashing.
#
# SOUNDNESS — the corrected rationale (round 3).  The `ensures` obligation IS
# proved at TIER 1 (the verifier substitutes `T:=Int` and proves the composite
# `==` structurally); the earlier "defers to Tier 3" claim was WRONG — the only
# Tier-3 obligation is an incidental `nat_to_int_coerce` in `main`, unrelated to
# the `==`.  The scalar fallback is nonetheless sound because it only ever
# affects UNREACHABLE DEAD CODE: the base generic clone `$id2` (the `Box<T>`
# one, lowered `i32.eq`) is emitted but is never a call target and never
# exported — a bare generic fn cannot escape higher-order (that is a parse
# error, E005), so it can never reach a `call_indirect`/table.  Every reachable
# call dispatches to a MONOMORPHIZED clone `$id2$Int` whose `@Box<Int>.result ==
# @Box<Int>.0` is lowered STRUCTURALLY (`call $rt.eq_Box_LInt_R`, since `Box<Int>`
# is concrete and NOT matched by the free-var guard), correctly discharging the
# Tier-1 proof.  The `rebox`-style test below is the direct witness: a result
# that is a FRESHLY-constructed, structurally-equal, DIFFERENT-pointer box is
# Tier-1-verified AND runs correctly (via the structural mono clone) — the exact
# case that WOULD trap if a reachable call were scalar (pointer) lowered.
# =====================================================================

_GENERIC_PARAM_ADT = """
private data Box<T> {{ MkBox(T) }}
private forall<T> fn id2(@Box<T> -> @Box<T>)
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  @Box<T>.0
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match id2(MkBox(7)) {{ MkBox(@Int) -> @Int.0 }}
}}
"""

# `rebox` returns a FRESHLY-CONSTRUCTED box (a NEW `MkBox` allocation at a
# DIFFERENT heap address) that is structurally equal to its argument.  This is
# the case that distinguishes structural from pointer equality: a reachable
# scalar (`i32.eq`) postcondition check would compare two distinct pointers and
# trap; the structural mono clone compares by value and passes.
_REBOX = """
private data Box<T> {{ MkBox(T) }}
private forall<T> fn rebox(@Box<T> -> @Box<T>)
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  match @Box<T>.0 {{ MkBox(@T) -> MkBox(@T.0) }}
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match rebox(MkBox(7)) {{ MkBox(@Int) -> @Int.0 }}
}}
"""


def _mono_clone_postcond_wat(source: str, clone: str) -> str:
    """The WAT body of a named monomorphized clone (`$id2$Int`, `$rebox$Int`).

    Slices from the clone's `(func $<clone>` header to the next `(func ` so a
    test can assert HOW its postcondition `==` was lowered (structural
    `call $rt.eq_...` vs scalar `i32.eq`).
    """
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected compile errors: {errors}"
    # Boundary-safe: the clone name is followed by whitespace or `(` in the
    # WAT header, so anchor on that to avoid matching a longer symbol sharing
    # the prefix (`$rebox$Int` must not match `$rebox$IntArray`).
    m = re.search(r"\(func \$" + re.escape(clone) + r"[\s(]", result.wat)
    assert m is not None, f"clone {clone!r} not found in WAT:\n{result.wat}"
    start = m.start()
    end = result.wat.find("(func ", m.end())
    return result.wat[start:end if end != -1 else len(result.wat)]


class TestGenericParamAdtPostcondition912:
    def test_generic_param_adt_slot_eq_slot_runs(self) -> None:
        # RED (round 2): `@Box<T>.result == @Box<T>.0` crashed codegen with an
        # uncaught AdtEqNotDerivableError('Box<T>') — the base generic clone
        # reached the derivability gate.  The free-var scalar fallback lets that
        # dead base clone compile (harmless dead `i32.eq`) instead of erroring;
        # main dispatches to the structural mono clone and returns 7.
        src = _GENERIC_PARAM_ADT.format(ensures="@Box<T>.result == @Box<T>.0")
        assert _run(src, fn="main") == 7

    def test_generic_param_adt_slot_neq_slot_runs(self) -> None:
        # RED (round 2): the `!=` form shares the crash.  `main` still returns 7;
        # what we pin is that it COMPILES and RUNS rather than crashing codegen.
        src = _GENERIC_PARAM_ADT.format(ensures="@Box<T>.result != @Box<T>.0 || true")
        assert _run(src, fn="main") == 7

    def test_rebox_fresh_pointer_result_is_tier1_verified_and_runs(self) -> None:
        # THE soundness pin (round 3, replaces the vacuous Tier-3 assertion).
        # `rebox` returns a FRESHLY-constructed, structurally-equal, DIFFERENT-
        # pointer box.  Its `ensures(@Box<T>.result == @Box<T>.0)` is proved at
        # TIER 1 (the verifier substitutes T:=Int), and it must RUN without
        # trapping — which it can only do if the reachable mono clone lowers the
        # `==` STRUCTURALLY.  A reachable scalar (pointer) lowering would compare
        # the two distinct allocations and trap: this is the case #912 was
        # about, now for a generic-parameterized ADT.
        src = _REBOX.format(ensures="@Box<T>.result == @Box<T>.0")
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Unexpected verify errors: {errors}"
        # The composite `==` is proved at Tier 1 (NOT deferred to Tier 3).
        ensures_obls = [
            o for o in result.obligations
            if getattr(o, "kind", None) == "ensures"
            and getattr(o, "fn_name", getattr(o, "function", None)) == "rebox"
        ]
        assert ensures_obls, "expected a `rebox` ensures obligation"
        assert all(getattr(o, "status", None) == "verified" for o in ensures_obls), (
            "the rebox composite `==` postcondition must be proved at Tier 1"
        )
        # And it runs correctly — structural eq on different pointers, no trap.
        assert _run(src, fn="main") == 7

    def test_reachable_mono_clone_postcondition_is_structural(self) -> None:
        # Pins the ACTUAL soundness invariant: the REACHABLE monomorphized clone
        # (`$rebox$Int`, the one `main` calls) lowers its postcondition `==`
        # STRUCTURALLY (`call $rt.eq_...`), never a scalar `i32.eq` pointer compare.
        # This is what makes the free-var scalar fallback on the dead BASE clone
        # harmless.  (The check keys on the postcondition dispatch: the mono
        # clone must contain a structural `call $rt.eq_` helper call.)
        src = _REBOX.format(ensures="@Box<T>.result == @Box<T>.0")
        clone_wat = _mono_clone_postcond_wat(src, "rebox$Int")
        assert "call $rt.eq_" in clone_wat, (
            "the reachable mono clone's postcondition `==` must be lowered "
            f"structurally (call $rt.eq_...), got:\n{clone_wat}"
        )


# =====================================================================
# Genuinely non-Eq composite in a postcondition → clean E613, not a
# codegen crash.  These operands carry a CONCRETE non-Eq argument (an
# `Array` field, or `Tuple`), so — unlike the free-type-var `Box<T>` case
# — they are correctly NOT routed to the scalar fallback and reach the
# structural-Eq dispatch, which raises `AdtEqNotDerivableError`.  The #912
# postcondition backstop (`vera/codegen/functions.py`) catches it and emits
# the same clean E613 the body / closure paths already emit, instead of the
# uncaught Python traceback the postcondition path produced before.
# =====================================================================

_BOX_GENERIC = """
private data Box<T> {{ MkBox(T) }}
private fn mk(@Array<Int> -> @Box<Array<Int>>)
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  MkBox(@Array<Int>.0)
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk([1, 2]) {{ MkBox(@Array<Int>) -> 0 }}
}}
"""

_TUPLE_POSTCOND = """
private fn mk(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  Tuple(@Int.0, @Int.0)
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(5) {{ Tuple(@Int, @Int) -> @Int.1 }}
}}
"""


class TestNonEqCompositePostconditionCleanE613912:
    def test_array_field_adt_postcond_is_clean_e613(self) -> None:
        # `@Box<Array<Int>>.result == MkBox(...)`: the argument is a CONCRETE
        # non-Eq type (`Array`), so the operand is NOT a free-type-var clone —
        # it correctly reaches the structural-Eq dispatch, which is non-
        # derivable.  Before the #912 postcondition backstop this escaped as an
        # uncaught `AdtEqNotDerivableError` traceback; now it is a clean E613
        # (the same the body path emits), never an unhandled exception.
        src = _BOX_GENERIC.format(
            ensures="@Box<Array<Int>>.result == MkBox(@Array<Int>.0)")
        codes = _error_codes(src)
        assert "E613" in codes, f"expected E613, got {codes}"

    def test_tuple_postcond_is_clean_e613(self) -> None:
        # `Tuple` is intentionally non-Eq (spec §9.8), so a `Tuple<...>` `==` in
        # a postcondition is non-derivable.  The backstop turns the previously
        # uncaught crash into a clean E613 — pinned so the postcondition path
        # keeps parity with the body path's handling.
        src = _TUPLE_POSTCOND.format(
            ensures="@Tuple<Int, Int>.result == Tuple(@Int.0, @Int.0)")
        codes = _error_codes(src)
        assert "E613" in codes, f"expected E613, got {codes}"
