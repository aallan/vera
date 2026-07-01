"""Tests for vera.verifier — mutation_gates_smt (#387 mutation-hardening: verifier gates and SMT translation).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations

from vera.verifier import VerifyResult

from tests.verifier_helpers import (
    _verify,
)


class TestVerifierGates387:
    """#387: pin the verifier's *soundness-gate* predicates and the
    generic-instantiation aggregation/meet logic — the code that decides
    WHETHER an obligation fires, and how per-instantiation verdicts collapse.

    These are the highest-value mutation targets: a wrong boolean from a typing
    predicate silently skips (or spuriously fires) a `value >= 0` / refinement
    obligation, and a wrong meet folds a reachable counterexample into a false
    Tier-1.  Each test is a DIFFERENTIAL — the predicate's wrong answer changes
    the obligation SET (a `nat_sub`/`nat_bind`/`refine_bind` appears or
    vanishes), its KIND/CODE, or its STATUS.

    Observable surface (per the #387 convention): `ProofObligation` fields via
    `==` (mutmut wraps string literals as ``"XX"+s+"XX"`` so substring ``in``
    does NOT kill a string mutation — kinds/codes/statuses/fn_name use ``==``)
    and exact tuples on `result.summary`.  Distinct ``_387`` fn names catch a
    ``fn_name → None`` mutation; inputs are chosen so the right answer can't
    coincide with a fallback default.
    """

    @staticmethod
    def _subs(result: VerifyResult) -> list:
        return [o for o in result.obligations if o.kind == "nat_sub"]

    @staticmethod
    def _binds(result: VerifyResult) -> list:
        return [o for o in result.obligations if o.kind == "nat_bind"]

    @staticmethod
    def _refbinds(result: VerifyResult) -> list:
        return [o for o in result.obligations if o.kind == "refine_bind"]

    # =================================================================
    # _is_nat_typed / _has_nat_origin  (4402-4543)
    # Gate the #520 `@Nat - @Nat` underflow obligation (kind nat_sub,
    # E502) at _walk_for_primitive_op_obligations:2097-2101.  The
    # obligation fires iff op==SUB AND both operands _is_nat_typed AND
    # (either _has_nat_origin).  A wrong boolean flips the obligation's
    # EXISTENCE — the cleanest differential.
    # =================================================================

    def test_nat_slot_subtraction_is_obligated(self) -> None:
        """``@Nat.0 - @Nat.1`` (both SlotRefs, @Nat-typed + @Nat-origin) →
        exactly one ``nat_sub`` E502 (unguarded → violated, with CE).  Pins the
        baseline gate: ``_is_nat_typed(SlotRef)`` / ``_has_nat_origin(SlotRef)``
        both keyed on ``type_name == "Nat"`` (line 4431/4494).  A mutation
        flipping either SlotRef branch drops the obligation (false Tier-1)."""
        result = _verify("""
private fn slotsub_neg_387(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        o = subs[0]
        assert o.kind == "nat_sub", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E502", o.error_code
        assert o.fn_name == "slotsub_neg_387", o.fn_name
        assert o.counterexample, o.counterexample

    def test_int_slot_subtraction_not_obligated(self) -> None:
        """``@Int.0 - @Int.1 → @Int`` carries NO ``nat_sub`` — the negative
        partner of the gate.  ``_is_nat_typed(@Int.0)`` must be False (its
        ``type_name`` is ``Int`` not ``Nat``), so the ``and`` at 2098-2099
        short-circuits.  A mutation making ``_is_nat_typed`` return True for an
        @Int SlotRef would spuriously fire E502 on well-defined signed
        arithmetic."""
        result = _verify("""
private fn intsub_387(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 - @Int.1 }
""")
        assert self._subs(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_pure_literal_subtraction_origin_gate_skips(self) -> None:
        """``0 - 1`` consumed at @Int: both operands are @Nat-TYPED (non-negative
        IntLits, ``_is_nat_typed`` line 4434 ``value >= 0``) but NEITHER has
        @Nat *origin* (``_has_nat_origin`` returns False for IntLit — it has no
        IntLit branch), so the ``(_has_nat_origin OR _has_nat_origin)`` conjunct
        at 2100-2101 is False and NO obligation fires.  This is the #520
        deliberate pure-literal exemption: a mutation deleting the origin
        conjunct would spuriously E502 every ``0 - 1`` sentinel in the
        corpus."""
        result = _verify("""
private fn litsub_387(@Unit -> @Int)
  requires(true) ensures(@Int.result < 0) effects(pure)
{ 0 - 1 }
""")
        assert self._subs(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_literal_minus_natslot_origin_or_branch(self) -> None:
        """``0 - @Nat.0``: left IntLit has no @Nat origin, right SlotRef does.
        The gate fires only because ``_has_nat_origin`` uses ``left OR right``
        (line 4528-4529).  A mutation ``or → and`` makes ``(False and True) =
        False`` and the obligation vanishes — so this pins the OR specifically,
        not just "some operand has origin".  Unguarded → violated E502 with a
        CE (``@Nat.0 = 1`` gives ``-1``)."""
        result = _verify("""
private fn litnat_387(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 0 - @Nat.0 }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        o = subs[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E502", o.error_code
        assert o.fn_name == "litnat_387", o.fn_name
        assert o.counterexample, o.counterexample

    def test_natslot_minus_literal_origin_or_left(self) -> None:
        """``@Nat.0 - 1``: left SlotRef has @Nat origin, right IntLit does not.
        The mirror of the previous test — pins the LEFT disjunct of the OR.
        Guarded by ``@Nat.0 >= 1`` so it verifies, isolating the gate's
        existence (one ``nat_sub``, verified) from the discharge."""
        result = _verify("""
private fn natlit_387(@Nat -> @Nat)
  requires(@Nat.0 >= 1) ensures(true) effects(pure)
{ @Nat.0 - 1 }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        o = subs[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "natlit_387", o.fn_name
        assert o.counterexample is None, o.counterexample

    def test_is_nat_typed_recurses_arithmetic_operand(self) -> None:
        """``(@Nat.0 + @Nat.1) - @Nat.0``: the LEFT operand of the SUB is itself
        a BinaryExpr.  The gate fires only if ``_is_nat_typed`` RECURSES into
        the ADD (line 4443-4444, ``left AND right``) and reports @Nat.  Drop the
        BinaryExpr recursion (return False) and the SUB's left operand reads as
        non-@Nat, killing the obligation.  Guarded (sum >= @Nat.0 always) →
        verified."""
        result = _verify("""
private fn natarith_387(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ (@Nat.0 + @Nat.1) - @Nat.0 }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        assert subs[0].status == "verified", subs[0].status
        assert subs[0].fn_name == "natarith_387", subs[0].fn_name

    def test_is_nat_typed_int_addend_blocks_obligation(self) -> None:
        """``(@Nat.0 + @Int.0) - @Nat.1 → @Int``: the ADD has an @Int operand so
        is @Int-typed, the SUB result is @Int, and NO ``nat_sub`` fires.  Pins
        the ``and`` in ``_is_nat_typed``'s BinaryExpr branch (4443-4444): a
        mutation ``and → or`` would call the mixed ADD @Nat-typed, then
        spuriously obligate the @Int subtraction."""
        result = _verify("""
private fn mixedarith_387(@Nat, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ (@Nat.0 + @Int.0) - @Nat.1 }
""")
        assert self._subs(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_is_nat_typed_recurses_block_tail(self) -> None:
        """``{ @Nat.0 - @Nat.1 }`` as the function body: the SUB sits inside a
        Block.  Pins ``_is_nat_typed``'s Block branch (4451-4452, recurse on
        ``expr.expr``) AND the walker's Block recursion — the obligation fires
        only if both descend.  Unguarded → violated E502."""
        result = _verify("""
private fn blocksub_387(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ { @Nat.0 - @Nat.1 } }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        assert subs[0].status == "violated", subs[0].status
        assert subs[0].error_code == "E502", subs[0].error_code

    def test_has_nat_origin_recurses_index_element(self) -> None:
        """``arr[0] - arr[1]`` on ``@Array<Nat>`` (length >= 2): array indexing
        carries @Nat provenance only because ``_has_nat_origin``'s IndexExpr
        branch (4518-4526) consults the resolved ELEMENT type — it cannot
        recurse on the ``@Array`` operand, which is not itself @Nat.  Drop that
        branch and the underflow is silently skipped (CR #756).  Both indices
        in-bounds → the obligation is the genuine value comparison (violated:
        ``arr[0] < arr[1]`` is possible)."""
        result = _verify("""
public fn arrsub_387(@Array<Nat> -> @Nat)
  requires(array_length(@Array<Nat>.0) >= 2)
  ensures(true) effects(pure)
{ @Array<Nat>.0[0] - @Array<Nat>.0[1] }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        assert subs[0].status == "violated", subs[0].status
        assert subs[0].error_code == "E502", subs[0].error_code
        assert subs[0].fn_name == "arrsub_387", subs[0].fn_name

    # =================================================================
    # _narrows_into_nat / _has_underflow_leaf  (4545-4598)
    # Gate the #552 binding-site `value >= 0` obligation (kind
    # nat_bind, E503).  _narrows_into_nat = (NOT _is_nat_typed(v))
    # OR _has_underflow_leaf(v).  Differential: nat_bind appears or
    # vanishes.
    # =================================================================

    def test_int_narrow_into_nat_let_is_obligated(self) -> None:
        """``let @Nat = @Int.0``: value is NOT @Nat-typed, so
        ``_narrows_into_nat`` returns True via its FIRST clause
        (``not _is_nat_typed``, 4564-4565) → one ``nat_bind`` E503 (unguarded →
        violated, CE).  A mutation negating that clause drops the narrowing
        check entirely (false Tier-1 on every @Int→@Nat bind)."""
        result = _verify("""
private fn letnarrow_387(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = @Int.0; @Nat.0 }
""")
        binds = self._binds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.kind == "nat_bind", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E503", o.error_code
        assert o.fn_name == "letnarrow_387", o.fn_name
        assert o.counterexample, o.counterexample

    def test_nat_narrow_into_nat_let_not_obligated(self) -> None:
        """``let @Nat = @Nat.0``: value IS @Nat-typed AND has no underflow leaf,
        so ``_narrows_into_nat`` returns False — NO ``nat_bind``.  The negative
        partner: a mutation forcing ``_narrows_into_nat`` True (e.g. dropping
        the ``_is_nat_typed`` guard) would spuriously E503 a Nat→Nat bind."""
        result = _verify("""
private fn natbind_387(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = @Nat.0; @Nat.0 }
""")
        assert self._binds(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_underflow_leaf_pure_literal_sub_into_nat(self) -> None:
        """``let @Nat = 0 - 1``: the value is @Nat-TYPED (both literals
        non-negative) yet can be negative.  Only ``_has_underflow_leaf`` (the
        SECOND clause of ``_narrows_into_nat``, 4566) catches it: it sees a SUB
        with no @Nat origin (4583-4585) and returns True → one ``nat_bind`` E503
        violated.  Drop ``_has_underflow_leaf`` and this @Nat-typed-but-negative
        bind escapes (the exact #520→#552 hand-off, false Tier-1)."""
        result = _verify("""
private fn ufl_let_387(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = 0 - 1; @Nat.0 }
""")
        binds = self._binds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E503", o.error_code
        assert o.fn_name == "ufl_let_387", o.fn_name
        assert o.counterexample, o.counterexample
        # No `nat_sub` co-fires: the SUB has no @Nat origin (#520 exempt),
        # so #552 owns this site exclusively.
        assert self._subs(result) == [], [
            (o.kind, o.status) for o in result.obligations]

    def test_no_underflow_leaf_nonneg_addition_into_nat(self) -> None:
        """``let @Nat = 1 + 2``: @Nat-typed with NO subtraction anywhere, so
        ``_has_underflow_leaf`` returns False and ``_narrows_into_nat`` is False
        — NO obligation.  Pins the SUB-specific guard in ``_has_underflow_leaf``
        (4583): a mutation that returns True for a non-SUB BinaryExpr would
        spuriously E503 a constant addition."""
        result = _verify("""
private fn noleaf_387(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = 1 + 2; @Nat.0 }
""")
        assert self._binds(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_underflow_leaf_recurses_block(self) -> None:
        """``let @Nat = { 0 - 1 }``: the underflowing SUB is wrapped in a Block.
        Pins ``_has_underflow_leaf``'s Block branch (4588-4589, recurse on
        ``value.expr``) — drop it and the wrapped pure-literal underflow is no
        longer caught.  One ``nat_bind`` E503 violated."""
        result = _verify("""
private fn ufl_block_387(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = { 0 - 1 }; @Nat.0 }
""")
        binds = self._binds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        assert binds[0].status == "violated", binds[0].status
        assert binds[0].error_code == "E503", binds[0].error_code

    def test_underflow_leaf_recurses_if_branch(self) -> None:
        """``let @Nat = if c then { 5 } else { 0 - 1 }``: the underflow lives in
        the ELSE branch.  Pins ``_has_underflow_leaf``'s IfExpr branch
        (4590-4594, ``then OR else``) — the value is @Nat-typed (both branches
        @Nat) but the else can be negative.  One ``nat_bind`` E503 violated;
        drop the IfExpr recursion (or its else disjunct) and it escapes."""
        result = _verify("""
private fn ufl_if_387(@Bool -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = if @Bool.0 then { 5 } else { 0 - 1 }; @Nat.0 }
""")
        binds = self._binds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        assert binds[0].status == "violated", binds[0].status
        assert binds[0].error_code == "E503", binds[0].error_code
        assert binds[0].fn_name == "ufl_if_387", binds[0].fn_name

    # =================================================================
    # _narrows_into_refined  (4600-4637)
    # Gate the #746 refinement binding obligation (kind refine_bind,
    # E505).  Fires unless the source already carries the target's
    # EXACT (base AND predicate) refinement (the R3 exemption).
    # =================================================================

    def test_int_narrow_into_refined_is_obligated(self) -> None:
        """``let @Pos387 = @Int.0`` (``@Pos387 = {@Int | @Int.0 > 0}``): the
        source is bare @Int with no refinement, so ``_narrows_into_refined``
        returns True (no source_parts match) → one ``refine_bind`` E505
        (violated: @Int.0 may be <= 0, CE).  The baseline refinement gate."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn refnarrow_387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Pos387 = @Int.0; @Pos387.0 }
""")
        binds = self._refbinds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.kind == "refine_bind", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E505", o.error_code
        assert o.fn_name == "refnarrow_387", o.fn_name
        assert o.counterexample, o.counterexample

    def test_same_refinement_bind_is_r3_exempt(self) -> None:
        """``let @Pos387 = @Pos387.0``: source and target share base AND
        predicate, so the R3 exemption (4633-4636) returns False — NO
        ``refine_bind``.  The negative partner: a mutation deleting the R3
        early-return (always obligate) would E505 an already-discharged
        refinement, a false positive on sound code."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn refexempt_387(@Pos387 -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Pos387 = @Pos387.0; @Pos387.0 }
""")
        assert self._refbinds(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_different_predicate_not_r3_exempt(self) -> None:
        """``let @Pos387 = @Gt5_387.0`` (source ``> 5``, target ``> 0``): the
        bases match (both @Int) but the PREDICATES differ, so the R3 exemption
        does NOT apply — the obligation fires and is DISCHARGED (``> 5`` implies
        ``> 0``) → one ``refine_bind`` VERIFIED.  Pins the predicate half of the
        R3 ``and`` (4634): a mutation matching on base alone would wrongly exempt
        this and the obligation would vanish (status flips to absent)."""
        result = _verify("""
type Gt5_387 = { @Int | @Int.0 > 5 };
type Pos387 = { @Int | @Int.0 > 0 };
private fn refdiff_387(@Gt5_387 -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Pos387 = @Gt5_387.0; @Pos387.0 }
""")
        binds = self._refbinds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "refdiff_387", o.fn_name

    # =================================================================
    # _check_generic_refined_return  (3387-3493)
    # Discharge a CONCRETE refined return on an UNINSTANTIATED generic
    # (forall<T>).  Reached via the uninstantiated-generic branch of
    # _verify_fn (1234-1238).  kind refine_bind, E505.
    # =================================================================

    def test_generic_refined_return_violated(self) -> None:
        """Uninstantiated ``forall<T> fn g(@T -> @Pos387) { 0 }``: the concrete
        refined return is T-independent, discharged at Tier 1, and ``0`` violates
        ``> 0`` → one ``refine_bind`` E505 violated (CE).  Pins the violated
        branch (3480-3489): kind/code/CE and the ``total -= 1`` (the error is not
        a counted verdict, so total = requires + ensures = 2)."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private forall<T>
fn gret_bad_387(@T -> @Pos387)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")
        binds = self._refbinds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.kind == "refine_bind", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E505", o.error_code
        assert o.fn_name == "gret_bad_387", o.fn_name
        assert o.counterexample, o.counterexample
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (2, 0, 2), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_generic_refined_return_verified(self) -> None:
        """Uninstantiated ``forall<T> fn g(@T -> @Pos387) { 5 }``: ``5`` proves
        ``> 0`` → one ``refine_bind`` VERIFIED.  Pins the verified branch
        (3476-3479): status ``verified``, empty code, no CE, and the
        ``tier1_verified += 1`` + ``total += 1`` (total = requires + refine_bind
        + ensures = 3).  Together with the violated test this brackets the
        check_valid verdict routing."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private forall<T>
fn gret_ok_387(@T -> @Pos387)
  requires(true) ensures(true) effects(pure)
{ 5 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = self._refbinds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "gret_ok_387", o.fn_name
        assert o.counterexample is None, o.counterexample
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    # =================================================================
    # _aggregate_generic_instances / _emit_aggregated_diagnostic
    # (1002-1162)  — collapse per-instantiation obligations at one
    # source site to a single met obligation (#732).  Reached by a
    # forall<T> instantiated at >=2 concrete types.
    # =================================================================

    def test_generic_instances_aggregate_violated_to_one(self) -> None:
        """``forall<T> fn g(@T,@Nat,@Nat -> @Nat) { @Nat.0 - @Nat.1 }``
        instantiated at Int AND Bool: the unguarded SUB violates in BOTH
        instantiations, but ``_aggregate_generic_instances`` collapses the two
        per-instance obligations at the one source site to a SINGLE met
        obligation.  Pins the de-dup (exactly one ``nat_sub``, not two) and the
        ``violated`` meet; ``_emit_aggregated_diagnostic`` produces ONE E502."""
        result = _verify("""
private forall<T>
fn gsub_bad_387(@T, @Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 - @Nat.1 }

public fn use_int_bad_387(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ gsub_bad_387(@Int.0, 3, 1) }

public fn use_bool_bad_387(@Bool -> @Nat)
  requires(true) ensures(true) effects(pure)
{ gsub_bad_387(@Bool.0, 5, 2) }
""")
        subs = [o for o in result.obligations
                if o.kind == "nat_sub" and o.fn_name == "gsub_bad_387"]
        assert len(subs) == 1, [(o.kind, o.fn_name, o.status)
                                for o in result.obligations]
        assert subs[0].status == "violated", subs[0].status
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        # The aggregated diagnostic names the generic and BOTH instantiations
        # (sorted): pins _emit_aggregated_diagnostic's prefix + label set.
        d = errs[0]
        assert d.description.startswith(
            "In generic function 'gsub_bad_387' instantiated at "
            "gsub_bad_387<Bool>, gsub_bad_387<Int>: "), d.description

    def test_generic_instances_aggregate_verified_counts_once(self) -> None:
        """Same generic but GUARDED (``requires(@Nat.0 >= @Nat.1)``): the SUB
        verifies in both instantiations and the meet is ``verified`` → exactly
        one ``nat_sub`` verified, NO diagnostic.  Pins the verified branch of
        ``_aggregate_generic_instances`` (1065-1067: ``tier1_verified += 1`` and
        ``total += 1`` ONCE, not per-instance).  The negative partner to the
        violated aggregation — together they pin the meet's two extreme
        verdicts feeding the summary.

        De Bruijn: in ``gsub_ok_387(@Int.0, 1, 3)`` the args fill the two
        ``@Nat`` params left-to-right, so the EARLIER param is ``1`` and the
        LATER (rightmost) is ``3``; ``@Nat.0`` is the rightmost (``3``) and
        ``@Nat.1`` the earlier (``1``), so ``requires(@Nat.0 >= @Nat.1)`` is
        ``3 >= 1`` — genuinely satisfied at BOTH call sites."""
        result = _verify("""
private forall<T>
fn gsub_ok_387(@T, @Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1) ensures(true) effects(pure)
{ @Nat.0 - @Nat.1 }

public fn use_int_ok_387(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ gsub_ok_387(@Int.0, 1, 3) }

public fn use_bool_ok_387(@Bool -> @Nat)
  requires(true) ensures(true) effects(pure)
{ gsub_ok_387(@Bool.0, 2, 5) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        subs = [o for o in result.obligations
                if o.kind == "nat_sub" and o.fn_name == "gsub_ok_387"]
        assert len(subs) == 1, [(o.kind, o.fn_name, o.status)
                                for o in result.obligations]
        assert subs[0].status == "verified", subs[0].status

    # =================================================================
    # _meet_status  (1164-1175) — worst-case status across
    # instantiations, with timeout folded into tier3.  Pure static
    # method: tested directly so each ordered branch has a surgical
    # differential (integration can't easily mix tier3_unguarded with
    # tier3 across instantiations).
    # =================================================================

    def test_meet_status_violated_dominates(self) -> None:
        """``violated`` is the worst case — it must win over every other status.
        Pins the FIRST branch (1169-1170).  A mutation deleting it would let a
        reachable counterexample be downgraded to tier3/verified — the exact
        false-Tier-1 the meet exists to prevent."""
        from vera.verifier import ContractVerifier
        m = ContractVerifier._meet_status
        assert m(["verified", "violated", "tier3"]) == "violated"
        assert m(["tier3_unguarded", "violated"]) == "violated"
        assert m(["violated"]) == "violated"

    def test_meet_status_tier3_unguarded_over_tier3(self) -> None:
        """``tier3_unguarded`` outranks ``tier3``/``verified`` (1171-1172).
        Pins the ORDER: a mutation swapping this below the tier3 check would
        report ``tier3`` for a mix that includes an UNGUARDED runtime obligation,
        losing the "no codegen guard" distinction (a refined narrowing has no
        runtime guard, so mislabeling it tier3 implies a guard that isn't
        there)."""
        from vera.verifier import ContractVerifier
        m = ContractVerifier._meet_status
        assert m(["verified", "tier3_unguarded", "tier3"]) == "tier3_unguarded"
        assert m(["tier3", "tier3_unguarded"]) == "tier3_unguarded"

    def test_meet_status_tier3_from_tier3_or_timeout(self) -> None:
        """The tier3 branch (1173-1174) folds BOTH ``tier3`` and ``timeout``
        into ``tier3`` (the mirror-friendly vocabulary).  Two assertions pin the
        two disjuncts independently: a mutation deleting the ``timeout`` disjunct
        would mis-report a timed-out instantiation as ``verified``."""
        from vera.verifier import ContractVerifier
        m = ContractVerifier._meet_status
        assert m(["verified", "tier3"]) == "tier3"
        assert m(["verified", "timeout"]) == "tier3"

    def test_meet_status_all_verified(self) -> None:
        """All instantiations ``verified`` → ``verified`` (the 1175 fallthrough).
        The negative partner: a mutation hard-coding an earlier branch's return
        would mislabel a fully-proven generic as tier3/violated."""
        from vera.verifier import ContractVerifier
        m = ContractVerifier._meet_status
        assert m(["verified", "verified", "verified"]) == "verified"
        assert m(["verified"]) == "verified"


class TestSmtTranslation387:
    """#387: pin the Z3-translation layer (``vera/smt.py``) differentially.

    ``smt.py`` is never called directly by a test — it is the Z3 layer the
    verifier reaches *through* ``_verify(source)``.  So every test here is a
    DIFFERENTIAL: a Vera program whose verification *outcome* (an obligation's
    ``.status`` / ``.error_code``, the summary counters, or a counterexample's
    content) depends on ``smt`` translating an operator / built-in, solving
    sat↔unsat, or extracting a model correctly.  For each test the docstring
    names the targeted ``smt`` function and the mutation it would catch: "if
    ``smt``'s F mutated to M, THIS assertion flips" is what makes it a kill
    rather than a mere pass.

    Lever (the ``ensures``-over-body postcondition is Tier 3 in this verifier,
    so it is NOT the lever): the **call-site precondition check** (``call_pre``
    / E501) runs a callee ``requires`` predicate through
    ``check_valid`` → ``_extract_counterexample``, with the actual-argument
    expression translated by ``translate_expr`` / the built-in dispatch.  A
    callee whose ``requires`` bound (``>= 0``, ``<= 10`` …) holds for the real
    semantics of the argument expression but NOT for a mutated one therefore
    flips ``verified`` ↔ ``violated`` exactly on the mutation.  The Tier-1
    obligation walkers (``nat_sub`` E502, ``nat_bind`` E503, ``div_zero`` E526,
    ``index_bounds`` E527) give the same lever without a callee.

    Assertions use ``==`` on obligation fields/codes/statuses, ``==`` on the
    exact summary tuple, and ``==`` on counterexample dict items — never
    substring ``in`` on a message (mutmut wraps string literals as ``"XX"+s+
    "XX"`` so substring assertions don't kill string mutations).  Distinct
    ``_387`` names defeat a ``fn_name → None`` mutation.
    """

    # Reusable callee skeletons.  Each imposes a single primitive bound so the
    # caller's argument-expression translation is the only thing under test.
    _NEEDS_GE0 = """
private fn needs_ge0_s387(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ @Int.0 }
"""
    _NEEDS_LE10 = """
private fn needs_le10_s387(@Int -> @Int)
  requires(@Int.0 <= 10) ensures(true) effects(pure)
{ @Int.0 }
"""
    _NEEDS_TRUE = """
private fn needs_true_s387(@Bool -> @Int)
  requires(@Bool.0) ensures(true) effects(pure)
{ 0 }
"""

    @staticmethod
    def _viol(result: VerifyResult) -> list:
        return [o for o in result.obligations if o.status == "violated"]

    @staticmethod
    def _by_fn_kind(result: VerifyResult, fn: str, kind: str):
        ms = [o for o in result.obligations
              if o.fn_name == fn and o.kind == kind]
        assert len(ms) == 1, [(o.fn_name, o.kind, o.status) for o in result.obligations]
        return ms[0]

    # =================================================================
    # translate_expr / _translate_binary — arithmetic + comparison ops.
    # The call-precondition lever: a callee `requires(@Int.0 >= 100)` is
    # discharged iff the actual argument translates with the right op.
    # =================================================================

    def test_arith_add_satisfies_precondition(self) -> None:
        """``@Int.0 + @Int.1`` as an actual arg to ``requires(@Int.0 >= 0)``
        with both params constrained ``>= 0`` VERIFIES (sum of two nonneg is
        nonneg) — pins ``_translate_binary`` ADD.  A mutation of ``+`` to ``-``
        would make ``@Int.0 - @Int.1`` possibly negative → E501.  Uses Nat
        params so the premise is carried."""
        result = _verify(self._NEEDS_GE0 + """
private fn add_arg_s387(@Nat, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Nat.0 + @Nat.1) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        # The callee precondition is DISCHARGED: a successful call-site check
        # records NO obligation, so assert the ABSENCE of a call_pre violation
        # (and of E501).  Asserting the caller's own ``requires(true)`` here
        # would be a tautology — verified regardless of the ADD translation.
        # Paired negative: test_arith_sub_violates_precondition_with_ce.
        assert [o for o in result.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in result.obligations
            if o.kind == "call_pre"]
        assert [d for d in result.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in result.diagnostics if d.error_code == "E501"]

    def test_arith_sub_violates_precondition_with_ce(self) -> None:
        """``@Nat.0 - @Nat.1`` (Nat subtraction) fed to ``requires(@Int.0 >= 0)``
        is NOT provably nonneg (it can underflow into the integers) → E501
        ``call_pre`` violated.  Pins ``_translate_binary`` SUB *and*
        ``_extract_counterexample``: the CE names BOTH operands.  A mutation of
        ``-`` to ``+`` would discharge the bound (nonneg) and lose the
        error."""
        result = _verify(self._NEEDS_GE0 + """
private fn sub_arg_s387(@Nat, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Nat.0 - @Nat.1) }
""")
        o = self._by_fn_kind(result, "sub_arg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.counterexample is not None, o.counterexample
        assert "@Nat.0" in o.counterexample, o.counterexample
        assert "@Nat.1" in o.counterexample, o.counterexample

    def test_comparison_lt_path_condition_discharges(self) -> None:
        """A branch guard ``if @Int.0 < 10 then needs_le10(@Int.0) else 0``
        discharges the callee ``requires(@Int.0 <= 10)`` in the then-branch —
        pins ``_translate_binary`` LT feeding ``_path_conditions``.  The else
        branch passes a literal in range.  A mutation of ``<`` to ``>`` would
        flip the guard so the then-branch sees ``@Int.0 > 10`` and the bound
        ``<= 10`` would fail."""
        result = _verify(self._NEEDS_LE10 + """
private fn lt_guard_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 < 10 then { needs_le10_s387(@Int.0) } else { 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        # Discharged via the then-branch path condition: assert the ABSENCE of a
        # call_pre violation (a successful check leaves no obligation).
        assert [o for o in result.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in result.obligations
            if o.kind == "call_pre"]
        assert [d for d in result.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in result.diagnostics if d.error_code == "E501"]
        # Paired negative (real differential): flip the guard to ``>`` so the
        # then-branch sees ``@Int.0 > 10`` fed to ``requires(@Int.0 <= 10)`` —
        # the path condition no longer discharges the bound → E501 call_pre.
        neg = _verify(self._NEEDS_LE10 + """
private fn lt_neg_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 > 10 then { needs_le10_s387(@Int.0) } else { 0 } }
""")
        o = self._by_fn_kind(neg, "lt_neg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code

    # =================================================================
    # _translate_call (built-ins): abs / min / max — `If(...)` shapes.
    # Each pairs a verify (real semantics satisfy the bound) with a
    # violate (real semantics break it but the swapped op would pass).
    # =================================================================

    def test_builtin_abs_nonneg_satisfies_precondition(self) -> None:
        """``abs(@Int.0)`` fed to ``requires(@Int.0 >= 0)`` VERIFIES — pins the
        ``abs`` built-in ``If(arg >= 0, arg, -arg)``.  A mutation of the ``-arg``
        branch (to ``arg``) makes ``abs`` the identity, so a negative argument
        would violate the bound."""
        result = _verify(self._NEEDS_GE0 + """
private fn abs_ok_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(abs(@Int.0)) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        # ``abs`` makes the value nonneg, so the call is DISCHARGED: assert the
        # ABSENCE of a call_pre violation (a success leaves no obligation).
        assert [o for o in result.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in result.obligations
            if o.kind == "call_pre"]
        assert [d for d in result.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in result.diagnostics if d.error_code == "E501"]
        # Paired negative (real differential): drop ``abs`` and pass the raw
        # ``@Int.0`` — without the nonneg-making built-in the bound can fail
        # → E501 call_pre.  Confirms the success above hinges on ``abs``.
        neg = _verify(self._NEEDS_GE0 + """
private fn abs_neg_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Int.0) }
""")
        o = self._by_fn_kind(neg, "abs_neg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code

    def test_builtin_min_upper_bound_satisfies_and_lower_violates(self) -> None:
        """``min(@Int.0, 10)`` is always ``<= 10`` (satisfies ``requires(@Int.0
        <= 10)``) but NOT always ``>= 0`` (violates ``requires(@Int.0 >= 0)``,
        CE ``@Int.0 = -1``).  The pair pins ``min`` = ``If(a <= b, a, b)``: a
        mutation of ``<=`` to ``>=`` turns ``min`` into ``max``, which would
        flip BOTH verdicts (``max(x,10) >= 10`` discharges the lower bound and
        can exceed the upper)."""
        ok = _verify(self._NEEDS_LE10 + """
private fn min_le_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_le10_s387(min(@Int.0, 10)) }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == [], [
            d.description for d in ok.diagnostics if d.severity == "error"]
        # ``min(x,10) <= 10`` discharges the upper bound: a successful call-site
        # check records no obligation, so assert the ABSENCE of a call_pre
        # violation (the ``min_ge`` block below is the paired E501 negative).
        assert [o for o in ok.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in ok.obligations if o.kind == "call_pre"]
        assert [d for d in ok.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in ok.diagnostics if d.error_code == "E501"]

        neg = _verify(self._NEEDS_GE0 + """
private fn min_ge_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(min(@Int.0, 10)) }
""")
        o = self._by_fn_kind(neg, "min_ge_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.counterexample == {"@Int.0": "-1", "@result": "0"}, o.counterexample

    def test_builtin_max_lower_bound_satisfies_and_upper_violates(self) -> None:
        """Mirror of ``min``: ``max(@Int.0, 0)`` is always ``>= 0`` (satisfies
        the lower bound) but NOT always ``<= 10`` (violates the upper, CE
        ``@Int.0 = 11``).  Pins ``max`` = ``If(a >= b, a, b)``: the ``>=``→``<=``
        mutation turns it into ``min`` and flips both verdicts."""
        ok = _verify(self._NEEDS_GE0 + """
private fn max_ge_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(max(@Int.0, 0)) }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == [], [
            d.description for d in ok.diagnostics if d.severity == "error"]
        # ``max(x,0) >= 0`` discharges the lower bound: assert the ABSENCE of a
        # call_pre violation (the ``max_le`` block below is the paired E501
        # negative).
        assert [o for o in ok.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in ok.obligations if o.kind == "call_pre"]
        assert [d for d in ok.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in ok.diagnostics if d.error_code == "E501"]

        neg = _verify(self._NEEDS_LE10 + """
private fn max_le_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_le10_s387(max(@Int.0, 0)) }
""")
        o = self._by_fn_kind(neg, "max_le_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.counterexample == {"@Int.0": "11", "@result": "0"}, o.counterexample

    # =================================================================
    # _translate_call (built-ins): array_length / string_length —
    # uninterpreted fns with an asserted `result >= 0` axiom.
    # =================================================================

    def test_builtin_array_length_nonneg_axiom(self) -> None:
        """``array_length(@Array<Int>.0)`` fed to ``requires(@Int.0 >= 0)``
        VERIFIES SOLELY because the built-in asserts ``result >= 0`` to the
        solver — pins that ``self.solver.add(result >= 0)`` in the
        ``array_length`` branch (an uninterpreted length fn is otherwise
        unconstrained, so dropping the axiom flips this to E501)."""
        result = _verify(self._NEEDS_GE0 + """
private fn arrlen_s387(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(array_length(@Array<Int>.0)) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        # The ``result >= 0`` axiom discharges the call: assert the ABSENCE of a
        # call_pre violation (success records no obligation).
        assert [o for o in result.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in result.obligations
            if o.kind == "call_pre"]
        assert [d for d in result.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in result.diagnostics if d.error_code == "E501"]
        # Paired negative (real differential): pass a raw ``@Int.0`` instead of
        # the ``array_length`` result — without the nonneg axiom the bound can
        # fail → E501 call_pre.  Confirms the success hinges on that axiom.
        neg = _verify(self._NEEDS_GE0 + """
private fn arrlen_neg_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Int.0) }
""")
        o = self._by_fn_kind(neg, "arrlen_neg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code

    def test_builtin_string_length_nonneg_via_z3_length(self) -> None:
        """``string_length(@String.0)`` fed to ``requires(@Int.0 >= 0)``
        VERIFIES — pins the ``string_length`` branch (``z3.Length`` for the Seq
        sort, plus the ``result >= 0`` axiom).  Z3's ``Length`` is nonneg by
        theory, so a String literal/var length is always ``>= 0``; a mutation
        dropping the axiom or the Seq-sort guard would lose the discharge."""
        result = _verify(self._NEEDS_GE0 + """
private fn strlen_s387(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(string_length(@String.0)) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        # ``z3.Length`` (+ the ``>= 0`` axiom) discharges the call: assert the
        # ABSENCE of a call_pre violation (success records no obligation).
        assert [o for o in result.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in result.obligations
            if o.kind == "call_pre"]
        assert [d for d in result.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in result.diagnostics if d.error_code == "E501"]
        # Paired negative (real differential): pass a raw ``@Int.0`` instead of
        # the ``string_length`` result — without the nonneg guarantee the bound
        # can fail → E501 call_pre.
        neg = _verify(self._NEEDS_GE0 + """
private fn strlen_neg_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Int.0) }
""")
        o = self._by_fn_kind(neg, "strlen_neg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code

    def test_builtin_string_contains_self_is_true(self) -> None:
        """``string_contains(@String.0, @String.0)`` fed to ``requires(@Bool.0)``
        VERIFIES — a string contains itself (``z3.Contains(s, s)`` is valid).
        Pins the ``string_contains`` → ``z3.Contains`` mapping: a mutation
        swapping the argument order is masked here (self-contains), but a
        mutation to ``PrefixOf``/``SuffixOf`` with swapped args, or returning an
        unconstrained Bool, would drop the discharge."""
        result = _verify(self._NEEDS_TRUE + """
private fn contains_s387(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_true_s387(string_contains(@String.0, @String.0)) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        # ``Contains(s, s)`` is valid, so the ``requires(@Bool.0)`` call is
        # discharged: assert the ABSENCE of a call_pre violation (success
        # records no obligation).
        assert [o for o in result.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in result.obligations
            if o.kind == "call_pre"]
        assert [d for d in result.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in result.diagnostics if d.error_code == "E501"]
        # Paired negative (real differential): two DISTINCT strings need not
        # contain each other, so ``Contains(@String.1, @String.0)`` is not
        # provably true → ``requires(@Bool.0)`` fails → E501 call_pre.
        neg = _verify(self._NEEDS_TRUE + """
private fn contains_neg_s387(@String, @String -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_true_s387(string_contains(@String.1, @String.0)) }
""")
        o = self._by_fn_kind(neg, "contains_neg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code

    # =================================================================
    # check_valid — the sat/unsat → verified/violated mapping, and
    # _extract_counterexample — model → dict[str,str].
    # =================================================================

    def test_check_valid_verified_branch(self) -> None:
        """A provably-valid precondition (``@Nat.0 >= 0`` passed a Nat) maps to
        ``verified`` — pins ``check_valid``'s ``unsat → SmtResult(verified)``
        arm.  Carried by ``declare_nat``'s ``>= 0`` premise."""
        result = _verify(self._NEEDS_GE0 + """
private fn cv_ok_s387(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Nat.0) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        # A Nat satisfies ``>= 0``, so the call is DISCHARGED: assert the ABSENCE
        # of a call_pre violation (success records no obligation; the caller's
        # own ``requires(true)`` would verify regardless).  Paired E501 negative:
        # test_check_valid_violated_branch_carries_counterexample (cv_neg).
        assert [o for o in result.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in result.obligations
            if o.kind == "call_pre"]
        assert [d for d in result.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in result.diagnostics if d.error_code == "E501"]

    def test_check_valid_violated_branch_carries_counterexample(self) -> None:
        """A refutable precondition (``@Int.0 >= 0`` passed an unconstrained
        Int) maps to ``violated`` WITH a counterexample — pins ``check_valid``'s
        ``sat → SmtResult(violated, ce)`` arm AND the model-before-pop ordering
        (a witness, not a base-context default).  CE is the forced witness
        ``@Int.0 = -1``."""
        result = _verify(self._NEEDS_GE0 + """
private fn cv_neg_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Int.0) }
""")
        o = self._by_fn_kind(result, "cv_neg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.counterexample == {"@Int.0": "-1", "@result": "0"}, o.counterexample

    def test_extract_counterexample_enumerates_all_vars(self) -> None:
        """``needs_big(@Int.0 + @Int.1)`` against ``requires(@Int.0 >= 100)``
        violates with a CE naming BOTH operands — pins
        ``_extract_counterexample`` iterating EVERY entry of ``self._vars`` (a
        mutation iterating a subset, or skipping the loop body, would drop one
        slot key)."""
        result = _verify("""
private fn needs_big_s387(@Int -> @Int)
  requires(@Int.0 >= 100) ensures(true) effects(pure)
{ 0 }
private fn ce_two_s387(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_big_s387(@Int.0 + @Int.1) }
""")
        o = self._by_fn_kind(result, "ce_two_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.counterexample is not None, o.counterexample
        assert "@Int.0" in o.counterexample, o.counterexample
        assert "@Int.1" in o.counterexample, o.counterexample

    # =================================================================
    # _translate_call_with_info — precondition checking + arity.
    # (The postcondition-assumption loop is not differentially reachable
    # from the verifier surface: an assumed ensures does not propagate
    # to discharge a *downstream* call precondition, so it has no test
    # here — see the agent report's residual note.)
    # =================================================================

    def test_callee_precondition_propagates_to_caller(self) -> None:
        """The caller passes a possibly-negative value to a helper that
        ``requires(@Int.0 >= 0)`` → the precondition check fires as the caller's
        ``call_pre`` E501 (not the callee's).  Pins ``_translate_call_with_info``
        precondition-checking: the violation is attributed to the CALL SITE
        (``fn_name == "fwd_neg_s387"``, ``callee_name`` recorded separately)."""
        result = _verify("""
private fn sink_ge0_s387(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ @Int.0 }
private fn fwd_neg_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ sink_ge0_s387(@Int.0) }
""")
        o = self._by_fn_kind(result, "fwd_neg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.fn_name == "fwd_neg_s387", o.fn_name
        # The callee verifies its own (trivial) contracts independently.
        sink = self._by_fn_kind(result, "sink_ge0_s387", "requires")
        assert sink.status == "verified", sink.status

    # =================================================================
    # _pattern_condition / _translate_match — path-condition narrowing.
    # The matched arm asserts `scrutinee == <pattern value>`; a call
    # precondition inside the arm is discharged iff that holds.
    # =================================================================

    def test_bool_pattern_true_arm_discharges_precondition(self) -> None:
        """In ``match b { true -> needs_true(b), false -> 0 }`` the true-arm
        path condition ``b == true`` discharges ``requires(@Bool.0)`` — pins
        ``_pattern_condition`` ``BoolPattern → scrutinee == BoolVal(True)`` and
        ``_translate_match`` pushing it into ``_path_conditions``."""
        result = _verify(self._NEEDS_TRUE + """
private fn bool_t_s387(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Bool.0 { true -> needs_true_s387(@Bool.0), false -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        # The true-arm path condition discharges ``requires(@Bool.0)``: assert
        # the ABSENCE of a call_pre violation (success records no obligation).
        # Paired E501 negative: test_bool_pattern_false_arm_violates_with_ce.
        assert [o for o in result.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in result.obligations
            if o.kind == "call_pre"]
        assert [d for d in result.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in result.diagnostics if d.error_code == "E501"]

    def test_bool_pattern_false_arm_violates_with_ce(self) -> None:
        """The mirror: in the FALSE arm, ``needs_true(b)`` is unsatisfiable
        because the path condition is ``b == false`` → E501 with CE
        ``@Bool.0 = False``.  If ``_pattern_condition`` mutated the BoolPattern
        value (or used the wrong recognizer) the two arms would swap verdicts."""
        result = _verify(self._NEEDS_TRUE + """
private fn bool_f_s387(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Bool.0 { false -> needs_true_s387(@Bool.0), true -> 0 } }
""")
        o = self._by_fn_kind(result, "bool_f_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.counterexample == {"@Bool.0": "False", "@result": "0"}, o.counterexample

    def test_int_pattern_arm_narrows_scrutinee(self) -> None:
        """In ``match n { 5 -> needs_ge3(n), _ -> 0 }`` the literal arm's path
        condition ``n == 5`` discharges ``requires(@Int.0 >= 3)`` — pins
        ``_pattern_condition`` ``IntPattern → scrutinee == IntVal(5)``."""
        result = _verify("""
private fn needs_ge3_s387(@Int -> @Int)
  requires(@Int.0 >= 3) ensures(true) effects(pure)
{ 0 }
private fn int5_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Int.0 { 5 -> needs_ge3_s387(@Int.0), @Int -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        # The ``5`` arm's path condition ``n == 5`` discharges
        # ``requires(@Int.0 >= 3)``: assert the ABSENCE of a call_pre violation
        # (success records no obligation).  Paired E501 negative:
        # test_int_pattern_wrong_value_arm_violates_with_ce.
        assert [o for o in result.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in result.obligations
            if o.kind == "call_pre"]
        assert [d for d in result.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in result.diagnostics if d.error_code == "E501"]

    def test_int_pattern_wrong_value_arm_violates_with_ce(self) -> None:
        """The mirror: the ``1`` arm's path condition ``n == 1`` does NOT satisfy
        ``>= 3`` → E501 with CE ``@Int.0 = 1`` (the IntVal the pattern pinned).
        A mutation of the pattern literal would change the CE value."""
        result = _verify("""
private fn needs_ge3b_s387(@Int -> @Int)
  requires(@Int.0 >= 3) ensures(true) effects(pure)
{ 0 }
private fn int1_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Int.0 { 1 -> needs_ge3b_s387(@Int.0), @Int -> 0 } }
""")
        o = self._by_fn_kind(result, "int1_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.counterexample == {"@Int.0": "1", "@result": "0"}, o.counterexample

    # =================================================================
    # _translate_nullary_ctor / _pattern_condition (recognizer) /
    # _get_or_create_adt_sort — custom-ADT nullary match dispatch.
    # =================================================================

    def test_custom_adt_nullary_match_verifies(self) -> None:
        """A custom 3-constructor ADT (``Red|Green|Blue``) matched with nullary
        recognizers, where one arm discharges a nonneg bound via
        ``array_length`` — pins ``_translate_nullary_ctor`` + the
        ``_pattern_condition`` NullaryPattern recognizer + ADT-sort creation
        (``_get_or_create_adt_sort``).  Reachability: a malformed sort or a
        wrong recognizer would make the match untranslatable (whole obligation
        drops to Tier 3)."""
        result = _verify("""
private data Color_s387 { Red, Green, Blue }
private fn needs_ge0col_s387(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ 0 }
private fn col_s387(@Color_s387 -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Color_s387.0 {
    Red -> needs_ge0col_s387(array_length([7])),
    Green -> 0,
    Blue -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        # ``array_length([7])`` is nonneg, so the Red-arm call is DISCHARGED:
        # assert the ABSENCE of a call_pre violation (success records no
        # obligation).
        assert [o for o in result.obligations
                if o.kind == "call_pre" and o.status == "violated"] == [], [
            (o.fn_name, o.status) for o in result.obligations
            if o.kind == "call_pre"]
        assert [d for d in result.diagnostics if d.error_code == "E501"] == [], [
            d.description for d in result.diagnostics if d.error_code == "E501"]
        # Paired negative (real differential): same nullary-match dispatch, but
        # the Red arm passes a raw possibly-negative ``@Int.0`` instead of the
        # nonneg ``array_length`` result → ``requires(@Int.0 >= 0)`` fails →
        # E501 call_pre.  Confirms the match arm actually reaches the check.
        neg = _verify("""
private data Color_neg_s387 { Red, Green, Blue }
private fn needs_ge0coln_s387(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ 0 }
private fn col_neg_s387(@Color_neg_s387, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Color_neg_s387.0 {
    Red -> needs_ge0coln_s387(@Int.0),
    Green -> 0,
    Blue -> 0 } }
""")
        o = self._by_fn_kind(neg, "col_neg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code

    # =================================================================
    # get_rank_fn — structural rank axioms for recursive-ADT decreases.
    # =================================================================

    def test_recursive_decreases_verified_via_rank_fn(self) -> None:
        """A structurally-recursive ``len`` over ``Cons(T, L<T>)`` with
        ``decreases(@L<Int>.0)`` VERIFIES — pins ``get_rank_fn``'s structural
        axiom ``is_Cons(x) ⟹ rank(tail(x)) < rank(x)`` (without it the recursive
        call on the tail can't be shown to decrease → not ``verified``)."""
        result = _verify("""
private data L_s387<T> { Nil, Cons(T, L_s387<T>) }
private fn len_s387(@L_s387<Int> -> @Nat)
  requires(true) ensures(true) decreases(@L_s387<Int>.0) effects(pure)
{ match @L_s387<Int>.0 {
    Nil -> 0,
    Cons(@Int, @L_s387<Int>) -> 1 + len_s387(@L_s387<Int>.0) } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "len_s387", "decreases")
        assert o.status == "verified", o.status

    def test_nondecreasing_recursion_is_not_verified(self) -> None:
        """The mirror: recursing on the SAME metric ``bad(@Nat.0)`` does NOT
        decrease, so the ``decreases`` obligation is NOT ``verified`` (Tier 3,
        E525).  Distinguishes ``get_rank_fn``/numeric-decrease from a mutation
        that always reports the metric as decreasing."""
        result = _verify("""
private fn bad_s387(@Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{ if @Nat.0 == 0 then { 0 } else { bad_s387(@Nat.0) } }
""")
        o = self._by_fn_kind(result, "bad_s387", "decreases")
        assert o.status != "verified", o.status
        assert o.status == "tier3", o.status

    # =================================================================
    # _get_or_create_tuple_sort — non-literal tuple destructure makes
    # the components projectable so each narrows independently.
    # =================================================================

    def test_nonliteral_tuple_destructure_obligates_each_field(self) -> None:
        """``let Tuple<@Nat,@Nat> = mk(@Int.0)`` where ``mk`` returns
        ``@Tuple<Int,Int>`` produces TWO ``nat_bind`` (E503) obligations — one
        per projected component.  Pins ``_get_or_create_tuple_sort``: it builds
        a Tuple datatype with a field+accessor per component so each projection
        narrows.  If Tuple fell back to a scalar ``Int``, the per-field
        projections would not exist and the obligation count would change."""
        result = _verify("""
private fn mk_s387(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(@Int.0, @Int.0) }
private fn use_tup_s387(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk_s387(@Int.0); @Nat.0 }
""")
        binds = [o for o in result.obligations
                 if o.fn_name == "use_tup_s387" and o.kind == "nat_bind"]
        assert len(binds) == 2, [(o.kind, o.status) for o in result.obligations]
        for o in binds:
            assert o.status == "violated", o.status
            assert o.error_code == "E503", o.error_code

    # =================================================================
    # _get_index_fn / _get_element_sort_for_array / _get_length_fn —
    # array index-bounds machinery.
    # =================================================================

    def test_index_bounds_guarded_verifies(self) -> None:
        """``arr[i]`` guarded by ``requires(i >= 0 && i < array_length(arr))``
        makes the ``index_bounds`` (E527) obligation VERIFIED — pins the array
        machinery (``_get_length_fn`` for ``array_length``, ``_get_index_fn`` /
        ``_get_element_sort_for_array`` for the index translation) AND the
        ``&&``/``<`` translation in the guard.  Without the length fn correctly
        modelling the bound, the index check would not discharge."""
        result = _verify("""
private fn idx_ok_s387(@Array<Int>, @Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 < array_length(@Array<Int>.0))
  ensures(true) effects(pure)
{ @Array<Int>.0[@Int.0] }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "idx_ok_s387", "index_bounds")
        assert o.status == "verified", o.status

    def test_index_bounds_unguarded_is_tier3(self) -> None:
        """The mirror: an unguarded ``arr[i]`` cannot prove ``0 <= i <
        length(arr)`` → ``index_bounds`` is Tier 3 (runtime check), not
        verified.  Distinguishes the real bound check from a mutation that
        vacuously discharges it."""
        result = _verify("""
private fn idx_raw_s387(@Array<Int>, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[@Int.0] }
""")
        o = self._by_fn_kind(result, "idx_raw_s387", "index_bounds")
        assert o.status == "tier3", o.status

    # =================================================================
    # div_zero (E526) / nat_sub (E502) — Tier-1 walker obligations that
    # exercise translate_expr's DIV and SUB plus counterexample content.
    # =================================================================

    def test_div_zero_unguarded_violates(self) -> None:
        """``@Int.1 / @Int.0`` with no guard on the divisor → ``div_zero`` (E526)
        violated.  Pins translate_expr DIV reaching the verifier's divisor
        walker; guarding the divisor (next test) flips it to verified."""
        result = _verify("""
private fn div_raw_s387(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 / @Int.0 }
""")
        o = self._by_fn_kind(result, "div_raw_s387", "div_zero")
        assert o.status == "violated", o.status
        assert o.error_code == "E526", o.error_code

    def test_div_zero_guarded_verifies(self) -> None:
        """``@Int.1 / @Int.0`` with ``requires(@Int.0 != 0)`` → ``div_zero``
        verified.  Pins the ``!=`` (NEQ) translation feeding the divisor guard:
        a mutation of NEQ to EQ would make the guard ``@Int.0 == 0`` and the
        divisor obligation would no longer discharge."""
        result = _verify("""
private fn div_ok_s387(@Int, @Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(pure)
{ @Int.1 / @Int.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "div_ok_s387", "div_zero")
        assert o.status == "verified", o.status

    def test_nat_sub_underflow_violates_with_both_slots_in_ce(self) -> None:
        """``@Nat.1 - @Nat.0`` can underflow → ``nat_sub`` (E502) violated, with a
        counterexample naming BOTH Nat operands.  Pins translate_expr SUB on the
        Nat-subtraction walker AND ``_extract_counterexample`` enumerating each
        ``_vars`` entry."""
        result = _verify("""
private fn natsub_s387(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.1 - @Nat.0 }
""")
        o = self._by_fn_kind(result, "natsub_s387", "nat_sub")
        assert o.status == "violated", o.status
        assert o.error_code == "E502", o.error_code
        assert o.counterexample is not None, o.counterexample
        assert "@Nat.0" in o.counterexample, o.counterexample
        assert "@Nat.1" in o.counterexample, o.counterexample
