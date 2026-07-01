"""Tests for vera.verifier — mutation_obligations (#387 mutation-hardening: obligation-record completeness and projection helpers).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations


from tests.verifier_helpers import (
    _verify,
)


# =====================================================================
# Obligation-record completeness (#387 mutation sweep — V0)
#
# The #680/#552/#520 batteries pin each obligation's `kind` + `status`.
# These pin the REMAINING `ProofObligation` fields — `fn_name`,
# `error_code`, `counterexample`, `expr_text` — across the
# `_check_*_obligation` discharge layer and its `_report_*` siblings.
# The coarse `_verify_err` / `_verify_ok` helpers only assert "an error
# exists", so a mutation that drops `fn_name` (→ `None`), nulls the
# counterexample, or flips an `error_code` string survives them.  A
# distinct `_387` function name per test ensures the `None`-substitution
# mutant (`_record_obligation(None, ...)`) cannot coincide with a default.
# =====================================================================

class TestObligationRecordCompleteness387:
    """Pin every `ProofObligation` field at the primitive-safety discharge
    sites so the discharge / report bookkeeping cannot silently mutate."""

    def test_div_zero_violation_pins_full_record(self) -> None:
        result = _verify("""
private fn unsafe_div_387(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""")
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1, [(o.kind, o.status) for o in divs]
        o = divs[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E526", o.error_code
        assert o.fn_name == "unsafe_div_387", o.fn_name
        assert o.counterexample, o.counterexample
        assert o.expr_text == "@Int.0 / @Int.1", o.expr_text
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [e.error_code for e in errors] == ["E526"], [
            (e.error_code, e.description) for e in errors]

    def test_div_zero_verified_pins_record(self) -> None:
        result = _verify("""
private fn safe_div_387(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1, [(o.kind, o.status) for o in divs]
        o = divs[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "safe_div_387", o.fn_name
        assert o.error_code == "", o.error_code
        assert o.counterexample is None, o.counterexample

    def test_nat_sub_violation_pins_full_record(self) -> None:
        result = _verify("""
private fn unsafe_sub_387(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(subs) == 1, [(o.kind, o.status) for o in subs]
        o = subs[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E502", o.error_code
        assert o.fn_name == "unsafe_sub_387", o.fn_name
        assert o.counterexample, o.counterexample
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [e.error_code for e in errors] == ["E502"], [
            (e.error_code, e.description) for e in errors]

    def test_nat_sub_verified_pins_record(self) -> None:
        result = _verify("""
private fn safe_sub_387(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(subs) == 1, [(o.kind, o.status) for o in subs]
        o = subs[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "safe_sub_387", o.fn_name
        assert o.error_code == "", o.error_code

    def test_index_oob_violation_pins_full_record(self) -> None:
        result = _verify("""
private fn oob_387(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [1, 2, 3][5] }
""")
        idxs = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idxs) == 1, [(o.kind, o.status) for o in idxs]
        o = idxs[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E527", o.error_code
        assert o.fn_name == "oob_387", o.fn_name
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [e.error_code for e in errors] == ["E527"], [
            (e.error_code, e.description) for e in errors]

    def test_index_in_bounds_verified_pins_record(self) -> None:
        result = _verify("""
private fn inbounds_387(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [10, 20, 30][1] }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        idxs = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idxs) == 1, [(o.kind, o.status) for o in idxs]
        o = idxs[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "inbounds_387", o.fn_name
        assert o.error_code == "", o.error_code

    # --- _report_* diagnostic content (deterministic; runs after the solver) ---

    def test_div_by_zero_diagnostic_content(self) -> None:
        """Pin the E526 diagnostic's description / rationale / fix / spec_ref /
        counterexample (`_report_div_by_zero`), not just its code."""
        result = _verify("""
private fn unsafe_div_387(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E526"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "unsafe_div_387" in d.description, d.description
        assert "may divide by zero" in d.description, d.description
        assert "division" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        assert "@Int.1 = " in d.description, d.description
        assert "divisor is non-zero" in d.rationale, d.rationale
        assert "i64.div_s" in d.rationale, d.rationale
        assert "requires(@Int.1 != 0)" in d.fix, d.fix
        assert "6.4.3" in d.spec_ref, d.spec_ref

    def test_modulo_diagnostic_says_modulo(self) -> None:
        """`a % b` must report "modulo", not "division" — pins the
        `op_word = "modulo" if MOD else "division"` branch (`_report_div_by_zero`)."""
        result = _verify("""
private fn unsafe_mod_387(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 % @Int.1 }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E526"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        assert "modulo" in errs[0].description, errs[0].description
        assert "division" not in errs[0].description, errs[0].description

    def test_float_divisor_is_exempt_no_obligation(self) -> None:
        """A `@Float64` divisor traps to inf/NaN, not a runtime trap, so it
        carries NO `div_zero` obligation — pins the float64 early-exit guard
        in `_check_div_zero_obligation` (a mutation here would emit a bogus
        E526 on float division)."""
        result = _verify("""
private fn fdiv_387(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ @Float64.0 / @Float64.1 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o for o in result.obligations if o.kind == "div_zero"] == [], [
            (o.kind, o.status) for o in result.obligations]

    def test_underflow_diagnostic_content(self) -> None:
        """Pin the E502 diagnostic's description / rationale / fix / spec_ref
        (`_report_underflow`)."""
        result = _verify("""
private fn unsafe_sub_387(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "unsafe_sub_387" in d.description, d.description
        assert "may underflow" in d.description, d.description
        assert "@Nat subtraction" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        # The counterexample loop renders each non-@result slot as
        # `    <name> = <value>`; pin the format (value is Z3-chosen).
        assert "@Nat.0 = " in d.description, d.description
        assert "@Nat.1 = " in d.description, d.description
        assert "non-negativity" in d.rationale, d.rationale
        assert "requires(@Nat.0 >= @Nat.1)" in d.fix, d.fix
        assert "4.4" in d.spec_ref, d.spec_ref

    def test_index_oob_diagnostic_content(self) -> None:
        """Pin the E527 diagnostic's description / rationale / fix / spec_ref
        (`_report_index_oob`)."""
        result = _verify("""
private fn oob_387(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [1, 2, 3][5] }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E527"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "oob_387" in d.description, d.description
        assert "out of bounds" in d.description, d.description
        assert "array_length" in d.rationale, d.rationale
        assert "array_length" in d.fix, d.fix
        assert "6.4.3" in d.spec_ref, d.spec_ref

    def test_nat_binding_violation_pins_record_and_content(self) -> None:
        """`let @Nat = @Int.0` (unguarded) → E503 nat_bind violation;
        pins the record fields + `_report_nat_binding` content."""
        result = _verify("""
private fn narrow_neg_387(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in binds]
        o = binds[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E503", o.error_code
        assert o.fn_name == "narrow_neg_387", o.fn_name
        assert o.counterexample, o.counterexample
        errs = [d for d in result.diagnostics if d.error_code == "E503"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "narrow_neg_387" in d.description, d.description
        assert "narrowing into a @Nat" in d.description, d.description
        assert "may be negative" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        assert "@Int.0 = " in d.description, d.description
        assert "non-negativity invariant" in d.rationale, d.rationale
        assert "requires(@Int.0 >= 0)" in d.fix, d.fix
        assert "2.2.1" in d.spec_ref, d.spec_ref

    def test_nat_binding_verified_pins_record(self) -> None:
        result = _verify("""
private fn narrow_ok_387(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in binds]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "narrow_ok_387", o.fn_name
        assert o.error_code == "", o.error_code

    def test_postcondition_violation_diagnostic_content(self) -> None:
        """A false `ensures` → E500; pins `_report_violation`'s description /
        rationale / fix (all three repair classes, #675) / spec_ref + the
        recorded `ensures` obligation."""
        result = _verify("""
private fn bad_post_387(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E500"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "Postcondition does not hold" in d.description, d.description
        assert "bad_post_387" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        # E500 also renders the @result slot via `_type_expr_to_slot_name`.
        assert "@Int.0 = " in d.description, d.description
        assert "@Int.result = " in d.description, d.description
        assert "concrete input values" in d.rationale, d.rationale
        assert "implementation" in d.fix, d.fix
        assert "strengthen" in d.fix and "requires(" in d.fix, d.fix
        assert "ensures(" in d.fix, d.fix
        assert "6.4.1" in d.spec_ref, d.spec_ref
        # The E500 code lives on the diagnostic (asserted above); the
        # `ensures` obligation records kind + status + fn_name (no error_code).
        viol = [o for o in result.obligations
                if o.kind == "ensures" and o.status == "violated"]
        assert len(viol) == 1, [(o.kind, o.status) for o in result.obligations]
        assert viol[0].fn_name == "bad_post_387", viol[0].fn_name

    # --- summary-counter bookkeeping ------------------------------------
    # Pin `tier1_verified` / `tier3_runtime` / `total` so a `summary.X += 1`
    # cannot silently mutate to `= 1` or `+= 2`.  A guarded obligation already
    # sits at counter >= 1 (requires + ensures discharged first), so ONE
    # obligation pins the verified + total counters.  The tier3 counter starts
    # at 0 (contracts verify, they don't go tier3), so TWO tier3 sites are
    # needed to make `tier3_runtime += 1 → = 1` observable.

    def test_div_verified_summary_counts(self) -> None:
        result = _verify("""
private fn sdiv_387(@Int, @Int -> @Int)
  requires(@Int.1 != 0) ensures(true) effects(pure)
{ @Int.0 / @Int.1 }
""")
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_div_two_tier3_summary_counts(self) -> None:
        result = _verify("""
effect Src387 { op g(Unit -> Option<Int>); }
private fn d1_387(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Src387>)
{ match Src387.g(()) { Some(@Int) -> 1 / @Int.0, None -> 1 } }
private fn d2_387(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Src387>)
{ match Src387.g(()) { Some(@Int) -> 1 / @Int.0, None -> 1 } }
""")
        s = result.summary
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert [o.status for o in divs] == ["tier3", "tier3"], [
            (o.kind, o.status) for o in result.obligations]
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (4, 2, 6), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_sub_verified_summary_counts(self) -> None:
        result = _verify("""
private fn ssub_387(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1) ensures(true) effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_sub_two_tier3_summary_counts(self) -> None:
        result = _verify("""
effect SrcN387 { op g(Unit -> Option<Nat>); }
private fn s1_387(@Nat -> @Nat)
  requires(true) ensures(true) effects(<SrcN387>)
{ match SrcN387.g(()) { Some(@Nat) -> @Nat.0 - @Nat.1, None -> 0 } }
private fn s2_387(@Nat -> @Nat)
  requires(true) ensures(true) effects(<SrcN387>)
{ match SrcN387.g(()) { Some(@Nat) -> @Nat.0 - @Nat.1, None -> 0 } }
""")
        s = result.summary
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert [o.status for o in subs] == ["tier3", "tier3"], [
            (o.kind, o.status) for o in result.obligations]
        assert s.tier3_runtime == 2, s.tier3_runtime

    def test_index_verified_summary_counts(self) -> None:
        result = _verify("""
private fn sidx_387(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ [10, 20, 30][1] }
""")
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_index_two_tier3_summary_counts(self) -> None:
        result = _verify("""
private fn i1_387(@Array<Int>, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[@Nat.0] }
private fn i2_387(@Array<Int>, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")
        s = result.summary
        idxs = [o for o in result.obligations if o.kind == "index_bounds"]
        assert [o.status for o in idxs] == ["tier3", "tier3"], [
            (o.kind, o.status) for o in result.obligations]
        assert s.tier3_runtime == 2, s.tier3_runtime

    def test_nat_binding_verified_summary_counts(self) -> None:
        result = _verify("""
private fn nbind_ok_387(@Int -> @Nat)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ let @Nat = @Int.0; @Nat.0 }
""")
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    # --- refinement-predicate binding (refine_bind, E505) ----------------

    def test_refined_binding_violation_pins_record_and_content(self) -> None:
        """`let @Pos387 = @Int.0 - 100` cannot prove `> 0` → E505 refine_bind
        violation; pins the record fields + `_report_refined_binding` content."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };

private fn rbind_neg_387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Pos387 = @Int.0 - 100; @Pos387.0 }
""")
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in binds]
        o = binds[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E505", o.error_code
        assert o.fn_name == "rbind_neg_387", o.fn_name
        assert o.counterexample, o.counterexample
        errs = [d for d in result.diagnostics if d.error_code == "E505"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "rbind_neg_387" in d.description, d.description
        assert "may violate the refinement predicate" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        assert "@Int.0 = " in d.description, d.description
        assert "refinement type" in d.rationale, d.rationale
        assert "requires(" in d.fix, d.fix
        assert "2.6" in d.spec_ref, d.spec_ref

    def test_refined_binding_verified_pins_record(self) -> None:
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };

private fn rbind_ok_387(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ let @Pos387 = @Int.0; @Pos387.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in binds]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "rbind_ok_387", o.fn_name
        assert o.error_code == "", o.error_code


class TestProjectionHelpers387:
    """#387: pin the De Bruijn *projection* / *term* obligation helpers — the
    methods that obligate a @Nat / refined narrowing against an uninterpreted
    field-accessor Z3 term rather than an AST node.

    These have no translation step and (for ADT sub-patterns / nested ctor
    patterns) no Tier-3 ``let``-downgrade, so an undischarged obligation is a
    genuine E503 / E505.  The De Bruijn projection math (which accessor index
    maps to which obligation) is SOUNDNESS: a ``(idx, i)`` off-by-one silently
    obligates the wrong field, flipping an obligation's existence or verdict.

    Reachability (probed):
      - ``_check_nat_binding_obligation_term`` / ``_obligate_subpattern_
        narrowings``: ``match opt { Some(@Nat) -> ... }`` on ``Option<Int>``
        (the @Int payload narrows into @Nat).
      - ``_check_refined_binding_obligation_term``: same shape narrowing into a
        refined type (``Some(@Pos387)`` on ``Option<Int>``) → E505.
      - ``_obligate_subpattern_term``: nested ``Some(Some(@Nat))`` on
        ``Option<Option<Int>>``.
      - ``_obligate_destructure_narrowings``: ``let Tuple<@Nat,@Nat> = mk()``.

    Assertions use ``==`` on obligation fields/codes (mutmut wraps string
    literals as ``"XX"+s+"XX"``, so substring ``in`` does NOT kill a string
    mutation) and exact tuples on the summary counters.  Distinct ``_387``
    function names catch a ``fn_name → None`` mutation.
    """

    # =================================================================
    # _check_nat_binding_obligation_term  (3243-3283)
    # via _obligate_subpattern_narrowings opaque path (Some(@Nat))
    # =================================================================

    def test_nat_subpattern_violated_pins_record_and_content(self) -> None:
        """``Some(@Nat)`` on ``Option<Int>`` (unguarded @Int payload) → E503.
        Pins the violated branch: status/code/fn_name/CE + ``total -= 1`` and
        the ``_report_nat_binding`` "ADT sub-pattern bind" diagnostic."""
        result = _verify("""
private fn sp_nat_neg_387(@Option<Int> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.kind == "nat_bind", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E503", o.error_code
        assert o.fn_name == "sp_nat_neg_387", o.fn_name
        assert o.counterexample, o.counterexample
        errs = [d for d in result.diagnostics if d.error_code == "E503"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "sp_nat_neg_387" in d.description, d.description
        assert "ADT sub-pattern bind" in d.description, d.description
        assert "may be negative" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        # The narrowed @Nat obligation decrements `total` (it's an error, not a
        # counted verdict); requires + ensures remain the only counted verdicts.
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (2, 0, 2), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_nat_subpattern_verified_pins_record(self) -> None:
        """``Some(@Nat)`` on ``Option<Pos387>`` — the source field is ``> 0``
        hence ``>= 0``, so the projection VERIFIES.  Pins the verified branch
        (``tier1_verified += 1``, status ``verified``, empty code, no CE) AND
        the ``source_ty`` premise: drop the ``_term_source_fact`` assumption and
        this flips to a false E503."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn sp_nat_ok_387(@Option<Pos387> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match @Option<Pos387>.0 { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "sp_nat_ok_387", o.fn_name
        assert o.counterexample is None, o.counterexample
        # verified narrowing counts: requires + nat_bind + ensures.
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    # =================================================================
    # _check_refined_binding_obligation_term  (3495-3548)
    # via _obligate_subpattern_narrowings (Some(@Pos387))
    # =================================================================

    def test_refined_subpattern_violated_pins_record_and_content(self) -> None:
        """``Some(@Pos387)`` on ``Option<Int>`` → E505 (Int payload may be
        ``<= 0``).  Pins the violated branch of
        ``_check_refined_binding_obligation_term``: refine_bind / E505 / CE /
        ``total -= 1`` + the predicate text in the diagnostic."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn sp_ref_neg_387(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@Pos387) -> @Pos387.0, None -> 1 } }
""")
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.kind == "refine_bind", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E505", o.error_code
        assert o.fn_name == "sp_ref_neg_387", o.fn_name
        assert o.counterexample, o.counterexample
        errs = [d for d in result.diagnostics if d.error_code == "E505"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "sp_ref_neg_387" in d.description, d.description
        assert "ADT sub-pattern bind" in d.description, d.description
        assert "@Int.0 > 0" in d.description, d.description
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (2, 0, 2), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_refined_subpattern_verified_pins_source_fact(self) -> None:
        """``Some(@Pos387)`` (``> 0``) on ``Option<Gt5_387>`` (``> 5``): a
        GENUINE narrowing (the predicates differ) that nonetheless holds —
        because the ``source_ty`` premise ``> 5`` implies ``> 0``.  Soundness:
        if ``_term_source_fact`` drops the source predicate, this flips to a
        false E505; if ``_refined_field_narrows`` mis-fires, the obligation
        vanishes entirely."""
        result = _verify("""
type Gt5_387 = { @Int | @Int.0 > 5 };
type Pos387 = { @Int | @Int.0 > 0 };
private fn sp_ref_ok_387(@Option<Gt5_387> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Gt5_387>.0 { Some(@Pos387) -> @Pos387.0, None -> 1 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "sp_ref_ok_387", o.fn_name
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_refined_vs_nat_subpattern_kind_discriminates(self) -> None:
        """A refined sub-pattern records ``refine_bind``/E505, a bare-@Nat one
        records ``nat_bind``/E503 — pins the kind/code routing in
        ``_obligate_subpattern_narrowings`` (refined-first branch vs nat
        branch).  A mutation collapsing the refined branch would re-route the
        @Pos387 narrowing through the nat path (wrong kind + wrong code)."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn route_ref_387(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@Pos387) -> @Pos387.0, None -> 1 } }
private fn route_nat_387(@Option<Int> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        by_fn = {o.fn_name: o for o in result.obligations
                 if o.kind in ("nat_bind", "refine_bind")}
        assert by_fn["route_ref_387"].kind == "refine_bind", by_fn
        assert by_fn["route_ref_387"].error_code == "E505", by_fn
        assert by_fn["route_nat_387"].kind == "nat_bind", by_fn
        assert by_fn["route_nat_387"].error_code == "E503", by_fn

    # =================================================================
    # _obligate_subpattern_term  (3697-3755) — nested ctor patterns
    # Some(Some(@Nat)) on Option<Option<Int>>
    # =================================================================

    def test_nested_subpattern_violated_is_obligated(self) -> None:
        """``Some(Some(@Nat))`` on ``Option<Option<Int>>``: the INNER @Int->@Nat
        narrowing must be obligated (E503) — pins the recursion in
        ``_obligate_subpattern_narrowings`` → ``_obligate_subpattern_term``.
        Drop the recursion and this becomes an unguarded false Tier-1 (NO
        obligation at all)."""
        result = _verify("""
private fn nested_neg_387(@Option<Option<Int>> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match @Option<Option<Int>>.0 {
    Some(Some(@Nat)) -> @Nat.0, Some(None) -> 0, None -> 0 } }
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E503", o.error_code
        assert o.fn_name == "nested_neg_387", o.fn_name
        assert o.counterexample, o.counterexample

    def test_nested_subpattern_verified_carries_source_fact(self) -> None:
        """``Some(Some(@Nat))`` on ``Option<Option<Pos387>>``: the inner source
        is ``> 0`` hence ``>= 0``, so the nested narrowing VERIFIES — pins both
        the recursion AND the recursive ``_subpattern_source_facts_term`` carry
        of the inner field's source fact through the nesting."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn nested_ok_387(@Option<Option<Pos387>> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match @Option<Option<Pos387>>.0 {
    Some(Some(@Nat)) -> @Nat.0, Some(None) -> 0, None -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "nested_ok_387", o.fn_name
        assert o.error_code == "", o.error_code

    def test_nested_refined_subpattern_violated(self) -> None:
        """``Some(Some(@Pos387))`` on ``Option<Option<Int>>`` → E505 via the
        nested-recursion refined branch of ``_obligate_subpattern_term``."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn nested_ref_neg_387(@Option<Option<Int>> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Option<Int>>.0 {
    Some(Some(@Pos387)) -> @Pos387.0, Some(None) -> 1, None -> 1 } }
""")
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E505", o.error_code
        assert o.fn_name == "nested_ref_neg_387", o.fn_name
        assert o.counterexample, o.counterexample

    # =================================================================
    # _obligate_destructure_narrowings  (3901-3995)
    # =================================================================

    def test_destructure_projectable_violated_two_components(self) -> None:
        """``let Tuple<@Nat,@Nat> = Tuple(@Int.0, @Int.1)`` — a literal tuple
        RHS the SMT layer projects.  Both components narrow @Int->@Nat and both
        VIOLATE (E503) via the projectable ``for i in nat_narrowing`` loop.
        Pins: 2 obligations (a ``+= 2``→``+= 1`` loop mutation drops one), each
        violated/E503/fn_name."""
        result = _verify("""
private fn dest_neg_387(@Int, @Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Nat, @Nat> = Tuple(@Int.0, @Int.1);
  @Nat.0 + @Nat.1
}
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 2, [(o.kind, o.status) for o in result.obligations]
        assert all(o.status == "violated" for o in binds), [
            o.status for o in binds]
        assert all(o.error_code == "E503" for o in binds), [
            o.error_code for o in binds]
        assert all(o.fn_name == "dest_neg_387" for o in binds), [
            o.fn_name for o in binds]
        assert all(o.counterexample for o in binds), binds
        errs = [d for d in result.diagnostics if d.error_code == "E503"]
        assert len(errs) == 2, [d.description for d in result.diagnostics]
        assert all("tuple destructure" in d.description for d in errs), [
            d.description for d in errs]

    def test_destructure_refined_projectable_violated(self) -> None:
        """``let Tuple<@Pos387,@Pos387> = Tuple(@Int.0, @Int.1)`` → 2× E505 via
        the projectable ``for i, target in refined_narrowing`` loop."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn dest_ref_neg_387(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Pos387, @Pos387> = Tuple(@Int.0, @Int.1);
  @Pos387.0 + @Pos387.1
}
""")
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 2, [(o.kind, o.status) for o in result.obligations]
        assert all(o.status == "violated" for o in binds), [
            o.status for o in binds]
        assert all(o.error_code == "E505" for o in binds), [
            o.error_code for o in binds]
        assert all(o.fn_name == "dest_ref_neg_387" for o in binds), [
            o.fn_name for o in binds]

    def test_destructure_asymmetric_projection_index_soundness(self) -> None:
        """SOUNDNESS — the De Bruijn projection index.  An asymmetric tuple
        ``Tuple<@Nat, @Int>`` from ``Tuple(@Pos387.0, @Int.0)``: only component
        0 narrows (into @Nat), and it VERIFIES because component 0's source
        ``@Pos387`` is ``> 0``.  If the accessor index ``(idx, 0)`` were mutated
        to ``(idx, 1)`` it would project the unconstrained ``@Int`` component
        and the obligation would VIOLATE; an off-by-one the other way would
        mis-source the fact.  Exactly ONE nat_bind, verified."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn dest_asym_387(@Pos387, @Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Nat, @Int> = Tuple(@Pos387.0, @Int.0);
  @Nat.0
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "dest_asym_387", o.fn_name

    def test_destructure_unprojectable_guarded_tier3(self) -> None:
        """``let Tuple<@Nat,@Nat> = TupSrc387.mk(())`` where the source is an
        EFFECT OPERATION returning ``Tuple<Int,Int>`` (a genuinely opaque value
        the SMT layer cannot project as a datatype) → the ``sort is None``
        branch: 2 GUARDED Tier-3 nat_bind obligations (codegen runtime-guards
        the destructure).  Pins ``tier3``/``tier3_runtime += 1`` ×2 and that they
        are NOT errors.

        The source MUST be opaque for a structural reason — an effect op's
        return is uninterpreted.  A plain ``fn`` call whose return type is the
        same ``Tuple<Int,Int>`` does NOT reach this branch when the call carries
        a non-Unit argument: the projector builds a Tuple sort and the
        components narrow to E503 (see
        ``test_nonliteral_tuple_destructure_obligates_each_field``).  Using the
        effect op keeps this test pinned to the unprojectable Tier-3 path
        regardless of argument shape."""
        result = _verify("""
effect TupSrc387 { op mk(Unit -> Tuple<Int, Int>); }
private fn dest_t3_387(@Unit -> @Nat)
  requires(true) ensures(true) effects(<TupSrc387>)
{
  let Tuple<@Nat, @Nat> = TupSrc387.mk(());
  @Nat.0 + @Nat.1
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations
                 if o.kind == "nat_bind" and o.fn_name == "dest_t3_387"]
        assert len(binds) == 2, [(o.kind, o.status) for o in result.obligations]
        assert all(o.status == "tier3" for o in binds), [
            o.status for o in binds]
        # tier3_runtime starts at 0, so 2 guarded sites pin `+= 1` (vs `= 1`),
        # plus #798: the body `@Nat.0 + @Nat.1` add emits a third Tier-3
        # int_overflow obligation (opaque operands → runtime overflow trap).
        assert result.summary.tier3_runtime == 3, result.summary.tier3_runtime

    def test_destructure_no_narrowing_no_obligation(self) -> None:
        """``let Tuple<@Int,@Int> = Tuple(...)`` — neither component narrows
        (target @Int == source @Int), so NO nat_bind/refine_bind obligation
        fires.  Pins the ``not _is_nat_type(target)`` / narrowing guard: a
        mutation that obligates a non-narrowing component would emit a bogus
        E503 here."""
        result = _verify("""
private fn dest_none_387(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(@Int.0, @Int.1);
  @Int.0 + @Int.1
}
""")
        proj = [o for o in result.obligations
                if o.kind in ("nat_bind", "refine_bind")]
        assert proj == [], [(o.kind, o.status) for o in proj]

    # --- _obligate_subpattern_narrowings: opaque (unprojectable) scrutinee ---
    # A `match f() { Some(@Nat) -> ... }` whose scrutinee is a function-call
    # return: the SMT layer can't project it as a datatype (sort/idx is None),
    # so the narrowing falls to the opaque tail branch rather than a term check.

    def test_opaque_nat_subpattern_guarded_tier3(self) -> None:
        """Opaque scrutinee (call return) ``Some(@Nat)`` on ``Option<Int>`` →
        the unprojectable nat tail (3887-3898): a GUARDED Tier-3 nat_bind
        (codegen guards the sub-pattern bind at run time).  Pins ``tier3`` +
        ``tier3_runtime`` and that it is NOT an error."""
        result = _verify("""
private fn srcopt_387(@Unit -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(1) }
private fn sp_opaque_nat_387(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match srcopt_387(()) { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations
                 if o.kind == "nat_bind" and o.fn_name == "sp_opaque_nat_387"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "tier3", o.status
        assert result.summary.tier3_runtime == 1, result.summary.tier3_runtime

    def test_opaque_refined_subpattern_unguarded_tier3(self) -> None:
        """Opaque scrutinee ``Some(@Pos387)`` on ``Option<Int>`` → the
        unprojectable refined tail (3864-3870): an UNGUARDED Tier-3 refine_bind
        (E506 warning, ``tier3_unguarded``, excluded from totals — refined
        narrowings have no codegen runtime guard).  Distinguishes the
        ``guarded=False`` refined opaque path from the ``guarded=True`` nat one:
        a mutation flipping the flag would mis-claim a runtime guard."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn srcopt2_387(@Unit -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(1) }
private fn sp_opaque_ref_387(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match srcopt2_387(()) { Some(@Pos387) -> @Pos387.0, None -> 1 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations
                 if o.kind == "refine_bind" and o.fn_name == "sp_opaque_ref_387"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "tier3_unguarded", o.status
        assert o.error_code == "E506", o.error_code
        warns = [d for d in result.diagnostics if d.error_code == "E506"]
        assert len(warns) == 1, [d.description for d in result.diagnostics]
        # Unguarded refined Tier-3 does NOT increment tier3_runtime (R7).
        assert result.summary.tier3_runtime == 0, result.summary.tier3_runtime
