"""Tests for vera.verifier — nat_obligations (@Nat subtraction-underflow (#520) and binding-site narrowing (#552) obligations).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations


from vera.parser import parse_to_ast

from tests.verifier_helpers import (
    _verify,
    _verify_err,
    _verify_ok,
)


# =====================================================================
# @Nat subtraction underflow obligation (#520)
# =====================================================================

class TestNatSubtractionObligation520:
    """`@Nat - @Nat` carries a Tier-1 proof obligation `lhs >= rhs`.

    Per spec/04 §4.4 and spec/11 §11.2.1, a subtraction site whose
    result type is `@Nat` AND at least one operand has `@Nat`
    *provenance* (a slot reference, a function call returning `@Nat`,
    or a sub-expression containing one) must prove that the left
    operand is at least as large as the right. The verifier
    discharges the obligation from preconditions (`requires`) and
    path conditions (`if` / `match` branches). When Z3 cannot
    discharge it, verification fails with a counterexample so the
    author can add a `requires` clause; the codegen separately emits
    a runtime guard at the same set of sites.

    Path-A scope (#520): pure-literal subtractions like `0 - 1`
    (the canonical "I want -1 as a literal" idiom widely used in
    `Err(_) -> 0 - 1` and `throw(0 - 1)` positions) are intentionally
    exempt — neither operand has `@Nat` provenance, so the
    obligation does not fire. `test_pure_literal_subtraction_not_flagged`
    pins that exception. Catching `let @Nat = 0 - 1` (binding-site
    narrowing) is the broader generalisation tracked as #552.

    `@Int - @Int` and `@Nat - @Int → @Int` carry no obligation —
    `Int` is allowed to be negative, so underflow is not a violation.
    """

    def test_requires_clause_discharges_obligation(self) -> None:
        """Explicit `requires(@Nat.0 >= @Nat.1)` discharges the obligation."""
        _verify_ok("""
private fn safe_sub(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(@Nat.result <= @Nat.0)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""")

    def test_if_guard_discharges_obligation(self) -> None:
        """Path condition `@Nat.0 != 0` (else branch of `if @Nat.0 == 0`)
        implies `@Nat.0 >= 1`, which discharges `@Nat.0 - 1 >= 0`.

        This is the canonical recursion shape used throughout the
        examples and conformance suite (factorial, fib, mutual
        recursion). After this fix lands they must continue to verify
        without source changes.
        """
        _verify_ok("""
private fn dec(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    @Nat.0 - 1
  }
}
""")

    def test_subtract_zero_discharges_trivially(self) -> None:
        """`@Nat.0 - 0` is always safe — RHS is the literal 0."""
        _verify_ok("""
private fn id_via_sub(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.0)
  effects(pure)
{ @Nat.0 - 0 }
""")

    def test_self_subtract_discharges(self) -> None:
        """`@Nat.0 - @Nat.0` is always 0 — Z3 knows lhs == rhs."""
        _verify_ok("""
private fn self_sub(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == 0)
  effects(pure)
{ @Nat.0 - @Nat.0 }
""")

    def test_unguarded_subtract_fails(self) -> None:
        """Bare `@Nat.0 - @Nat.1` without a `requires` fails verification.

        Counterexample: @Nat.0 = 0, @Nat.1 = 1 produces -1, which is
        not a valid @Nat. The verifier must reject.
        """
        _verify_err("""
private fn unsafe_sub(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""", "underflow")

    def test_unsafe_sub_stmt_position_obligated(self) -> None:
        """A `@Nat - @Nat` in STATEMENT position (result discarded) still carries
        the underflow obligation — the subtraction walker recurses into the
        block's `ExprStmt` statements.  Pins the statement-position path the
        same way #730 closes it for call preconditions."""
        _verify_err("""
private fn stmt_sub(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1; 0 }
""", "underflow")

    def test_int_subtract_not_obligated(self) -> None:
        """`@Int - @Int → @Int` carries no underflow obligation.

        @Int is signed; negative results are well-defined. The
        obligation should fire only when the *result type* is @Nat.
        """
        _verify_ok("""
private fn int_sub(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 - @Int.1)
  effects(pure)
{ @Int.0 - @Int.1 }
""")

    def test_nat_minus_int_not_obligated(self) -> None:
        """`@Nat - @Int → @Int` carries no obligation.

        Per checker.py:264 the type rule promotes to the more general
        type when operands differ. `@Nat - @Int` becomes `@Int`
        because @Nat <: @Int, so the result is allowed to be negative.
        Author opted into Int semantics by mixing types.
        """
        _verify_ok("""
private fn mixed_sub(@Nat, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Int.0 }
""")

    def test_partial_requires_does_not_discharge(self) -> None:
        """`requires(@Nat.0 > 0)` alone does not discharge `@Nat.0 - @Nat.1`.

        The precondition rules out @Nat.0 == 0 but says nothing about
        @Nat.1 vs @Nat.0. Counterexample: @Nat.0 = 1, @Nat.1 = 5.
        """
        _verify_err("""
private fn partial_req(@Nat, @Nat -> @Nat)
  requires(@Nat.0 > 0)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""", "underflow")

    def test_pure_literal_subtraction_not_flagged(self) -> None:
        """`0 - 1` (pure-literal "I want -1" idiom) is intentionally
        not flagged at Path A (#520) scope.

        The checker classifies non-negative literals as `@Nat`, so the
        subtraction is technically `@Nat - @Nat`. But the corpus uses
        this idiom widely in `Err(_) -> 0 - 1` and `throw(0 - 1)`
        positions where the result is consumed at `@Int` and upcast
        cleanly. Flagging would force a corpus-wide migration to
        negative literals (`-1`).

        The verifier therefore requires at least one operand to have
        Nat *provenance* (slot ref or function return), not just
        non-negative-literal classification. Pure-literal underflow
        consumed at a `@Nat` position (e.g. `let @Nat = 0 - 1`) would
        still escape — that is Path B (#552) territory.
        """
        _verify_ok("""
private fn negative_sentinel(@Unit -> @Int)
  requires(true)
  ensures(@Int.result < 0)
  effects(pure)
{ 0 - 1 }
""")

    def test_compound_shadow_subtraction_is_tier3_not_e502(self) -> None:
        """A subtraction where BOTH operands are compound expressions embedding
        opaque shadows must fall to Tier-3, not a false E502.  After a
        non-literal destructure shadows both `@Nat` components, `(@Nat.0 + 1) -
        (@Nat.1 + 1)` has neither operand a *direct* shadow, so the direct
        guard misses it — `_contains_opaque_shadow` catches the embedded
        shadows (PR #778 review, the subtraction analogue of the E526
        compound-divisor fix)."""
        result = _verify("""
private fn mksub(@Nat -> @Tuple<Nat, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Nat.0, @Nat.0) }

private fn sub_compound(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Nat, @Nat> = mksub(@Nat.0); (@Nat.0 + 1) - (@Nat.1 + 1) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(subs) == 1 and subs[0].status == "tier3", [
            (o.kind, o.status) for o in subs
        ]


class TestNatBindingObligation552:
    """`@Int` narrowing into a `@Nat` slot carries a Tier-1 `value >= 0`
    obligation at every binding site (#552, generalising #520).

    Fires when the target slot is `@Nat` AND the bound value is not
    already statically `@Nat` — the single condition that keeps #552
    disjoint from #520's `@Nat - @Nat` subtraction obligation (a
    `@Nat - @Nat` value is already `@Nat`, so it is not a narrowing).
    Discharged from preconditions and path conditions; an undischarged
    narrowing fails with E503 and a counterexample.

    Projection sites whose *source* type the verifier cannot resolve
    statically — ADT sub-pattern binds (`Some(@Nat.0)`) and non-literal
    tuple destructures — are left to the Tier-3 codegen runtime guard.
    """

    # ---- Site 1: let bindings -------------------------------------
    def test_let_narrow_unguarded_fails(self) -> None:
        _verify_err("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}
""", "may be negative")

    def test_narrow_stmt_position_obligated(self) -> None:
        """An `@Int -> @Nat` narrowing in STATEMENT position (a discarded call
        whose `@Nat` formal receives an `@Int` arg) still carries the
        `value >= 0` obligation — the narrowing walker recurses into the block's
        `ExprStmt` statements.  Same statement-position blind spot #730 closes
        for call preconditions."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn g(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ takes_nat(@Int.0); @Int.0 }
""", "may be negative")

    def test_let_narrow_requires_discharges(self) -> None:
        _verify_ok("""
private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}
""")

    def test_let_narrow_if_guard_discharges(self) -> None:
        """Path condition `@Int.0 >= 0` discharges the let narrowing.

        Asserts the obligation actually *fired and verified* on the
        constrained path, not merely that no error surfaced — a regression
        that dropped the obligation would otherwise pass silently (#748
        review)."""
        result = _verify("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 >= 0 then {
    let @Nat = @Int.0;
    @Nat.0
  } else {
    0
  }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]

    def test_let_already_nat_not_flagged(self) -> None:
        """`let @Nat = @Nat.0` is Nat->Nat — no narrowing, no obligation."""
        result = _verify("""
private fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Nat.0;
  @Nat.0
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == []
        assert not [o for o in result.obligations if o.kind == "nat_bind"]

    # ---- Site 2: call arguments -----------------------------------
    def test_call_arg_narrow_unguarded_fails(self) -> None:
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ takes_nat(@Int.0) }
""", "may be negative")

    def test_call_arg_narrow_requires_discharges(self) -> None:
        _verify_ok("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ takes_nat(@Int.0) }
""")

    # ---- Site 3: constructor fields -------------------------------
    def test_ctor_field_narrow_unguarded_fails(self) -> None:
        _verify_err("""
private data Box { MkBox(Nat) }

private fn f(@Int -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{ MkBox(@Int.0) }
""", "may be negative")

    def test_ctor_field_narrow_requires_discharges(self) -> None:
        _verify_ok("""
private data Box { MkBox(Nat) }

private fn f(@Int -> @Box)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ MkBox(@Int.0) }
""")

    # ---- Site 4: top-level match binds ----------------------------
    def test_match_bind_narrow_unguarded_fails(self) -> None:
        _verify_err("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    @Nat -> @Nat.0
  }
}
""", "may be negative")

    def test_match_bind_narrow_requires_discharges(self) -> None:
        _verify_ok("""
private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    @Nat -> @Nat.0
  }
}
""")

    # ---- Site 6: literal-tuple destructure ------------------------
    def test_destructure_narrow_unguarded_fails(self) -> None:
        """Component 0 (`@Int.0`) narrows; component 1 (literal 5) does not."""
        _verify_err("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = Tuple(@Int.0, 5);
  @Nat.0
}
""", "may be negative")

    def test_destructure_narrow_requires_discharges(self) -> None:
        result = _verify("""
private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = Tuple(@Int.0, 5);
  @Nat.0
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]

    # ---- Double-emit disjointness with #520 -----------------------
    def test_nat_minus_nat_is_sub_not_bind(self) -> None:
        """`let @Nat = @Nat.0 - @Nat.1`: value already @Nat -> #520 only."""
        result = _verify("""
private fn f(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true)
  effects(pure)
{
  let @Nat = @Nat.0 - @Nat.1;
  @Nat.0
}
""")
        kinds = [o.kind for o in result.obligations]
        assert kinds.count("nat_bind") == 0, kinds
        assert kinds.count("nat_sub") == 1, kinds
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_int_minus_literal_is_bind_not_sub(self) -> None:
        """`let @Nat = @Int.0 - 100`: value @Int -> #552 only."""
        result = _verify("""
private fn f(@Int -> @Nat)
  requires(@Int.0 >= 100)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0 - 100;
  @Nat.0
}
""")
        kinds = [o.kind for o in result.obligations]
        assert kinds.count("nat_bind") == 1, kinds
        assert kinds.count("nat_sub") == 0, kinds
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_generic_nat_call_subtraction_obligated(self) -> None:
        """`idv(@Nat.0) - idv(@Nat.1)` with `idv<T>(@T -> @T)`: both operands
        are generic calls returning @Nat.  `_has_nat_origin` now recovers the
        instantiated @Nat result from the checker's side-table — the declared
        return is a `TypeVar` the local heuristic missed — so the #520
        underflow obligation fires instead of being silently skipped (CR #756).
        The generic calls are untranslatable to Z3, so the obligation is
        Tier-3 (codegen-#520-guarded), not a static E502; the point is it is no
        longer dropped."""
        result = _verify("""
private forall<T>
fn idv(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

public fn f(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ idv(@Nat.0) - idv(@Nat.1) }
""")
        kinds = [o.kind for o in result.obligations]
        assert kinds.count("nat_sub") >= 1, kinds
        assert any(o.kind == "nat_sub" and o.status == "tier3"
                   for o in result.obligations), \
            [(o.kind, o.status) for o in result.obligations]

    def test_array_nat_element_subtraction_obligated(self) -> None:
        """`arr[0] - arr[1]` on an `@Array<Nat>` parameter (length >= 2, so both
        indices are in bounds) reports the #520 underflow (E502): array indexing
        preserves the element's @Nat provenance.  `_has_nat_origin` consults the
        checker's
        side-table for the IndexExpr's resolved element type (it cannot recurse
        on the `@Array` operand, which is not itself @Nat), so the subtraction
        is obligated like any `@Nat - @Nat` (CR #756)."""
        result = _verify("""
public fn f(@Array<Nat> -> @Nat)
  requires(array_length(@Array<Nat>.0) >= 2)
  ensures(true)
  effects(pure)
{ @Array<Nat>.0[0] - @Array<Nat>.0[1] }
""")
        assert [o.status for o in result.obligations
                if o.kind == "nat_sub"] == ["violated"], \
            [(o.kind, o.status) for o in result.obligations]
        assert any(d.error_code == "E502"
                   for d in result.diagnostics if d.severity == "error")

    def test_nat_addition_not_flagged(self) -> None:
        """`let @Nat = @Nat.0 + @Nat.1`: value already @Nat, no obligation."""
        result = _verify("""
private fn f(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Nat.0 + @Nat.1;
  @Nat.0
}
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"]

    def test_pure_literal_subtraction_caught(self) -> None:
        """`let @Nat = 0 - 1`: typed @Nat but valued -1.  #520 exempts the
        pure-literal subtraction (no @Nat provenance) and defers it here;
        #552 must catch it (E503)."""
        _verify_err("""
private fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = 0 - 1;
  @Nat.0
}
""", "may be negative")

    def test_nonneg_literal_not_flagged(self) -> None:
        """`let @Nat = 5`: a non-negative literal is genuinely @Nat — no
        obligation.  The pure-literal carve-out is subtraction-only, so
        bare literals and additions don't fire."""
        result = _verify("""
private fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = 5;
  @Nat.0
}
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"]

    def test_wrapped_underflow_subtraction_caught(self) -> None:
        """A pure-literal subtraction wrapped in a block / if-branch /
        match arm, or nested in arithmetic, still narrows a
        possibly-negative value into @Nat.  `_is_nat_typed` calls the
        wrapper @Nat, so a top-level-only check would miss these — the
        obligation must look through to the value-producing leaf
        (#552 review)."""
        for body in (
            "let @Nat = { 0 - 1 };\n  @Nat.0",
            "let @Nat = if @Int.0 >= 0 then { 5 } else { 0 - 1 };\n  @Nat.0",
            "let @Nat = match @Int.0 { @Int -> 0 - 1 };\n  @Nat.0",
            "let @Nat = (0 - 1) + (0 - 1);\n  @Nat.0",
        ):
            src = (
                "private fn f(@Int -> @Nat)\n"
                "  requires(true)\n"
                "  ensures(true)\n"
                "  effects(pure)\n"
                "{\n"
                "  " + body + "\n"
                "}\n"
            )
            _verify_err(src, "may be negative")

    def test_subpattern_bind_literal_nat_obligated(self) -> None:
        """An @Nat sub-pattern binding the @Int payload of a *literal*
        `Some(@Int.0)` narrows — #747 obligates the constructor argument
        directly (deferred pre-#747)."""
        _verify_err("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(@Int.0) {
    Some(@Nat) -> @Nat.0,
    None -> 0
  }
}
""", "may be negative")

    def test_subpattern_bind_opaque_nat_obligated(self) -> None:
        """An @Nat sub-pattern binding a non-@Nat field of an *opaque*
        scrutinee (`match opt { Some(@Nat) -> }` on `Option<Int>`) narrows
        — #747 obligates the uninterpreted field accessor `>= 0`."""
        _verify_err("""
private fn f(@Option<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(@Nat) -> @Nat.0,
    None -> 0
  }
}
""", "may be negative")

    def test_subpattern_bind_already_nat_not_obligated(self) -> None:
        """A @Nat sub-pattern over an already-@Nat field (`Option<Nat>`)
        is not a narrowing — #747 must NOT obligate it (the accessor
        carries no `>= 0` fact, so a spurious obligation would fail)."""
        result = _verify("""
private fn f(@Option<Nat> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Nat>.0 {
    Some(@Nat) -> @Nat.0,
    None -> 0
  }
}
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_generic_effect_op_formal_nat_obligated(self) -> None:
        """A generic effect-op formal instantiated to @Nat (`E<Nat>.wait`)
        narrows an @Int argument.  #747 makes the checker synthesise op
        arguments against their instantiated formal, recording the @Nat
        target, so the obligation now fires (deferred pre-#747)."""
        result = _verify("""
effect E<T> {
  op wait(T -> Unit);
}

public fn f(@Int -> @Unit)
  requires(true)
  ensures(true)
  effects(<E<Nat>>)
{
  E.wait(@Int.0)
}
""")
        assert [o for o in result.obligations if o.kind == "nat_bind"], \
            "expected a nat_bind obligation at the generic effect-op formal"
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any("may be negative" in e.description.lower() for e in errors)

    def test_generic_effect_op_formal_nat_discharged(self) -> None:
        """The generic effect-op narrowing discharges from a precondition.
        Pins the emitted `nat_bind` status as ``verified`` so a regression to
        *no* obligation can't pass silently (CR #756)."""
        result = _verify("""
effect E<T> {
  op wait(T -> Unit);
}

public fn f(@Int -> @Unit)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(<E<Nat>>)
{
  E.wait(@Int.0)
}
""")
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"], \
            [(o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_generic_function_formal_nat_obligated(self) -> None:
        """A generic function formal fixed to @Nat by a sibling argument
        (`pick(@Nat.0, @Int.0)` with `pick<T>(@T, @T -> @T)`) narrows the
        @Int argument into the @Nat-instantiated formal.  #747 recovers the
        instantiation from the target side-table (deferred pre-#747)."""
        result = _verify("""
private forall<T>
fn pick(@T, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

private fn f(@Nat, @Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ pick(@Nat.0, @Int.0) }
""")
        assert [o for o in result.obligations if o.kind == "nat_bind"], \
            "expected a nat_bind obligation at the generic function formal"
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any("may be negative" in e.description.lower() for e in errors)

    def test_generic_function_formal_nat_discharged(self) -> None:
        """The generic function-formal narrowing discharges from a
        precondition constraining the @Int argument.  Pins the emitted
        `nat_bind` status as ``verified`` (CR #756)."""
        result = _verify("""
private forall<T>
fn pick(@T, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

private fn f(@Nat, @Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ pick(@Nat.0, @Int.0) }
""")
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"], \
            [(o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_generic_ctor_field_nat_obligated(self) -> None:
        """A generic constructor field instantiated to @Nat (`Some(@Int.0)`
        building an `Option<Nat>`) narrows an @Int into the @Nat field.
        #747 recovers the instantiation from the checker's *target*
        side-table, so the obligation now fires (deferred pre-#747)."""
        result = _verify("""
private fn f(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}
""")
        assert [o for o in result.obligations if o.kind == "nat_bind"], \
            "expected a nat_bind obligation at the generic constructor field"
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any("may be negative" in e.description.lower() for e in errors)

    def test_generic_ctor_field_nat_discharged(self) -> None:
        """The generic constructor-field narrowing discharges from a
        precondition, exactly like the concrete-field case (#747).  Pins the
        emitted `nat_bind` status as ``verified`` (CR #756)."""
        result = _verify("""
private fn f(@Int -> @Option<Nat>)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}
""")
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"], \
            [(o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_generic_nat_returning_call_no_false_narrowing(self) -> None:
        """A generic call whose result is @Nat (`ident(@Nat.0)` with
        `ident<T>(@T -> @T)`) flowing into a @Nat slot is NOT a narrowing —
        the source is already @Nat.  `_is_nat_typed` consults the checker's
        semantic side-table (the local heuristics see only the callee's
        TypeVar return), so no spurious obligation / false E504 fires at the
        unguarded generic constructor field (CR #756)."""
        result = _verify("""
private forall<T>
fn ident(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

public fn f(@Nat -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Some(ident(@Nat.0)) }
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"], \
            [(o.kind, o.status) for o in result.obligations]
        assert not [d for d in result.diagnostics if d.error_code == "E504"]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_non_literal_nat_destructure_obligated(self) -> None:
        """#747 site 2: a non-literal tuple-destructure source — here a
        function call returning `Tuple<Int, Int>` — narrowing both @Int
        components into @Nat slots is obligated `>= 0`.  Under `requires(true)`
        each component is unconstrained, so both narrowings fail (E503).
        Closes the deferral the SMT tuple-datatype support unblocked: the RHS
        now translates to a projectable Z3 datatype."""
        result = _verify("""
private fn mk(@Unit -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(1, 2) }

private fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = mk(@Unit.0);
  @Nat.0
}
""")
        violated = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]
        assert len(violated) == 2, [(o.kind, o.status)
                                    for o in result.obligations]
        assert all(o.error_code == "E503" for o in violated)
        assert any(d.error_code == "E503" for d in result.diagnostics)

    def test_non_literal_nat_destructure_already_nat_not_obligated(
        self,
    ) -> None:
        """#747: a non-literal destructure whose source components are
        *already* @Nat (`Tuple<Nat, Nat>`) is not a narrowing, so no
        obligation fires.  Pins the soundness guard — the projected accessor
        term carries no `>= 0` fact, so obligating an already-@Nat source
        would fail the proof spuriously (the parallel of the ADT-sub-pattern
        guard).  A `requires`-discharge isn't expressible here: Vera contracts
        cannot project an opaque tuple's components, so the already-@Nat
        source is the discharge analog."""
        result = _verify("""
private fn mkn(@Unit -> @Tuple<Nat, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(1, 2) }

private fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = mkn(@Unit.0);
  @Nat.0
}
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_if_expr_destructure_tier3_runtime(self) -> None:
        """#747: an `if`-expression tuple source the SMT layer does not model
        as a projectable datatype leaves a real @Int->@Nat destructure
        narrowing unverifiable *statically* — but codegen guards every @Nat
        destructure component at run time, so each is recorded as a guarded
        Tier-3 obligation (`tier3` / `tier3_runtime`), not a false unguarded
        E504 (CodeRabbit, PR #756).  Both @Nat components of the
        `Tuple<@Nat, @Nat>` are recorded independently — the per-component
        accounting the untranslatable fallback must mirror the projectable
        path (CodeRabbit, PR #756 round 6)."""
        result = _verify("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = if @Int.0 > 0 then { Tuple(@Int.0, @Int.0) } else { Tuple(@Int.0, @Int.0) };
  @Nat.0
}
""")
        tier3 = [o for o in result.obligations
                 if o.kind == "nat_bind" and o.status == "tier3"]
        # One Tier-3 obligation per @Nat component (the 2-tuple → 2).
        assert len(tier3) == 2, [(o.kind, o.status)
                                 for o in result.obligations]
        # Codegen-guarded → counted as runtime checks, with no E504 warning.
        assert result.summary.tier3_runtime == 2
        assert not [d for d in result.diagnostics if d.error_code == "E504"]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_caught_narrowing_carries_e503_and_nat_bind(self) -> None:
        """A caught narrowing is tagged E503 with a `nat_bind`-kind
        obligation — not merely a description substring (#552 review)."""
        result = _verify("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}
""")
        violated = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]
        assert len(violated) == 1, [o.kind for o in result.obligations]
        assert violated[0].error_code == "E503"
        # The counterexample must WITNESS the violation with a negative
        # @Int.0, not a model-completed default — pins the check_valid
        # model-before-pop fix, which a revert silently degrades to
        # @Int.0 = 0 (a non-witness for `value >= 0`) (#748 review).
        ce = violated[0].counterexample or {}
        assert "@Int.0" in ce and int(ce["@Int.0"]) < 0, ce

    def test_non_let_tier3_narrowing_warns_unguarded(self) -> None:
        """A narrowing at a *genuinely unguarded* site whose value the SMT
        layer can't translate surfaces an E504 warning + a `tier3_unguarded`
        obligation — NOT a silent `tier3_runtime` 'runtime check'.  The
        effect-operation argument is the canonical unguarded site: codegen
        does not yet emit a runtime guard there (#754), so an untranslatable
        narrowing into a @Nat effect-op formal (here `array_length`'s opaque
        @Int into `E.wait(Nat)`) is neither statically proven nor
        runtime-checked.  Distinct from the concrete @Nat *call argument*
        form, which #747 codegen DOES guard (now a `tier3_runtime`) — the
        `guarded` flag the verifier threads must distinguish them
        (CodeRabbit, PR #756 round 6)."""
        result = _verify('''
effect E {
  op wait(Nat -> Unit);
}

public fn f(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<E>)
{
  E.wait(array_length(string_lines("a\\nb")))
}
''')
        unguarded = [o for o in result.obligations
                     if o.status == "tier3_unguarded"]
        assert len(unguarded) == 1, [o.status for o in result.obligations]
        assert unguarded[0].error_code == "E504"
        warns = [d for d in result.diagnostics if d.error_code == "E504"]
        assert len(warns) == 1 and warns[0].severity == "warning"
        # excluded from the discharged totals (like a violation)
        assert not any(o.status == "tier3" for o in result.obligations
                       if o.kind == "nat_bind")
        assert result.summary.tier3_runtime == 0

    def test_call_arg_nat_minus_nat_is_sub_not_bind(self) -> None:
        """A `@Nat - @Nat` *call argument* is #520's obligation (nat_sub),
        not #552's — the disjointness holds at a non-let site too, where
        the site walk (not just `_narrows_into_nat`) could regress
        (#552 review)."""
        result = _verify("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true)
  effects(pure)
{ takes_nat(@Nat.0 - @Nat.1) }
""")
        kinds = [o.kind for o in result.obligations]
        assert kinds.count("nat_bind") == 0, kinds
        assert kinds.count("nat_sub") == 1, kinds
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_pipe_call_arg_narrowing_obligated(self) -> None:
        """`(0 - 5) |> takesNat()` desugars to `takesNat(0 - 5)` — the piped
        left operand narrows @Int into a @Nat formal, so it must carry the
        same `value >= 0` obligation as the direct call.  The walker keeps the
        pipe as a `BinaryExpr`, so without explicit handling the narrowing was
        missed entirely — a false 'verified' for a negative value (CR #756)."""
        _verify_err("""
private fn takesNat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

public fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ (0 - 5) |> takesNat() }
""", "may be negative")

    def test_pipe_call_arg_narrowing_discharged(self) -> None:
        """The piped narrowing verifies when the precondition proves the
        argument non-negative — the discharged companion to
        `test_pipe_call_arg_narrowing_obligated` (CR #756)."""
        result = _verify("""
private fn takesNat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

public fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ @Int.0 |> takesNat() }
""")
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"], \
            [(o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_destructure_threads_cur_env_for_later_obligation(self) -> None:
        """After a literal destructure, a later statement's narrowing
        obligation must translate against the destructured slot, not a
        stale outer binding of the same slot name (CodeRabbit, PR #748).
        Both components are -5, so `takes_nat(@Int.0)` must fail (E503),
        proving the destructured value rather than the @Int param (which
        `requires(@Int.0 >= 0)` would have wrongly discharged)."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(0 - 5, 0 - 5);
  takes_nat(@Int.0)
}
""", "may be negative")

    def test_destructure_non_literal_source_invalidates_stale_binding(
        self,
    ) -> None:
        """A non-literal destructure source (here an `if`-expression) cannot
        pair each binding with a translatable component, so the destructured
        slots must be rebound to fresh vars — otherwise `takes_nat(@Int.0)`
        would wrongly discharge against the `@Int` param's
        `requires(@Int.0 >= 0)` instead of the unknown destructured value
        (CodeRabbit, PR #748)."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = if @Int.0 > 0 then { Tuple(0 - 1, 0 - 1) } else { Tuple(1, 1) };
  takes_nat(@Int.0)
}
""", "may be negative")

    def test_let_non_translatable_source_invalidates_stale_binding(
        self,
    ) -> None:
        """An untranslatable `let` RHS (here `array_length(string_lines(...))`)
        rebinds the slot to a fresh var, so a later `takes_nat(@Int.0)` cannot
        falsely discharge against the `@Int` param's `requires(@Int.0 >= 0)` —
        the let-statement analogue of the destructure stale-binding fix
        (CodeRabbit, PR #748)."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let @Int = array_length(string_lines("ab"));
  takes_nat(@Int.0)
}
""", "may be negative")

    def test_narrowing_inside_array_literal_caught(self) -> None:
        """A narrowing nested in an expression container (array literal)
        is visited by the walker, not skipped at the fallthrough
        (CodeRabbit, PR #748)."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Nat> = [takes_nat(@Int.0)];
  0
}
""", "may be negative")

    def test_narrowing_inside_index_expr_caught(self) -> None:
        """A narrowing nested in an `IndexExpr` (here the index position) is
        visited by the walker, not skipped — pins the IndexExpr recursion
        branch a regression could silently drop (#749 item 1)."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Array<Int>, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Array<Int>.0[takes_nat(@Int.0)] }
""", "may be negative")

    def test_narrowing_inside_interpolated_string_caught(self) -> None:
        """A narrowing nested in an interpolated-string part is visited by
        the walker — pins the InterpolatedString recursion branch a
        regression could silently drop (#749 item 1)."""
        _verify_err(r"""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{ "v: \(takes_nat(@Int.0))" }
""", "may be negative")

    def test_fresh_slot_var_resolves_nat_alias(self) -> None:
        """`_fresh_slot_var` dispatches on the *resolved* type, so a
        destructure slot whose declared type is an alias of a scalar
        (`type Count = Nat`) is invalidated with the scalar's Z3 invariant,
        not dropped as an unknown ADT.  Direct unit pin for the alias path
        the destructure suite only exercises indirectly (#749 item 2)."""
        from vera import ast
        from vera.smt import SmtContext
        from vera.verifier import ContractVerifier

        verifier = ContractVerifier()
        verifier._register_all(parse_to_ast(
            "type Count = Nat;\n"
            "private fn f(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 }"
        ))
        smt = SmtContext()

        def named(name: str) -> ast.NamedType:
            return ast.NamedType(name=name, type_args=())

        alias = verifier._fresh_slot_var(smt, named("Count"))
        direct = verifier._fresh_slot_var(smt, named("Nat"))
        # The alias resolves to Nat and gets a real Z3 var with the same
        # sort as a directly-@Nat slot...
        assert alias is not None and direct is not None
        assert alias.sort() == direct.sort()
        # ...while a genuinely-unknown ADT type has no scalar sort.
        assert verifier._fresh_slot_var(smt, named("SomeUserAdt")) is None

    def test_narrows_into_nat_verifier_codegen_parity(self) -> None:
        """`_narrows_into_nat` is hand-mirrored in the verifier and codegen
        (#749 item 3).  The soundness-relevant property is an *implication*,
        not equality: codegen must emit a runtime guard for everything the
        verifier obligates (`verifier ⟹ codegen`).  The reverse — codegen
        guarding a value the verifier already proves @Nat — is a harmless
        over-guard (e.g. `string_length`, whose @Nat return codegen's
        `_is_static_nat_typed` does not recognise, so it conservatively
        guards while the verifier raises no obligation).  The *dangerous*
        desync is verifier-obligates-but-codegen-doesn't-guard, which would
        let a negative @Nat escape an unverified compile — a builtin's @Nat
        return wired into the verifier mirror but not codegen would trip the
        assertion below."""
        from vera.verifier import ContractVerifier
        from vera.wasm.context import StringPool, WasmContext

        verifier = ContractVerifier()
        codegen = WasmContext(StringPool())
        corpus = [
            "@Int.0", "@Nat.0", "0 - 1", "5 - 1", "@Int.0 + 1",
            "@Nat.0 - @Nat.1", "-1", "{ 0 - 1 }",
            "if @Int.0 > 0 then { 1 } else { 0 - 1 }",
            # FnCall returns are the most likely place the two mirrors desync,
            # since each independently classifies the callee's @Nat-ness.
            "array_length(@Array<Int>.0)", 'string_length("hi")',
            "abs(@Int.0)", "nat_to_int(@Nat.0)",
        ]
        for body in corpus:
            src = (
                "private fn f(@Int, @Nat, @Array<Int> -> @Int)\n"
                "  requires(true) ensures(true) effects(pure)\n"
                f"{{ {body} }}"
            )
            expr = parse_to_ast(src).declarations[0].decl.body.expr
            v = verifier._narrows_into_nat(expr)
            c = codegen._narrows_into_nat(expr)
            # codegen guards ⊇ verifier obligates (no unsound miss).
            assert (not v) or c, (
                f"unsound `_narrows_into_nat` desync on {body!r}: the verifier "
                f"obligates a `>= 0` check but codegen emits no runtime guard")

    def test_effect_op_argument_narrowing_caught(self) -> None:
        """An @Int narrowing into an effect operation's @Nat formal
        (`IO.sleep : Nat -> Unit`) is obligated — qualified calls were
        previously only recursed into, never checked against their
        formal parameter types (CodeRabbit, PR #748)."""
        _verify_err("""
public fn f(@Int -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.sleep(@Int.0)
}
""", "may be negative")

    def test_effect_op_argument_narrowing_discharged(self) -> None:
        """The effect-op narrowing verifies cleanly when the argument is
        constrained non-negative — guards against an over-conservative
        regression at the new binding site (CodeRabbit, PR #748)."""
        result = _verify("""
public fn f(@Int -> @Unit)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(<IO>)
{
  IO.sleep(@Int.0)
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]

    def test_user_effect_op_argument_narrowing_caught(self) -> None:
        """A user-declared effect operation with a @Nat parameter obligates
        an @Int argument the same as built-in IO.sleep. User effects must
        register their OpInfo (operations were previously stored empty), so
        lookup_effect_op exposes param_types (CodeRabbit, PR #748)."""
        _verify_err("""
effect E {
  op wait(Nat -> Unit);
}

public fn f(@Int -> @Unit)
  requires(true)
  ensures(true)
  effects(<E>)
{
  E.wait(@Int.0)
}
""", "may be negative")

    def test_user_effect_op_argument_narrowing_discharged(self) -> None:
        """The user-effect-op narrowing verifies cleanly when the argument
        is constrained non-negative — the discharged companion to
        test_user_effect_op_argument_narrowing_caught.  Asserts the
        `nat_bind` obligation actually fired and verified, not merely "no
        error" (CodeRabbit, PR #748)."""
        result = _verify("""
effect E {
  op wait(Nat -> Unit);
}

public fn f(@Int -> @Unit)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(<E>)
{
  E.wait(@Int.0)
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]


class TestGenericCloneInstantiatedTypes:
    """Generic-clone verification must see INSTANTIATED types, not the
    generic registration (PR #972 review; pre-existing on main).

    A generic's instances are verified by monomorphizing a clone and running
    it through the normal path (`_verify_generic_instances`).  The clone's
    AST nodes keep their SOURCE spans (diagnostics anchor at the generic),
    so the #747 span-keyed side-table (`_resolved_type_of` /
    `_target_type_of`) returns the GENERIC type — `Option<T>`, not the
    instance's `Option<Nat>`.  The sub-pattern narrowing walk then saw a
    `TypeVar` field under a `@Nat` binder and obligated an IMPOSSIBLE
    narrowing: `is_some_g<Nat>` matching `Some(@T)` on `@Option<T>.0` E503'd
    with counterexample `Some(-1)` even though `Option<Nat>` cannot hold a
    negative.  The fix substitutes the instance's concrete types into every
    side-table lookup while a clone is being verified.
    """

    def test_generic_subpattern_nat_instance_not_obligated(self) -> None:
        """`is_some_g<Nat>`: the clone's `Some(@Nat)` bind over an
        `Option<Nat>` scrutinee is NOT a narrowing — the payload is already
        @Nat, so no obligation may fire (the accessor carries no `>= 0`
        fact, so a spurious obligation manufactures the impossible
        counterexample `Some(-1)`)."""
        result = _verify("""
private forall<T> fn is_some_g(@Option<T> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<T>.0 {
    None -> false,
    Some(@T) -> true
  }
}

public fn main(@Nat -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Nat> = Some(@Nat.0);
  is_some_g(@Option<Nat>.0)
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert not [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]

    def test_generic_clone_genuine_subpattern_narrowing_still_obligated(
        self,
    ) -> None:
        """Control: a GENUINE `Some(@Nat)` narrowing over a concrete
        `Option<Int>` scrutinee inside a generic function's clone still
        E503s — the instance-substitution fix must scope to the
        impossible-counterexample case (already-@Nat instantiated field),
        never weaken the E503 machinery on the clone path."""
        _verify_err("""
private forall<T> fn first_nat_g(@Option<Int>, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    None -> 0,
    Some(@Nat) -> @Nat.0
  }
}

public fn main(@Option<Int> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  first_nat_g(@Option<Int>.0, true)
}
""", "may be negative")

    def test_generic_subpattern_int_instance_not_obligated(self) -> None:
        """`is_some_g<Int>`: the clone binds `Some(@Int)` — an @Int target
        is no narrowing at all, so the Int instance stays clean too (pins
        the substitution is per-instance, not a Nat special case)."""
        result = _verify("""
private forall<T> fn is_some_g(@Option<T> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<T>.0 {
    None -> false,
    Some(@T) -> true
  }
}

public fn main(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Int> = Some(@Int.0);
  is_some_g(@Option<Int>.0)
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert not [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]


# =====================================================================
# @Nat narrowing at the RETURN position (#758)
# =====================================================================

class TestNatReturnObligation758:
    """A function whose declared return is `@Nat` but whose body tail
    narrows an `@Int` value must prove `result >= 0` at the return slot —
    the return-position analogue of the #552 let/call-arg narrowing and the
    dual of #813's `@Nat -> @Int` widen-return obligation (7d/7c).

    Pre-fix (issue #758): `to_nat(@Int -> @Nat) { @Int.0 }` verified clean —
    no `nat_bind` obligation at the return slot — yet `to_nat(0 - 5)` returned
    -5 through the `@Nat` slot at runtime.  `vera verify`-clean was not a
    "no negative @Nat" guarantee at the return position.
    """

    def test_bare_slot_return_narrow_unguarded_fails(self) -> None:
        """`{ @Int.0 }` into a `@Nat` return is an unconstrained narrowing —
        Z3 witnesses `@Int.0 = -1`, so a loud E503 (mirrors the let site)."""
        _verify_err("""
public fn to_nat(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
""", "may be negative")

    def test_literal_subtraction_return_fails(self) -> None:
        """`{ 0 - 5 }` is provably negative at the `@Nat` return — E503."""
        _verify_err("""
public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ 0 - 5 }
""", "may be negative")

    def test_match_tail_return_narrow_fails(self) -> None:
        """A match whose `_` arm returns the raw `@Int` scrutinee into the
        `@Nat` return is a narrowing — the arm value can be negative (E503)."""
        _verify_err("""
public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ match @Int.0 { 0 -> 0, _ -> @Int.0 } }
""", "may be negative")

    def test_return_narrow_requires_discharges(self) -> None:
        """An explicit `requires(@Int.0 >= 0)` discharges the return narrowing
        at Tier 1 — the obligation fires and verifies (not merely silent)."""
        result = _verify("""
public fn to_nat(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]

    def test_abs_if_tail_discharges_per_branch(self) -> None:
        """The canonical absolute-value shape: `if @Int.0 >= 0 then @Int.0
        else 0 - @Int.0`.  The whole-if term encodes the per-arm path
        condition (`ite`), so the return `>= 0` obligation proves at Tier 1 —
        this is what keeps `examples/absolute_value.vera` Tier-1-provable
        under the new obligation."""
        result = _verify("""
public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ if @Int.0 >= 0 then { @Int.0 } else { 0 - @Int.0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]

    def test_nat_return_of_nat_body_not_flagged(self) -> None:
        """`@Nat -> @Nat` returning a `@Nat` slot is not a narrowing — no
        obligation (guards against a walker firing on every `@Nat` return)."""
        result = _verify("""
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert not [o for o in result.obligations if o.kind == "nat_bind"]

    def test_int_return_of_int_body_not_flagged(self) -> None:
        """Control: an `@Int -> @Int` return is not a narrowing (nor a
        widening), so no `nat_bind` obligation at the return."""
        result = _verify("""
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"]

    def test_untranslatable_builtin_return_is_tier3_guarded(self) -> None:
        """`array_length(...)` returns `@Int` (registry), so returning it into a
        `@Nat` slot is a narrowing.  Over an opaque (let-bound) array the value
        is untranslatable to Z3, so it is an honest Tier-3 narrowing (a codegen
        runtime guard backs it) — never a silent Tier-1 pass, and never a loud
        E503 (not provably negative).  This is the return-position analogue of
        the untranslatable let-site narrowing and the shape that makes
        `examples/nested_closures.vera` gain a Tier-3."""
        result = _verify("""
public fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = array_range(0, 2);
  array_length(@Array<Int>.0)
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["tier3"]


# =====================================================================
# @Nat component of a partially-generic ctor argument (#1010)
# =====================================================================

class TestGenericCtorParamNatObligation1010:
    """#1010: the E503 narrowing obligation was lost when a constructor
    argument's parameter type contains a type variable — the argument loop's
    re-synth and target recording were gated all-or-nothing on the whole
    parameter containing a typevar, so the concrete `Nat` component of
    `Pair<Nat, T>` never obligated and a provably-negative value verified
    clean and silently stored.  Found by the PR #1009 review."""

    _PAIR = """
private data Pair<A, B> { MkPair(A, B) }

private forall<T> fn wants(@Pair<Nat, T> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  0
}
"""

    def test_generic_ctor_param_negative_nat_component_e503(self) -> None:
        """Provably-negative into the concrete Nat component of a
        partially-generic param is a loud E503 (was verify-clean)."""
        errs = _verify_err(self._PAIR + """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  wants(MkPair(0 - 5, None))
}
""", "narrowing into a @Nat constructor field")
        assert any(e.error_code == "E503" for e in errs)

    def test_generic_ctor_param_opaque_int_component_obligated(self) -> None:
        """An unconstrained @Int param into the Nat component obligates and
        is E503 (the `requires(true)` domain admits negatives) — exactly the
        concrete path's verdict; was silent verify-clean."""
        errs = _verify_err(self._PAIR + """
public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  wants(MkPair(@Int.0, None))
}
""", "narrowing into a @Nat constructor field")
        assert any(e.error_code == "E503" for e in errs)

    def test_generic_ctor_param_proved_int_component_tier1(self) -> None:
        """The same shape under `requires(@Int.0 >= 0)` discharges Tier-1 —
        the obligation is present AND statically proved (`verified`, not a
        Tier-3 runtime fallback, which mere error-absence could not
        distinguish)."""
        result = _verify(self._PAIR + """
public fn main(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{
  wants(MkPair(@Int.0, None))
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]

    def test_generic_ctor_param_nat_component_ok(self) -> None:
        """A genuine Nat into the component verifies clean — no false E503
        from the new re-synth."""
        _verify_ok(self._PAIR + """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  wants(MkPair(5, None))
}
""")

    def test_concrete_ctor_param_negative_nat_component_e503(self) -> None:
        """Control: the fully-concrete analogue already obligates — pins
        that the generic fix reuses the same path, not a parallel one."""
        errs = _verify_err("""
private data Pair<A, B> { MkPair(A, B) }

private fn wants(@Pair<Nat, Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  wants(MkPair(0 - 5, 7))
}
""", "narrowing into a @Nat constructor field")
        assert any(e.error_code == "E503" for e in errs)
