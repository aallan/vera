"""Tests for vera.verifier — shadow_audits (per-monomorphization verification (#732) and the #680 shadow/projection audit battery).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations


from tests.verifier_helpers import (
    _MK,
    _nat_sub_status,
    _verify,
    _verify_err,
    _verify_ok,
)


class TestPerMonomorphizationVerification:
    """#732: instantiated generics are verified statically per monomorphization.

    Before #732 a generic body skipped SMT entirely — every non-trivial
    contract fell to Tier 3 (E520), a silent Tier-1 -> Tier-3 downgrade.  Now
    each concrete instantiation is verified through the normal path, so body
    obligations (a @Nat underflow, an `ensures`, a refined return) are actually
    discharged — or caught.
    """

    def test_body_nat_underflow_caught_per_instantiation(self) -> None:
        """An unguarded @Nat subtraction in a generic body — silently skipped
        (Tier-3 E520) before #732 — is now caught, naming the instantiation."""
        result = _verify("""
private forall<T>
fn dec(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn caller(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ dec(@Nat.1, @Nat.0, true) }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1, "expected exactly one underflow diagnostic"
        assert "instantiated at dec<Bool>" in errs[0].description
        assert "underflow" in errs[0].description
        violated = [o for o in result.obligations
                    if o.kind == "nat_sub" and o.status == "violated"]
        assert len(violated) == 1
        assert violated[0].fn_name == "dec"
        assert violated[0].counterexample is not None

    def test_body_nat_underflow_discharged_when_guarded(self) -> None:
        """The same body verifies statically (Tier 1) when a precondition
        guards it — the per-instance path PROVES, it does not merely reject."""
        result = _verify("""
private forall<T>
fn dec(@Nat, @Nat, @T -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn caller(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true)
  effects(pure)
{ dec(@Nat.1, @Nat.0, true) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert result.summary.tier3_runtime == 0
        # the body's nat_sub obligation is discharged statically for dec<Bool>
        assert any(o.kind == "nat_sub" and o.status == "verified"
                   for o in result.obligations)

    def test_never_instantiated_generic_stays_tier3(self) -> None:
        """A generic with no call site cannot be monomorphized, so its
        non-trivial contracts still fall to Tier 3 (E520) — the residual that
        #732 deliberately leaves untouched."""
        result = _verify("""
private forall<T>
fn unused(@T -> @T)
  requires(true)
  ensures(@T.result == @T.0)
  effects(pure)
{ @T.0 }
""")
        assert result.summary.tier3_runtime == 1
        e520 = [d for d in result.diagnostics if d.error_code == "E520"]
        assert len(e520) == 1
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_collapsed_type_vars_verify_correctly(self) -> None:
        """When two type vars collapse to the same concrete type (A=B=Int), the
        De Bruijn reindex must keep slot references consistent — the contract
        over the collapsed slots still discharges, with no false result."""
        result = _verify("""
private forall<A, B>
fn pick_first(@A, @B -> @A)
  requires(true)
  ensures(@A.result == @A.0)
  effects(pure)
{ @A.0 }

private fn use_same(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.1)
  effects(pure)
{ pick_first(@Int.1, @Int.0) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        # pick_first<Int, Int>'s ensures discharges statically.
        assert any(o.fn_name == "pick_first" and o.kind == "ensures"
                   and o.status == "verified" for o in result.obligations)

    def test_one_diagnostic_dedups_across_instantiations(self) -> None:
        """A body bug reachable in several instantiations surfaces ONCE (deduped
        to the source span), naming each offending instantiation — not N times."""
        result = _verify("""
private forall<T>
fn dec(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn use_bool(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ dec(@Nat.1, @Nat.0, true) }

private fn use_int(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ dec(@Nat.1, @Nat.0, 7) }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1, "one diagnostic per source site, not per instance"
        assert "dec<Bool>" in errs[0].description
        assert "dec<Int>" in errs[0].description
        # exactly one violated nat_sub obligation, not one per instantiation
        violated = [o for o in result.obligations
                    if o.kind == "nat_sub" and o.status == "violated"]
        assert len(violated) == 1

    def test_body_ensures_violation_caught_per_instantiation(self) -> None:
        """A generic body that violates its own `ensures` is caught per
        instantiation (E500), naming the instantiation.  A violated
        postcondition records its obligation with no error_code while its
        diagnostic carries E500, so the aggregation must correlate by
        (severity, span) — not error code — or it silently drops the violation
        (a false Tier-1).  Regression for the PR #767 review."""
        result = _verify("""
private forall<T>
fn bad_id(@Int, @T -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 + 1 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ bad_id(@Int.0, true) }
""")
        errs = [d for d in result.diagnostics
                if d.severity == "error" and d.error_code == "E500"]
        assert len(errs) == 1
        assert "instantiated at bad_id<Bool>" in errs[0].description
        violated = [o for o in result.obligations
                    if o.kind == "ensures" and o.status == "violated"]
        assert len(violated) == 1
        assert violated[0].fn_name == "bad_id"

    def test_body_bug_in_transitively_reached_generic_caught(self) -> None:
        """A body bug in a generic reached only transitively (through another
        generic's body) is verified and caught — discovery AND verification
        both follow the transitive worklist, not just discovery."""
        result = _verify("""
private forall<T>
fn inner(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private forall<T>
fn outer(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ inner(@Nat.1, @Nat.0, @T.0) }

private fn caller(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ outer(@Nat.1, @Nat.0, true) }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1
        assert "instantiated at inner<Bool>" in errs[0].description

    def test_generic_in_arraylit_is_discovered_and_verified(self) -> None:
        """The discovery walk is TOTAL over Expr, so a generic reachable only
        from inside an `ArrayLit` (a form the old explicit-arm walk skipped) is
        discovered and verified — its body @Nat underflow is caught, not missed
        into the Tier-3 fallback."""
        result = _verify("""
private forall<T>
fn dec(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn caller(@Nat, @Nat -> @Array<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ [dec(@Nat.1, @Nat.0, true)] }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1
        assert "instantiated at dec<Bool>" in errs[0].description

    def test_generic_in_contract_clause_is_verified(self) -> None:
        """A generic reachable only from a contract predicate (here an `ensures`)
        is discovered and verified — discovery walks contract clauses, not just
        the body and where-helpers — so its body bug is caught."""
        result = _verify("""
private forall<T>
fn bad_dec(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn checker(@Nat, @Nat -> @Bool)
  requires(true)
  ensures(bad_dec(@Nat.1, @Nat.0, true) >= 0)
  effects(pure)
{ true }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1
        assert "instantiated at bad_dec<Bool>" in errs[0].description

    def test_generic_reached_only_via_decreases_is_verified(self) -> None:
        """A generic reachable only from a `decreases(...)` measure is discovered
        and verified.  Decreases is the one Contract subclass that holds its
        predicates in `.exprs` (a tuple) rather than `.expr`, so a contract walk
        reading only `.expr` silently skipped it (PR #767 review) — degrading
        such a generic to the E520 Tier-3 fallback and missing its body bug.  The
        first lexicographic component (`@Nat.0`) carries termination; the second
        only has to be discovered."""
        result = _verify("""
private forall<T>
fn bad_measure(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn countdown(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0, bad_measure(@Nat.0, 0, true))
  effects(pure)
{ if @Nat.0 == 0 then { 0 } else { countdown(@Nat.0 - 1) } }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1
        assert "instantiated at bad_measure<Bool>" in errs[0].description

    def test_typevar_contract_aggregates_across_instantiations(self) -> None:
        """A generic whose contract references @T renders different expr_text per
        instantiation; the meet must group by SOURCE SITE so it stays ONE
        obligation, not one per instantiation (else summaries over-count) — from
        the PR #767 review."""
        result = _verify("""
private forall<T>
fn idc(@T -> @T)
  requires(true)
  ensures(@T.result == @T.0)
  effects(pure)
{ @T.0 }

private fn use2(@Int, @Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = idc(@Int.0);
  let @Bool = idc(@Bool.0);
  @Int.0
}
""")
        ens = [o for o in result.obligations
               if o.fn_name == "idc" and o.kind == "ensures"]
        assert len(ens) == 1, "one obligation per source site, not per instance"
        assert ens[0].status == "verified"
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_aggregated_tier3_label_includes_timeout_instances(self) -> None:
        """A mixed tier3/timeout Tier-3 aggregate must list BOTH instantiations
        in the diagnostic prefix.  ``_meet_status`` folds ``timeout`` into
        ``tier3``, so the instantiation-label filter must group them together;
        an exact status-match drops the ``timeout`` instance from the prefix
        (PR #767 review).  Synthesised directly because a real Z3 timeout is
        non-deterministic and cannot be pinned through the normal pipeline."""
        from types import SimpleNamespace

        from vera.errors import Diagnostic, SourceLocation
        from vera.obligations.core import ProofObligation
        from vera.verifier import ContractVerifier

        v = ContractVerifier(source="", file="t.vera")
        decl = SimpleNamespace(name="g")
        ob_t3 = ProofObligation(
            fn_name="g", kind="ensures", expr_text="p", status="tier3",
            line=3, column=5, error_code="E506",
        )
        ob_to = ProofObligation(
            fn_name="g", kind="ensures", expr_text="p", status="timeout",
            line=3, column=5, error_code="E506",
        )
        members = [(("Int",), ob_t3), (("Float64",), ob_to)]
        src = Diagnostic(
            description="runtime check deferred",
            location=SourceLocation(file="t.vera", line=3, column=5),
            severity="warning", error_code="E506", tier=None,
        )
        errs = {("Int",): [src]}
        v._emit_aggregated_diagnostic(
            decl, members, ("Int",), ob_t3, errs,  # type: ignore[arg-type]
        )

        assert v.errors, "expected an aggregated Tier-3 diagnostic"
        desc = v.errors[-1].description
        assert "g<Int>" in desc and "g<Float64>" in desc, (
            f"both the tier3 and the timeout instance must appear: {desc}"
        )

    def test_recursive_generic_clone_keeps_source_name_for_decreases(self) -> None:
        """A recursive generic's clone must keep the SOURCE name so the verifier
        recognizes its recursive call and obligates `decreases`.

        `monomorphize_fn` mangles the clone name (for codegen WAT symbols), but
        `_verify_generic_instances` renames it back to `decl.name` ("keep the
        source name").  Recursion/`decreases` resolution is purely by name
        (`_collect_recursive_calls` matches `FnCall.name`), so without that
        rename the clone `countdown$Int` whose body still calls `countdown`
        would have NO recognized recursive call → no `decreases` obligation → a
        terminating function's measure silently unchecked.  Pin that the
        obligation is present and verified — identical to the non-generic twin
        — which refutes the "mangled clone breaks recursion" claim (PR #767
        review) and fails loudly if the source-name rename is ever removed."""
        result = _verify("""
private forall<T> fn countdown(@T, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{ if @Nat.0 == 0 then { 0 } else { countdown(@T.0, @Nat.0 - 1) } }

private fn driver(@Int, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ countdown(@Int.0, @Nat.0) }
""")
        decr = [o for o in result.obligations
                if o.fn_name == "countdown" and o.kind == "decreases"]
        assert len(decr) == 1, (
            "the recursive generic clone must obligate `decreases` (recursion "
            f"recognized via the source-name clone); got {decr}"
        )
        assert decr[0].status == "verified"
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_generic_reached_only_via_where_helper_is_verified(self) -> None:
        """A generic reachable solely through a `where` helper is discovered and
        verified — its body bug is caught — not missed into the uninstantiated
        Tier-3 fallback (the PR #767 review)."""
        result = _verify("""
private forall<T>
fn inner(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn caller(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ helper(@Nat.1, @Nat.0) }
where {
  fn helper(@Nat, @Nat -> @Nat)
    requires(true)
    ensures(true)
    effects(pure)
  { inner(@Nat.1, @Nat.0, true) }
}
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1
        assert "instantiated at inner<Bool>" in errs[0].description


class TestShadowAuditDivision680:
    def test_compound_mult_shadow_divisor_is_tier3(self) -> None:
        """`2 * shadow` divisor (opaque shadow inside a multiplication) stays
        Tier-3 — never a false E526 AND never silently discharged.  The `let`
        shadows a guarded `requires(@Int.0 != 0)` outer, so a lost shadow would
        verify `2 * @Int.0 != 0` against the stale `!= 0`; the *tracked* shadow
        forces `_contains_opaque_shadow` to route it to Tier-3.  (Breaking the
        `*`-operand recursion flips this to a false E526 — mutation-checked.)"""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / (2 * @Int.0) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_product_of_two_shadow_terms_is_tier3(self) -> None:
        """A divisor that is a product of two shadow-bearing subexpressions
        `(shadow + 1) * (shadow + 2)` stays Tier-3: the opaque-shadow walk must
        descend into BOTH operands of the `*`, not just the leftmost.  The `let`
        shadows a guarded `requires(@Int.0 != 0)` outer — a lost shadow would
        silently discharge against the stale `!= 0` (mutation-checked)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / ((@Int.0 + 1) * (@Int.0 + 2)) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_self_subtraction_of_shadow_is_provably_zero_e526(self) -> None:
        """`shadow - shadow` as a divisor is a loud E526 — the compound-shadow
        guard must NOT over-mask a *provably*-zero divisor just because it
        embeds a shadow.  Even with a tracked shadow `s`, `s - s` simplifies to
        0 for every value, so `divisor == 0` is valid and the guard correctly
        falls through to E526 (the `let` shadows a guarded `requires(@Int.0 !=
        0)` outer, so this is the genuine-zero half of the differential, not a
        stale-outer leak).  A `tier3` here would be the guard wrongly masking a
        decidable divide-by-zero — mutation-checked against an over-eager
        guard."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / (@Int.0 - @Int.0) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [e.error_code for e in errors] == ["E526"], [
            e.error_code for e in errors
        ]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "violated", [
            (o.kind, o.status) for o in divs
        ]

    def test_modulo_compound_shadow_divisor_is_tier3(self) -> None:
        """Modulo mirrors division on the compound-shadow path: `1 % (shadow + 1)`
        is Tier-3, never a false E526.  Pins `%` to the same
        `_contains_opaque_shadow` treatment as `/`.  The `let` shadows a guarded
        `requires(@Int.0 != 0)` outer — a lost shadow would silently discharge
        the modulo against the stale `!= 0` (mutation-checked)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 % (@Int.0 + 1) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_modulo_opaque_let_divisor_is_tier3(self) -> None:
        """A direct opaque-let modulo divisor `1 % shadow` is Tier-3 — the `%`
        obligation is recorded under the same `div_zero` kind as `/` and is not
        silently dropped.  The `let` shadows a guarded `requires(@Int.0 != 0)`
        outer, so a lost (untracked) shadow would discharge `@Int.0 != 0`
        against the stale `!= 0` — `_is_opaque_shadow` keeps it Tier-3
        (mutation-checked: turning it off flips this to a false E526)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 % @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_mixed_destructure_divisor_by_literal_component_discharges(self) -> None:
        """In `Tuple(10, random_int(...))` the FIRST component is a translatable
        literal: dividing by it (`@Int.1`, the prior De Bruijn slot) discharges
        `10 != 0` at Tier-1 even though the SECOND component is opaque.  The
        literal projection must survive an opaque sibling in the same tuple."""
        result = _verify("""
private fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10)); 1 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [
            (o.kind, o.status) for o in divs
        ]

    def test_mixed_destructure_divisor_by_opaque_component_stays_tier3(self) -> None:
        """The De Bruijn-collapse trap: in `Tuple(10, random_int(...))` dividing
        by `@Int.0` (most-recent slot = the OPAQUE second component) must stay
        Tier-3.  If the opaque component were skipped instead of pushed, `@Int.0`
        would collapse onto the literal `10` and falsely discharge — the worst
        #680 failure class (silent false-discharge)."""
        result = _verify("""
private fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10)); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_outer_requires_does_not_discharge_shadowing_opaque_let(self) -> None:
        """The canonical silent-failure differential: an opaque `let @Int =
        random_int(...)` shadows an outer `@Int` param guarded by
        `requires(@Int.0 != 0)`.  Dividing by `@Int.0` now refers to the
        *shadow* (which can be 0), so it must be Tier-3, NOT verified against
        the stale outer guard.  A `verified` here is a SILENT_FAILURE."""
        result = _verify("""
public fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_divisor_is_outer_param_after_opaque_let_discharges(self) -> None:
        """The complement of the shadow trap: after an opaque `let @Int` shadows
        the param, the ORIGINAL guarded param is reachable as `@Int.1` (prior
        slot).  Dividing by `@Int.1` discharges the outer `requires(@Int.0 != 0)`
        at Tier-1 — the shadow must not poison the still-visible outer slot, and
        De Bruijn must address the correct one."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [
            (o.kind, o.status) for o in divs
        ]

    def test_two_opaque_lets_divide_by_each_keep_debruijn(self) -> None:
        """Two same-type opaque lets each occupy a distinct De Bruijn slot, and
        both shadow the guarded `requires(@Int.0 != 0)` outer.  The divisor
        `@Int.1` (the FIRST, prior let) is a tracked shadow → Tier-3; a lost
        shadow would resolve `@Int.1` to the guarded param and silently
        discharge.  Pins that the prior-slot divisor stays tracked (not
        collapsed onto the most-recent let or leaked to the param)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(1, 10); let @Int = random_int(0, 10); @Int.0 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_two_ops_reuse_same_shadow_both_tier3(self) -> None:
        """A shadow stays opaque across MULTIPLE ops in the same body.  Both
        `1 / @Int.0` and `2 / @Int.0` over one opaque `let @Int` (shadowing a
        guarded `requires(@Int.0 != 0)` outer) each record a Tier-3 `div_zero`
        obligation — the first op must not "consume" the shadow and leave the
        second silently discharged against the stale `!= 0`."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); (1 / @Int.0) + (2 / @Int.0) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 2 and all(d.status == "tier3" for d in divs), [
            (o.kind, o.status) for o in divs
        ]

    def test_opaque_match_arm_divisor_does_not_use_stale_outer_guard(self) -> None:
        """Match-arm binding over an UNTRANSLATABLE scrutinee (effect op) shadows
        its pattern slot, so `1 / @Int.0` in the arm is Tier-3 even though an
        outer `@Int` param carries `requires(@Int.0 != 0)`.  The matched field
        can be 0; discharging against the outer guard would be a silent
        false-discharge."""
        result = _verify("""
effect Source {
  op next(Unit -> Option<Int>);
}

private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Source>)
{ match Source.next(()) { Some(@Int) -> 1 / @Int.0, None -> 1 } }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]


class TestShadowAuditSubtraction680:
    """Soundness battery for the `nat_sub` (#520, E502) underflow obligation
    under the shadow/projection machinery.

    Invariant trichotomy:
      * provably non-underflowing  -> 'verified' (Tier-1)
      * an opaque operand (direct OR embedded in a compound) for which the
        obligation is genuinely undecidable -> 'tier3' (runtime guard);
        MUST NOT be 'verified' (silent failure) NOR 'violated' (false E502)
      * provably underflowing for *every* runtime value -> 'violated' (E502)
    """

    def test_opaque_direct_operand_is_tier3(self) -> None:
        """A direct opaque shadow operand (`@Nat.0 - 1` after a non-literal
        destructure) is undecidable -> Tier-3, never a false E502."""
        st = _nat_sub_status(_MK + """
private fn d(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); @Nat.0 - 1 }
""")
        assert st == ["tier3"], st

    def test_opaque_both_compound_undecidable_is_tier3(self) -> None:
        """Both operands compound over *different* opaque shadows
        (`(@Nat.0 + 1) - (@Nat.1 + 1)`): neither a direct shadow, and
        `lhs >= rhs` / `lhs < rhs` both undecidable, so the recursive
        `_contains_opaque_shadow` guard routes to Tier-3, not E502."""
        st = _nat_sub_status(_MK + """
private fn c(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); (@Nat.0 + 1) - (@Nat.1 + 1) }
""")
        assert st == ["tier3"], st

    def test_opaque_compound_minus_direct_is_tier3(self) -> None:
        """Asymmetric compound/direct over different opaque shadows
        (`(@Nat.0 + 1) - @Nat.1`) is undecidable -> Tier-3."""
        st = _nat_sub_status(_MK + """
private fn c(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); (@Nat.0 + 1) - @Nat.1 }
""")
        assert st == ["tier3"], st

    def test_opaque_scaled_compound_undecidable_is_tier3(self) -> None:
        """Scaled compound over different opaque shadows
        (`(2 * @Nat.0) - (@Nat.1 + 5)`) is undecidable -> Tier-3."""
        st = _nat_sub_status(_MK + """
private fn c(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); (2 * @Nat.0) - (@Nat.1 + 5) }
""")
        assert st == ["tier3"], st

    def test_opaque_match_bound_operand_is_tier3(self) -> None:
        """A @Nat bound by matching `Some(@Nat)` over an opaque effect-op
        scrutinee (`Src.g(()) : Option<Nat>`) is opaque; `@Nat.0 - 1` in the
        arm is undecidable -> Tier-3, never a false E502."""
        st = _nat_sub_status("""
effect Src { op g(Unit -> Option<Nat>); }

private fn m(@Nat -> @Nat)
  requires(true) ensures(true) effects(<Src>)
{ match Src.g(()) { Some(@Nat) -> @Nat.0 - 1, None -> 0 } }
""")
        assert st == ["tier3"], st

    def test_param_requires_does_not_leak_to_shadow(self) -> None:
        """SILENT-FAILURE guard: a `requires(@Nat.0 >= 100)` constraining the
        *parameter* must NOT discharge an obligation whose operands are the
        independent destructured shadows -- the param is shadowed out of
        scope at the subtraction site, so it stays Tier-3 (not falsely
        'verified')."""
        st = _nat_sub_status(_MK + """
private fn leak(@Nat -> @Nat)
  requires(@Nat.0 >= 100)
  ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); @Nat.0 - @Nat.1 }
""")
        assert st == ["tier3"], st

    def test_effect_op_nat_operands_are_tier3(self) -> None:
        """Two @Nat values produced by an effect op (`Rng.rand()`), let-bound
        and subtracted, are opaque -> Tier-3."""
        st = _nat_sub_status("""
effect Rng { op rand(Unit -> Nat); }

private fn e(@Unit -> @Nat)
  requires(true) ensures(true) effects(<Rng>)
{ let @Nat = Rng.rand(()); let @Nat = Rng.rand(()); @Nat.0 - @Nat.1 }
""")
        assert st == ["tier3"], st

    def test_compound_shadow_provably_safe_is_verified(self) -> None:
        """When the opaque shadow CANCELS so the obligation is decidable and
        true (`(@Nat.0 + 2) - (@Nat.0 + 1) == 1 >= 0` for all values), the
        compound-shadow Tier-3 fallback is correctly suppressed (its guard
        requires `lhs < rhs` to be non-valid) -> 'verified', not Tier-3.
        Pins that the fallback does not over-fire into a silent under-check."""
        st = _nat_sub_status(_MK + """
private fn safe(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); (@Nat.0 + 2) - (@Nat.0 + 1) }
""")
        assert st == ["verified"], st

    def test_compound_shadow_provably_underflow_is_violated(self) -> None:
        """When the opaque shadow CANCELS so underflow holds for *every*
        runtime value (`(@Nat.0 + 1) - (@Nat.0 + 2) == -1` for all values),
        this is a genuine bug -> loud 'violated'/E502, NOT a Tier-3 mask.
        Distinguishes 'undecidable-because-opaque' (Tier-3) from
        'decidably-underflows-regardless-of-opaque' (E502)."""
        r = _verify(_MK + """
private fn bad(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); (@Nat.0 + 1) - (@Nat.0 + 2) }
""")
        subs = [o.status for o in r.obligations if o.kind == "nat_sub"]
        assert subs == ["violated"], subs
        codes = [d.error_code for d in r.diagnostics if d.severity == "error"]
        assert "E502" in codes, codes

    def test_requires_ge_discharges_to_verified(self) -> None:
        """Baseline (no shadow): explicit `requires(@Nat.0 >= @Nat.1)` on the
        actual subtraction operands -> 'verified'."""
        st = _nat_sub_status("""
private fn safe(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true) effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        assert st == ["verified"], st


class TestShadowAuditIndex680:
    """Soundness battery for the `index_bounds` (#680/E527) obligation under the
    shadow/projection machinery: in-bounds -> verified, provably-OOB ->
    violated, opaque length/index -> honest Tier-3 (never silent, never a false
    E527).  Array length is an uninterpreted SMT function (#427)."""

    def test_index_lower_edge_literal_discharges(self) -> None:
        """`[1, 2, 3][0]` — index 0 is the in-bounds lower edge -> Tier 1.
        Pins the `0 <= i` conjunct's *inclusive* lower edge."""
        result = _verify("""
private fn first(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ [1, 2, 3][0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "verified", [
            (o.kind, o.status) for o in idx
        ]

    def test_index_equals_opaque_length_is_violated(self) -> None:
        """`arr[array_length(arr)]` is out of bounds for ANY length, even an
        uninterpreted one: `i == length` makes `i >= length` tautologically
        valid -> loud E527 (not a silent drop on a non-numeric length)."""
        matched = _verify_err("""
private fn at_len(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[array_length(@Array<Int>.0)] }
""", "out of bounds")
        assert matched[0].error_code == "E527", matched[0].error_code

    def test_index_last_elem_opaque_length_is_tier3(self) -> None:
        """`arr[array_length(arr) - 1]` is in bounds iff `length > 0`, unknown
        for an opaque length -> honest Tier 3, never a false E527."""
        result = _verify("""
private fn last(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[array_length(@Array<Int>.0) - 1] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_unguarded_nat_index_into_literal_is_tier3_not_violated(self) -> None:
        """`[1, 2, 3][@Nat.0]` with an unconstrained `@Nat` — could be in range
        (0/1/2) so NOT provably OOB (no false E527), but could be >= 3 so not
        provably in bounds -> honest Tier 3."""
        result = _verify("""
private fn at(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ [1, 2, 3][@Nat.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_precondition_guards_wrong_array_stays_tier3(self) -> None:
        """A precondition bounding a DIFFERENT array than the one indexed must
        not discharge.  `requires(@Nat.0 < array_length(@Array<Int>.1))` but
        body indexes `@Array<Int>.0` -> Tier 3, never a silent 'verified'
        against an unrelated array's length (De Bruijn discrimination)."""
        result = _verify("""
private fn at(@Array<Int>, @Array<Int>, @Nat -> @Int)
  requires(@Nat.0 < array_length(@Array<Int>.1))
  ensures(true) effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_precondition_guards_wrong_nat_index_stays_tier3(self) -> None:
        """A precondition bounding a DIFFERENT index var than the one used must
        not discharge.  Two `@Nat` params, `requires(@Nat.1 < array_length(arr))`
        but body indexes `@Nat.0` -> Tier 3 (the indexed var carries no upper
        bound)."""
        result = _verify("""
private fn at(@Array<Int>, @Nat, @Nat -> @Int)
  requires(@Nat.1 < array_length(@Array<Int>.0))
  ensures(true) effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_reassign_to_longer_literal_uses_current_length(self) -> None:
        """Re-binding to a LONGER literal then indexing past the OLD length is
        valid against the CURRENT one.  `let a = [1,2]; let a = [1,2,3,4,5];
        a[4]` -> Tier 1 (4 < 5), reading the current binding's length."""
        result = _verify("""
private fn grow(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [1, 2]; let @Array<Int> = [1, 2, 3, 4, 5]; @Array<Int>.0[4] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "verified", [
            (o.kind, o.status) for o in idx
        ]

    def test_reassign_to_shorter_literal_violates_current_length(self) -> None:
        """Re-binding to a SHORTER literal then indexing past the NEW length is
        provably OOB.  `let a = [1,2,3,4,5]; let a = [1,2]; a[4]` -> E527
        (4 >= 2), checking the shadowing binding's shorter length."""
        matched = _verify_err("""
private fn shrink(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [1, 2, 3, 4, 5]; let @Array<Int> = [1, 2]; @Array<Int>.0[4] }
""", "out of bounds")
        assert matched[0].error_code == "E527", matched[0].error_code

    def test_append_then_low_index_is_tier3_not_verified(self) -> None:
        """`let a = [1,2,3]; let a = array_append(a, 9); a[0]` — a[0] IS valid,
        but the appended length is OPAQUE, so the verifier cannot PROVE in
        bounds -> Tier 3.  A 'verified' would claim a Tier-1 proof the opaque
        length can't support (silent over-claim)."""
        result = _verify("""
private fn appended(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [1, 2, 3]; let @Array<Int> = array_append(@Array<Int>.0, 9); @Array<Int>.0[0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_opaque_shadow_index_does_not_leak_outer_bound(self) -> None:
        """An index `let`-shadowing a guarded index param must be Tier-3, NOT
        silently verified against the stale outer bound.  The param carries
        `0 <= @Int.0 && @Int.0 < array_length(...)`; after `let @Int =
        random_int(...)`, `@Int.0` is the (unbounded) shadow, so the bounds are
        indeterminate → Tier 3.  A lost shadow would resolve `@Int.0` to the
        guarded param and falsely *verify* (silent failure) — the differential:
        the same body WITHOUT the `let` verifies at Tier 1, with it falls to
        Tier 3 (mutation-checked against the scalar `let`-shadow push)."""
        result = _verify("""
private fn idx(@Array<Int>, @Int -> @Int)
  requires(0 <= @Int.0 && @Int.0 < array_length(@Array<Int>.0))
  ensures(true) effects(<Random>)
{ let @Int = random_int(0, 5); @Array<Int>.0[@Int.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_literal_constructor_tuple_destructure_projects_lengths(self) -> None:
        """A LITERAL-constructor tuple destructure projects each component's
        length; De Bruijn indexes the right array.  `let Tuple<@Array, @Array>
        = Tuple([1,2,3], [9,9]); @Array<Int>.0[5]` -> `@Array<Int>.0` is the
        2nd component [9,9] (length 2), so [5] is OOB -> E527."""
        matched = _verify_err("""
private fn pick(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Array<Int>, @Array<Int>> = Tuple([1, 2, 3], [9, 9]); @Array<Int>.0[5] }
""", "out of bounds")
        assert matched[0].error_code == "E527", matched[0].error_code

    def test_call_sourced_tuple_destructure_array_is_tier3(self) -> None:
        """A tuple destructure whose source is a CALL cannot project, so each
        array slot shadows to an opaque array -> Tier 3, never a false E527
        against a stale same-type outer's length (the alignment trap)."""
        result = _verify("""
private fn mk(@Array<Int> -> @Tuple<Array<Int>, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(@Array<Int>.0, 0) }

private fn destr(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [1, 2, 3]; let Tuple<@Array<Int>, @Int> = mk(@Array<Int>.0); @Array<Int>.0[5] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_index_inside_quantifier_closure_not_obligated(self) -> None:
        """An index inside a `forall` quantifier closure body is NOT walked
        (captured length beyond Tier 1 without #427), so it records ZERO
        index_bounds obligations — left to the runtime trap (#779)."""
        result = _verify("""
private fn allpos(@Array<Int> -> @Bool)
  requires(true) ensures(true) effects(pure)
{ forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { @Array<Int>.1[5] == 0 }) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert idx == [], f"quantifier-body index must not be obligated, got {len(idx)}"


class TestDestructureDeBruijnAlignment680:
    """Every destructure binding occupies exactly its De Bruijn slot, and a
    trapping op reads the value actually at that slot — never a stale sibling,
    never a collapsed/shifted index (#680 review's `collapse` failure class).
    Values are chosen so reading the WRONG sibling flips the verdict."""

    def test_literal_destructure_divisor_order_pins_first_component(self) -> None:
        """`Tuple(10, 0)`: `@Int.1` = first (10), `@Int.0` = second (0).
        Dividing by `@Int.1` discharges `10 != 0` — a swap onto the `0` sibling
        would flip to a false E526."""
        result = _verify("""
private fn lit_order_first(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(10, 0); @Int.0 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [
            (o.kind, o.status) for o in divs
        ]

    def test_literal_destructure_divisor_order_pins_second_component(self) -> None:
        """`Tuple(10, 0)`: `@Int.0` = second (0) -> dividing by it is a provable
        E526.  Reading the `10` sibling would silently discharge a real zero."""
        _verify_err("""
private fn lit_order_second(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(10, 0); @Int.1 / @Int.0 }
""", "by zero")

    def test_mixed_literal_opaque_keeps_debruijn_no_collapse(self) -> None:
        """`Tuple(10, <opaque>)`: `@Int.0` = OPAQUE second component -> Tier 3,
        NOT shifted onto the literal `10`.  A skip would collapse `@Int.0` onto
        `10` and silently discharge (the worst #680 failure)."""
        result = _verify("""
private fn mixed_opaque_first(@Unit -> @Int)
  requires(true) ensures(true) effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10)); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_mixed_literal_opaque_literal_component_still_tier1(self) -> None:
        """`Tuple(10, <opaque>)`: the literal `@Int.1` (10) stays Tier 1 even
        with an opaque sibling — projection precision survives a mixed source."""
        result = _verify("""
private fn mixed_opaque_lit(@Unit -> @Int)
  requires(true) ensures(true) effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10)); 1 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [
            (o.kind, o.status) for o in divs
        ]

    def test_three_component_literal_each_index_reads_its_own(self) -> None:
        """`Tuple(10, 0, 7)`: `@Int.1` = middle (0 -> violated), `@Int.2` = first
        (7 -> safe).  Distinct values so any off-by-one flips a verdict."""
        _verify_err("""
private fn tri_middle(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int, @Int> = Tuple(10, 0, 7); 1 / @Int.1 }
""", "by zero")
        _verify_ok("""
private fn tri_last(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int, @Int> = Tuple(10, 0, 7); 1 / @Int.2 }
""")

    def test_intervening_different_type_does_not_shift_same_type_index(self) -> None:
        """`Tuple<@Int, @Nat, @Int> = Tuple(7, 99, 0)`: `@Int.0` skips the
        intervening `@Nat` to read the 3rd component (0 -> violated); `@Int.1`
        reads the first (7 -> safe).  Different types = different namespaces."""
        _verify_err("""
private fn interleaved_zero(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Nat, @Int> = Tuple(7, 99, 0); 1 / @Int.0 }
""", "by zero")
        _verify_ok("""
private fn interleaved_safe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Nat, @Int> = Tuple(7, 99, 0); 1 / @Int.1 }
""")

    def test_destructure_zero_shadows_guarded_outer_param(self) -> None:
        """A destructure binding `0` that shadows a `requires(@Int.0 != 0)`
        outer param makes `@Int.0` read the destructured `0` (violated), not
        the stale guarded outer."""
        _verify_err("""
public fn destr_shadows_guard(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(5, 0); 1 / @Int.0 }
""", "by zero")

    def test_opaque_destructure_component_not_discharged_by_outer_guard(self) -> None:
        """`requires(@Int.0 != 0)` then `let Tuple = Tuple(<opaque>, <opaque>)`:
        `@Int.0` = opaque -> Tier 3.  The outer `!= 0` must NOT leak through the
        shadow (silent-failure differential)."""
        result = _verify("""
public fn opaque_destr_guard(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(random_int(0, 10), random_int(0, 10)); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_stacked_destructures_deep_index_reaches_outer_first(self) -> None:
        """Two stacked literal destructures: `@Int.3` reaches PAST the inner two
        slots to the first component of the OUTER destructure.  Pins the 4-deep
        De Bruijn stack and stacked literal projection."""
        _verify_ok("""
private fn stacked_outer_safe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(3, 9); let Tuple<@Int, @Int> = Tuple(0, 5); 1 / @Int.3 }
""")
        _verify_err("""
private fn stacked_outer_zero(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(0, 9); let Tuple<@Int, @Int> = Tuple(7, 5); 1 / @Int.3 }
""", "by zero")

    def test_nat_subtraction_destructure_projection_is_order_sensitive(self) -> None:
        """Non-commutative `@Nat` subtraction through projection: `Tuple(3, 10)`.
        `@Nat.1 - @Nat.0` = 3 - 10 underflows (E502); `@Nat.0 - @Nat.1` = 10 - 3
        is safe.  Alignment is op-agnostic."""
        _verify_err("""
private fn sub_underflow(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = Tuple(3, 10); @Nat.1 - @Nat.0 }
""", "underflow")
        _verify_ok("""
private fn sub_safe(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = Tuple(3, 10); @Nat.0 - @Nat.1 }
""")

    def test_index_bounds_destructure_projection_reads_right_index(self) -> None:
        """`index_bounds` through projection: `Tuple(5, 1)` indexing `[10,20,30]`.
        `[..][@Int.0]` = `[..][1]` in bounds; `[..][@Int.1]` = `[..][5]` OOB
        (E527).  Alignment holds for the index op too."""
        _verify_ok("""
private fn idx_inbounds(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(5, 1); [10, 20, 30][@Int.0] }
""")
        _verify_err("""
private fn idx_oob(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(5, 1); [10, 20, 30][@Int.1] }
""", "bounds")

    def test_refinement_typed_component_projects_value_and_invariant(self) -> None:
        """A refinement-typed component keeps its own namespace AND invariant:
        `Tuple<@PosInt, @Int> = Tuple(3, 0)`.  `@Int.0` = literal 0 (violated);
        `@PosInt.0` = 3, discharges `3 > 0 => != 0` (verified)."""
        _verify_err("""
type PosInt = { @Int | @Int.0 > 0 };

private fn refined_zero_sibling(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@PosInt, @Int> = Tuple(3, 0); 1 / @Int.0 }
""", "by zero")
        _verify_ok("""
type PosInt = { @Int | @Int.0 > 0 };

private fn refined_posint_divisor(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@PosInt, @Int> = Tuple(3, 0); 1 / @PosInt.0 }
""")


class TestShadowAuditInteractions680:
    """Cross-construct shadow interactions: a `1 / shadow` (or `%` / `@Nat -`)
    embedded in array-literals, asserts, nested blocks, nested matches, and
    alongside independent shadows must stay Tier-3 (never silent, never false),
    and shadows must respect block scoping (#680 audit, interaction dimension)."""

    def test_shadow_div_inside_array_literal_is_tier3(self) -> None:
        """A `1 / shadow` inside an array-literal element is Tier-3 — the
        array-lit walker arm recurses into elements and the opaque-shadow guard
        applies one host-construct deep."""
        result = _verify("""
private fn f(@Int -> @Array<Int>)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{ let @Int = random_int(0, 10); [1 / @Int.0, 99] }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_shadow_div_inside_assert_is_tier3(self) -> None:
        """`assert(1 / shadow > 0)` over an opaque `random_int` shadow is
        Tier-3 — the Assert walker arm recurses into the condition."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{ let @Int = random_int(0, 10); assert(1 / @Int.0 > 0); 0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_let_value_is_opaque_match_then_divisor_is_tier3(self) -> None:
        """A `let @Int = match <opaque-scrutinee> {...}` value is opaque (the
        SMT layer returns None for a match over an effect op), so a later
        `1 / @Int.0` is Tier-3 even when both arms are non-zero literals (the
        arm taken is unknown)."""
        result = _verify("""
effect Src {
  op g(Unit -> Option<Int>);
}

private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Src>)
{ let @Int = match Src.g(()) { Some(@Int) -> 7, None -> 1 }; 1 / @Int.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_nested_opaque_match_divisor_is_tier3(self) -> None:
        """A divisor in a `match` nested inside another `match`, both over an
        opaque effect-op scrutinee, is Tier-3 — `_fresh_pattern_env` shadows the
        inner pattern slot through two arm levels, never discharging against the
        outer `requires(@Int.0 != 0)`."""
        result = _verify("""
effect Src {
  op g(Unit -> Option<Int>);
}

private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Src>)
{
  match Src.g(()) {
    Some(@Int) -> match Src.g(()) { Some(@Int) -> 1 / @Int.0, None -> 1 },
    None -> 1
  }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_independent_shadows_do_not_cross_contaminate(self) -> None:
        """Two independent opaque shadows — a `random_int` Int and a
        `random_nat` Nat — keep separate obligations: the `1 / @Int.0` div and
        the `@Nat.0 - @Nat.1` subtraction each fall to their own Tier-3,
        neither masking nor leaking onto the other."""
        result = _verify("""
private fn f(@Int, @Nat -> @Array<Int>)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{
  let @Int = random_int(0, 9);
  let @Nat = random_nat(0, 9);
  [1 / @Int.0, @Nat.0 - @Nat.1]
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]
        assert len(subs) == 1 and subs[0].status == "tier3", [(o.kind, o.status) for o in subs]

    def test_division_before_shadow_let_stays_tier1(self) -> None:
        """A division by the constrained param *before* an opaque shadow let is
        Tier-1; a division by the shadow *after* is Tier-3.  The shadow applies
        only from its binding point onward (intra-block scoping)."""
        result = _verify("""
private fn f(@Int -> @Array<Int>)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{
  let @Int = 1 / @Int.0;
  let @Int = random_int(0, 9);
  [@Int.1, 1 / @Int.0]
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        statuses = sorted(o.status for o in divs)
        assert statuses == ["tier3", "verified"], [(o.kind, o.status) for o in divs]

    def test_nested_block_shadow_does_not_leak_to_outer_divisor(self) -> None:
        """An opaque shadow bound inside a nested block does not bleed onto an
        outer divisor.  `let @Int = { let @Int = random_int(...); ... }; 1 /
        @Int.1` divides by the outer constrained param (`@Int.1`), Tier-1."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{
  let @Int = { let @Int = random_int(0, 9); @Int.0 + 0 };
  1 / @Int.1
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [(o.kind, o.status) for o in divs]

    def test_nested_block_opaque_return_bound_to_outer_let_is_tier3(self) -> None:
        """When a nested block's RETURN value is opaque (a `random_int` in inner
        scope) and is bound to an outer `let`, a division by that outer binding
        is Tier-3 (the outer let value translates to None)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{
  let @Int = { let @Int = random_int(0, 9); @Int.0 };
  1 / @Int.0
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_modulo_in_opaque_match_arm_is_tier3(self) -> None:
        """The modulo analogue of the opaque-match-scrutinee case: `1 % @Int.0`
        in an arm over an opaque effect op is Tier-3 (modulo carries the same
        `!= 0` obligation)."""
        result = _verify("""
effect Src {
  op g(Unit -> Option<Int>);
}

private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Src>)
{ match Src.g(()) { Some(@Int) -> 1 % @Int.0, None -> 1 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_nat_sub_in_opaque_match_arm_is_tier3(self) -> None:
        """The subtraction analogue: `@Nat.0 - @Nat.1` in an arm over an opaque
        effect op (returning Option<Nat>) is Tier-3 — the matched field is an
        opaque shadow, so the underflow obligation can't discharge against it."""
        result = _verify("""
effect SrcN {
  op g(Unit -> Option<Nat>);
}

private fn f(@Nat -> @Nat)
  requires(true) ensures(true) effects(<SrcN>)
{ match SrcN.g(()) { Some(@Nat) -> @Nat.0 - @Nat.1, None -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(subs) == 1 and subs[0].status == "tier3", [(o.kind, o.status) for o in subs]
