"""Tests for vera.verifier — calls_modules (call-site preconditions, pipe operator, cross-module contracts).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations

from pathlib import Path

from vera.parser import parse_to_ast
from vera.checker import typecheck
from vera.resolver import ResolvedModule
from vera.verifier import VerifyResult, verify

from tests.verifier_helpers import (
    _verify,
    _verify_err,
    _verify_ok,
)


# =====================================================================
# Call-site precondition verification (C6b)
# =====================================================================

class TestCallSiteVerification:
    """Modular verification: callee preconditions checked at call sites."""

    def test_call_satisfied_precondition(self) -> None:
        """Calling with a literal that satisfies requires(@Int.0 != 0)."""
        _verify_ok("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(1) }
""")

    def test_call_violated_precondition(self) -> None:
        """Calling with literal 0 violates requires(@Int.0 != 0)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0) }
""", "precondition")

    def test_call_precondition_forwarded(self) -> None:
        """Caller's precondition implies callee's — passes."""
        _verify_ok("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn safe_caller(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ non_zero(@Int.0) }
""")

    # ---- #730: preconditions for calls in STATEMENT position ----
    # A call whose result is discarded (a bare `f(x);` statement) must still be
    # checked against its requires(...) — DESIGN.md: contracts are checked "at
    # every call site".  Before #730 the SMT body translation skipped ExprStmt.

    def test_call_violated_precondition_stmt_position(self) -> None:
        """#730 (headline): a statement-position call (result discarded) whose
        precondition is violated must fire E501 — the gap this fix closes."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0); 1 }
""", "precondition")

    def test_call_satisfied_precondition_stmt_position(self) -> None:
        """#730 guard: a satisfied precondition in statement position must NOT
        fire a spurious E501 (the fix must not over-fire)."""
        _verify_ok("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn ok_caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(1); 1 }
""")

    def test_call_violated_precondition_stmt_position_in_if_branch(self) -> None:
        """#730: a statement-position call inside an if-branch block (routed via
        _translate_if -> _translate_block) is precondition-checked."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ if @Int.0 > 5 then { non_zero(0); @Int.0 } else { @Int.0 } }
""", "precondition")

    def test_call_violated_precondition_stmt_position_in_match_arm(self) -> None:
        """#730: a statement-position call inside a match-arm block (routed via
        _translate_match -> _translate_block) is precondition-checked."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

public data Flag {
  On,
  Off
}

private fn caller(@Flag -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match @Flag.0 { On -> { non_zero(0); 1 }, Off -> 2 } }
""", "precondition")

    def test_call_stmt_position_sees_preceding_let(self) -> None:
        """#730: a statement-position call sees preceding let bindings — the env
        is threaded through ExprStmt translation (here @Int.0 == 0 violates)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let @Int = 0; non_zero(@Int.0); 1 }
""", "precondition")

    def test_call_stmt_position_no_double_count(self) -> None:
        """#730: a single statement-position violating call yields EXACTLY ONE
        call_pre E501 obligation — not zero (the bug pre-fix), not accidentally
        more.  In statement position the call is translated once, so this is a
        precise-count guard; the span-keyed #727 dedup's no-OVER-collapse
        property is pinned separately by
        test_two_distinct_stmt_position_violations_each_fire."""
        result = _verify("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0); 1 }
""")
        e501 = [o for o in result.obligations
                if o.kind == "call_pre" and o.error_code == "E501"]
        assert len(e501) == 1, (
            f"expected exactly one call_pre E501 obligation, got {len(e501)}: "
            f"{[(o.line, o.column) for o in e501]}"
        )

    def test_call_stmt_position_effect_op_degrades(self) -> None:
        """#730 guard: an untranslatable statement (an effect op) is ignored, not
        crashed on, and does not abort verification of the rest of the block."""
        _verify_ok("""
private fn logged(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{ IO.print("hi"); @Int.0 }
""")

    def test_call_violated_precondition_after_untranslatable_stmt(self) -> None:
        """#730 soundness: an untranslatable statement (an effect op) preceding a
        decidable violating call must NOT abort the block — the later call is
        still precondition-checked.  Guards the `_translate_block` invariant that
        a None-returning ExprStmt is IGNORED, not propagated as a block bail: the
        abort-on-None wrong-fix passes every other statement-position test yet
        silently drops this E501 (PR #777 review)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{ IO.print("side"); non_zero(0); @Int.0 }
""", "precondition")

    def test_two_distinct_stmt_position_violations_each_fire(self) -> None:
        """Two distinct statement-position violating calls produce TWO E501
        obligations — the span-keyed #727 dedup collapses a re-translated SAME
        site to one, but must NOT over-collapse genuinely-different sites
        (PR #777 review)."""
        result = _verify("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0); non_zero(0); 1 }
""")
        e501 = [o for o in result.obligations
                if o.kind == "call_pre" and o.error_code == "E501"]
        assert len(e501) == 2, (
            f"two distinct statement-position violations must each fire, got "
            f"{len(e501)}: {[(o.line, o.column) for o in e501]}"
        )

    def test_call_violated_precondition_nested_in_stmt_expr(self) -> None:
        """A violating call buried inside a larger statement-position expression
        (`non_zero(0) + 5;`) is precondition-checked — the ExprStmt translation
        recurses into sub-expressions, not just the outermost node (PR #777
        review)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0) + 5; 1 }
""", "precondition")

    def test_decreases_resolves_via_stmt_position_recursive_call(self) -> None:
        """A recursive call in STATEMENT position (result discarded) is seen by
        the termination walker, so `decreases` still resolves to Tier-1 — the
        third statement-iterating walker (`_walk_for_calls`) recurses into
        ExprStmt (the branch that was the last `# pragma: no cover`).  Without it
        the recursive call is invisible and `decreases` silently degrades to
        Tier-3 (PR #777 review)."""
        result = _verify("""
private fn countdown(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{ if @Nat.0 == 0 then { 0 } else { countdown(@Nat.0 - 1); 0 } }
""")
        decr = [o for o in result.obligations
                if o.fn_name == "countdown" and o.kind == "decreases"]
        assert len(decr) == 1 and decr[0].status == "verified", (
            "decreases must resolve to Tier-1 via the statement-position "
            f"recursive call; got {[(o.kind, o.status) for o in decr]}"
        )
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_call_postcondition_assumed(self) -> None:
        """Caller's ensures relies on callee's postcondition."""
        _verify_ok("""
private fn succ(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }

private fn add_two(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 2)
  effects(pure)
{ succ(succ(@Int.0)) }
""")

    def test_recursive_call_uses_postcondition(self) -> None:
        """Recursive factorial: ensures(@Nat.result >= 1) now Tier 1.

        The postcondition is assumed at the recursive call site,
        and base case returns 1, so result >= 1 is provable.
        """
        result = _verify("""
private fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 1 }
  else { @Nat.0 * factorial(@Nat.0 - 1) }
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Expected no errors, got: {[e.description for e in errors]}"
        # ensures now Tier 1 (modular verification), decreases still Tier 3
        assert result.summary.tier1_verified >= 2

    def test_call_trivial_precondition(self) -> None:
        """Callee with requires(true) — always satisfied."""
        _verify_ok("""
private fn id(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ id(@Int.0) }
""")

    def test_call_in_let_binding(self) -> None:
        """Call result used via let binding, passed to second call."""
        _verify_ok("""
private fn succ(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }

private fn add_two_let(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 2)
  effects(pure)
{
  let @Int = succ(@Int.0);
  succ(@Int.0)
}
""")

    def test_where_block_call(self) -> None:
        """Call to a where-block helper function."""
        _verify_ok("""
private fn outer(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ helper(@Int.0) }
where {
  fn helper(@Int -> @Int)
    requires(true)
    ensures(@Int.result == @Int.0 + 1)
    effects(pure)
  { @Int.0 + 1 }
}
""")

    def test_generic_call_verified_per_instantiation(self) -> None:
        """#732: a generic instantiated by a caller is verified statically per
        monomorphization — Tier 1, not the old Tier-3 bail."""
        result = _verify("""
private forall<T>
fn id(@T -> @T)
  requires(true)
  ensures(@T.result == @T.0)
  effects(pure)
{ @T.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ id(@Int.0) }
""")
        # id<Int>'s ensures(@T.result == @T.0) holds for the body @T.0, so the
        # instantiated generic is now discharged statically with no Tier-3
        # fallback — the core #732 behavior change.
        assert result.summary.tier3_runtime == 0
        assert not result.diagnostics
        # Check id's OWN ensures is the verified obligation, not just the
        # summary counter (which a non-generic obligation could also bump).
        assert any(
            o.fn_name == "id" and o.kind == "ensures" and o.status == "verified"
            for o in result.obligations
        )

    def test_multiple_preconditions_all_checked(self) -> None:
        """Two requires on callee, second one violated."""
        _verify_err("""
private fn guarded(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ guarded(@Int.0) }
""", "precondition")

    def test_precondition_via_caller_requires(self) -> None:
        """Caller's requires forwards two constraints to satisfy callee."""
        _verify_ok("""
private fn guarded(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn good_caller(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ guarded(@Int.0) }
""")

    def test_multiple_calls_in_sequence(self) -> None:
        """Two calls in sequence, each gets a fresh return variable."""
        _verify_ok("""
private fn inc(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }

private fn add_two_seq(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 2)
  effects(pure)
{
  let @Int = inc(@Int.0);
  inc(@Int.0)
}
""")

    def test_violation_error_mentions_callee_name(self) -> None:
        """Error message includes the callee function name."""
        errors = _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0) }
""", "precondition")
        # Check that the error mentions the callee name
        assert any("non_zero" in e.description for e in errors)

    # -- Branch-aware precondition checking (#283) -------------------------

    def test_call_precondition_satisfied_by_if_guard(self) -> None:
        """Call inside if-branch where branch condition implies precondition."""
        _verify_ok("""
private fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then { positive(@Int.0) }
  else { 0 }
}
""")

    def test_call_precondition_with_else_guard(self) -> None:
        """Call inside else-branch where negated condition implies precondition."""
        _verify_ok("""
private fn non_negative(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { non_negative(@Int.0) }
}
""")

    def test_recursive_call_guarded_by_if(self) -> None:
        """Recursive call guarded by if — the fizzbuzz pattern (#283).

        De Bruijn: @Nat.0 = counter (second param, most recent),
        @Nat.1 = limit (first param).  The recursive call passes
        limit first, counter+1 second: loop(@Nat.1, @Nat.0 + 1).
        """
        _verify_ok("""
private fn loop(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  effects(pure)
{
  if @Nat.0 < @Nat.1 then {
    loop(@Nat.1, @Nat.0 + 1)
  } else { @Nat.0 }
}
""")

    def test_call_precondition_with_match_guard(self) -> None:
        """Call inside match arm with nested if-guard."""
        _verify_ok("""
private data Maybe {
  Nothing,
  Just(Int)
}

private fn use_positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn process(@Maybe -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Maybe.0 {
    Just(@Int) -> if @Int.0 > 0 then { use_positive(@Int.0) } else { 0 },
    Nothing -> 0
  }
}
""")

    def test_call_precondition_nested_if(self) -> None:
        """Nested if-branches compounding conditions."""
        _verify_ok("""
private fn bounded(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then {
    if @Int.0 < 100 then {
      bounded(@Int.0)
    } else { 0 }
  } else { 0 }
}
""")

    def test_call_precondition_violated_despite_branch(self) -> None:
        """Call violates precondition even inside an if-branch."""
        _verify_err("""
private fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 10 then { positive(@Int.0) }
  else { positive(@Int.0) }
}
""", "precondition")


# =====================================================================
# Pipe operator verification
# =====================================================================

class TestPipeVerification:
    """Pipe operator desugars correctly in SMT translation."""

    def test_pipe_verifies(self) -> None:
        """Pipe expression in verified function."""
        _verify_ok("""
private fn inc(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 + 1 }

private fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 |> inc() }
""")


# =====================================================================
# Cross-module contract verification (C7d)
# =====================================================================

class TestCrossModuleVerification:
    """Imported function contracts are verified at call sites."""

    # Reusable module sources
    MATH_MODULE = """\
public fn abs(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }

public fn max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= @Int.0)
  ensures(@Int.result >= @Int.1)
  effects(pure)
{ if @Int.0 >= @Int.1 then { @Int.0 } else { @Int.1 } }
"""

    GUARDED_MODULE = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result > 0)
  effects(pure)
{ @Int.0 }

private fn internal(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> ResolvedModule:
        """Build a ResolvedModule from source text."""
        prog = parse_to_ast(source)
        return ResolvedModule(
            path=path,
            file_path=Path(f"/fake/{'/'.join(path)}.vera"),
            program=prog,
            source=source,
        )

    @staticmethod
    def _verify_mod(
        source: str,
        modules: list[ResolvedModule],
    ) -> VerifyResult:
        """Parse, type-check, and verify with resolved modules."""
        prog = parse_to_ast(source)
        typecheck(prog, source, resolved_modules=modules)
        return verify(prog, source, resolved_modules=modules)

    # -- Postcondition assumption -----------------------------------------

    def test_imported_postcondition_assumed(self) -> None:
        """abs(x) ensures result >= 0, so caller's ensures(@Int.result >= 0) verifies."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ abs(@Int.0) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_local_shadow_uses_local_contract(self) -> None:
        """§8.5.2: a bare call resolves to the LOCAL shadow's contract.

        A non-builtin name (``triple``) isolates module shadowing from the
        verifier's built-in models (abs/min/max).  The local's ensures
        (== 42) lets the caller's ensures(== 42) verify; the imported ensures
        (>= 0) alone would not — so this pins that the verifier reasons with
        the local definition for a bare call, matching codegen (§8.5.2).
        """
        mod = self._resolved(("m",), """\
public fn triple(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }
""")
        result = self._verify_mod("""\
import m(triple);
public fn triple(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 42)
  effects(pure)
{ 42 }
public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 42)
  effects(pure)
{ triple(0 - 5) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Precondition violation -------------------------------------------

    def test_imported_precondition_violation(self) -> None:
        """positive(0) violates requires(@Int.0 > 0)."""
        mod = self._resolved(("util",), self.GUARDED_MODULE)
        result = self._verify_mod("""\
import util(positive);
private fn bad(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ positive(0) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, "Expected precondition violation"
        assert any("precondition" in e.description.lower() for e in errors)

    # -- Precondition satisfied by caller's requires ----------------------

    def test_imported_precondition_satisfied(self) -> None:
        """Caller's requires(@Int.0 > 0) implies positive's precondition."""
        mod = self._resolved(("util",), self.GUARDED_MODULE)
        result = self._verify_mod("""\
import util(positive);
private fn good(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ positive(@Int.0) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Chained imported calls -------------------------------------------

    def test_chained_imported_calls(self) -> None:
        """abs(max(x, y)) >= 0 verifies via composed postconditions."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs, max);
private fn abs_max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ abs(max(@Int.0, @Int.1)) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Selective import filter ------------------------------------------

    def test_selective_import_not_imported(self) -> None:
        """Function not in import list falls back to Tier 3."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ abs(@Int.0) }
""", [mod])
        # abs is imported, max is not — but we're only calling abs here
        # abs should be Tier 1 verified (postcondition is trivial ensures(true))
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Private function not available -----------------------------------

    def test_private_function_not_registered(self) -> None:
        """Private function from module is not injected into verifier env."""
        mod = self._resolved(("util",), self.GUARDED_MODULE)
        # 'internal' is private — it shouldn't be available as a bare call.
        # The verifier should not have it registered, so any ensures relying
        # on its postcondition would fall to Tier 3.
        result = self._verify_mod("""\
import util(positive);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ positive(1) }
""", [mod])
        # positive is public with ensures(@Int.result > 0) → Tier 1
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]
        # Verify the private function 'internal' is not in the env
        assert result.summary.tier3_runtime == 0

    # -- Tier summary counts ----------------------------------------------

    def test_tier_counts_with_imports(self) -> None:
        """Imported calls promote to Tier 1 instead of Tier 3."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ abs(@Int.0) }
""", [mod])
        # requires(true) → Tier 1, ensures(@Int.result >= 0) → Tier 1 (via abs postcondition)
        assert result.summary.tier1_verified >= 2

    # -- No regression on single-module -----------------------------------

    def test_single_module_unchanged(self) -> None:
        """Single-module programs verify identically with empty modules list."""
        source = """\
private fn id(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }
"""
        result_without = _verify(source)
        result_with = self._verify_mod(source, [])
        assert result_without.summary.tier1_verified == result_with.summary.tier1_verified
        assert result_without.summary.tier3_runtime == result_with.summary.tier3_runtime

    # -- #747 site 4: imported constructor @Nat-field narrowing ------------

    BOXES_MODULE = """\
public data NatBox {
  WrapN(Nat)
}

public data Box<T> {
  Wrap(T)
}
"""

    def test_imported_ctor_concrete_nat_field_obligated(self) -> None:
        """#747 site 4: an imported constructor with a concrete @Nat field
        (`WrapN(Nat)` from another module) narrowing an @Int argument is
        obligated `>= 0`.  The verifier harvests the imported ctor's field
        types into `_module_constructors`, so the narrowing fires (E503)
        under `requires(true)` instead of passing silently."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(WrapN, NatBox);
private fn f(@Int -> @NatBox)
  requires(true)
  ensures(true)
  effects(pure)
{ WrapN(@Int.0) }
""", [mod])
        violated = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]
        assert len(violated) == 1, [(o.kind, o.status)
                                    for o in result.obligations]
        assert violated[0].error_code == "E503"

    def test_imported_ctor_concrete_nat_field_discharged(self) -> None:
        """The imported concrete-@Nat-field narrowing discharges from a
        precondition that proves the argument non-negative."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(WrapN, NatBox);
private fn f(@Int -> @NatBox)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ WrapN(@Int.0) }
""", [mod])
        # Pin that the obligation actually fired and verified — not merely the
        # absence of a violation (which a no-obligation regression would also
        # satisfy), mirroring the generic discharged companion (CR #756).
        statuses = [o.status for o in result.obligations
                    if o.kind == "nat_bind"]
        assert statuses == ["verified"], statuses
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_imported_ctor_generic_field_nat_obligated(self) -> None:
        """#747 site 4: an imported *generic* constructor field instantiated
        to @Nat at the call site (`Wrap(@Int.0)` building `Box<Nat>`) is
        obligated — the harvested field type is a TypeVar, so the
        instantiated @Nat target comes from the checker's side-table."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(Wrap, Box);
private fn f(@Int -> @Box<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Wrap(@Int.0) }
""", [mod])
        violated = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]
        assert len(violated) == 1, [(o.kind, o.status)
                                    for o in result.obligations]
        assert violated[0].error_code == "E503"

    def test_imported_ctor_generic_field_nat_discharged(self) -> None:
        """The imported generic-constructor narrowing discharges from a
        precondition — pins that imported generic-field instantiation isn't
        always treated as violated (CodeRabbit, PR #756)."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(Wrap, Box);
private fn f(@Int -> @Box<Nat>)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ Wrap(@Int.0) }
""", [mod])
        # The obligation must be present AND verified — not merely absent
        # (a regression that stopped emitting it would also be "not
        # violated") (CodeRabbit, PR #756).
        verified = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "verified"]
        assert len(verified) == 1, [(o.kind, o.status)
                                    for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == []
