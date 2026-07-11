"""#991 (verifier facet): the verifier resolved a bare call to a ``where``-helper
through the flat, last-wins ``env.functions`` lookup, so in a diamond shape —
two sibling helpers each carrying a nested helper of the SAME name but a
DIFFERENT postcondition — it assumed the WRONG helper's ``ensures`` at the call
site and reported a false E500 against a correct program.

The fix makes the call lookup lexically scoped: a bare call inside a function
body resolves to the nearest same-named helper in the enclosing ``where``-tree
(own children first, then each ancestor's helpers), and only falls back to the
top-level / flat registry when no enclosing helper matches — so the checker,
verifier, and codegen agree on helper-name scoping.
"""

from __future__ import annotations

from tests.verifier_helpers import _verify, _verify_err, _verify_ok


# The diamond: `branchA` and `branchB` each own a nested `leaf`; both are named
# `leaf` but carry different postconditions (result == 100 vs result == 200).
# Each parent's own `leaf` discharges its own postcondition, so the whole
# program is correct — the flat lookup proved `branchA` against `branchB`'s leaf
# (or vice-versa) and rejected it.
_DIAMOND_OK = """\
public fn top(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  branchA(@Int.0) + branchB(@Int.0)
} where {
  fn branchA(@Int -> @Int)
    requires(true) ensures(@Int.result == 100) effects(pure)
  {
    leaf(@Int.0)
  } where {
    fn leaf(@Int -> @Int)
      requires(true) ensures(@Int.result == 100) effects(pure)
    {
      100
    }
  }
  fn branchB(@Int -> @Int)
    requires(true) ensures(@Int.result == 200) effects(pure)
  {
    leaf(@Int.0)
  } where {
    fn leaf(@Int -> @Int)
      requires(true) ensures(@Int.result == 200) effects(pure)
    {
      200
    }
  }
}
"""

# The negative control: `branchA`'s own `leaf` genuinely violates branchA's
# postcondition (leaf returns 200 but branchA claims result == 100).  The
# scoped lookup must still catch this against branchA's OWN leaf — the fix
# tightens resolution, it does not silence the check.
_DIAMOND_GENUINE_VIOLATION = """\
public fn top(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  branchA(@Int.0) + branchB(@Int.0)
} where {
  fn branchA(@Int -> @Int)
    requires(true) ensures(@Int.result == 100) effects(pure)
  {
    leaf(@Int.0)
  } where {
    fn leaf(@Int -> @Int)
      requires(true) ensures(@Int.result == 200) effects(pure)
    {
      200
    }
  }
  fn branchB(@Int -> @Int)
    requires(true) ensures(@Int.result == 200) effects(pure)
  {
    leaf(@Int.0)
  } where {
    fn leaf(@Int -> @Int)
      requires(true) ensures(@Int.result == 200) effects(pure)
    {
      200
    }
  }
}
"""


class TestWhereHelperScope991:
    def test_diamond_same_named_helpers_verifies(self) -> None:
        # THE BUG: false E500 on `branchA` — the flat lookup assumed
        # `branchB`'s leaf (ensures result == 200) at branchA's call site.
        _verify_ok(_DIAMOND_OK)

    def test_diamond_counterexample_gone(self) -> None:
        # Pin the exact wrong-helper signature: the pre-fix counterexample
        # bound the call result to 200 (branchB's leaf) while proving
        # branchA's `result == 100`.  No branchA error at all post-fix.
        result = _verify(_DIAMOND_OK)
        branch_a_errors = [
            d for d in result.diagnostics
            if d.severity == "error" and "branchA" in d.description
        ]
        assert branch_a_errors == [], (
            f"branchA must verify against its OWN leaf, got: "
            f"{[e.description for e in branch_a_errors]}"
        )

    def test_genuine_violation_still_caught(self) -> None:
        # The scoped lookup must not silence a real mismatch: branchA's own
        # leaf returns 200, contradicting branchA's `result == 100`.
        _verify_err(_DIAMOND_GENUINE_VIOLATION, "branchA")


# PR #1013 review (CodeRabbit outside-diff): `_verify_fn`'s generic dispatch
# called `_verify_generic_instances` WITHOUT the `enclosing` chain, and the
# clone verification inside it called `_verify_fn(clone)` with the default
# `enclosing=()` — so a GENERIC helper nested under a non-generic parent lost
# its ancestor scope during per-instantiation verification.  Its bare call to
# an UNSHADOWED ancestor helper then fell through the scoped lookup (no own
# helper, no top-level match) to the flat last-wins registry, where a
# same-named DECOY helper under any other function captured it: `gen`'s
# `aunt(@Int.0)` was proved against the decoy's `ensures(result == 0)` instead
# of the real aunt's `+ 7` — a false E500 on a correct program
# (registration-order-dependent: the decoy registers last and wins).
_GENERIC_HELPER_ANCESTOR_DECOY = """\
public fn host(@Int -> @Int)
  requires(true) ensures(@Int.result == @Int.0 + 7) effects(pure)
{
  gen(@Int.0)
} where {
  fn aunt(@Int -> @Int)
    requires(true) ensures(@Int.result == @Int.0 + 7) effects(pure)
  {
    @Int.0 + 7
  }
  forall<T> fn gen(@Int -> @Int)
    requires(true) ensures(@Int.result == @Int.0 + 7) effects(pure)
  {
    aunt(@Int.0)
  }
}

public fn decoy(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  aunt(@Int.0)
} where {
  fn aunt(@Int -> @Int)
    requires(true) ensures(@Int.result == 0) effects(pure)
  {
    0
  }
}
"""


def _run(source: str, fn: str, args: list[int]) -> int:
    """Compile and execute, mirroring the codegen-test pipeline — paired with
    the verify assertion so verifier↔codegen agreement is pinned per shape."""
    from vera.checker import typecheck_with_artifacts
    from vera.codegen import compile as codegen_compile
    from vera.codegen import execute
    from vera.parser import parse_to_ast

    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source)
    assert not [d for d in diags if d.severity == "error"]
    result = codegen_compile(
        program, source=source,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    errs = [d for d in result.diagnostics if d.severity == "error"]
    assert not errs, f"codegen errors: {[d.description for d in errs]}"
    return execute(result, fn_name=fn, args=args).value


class TestGenericCloneEnclosingScope1013:
    def test_generic_helper_clone_sees_ancestor_helpers(self) -> None:
        # THE BUG: false E500 on `gen` — its clone was verified with an empty
        # enclosing chain, so `aunt` resolved through the flat registry to the
        # decoy's `ensures(result == 0)`.  Post-fix the chain is threaded and
        # `aunt` resolves to host's own aunt (`+ 7`), proving gen's contract.
        result = _verify(_GENERIC_HELPER_ANCESTOR_DECOY)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], (
            f"gen must verify against host's OWN aunt, got: "
            f"{[e.description for e in errors]}"
        )
        # Codegen agreement: the compiled program runs the real aunt (+7).
        assert _run(_GENERIC_HELPER_ANCESTOR_DECOY, "host", [1]) == 8

    def test_decoy_still_verified_against_its_own_helper(self) -> None:
        # Control: the decoy function's own aunt (result == 0) is a correct
        # contract for its own body — no error anywhere in the program.
        result = _verify(_GENERIC_HELPER_ANCESTOR_DECOY)
        decoy_errors = [
            d for d in result.diagnostics
            if d.severity == "error" and "decoy" in d.description
        ]
        assert decoy_errors == []
