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
