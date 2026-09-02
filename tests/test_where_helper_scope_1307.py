"""#1307 — a `where`-helper is local to its parent, on the checker's table too.

``register_fn`` recursed every ``where``-helper into the flat ``TypeEnv``
(``vera/registration.py``), and ``_lookup_function_scoped``'s final
``env.lookup_function(name)`` fallback found them from anywhere in the
module.  Two consequences, both measured on ``origin/release/v0.2.0``
(6dc41d40):

* A bare call in a SIBLING declaration resolved to another function's
  helper: the program checked green (``OK``) and died at ``vera run``
  with "Function 'helperx' is not defined in this module", because
  codegen emits a helper as ``parent$where$name`` and scopes the name to
  its parent (#1299).
* Where the helper's name is an operation's, a VALID program was
  rejected: a sibling's ``get(())`` under ``handle[State<Int>]`` reported
  ``[E202] Argument 0 of 'get' has type Unit, expected Int`` — the
  checker bound the sibling's helper where codegen lowers the State
  operation (spec §7.4).

Spec §5.8 settles which side is right: functions declared inside `where`
blocks "are always local to the parent function".  So registration stops
publishing helpers into the flat registry, leaving the frame-stack walk
``_lookup_function_scoped`` already performs as the only way to reach
one, and a bare call that names a helper from outside its parent is
refused with E178 — an error naming the parent, rather than E200's
"Unresolved function 'helperx'. Define 'fn helperx(...)' in this file",
which is false advice for a name the file already declares.
"""
from __future__ import annotations

from pathlib import Path

import pytest

from tests.checker_helpers import _check, _check_clean, _check_ok, _errors
from tests.codegen_helpers import _compile, _run
from tests.module_fixture_helpers import build_multi_module_past_check
from tests.verifier_helpers import _verify_ok


# =====================================================================
# Sources
# =====================================================================

HOLDER_WITH_HELPERX = """private fn holder(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == 5)
  effects(pure)
{
  helperx(5)
}
where {
  fn helperx(@Int -> @Int)
    requires(true)
    ensures(@Int.result == @Int.0)
    effects(pure)
  {
    @Int.0
  }
}
"""

SIBLING_CALLS_HELPER = HOLDER_WITH_HELPERX + """
private fn other(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(pure)
{
  helperx(7)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 12)
  effects(pure)
{
  holder(true) + other(())
}
"""

OP_NAME_SIBLING = """public fn holder(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  get(5)
}
where {
  fn get(@Int -> @Int)
    requires(true)
    ensures(@Int.result == @Int.0)
    effects(pure)
  {
    @Int.0
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 3) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""

NESTED_HELPERS = """public fn holder(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  h1(@Int.0)
}
where {
  fn h1(@Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    h2(@Int.0)
  }
  where {
    fn h2(@Int -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {
      @Int.0
    }
  }
}
"""

GRANDPARENT_CALLS_NESTED_HELPER = """private fn holder(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  h2(@Int.0)
}
where {
  fn h1(@Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    @Int.0
  }
  where {
    fn h2(@Int -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {
      @Int.0
    }
  }
}
"""

MUTUAL_RECURSION = """public fn is_even(@Nat -> @Bool)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    true
  } else {
    is_odd(@Nat.0 - 1)
  }
}
where {
  fn is_odd(@Nat -> @Bool)
    requires(true)
    ensures(true)
    decreases(@Nat.0)
    effects(pure)
  {
    if @Nat.0 == 0 then {
      false
    } else {
      is_even(@Nat.0 - 1)
    }
  }
}
"""

SIBLING_HELPERS_IN_ONE_BLOCK = """public fn top(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  a(@Int.0)
}
where {
  fn a(@Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    b(@Int.0)
  }

  fn b(@Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    @Int.0 + 1
  }
}
"""

HELPER_SHADOWS_TOP_LEVEL = """private fn shared(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}

private fn holder(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  shared(@Int.0)
}
where {
  fn shared(@Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    @Int.0 + 2
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  shared(1) + holder(1)
}
"""

HELPER_NAMED_AFTER_BUILTIN = """private fn holder(@Array<Int> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@Array<Int>.0)
}
where {
  fn array_length(@Array<Int> -> @Nat)
    requires(true)
    ensures(true)
    effects(pure)
  {
    0
  }
}

public fn main(@Array<Int> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@Array<Int>.0)
}
"""


def _e178(diags: list) -> list:
    return [d for d in diags if d.error_code == "E178"]


# =====================================================================
# The refusal
# =====================================================================

class TestSiblingCallRefused:

    def test_repro_is_rejected(self) -> None:
        """#1307's repro, verbatim: `OK` on the base revision."""
        hits = _e178(_check(SIBLING_CALLS_HELPER))
        assert hits, "expected E178 for the sibling's bare call"
        assert all(d.severity == "error" for d in hits)

    def test_diagnostic_names_the_parent(self) -> None:
        hit = _e178(_check(SIBLING_CALLS_HELPER))[0]
        assert "helperx" in hit.description
        assert "holder" in hit.description
        assert hit.rationale and len(hit.rationale) > 30
        assert hit.fix and len(hit.fix) > 30
        assert hit.spec_ref == 'Chapter 5, Section 5.8 "Function Visibility"'

    def test_not_reported_as_unresolved(self) -> None:
        """E200's fix instruction is wrong here — the name IS declared."""
        codes = [d.error_code for d in _check(SIBLING_CALLS_HELPER)]
        assert "E200" not in codes, codes

    def test_grandparent_cannot_call_a_nested_helper(self) -> None:
        """`h2` is local to `h1`, not to `h1`'s parent."""
        hits = _e178(_check(GRANDPARENT_CALLS_NESTED_HELPER))
        assert hits, "expected E178 for the grandparent's call"
        assert "h1" in hits[0].description

    def test_e178_is_registered(self) -> None:
        from vera.errors import ERROR_CODES
        assert "E178" in ERROR_CODES
        assert ERROR_CODES["E178"]


# =====================================================================
# The op-name variant — the checker was the diverging side
# =====================================================================

class TestOperationNameVariant:

    def test_sibling_bare_op_resolves_to_the_operation(self) -> None:
        """A valid program the base revision rejected with E202."""
        _check_ok(OP_NAME_SIBLING)

    def test_it_runs_to_the_handler_state(self) -> None:
        assert _run(OP_NAME_SIBLING, "main", []) == 3

    def test_parent_still_calls_its_own_helper(self) -> None:
        """`holder`'s own `get(5)` is the helper, not the operation."""
        assert _run(OP_NAME_SIBLING, "holder", [True]) == 5


# =====================================================================
# Shapes that MUST stay green
# =====================================================================

class TestAcceptedShapes:

    def test_parent_calls_its_own_helper(self) -> None:
        _check_clean(HOLDER_WITH_HELPERX)

    def test_mutual_recursion_between_parent_and_helper(self) -> None:
        """spec §5.6.2's own example, through check and verify."""
        _check_clean(MUTUAL_RECURSION)
        _verify_ok(MUTUAL_RECURSION)

    def test_helpers_in_one_block_see_each_other(self) -> None:
        _check_clean(SIBLING_HELPERS_IN_ONE_BLOCK)
        assert _run(SIBLING_HELPERS_IN_ONE_BLOCK, "top", [1]) == 2

    def test_nested_helper_visible_to_its_own_parent(self) -> None:
        _check_clean(NESTED_HELPERS)
        assert _run(NESTED_HELPERS, "holder", [4]) == 4

    def test_helper_shadows_a_top_level_of_the_same_name(self) -> None:
        """#991's diamond: the parent gets its helper, `main` the top-level."""
        _check_clean(HELPER_SHADOWS_TOP_LEVEL)
        # holder(1) -> its helper -> 3;  shared(1) -> top-level -> 2.
        assert _run(HELPER_SHADOWS_TOP_LEVEL, "main", []) == 5

    @pytest.mark.parametrize(
        ("label", "source"),
        [
            ("ensures", """public fn holder(@Int -> @Int)
  requires(true)
  ensures(@Int.result == helperx(@Int.0))
  effects(pure)
{
  helperx(@Int.0)
}
where {
  fn helperx(@Int -> @Int)
    requires(true)
    ensures(@Int.result == @Int.0)
    effects(pure)
  {
    @Int.0
  }
}
"""),
            ("requires", """public fn holder(@Int -> @Int)
  requires(helperx(@Int.0) > 0)
  ensures(true)
  effects(pure)
{
  helperx(@Int.0)
}
where {
  fn helperx(@Int -> @Int)
    requires(true)
    ensures(@Int.result == @Int.0)
    effects(pure)
  {
    @Int.0
  }
}
"""),
            ("closure", """public fn holder(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { helperx(@Int.0) })
}
where {
  fn helperx(@Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    @Int.0 + 1
  }
}
"""),
            ("handler-clause", """public fn holder(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 3) {
    get(@Unit) -> { resume(helperx(@Int.0)) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
where {
  fn helperx(@Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    @Int.0 + 1
  }
}
"""),
        ],
    )
    def test_every_position_inside_the_parent_still_resolves(
        self, label: str, source: str,
    ) -> None:
        """The frame stack has to cover more than the body.

        A helper is reachable from its parent's contracts, from a closure
        in its body, and from a handler clause — all positions whose
        resolution used to be able to fall through to the flat registry
        and would now silently become E178 if the stack were not live
        there.
        """
        _check_clean(source)

    def test_helper_named_after_a_builtin_keeps_e151(self) -> None:
        """#815's rule is independent of where the helper is visible.

        The helper is still rejected (E151) and the sibling's call still
        resolves to the built-in, which is what makes `main` return the
        real length rather than the helper's 0.
        """
        codes = [d.error_code for d in _check(HELPER_NAMED_AFTER_BUILTIN)]
        assert "E151" in codes, codes
        assert "E178" not in codes, codes


# =====================================================================
# Across a module boundary
# =====================================================================

class TestModuleImport:
    """A module's helper is not part of that module's namespace either.

    The flat registration published helpers into the temp checker's
    ``env.functions``, which is where the importer's private-name check
    read them from — so the refusal below used to come from a helper
    being *not public*.  It is not a declaration of the module at all,
    and the check now says so from the module's own AST; without this
    the import would be silently accepted and only the call site would
    warn, leaving `vera check` exit-0 on a program that cannot compile.
    """

    LIB = """module libhelpers;

public fn parent_fn(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  inner_helper(@Int.0)
}
where {
  fn inner_helper(@Int -> @Int)
    requires(true)
    ensures(@Int.result == @Int.0)
    effects(pure)
  {
    @Int.0
  }
}
"""

    MAIN = """import libhelpers(inner_helper);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  inner_helper(3)
}
"""

    PUBLIC_MAIN = """import libhelpers(parent_fn);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent_fn(3)
}
"""

    def test_importing_a_helper_is_refused(self, tmp_path: Path) -> None:
        check_errors, _result, _cg = build_multi_module_past_check(
            tmp_path, {
                "main.vera": self.MAIN,
                "libhelpers.vera": self.LIB,
            },
        )
        codes = [c for c, _ in check_errors]
        assert "E150" in codes, check_errors
        assert any(
            "where-helper of 'parent_fn'" in d for _, d in check_errors
        ), check_errors

    def test_importing_the_parent_still_works(self, tmp_path: Path) -> None:
        from tests.module_fixture_helpers import build_multi_module, module_value
        verify_errors, result, cg_errors = build_multi_module(
            tmp_path, {
                "main.vera": self.PUBLIC_MAIN,
                "libhelpers.vera": self.LIB,
            },
        )
        assert verify_errors == [], verify_errors
        assert cg_errors == [], cg_errors
        assert module_value(result, "main") == ("ok", 3)


# =====================================================================
# Cross-component differential: the two tables answer alike
# =====================================================================

class TestCheckerAndCodegenAgree:
    """check-green ⇒ compilable, over the shapes the scope rule decides.

    A unit test on either side alone cannot see the desync this issue is
    about: the checker resolved a name codegen does not, so only running
    both and comparing catches it.
    """

    @pytest.mark.parametrize(
        "source",
        [
            SIBLING_CALLS_HELPER,
            GRANDPARENT_CALLS_NESTED_HELPER,
            OP_NAME_SIBLING,
            HOLDER_WITH_HELPERX,
            MUTUAL_RECURSION,
            SIBLING_HELPERS_IN_ONE_BLOCK,
            NESTED_HELPERS,
            HELPER_SHADOWS_TOP_LEVEL,
        ],
        ids=[
            "sibling-call", "grandparent-call", "op-name", "parent-call",
            "mutual-recursion", "one-block", "nested", "diamond",
        ],
    )
    def test_agreement(self, source: str) -> None:
        check_rejects = bool(_errors(source))
        if check_rejects:
            # Nothing to compare: a rejected program is never compiled.
            return
        result = _compile(source)
        codegen_errors = [
            d for d in result.diagnostics if d.severity == "error"
        ]
        assert not codegen_errors, (
            "check-green program did not compile: "
            f"{[d.description for d in codegen_errors]}"
        )
