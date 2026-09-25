"""A callee's contract is READ in the callee's own module (#1220, #1225, #1226).

Three ways the toolchain read an imported callee's contract as though it had
been written in the importer's file:

* #1220 — the ``Precondition:`` line of an E501 quoted the IMPORTER's source
  buffer at the callee's span, so the message showed whatever text sat on that
  line here (a plausible-looking `requires` from another function, or nothing
  at all when the callee's file is the longer one);
* #1225 — a bare-name call *inside* the callee's contract resolved through the
  IMPORTER's function registry, so the callee's ``requires`` / ``ensures`` was
  interpreted against a same-named local function's contract: a false Tier 1
  whose runtime traps, and the mirror spurious E501;
* #1226 — the refined-RETURN binder was the predicate's bare head identifier,
  so a refinement over a PARAMETERISED base pushed ``Box`` where the
  predicate's reference resolves ``Box<Nat>``: the return fact was dropped and
  a valid program rejected.

Every direction is asserted against a runtime oracle wherever the two can
disagree — a wrong namespace's two failure modes (an obligation that vanishes
and one that fires for no reason) look identical from inside the verifier, and
only `vera run` says which one a verdict is.
"""
from __future__ import annotations

import os
import tempfile
from pathlib import Path

import pytest

from vera import ast
from vera.checker import typecheck
from vera.codegen import compile, execute
from vera.parser import parse_file, parse_to_ast
from vera.resolver import ResolvedModule
from vera.runtime.traps import WasmTrapError
from vera.transform import transform
from vera.verifier import ContractVerifier, VerifyResult, verify


# =====================================================================
# Helpers
# =====================================================================

def _resolved(
    path: tuple[str, ...], source: str, direct: bool = True,
) -> ResolvedModule:
    """A ``ResolvedModule`` from source text, via a real temp file.

    ``delete=False`` + explicit unlink is the Windows-safe pattern (an open
    ``NamedTemporaryFile`` cannot be reopened there).

    *direct* is whether the ENTRY program imports this module (§8.6.4): a
    module reached only through another module's imports must be marked
    ``False``, or the verifier injects its public surface into the entry
    program's namespace and a visibility assertion measures the fixture
    instead of the compiler.
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        fp = f.name
    try:
        return ResolvedModule(
            path=path, file_path=Path(fp),
            program=transform(parse_file(fp)), source=source, direct=direct,
        )
    finally:
        os.unlink(fp)


#: The entry file name every helper here verifies under.  Named rather than
#: defaulted to ``None``, so an assertion about WHICH file a location carries
#: compares against a known value instead of only ruling out ``None``.
_ENTRY_FILE = "main.vera"


def _verify_mod(source: str, modules: list[ResolvedModule]) -> VerifyResult:
    """Type-check and verify *source* against *modules*, asserting check-clean.

    Check-clean is the premise of every test here: a fixture that fails to
    type-check would satisfy a "no errors" assertion trivially.
    """
    prog = parse_to_ast(source)
    diags = typecheck(prog, source, resolved_modules=modules, file=_ENTRY_FILE)
    check_errors = [d for d in diags if d.severity == "error"]
    assert not check_errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:70]) for d in check_errors]}"
    )
    return verify(
        prog, source, file=_ENTRY_FILE, resolved_modules=modules)


def _codes(result: VerifyResult) -> set[str]:
    return {d.error_code for d in result.diagnostics if d.severity == "error"}


def _e501(result: VerifyResult) -> str:
    """The single E501 message, asserting there is exactly one."""
    messages = [
        d.description for d in result.diagnostics
        if d.error_code == "E501" and d.severity == "error"
    ]
    assert len(messages) == 1, [
        (d.error_code, d.description[:80]) for d in result.diagnostics
    ]
    return messages[0]


def _run_mod(source: str, modules: list[ResolvedModule]) -> object:
    """Compile *source* with *modules* and call ``main`` — the runtime oracle.

    Raises :class:`WasmTrapError` when the program violates a contract at run
    time, which is exactly what a false Tier 1 has to be caught by.  Compiled
    through a real temp file, the Windows-safe way ``_resolved`` is.
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        fp = f.name
    try:
        result = compile(
            transform(parse_file(fp)), source=source, file=fp,
            resolved_modules=modules,
        )
    finally:
        os.unlink(fp)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"unexpected codegen errors: {errors}"
    return execute(result, fn_name="main").value


# =====================================================================
# #1220 — the quoted clause comes from the file that declared it
# =====================================================================

# `requires` sits on LINE 4 of this module.
_QUOTE_LIB = """\
module qlib;

public fn need3(@Option<Int> -> @Int)
  requires(@Option<Int>.0 == Some(3))
  ensures(true)
  effects(pure)
{
  0
}
"""

# ... and line 4 HERE is a different, entirely plausible `requires`.  Quoted
# out of this buffer the message reads as a real clause, so a reader has no
# way to tell it is the wrong one.
_QUOTE_MAIN = """\
import qlib(need3);

public fn main(@Int -> @Int)
  requires(@Int.0 != 424242)
  ensures(true)
  effects(pure)
{
  need3(Some(9))
}
"""


class TestE501QuotesTheDeclaringFile:
    """The ``Precondition:`` line quotes the CALLEE's own source (#1220)."""

    def test_the_callees_actual_requires_clause_is_quoted(self) -> None:
        result = _verify_mod(_QUOTE_MAIN, [_resolved(("qlib",), _QUOTE_LIB)])
        assert "requires(@Option<Int>.0 == Some(3))" in _e501(result), (
            _e501(result)
        )

    def test_the_importers_text_at_that_line_is_not_quoted(self) -> None:
        """The misattribution, not just the absence of the right text.

        Both files have a ``requires`` on line 4, so the pre-fix rendering
        produced a well-formed clause belonging to another function — the
        failure mode a "contains the right text" assertion alone would still
        pass if the message quoted BOTH.
        """
        result = _verify_mod(_QUOTE_MAIN, [_resolved(("qlib",), _QUOTE_LIB)])
        assert "424242" not in _e501(result), _e501(result)

    def test_a_local_callee_still_quotes_this_program(self) -> None:
        """Control: a same-file callee's clause is quoted as it always was."""
        source = """\
private fn need_positive(@Int -> @Int)
  requires(@Int.0 > 424242)
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
  need_positive(1)
}
"""
        result = _verify_mod(source, [])
        assert "requires(@Int.0 > 424242)" in _e501(result), _e501(result)

    def test_a_qualified_call_quotes_the_declaring_file_too(self) -> None:
        """``mod::fn`` reaches the same renderer by a different lookup."""
        qualified = _QUOTE_MAIN.replace(
            "import qlib(need3);", "import qlib;",
        ).replace("need3(Some(9))", "qlib::need3(Some(9))")
        # Both rewrites must have landed: a reworded fixture would make them
        # no-ops and this would silently re-run the bare-import case above.
        assert "import qlib;" in qualified, qualified
        assert "qlib::need3(Some(9))" in qualified, qualified
        result = _verify_mod(qualified, [_resolved(("qlib",), _QUOTE_LIB)])
        message = _e501(result)
        assert "requires(@Option<Int>.0 == Some(3))" in message, message
        assert "424242" not in message, message


# The helper's `requires` is on line 18 — past the end of the importer, so the
# pre-fix rendering had no line to quote and dropped the `Precondition:` line
# entirely.  An imported GENERIC's helper, so its clause is reached through a
# monomorphized clone rather than the harvested registry.
_HELPER_LIB = """\
module hlib;

type Cnt = Bool;

public forall<T> fn f(@Array<Bool>, @Array<Int>, @T -> @Nat)
  requires(array_length(@Array<Bool>.0) == 3)
  ensures(@Nat.result >= 0)
  effects(pure)
{
  help(@Array<Bool>.0, @Array<Int>.0)
}
where {
  fn help(@Array<Cnt>, @Array<Int> -> @Nat)
    requires(array_length(@Array<Cnt>.0) == 2)
    ensures(@Nat.result >= 0)
    effects(pure)
  {
    array_length(@Array<Int>.0)
  }
}
"""

_HELPER_MAIN = """\
import hlib(f);

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f([true, false, true], array_range(0, 2), 9)
}
"""


class TestImportedGenericHelperClauseIsQuoted:
    """A clone's clause is quoted from the module that declared the generic.

    The clone's contract nodes are fresh — the harvested-clause pin cannot see
    them — so this is the case that needs the DECLARING-module scope, not the
    per-clause one: while the clone verifies, the buffer its spans number is
    its own module's.
    """

    def test_the_helpers_own_precondition_text_is_quoted(self) -> None:
        result = _verify_mod(_HELPER_MAIN, [_resolved(("hlib",), _HELPER_LIB)])
        message = _e501(result)
        assert "requires(array_length(@Array<Cnt>.0) == 2)" in message, message

    def test_the_violation_is_real(self) -> None:
        """The oracle: this E501 is a caught violation, not a spurious one.

        ``help``'s two parameters are two stacks in ``hlib`` (``Cnt = Bool``),
        so ``@Array<Cnt>.0`` is the length-3 array and the precondition really
        does fail.  Without this the quoting test above could be pinning the
        text of a message that should not exist.
        """
        modules = [_resolved(("hlib",), _HELPER_LIB)]
        with pytest.raises(WasmTrapError) as exc:
            _run_mod(_HELPER_MAIN, modules)
        assert exc.value.kind == "contract_violation", exc.value.kind


# =====================================================================
# #1225 — a bare name in the callee's contract resolves in ITS module
# =====================================================================

# `cap` is PRIVATE, so nothing the importer writes can be the same function —
# and `guarded`'s precondition is written entirely in terms of it.
_CAP_LIB = """\
module caplib;

private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 100)
  effects(pure)
{
  100
}

public fn guarded(@Int -> @Int)
  requires(@Int.0 < cap(0))
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


def _cap_main(local_cap: int, argument: int) -> str:
    """An importer declaring its OWN ``cap`` and calling ``guarded``."""
    return f"""\
import caplib(guarded);

private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == {local_cap})
  effects(pure)
{{
  {local_cap}
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  guarded({argument}) + cap(0)
}}
"""


class TestCalleeContractCallsResolveInItsModule:
    """The callee's ``requires`` is read against the callee's own ``cap``."""

    def test_the_false_tier1_is_reported_and_the_run_agrees(self) -> None:
        """`guarded(500)` violates `500 < 100`; the importer's cap is 1000.

        Read through the importer's registry the precondition is `500 < 1000`
        and verification reported all-Tier-1 clean on a program whose run traps
        — a false Tier 1, the direction that matters.
        """
        modules = [_resolved(("caplib",), _CAP_LIB)]
        source = _cap_main(local_cap=1000, argument=500)
        result = _verify_mod(source, modules)
        assert "E501" in _codes(result), (
            "the callee's precondition was proved against the IMPORTER's "
            f"`cap`: {_codes(result)}"
        )
        with pytest.raises(WasmTrapError) as exc:
            _run_mod(source, modules)
        assert exc.value.kind == "contract_violation", exc.value.kind

    def test_the_mirror_correct_program_is_accepted(self) -> None:
        """The other direction: `guarded(50)` satisfies `50 < 100`.

        The importer's cap is 0, so reading the precondition through its
        registry made it `50 < 0` and rejected a program that runs fine.  A fix
        that merely stopped checking imported preconditions would pass here and
        fail the test above, and vice versa.
        """
        modules = [_resolved(("caplib",), _CAP_LIB)]
        source = _cap_main(local_cap=0, argument=50)
        result = _verify_mod(source, modules)
        assert not _codes(result), (
            f"valid cross-module call spuriously rejected: {_codes(result)}"
        )
        assert _run_mod(source, modules) == 50

    def test_no_collision_control_discharges_and_violates_honestly(
        self,
    ) -> None:
        """Control: an importer with no ``cap`` of its own, both directions.

        The name is then absent from the importer's registry entirely, so the
        precondition did not translate at all and the obligation was a loud
        Tier-3 demotion (E532) — including for the call that violates it.  Both
        calls now get a static verdict, and each matches its runtime.
        """
        modules = [_resolved(("caplib",), _CAP_LIB)]
        template = """\
import caplib(guarded);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  guarded(%d)
}
"""
        satisfied = template % 50
        ok = _verify_mod(satisfied, modules)
        assert not _codes(ok), _codes(ok)
        assert not [
            d for d in ok.diagnostics if d.error_code == "E532"
        ], "the callee's precondition still is not translated"
        assert _run_mod(satisfied, modules) == 50

        violated = template % 500
        bad = _verify_mod(violated, modules)
        assert "E501" in _codes(bad), _codes(bad)
        with pytest.raises(WasmTrapError):
            _run_mod(violated, modules)


# The ENSURES path: `bounded`'s postcondition is written in terms of the same
# private `cap`, and the importer relies on it to prove its own.
_ENS_LIB = """\
module enslib;

private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 1000)
  effects(pure)
{
  1000
}

public fn bounded(@Int -> @Int)
  requires(true)
  ensures(@Int.result < cap(0))
  effects(pure)
{
  700
}
"""

_ENS_MAIN = """\
import enslib(bounded);

private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 5)
  effects(pure)
{
  5
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result < 5)
  effects(pure)
{
  bounded(0) + cap(0) - cap(0)
}
"""


class TestCalleeEnsuresIsReadInItsModuleToo:
    """The postcondition ASSUMED at a call site is the callee's own (#1225).

    Not a refined-return special case: the plain ``ensures`` path carries the
    same defect, and it fails the other way round — a postcondition read too
    STRONGLY proves the caller's own contract, so the caller is what traps.
    """

    def test_the_assumed_postcondition_cannot_prove_a_false_caller_contract(
        self,
    ) -> None:
        modules = [_resolved(("enslib",), _ENS_LIB)]
        result = _verify_mod(_ENS_MAIN, modules)
        assert "E500" in _codes(result), (
            "main's `ensures(@Int.result < 5)` was proved from the IMPORTER's "
            f"`cap`, which the callee's contract never names: {_codes(result)}"
        )
        with pytest.raises(WasmTrapError) as exc:
            _run_mod(_ENS_MAIN, modules)
        assert exc.value.kind == "contract_violation", exc.value.kind


# Both dimensions of the scope in ONE contract: `both`'s precondition names an
# alias-typed parameter AND calls a private helper.  `Cnt` is `Bool` here, so
# the two parameters are two stacks and `@Array<Int>.0` is the FIRST.
_BOTH_LIB = """\
module bothlib;

type Cnt = Bool;

private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 3)
  effects(pure)
{
  3
}

public fn both(@Array<Int>, @Array<Cnt> -> @Nat)
  requires(array_length(@Array<Int>.0) < cap(0))
  ensures(@Nat.result >= 0)
  effects(pure)
{
  0
}
"""

_BOTH_ALIAS_CONFLICT = "type Cnt = Int;\n\n"

_BOTH_CAP_CONFLICT = """\
private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 100)
  effects(pure)
{
  100
}

"""

# The call is made from a function whose OWN parameters are the arrays, with
# their lengths as its precondition: an array LITERAL argument does not
# translate, so a call site spelled `both([...], [...])` demotes to Tier 3
# before either half of the scope is consulted and would measure nothing.
_BOTH_MAIN = """\
import bothlib(both);

""" + _BOTH_ALIAS_CONFLICT + _BOTH_CAP_CONFLICT + """\
private fn go(@Array<Int>, @Array<Bool> -> @Nat)
  requires(array_length(@Array<Int>.0) == 5 && array_length(@Array<Bool>.0) == 2)
  ensures(true)
  effects(pure)
{
  both(@Array<Int>.0, @Array<Bool>.0)
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  go(array_range(0, 5), [true, false])
}
"""


class TestBothHalvesOfTheScopeRideTogether:
    """The naming env and the function registry are ONE swap (#1208, #1225).

    ``both``'s precondition is ``array_length(@Array<Int>.0) < cap(0)``, and
    each half of the scope decides one side of that comparison:

    * the naming env decides WHICH argument ``@Array<Int>.0`` is — the
      length-5 ``Array<Int>`` in ``bothlib`` (``Cnt = Bool``, two stacks), the
      length-2 ``Array<Bool>`` under the importer's ``type Cnt = Int`` (one
      merged stack, so ``.0`` is the most recent);
    * the function registry decides what ``cap(0)`` is — 3 in ``bothlib``, 100
      in the importer.

    Only ``5 < 3`` is false.  Each of the other three combinations — either
    half read in the importer, or both — proves the precondition and returns a
    verify-clean verdict on a program that traps, so this one program's E501
    can only be produced by swapping both halves together.  The two isolating
    controls below then show each half is separately load-bearing, so the pair
    test cannot be passing on one of them alone.
    """

    def test_the_violation_needs_both_halves(self) -> None:
        modules = [_resolved(("bothlib",), _BOTH_LIB)]
        result = _verify_mod(_BOTH_MAIN, modules)
        assert "E501" in _codes(result), (
            "at least one half of the callee's scope was read in the "
            f"importer: {_codes(result)}"
        )
        with pytest.raises(WasmTrapError) as exc:
            _run_mod(_BOTH_MAIN, modules)
        assert exc.value.kind == "contract_violation", exc.value.kind

    def test_the_registry_half_alone_decides_a_verdict(self) -> None:
        """Drop the alias conflict: only ``cap`` still differs.

        ``@Array<Int>.0`` is the length-5 array under either env now, so the
        verdict turns purely on which ``cap`` the contract's call resolves to
        — 5 < 3 (violated) against 5 < 100 (clean).
        """
        source = _BOTH_MAIN.replace(_BOTH_ALIAS_CONFLICT, "")
        assert "type Cnt" not in source
        modules = [_resolved(("bothlib",), _BOTH_LIB)]
        result = _verify_mod(source, modules)
        assert "E501" in _codes(result), _codes(result)
        with pytest.raises(WasmTrapError):
            _run_mod(source, modules)

    def test_the_naming_half_alone_decides_a_verdict(self) -> None:
        """Drop the ``cap`` conflict: only the alias still differs.

        ``cap(0)`` is 3 either way now (the importer has no ``cap`` at all), so
        the verdict turns purely on which argument ``@Array<Int>.0`` names —
        5 < 3 (violated) against 2 < 3 (clean).
        """
        source = _BOTH_MAIN.replace(_BOTH_CAP_CONFLICT, "")
        assert "ensures(@Int.result == 100)" not in source
        modules = [_resolved(("bothlib",), _BOTH_LIB)]
        result = _verify_mod(source, modules)
        assert "E501" in _codes(result), _codes(result)
        with pytest.raises(WasmTrapError):
            _run_mod(source, modules)


# =====================================================================
# #1226 — the refined-return binder is the key its predicate looks up
# =====================================================================

# `Box` is a PARAMETERISED alias, so the binder renders `Box<Nat>` while its
# head identifier is `Box`.  The base resolves to `Nat`, which is a base the
# SMT layer models, so nothing but the binder key decides whether the return
# fact survives.  The body is the natural `= T`: until #1237 it had to be
# written `= Nat` to keep that isolation, because the verifier resolved an
# alias APPLICATION to the alias's own parameter instead of substituting the
# argument, which failed the modelled-primitive gate and dropped the fact for
# an unrelated reason — these tests would then have passed or failed without
# touching the binder at all.  With the application substituted, both bodies
# resolve the base to `Nat` and the isolation holds either way; the parameter
# is exercised rather than written around.
_PARAM_BINDER = """\
type Cnt = Nat;

type Box<T> = T;

type Grown = { @Box<Cnt> | @Box<Cnt>.0 >= 18 };

private fn mk(@Nat -> @Grown)
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

private fn need18(@Nat -> @Nat)
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  need18(mk(20))
}
"""


class TestParameterisedRefinedReturnBinder:
    """A refined return over a parameterised base keeps its fact (#1226).

    ``mk``'s result is a fresh variable constrained ONLY by the refinement
    predicate — its `ensures` is `true` and the literal `20` tells the caller
    nothing about it — so `need18(mk(20))` is provable exactly when the
    refined-return fact survives.  It did not: the value was pushed under the
    predicate's head identifier ``Box`` while ``@Box<Cnt>.0`` resolves
    ``Box<Nat>``, the predicate failed to translate, and the fact was dropped
    in silence.
    """

    def test_the_valid_program_is_accepted(self) -> None:
        result = _verify_mod(_PARAM_BINDER, [])
        assert not _codes(result), (
            "the refined-return fact was dropped and a valid program "
            f"rejected: {_codes(result)}"
        )

    def test_the_program_really_does_run(self) -> None:
        """The oracle: `vera run` returns 20, so the E501 was spurious."""
        assert _run_mod(_PARAM_BINDER, []) == 20

    def test_the_producer_discharges_at_tier_1(self) -> None:
        """The other side of the same key: ``mk``'s own return obligation.

        The producing function must PROVE its refined return, and that proof
        pushes the value under the same binder.  Missing, the predicate fell
        outside the fragment and the obligation demoted to a Tier-3 runtime
        guard (E506) — conservative rather than unsound, but a provable
        refinement that no longer proves.
        """
        result = _verify_mod(_PARAM_BINDER, [])
        assert not [
            d for d in result.diagnostics if d.error_code == "E506"
        ], [d.description[:90] for d in result.diagnostics]
        assert result.summary.tier3_runtime == 0, result.summary

    def test_the_fact_is_BOUNDED_by_what_the_refinement_grants(self) -> None:
        """The over-correction direction: assuming the predicate is not the
        same as assuming anything.

        Every other test in this class and its cross-module sibling asserts
        that the refined-return fact SURVIVES, so a regression that keyed the
        binder correctly and then assumed the predicate unconditionally would
        pass all of them.  Here the consumer wants `>= 100` and the refinement
        grants `>= 18`, so the call must still be rejected — and the runtime
        agrees, which is what distinguishes a correct rejection from the
        spurious one this class exists to have removed.
        """
        bounded = _PARAM_BINDER.replace(
            "private fn need18(@Nat -> @Nat)\n  requires(@Nat.0 >= 18)",
            "private fn need18(@Nat -> @Nat)\n  requires(@Nat.0 >= 100)",
        )
        assert "requires(@Nat.0 >= 100)" in bounded, bounded
        result = _verify_mod(bounded, [])
        assert "E501" in _codes(result), (
            "the refined return grants `>= 18`; a consumer wanting `>= 100` "
            f"must not be discharged from it: {_codes(result)}"
        )
        with pytest.raises(WasmTrapError) as exc:
            _run_mod(bounded, [])
        assert exc.value.kind == "contract_violation", exc.value.kind

    def test_the_bare_base_control_is_unchanged(self) -> None:
        """The same program with an UNPARAMETERISED binder, which always
        worked: head and key coincide when there are no type arguments."""
        control = _PARAM_BINDER.replace(
            "type Box<T> = T;\n\n", "",
        ).replace("@Box<Cnt>", "@Cnt")
        assert "Box" not in control
        result = _verify_mod(control, [])
        assert not _codes(result), _codes(result)
        assert result.summary.tier3_runtime == 0, result.summary


# The cross-module twin: `Cnt` is `Nat` in the module and `Int` in the
# importer, so the binder key differs BETWEEN the two namespaces —
# `Box<Nat>` against `Box<Int>`.  `type Box<T> = T;` for the same reason as
# its single-module sibling above: the application substitutes since #1237, so
# the parameterised body isolates the binder question rather than confounding
# it.
_BINDER_LIB = """\
module boxlib;

type Cnt = Nat;

type Box<T> = T;

public fn mk(@Nat -> @{ @Box<Cnt> | @Box<Cnt>.0 >= 18 })
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}
"""

_BINDER_MAIN = """\
import boxlib(mk);

type Cnt = Int;

private fn need18(@Nat -> @Nat)
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  need18(mk(20))
}
"""


class TestRefinedReturnBinderIsKeyedInTheCalleeScope:
    """The binder is derived INSIDE the callee's scope (#1208, #1226).

    Now that the key renders its type arguments, it is env-dependent: the same
    predicate binds ``Box<Nat>`` in ``boxlib`` and ``Box<Int>`` under the
    importer's ``type Cnt = Int``.  The reference side has been translated in
    the callee's namespace since #1208, so a binder derived OUTSIDE that scope
    mints one key and looks up another — the exact miss this file's
    single-module case is about, arriving through provenance instead of
    through the head identifier.

    Moving the derivation out of the scope leaves the single-module case above
    green and turns this one red, which is what makes the wrap load-bearing
    rather than defensive: ``TestRefinedReturnTranslatesInTheCalleeNamespace``
    in the #1208 provenance suite recorded exactly that prediction while the
    bare-headed binder still masked it.
    """

    def test_the_imported_refined_return_fact_survives(self) -> None:
        modules = [_resolved(("boxlib",), _BINDER_LIB)]
        result = _verify_mod(_BINDER_MAIN, modules)
        assert not _codes(result), (
            "the callee's refined-return binder was keyed in the IMPORTER's "
            f"namespace: {_codes(result)}"
        )
        assert _run_mod(_BINDER_MAIN, modules) == 20

    def test_the_control_without_a_conflicting_alias_is_clean_too(
        self,
    ) -> None:
        """Control: the same import with the shadowing alias removed.

        The two envs then agree, so this case turns on the KEY alone and not
        on which env rendered it — it separates the two axes, and it is the
        case a fix that simply stopped assuming imported refined returns would
        also break.
        """
        control = _BINDER_MAIN.replace("type Cnt = Int;\n\n", "")
        assert "type Cnt" not in control
        result = _verify_mod(control, [_resolved(("boxlib",), _BINDER_LIB)])
        assert not _codes(result), _codes(result)


# =====================================================================
# A module's pinned registry holds what its OWN file can call
# =====================================================================

_DEEP = """\
module deep;

public fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 100)
  effects(pure)
{
  100
}

public fn other(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(pure)
{
  7
}
"""

_MID_REQ = """\
module mid;

import deep(cap);

public fn guarded(@Int -> @Int)
  requires(@Int.0 < cap(0))
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""

_MID_ENS = """\
module mid;

import deep(cap);

public fn get(@Int -> @Int)
  requires(true)
  ensures(@Int.result == cap(0))
  effects(pure)
{
  cap(@Int.0)
}
"""

_MAIN_REQ = """\
import mid(guarded);
import deep(cap);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  guarded(5) + cap(0)
}
"""

_MAIN_ENS = """\
import mid(get);
import deep(cap);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 100)
  effects(pure)
{
  get(1)
}
"""


def _deep_chain(mid_source: str) -> list[ResolvedModule]:
    return [_resolved(("mid",), mid_source), _resolved(("deep",), _DEEP)]


class TestAModulesOwnImportsAreInItsRegistry:
    """A module's contract can call what its own file IMPORTS (PR #1239).

    The registry pinned as a module's ``CalleeScope`` was built by walking its
    DECLARATIONS, so a bare name its own file imported resolved to nothing —
    silently, and only for the bare spelling.  The corpus and this file's own
    suite were single-level (a program importing leaf modules), which is why a
    byte-identical corpus differential said nothing about it: the shape needs
    a module that itself imports.

    Both directions of the miss are asserted, because they fail differently:
    a lost `requires` demotes an honest Tier-1 to E532 (a coverage loss), and
    a lost `ensures` REJECTS a valid program (a correctness one).
    """

    def test_requires_calling_a_name_the_module_imported_stays_tier1(
        self,
    ) -> None:
        result = _verify_mod(_MAIN_REQ, _deep_chain(_MID_REQ))
        codes = {d.error_code for d in result.diagnostics}
        assert "E532" not in codes, (
            "the callee's requires calls `cap`, which its own module IMPORTS; "
            f"the pinned module registry could not see it: {codes}"
        )
        assert not _codes(result), _codes(result)

    def test_ensures_calling_a_name_the_module_imported_is_still_assumed(
        self,
    ) -> None:
        """The correctness direction: `get`'s ensures is what proves `main`'s.

        `main` returns exactly what its own `ensures` demands, and the run
        agrees — so a rejection here is a rejection of a valid program.
        """
        modules = _deep_chain(_MID_ENS)
        result = _verify_mod(_MAIN_ENS, modules)
        assert not _codes(result), (
            "valid program rejected: the callee's ensures references `cap`, "
            f"which its own module IMPORTS: {_codes(result)}"
        )
        assert _run_mod(_MAIN_ENS, modules) == 100

    def test_the_bare_and_qualified_spellings_agree(self) -> None:
        """The tier stopped depending on how the call is SPELLED.

        `deep::cap(0)` goes through the path-keyed module registry, which was
        never missing, so the two spellings of one contract disagreed about
        the tier — the asymmetry that dated the regression.
        """
        qualified_mid = _MID_REQ.replace(
            "import deep(cap);", "import deep;",
        ).replace("cap(0)", "deep::cap(0)")
        # Without this the two sides could be the SAME spelling — a reworded
        # `_MID_REQ` makes both replaces no-ops and the comparison compares
        # the bare case against itself, which passes and measures nothing.
        assert "import deep;" in qualified_mid, qualified_mid
        assert "deep::cap(0)" in qualified_mid, qualified_mid
        bare = _verify_mod(_MAIN_REQ, _deep_chain(_MID_REQ))
        qual = _verify_mod(_MAIN_REQ, _deep_chain(qualified_mid))
        for result, label in ((bare, "bare"), (qual, "qualified")):
            assert not [
                d for d in result.diagnostics if d.error_code == "E532"
            ], f"{label} spelling demoted: {[d.error_code for d in result.diagnostics]}"
        assert (bare.summary.tier1_verified, bare.summary.tier3_runtime) == (
            qual.summary.tier1_verified, qual.summary.tier3_runtime
        ), (bare.summary, qual.summary)

    def test_a_name_the_middle_module_did_not_import_still_misses(
        self,
    ) -> None:
        """§8.5.1 is the rule, and the fix does not widen past it.

        `mid` imports only `cap`, so `other` is NOT in scope inside `mid`.
        The checker refuses it (E200, located in `mid`): since #1244 it
        re-checks `mid`'s bodies under `mid`'s own import filter, and since
        #1513 an unresolved call is an error rather than a warning, because
        the name has no meaning in the module that wrote it — code
        generation took the IMPORTER's `other`, so the same `mid` passed its
        precondition under one importer and trapped under another.

        The verifier is asked as well, past the checker, because its own
        scope is the invariant here.  The importer happens to import `other`
        itself, so a registry that took the whole reachable set (or fell
        through to the importer's, the pre-#1225 behaviour) would bind it
        and interpret the callee's contract with a function the callee
        cannot name.  It must miss instead — loudly, as an E532 demotion.
        """
        mid = _MID_REQ.replace("cap(0)", "other(0)")
        main = _MAIN_REQ.replace("import deep(cap);", "import deep(other);")
        main = main.replace("cap(0)", "other(0)")
        modules = _deep_chain(mid)
        prog = parse_to_ast(main)
        check = typecheck(prog, main, resolved_modules=modules,
                          file=_ENTRY_FILE)
        refused = [d for d in check
                   if d.severity == "error" and d.error_code == "E200"]
        assert len(refused) == 1, [(d.error_code, d.severity) for d in check]
        assert "other" in refused[0].description
        assert refused[0].location.file != _ENTRY_FILE
        result = verify(
            prog, main, file=_ENTRY_FILE, resolved_modules=modules)
        assert [
            d for d in result.diagnostics if d.error_code == "E532"
        ], (
            "`other` is not in `mid`'s scope, so its contract must not "
            f"resolve: {[d.error_code for d in result.diagnostics]}"
        )
        assert not _codes(result), _codes(result)

    def test_the_module_does_not_re_export_what_it_imports(self) -> None:
        """The mirror gate: filling `mid`'s registry must not widen `main`'s.

        What a module can CALL and what it EXPORTS are different sets — §8.6.4
        gives the importer only `mid`'s own public declarations — so the
        injection feeds the first and never the second.  Asserted on the
        registries rather than through a program, because the checker does not
        enforce this leg either (see the sibling test's note): a behavioural
        assertion would be pinning the checker's gap, not this fix's invariant.
        """
        main = """\
import mid(guarded);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  guarded(5)
}
"""
        prog = parse_to_ast(main)
        # `deep` is transitive HERE — `main` imports only `mid`.
        modules = [
            _resolved(("mid",), _MID_REQ),
            _resolved(("deep",), _DEEP, direct=False),
        ]
        typecheck(prog, main, resolved_modules=modules)
        verifier = ContractVerifier(source=main, resolved_modules=modules)
        verifier.register_program(prog)
        exported = verifier._module_functions[("mid",)]
        assert set(exported) == {"guarded"}, sorted(exported)
        assert "cap" not in verifier.env.functions, (
            "`mid` re-exported a name it merely imports"
        )
        # ... while the registry `mid`'s OWN contracts resolve in does have it.
        mid_scope = verifier._pinned_scope(exported["guarded"])
        assert mid_scope is not None
        assert mid_scope.fn_lookup is not None
        assert mid_scope.fn_lookup("cap") is not None, (
            "`mid`'s own registry lost the name its file imports"
        )


# =====================================================================
# The rest of the message points at the declaring file too
# =====================================================================

class TestDiagnosticLocationsFollowTheDeclaringModule:
    """A diagnostic raised while an imported clone verifies names ITS file.

    #1220 moved the QUOTED CLAUSE to the declaring module's buffer and left the
    rest of the message on the entry program's: the excerpt under the caret was
    sliced from `self.source` and the location named `self.file`, so a reader
    was sent to the importer's line N for a clause that lives at another file's
    line N — and where the importer is the shorter file, to an empty excerpt
    with nothing to say it was missing (PR #1239 review).
    """

    def test_the_location_and_excerpt_come_from_the_module(self) -> None:
        module = _resolved(("hlib",), _HELPER_LIB)
        result = _verify_mod(_HELPER_MAIN, [module])
        raised_in_module = [
            d for d in result.diagnostics
            if "generic function 'f'" in d.description
        ]
        assert raised_in_module, [d.description[:70] for d in result.diagnostics]
        lib_lines = _HELPER_LIB.splitlines()
        for d in raised_in_module:
            # The module's EXACT path, not merely "not the entry file": the
            # entry name is known (`_ENTRY_FILE`), so ruling it out would also
            # accept any third file.
            assert d.location.file == str(module.file_path), d.location.file
            assert d.source_line == lib_lines[d.location.line - 1], (
                f"{d.error_code} at line {d.location.line} excerpted "
                f"{d.source_line!r}, but that line of the module reads "
                f"{lib_lines[d.location.line - 1]!r}"
            )

    def test_a_clause_past_the_importers_end_still_has_an_excerpt(
        self,
    ) -> None:
        """The importer is 9 lines; the clause that raises sits at line 12+.

        Sliced from the entry buffer the index simply falls off the end and the
        excerpt is empty — a silent miss, which is the failure mode the whole
        naming consolidation exists to remove.
        """
        modules = [_resolved(("hlib",), _HELPER_LIB)]
        result = _verify_mod(_HELPER_MAIN, modules)
        deep = [
            d for d in result.diagnostics
            if d.location.line > len(_HELPER_MAIN.splitlines())
        ]
        assert deep, [
            (d.error_code, d.location.line) for d in result.diagnostics
        ]
        for d in deep:
            assert d.source_line.strip(), (
                f"{d.error_code} at line {d.location.line} has no excerpt"
            )

    def test_a_local_diagnostic_still_names_this_program(self) -> None:
        """Control: nothing moves for a diagnostic raised in the entry file."""
        result = _verify_mod(_QUOTE_MAIN, [_resolved(("qlib",), _QUOTE_LIB)])
        local = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(local) == 1
        assert local[0].source_line == _QUOTE_MAIN.splitlines()[
            local[0].location.line - 1
        ]


class TestMultiLineClauseIsQuotedWhole:
    """A clause broken across lines is quoted whole, not to its first line.

    The renderer sliced one physical line, so a wrapped `requires` was quoted
    mid-expression with unbalanced parentheses — a message naming a condition
    the program does not have (PR #1239 review).
    """

    _WRAPPED = """\
private fn needs_both(@Int, @Int -> @Int)
  requires(@Int.0 > 424242
           && @Int.1 > 424242)
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
  needs_both(1, 2)
}
"""

    def test_the_whole_clause_is_quoted(self) -> None:
        message = _e501(_verify_mod(self._WRAPPED, []))
        quoted = next(
            line.split("Precondition:", 1)[1].strip()
            for line in message.splitlines() if "Precondition:" in line
        )
        assert quoted == "requires(@Int.0 > 424242 && @Int.1 > 424242)", quoted
        assert quoted.count("(") == quoted.count(")"), quoted

    def test_a_single_line_clause_is_unchanged(self) -> None:
        """Control: the common case renders exactly as it always did."""
        single = self._WRAPPED.replace(
            "  requires(@Int.0 > 424242\n           && @Int.1 > 424242)",
            "  requires(@Int.0 > 424242 && @Int.1 > 424242)",
        )
        assert "\n           &&" not in single
        assert "requires(@Int.0 > 424242 && @Int.1 > 424242)" in _e501(
            _verify_mod(single, []))


class TestClosureInAPredicateTakesTheBinderSlot:
    """Characterization: a closure inside a predicate owns the first ``@T.n``.

    ``predicate_binder_ref`` documents "the first ``SlotRef`` in traversal
    order", and that is genuinely not the outermost one: a closure passed to a
    quantifier-like builtin introduces a binder of its own and the stack walk
    reaches it first.  The key derived from it therefore names the CLOSURE's
    parameter type, not the refinement's base (PR #1239 review).

    Pinned rather than fixed because the consequence is conservative: a value
    pushed under a key no reference resolves leaves the predicate
    untranslatable — a Tier-3 demotion, never a fact assumed about the wrong
    term — and the SMT refined-return path does not reach this shape at all (an
    ``Array`` base is outside its five modelled bases).  The test exists so the
    day someone makes the derivation outermost-first, this records what
    changed.
    """

    _CLOSURE_PREDICATE = """\
type Grown = { @Array<Nat> | array_all(@Array<Nat>.0, fn(@Nat -> @Bool) effects(pure) { @Nat.0 >= 18 }) };

private fn mk(@Array<Nat> -> @Grown)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<Nat>.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(mk(array_range(0, 0)))
}
"""

    def _predicate(
        self,
    ) -> tuple[ContractVerifier, ast.RefinementType]:
        prog = parse_to_ast(self._CLOSURE_PREDICATE)
        verifier = ContractVerifier(source=self._CLOSURE_PREDICATE)
        verifier.register_program(prog)
        body = verifier.env.type_aliases["Grown"].body
        assert isinstance(body, ast.RefinementType), body
        return verifier, body

    def test_the_closures_own_binder_is_found_first(self) -> None:
        from vera import naming
        from vera.naming import alias_env_from_environment

        verifier, refinement = self._predicate()
        ref = ast.predicate_binder_ref(refinement.predicate)
        assert ref is not None and ref.type_name == "Nat", ref
        env = alias_env_from_environment(verifier.env)
        assert naming.predicate_binder_key(refinement.predicate, env) == "Nat"
        # ... while the refinement's BASE — what the binder actually is —
        # renders differently, which is the whole point.
        assert naming.slot_name(refinement.base_type, env) == "Array<Nat>"

    def test_the_consequence_is_a_demotion_not_a_wrong_fact(self) -> None:
        """The direction that matters: nothing is claimed, nothing is rejected.

        No runtime oracle here: codegen cannot lower this predicate to a
        boundary guard, so the program compiles to no exports (a loud E617/E620
        chain, pre-existing and unrelated to the binder).  What the verifier
        must not do is either half of a wrong answer — reject the program, or
        claim a Tier-1 for a refinement it never translated.
        """
        result = _verify_mod(self._CLOSURE_PREDICATE, [])
        assert not _codes(result), _codes(result)
        refine = [o for o in result.obligations if o.kind == "refine_bind"]
        assert refine, [o.kind for o in result.obligations]
        assert all(o.status != "verified" for o in refine), [
            (o.fn_name, o.status, o.error_code) for o in refine
        ]


class TestObligationsCarryTheirDeclaringFile:
    """An obligation names the file its line number belongs to (#1220).

    The rendering fix moved DIAGNOSTICS onto the declaring module and left the
    obligation stream behind: `ProofObligation` had no file at all, so the CLI
    stamped the entry path on every entry and the documented
    ``(file, line, column)`` join between the two halves of ``verify --json``
    silently produced non-matches — and line numbers past the entry file's end
    (PR #1239 review).
    """

    def _verified(
        self, modules: list[ResolvedModule] | None = None,
    ) -> VerifyResult:
        if modules is None:
            modules = [_resolved(("hlib",), _HELPER_LIB)]
        prog = parse_to_ast(_HELPER_MAIN)
        # `file=` on BOTH legs, and from the constant `_verify_mod` uses, so
        # the assertions below compare against a known value rather than
        # against a literal that agrees with `_ENTRY_FILE` only by habit
        # (PR #1283 review).
        typecheck(
            prog, _HELPER_MAIN, resolved_modules=modules, file=_ENTRY_FILE)
        return verify(
            prog, _HELPER_MAIN, file=_ENTRY_FILE, resolved_modules=modules)

    def test_a_module_located_obligation_joins_its_diagnostic(self) -> None:
        result = self._verified()
        e501 = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(e501) == 1, [d.error_code for d in result.diagnostics]
        key = (e501[0].location.file, e501[0].location.line,
               e501[0].location.column)
        assert key in {(o.file, o.line, o.column) for o in result.obligations}, (
            f"no obligation joins the E501 at {key}: "
            f"{[(o.kind, o.file, o.line, o.column) for o in result.obligations]}"
        )
        assert key[0] != _ENTRY_FILE, key

    def test_an_entry_located_obligation_keeps_the_entry_file(self) -> None:
        """The control: `main`'s own contracts are still the entry file's."""
        result = self._verified()
        entry = [o for o in result.obligations if o.fn_name == "main"]
        assert entry, [o.fn_name for o in result.obligations]
        assert {o.file for o in entry} == {_ENTRY_FILE}, entry

    def test_no_obligation_cites_a_line_its_file_lacks(self) -> None:
        """The symptom that made the break visible without a join.

        BOTH files are bounded, not just the entry one: bounding the entry
        file alone leaves an obligation that names the MODULE free to cite any
        line at all, which is the same defect one file over.
        """
        module = _resolved(("hlib",), _HELPER_LIB)
        lengths = {
            _ENTRY_FILE: len(_HELPER_MAIN.splitlines()),
            str(module.file_path): len(_HELPER_LIB.splitlines()),
        }
        result = self._verified([module])
        seen = {o.file for o in result.obligations}
        assert seen == set(lengths), (seen, set(lengths))
        for o in result.obligations:
            assert o.line <= lengths[o.file], (o.kind, o.file, o.line)

    def test_the_warm_session_agrees_with_the_cold_run(self) -> None:
        """The warm incremental path reifies through the same recorder, so
        its stream must carry the same files — the differential oracle in
        test_obligations.py compares the two, and a field only one of them
        populated would slip through a fingerprint that ignores it."""
        from vera.obligations.session import VerificationSession

        # ONE module list for both runs: `_resolved` writes a fresh temp
        # file each call, so two lists would differ by path alone.
        modules = [_resolved(("hlib",), _HELPER_LIB)]
        cold = self._verified(modules)
        session = VerificationSession()
        warm = session.verify_source(
            _HELPER_MAIN, file=_ENTRY_FILE, resolved_modules=modules)
        assert [(o.kind, o.file, o.line, o.column) for o in warm.obligations] \
            == [(o.kind, o.file, o.line, o.column) for o in cold.obligations]


class TestQuotedClauseDropsComments:
    """A comment inside a multi-line clause is not quoted as code.

    Joining physical lines put a trailing `--` comment in front of the rest of
    the clause: the message showed a condition that stops where the comment
    starts, with the comment's prose reading as source (PR #1239 review).
    """

    _COMMENTED = """\
private fn needs_both(@Int, @Int -> @Int)
  requires(@Int.0 > 424242    -- the first bound
           && @Int.1 > 424242) -- and the second
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
  needs_both(1, 2)
}
"""

    _WITH_STRING = """\
private fn needs_tag(@String, @Int -> @Int)
  requires(string_contains(@String.0, "a--b")
           && @Int.0 > 424242)
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
  needs_tag("zz", 2)
}
"""

    @staticmethod
    def _quoted(source: str) -> str:
        message = _e501(_verify_mod(source, []))
        return next(
            line.split("Precondition:", 1)[1].strip()
            for line in message.splitlines() if "Precondition:" in line
        )

    def test_the_comments_are_not_quoted(self) -> None:
        quoted = self._quoted(self._COMMENTED)
        assert quoted == "requires(@Int.0 > 424242 && @Int.1 > 424242)", quoted
        assert "--" not in quoted, quoted
        assert quoted.count("(") == quoted.count(")"), quoted

    def test_a_double_dash_inside_a_string_survives(self) -> None:
        """The case a naive split on `--` would corrupt: the scanner is the
        lexer's own, so a string literal is not comment syntax."""
        quoted = self._quoted(self._WITH_STRING)
        assert '"a--b"' in quoted, quoted
        assert quoted.count("(") == quoted.count(")"), quoted

    _WITH_ANNOTATION = """\
private fn needs_both(@Int, @Int -> @Int)
  requires(@Int.0 > 424242 /* first bound */
           && @Int.1 > 424242)
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
  needs_both(1, 2)
}
"""

    def test_an_annotation_comment_is_blanked_too(self) -> None:
        """The third comment syntax, which the blanking fast path missed.

        Vera has three comment forms — `--` to end of line, `{- -}` nesting,
        and `/* */` annotation comments (spec §1.3) — and the early return
        that skips blanking checked only the first two.  A clause whose ONLY
        comment was an annotation therefore came back unblanked and was quoted
        with the comment inside it, which is the defect the blanking exists to
        prevent (PR #1239 review).
        """
        assert "--" not in self._WITH_ANNOTATION
        assert "{-" not in self._WITH_ANNOTATION
        quoted = self._quoted(self._WITH_ANNOTATION)
        assert quoted == "requires(@Int.0 > 424242 && @Int.1 > 424242)", quoted
        assert "/*" not in quoted and "first bound" not in quoted, quoted

    def test_an_uncommented_clause_is_unchanged(self) -> None:
        """Control: blanking must not touch a clause with no comment."""
        plain = self._COMMENTED.replace("    -- the first bound", "").replace(
            " -- and the second", "")
        assert "--" not in plain
        assert self._quoted(plain) == (
            "requires(@Int.0 > 424242 && @Int.1 > 424242)")
