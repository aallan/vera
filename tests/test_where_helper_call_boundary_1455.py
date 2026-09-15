"""#1455 — a call boundary obligates its argument wherever the callee is declared.

A parameter list is a binder position and an argument narrows into it, so the
obligation is derived from the callee's formals — which first requires knowing
which declaration the name reaches from the call.  The verifier's narrowing walk
asked ``env.functions``, the program-wide FLAT namespace.  Since #1378 a
``where`` helper is deliberately absent from it (spec §5.8: a helper is local to
its parent, and publishing it let a sibling's bare call resolve onto another
function's helper), so the lookup answered ``None``, ``param_types`` was
``None``, and the loop over the formals never ran.

The measured consequence, at ``origin/release/v0.2.0`` 8eca11c0:

* ``h(0 - 5)`` into a helper's ``@{ @Int | @Int.0 > 0 }`` parameter recorded
  NOTHING — not ``violated``, not ``tier3``, not ``tier3_unguarded`` — while
  the identical top-level spelling reported ``refine_bind``/``violated``/E505;
* the ``@Nat`` spelling lost its E503 the same way;
* codegen guarded the helper's parameter throughout, so ``vera verify``
  reported "4 verified (Tier 1)" on a program whose caller's ``ensures`` rested
  on a call that traps.

`git bisect --first-parent` over the 34 first-parent revisions from ``main``
6dc41d40 to the release tip names 2b2ef63f (PR #1378) as the first revision
that reports the where spelling clean.

The class is every obligation the call boundary raises, at every depth of
``where`` nesting, for every spelling of the narrowing — so the matrix below is
the differential against the top-level control rather than a list of statuses,
and its premise is that the control records something.  The PIPED spelling is
in it as the discriminating control in the other direction: a piped argument is
recovered from the checker's #747 target side-table with ``formal=None``, never
touching the registry, so it was correct throughout and stays correct.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera
from tests.codegen_helpers import _run_refine_trap
from tests.verifier_helpers import _verify

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])


# =====================================================================
# The issue's own reproducers, verbatim
# =====================================================================

#: The issue body's control — a top-level `h`, which behaved correctly.
_ISSUE_CONTROL = """type Pos = { @Int | @Int.0 > 0 };

private fn h(@Pos -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  @Pos.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  h(0 - 5)
}
"""

#: The issue body's spelling 1 — the same helper inside a `where` block.
_ISSUE_WHERE = """type Pos = { @Int | @Int.0 > 0 };

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  h(0 - 5)
}
where {
  fn h(@Pos -> @Int)
    requires(true)
    ensures(@Int.result > 0)
    effects(pure)
  {
    @Pos.0
  }
}
"""

#: The #1458 reviewer's comment reproducer, which pins the same site with an
#: inline refinement rather than a named one.
_COMMENT_REPRO = """public fn user(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  take(7)
}
where {
  fn take(@{ @Int | @Int.0 < 3 } -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    @Int.0
  }
}
"""


def _binds(source: str) -> list[tuple[str, str, str | None]]:
    """The narrowing obligations *source* records, as a sorted signature.

    Kind, status and error code together: a status alone would let a
    ``violated`` recorded with no code, or under the wrong kind, read as the
    control's answer.
    """
    result = _verify(source)
    return sorted(
        (o.kind, o.status, o.error_code or None)
        for o in result.obligations
        if o.kind in ("refine_bind", "nat_bind")
    )


def _error_codes(source: str) -> list[str]:
    """The error-severity diagnostic codes *source* verifies to, in order."""
    return [
        d.error_code
        for d in _verify(source).diagnostics
        if d.severity == "error"
    ]


class TestTheIssueReproducers:
    """The three programs the issue and its comment measure, as filed."""

    def test_the_control_obligates_and_refutes(self) -> None:
        """The premise for everything below: the top-level spelling records."""
        assert _binds(_ISSUE_CONTROL) == [("refine_bind", "violated", "E505")]

    def test_the_where_spelling_obligates_and_refutes_too(self) -> None:
        """The issue: this recorded NOTHING and reported `ok: true`."""
        assert _binds(_ISSUE_WHERE) == [("refine_bind", "violated", "E505")]

    def test_the_comment_reproducer_is_refuted(self) -> None:
        """`take(7)` against `@{ @Int | @Int.0 < 3 }`, the reviewer's shape."""
        assert _error_codes(_COMMENT_REPRO) == ["E505"]


# =====================================================================
# The class instrument: call spelling x refinement kind x callee position
# =====================================================================

_PRELUDE = {
    "refined": "type Pos = { @Int | @Int.0 > 0 };\n\n",
    "chain": (
        "type Pos = { @Int | @Int.0 > 0 };\n"
        "type Small = { @Pos | @Pos.0 < 10 };\n\n"
    ),
    "flat": "type Small = { @Int | @Int.0 > 0 && @Int.0 < 10 };\n\n",
    "nat": "",
}
_FORMAL = {
    "refined": "@Pos", "chain": "@Small", "flat": "@Small", "nat": "@Nat",
}
_BODY = {
    "refined": "@Pos.0", "chain": "@Small.0", "flat": "@Small.0",
    "nat": "nat_to_int(@Nat.0)",
}

#: The three spellings of the refinement the issue measures, plus `@Nat`.
#: `chain` and `flat` are logically the same predicate written two ways, and
#: the issue reports both silent — a refinement-machinery fix would have moved
#: one and not the other, which is why both are cells.
REFINEMENT_KINDS = ("refined", "chain", "flat", "nat")

#: `direct` is the broken spelling.  `piped` is the control in the other
#: direction: `left |> right()` desugars to a call the AST keeps as a
#: `BinaryExpr`, so the walk recovers the formal from the checker's target
#: side-table instead of the registry and was never affected.  Keeping it in
#: the matrix is what stops the fix from being stated more widely than it is.
CALL_SPELLINGS = (("direct", "h(0 - 5)"), ("piped", "(0 - 5) |> h()"))

#: Nesting depth of the callee.  `top` is the control; `where1` is the issue;
#: `where2` is a helper's own helper, which `where_helper_parents` records
#: against the helper that declares it and which a one-level fix would miss.
CALLEE_POSITIONS = ("top", "where1", "where2")


def _helper(kind: str, indent: int) -> str:
    pad = " " * indent
    return (
        f"{pad}fn h({_FORMAL[kind]} -> @Int)\n"
        f"{pad}  requires(true)\n"
        f"{pad}  ensures(true)\n"
        f"{pad}  effects(pure)\n"
        f"{pad}{{\n"
        f"{pad}  {_BODY[kind]}\n"
        f"{pad}}}\n"
    )


def _program(kind: str, position: str, call: str) -> str:
    """A minimal program calling `h` from *position* with *call*."""
    if position == "top":
        return _PRELUDE[kind] + "private " + _helper(kind, 0) + f"""
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {call}
}}
"""
    if position == "where1":
        return _PRELUDE[kind] + f"""public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {call}
}}
where {{
{_helper(kind, 2)}}}
"""
    return _PRELUDE[kind] + f"""public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  outer(())
}}
where {{
  fn outer(@Unit -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {{
    {call}
  }}
  where {{
{_helper(kind, 4)}  }}
}}
"""


class TestEveryCallBoundaryRecordsWhateverItsControlRecords:
    """24 cells: spelling x refinement kind x callee position.

    Eight of them — `direct` x the four kinds x the two `where` depths — were
    empty at 8eca11c0 while their `top` controls reported E505/E503.  The
    assertion is the differential rather than a literal status, so a compiler
    that stopped obligating ANY of the three positions fails rather than
    agreeing with itself; the separate control assertion supplies the premise
    that the answer being compared is not "nothing".
    """

    @pytest.mark.parametrize("spelling,call", CALL_SPELLINGS)
    @pytest.mark.parametrize("kind", REFINEMENT_KINDS)
    def test_the_control_records_a_narrowing(
        self, kind: str, spelling: str, call: str,
    ) -> None:
        """Premise: the top-level control is not silent, so the cells below
        are comparing against an answer rather than against an absence."""
        assert _binds(_program(kind, "top", call)), (
            f"{spelling}/{kind}: the top-level control records nothing, so "
            f"the where cells cannot be held to it"
        )

    @pytest.mark.parametrize("position", ("where1", "where2"))
    @pytest.mark.parametrize("spelling,call", CALL_SPELLINGS)
    @pytest.mark.parametrize("kind", REFINEMENT_KINDS)
    def test_a_where_helper_records_what_the_top_level_does(
        self, kind: str, spelling: str, call: str, position: str,
    ) -> None:
        control = _binds(_program(kind, "top", call))
        helper = _binds(_program(kind, position, call))
        assert helper == control, (
            f"{spelling}/{kind}/{position}: the helper spelling records "
            f"{helper} where the identical top-level one records {control}"
        )


# =====================================================================
# The false Tier 1: what the silence let through
# =====================================================================

class TestAProvedEnsuresDoesNotRestOnATrappingCall:
    """The ensures + run differential, which is what makes this a soundness
    defect rather than a reporting one.

    At 8eca11c0 this program reported "4 verified (Tier 1)" and trapped at
    `vera run`: the caller's `ensures(@Int.result > 0)` was discharged over a
    call whose argument the artifact refuses.  A proof that survives only
    because a runtime guard catches the counterexample is not a proof.
    """

    def test_the_call_is_refuted_rather_than_proved(self) -> None:
        assert _error_codes(_ISSUE_WHERE) == ["E505"]

    def test_the_artifact_still_refuses_the_value(self) -> None:
        """The other half of the differential: codegen was never the problem.

        The guard is planted and fires, before and after — the fix moves what
        the STREAM says, and this cell is what stops a future change from
        "fixing" the disagreement by removing the guard instead.
        """
        _run_refine_trap(_ISSUE_WHERE, fn="main")


# =====================================================================
# The second site the same mechanism reached
# =====================================================================

_GENERIC_HELPER = """type Pos = { @Int | @Int.0 > 0 };

public forall<T> fn g(@T -> @Pos)
  requires(true)
  ensures(true)
  effects(pure)
{
  h(())
}
where {
  fn h(@Unit -> @Int)
    requires(true)
    ensures(@Int.result > 0)
    effects(pure)
  {
    1
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""

_GENERIC_TOP = """type Pos = { @Int | @Int.0 > 0 };

private fn h(@Unit -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  1
}

public forall<T> fn g(@T -> @Pos)
  requires(true)
  ensures(true)
  effects(pure)
{
  h(())
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""


class TestTheGenericRefinedReturnReadsTheSameScope:
    """`_check_generic_refined_return` bound the flat registry as the SMT
    layer's callee lookup, so the same omission reached an UNINSTANTIATED
    generic's concrete refined return: the helper's `ensures` was invisible
    and the return fell to `tier3`/E506 where the top-level spelling proved.

    Precision rather than soundness — a demotion is honest — but the same
    mechanism, and the only other place a call was resolved against the flat
    table where a lexical scope applies.  `g` is never called, so the clone
    path does not run and this is the only route to the obligation.
    """

    def test_the_top_level_spelling_proves(self) -> None:
        result = _verify(_GENERIC_TOP)
        assert [(o.kind, o.status) for o in result.obligations
                if o.kind == "refine_bind"] == [("refine_bind", "verified")]

    def test_the_helper_spelling_proves_too(self) -> None:
        result = _verify(_GENERIC_HELPER)
        assert [(o.kind, o.status) for o in result.obligations
                if o.kind == "refine_bind"] == [("refine_bind", "verified")]


# =====================================================================
# The resolution is LEXICAL, not merely helper-aware
# =====================================================================

_SHADOWED = """type Pos = { @Int | @Int.0 > 0 };

private fn h(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

private fn other(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  h(0 - 5)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  h(0 - 5) + other(())
}
where {
  fn h(@Pos -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    @Pos.0
  }
}
"""


class TestTheCalleeIsResolvedWhereTheCallIsWritten:
    """A helper shadowing a top-level name of its own.

    A fix that merely made helpers findable again would answer either `h` here
    and be green on the reproducer.  The call inside `main` resolves to the
    HELPER (spec §5.8; the checker and codegen's `parent$where$h` mangling both
    say so), so the obligation is against `@Pos` and it is refuted; the SAME
    call text inside `other` resolves to the top-level `@Int` `h`, which
    narrows nothing and is obligated nothing.  Both readings come from one
    lexical chain, which is why one cell can hold them together.
    """

    def test_the_helper_shadows_for_its_own_parent(self) -> None:
        assert _binds(_SHADOWED) == [("refine_bind", "violated", "E505")]

    def test_and_the_sibling_call_still_reaches_the_top_level_one(self) -> None:
        """One record, not two: `other`'s `h(0 - 5)` obligates nothing,
        because the declaration IT reaches takes a plain `@Int`."""
        lines = sorted(
            o.line
            for o in _verify(_SHADOWED).obligations
            if o.kind == "refine_bind"
        )
        assert lines == [24], lines


# =====================================================================
# The fourth callee position: a module-qualified call
# =====================================================================

def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=600,
    )


_LIB = """type Pos = { @Int | @Int.0 > 0 };

public fn h(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Pos.0
}
"""

_IMPORTER = """import lib;

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  lib::h(0 - 5)
}
"""


class TestAModuleQualifiedCallIsObligatedToo:
    """The position `_callee_in_scope` routes DIFFERENTLY, pinned.

    A path names its module outright, so no lexical chain applies and the
    per-module registry answers instead of `smt._fn_lookup`.  That branch is
    unchanged by this PR, and the matrix above cannot reach it — every cell
    there is a bare call in one file.  A qualified call is therefore the one
    callee position whose obligation nothing here would notice the loss of,
    which is what makes it worth a cell rather than an argument (CodeRabbit
    on PR #1465).

    Measured before writing it: the qualified spelling does report E505
    today, so this is coverage of a working path, not a fix.
    """

    def test_a_refined_formal_across_an_import_is_refuted(
        self, tmp_path: Path,
    ) -> None:
        (tmp_path / "lib.vera").write_text(_LIB, encoding="utf-8")
        main = tmp_path / "main.vera"
        main.write_text(_IMPORTER, encoding="utf-8")
        proc = _cli("verify", "--json", str(main))
        envelope = json.loads(proc.stdout)
        binds = sorted(
            (o["kind"], o["status"], o.get("error_code"))
            for o in envelope["obligations"]
            if o["kind"] in ("refine_bind", "nat_bind")
        )
        assert binds == [("refine_bind", "violated", "E505")], (
            f"a module-qualified call into a refined formal records "
            f"{binds}; the same call in one file records "
            f"{_binds(_ISSUE_CONTROL)}"
        )
