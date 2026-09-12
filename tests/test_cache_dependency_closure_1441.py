"""#1441 — the warm session's cache key must cover what a proof actually reads.

`DischargeCache` keyed a function's entry on its own text, its program
context, and the interfaces of its DIRECT callees.  The reasoning recorded
for that last part was "transitive callees are read only by their own
callers", and it is false in one specific and reachable way: a callee's
CONTRACT may name other functions, and a caller that assumes that contract
reads those functions' interfaces without calling them.

    g  ensures(@Int.result == 1)
    f  ensures(@Int.result == g(()))   <- names g
    h  ensures(@Int.result == 1)       <- calls f, never mentions g

Editing `g` changes what `f`'s postcondition MEANS, so `h`'s proof stops
holding.  `g` and `f` were re-verified, `h` was replayed, and the warm
session reported `ok=True` where a fresh session on the same text reports
`violated`/E500.  The LSP proof-delta methods and `propose_edit` sit on this
session, so an editor could be told an edit still proves when it does not.

THE ORACLE IS A FRESH SESSION, NOT A LITERAL STATUS.  Every cell here runs
the edited text twice — once on the session that already saw the original,
once on a session that has never seen anything — and requires the two to
agree, obligation for obligation and diagnostic code for diagnostic code.  A
cell that asserted `violated` outright would go green for a compiler that
had stopped verifying anything at all.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vera.obligations.cache import interface_closure_names
from vera.obligations.session import VerificationSession

# ---------------------------------------------------------------------------
# Fixtures: each is (original, edited) differing in ONE declaration
# ---------------------------------------------------------------------------

#: #1441's own reproducer: the dependency runs through a callee's `ensures`.
_ENSURES_ORIGINAL = """public fn g(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  1
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == g(()))
  effects(pure)
{
  g(())
}

public fn h(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  f(())
}
"""

#: Positions preserved: `1` -> `2` in `g`'s postcondition and body.  A shifted
#: line would miss the cache for a reason that has nothing to do with #1441.
_ENSURES_EDITED = _ENSURES_ORIGINAL.replace(
    "ensures(@Int.result == 1)\n  effects(pure)\n{\n  1\n}",
    "ensures(@Int.result == 2)\n  effects(pure)\n{\n  2\n}",
    1,
)

#: The same shape through a `requires`: `needs`'s PREcondition names `lo`, so
#: a caller checking that precondition at its call site reads `lo`'s contract.
_REQUIRES_ORIGINAL = """public fn lo(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  1
}

public fn needs(@Int -> @Int)
  requires(@Int.0 >= lo(()))
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  needs(1)
}
"""

_REQUIRES_EDITED = _REQUIRES_ORIGINAL.replace(
    "ensures(@Int.result == 1)\n  effects(pure)\n{\n  1\n}",
    "ensures(@Int.result == 9)\n  effects(pure)\n{\n  9\n}",
    1,
)

#: THE CONTROL.  Only a BODY changes, and no contract anywhere refers to it,
#: so nothing a caller reads has moved: the caller must still be replayed.
#: Without this, "invalidate whenever anything changes" would pass every cell
#: above while throwing the optimisation away.
_BODY_ONLY_ORIGINAL = """public fn base(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  1
}

public fn user(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  base(())
}
"""

#: `1` -> `1 + 0`: a different body, the same contract, the same line count.
_BODY_ONLY_EDITED = _BODY_ONLY_ORIGINAL.replace("{\n  1\n}", "{\n  1 + 0\n}", 1)


def _summary(result) -> tuple[list[str], list[tuple[str, str, str]]]:
    """Everything a consumer would act on: error codes and obligation verdicts."""
    codes = sorted({d.error_code for d in result.diagnostics
                    if d.severity == "error"})
    obligations = sorted((o.fn_name, o.kind, o.status) for o in result.obligations)
    return codes, obligations


def _warm_then_fresh(tmp_path: Path, original: str, edited: str):
    """(warm-after-edit, fresh-on-edit, warm session) for one edit."""
    path = tmp_path / "p.vera"
    warm = VerificationSession()
    warm.verify_source(original, file=str(path))
    warm_edited = warm.verify_source(edited, file=str(path))
    fresh = VerificationSession()
    fresh_edited = fresh.verify_source(edited, file=str(path))
    return _summary(warm_edited), _summary(fresh_edited), warm


# ---------------------------------------------------------------------------
# The rule: a warm session agrees with a fresh one, for every edit
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "original,edited,caller,route",
    [
        (_ENSURES_ORIGINAL, _ENSURES_EDITED, "h", "ensures"),
        (_REQUIRES_ORIGINAL, _REQUIRES_EDITED, "caller", "requires"),
    ],
    ids=["through_ensures", "through_requires"],
)
def test_1441_a_dependency_two_calls_away_invalidates_the_caller(
    tmp_path: Path, original: str, edited: str, caller: str, route: str,
) -> None:
    """Warm equals fresh when the changed function is read through a contract.

    The premise is checked with the conclusion: the ORIGINAL must verify
    clean, or the edit is not what makes the difference.
    """
    path = tmp_path / "p.vera"
    warm = VerificationSession()
    before = warm.verify_source(original, file=str(path))
    assert _summary(before)[0] == [], (
        f"{route}: the original program does not verify clean, so this cell "
        f"measures something other than the edit — {_summary(before)}"
    )

    warm_edited = _summary(warm.verify_source(edited, file=str(path)))
    fresh = VerificationSession()
    fresh_edited = _summary(fresh.verify_source(edited, file=str(path)))

    assert warm_edited == fresh_edited, (
        f"{route}: the warm session and a fresh one disagree about the same "
        f"text — warm {warm_edited} vs fresh {fresh_edited}"
    )
    # And the disagreement it used to hide was a real one: the edit breaks
    # the caller, so this must not be two agreeing clean runs.
    assert warm_edited[0], (
        f"{route}: the edit was expected to break {caller}, and nothing was "
        f"reported — the fixture no longer exercises the bug"
    )


def test_1441_the_broken_caller_is_the_one_the_edit_reaches(
    tmp_path: Path,
) -> None:
    """Not just 'some error': `h`'s postcondition is what stops holding.

    `g` and `f` still verify — their own contracts are consistent with their
    own bodies — and `h`, which never mentions `g`, is the one that breaks.
    """
    warm_edited, fresh_edited, _ = _warm_then_fresh(
        tmp_path, _ENSURES_ORIGINAL, _ENSURES_EDITED)
    assert warm_edited == fresh_edited
    codes, obligations = warm_edited
    assert "E500" in codes, codes
    statuses = {(fn, kind): status for fn, kind, status in obligations}
    assert statuses[("h", "ensures")] == "violated", obligations
    assert statuses[("g", "ensures")] == "verified", obligations
    assert statuses[("f", "ensures")] == "verified", obligations


def test_1441_a_body_only_edit_still_replays_its_callers(
    tmp_path: Path,
) -> None:
    """The optimisation survives: a body no contract reads invalidates nobody.

    A fix that invalidated on any local change would satisfy every cell above
    and cost the cache its purpose, so the cheap direction is pinned too —
    `user` must be REPLAYED, which is a count, because replay is the claim.
    """
    path = tmp_path / "p.vera"
    warm = VerificationSession()
    warm.verify_source(_BODY_ONLY_ORIGINAL, file=str(path))
    warm_edited = _summary(warm.verify_source(_BODY_ONLY_EDITED, file=str(path)))
    replayed = warm.last_run_stats.replayed_fns

    fresh = VerificationSession()
    fresh_edited = _summary(fresh.verify_source(_BODY_ONLY_EDITED, file=str(path)))

    assert warm_edited == fresh_edited, (warm_edited, fresh_edited)
    assert warm_edited[0] == [], f"the control must stay clean — {warm_edited}"
    assert replayed >= 1, (
        "a body-only edit invalidated every caller, so the closure is being "
        "computed over bodies rather than over contracts"
    )



def _decl(name: str, *, contract_call: str | None, body_call: str | None):
    """A minimal `FnDecl` naming a function in its contract and/or its body.

    Hand-built rather than parsed: the shapes these two cells need — a
    contract CYCLE, and a body reference that must stay out of the closure —
    are refused earlier in the pipeline or need a whole program to express,
    while the walk has to be total over whatever `fn_map` it is handed.
    """
    from vera import ast as a

    contracts = ()
    if contract_call is not None:
        contracts = (a.Ensures(expr=a.FnCall(name=contract_call, args=())),)
    body = a.Block(
        statements=(),
        expr=a.FnCall(name=body_call, args=()) if body_call else a.IntLit(value=0),
    )
    return a.FnDecl(
        name=name, forall_vars=None, forall_constraints=None,
        params=(), return_type=a.NamedType(name="Int", type_args=None),
        contracts=contracts, effect=a.PureEffect(), body=body, where_fns=None,
    )


# ---------------------------------------------------------------------------
# Cycles, and the closure itself
# ---------------------------------------------------------------------------

def test_1441_the_closure_terminates_on_a_contract_cycle() -> None:
    """Contracts may refer to each other; the walk must stop anyway.

    A unit rather than a program, because a contract cycle between two
    top-level functions is refused earlier in the pipeline — the walk still
    has to be total over whatever `fn_map` it is handed, and a caller of a
    cyclic pair reads BOTH interfaces.
    """
    def fn(name: str, mentions: str):
        return _decl(name, contract_call=mentions, body_call=None)

    # a's contract names b, b's names a — the cycle the visited set exists for.
    fn_a, fn_b = fn("a", "b"), fn("b", "a")
    fn_map = {"a": fn_a, "b": fn_b}

    caller = fn("caller", "a")
    names = interface_closure_names(caller, fn_map, {})
    assert names == frozenset({"a", "b"}), names


def test_1441_the_closure_follows_contracts_and_not_bodies() -> None:
    """The distinction the body-only optimisation rests on, asserted directly.

    A function named only in a callee's BODY is not read by that callee's
    callers, so it must stay out of the closure; one named in its CONTRACT
    must be in it.
    """
    def fn(name: str, *, in_contract: str | None,
           in_body: str | None):
        return _decl(name, contract_call=in_contract, body_call=in_body)

    callee = fn("callee", in_contract="seen", in_body="unseen")
    fn_map = {
        "callee": callee,
        "seen": fn("seen", in_contract=None, in_body=None),
        "unseen": fn("unseen", in_contract=None, in_body=None),
    }
    caller = fn("caller", in_contract=None, in_body="callee")

    names = interface_closure_names(caller, fn_map, {})
    assert "callee" in names, names
    assert "seen" in names, (
        "a function named in a callee's CONTRACT is read by that callee's "
        f"callers and must be in the closure — {names}"
    )
    assert "unseen" not in names, (
        "a function named only in a callee's BODY is not read across the call "
        f"boundary; including it would cost the body-only optimisation — {names}"
    )


# ---------------------------------------------------------------------------
# The signature half: refinement predicates on a callee's parameter / return
# ---------------------------------------------------------------------------

#: A caller reads more of a callee than its contracts.  It takes the
#: refinements on the callee's PARAMETER types (checking them at the call
#: site) and on its RETURN type (assuming them afterwards) — and a refinement
#: predicate may call a function, so reading the signature reads that
#: function's contract.  Walking `contracts` alone missed it, and the first
#: version of this fix did exactly that (#1458 review).
#:
#: A NAMED type hides the predicate behind an alias, so the closure has to
#: resolve through `alias_map`; #1453 made alias CHAINS real, which the third
#: fixture below walks.
_RETURN_ORIGINAL = """public fn cap(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 2)
  effects(pure)
{
  2
}

type Small = { @Int | @Int.0 < cap(()) };

public fn mk(@Unit -> @Small)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

public fn use_it(@Unit -> @Int)
  requires(true)
  ensures(@Int.result < 3)
  effects(pure)
{
  mk(())
}
"""

#: `cap` 2 -> 9 widens `Small`, so `use_it` can no longer conclude `< 3` from
#: `mk`'s return type.  `mk` itself still verifies (1 is below either bound),
#: which is what makes the caller the only thing that moves.
_RETURN_EDITED = _RETURN_ORIGINAL.replace(
    "ensures(@Int.result == 2)\n  effects(pure)\n{\n  2\n}",
    "ensures(@Int.result == 9)\n  effects(pure)\n{\n  9\n}",
    1,
)

#: The parameter half.  `needs` takes a refined PARAMETER, so `caller`
#: discharges that refinement at its call site; raising the floor makes the
#: argument illegal and the call site is where it is caught (E505).
_PARAM_ORIGINAL = """public fn floor_of(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{
  0
}

type Pos = { @Int | @Int.0 > floor_of(()) };

public fn needs(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Pos.0
}

public fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  needs(1)
}
"""

_PARAM_EDITED = _PARAM_ORIGINAL.replace(
    "ensures(@Int.result == 0)\n  effects(pure)\n{\n  0\n}",
    "ensures(@Int.result == 5)\n  effects(pure)\n{\n  5\n}",
    1,
)

#: Two alias hops between the signature and the refinement that names `cap`.
_CHAIN_ORIGINAL = _RETURN_ORIGINAL.replace(
    "type Small = { @Int | @Int.0 < cap(()) };",
    "type Small = { @Int | @Int.0 < cap(()) };\n\ntype Tiny = Small;\n\n"
    "type Wee = Tiny;",
    1,
).replace("public fn mk(@Unit -> @Small)", "public fn mk(@Unit -> @Wee)", 1)

_CHAIN_EDITED = _CHAIN_ORIGINAL.replace(
    "ensures(@Int.result == 2)\n  effects(pure)\n{\n  2\n}",
    "ensures(@Int.result == 9)\n  effects(pure)\n{\n  9\n}",
    1,
)


@pytest.mark.parametrize(
    "original,edited,route",
    [
        (_RETURN_ORIGINAL, _RETURN_EDITED, "refined return type"),
        (_PARAM_ORIGINAL, _PARAM_EDITED, "refined parameter type"),
        (_CHAIN_ORIGINAL, _CHAIN_EDITED, "refinement two alias hops away"),
    ],
    ids=["through_refined_return", "through_refined_parameter",
         "through_an_alias_chain"],
)
def test_1458_a_refinement_predicate_is_part_of_the_interface(
    tmp_path: Path, original: str, edited: str, route: str,
) -> None:
    """Warm equals fresh when the changed function is read through a TYPE.

    Measured with the closure walking contracts only: warm reported the
    caller `verified` where a fresh session reports `violated` — E500 for the
    return route, E505 for the parameter route, since the parameter's
    refinement is discharged at the call site rather than assumed after it.
    `propose_edit` sits on this session and would have answered
    `should_apply=True`.
    """
    path = tmp_path / "p.vera"
    warm = VerificationSession()
    before = _summary(warm.verify_source(original, file=str(path)))
    assert before[0] == [], (
        f"{route}: the original does not verify clean, so this cell measures "
        f"something other than the edit — {before}"
    )

    warm_edited = _summary(warm.verify_source(edited, file=str(path)))
    fresh_edited = _summary(
        VerificationSession().verify_source(edited, file=str(path)))

    assert warm_edited == fresh_edited, (
        f"{route}: warm {warm_edited} vs fresh {fresh_edited}"
    )
    assert warm_edited[0], (
        f"{route}: the edit was expected to break the caller and nothing was "
        f"reported — the fixture no longer exercises the bug"
    )


def test_1458_editing_only_the_predicates_helper_body_still_replays(
    tmp_path: Path,
) -> None:
    """The control for the signature half: a BODY is still not read.

    `cap`'s body changes and its contract does not, so nothing any caller
    reads has moved — the refinement quotes `cap`'s postcondition, never its
    body.  Without this, "any function reachable from a signature invalidates
    everything" would satisfy the three cells above and throw the
    optimisation away for every refined type in the file.
    """
    edited = _RETURN_ORIGINAL.replace("{\n  2\n}", "{\n  1 + 1\n}", 1)
    assert edited != _RETURN_ORIGINAL
    assert "ensures(@Int.result == 2)" in edited, "the contract must not move"

    path = tmp_path / "p.vera"
    warm = VerificationSession()
    warm.verify_source(_RETURN_ORIGINAL, file=str(path))
    warm_edited = _summary(warm.verify_source(edited, file=str(path)))
    replayed = warm.last_run_stats.replayed_fns
    fresh_edited = _summary(
        VerificationSession().verify_source(edited, file=str(path)))

    assert warm_edited == fresh_edited, (warm_edited, fresh_edited)
    assert warm_edited[0] == [], f"the control must stay clean — {warm_edited}"
    assert replayed >= 1, (
        "a body-only edit invalidated every caller, so the closure is "
        "following bodies through signature types rather than refinements"
    )


# ---------------------------------------------------------------------------
# The edit-sequence differential
# ---------------------------------------------------------------------------

#: SEVERAL edits on ONE session, because that is how the session is used and
#: it is not what the cells above test.  A cache that invalidates correctly
#: for a single edit can still go stale on the third, when an entry stored
#: under an earlier program's key is reachable again — and the existing
#: warm/cold corpus oracle cannot see any of it, because it replays an
#: UNCHANGED corpus, where every replay is trivially right.
_SEQUENCES: dict[str, tuple[str, tuple[tuple[str, str], ...]]] = {
    # The issue's shape, walked through three states and back to the first.
    "ensures_chain": (
        _ENSURES_ORIGINAL,
        (
            ("== 1)\n  effects(pure)\n{\n  1\n}", "== 2)\n  effects(pure)\n{\n  2\n}"),
            ("== 2)\n  effects(pure)\n{\n  2\n}", "== 3)\n  effects(pure)\n{\n  3\n}"),
            ("== 3)\n  effects(pure)\n{\n  3\n}", "== 1)\n  effects(pure)\n{\n  1\n}"),
        ),
    ),
    # Through a precondition, then back.
    "requires_chain": (
        _REQUIRES_ORIGINAL,
        (
            ("== 1)\n  effects(pure)\n{\n  1\n}", "== 9)\n  effects(pure)\n{\n  9\n}"),
            ("== 9)\n  effects(pure)\n{\n  9\n}", "== 0)\n  effects(pure)\n{\n  0\n}"),
        ),
    ),
    # Contract edits interleaved with body-only ones: the entry for `user` is
    # invalidated and restored repeatedly, so a key that is right once but not
    # stable across the sequence shows up here.
    "mixed": (
        _BODY_ONLY_ORIGINAL,
        (
            ("{\n  1\n}", "{\n  1 + 0\n}"),
            ("ensures(@Int.result >= 0)", "ensures(@Int.result >= 1)"),
            ("{\n  1 + 0\n}", "{\n  2\n}"),
        ),
    ),
}


@pytest.mark.parametrize("name", sorted(_SEQUENCES))
def test_1441_a_sequence_of_edits_never_diverges_from_fresh(
    tmp_path: Path, name: str,
) -> None:
    """After every edit in a session's life, warm equals fresh.

    The comparison is the whole reported surface — error codes and every
    obligation's `(function, kind, status)` — so a divergence anywhere in the
    program is caught, not just at the function the edit named.
    """
    path = tmp_path / "p.vera"
    source, edits = _SEQUENCES[name]
    warm = VerificationSession()
    warm.verify_source(source, file=str(path))

    for step, (old, new) in enumerate(edits, start=1):
        assert source.count(old) >= 1, (
            f"{name} step {step}: the edit anchor {old!r} is absent, so this "
            f"step changes nothing and the sequence proves less than it reads"
        )
        source = source.replace(old, new, 1)

        warm_result = _summary(warm.verify_source(source, file=str(path)))
        fresh_result = _summary(
            VerificationSession().verify_source(source, file=str(path)))
        assert warm_result == fresh_result, (
            f"{name} step {step}: warm {warm_result} vs fresh {fresh_result}"
        )
