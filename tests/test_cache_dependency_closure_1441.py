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

from vera import ast
from vera.obligations.cache import (
    TypeEnvironment,
    _type_reference_calls,
    interface_closure_names,
)
from vera.obligations.session import VerificationSession

from tests.module_fixture_helpers import resolved_module

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


#: A program with no type, data or effect declarations in it — the two
#: unit cells below are about the CONTRACT half of the walk, so nothing
#: they hand it resolves through a declaration.
_EMPTY_ENV = TypeEnvironment(types={}, constructors={}, effect_ops={})


def _summary(result) -> tuple[list[str], list[tuple[str, str, str, str]]]:
    """Everything a consumer would act on: error codes and obligation verdicts."""
    codes = sorted({d.error_code for d in result.diagnostics
                    if d.severity == "error"})
    # `owner` is part of the identity, not decoration: `_record_obligation`
    # keeps a `where` helper's top-level owner beside its bare `fn_name`, and
    # `_scoped_fn_lookup` resolves same-named helpers per owner, so two
    # helpers called `h` in different owners can hold different verdicts.
    # Keyed on the bare name they collapse onto one triple, and an
    # invalidation that swapped their verdicts would read as agreement
    # (#1458 review).
    obligations = sorted(
        (o.fn_name, o.owner, o.kind, o.status) for o in result.obligations)
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
    statuses = {(fn, kind): status for fn, _owner, kind, status in obligations}
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
    names = interface_closure_names(caller, fn_map, _EMPTY_ENV)
    assert names == frozenset({"a", "b"}), names


def test_1458_the_signature_walk_terminates_on_an_alias_cycle() -> None:
    """`_type_reference_calls` is total over any alias map it is handed.

    An alias cycle is refused earlier in the pipeline (E-coded at check
    time), but the walk runs over whatever map the session builds and must
    terminate regardless — `seen_aliases` is the only thing that makes it
    so, and nothing else in this file hands it a cycle.  The contract half
    has the same cell one section up.
    """
    type_defs: dict[str, tuple[ast.TypeExpr, ...]] = {
        "A": (ast.NamedType(name="B", type_args=None),),
        "B": (ast.NamedType(name="A", type_args=None),),
    }

    found: set[str] = set()
    _type_reference_calls(
        (ast.NamedType(name="A", type_args=None),), type_defs, found)
    assert found == set(), found


def test_1458_the_type_walk_terminates_on_a_recursive_data_declaration() -> None:
    """The same totality, for the shape a `data` declaration makes reachable.

    `data List<T> { Nil, Cons(T, List<T>) }` names itself in its own field,
    and unlike an alias cycle that is LEGAL — so the walk meets it in
    ordinary programs rather than only in a malformed one.  The name enters
    the seen set before its definition is pushed, which is what makes the
    self-reference a stop rather than a loop; the predicate on the other
    field must still come out.
    """
    predicate = ast.RefinementType(
        base_type=ast.NamedType(name="Int", type_args=None),
        predicate=ast.FnCall(
            name="cap",
            args=(),
        ),
    )
    type_defs: dict[str, tuple[ast.TypeExpr, ...]] = {
        "List": (predicate, ast.NamedType(name="List", type_args=None)),
    }

    found: set[str] = set()
    _type_reference_calls(
        (ast.NamedType(name="List", type_args=None),), type_defs, found)
    assert found == {"cap"}, found


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

    names = interface_closure_names(caller, fn_map, _EMPTY_ENV)
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
#: resolve through `type_defs`; #1453 made alias CHAINS real, which the third
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
            # `user` now leans on `base`'s bound, and the next step takes that
            # bound away: without a state that BREAKS, every step of this
            # sequence is valid and warm agrees with fresh whatever the cache
            # does (#1458 review).  The step after restores it, so the
            # sequence also exercises re-proving something it refuted.
            ("ensures(@Int.result >= 0)", "ensures(@Int.result >= 1)"),
            ("ensures(@Int.result >= 1)", "ensures(@Int.result >= 0)"),
            ("ensures(@Int.result >= 0)", "ensures(@Int.result >= 1)"),
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
    seen_codes: set[str] = set()

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
        seen_codes.update(warm_result[0])

    assert seen_codes, (
        f"{name}: no state in this sequence reported an error, so every step "
        f"agreed for a program that was valid throughout — a cache that never "
        f"invalidated would pass it unchanged (#1458 review)"
    )


# ---------------------------------------------------------------------------
# The class matrix: every kind of thing a cached proof depends on
# ---------------------------------------------------------------------------

#: #1441 was reported as one instance — a helper named in a callee's
#: `ensures`.  The CLASS is "a cached proof survives a change to something it
#: depends on", and the cells below are the enumeration of what a proof in
#: this compiler can depend on, taken from the two components the key is
#: built out of rather than from the shapes that happened to be reported:
#: `callee_component` (the interface closure) covers everything
#: function-shaped, and `program_context_hash` covers every declaration that
#: is not a function.  A dependency kind neither component reaches is a hole
#: in the key.
#:
#: Vera has no constant declaration form — a named constant is a nullary
#: function — so "a constant changed" is the callee-contract rows.
#:
#: The dedicated cells above pin the specifics of the routes that were
#: broken (which function moves, which diagnostic code, whether the caller
#: replays).  This matrix is the sweep: one assertion, over the whole space.

#: The direct route, with no intermediary: `f` assumes `g`'s postcondition.
_DIRECT_ORIGINAL = """public fn g(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  1
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  g(())
}
"""

_DIRECT_EDITED = _DIRECT_ORIGINAL.replace(
    "ensures(@Int.result == 1)\n  effects(pure)\n{\n  1\n}",
    "ensures(@Int.result == 2)\n  effects(pure)\n{\n  2\n}",
    1,
)

#: Removal is the other edit a dependency admits: `g` disappears, so `f`'s
#: postcondition names something that is not there.
_CALLEE_REMOVED = _ENSURES_ORIGINAL.replace(
    """public fn g(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  1
}

""",
    "",
    1,
)

#: A refinement predicate written inline, with no function in it at all —
#: the alias TEXT is the dependency, and the program context hash is what
#: covers it.
_ALIAS_ORIGINAL = """type Small = { @Int | @Int.0 < 3 };

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

_ALIAS_WIDENED = _ALIAS_ORIGINAL.replace("@Int.0 < 3 }", "@Int.0 < 9 }", 1)
_ALIAS_REMOVED = _ALIAS_ORIGINAL.replace(
    "type Small = { @Int | @Int.0 < 3 };\n\n", "", 1)

_ADT_ORIGINAL = """public data Sign { Neg, Zero, Pos }

public fn rank(@Sign -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Sign.0 {
    Neg -> 0,
    Zero -> 1,
    Pos -> 2
  }
}
"""

_ADT_VARIANT_ADDED = _ADT_ORIGINAL.replace(
    "{ Neg, Zero, Pos }", "{ Neg, Zero, Pos, Huge }", 1)
_ADT_REMOVED = _ADT_ORIGINAL.replace(
    "public data Sign { Neg, Zero, Pos }\n\n", "", 1)

_EFFECT_ORIGINAL = """effect Counter {
  op bump(Int -> Int);
}

public fn use_c(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(<Counter>)
{
  Counter.bump(@Int.0)
}
"""

_EFFECT_RETYPED = _EFFECT_ORIGINAL.replace(
    "op bump(Int -> Int);", "op bump(Bool -> Int);", 1)

#: An imported module's surface: the caller reads `cap`'s contract across a
#: module boundary, where the closure cannot follow it — the session's
#: per-module (path, source digest) keys are what covers this.
_MODULE_LIB = """module lib;

public fn cap(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  1
}
"""

_MODULE_LIB_WEAKENED = _MODULE_LIB.replace(
    "== 1)\n  effects(pure)\n{\n  1\n}",
    "== 9)\n  effects(pure)\n{\n  9\n}",
    1,
)

_MODULE_LIB_UNEXPORTED = _MODULE_LIB.replace(
    "public fn cap", "private fn cap", 1)

_MODULE_MAIN = """import lib(cap);

public fn use_mod(@Unit -> @Int)
  requires(true)
  ensures(@Int.result < 3)
  effects(pure)
{
  cap(())
}
"""


def _lib(source: str) -> list:
    return [resolved_module(("lib",), source)]


#: The dependency an owner reads through its OWN `where` helper's signature.
#: `mk` is a helper, so it is not in `fn_map` and the closure never resolved
#: its name; its return type's refinement names `cap`, which the owner assumes
#: after the call.  Measured before the fix (#1458 review): warm reported
#: `owner` `verified` where a fresh session reports `violated` with E500.
_WHERE_SIG_ORIGINAL = """public fn cap(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 2)
  effects(pure)
{
  2
}

type Small = { @Int | @Int.0 < cap(()) };

public fn owner(@Unit -> @Int)
  requires(true)
  ensures(@Int.result < 3)
  effects(pure)
{
  mk(())
}
where {
  fn mk(@Unit -> @Small)
    requires(true)
    ensures(true)
    effects(pure)
  {
    1
  }
}
"""

_WHERE_SIG_EDITED = _WHERE_SIG_ORIGINAL.replace(
    "ensures(@Int.result == 2)\n  effects(pure)\n{\n  2\n}",
    "ensures(@Int.result == 9)\n  effects(pure)\n{\n  9\n}",
    1,
)

#: The carrier dimension: a refinement predicate reached through an ADT FIELD
#: rather than through an alias target.  A `data` declaration's field types
#: are read at construction and at destructure, so a predicate behind one is
#: as live as a predicate on a signature — and the closure resolved names
#: through type aliases only, so all four rows below were warm-clean where a
#: fresh session refutes (#1458 review).
_ADT_CARRIER_PRELUDE = """public fn cap(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 5)
  effects(pure)
{
  5
}

type Small = { @Int | @Int.0 < cap(()) };
"""

#: Widening `cap` widens `Small`, so a caller can no longer conclude its own
#: bound.  Positions preserved, so nothing moves for a reason other than the
#: edit.
_CAP_WIDENED = (
    "ensures(@Int.result == 5)\n  effects(pure)\n{\n  5\n}",
    "ensures(@Int.result == 9)\n  effects(pure)\n{\n  9\n}",
)

#: Tightening it instead makes a value that WAS legal illegal, which is
#: caught where the value is built rather than where it is read.
_CAP_TIGHTENED = (
    "ensures(@Int.result == 5)\n  effects(pure)\n{\n  5\n}",
    "ensures(@Int.result == 1)\n  effects(pure)\n{\n  1\n}",
)

_ADT_RETURN_ORIGINAL = _ADT_CARRIER_PRELUDE + """
public data Box { B(Small) }

public fn mk(@Unit -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{
  B(1)
}

public fn use_it(@Unit -> @Int)
  requires(true)
  ensures(@Int.result < 5)
  effects(pure)
{
  match mk(()) {
    B(@Small) -> @Small.0
  }
}
"""

_ADT_PARAM_ORIGINAL = _ADT_CARRIER_PRELUDE + """
public data Box { B(Small) }

public fn peek(@Box -> @Int)
  requires(true)
  ensures(@Int.result < 5)
  effects(pure)
{
  match @Box.0 {
    B(@Small) -> @Small.0
  }
}
"""

_ADT_BUILD_ORIGINAL = _ADT_CARRIER_PRELUDE + """
public data Box { B(Small) }

public fn build(@Unit -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{
  B(3)
}
"""

_LET_ALIAS_ORIGINAL = _ADT_CARRIER_PRELUDE + """
public fn user(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Small = 3;
  @Small.0
}
"""

#: The control that localises the four above to the TYPE walk: written
#: inline, the same predicate is an `FnCall` inside the declaration, which
#: `direct_callee_names` finds without resolving any type name at all.  It
#: agreed warm-with-fresh before the fix and must keep doing so after.
_LET_INLINE_ORIGINAL = """public fn cap(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 5)
  effects(pure)
{
  5
}

public fn user(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @{ @Int | @Int.0 < cap(()) } = 3;
  @Int.0
}
"""

#: The routes that name a VALUE rather than a type.  A declaration reads
#: types it never writes: `B(3)` reads `B`'s field types and mentions no
#: type at all, and `Counter.bump(3)` reads the operation's signature, which
#: lives in the effect declaration.  Both were warm-clean where a fresh
#: session refutes with E505 (#1458 review).
#:
#: `build2` binds the payload at `@Int` rather than at `@Small` on purpose:
#: spelling the binder at the refined type would write the name and seed the
#: walk directly, which is what the `adt_field_at_construction` row above
#: does through its `-> @Box` return.
_CTOR_CALL_ORIGINAL = _ADT_CARRIER_PRELUDE + """
public data Box { B(Small) }

public fn build2(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match B(3) {
    B(@Int) -> @Int.0
  }
}
"""

_OP_CALL_ORIGINAL = _ADT_CARRIER_PRELUDE + """
effect Counter {
  op bump(Small -> Int);
}

public fn use_c(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Counter>)
{
  Counter.bump(3)
}
"""

#: A type-correct ADT edit: the wildcard arm is unreachable while `Sign` has
#: three constructors, so `rank` proves its bound; a fourth constructor makes
#: it reachable and the bound false.  The earlier version of this row added a
#: constructor with no wildcard, which is an EXHAUSTIVENESS error — the
#: checker refuses, verification never runs, and the row passed against a
#: cache key that had been replaced by a constant (#1458 review).
_ADT_WILDCARD_ORIGINAL = """public data Sign { Neg, Zero, Pos }

public fn rank(@Sign -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Sign.0 {
    Neg -> 0,
    Zero -> 1,
    Pos -> 2,
    _ -> 0 - 1
  }
}
"""

_ADT_WILDCARD_EDITED = _ADT_WILDCARD_ORIGINAL.replace(
    "{ Neg, Zero, Pos }", "{ Neg, Zero, Pos, Huge }", 1)

#: (dependency kind, edit kind, original, edited, modules before, after).
#: Two dimensions, both taken from the code that computes the key rather
#: than from the shapes that were reported: WHERE the type is written (a
#: parameter, a return, a `where` helper's signature, a `let` annotation, a
#: callee's signature) and HOW the refinement is reached from there (inline,
#: through an alias, through a chain of aliases, through an ADT field).
#:
#: Every row here leaves the edited program type-correct, so everything it
#: moves moved in the proof and the row can hold the cache key to account.
#: An edit that makes the CHECKER refuse is a different instrument — the
#: checker re-runs on the warm path and the cold one alike, so agreement
#: there is architecture — and lives in `_CHECK_PHASE_GUARDS` below rather
#: than being counted here.
#:
#: Two rows are held by the span-sensitive structural hash rather than by
#: the closure or the context hash, because their edit deletes lines and
#: every later declaration shifts: `callee_removed` and `adt_removed`.  They
#: are kept — the invalidation they pin is real — and named so the table
#: does not claim them for a component that is not carrying them.
_CLASS_MATRIX = [
    ("callee contract, direct", "contract weakened",
     _DIRECT_ORIGINAL, _DIRECT_EDITED, None, None),
    ("callee contract, one hop through `ensures`", "contract weakened",
     _ENSURES_ORIGINAL, _ENSURES_EDITED, None, None),
    ("callee contract, one hop through `requires`", "contract weakened",
     _REQUIRES_ORIGINAL, _REQUIRES_EDITED, None, None),
    ("refinement on a callee's return type", "contract weakened",
     _RETURN_ORIGINAL, _RETURN_EDITED, None, None),
    ("refinement on a callee's parameter type", "contract weakened",
     _PARAM_ORIGINAL, _PARAM_EDITED, None, None),
    ("refinement two alias hops away", "contract weakened",
     _CHAIN_ORIGINAL, _CHAIN_EDITED, None, None),
    ("refinement on a `where` helper's return type", "contract weakened",
     _WHERE_SIG_ORIGINAL, _WHERE_SIG_EDITED, None, None),
    ("refinement behind an ADT field, read through a callee's return",
     "contract weakened", _ADT_RETURN_ORIGINAL,
     _ADT_RETURN_ORIGINAL.replace(*_CAP_WIDENED, 1), None, None),
    ("refinement behind an ADT field, on the function's own parameter",
     "contract weakened", _ADT_PARAM_ORIGINAL,
     _ADT_PARAM_ORIGINAL.replace(*_CAP_WIDENED, 1), None, None),
    ("refinement behind an ADT field, discharged at construction",
     "contract weakened", _ADT_BUILD_ORIGINAL,
     _ADT_BUILD_ORIGINAL.replace(*_CAP_TIGHTENED, 1), None, None),
    ("refinement behind an alias, on a `let` annotation", "contract weakened",
     _LET_ALIAS_ORIGINAL, _LET_ALIAS_ORIGINAL.replace(*_CAP_TIGHTENED, 1),
     None, None),
    ("refinement written inline, on a `let` annotation", "contract weakened",
     _LET_INLINE_ORIGINAL, _LET_INLINE_ORIGINAL.replace(*_CAP_TIGHTENED, 1),
     None, None),
    ("refinement behind an ADT field, reached through a CONSTRUCTOR CALL",
     "contract weakened", _CTOR_CALL_ORIGINAL,
     _CTOR_CALL_ORIGINAL.replace(*_CAP_TIGHTENED, 1), None, None),
    ("refinement on an effect operation's parameter, reached through a "
     "QUALIFIED CALL", "contract weakened", _OP_CALL_ORIGINAL,
     _OP_CALL_ORIGINAL.replace(*_CAP_TIGHTENED, 1), None, None),
    ("callee", "declaration removed",
     _ENSURES_ORIGINAL, _CALLEE_REMOVED, None, None),
    ("type alias refinement", "definition changed",
     _ALIAS_ORIGINAL, _ALIAS_WIDENED, None, None),
    ("ADT constructors", "definition changed",
     _ADT_WILDCARD_ORIGINAL, _ADT_WILDCARD_EDITED, None, None),
    ("ADT", "declaration removed",
     _ADT_ORIGINAL, _ADT_REMOVED, None, None),
    ("imported module contract", "contract weakened",
     _MODULE_MAIN, _MODULE_MAIN, _MODULE_LIB, _MODULE_LIB_WEAKENED),
]

_CLASS_MATRIX_IDS = [
    "direct_contract",
    "hop_through_ensures",
    "hop_through_requires",
    "refined_return",
    "refined_parameter",
    "alias_chain",
    "where_helper_refined_return",
    "adt_field_via_callee_return",
    "adt_field_on_own_parameter",
    "adt_field_at_construction",
    "alias_on_a_let_annotation",
    "inline_refinement_on_a_let_annotation",
    "constructor_call",
    "effect_op_qualified_call",
    "callee_removed",
    "alias_predicate_changed",
    "adt_variant_added",
    "adt_removed",
    "module_contract_weakened",
]

#: Edits whose kind has no type-correct form: removing a type alias, retyping
#: an effect operation, withdrawing a module export.  The checker refuses
#: each, so verification never runs and BOTH paths report an empty obligation
#: stream — which means these cannot hold the cache key to account, and a
#: cache key replaced by a constant passes every one of them (#1458 review).
#: They are kept as what they are: agreement across a refusal, pinning that
#: the checker is not itself replayed.
_CHECK_PHASE_GUARDS = [
    ("type alias", "declaration removed",
     _ALIAS_ORIGINAL, _ALIAS_REMOVED, None, None),
    ("effect operation signature", "definition changed",
     _EFFECT_ORIGINAL, _EFFECT_RETYPED, None, None),
    ("imported module export", "declaration removed",
     _MODULE_MAIN, _MODULE_MAIN, _MODULE_LIB, _MODULE_LIB_UNEXPORTED),
]

_CHECK_PHASE_GUARD_IDS = [
    "alias_removed",
    "effect_op_retyped",
    "module_export_removed",
]


@pytest.mark.parametrize(
    "kind,edit,original,edited,lib_before,lib_after",
    _CLASS_MATRIX,
    ids=_CLASS_MATRIX_IDS,
)
def test_1441_no_dependency_kind_replays_past_a_change_to_itself(
    tmp_path: Path,
    kind: str,
    edit: str,
    original: str,
    edited: str,
    lib_before: str | None,
    lib_after: str | None,
) -> None:
    """One assertion over the whole space a cached proof can depend on.

    The equality is paired with two premises, because "warm agrees with
    fresh" is satisfied by two sessions that are equally wrong: the original
    must verify CLEAN, and the edit must actually move what a fresh session
    reports.  Without the second, a cache that never invalidated anything
    would pass every row whose fixture had gone inert.
    """
    path = tmp_path / "p.vera"
    mods_before = None if lib_before is None else _lib(lib_before)
    mods_after = None if lib_after is None else _lib(lib_after)

    warm = VerificationSession()
    before = _summary(warm.verify_source(
        original, file=str(path), resolved_modules=mods_before))
    assert before[0] == [], (
        f"{kind} / {edit}: the original does not verify clean, so this cell "
        f"measures something other than the edit — {before}"
    )

    warm_edited = _summary(warm.verify_source(
        edited, file=str(path), resolved_modules=mods_after))
    fresh_edited = _summary(VerificationSession().verify_source(
        edited, file=str(path), resolved_modules=mods_after))

    assert fresh_edited != before, (
        f"{kind} / {edit}: a fresh session reports the same thing before and "
        f"after the edit, so this row is satisfied by a cache that never "
        f"invalidates — the fixture has stopped exercising the dependency"
    )
    assert warm_edited == fresh_edited, (
        f"{kind} / {edit}: warm {warm_edited} vs fresh {fresh_edited}"
    )

    # The premise that makes the row cache coverage at all.  A verification
    # code is E5xx; anything else is the checker refusing, and a refusal
    # means verification never ran — both paths then report an empty
    # obligation stream and agree whatever the key does.
    refused = [c for c in fresh_edited[0] if not c.startswith("E5")]
    assert not refused, (
        f"{kind} / {edit}: the edited program no longer type-checks "
        f"({refused}), so agreement here is the checker running twice rather "
        f"than the cache invalidating — belongs in _CHECK_PHASE_GUARDS"
    )
    assert fresh_edited[1], (
        f"{kind} / {edit}: the edited program produced no obligations at all, "
        f"so there is no proof for a stale entry to be wrong about"
    )


@pytest.mark.parametrize(
    "kind,edit,original,edited,lib_before,lib_after",
    _CHECK_PHASE_GUARDS,
    ids=_CHECK_PHASE_GUARD_IDS,
)
def test_1441_the_checker_is_not_replayed(
    tmp_path: Path,
    kind: str,
    edit: str,
    original: str,
    edited: str,
    lib_before: str | None,
    lib_after: str | None,
) -> None:
    """Warm agrees with fresh when the CHECKER refuses the edited program.

    Not cache coverage, and named so it is not counted as any: verification
    never runs for these, so both paths report the same empty obligation
    stream and a cache key replaced by a constant passes every one.  What
    they pin is that the checker is re-run rather than replayed — a session
    that cached diagnostics would fail them.
    """
    path = tmp_path / "p.vera"
    mods_before = None if lib_before is None else _lib(lib_before)
    mods_after = None if lib_after is None else _lib(lib_after)

    warm = VerificationSession()
    before = _summary(warm.verify_source(
        original, file=str(path), resolved_modules=mods_before))
    assert before[0] == [], f"{kind} / {edit}: the original is not clean — {before}"

    warm_edited = _summary(warm.verify_source(
        edited, file=str(path), resolved_modules=mods_after))
    fresh_edited = _summary(VerificationSession().verify_source(
        edited, file=str(path), resolved_modules=mods_after))

    refused = [c for c in fresh_edited[0] if not c.startswith("E5")]
    assert refused, (
        f"{kind} / {edit}: the edited program type-checks clean, so this is "
        f"cache coverage and belongs in _CLASS_MATRIX where a premise can "
        f"hold it to account — {fresh_edited[0]}"
    )
    assert warm_edited == fresh_edited, (
        f"{kind} / {edit}: warm {warm_edited} vs fresh {fresh_edited}"
    )


#: The one candidate dependency that turns out not to be one, and the
#: measurement that says so rather than an argument that it should be.
_OPAQUE_HELPER = """public fn f(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == lim(()))
  effects(pure)
{
  lim(())
}
where {
  fn lim(@Unit -> @Int)
    requires(true)
    ensures(@Int.result == 1)
    effects(pure)
  {
    1
  }
}

public fn h(@Unit -> @Int)
  requires(true)
  ensures(CALLER_CLAIM)
  effects(pure)
{
  f(())
}
"""


def test_1441_a_callees_where_helper_is_not_part_of_its_interface(
    tmp_path: Path,
) -> None:
    """A caller cannot read into a callee's `where` block, so it may replay.

    `callee_component` hashes a callee's params, return type, contracts and
    type parameters — not its `where` helpers.  That is only safe if a
    caller learns nothing from them, so the premise is measured rather than
    assumed: a caller that tries to conclude `== 1` from `f`'s postcondition
    `== lim(())` is REFUTED on the original text, before any edit, because
    `lim` is opaque across the call boundary.  Editing `lim` therefore moves
    nothing the caller reads, and replaying it is correct.
    """
    path = tmp_path / "p.vera"
    seeing = _OPAQUE_HELPER.replace("CALLER_CLAIM", "@Int.result == 1", 1)
    codes, obligations = _summary(
        VerificationSession().verify_source(seeing, file=str(path)))
    assert "E500" in codes, (
        "a caller CAN see a callee's where-helper contract, so the helper is "
        f"part of the interface and the closure must reach it — {codes}"
    )
    assert [o for o in obligations
            if (o[0], o[2], o[3]) == ("h", "ensures", "violated")], obligations

    blind = _OPAQUE_HELPER.replace("CALLER_CLAIM", "true", 1)
    edited = blind.replace(
        "ensures(@Int.result == 1)\n    effects(pure)\n  {\n    1\n  }",
        "ensures(@Int.result == 2)\n    effects(pure)\n  {\n    2\n  }",
        1,
    )
    assert edited != blind

    warm = VerificationSession()
    before = _summary(warm.verify_source(blind, file=str(path)))
    assert before[0] == [], before
    warm_edited = _summary(warm.verify_source(edited, file=str(path)))
    replayed = warm.last_run_stats.replayed_fns
    fresh_edited = _summary(
        VerificationSession().verify_source(edited, file=str(path)))

    assert warm_edited == fresh_edited, (warm_edited, fresh_edited)
    assert replayed >= 1, (
        "the caller was re-verified for an edit it cannot read, so the "
        "optimisation has been thrown away for every callee with a `where` "
        "block"
    )
