"""The two refinement-chain oracles answer the same question.

`vera.narrowing.narrows_into_refinement` is one rule with two oracles, the
way `narrows_into_nat` is: the verifier reads the checker's SEMANTIC types
(`naming.refined_type_chain`) and code generation reads the source's type
EXPRESSIONS and the alias table (`naming.refined_type_expr_chain`).  That is
the arrangement `vera/narrowing.py`'s own docstring describes — the type
oracle is a parameter, the rule is not — and it is only sound while the two
oracles agree.

They were two CONDITIONS before this PR's review round, not two oracles under
one rule, and they disagreed on every program where both the payload and the
clause binder are refined: one was guarded and recorded nowhere, another was
neither (R-1465 review).  This file is the differential that keeps the
replacement honest, in the shape
`test_refinement_binder_convergence_1208.py` uses for
`naming.refinement_binder_parts` and its reference side.
"""
from __future__ import annotations

import pytest

from vera import ast, narrowing
from vera.checker import typecheck_with_artifacts
from vera.naming import (
    alias_env_from_environment,
    refined_type_chain,
    refined_type_expr_chain,
)
from vera.parser import parse_to_ast
from vera.types import pretty_type
from vera.verifier import ContractVerifier


_PRELUDE = """type Pos = { @Int | @Int.0 > 0 };
type Neg = { @Int | @Int.0 < 0 };
type Big = { @Pos | @Pos.0 > 100 };
type AlsoPos = { @Int | @Int.0 > 0 };
type NonEmpty = { @String | string_length(@String.0) > 0 };
"""

#: (source spelling, declared spelling) -> does binding narrow?
#:
#: Enumerated over the shapes the rule distinguishes rather than over the
#: shapes that were reported: same chain, a chain over the source, disjoint
#: predicates on one base, a plain base under a refinement, an unrelated
#: base, and two aliases whose predicates are written identically.
_PAIRS = [
    ("Pos", "Pos"),
    ("Int", "Pos"),
    ("Nat", "Pos"),
    ("Pos", "Neg"),
    ("Pos", "Big"),
    ("Big", "Pos"),
    ("Pos", "AlsoPos"),
    ("AlsoPos", "Pos"),
    ("String", "NonEmpty"),
    ("NonEmpty", "String"),
    ("Int", "Int"),
    ("Pos", "Int"),
]


def _program(source: str, declared: str) -> str:
    return _PRELUDE + f"""
private fn h(@{declared} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}

public fn f(@{source} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}
"""


def _both_oracles(source: str, declared: str) -> tuple[bool, bool]:
    """The rule's answer under each oracle, for one (source, declared) pair."""
    text = _program(source, declared)
    program = parse_to_ast(text)
    diags, _arts = typecheck_with_artifacts(program, text)
    assert not [d for d in diags if d.severity == "error"], diags

    decls = [
        tld.decl for tld in program.declarations
        if isinstance(getattr(tld, "decl", None), ast.FnDecl)
    ]
    declared_te = next(d for d in decls if d.name == "h").params[0]
    source_te = next(d for d in decls if d.name == "f").params[0]

    verifier = ContractVerifier(program, text)
    verifier._register_all(program)
    alias_env = alias_env_from_environment(verifier.env)

    def semantic(te: ast.TypeExpr) -> narrowing.RefinementChain:
        resolved = verifier._resolve_type(te)
        chain = refined_type_chain(resolved)
        if chain is None:
            return (pretty_type(resolved), frozenset())
        base, predicates = chain
        return (pretty_type(base),
                frozenset(ast.format_expr(p) for p in predicates))

    return (
        narrowing.narrows_into_refinement(
            semantic(source_te), semantic(declared_te)),
        narrowing.narrows_into_refinement(
            refined_type_expr_chain(source_te, alias_env),
            refined_type_expr_chain(declared_te, alias_env)),
    )


@pytest.mark.parametrize(
    "source,declared", _PAIRS, ids=[f"{s}->{d}" for s, d in _PAIRS])
def test_the_two_oracles_give_the_rule_the_same_answer(
    source: str, declared: str,
) -> None:
    """The differential itself.

    Compared to each OTHER rather than to a literal: what the rule ought to
    say about a particular pair is the rule's question, and this file's
    question is only whether the two ways of reading a type reach it the same
    way.  The literals are pinned separately below, so the pair being equally
    wrong is not a way past both.
    """
    semantic, syntactic = _both_oracles(source, declared)
    assert semantic == syntactic, (
        f"@{source} bound at @{declared}: the semantic oracle says "
        f"narrows={semantic} and the type-expression oracle says "
        f"narrows={syntactic}"
    )


#: What the rule must say, so the differential above cannot pass on two
#: oracles that are equally wrong.  Each is a property of the chains, not of
#: a spelling: `Big` adds `> 100` to `Pos`'s `> 0` and narrows it; `Pos` and
#: `AlsoPos` are the same chain written twice and narrow nothing either way;
#: a plain base under a refinement narrows, and the reverse — a source
#: carrying MORE than the declared type asks for — does not.
_EXPECTED = {
    ("Pos", "Pos"): False,
    ("Int", "Pos"): True,
    ("Nat", "Pos"): True,
    ("Pos", "Neg"): True,
    ("Pos", "Big"): True,
    ("Big", "Pos"): False,
    ("Pos", "AlsoPos"): False,
    ("AlsoPos", "Pos"): False,
    ("String", "NonEmpty"): True,
    ("NonEmpty", "String"): False,
    ("Int", "Int"): False,
    ("Pos", "Int"): False,
}


@pytest.mark.parametrize(
    "source,declared", _PAIRS, ids=[f"{s}->{d}" for s, d in _PAIRS])
def test_the_rule_says_what_membership_means(
    source: str, declared: str,
) -> None:
    semantic, _syntactic = _both_oracles(source, declared)
    assert semantic == _EXPECTED[(source, declared)], (
        f"@{source} bound at @{declared}"
    )


def test_every_pair_is_expected() -> None:
    """No pair drifts out of the expectation table unnoticed."""
    assert sorted(_EXPECTED) == sorted(_PAIRS)


# =====================================================================
# What the OTHER pattern-bind positions do with the same pairs
# =====================================================================
#
# The clause binder is not the only position that answers "does this
# narrow?".  `let`, `match` and a destructuring `let` answer it through
# `_narrows_into_refined` / `_refined_field_narrows`, which compare ONE level
# — base plus predicate AST — rather than the conjoined chain.  Before
# routing them through the shared rule too, the question is whether they
# already agree with it; this is that differential, and it is the reason they
# were left alone.

_VALUE_FOR = {"Neg": "0 - 1", "Big": "101"}


def _records_at_the_bind(source: str, declared: str, position: str) -> bool:
    """Does *position* raise a `refine_bind` for this pair, at the BIND?

    Against a control that calls `mk` and binds nothing, because `mk`'s own
    refined RETURN raises a record of its own and counting every
    `refine_bind` in the program would read that one as the bind's.
    """
    import subprocess
    import sys
    import tempfile

    def program(body: str) -> str:
        return _PRELUDE + f"""
private fn mk(@Unit -> @{source})
  requires(true)
  ensures(true)
  effects(pure)
{{
  {_VALUE_FOR.get(source, "1")}
}}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}
"""

    bodies = {
        "control": "mk(());\n  1",
        "let": f"let @{declared} = mk(());\n  1",
        "match": f"match mk(()) {{\n    @{declared} -> 1\n  }}",
        "destructure": f"let Tuple<@Int, @{declared}> = Tuple(1, mk(()));\n  1",
    }

    def count(text: str) -> int:
        import json as _json
        import os as _os
        from pathlib import Path as _Path
        with tempfile.TemporaryDirectory() as tmp:
            path = _Path(tmp) / "p.vera"
            path.write_text(text, encoding="utf-8")
            env = dict(_os.environ)
            env["PYTHONPATH"] = str(
                _Path(__import__("vera").__file__).resolve().parents[1])
            proc = subprocess.run(
                [sys.executable, "-m", "vera.cli", "verify", "--json",
                 str(path)],
                capture_output=True, text=True, encoding="utf-8", env=env,
                check=False, timeout=600,
            )
        envelope = _json.loads(proc.stdout)
        assert not [
            d for d in envelope["diagnostics"]
            if d.get("severity") == "error"
            and not (d.get("error_code") or "").startswith("E5")
        ], envelope["diagnostics"]
        return sum(1 for o in envelope["obligations"]
                   if o["kind"] == "refine_bind")

    return count(program(bodies[position])) > count(program(bodies["control"]))


#: The one pair where the other positions answer differently, with the reason.
#:
#: A source carrying a STRONGER refinement than the slot asks for is exempt
#: under the chain rule — `Big`'s `> 0 AND > 100` already contains `Pos`'s
#: `> 0`, so the value satisfies what it is bound at.  `_narrows_into_refined`
#: obligates it anyway and DISCHARGES it from the source's assumed predicate,
#: which its docstring calls deliberate: at a `let` there is a value term to
#: discharge against, so the obligation is a free Tier 1 rather than noise.
#:
#: The clause binder cannot make that choice, which is why it takes the rule
#: as written: the bound value is whatever reaches the operation and no throw
#: or put site pins it, so an obligation there has nothing to discharge
#: against and would be a `tier3` that can never become anything else.
_DELIBERATE_DISAGREEMENT = {("Big", "Pos")}


@pytest.mark.parametrize("position", ["let", "match", "destructure"])
@pytest.mark.parametrize(
    "source,declared", _PAIRS, ids=[f"{s}->{d}" for s, d in _PAIRS])
def test_the_other_pattern_bind_positions_agree_with_the_rule(
    source: str, declared: str, position: str,
) -> None:
    """Where they agree, and the one place they do not.

    Routing these onto the shared rule would be a silent behaviour change at
    the disagreeing pair, so this differential is what says which pairs such
    a change would move — and the exemption set is small enough to name.
    """
    if declared not in ("Pos", "Neg", "Big", "AlsoPos"):
        pytest.skip(
            "the declared type carries no refinement, so no bind-site "
            "`refine_bind` is possible and the cell would assert False "
            "against False for a reason that is not the rule's")
    rule = _EXPECTED[(source, declared)]
    actual = _records_at_the_bind(source, declared, position)
    if (source, declared) in _DELIBERATE_DISAGREEMENT:
        assert actual and not rule, (
            f"@{source} bound at @{declared} in a {position} no longer "
            f"disagrees with the chain rule — if the position adopted the "
            f"rule, remove this pair from _DELIBERATE_DISAGREEMENT"
        )
        return
    assert actual == rule, (
        f"@{source} bound at @{declared} in a {position}: the position says "
        f"narrows={actual}, the shared rule says narrows={rule}, and this "
        f"pair is not in _DELIBERATE_DISAGREEMENT"
    )
