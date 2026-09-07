"""#1429 — a non-regularly recursive `data` declaration is refused at CHECK.

`data Nest<T> { N(Nest<Option<T>>), Z }` grows its type argument at every
level, so the chain `Nest<Int>` -> `Nest<Option<Int>>` ->
`Nest<Option<Option<Int>>>` never repeats and the type has no finite set of
instantiations.  Nothing downstream survives that, and the three ways it broke
are what settle where the rule belongs:

* `vera verify` had no verdict for 67-76 s and then an ``E699`` internal
  compiler error, because the datatype-group closure has no fixed point;
* ``==`` on such a value recurses the CHECKER into a ``RecursionError`` —
  an ``E699`` before verification is reached at all, so "check accepts it"
  was only ever true of the exact repro; and
* the SMT sort key doubles in SIZE per level for ``Ne<Tuple<T, T>>``, so a
  bound on the NUMBER of instantiations is never approached.

An earlier head bounded the group instead, and that is the wrong instrument on
every count: a cliff rather than a rule, silent at the edge, unconstrained in
its constant, and wrong for a legitimate large-but-finite closure — a
five-parameter declaration whose constructor PERMUTES its parameters reaches
610 members and lost a Tier-1 proof it verifies in 0.3 s without the bound.
Refusing the declaration closes all three at the one place the program says
what it means (DESIGN §0.2: explicit and decidable over a silent cliff), and
needs no bound at all.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])

#: Generous next to the sub-second answer the rule produces, and far below the
#: 67-76 s the unbounded walk took to reach its E699.
_DEADLINE_S = 60


def _cli(*args: str, timeout: int = _DEADLINE_S) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=timeout,
    )


def _check(tmp_path: Path, source: str, name: str = "p.vera") -> subprocess.CompletedProcess[str]:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    return _cli("check", str(p))


_MAIN = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""

# Every shape the review named, each non-regular for a different reason.
_IRREGULAR = {
    # The issue's own repro: the argument gains a layer per level.
    "grows-by-a-layer": "private data Nest<T> { N(Nest<Option<T>>), Z }" + _MAIN,
    # The key DOUBLES in size per level, which no member count ever reaches.
    "doubles-in-size": "private data Ne<T> { CE(Ne<Tuple<T, T>>), ZE }" + _MAIN,
    # MUTUAL: neither declaration mentions its own name irregularly, so a
    # per-declaration test that looked only for the declaration's own name
    # would pass both halves.
    "mutual": (
        "private data A<T> { CA(B<Option<T>>), ZA }\n"
        "private data B<T> { CB(A<T>), ZB }" + _MAIN
    ),
    # Reached through a CARRIER's type argument rather than a bare field.
    "through-array": "private data Av<T> { CV(Array<Av<Option<T>>>), ZV }" + _MAIN,
    # PERMUTING: finite per level but never repeating, and the shape whose
    # 610-member closure a count-based bound demoted.
    "permuting": (
        "private data R<A, B, C, D, E> { CR(R<B, C, D, E, A>), ZR }" + _MAIN
    ),
}

# Regular recursion, which must be entirely untouched.
_REGULAR = {
    "self": (
        "private data List<T> { Cons(T, List<T>), Nil }\n"
        "public fn f(@List<Int> -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ match @List<Int>.0 { Cons(@Int, @List<Int>) -> @Int.0, Nil -> 0 } }"
    ),
    "mutual": (
        "private data P<T> { CP(Q<T>), ZP }\n"
        "private data Q<T> { CQ(P<T>), ZQ }\n"
        "public fn f(@P<Int> -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ match @P<Int>.0 { CP(@Q<Int>) -> 1, ZP -> 0 } }"
    ),
    "branching": (
        "private data Tr<T> { Node(Tr<T>, Tr<T>), Leaf(T) }\n"
        "public fn f(@Tr<Int> -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ match @Tr<Int>.0 { Node(@Tr<Int>, @Tr<Int>) -> 1, Leaf(@Int) -> @Int.0 } }"
    ),
    "through-carrier": (
        "private data Av<T> { CV(Array<Av<T>>), ZV }\n"
        "public fn f(@Av<Int> -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ match @Av<Int>.0 { CV(@Array<Av<Int>>) -> 1, ZV -> 0 } }"
    ),
}


@pytest.mark.parametrize("shape", sorted(_IRREGULAR))
def test_non_regular_recursion_is_refused_at_check(
    shape: str, tmp_path: Path,
) -> None:
    """Each shape is refused, with E129, at CHECK — before anything downstream
    has to cope with a type that has no finite instantiation set."""
    proc = _check(tmp_path, _IRREGULAR[shape])
    assert proc.returncode != 0, proc.stdout
    combined = proc.stdout + proc.stderr
    assert "[E129]" in combined, combined[:600]
    # The message has to name the offending occurrence, or the reader cannot
    # tell WHICH of several fields broke the rule.
    assert "recursive group" in combined, combined[:600]


@pytest.mark.parametrize("shape", sorted(_REGULAR))
def test_regular_recursion_is_untouched(shape: str, tmp_path: Path) -> None:
    """The rule must separate non-regular from merely recursive.

    Self-recursion, a mutually recursive pair, a branching tree, and one
    reached through a carrier's type argument all instantiate their group at
    their own parameters, in order — and all still verify at Tier 1.
    """
    source = _REGULAR[shape]
    check = _check(tmp_path, source, name=f"{shape}.vera")
    assert check.returncode == 0, check.stdout + check.stderr

    p = tmp_path / f"{shape}.vera"
    envelope = json.loads(_cli("verify", "--json", str(p)).stdout)
    assert envelope["ok"] is True, envelope["diagnostics"]
    assert envelope["verification"]["tier1_verified"] > 0, envelope


def test_equality_on_the_shape_is_a_clean_diagnostic(tmp_path: Path) -> None:
    """`==` over a non-regular type recursed the CHECKER into a
    `RecursionError`, surfacing as an `E699` internal compiler error — so the
    defect was never confined to verification, and "check accepts it" held
    only for the exact repro.  Refusing the declaration turns it into the
    ordinary E129 the program earns."""
    source = (
        "private data Nest<T> { N(Nest<Option<T>>), Z }\n"
        "public fn f(@Nest<Int> -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Nest<Int>.0 == @Nest<Int>.1 }"
    )
    proc = _check(tmp_path, source, name="eq.vera")
    combined = proc.stdout + proc.stderr
    assert "[E129]" in combined, combined[:600]
    assert "E699" not in combined, combined[:600]


@pytest.mark.parametrize("shape", sorted(_IRREGULAR))
def test_the_refusal_is_prompt(shape: str, tmp_path: Path) -> None:
    """Non-termination is the failure being fixed, so the deadline is the
    assertion.  `pytest.fail` on the timeout, so a regression reports the
    property rather than the plumbing."""
    p = tmp_path / f"{shape}.vera"
    p.write_text(_IRREGULAR[shape], encoding="utf-8")
    try:
        proc = _cli("verify", "--json", str(p))
    except subprocess.TimeoutExpired:
        pytest.fail(
            f"{shape}: no answer within {_DEADLINE_S}s — a non-regular "
            "declaration reached the datatype-group closure again (#1429)"
        )
    assert proc.returncode != 0, proc.stdout
    # WHICH non-zero exit.  The failure this replaces was an internal-compiler
    # `E699` after 67-76 s, which is also non-zero — so the bare code cannot
    # tell the refusal from the crash it is meant to prevent.
    codes = [d["error_code"] for d in json.loads(proc.stdout)["diagnostics"]]
    assert "E129" in codes, codes
    assert "E699" not in codes, codes


def test_no_member_bound_remains() -> None:
    """The bound is gone, not merely raised.

    A count is the wrong instrument here in three measured ways: it demotes a
    legitimate 610-member closure, it never fires for a key that doubles in
    SIZE rather than in count, and nothing constrains its constant — at 1 the
    whole suite stayed green.  Asserted structurally so a future "just bump
    it" cannot quietly reintroduce the cliff the regularity rule replaced.
    """
    source = Path(vera.__file__).resolve().parent / "smt.py"
    text = source.read_text(encoding="utf-8")
    assert "_MAX_ADT_GROUP_MEMBERS" not in text, (
        "a member-count bound is back in the datatype-group walk; the "
        "regularity rule (E129) is what terminates it"
    )


def test_the_remedy_names_the_offending_type_not_the_declaration() -> None:
    """For a MUTUAL pair the offending occurrence is the OTHER member.

    `data A<T> { CA(B<Option<T>>) }` is refused at the `B<Option<T>>`
    occurrence, so the fix has to say `B<T>` — suggesting `A<T>` would send the
    reader to change a declaration that is not the one at fault (PR #1432
    review).
    """
    from vera.checker import typecheck
    from vera.parser import parse_to_ast

    source = (
        "private data A<T> { CA(B<Option<T>>), ZA }\n"
        "private data B<T> { CB(A<T>), ZB }\n" + _MAIN
    )
    program = parse_to_ast(source)
    bad = [d for d in typecheck(program, source) if d.error_code == "E129"]
    assert bad, "the mutual pair was not refused"
    assert "'B<T>'" in bad[0].fix, bad[0].fix


def test_verify_declines_a_non_regular_type_without_the_checker() -> None:
    """`verify()` is a public entry point, and its check-clean precondition is
    the caller's to keep.

    Measured before this: calling `verify()` directly on a program the checker
    refuses did not come back within 60 s, because the datatype-group closure
    has no fixed point — the rule protected the CLI path and nothing else
    (PR #1432 review).  The SMT layer now asks the same shared derivation and
    declines to model such a type, so the walk terminates by the RULE rather
    than by a bound on how far it may go.
    """
    import time

    from vera.checker import typecheck_with_artifacts
    from vera.parser import parse_to_ast
    from vera.verifier import verify

    source = (
        "private data Nest<T> { N(Nest<Option<T>>), Z }\n"
        "public fn f(@Nest<Int> -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ match @Nest<Int>.0 { N(@Nest<Option<Int>>) -> 1, Z -> 0 } }"
    )
    program = parse_to_ast(source)
    diags, artifacts = typecheck_with_artifacts(program, source)
    assert any(d.error_code == "E129" for d in diags), diags

    started = time.monotonic()
    verify(program, source,
           expr_types=artifacts.expr_semantic_types,
           expr_target_types=artifacts.expr_target_types)
    assert time.monotonic() - started < 30, "verify() did not decline promptly"


def test_one_derivation_serves_both_consumers() -> None:
    """The checker and the SMT layer must not be able to disagree.

    Two copies of the rule would be free to drift into one consumer refusing
    what the other models, and the drift would be invisible from either side.
    Asserted structurally, because the symptom of a second copy is silence.
    """
    from pathlib import Path as _Path

    root = _Path(vera.__file__).resolve().parent
    checker = (root / "checker" / "core.py").read_text(encoding="utf-8")
    smt = (root / "smt.py").read_text(encoding="utf-8")
    assert "from vera.regularity import" in checker, checker[:0] or "checker"
    assert "from vera.regularity import" in smt, "smt.py restates the rule"
    for consumer, text in (("checker", checker), ("smt", smt)):
        assert "def recursive_group" not in text, (
            f"{consumer} carries its own copy of the group walk"
        )
