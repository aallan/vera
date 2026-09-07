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
import re
import subprocess
import sys
from pathlib import Path

import pytest

import vera
from vera.environment import ConstructorInfo

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
    # A MIXED-ARITY mutual pair whose generic member does grow.  The pair
    # shape itself is legitimate (see `_REGULAR["mixed-arity-mutual"]`); what
    # is refused here is the growth, so the two cells together pin the rule to
    # the argument rather than to the pair.
    "mixed-arity-growing": (
        "private data Decl { D(Body<Int>), ZD }\n"
        "private data Body<T> { B(T, Body<Option<T>>), ZB }" + _MAIN
    ),
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
    # A MIXED-ARITY mutual pair.  Comparing an occurrence's argument list
    # against the ENCLOSING declaration's parameter list refused this, because
    # `Body<Int>` inside the zero-parameter `Decl` has an argument where
    # `Decl` has no parameter — yet the closure is two members and it verified
    # at Tier 1 before the rule existed (PR #1432 re-verification).
    "mixed-arity-mutual": (
        "private data Decl { D(Body<Int>), ZD }\n"
        "private data Body<T> { B(T, Decl), ZB }\n"
        "public fn f(@Decl -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ match @Decl.0 { D(@Body<Int>) -> 1, ZD -> 0 } }"
    ),
    # A CLOSED argument on a self-recursive occurrence.  `Expr<Int>` mentions
    # no parameter of `Expr`, so it cannot vary from level to level; the list
    # comparison refused it anyway.
    "closed-argument": (
        "private data Expr<T> { Lit(T), Add(Expr<Int>, Expr<Int>) }\n"
        "public fn f(@Expr<Int> -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ match @Expr<Int>.0 { Lit(@Int) -> @Int.0, "
        "Add(@Expr<Int>, @Expr<Int>) -> 1 } }"
    ),
    # A COMPOSITE closed argument: `Array<Int>` is a type constructor
    # application, so it is not a bare parameter — but it mentions no
    # parameter of `Tw` anywhere inside it, which is what the rule asks.  The
    # cell separates "closed" from "atomic"; a check that only allowed a bare
    # name would refuse this while accepting `Expr<Int>`.
    "closed-composite-argument": (
        "private data Tw<T> { CT(Tw<Array<Int>>), Lt(T) }\n"
        "public fn f(@Tw<Int> -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ match @Tw<Int>.0 { CT(@Tw<Array<Int>>) -> 1, Lt(@Int) -> @Int.0 } }"
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
    # The message has to name the OFFENDING OCCURRENCE, or the reader cannot
    # tell which of several fields broke the rule — and for a mutual pair the
    # occurrence is in a different declaration from the one at fault.
    assert "the occurrence '" in combined, combined[:600]
    # It must not claim the type has no finite set of instantiations: the
    # permuting shape's closure is finite (610 members) and still refused, so
    # the stated reason has to be the rule, not a false property (PR #1432
    # re-verification, item 3).
    assert "no finite set of instantiations" not in combined, combined[:900]


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


#: The three spellings that reach the Eq derivation.  TWO parameters, so
#: `.1` resolves — an earlier fixture had one, and the unresolved slot's E130
#: masked every code the cell was actually about (PR #1432 re-verification).
_EQ_SPELLINGS = {
    "==": "@Nest<Int>.1 == @Nest<Int>.0",
    "!=": "@Nest<Int>.1 != @Nest<Int>.0",
    "eq": "eq(@Nest<Int>.1, @Nest<Int>.0)",
}


@pytest.mark.parametrize("spelling", sorted(_EQ_SPELLINGS))
def test_equality_on_the_shape_reports_e129_alone(
    spelling: str, tmp_path: Path,
) -> None:
    """Every spelling that reaches the Eq derivation reports E129 and nothing
    else.

    All three recursed the derivation into a `RecursionError` — an internal
    `E699` that also DISCARDED the E129 the checker had already recorded, so
    the user was told the compiler had crashed and never told what to fix.
    The derivation now stops at a declaration the rule refuses, which is one
    root cause: not an E699, and not an E243 "does not derive Eq" about a type
    the program is not allowed to declare in the first place.
    """
    source = (
        "private data Nest<T> { N(Nest<Option<T>>), Z }\n"
        "public fn f(@Nest<Int>, @Nest<Int> -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        f"{{ {_EQ_SPELLINGS[spelling]} }}"
    )
    proc = _check(tmp_path, source, name="eq.vera")
    combined = proc.stdout + proc.stderr
    codes = sorted(set(re.findall(r"\[(E\d{3})\]", combined)))
    assert codes == ["E129"], combined[:900]


def test_the_eq_derivation_terminates_without_the_data_pass() -> None:
    """The derivation must terminate on its own, not only because E129 was
    recorded first.

    Eq is the only ability the CHECKER derives structurally over an ADT —
    Ord refuses a user-defined ADT outright, and the Eq walks in codegen and
    the WASM layer run only on a check-clean program, which E129 prevents — so
    `eq_ability.py` is where the whole family is covered.

    Two mechanisms, and this cell isolates the second.  A registry assembled
    directly — by a library caller, or by any entry point that registers data
    types without running the checker's data pass — carries no record of a
    refusal, so the suppression set is empty and only the STRUCTURAL question
    is left.  Before it, `is_eq_derivable` unfolded `Nest<Int>` ->
    `Nest<Option<Int>>` -> ... for ever: the walk's cycle-break keys on the
    fully-applied name, and for a growing chain every key is new.
    """
    from vera.checker.eq_ability import is_eq_derivable
    from vera.environment import AdtInfo, TypeEnv
    from vera.types import INT, AdtType, TypeVar

    env = TypeEnv()
    env.data_types["Nest"] = AdtInfo(
        name="Nest",
        type_params=("T",),
        constructors={
            "N": ConstructorInfo(
                name="N", parent_type="Nest", parent_type_params=("T",),
                field_types=(
                    AdtType("Nest", (AdtType("Option", (TypeVar("T"),)),)),
                ),
            ),
            "Z": ConstructorInfo(
                name="Z", parent_type="Nest", parent_type_params=("T",),
                field_types=None,
            ),
        },
    )
    assert env.refused_non_regular == set(), (
        "this cell is about the structural leg; a populated suppression set "
        "would answer before it is reached"
    )
    assert is_eq_derivable(AdtType("Nest", (INT,)), env) is False


def test_a_crash_does_not_discard_the_diagnostics_already_recorded(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Whatever the pass had already established reaches the user.

    The E129/`RecursionError` pair is fixed at its source, but the command
    boundary's behaviour was the second half of that defect and is worth
    keeping honest on its own: an exception escaping a pass replaced every
    diagnostic it had recorded with "internal compiler error".  A crash is a
    compiler bug; the refusals already found are still facts about the
    program.
    """
    from vera.checker import core as checker_core
    from vera.errors import partial_diagnostics
    from vera.parser import parse_to_ast

    source = "private data Nest<T> { N(Nest<Option<T>>), Z }" + _MAIN
    program = parse_to_ast(source)

    def _boom(self: object, decl: object) -> None:
        raise RuntimeError("synthetic crash after the data pass")

    monkeypatch.setattr(checker_core.TypeChecker, "_check_fn", _boom)
    # BOTH public entries, because they are separate code paths and every
    # `vera` command calls the second one: a first cut wired only `typecheck`
    # and went green here while the CLI went on discarding diagnostics.
    for entry in (
        checker_core.typecheck, checker_core.typecheck_with_artifacts,
    ):
        with pytest.raises(RuntimeError) as caught:
            entry(program, source)
        carried = partial_diagnostics(caught.value)
        assert [d.error_code for d in carried] == ["E129"], (entry, carried)


def test_the_backstop_prints_the_recorded_diagnostic_first(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """...and the envelope renders it BEFORE its own E699, on both paths.

    Order is the property: the internal error is the least actionable line in
    the output, so a reader who stops at the first diagnostic must find the
    one about their program.
    """
    from vera.cli import _internal_error_envelope
    from vera.errors import Diagnostic, SourceLocation, attach_partial_diagnostics

    recorded = Diagnostic(
        description="Non-regular recursion in data declaration 'Nest'.",
        location=SourceLocation(file="p.vera", line=1, column=1),
        source_line="private data Nest<T> { N(Nest<Option<T>>), Z }",
        rationale="r", fix="f", spec_ref="s",
        severity="error", error_code="E129",
    )
    exc = RuntimeError("maximum recursion depth exceeded")
    attach_partial_diagnostics(exc, [recorded])

    assert _internal_error_envelope(
        "p.vera", exc, doing="checking", as_json=False) == 1
    text = capsys.readouterr().err
    assert text.index("E129") < text.index("E699"), text

    assert _internal_error_envelope(
        "p.vera", exc, doing="checking", as_json=True) == 1
    codes = [
        d["error_code"]
        for d in json.loads(capsys.readouterr().out)["diagnostics"]
    ]
    assert codes == ["E129", "E699"], codes


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


def _chain_source(count: int, *, linked: bool) -> str:
    """*count* `data` declarations, chained by field reference or independent.

    The two shapes differ ONLY in whether each declaration names the previous
    one, which is what the regularity graph is built from — so the pair
    isolates the cost of deriving regularity from the cost of checking that
    many declarations at all.
    """
    lines = ["private data D0 { C0(Int), Z0 }"]
    for i in range(1, count):
        field = f"D{i - 1}" if linked else "Int"
        lines.append(f"private data D{i} {{ C{i}({field}), Z{i} }}")
    return "\n\n".join(lines) + "\n" + _MAIN


def test_the_group_index_agrees_with_the_reference_walk() -> None:
    """The SCC index and the straightforward reachability walk must give the
    same groups.

    The index exists only to make the walk affordable, so a differential is
    the assertion that matters: a unit test of either alone would pass while
    they disagreed.  The battery covers the shapes the walk's own definition
    turns on — a self-loop, a non-recursive singleton, a mutual pair, a
    three-cycle, a one-way reference into a cycle (NOT a group member), and a
    chain with no cycle at all.
    """
    from vera.checker.core import TypeChecker
    from vera.parser import parse_to_ast
    from vera.regularity import RegularityIndex, recursive_group

    programs = {
        "self-loop": "private data S { CS(S), ZS }",
        "no-recursion": "private data N { CN(Int), ZN }",
        "mutual": (
            "private data P { CP(Q), ZP }\nprivate data Q { CQ(P), ZQ }"
        ),
        "three-cycle": (
            "private data X { CX(Y), ZX }\nprivate data Y { CY(W), ZY }\n"
            "private data W { CW(X), ZW }"
        ),
        # `E` reaches the cycle but nothing reaches back, so it is NOT in the
        # group — a one-way reference is not recursion.
        "one-way-into-a-cycle": (
            "private data E { CE(F), ZE }\nprivate data F { CF(G), ZF }\n"
            "private data G { CG(F), ZG }"
        ),
        "acyclic-chain": _chain_source(40, linked=True),
    }
    for label, body in programs.items():
        source = body if body.endswith("}\n") else body + _MAIN
        checker = TypeChecker(source=source, file=label)
        checker._register_all(parse_to_ast(source))
        registry = checker.env.data_types
        index = RegularityIndex(registry)
        for name in registry:
            assert index.group(name) == recursive_group(name, registry), (
                label, name,
            )


def test_the_index_is_built_once_per_module(monkeypatch: pytest.MonkeyPatch) -> None:
    """One group computation for the whole module, not one per declaration.

    Deriving the group per declaration is what made `vera check` cubic; a
    count is the assertion that survives a refactor, because a timing cell
    alone cannot distinguish "still per declaration but on a faster machine"
    from "now per module".

    Counted on the CLASS rather than on one module's name for it, so the cell
    holds however the consumers reach it: the checker and the `Eq` derivation
    share the env's index, and patching a single import site would count only
    one of them.
    """
    from vera import regularity as regularity_mod
    from vera.checker import core as checker_core
    from vera.parser import parse_to_ast

    built = []
    original = regularity_mod.RegularityIndex.__init__

    def _counted(self: object, registry: dict[str, object]) -> None:
        built.append(registry)
        original(self, registry)  # type: ignore[arg-type]

    monkeypatch.setattr(regularity_mod.RegularityIndex, "__init__", _counted)
    source = _chain_source(50, linked=True)
    checker_core.typecheck(parse_to_ast(source), source)
    assert len(built) == 1, f"{len(built)} indexes built for one module"


def test_regularity_does_not_dominate_the_check(tmp_path: Path) -> None:
    """A thousand linked declarations must cost about what a thousand
    unlinked ones cost.

    Measured as a RATIO against the same program with its field references
    replaced by `Int`, so the ceiling is calibrated on the machine actually
    running it rather than on an absolute second count.  Before the index,
    linked chains of 300 / 600 / 1000 took 1.8 s / 12.5 s / 73 s against a
    0.5 s baseline — a ratio well past 100 — because the group was re-derived,
    from scratch, once per declaration (PR #1432 re-verification, item 5).
    """
    import time

    timings = {}
    for label, linked in (("linked", True), ("flat", False)):
        path = tmp_path / f"{label}.vera"
        path.write_text(_chain_source(1000, linked=linked), encoding="utf-8")
        started = time.monotonic()
        proc = _cli("check", "--quiet", str(path))
        timings[label] = time.monotonic() - started
        assert proc.returncode == 0, proc.stdout + proc.stderr

    ratio = timings["linked"] / max(timings["flat"], 1e-6)
    assert ratio < 3.0, (
        f"regularity dominates the check: linked={timings['linked']:.2f}s "
        f"flat={timings['flat']:.2f}s ratio={ratio:.1f}"
    )


def test_the_smt_context_reuses_its_index_across_sort_requests() -> None:
    """The verifier asks regularity on EVERY sort request, so its index has to
    be reused too — and invalidated when the registry changes.

    Two properties in one cell because they are the same mechanism seen from
    either side: without the cache the index is rebuilt per request (the cost
    the checker's cell measures, in the other consumer), and without the
    version bump a declaration registered after the first request would be
    judged against a registry that never contained it.
    """
    from vera.environment import AdtInfo, ConstructorInfo as _CI
    from vera.smt import SmtContext

    ctx = SmtContext()
    first = ctx._regularity_index()
    assert ctx._regularity_index() is first, "index rebuilt per request"

    ctx.register_adt(AdtInfo(
        name="Later", type_params=None,
        constructors={"CL": _CI(
            name="CL", parent_type="Later", parent_type_params=None,
            field_types=None,
        )},
    ))
    assert ctx._regularity_index() is not first, (
        "a registration after the first request left a stale index"
    )


def test_the_env_index_is_reused_and_invalidated() -> None:
    """The env's index is shared and must not go stale.

    Two properties, one mechanism.  Without reuse the checker's E129 test and
    the `Eq` derivation each pay a full walk of the declaration graph — the
    derivation once per FIELD of every `==`, which is where the cost would
    have come back after the checker's own site was fixed.  Without
    invalidation a declaration registered later would be judged against a
    registry that never contained it, which is the failure a cache earns if it
    is keyed on nothing.
    """
    from vera.environment import AdtInfo, ConstructorInfo as _CI, TypeEnv

    env = TypeEnv()
    first = env.regularity_index()
    assert env.regularity_index() is first, "index rebuilt per request"

    env.next_decl_index()
    env.data_types["Later"] = AdtInfo(
        name="Later", type_params=None,
        constructors={"CL": _CI(
            name="CL", parent_type="Later", parent_type_params=None,
            field_types=None,
        )},
    )
    assert env.regularity_index() is not first, (
        "a registration after the first request left a stale index"
    )


def test_no_built_in_adt_is_caught_by_the_rule() -> None:
    """`Json`, `MdInline`, `MdBlock` and `HtmlNode` are self-recursive, and
    none of them may be refused.

    The rule now gates the `Eq` derivation, which answers `False` for a type
    it judges irregular — so a rule that tightened onto a built-in would not
    raise a diagnostic, it would silently stop `==` deriving on `Json`.  A
    prompt cell rather than a slow one because the failure is silence: the
    conformance suite would keep passing right up to the first program that
    compares two `Json` values.
    """
    from vera.environment import TypeEnv

    env = TypeEnv()
    index = env.regularity_index()
    irregular = sorted(n for n in env.data_types if not index.is_regular(n))
    assert irregular == [], irregular
    # ...and the recursive ones really are recursive, so the cell is not
    # vacuously green on a registry whose groups are all empty.
    recursive = sorted(n for n in env.data_types if index.group(n))
    assert recursive == ["HtmlNode", "Json", "MdBlock", "MdInline"], recursive


@pytest.mark.parametrize("shape", sorted(_IRREGULAR))
def test_the_remedy_is_never_the_offending_occurrence(shape: str) -> None:
    """A fix line that repeats the line it is fixing is not a fix.

    The PERMUTING shape is how this was found: every argument of
    `R<B, C, D, E, A>` is already a bare parameter, so a repair that only
    unwrapped *growing* arguments changed nothing and handed the author back
    their own spelling.  An occurrence of the declaration's own name takes the
    positional clause instead — each argument mentioning a parameter becomes
    the parameter belonging to that position — while an occurrence of another
    group member keeps the unwrapping repair, since it has no positions to
    keep.  Asserted over every refused shape, because the defect is a fix line
    that is merely useless rather than wrong, and nothing else would catch it.
    """
    from vera.checker import typecheck
    from vera.parser import parse_to_ast

    source = _IRREGULAR[shape]
    refusals = [
        d for d in typecheck(parse_to_ast(source), source)
        if d.error_code == "E129"
    ]
    assert refusals, f"{shape} was not refused"
    diag = refusals[0]
    # Both are quoted in their sentences: "the occurrence 'X'" and
    # "Instantiate the recursive occurrence as 'Y'".
    occurrence = diag.description.split("'")[3]
    remedy = diag.fix.split("'")[1]
    assert remedy != occurrence, (
        f"{shape}: the fix repeats the occurrence ({occurrence})"
    )
