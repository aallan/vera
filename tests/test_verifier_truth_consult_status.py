"""Stream B — the verifier consults the statuses it computes.

An obligation's status is not a label; it is a claim about what the compiled
program does.  `tier3` says "a runtime guard covers this"; `tier3_unguarded`
says "nothing does, and here is the disclosure".  This file holds the cases
where a status was computed and then not consulted by the part that should
have acted on it.

#1362 — the call-argument site hardcoded `guarded=True` on the premise that a
concrete `@Nat` formal is guarded by codegen.  That is true of every user
function and was false of two builtins: `nat_to_int`, whose lowering is a
representation identity (`Nat` and `Int` are both `i64`), and `nat_to_string`,
which shares `int_to_string`'s lowering and so inherited no boundary check.
Neither was hard to guard — both were simply UNGUARDED, which is why this PR
plants the guards rather than only reporting their absence.  A refutable
argument hides the misclassification — the obligation is `violated` either way
— so it surfaces only when the value is OPAQUE, which is what a handler-clause
payload binder supplies.

`string_slice` is the case that does not resolve that way: it clamps its
bounds by design (#475), so no guard is coming and `tier3` would be a false
claim there permanently.  The rule therefore has THREE cases rather than the
one the issue implies — user function (always guarded), clamping builtin
(never), and everything else (by the shared narrowing derivation) — and the
differential below keeps all three equal to what the compiler actually emits.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera
from vera import narrowing
from vera.environment import TypeEnv

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])


def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=300,
    )


def _verify(tmp_path: Path, source: str, name: str = "p.vera") -> dict:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    proc = _cli("verify", "--json", str(p))
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"verify emitted no envelope (exit {proc.returncode})\n"
            f"{proc.stdout[:400]}\n{proc.stderr[-600:]}"
        ) from None


def _program_ast(source: str) -> object:
    """Parse + transform only — these cells drive the verifier directly."""
    from vera.parser import parse
    from vera.transform import transform

    return transform(parse(source, file="f.vera"))


def _wat(tmp_path: Path, source: str, name: str = "w.vera") -> str:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    proc = _cli("compile", "--wat", str(p))
    return proc.stdout


# The issue's own repro, verbatim.
_1362_REPRO = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    throw(@Int.0)
  }
}
"""


def test_1362_unguarded_narrowing_is_disclosed_not_claimed_guarded(
    tmp_path: Path,
) -> None:
    """The issue's repro: `tier3_unguarded` + E504, never plain `tier3`.

    `tier3` is counted in `tier3_runtime`, whose meaning is runtime-guarded.
    Claiming it here overcounts guarded obligations AND skips the disclosure
    machinery that exists for exactly this case.
    """
    result = _verify(tmp_path, _1362_REPRO)
    binds = [o for o in result["obligations"] if o["kind"] == "nat_bind"]
    assert len(binds) == 1, [(o["kind"], o["status"]) for o in result["obligations"]]
    assert binds[0]["status"] == "tier3_unguarded", (
        f"status {binds[0]['status']!r} claims a runtime guard; the emitted "
        f"module has none"
    )
    assert "E504" in [w.get("error_code") for w in result["warnings"]]


def test_1362_the_claim_and_the_module_agree(tmp_path: Path) -> None:
    """The claim is checked against the artifact, not against itself.

    `tier3_unguarded` asserts the emitted module plants no guard here — so the
    module is inspected.  Without this the status could be renamed without
    being made true.
    """
    wat = _wat(tmp_path, _1362_REPRO)
    assert wat.startswith("(module"), wat[:300]
    assert "unreachable" not in wat, (
        "the module DOES carry a guard — the obligation should then be "
        f"`tier3`, not disclosed:\n{wat}"
    )
    # And the value the guard would have caught flows through untrapped.
    p = tmp_path / "r.vera"
    p.write_text(_1362_REPRO, encoding="utf-8")
    run = _cli("run", str(p), "--fn", "f", "--", "-7")
    assert run.returncode == 0 and run.stdout.strip() == "-7", (
        f"expected the negative to pass through unguarded: {run.stdout!r} "
        f"{run.stderr[-300:]!r}"
    )


def test_1362_a_guarded_callee_is_still_tier3(tmp_path: Path) -> None:
    """The over-rejection control, and the axis the fix turns on.

    The SAME opaque clause binder passed to a USER function's `@Nat` formal is
    genuinely guarded, so it must stay `tier3`.  Without this cell the fix
    would be satisfied by disclosing every call argument.
    """
    source = """\
private fn takes(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{
  nat_to_int(@Nat.0)
}

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Nat) -> { takes(@Nat.0) }
  } in {
    throw(@Int.0)
  }
}
"""
    result = _verify(tmp_path, source, name="g.vera")
    binds = [o for o in result["obligations"] if o["kind"] == "nat_bind"]
    assert binds and all(o["status"] == "tier3" for o in binds), (
        f"a guarded callee was disclosed as unguarded: "
        f"{[(o['kind'], o['status']) for o in binds]}"
    )
    wat = _wat(tmp_path, source, name="g2.vera")
    assert "unreachable" in wat, "control claims a guard the module lacks"


def _nat_param_builtins() -> list[tuple[str, int]]:
    """Every builtin with a `@Nat` parameter, from the LIVE registry.

    Enumerated rather than listed, so a builtin added tomorrow joins the
    differential by existing.
    """
    env = TypeEnv()
    out: list[tuple[str, int]] = []
    for name, info in sorted(env.functions.items()):
        params = getattr(info, "param_types", None) or ()
        for i, ty in enumerate(params):
            if getattr(ty, "name", "") == "Nat":
                out.append((name, i))
    return out


def test_the_guard_rule_is_three_cases_not_one() -> None:
    """The classification consults callee CLASS and argument, not either alone.

    Measured, each by compiling the shape and running a negative through it:
    a USER function's `@Nat` formal is guarded unconditionally, a guarding
    BUILTIN guards only when the argument narrows, and `string_slice` never
    guards because it clamps by design (#475).  Callee-only cannot separate
    the two halves of the middle case; argument-only gets the first backwards
    and the last wrong.

    The argument half is the SHARED derivation, imported rather than re-listed,
    so codegen and this cannot drift on it.
    """
    import vera.verifier as V

    assert hasattr(narrowing, "narrows_into_nat"), (
        "the argument half must come from the shared derivation"
    )
    # The callee half is a set of exceptions with stated reasons, not a
    # restatement of every builtin: it names only what never guards.
    assert V._NAT_ARG_UNGUARDED_BUILTINS == frozenset({"string_slice"}), (
        f"the never-guards set drifted: {V._NAT_ARG_UNGUARDED_BUILTINS}"
    )


# Nine shapes the reviewer built, plus the two routes.  Each is a (params,
# body) pair whose ARGUMENT slot is the only thing the control varies — the
# return type is held at `@Int` deliberately: rewriting it too would mix the
# argument guard with a return-boundary check.
_SHAPES: dict[str, tuple[str, str]] = {
    "nat_to_int": ("@Int", "nat_to_int(@Int.0)"),
    "nat_to_string": ("@Int", "string_length(nat_to_string(@Int.0))"),
    "string_from_char_code": (
        "@Int", "string_length(string_from_char_code(@Int.0))"),
    "string_pad_end": ("@Int", 'string_length(string_pad_end("ab", @Int.0, "x"))'),
    "string_pad_start": (
        "@Int", 'string_length(string_pad_start("ab", @Int.0, "x"))'),
    "string_repeat": ("@Int", 'string_length(string_repeat("ab", @Int.0))'),
    "string_slice_pos1": (
        "@Int", 'string_length(string_slice("abcdef", @Int.0, 2))'),
    "string_slice_pos2": (
        "@Int", 'string_length(string_slice("abcdef", 1, @Int.0))'),
    "md_has_heading": (
        "@MdBlock, @Int",
        "if md_has_heading(@MdBlock.0, @Int.0) then { 1 } else { 0 }"),
}


def _program(params: str, body: str) -> str:
    return (f"public fn f({params} -> @Int)\n"
            f"  requires(true) ensures(true) effects(pure)\n"
            f"{{\n  {body}\n}}\n")


# An `@Int` the solver cannot reason about.  A plain parameter is REFUTABLE —
# nothing stops it being negative — so the narrowing obligation settles
# `violated` and the `guarded` flag is never consulted, which is the leg the
# parity differential exists to compare.  A value arriving across an effect
# boundary is opaque instead: the verifier cannot connect the thrown payload
# to the clause binder, so the obligation lands undecided.  It must stay
# INLINE — binding it through a `let` first reconnects the two and the
# obligation goes back to `violated` (measured, not assumed).
_OPAQUE_INT = "handle[Exn<Int>] { throw(@Int) -> { @Int.0 } } in { throw(@Int.0) }"


def _opaque_program(name: str) -> str:
    """*name*'s shape with its narrowing argument made opaque.

    The classification and artifact legs read different fixtures ON PURPOSE.
    Codegen's guard is a property of the call site, not of where the argument
    came from, so the runnable shape settles what the MODULE does while this
    one settles what the VERIFIER says — and only an undecided obligation has
    a `guarded` flag to say anything about.
    """
    params, body = _SHAPES[name]
    return _program(params, body.replace("@Int.0", f"({_OPAQUE_INT})"))



def _traps_on_negative(tmp_path: Path, name: str) -> bool:
    """Whether the compiled program traps when the argument is negative.

    The ARTIFACT, not the WAT text: a guard that is present but unreachable,
    or absent where a delta suggested one, shows up here and nowhere else.
    """
    params, body = _SHAPES[name]
    p = tmp_path / f"{name}_run.vera"
    p.write_text(_program(params, body), encoding="utf-8")
    assert params == "@Int", (
        f"{name} needs a non-scalar argument; the caller must skip it rather "
        f"than take a False from here, which would read as 'does not guard'"
    )
    proc = _cli("run", str(p), "--fn", "f", "--", "-7")
    out = proc.stdout + proc.stderr
    # A non-zero exit WITHOUT the trap word is not "ran and did not trap" — a
    # compile failure, a CLI usage error or a missing `--fn` target all look
    # identical to it, and each would read as "codegen does not guard" and
    # compare clean against a verifier that also says unguarded (CR PR-review).
    # That is not hypothetical: `nat_to_string`'s guard shipped wrapping the
    # String result instead of the i64 argument, so the module failed WASM
    # validation, and this helper read the failure as an honest no-guard answer.
    # So the artifact must be shown to RUN before its verdict is read.
    if "unreachable" in out:
        return True
    assert proc.returncode == 0, (
        f"{name}: the fixture did not run, so it reports no verdict about "
        f"guarding — exit {proc.returncode}, no trap word:\n{out[-700:]}"
    )
    return False


def test_every_nat_builtin_has_a_differential_shape() -> None:
    """Coverage: the shape map matches the live registry.

    A builtin gaining a `@Nat` parameter must gain a fixture, or the parity
    differential below would quietly stop covering it.
    """
    registered = {n for n, _ in _nat_param_builtins()}
    covered = {n.split("_pos")[0] for n in _SHAPES}
    missing = registered - covered
    assert not missing, f"no differential shape for: {sorted(missing)}"

    # Having a SHAPE is not having PARITY.  The parity cell runs the compiled
    # program, so a shape whose argument is not a scalar is skipped there and
    # is covered on the codegen side only — a verifier-side regression on one
    # of these would not be caught here (CR PR-review).  The roster is asserted
    # rather than derived so that a builtin joining it is a deliberate act.
    wat_only = {n for n, (params, _) in _SHAPES.items() if params != "@Int"}
    assert wat_only == {"md_has_heading"}, (
        f"the set of shapes parity cannot run has changed: {sorted(wat_only)} "
        f"— give the new one a scalar fixture, or record here that its guard "
        f"is checked on the codegen side only"
    )


@pytest.mark.parametrize("name", sorted(_SHAPES))
def test_nat_arg_guard_parity(tmp_path: Path, name: str) -> None:
    """PARITY: the verifier's classification equals codegen's behaviour.

    Derived from the emitted module and, where the shape allows it, from
    RUNNING the program on a value the guard exists to catch — a status is a
    claim about the artifact, so the artifact is what settles it.
    """
    params, body = _SHAPES[name]
    if params != "@Int":
        pytest.skip(
            f"{name} needs a non-scalar argument, so it cannot be RUN; the "
            f"WAT-delta reading alone is the confound this test avoids"
        )

    # THE ARTIFACT IS THE ORACLE — the program is run on the value the guard
    # exists to catch.  A WAT `unreachable` delta was the first reading and it
    # is confounded: for `nat_to_int` the body IS the argument, so declaring
    # the parameter `@Nat` in the control also removes the `@Nat -> @Int`
    # RETURN-widening guard, and the delta measures both boundaries at once.
    # That is the same confound in the other direction as the control which
    # rewrote the return type (PR review); running it has no such ambiguity.
    codegen_guards = _traps_on_negative(tmp_path, name)

    result = _verify(tmp_path, _opaque_program(name), name=f"{name}_v.vera")
    binds = [o for o in result["obligations"] if o["kind"] == "nat_bind"]
    assert binds, f"{name}: no nat_bind obligation to classify"

    # The `guarded` flag is consulted ONLY on the undecided leg — a `violated`
    # obligation is refuted statically and makes no claim about a runtime
    # guard, and a `verified` one needs none.  Asserting parity over those
    # would be asserting something the classification does not decide.
    undecided = [o for o in binds
                 if o["status"] in ("tier3", "tier3_unguarded", "timeout")]
    assert undecided, (
        f"{name}: every nat_bind settled statically "
        f"({[o['status'] for o in binds]}), so the `guarded` flag was never "
        f"consulted and this differential compared nothing.  The argument is "
        f"supposed to be OPAQUE — if the verifier has learned to see through "
        f"`_OPAQUE_INT`, the fixture needs a new opaque source, not a skip"
    )
    verifier_says_guarded = any(o["status"] != "tier3_unguarded"
                                for o in undecided)
    assert codegen_guards == verifier_says_guarded, (
        f"{name}: the compiled program "
        f"{'traps' if codegen_guards else 'does NOT trap'} on a negative, "
        f"verifier says {'guarded' if verifier_says_guarded else 'unguarded'} "
        f"({[o['status'] for o in undecided]}) — the two sides have drifted"
    )


# ---------------------------------------------------------------------------
# #1363 / E534 and its FIFTH consumer, `vera test` (#1375)
# ---------------------------------------------------------------------------

# A callee this run DISCLOSED (its `@Nat` binder narrowing is `tier3_unguarded`,
# E504), returning a value whose `@Nat` field a caller then reads off through a
# match.  That field's declared-type fact is exactly what #1363 is about: the
# run could neither prove nor guard it, so it is withheld from the first proof
# attempt, and `use_it`'s postcondition — which holds only once it is added —
# is reported `tier3` with E534 instead of `verified`.
_E534_SHAPE = """\
public fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  int_to_nat(handle[Exn<Int>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    throw(@Int.0)
  })
}

public fn use_it(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match mk(@Int.0) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0
  }
}
"""


def _test_json(tmp_path: Path, source: str, trials: int = 20) -> dict:
    p = tmp_path / "t.vera"
    p.write_text(source, encoding="utf-8")
    proc = _cli("test", "--json", "--trials", str(trials), str(p))
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"test emitted no envelope (exit {proc.returncode})\n"
            f"{proc.stdout[:400]}\n{proc.stderr[-600:]}"
        ) from None


def test_1363_a_disclosed_fact_demotes_the_goal_that_needs_it(
    tmp_path: Path,
) -> None:
    """E534 is reachable, and lands on the goal rather than on the disclosure.

    Two obligations, two different statuses, and the pairing is the point: the
    SOURCE is `tier3_unguarded` (nothing guards it, so it is disclosed) while
    the GOAL that leans on it is `tier3` (a runtime check does cover the
    caller's contract).  Collapsing either into the other loses the
    distinction #1363 exists to draw.
    """
    result = _verify(tmp_path, _E534_SHAPE)
    by_kind = [(o["kind"], o["status"], o.get("error_code"))
               for o in result["obligations"]]
    assert ("nat_bind", "tier3_unguarded", "E504") in by_kind, by_kind
    assert ("ensures", "tier3", "E534") in by_kind, by_kind
    codes = [w.get("error_code") for w in result["warnings"]]
    assert "E504" in codes and "E534" in codes, codes


def test_1375_a_demoted_contract_is_given_trials(tmp_path: Path) -> None:
    """The fifth consumer of the status stream: `vera test`.

    The verifier reported this postcondition `tier3` — runtime-checked, not
    proved.  Reading a Tier-3 WARNING-CODE set instead of the statuses, the
    tester did not recognise E534 (added by #1363, after that set was written)
    and reported the contract as "Tier 1 (proved)" while running ZERO trials on
    it — the one contract most in need of them.  Asserted on the reason string
    as well as the count, so a function reaching `tested` down some other path
    cannot pass this.
    """
    result = _test_json(tmp_path, _E534_SHAPE)
    fns = {f["name"]: f for f in result["functions"]}
    use_it = fns["use_it"]
    assert use_it["category"] == "tested", (
        f"a contract this run demoted to E534 was reported "
        f"{use_it['category']!r} ({use_it['reason']!r})"
    )
    assert use_it["reason"] == "Tier 3 contract (runtime check)"
    assert use_it["trials_run"] > 0


def test_1375_a_proved_contract_is_not_demoted_by_a_safety_obligation(
    tmp_path: Path,
) -> None:
    """The over-rejection control, and the axis the fix turns on.

    The obligation stream is strictly WIDER than the diagnostic set it
    replaces: it also carries the per-site safety kinds, which are `tier3`
    whenever a codegen trap rather than a proof is the guard.  `abs_val`'s two
    contracts are both proved and its subtraction carries an `int_overflow`
    site, so consulting the statuses without regard to KIND would report a
    fully proved function as runtime-checked and run trials on it — where the
    overflow guard firing legitimately would score as a falsified contract
    (#1229).  `verified` here is what keeps the #1375 fix a re-keying rather
    than a widening.
    """
    source = """\
public fn abs_val(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 >= 0 then { @Int.0 } else { 0 - @Int.0 }
}
"""
    verify = _verify(tmp_path, source)
    statuses = [(o["kind"], o["status"]) for o in verify["obligations"]]
    # The premise: a safety obligation IS undecided here, so the control is
    # live rather than vacuous.
    assert ("int_overflow", "tier3") in statuses, statuses
    assert ("ensures", "verified") in statuses, statuses

    result = _test_json(tmp_path, source)
    abs_val = {f["name"]: f for f in result["functions"]}["abs_val"]
    assert abs_val["category"] == "verified", (
        f"a proved contract was demoted to {abs_val['category']!r} by a "
        f"safety-kind obligation: {abs_val['reason']!r}"
    )
    assert abs_val["trials_run"] == 0


def test_every_obligation_kind_is_classified() -> None:
    """The partition is pinned against the LIVE vocabulary, not a copy of it.

    `_CONTRACT_KINDS` and its complement decide whether a Tier-3 obligation
    demotes its function for testing.  A kind added later must be placed
    deliberately: without this cell it would fall silently into the safety
    side, which is the failure mode #1375 was — a new code arriving after the
    set that was supposed to enumerate it.
    """
    import typing

    from vera.obligations.core import ObligationKind
    from vera.tester import _CONTRACT_KINDS

    kinds = set(typing.get_args(ObligationKind))
    assert _CONTRACT_KINDS <= kinds, (
        f"_CONTRACT_KINDS names kinds that no longer exist: "
        f"{sorted(_CONTRACT_KINDS - kinds)}"
    )
    safety = kinds - _CONTRACT_KINDS
    # Both sides non-empty and jointly exhaustive by construction; the value is
    # the roster, which changes loudly rather than silently.
    assert sorted(_CONTRACT_KINDS) == [
        "assert", "decreases", "ensures", "requires",
    ], sorted(_CONTRACT_KINDS)
    assert sorted(safety) == [
        "call_pre", "div_zero", "float_to_int_domain", "index_bounds",
        "int_overflow", "nat_bind", "nat_sub", "nat_to_int_coerce",
        "refine_bind", "state_decl",
    ], (
        "a new ObligationKind appeared — decide whether a Tier-3 instance of "
        f"it means a DEMOTED CONTRACT (add to _CONTRACT_KINDS) or a per-site "
        f"safety guard (leave it out), then update this roster: {sorted(safety)}"
    )


def test_the_disclosure_rerun_iterates_to_a_fixpoint(tmp_path: Path) -> None:
    """One extra pass is not enough, so the re-run is a LOOP.

    Within a pass the disclosed set is fixed, so a function disclosed during
    it taints nothing for callers already verified — and since a demotion can
    itself disclose (an `ensures` demoted to E534 makes its function
    disclosed), a chain propagates one hop per pass.  A two-hop chain whose
    middle function is declared after its caller therefore still proves at
    Tier 1 under a single re-run.

    Driven directly rather than through a source program: the end-to-end
    two-hop shape needs an ADT accessor that is BOTH translatable to Z3 and
    fact-bearing, and the built-in vocabulary has none — `option_unwrap_or`
    does not translate, so a middle function's postcondition over it lands on
    E523 (untranslatable) instead of E534 (demoted), and the chain stops at
    the first hop for a reason unrelated to this loop.  So the growth sequence
    is supplied and the loop's own behaviour asserted: a pass per growth, and
    a stop once the set repeats.
    """
    from vera.verifier import ContractVerifier

    source = "public fn f(@Int -> @Int)\n  requires(true) ensures(true) effects(pure)\n{ @Int.0 }\n"
    program = _program_ast(source)
    verifier = ContractVerifier(source=source, file="f.vera")

    # {} -> {a} -> {a, b} -> {a, b}: two growths, then a repeat that settles.
    sequence = [
        frozenset({"a"}), frozenset({"a", "b"}), frozenset({"a", "b"}),
    ]
    seen_sets: list[frozenset[str]] = []
    passes: list[frozenset[str]] = []

    def fake_disclosed() -> frozenset[str]:
        return sequence[min(len(seen_sets), len(sequence) - 1)]

    def fake_pass(_program: object) -> None:
        # The set the pass RAN UNDER — the property that matters, since a
        # pass repeated under an unchanged set would be wasted work and a
        # pass run under a stale one is the bug.
        passes.append(verifier._disclosed_fns)

    def fake_disclosed_recording() -> frozenset[str]:
        out = fake_disclosed()
        seen_sets.append(out)
        return out

    verifier._disclosed_fn_names = fake_disclosed_recording  # type: ignore[method-assign]
    verifier._verify_all_declarations = fake_pass  # type: ignore[method-assign]
    verifier.register_program = lambda _p: None  # type: ignore[method-assign]

    verifier._rerun_until_disclosure_settles(program)

    assert passes == [frozenset({"a"}), frozenset({"a", "b"})], (
        f"expected one re-verification per growth of the disclosed set, "
        f"each under the set the previous pass produced; got {passes}"
    )
    assert verifier._disclosed_fns == frozenset({"a", "b"})


def test_the_disclosure_rerun_does_not_run_when_nothing_is_disclosed(
) -> None:
    """The cost control: no corpus program discloses, so none pays for this.

    The fixpoint re-verifies the whole program per pass.  It must therefore
    not run at all on the overwhelmingly common case — asserted rather than
    assumed, because a loop that always runs one pass would be invisible in
    every result and visible only in the wall clock.
    """
    from vera.verifier import ContractVerifier

    source = "public fn f(@Int -> @Int)\n  requires(true) ensures(true) effects(pure)\n{ @Int.0 }\n"
    program = _program_ast(source)
    verifier = ContractVerifier(source=source, file="f.vera")

    passes: list[object] = []
    verifier._disclosed_fn_names = lambda: frozenset()  # type: ignore[method-assign]
    verifier._verify_all_declarations = lambda p: passes.append(p)  # type: ignore[method-assign]

    verifier._rerun_until_disclosure_settles(program)
    assert passes == [], "a program with nothing disclosed was re-verified"


# ---------------------------------------------------------------------------
# The two MUST-warnings of Chapter 6 (#1345), and their consumers
# ---------------------------------------------------------------------------

def test_1345_an_undecided_assert_says_so(tmp_path: Path) -> None:
    """§6.5: a contract falling to a runtime check MUST be reported.

    `assert` was the construct that did not: `requires` had E521, `ensures`
    E522, `decreases` E525, and `assert` fell to a runtime check silently, so
    the reader saw the Tier-3 count move with nothing naming the construct
    that moved it.  The obligation and the warning are asserted TOGETHER —
    the status was always recorded; it was the disclosure that was missing,
    so a cell reading only the obligation would have passed throughout.
    """
    source = """\
public fn f(@Int, @Array<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  assert(array_length(@Array<Int>.0) > @Int.0);
  @Int.0
}
"""
    result = _verify(tmp_path, source)
    asserts = [o for o in result["obligations"] if o["kind"] == "assert"]
    assert len(asserts) == 1, [o["kind"] for o in result["obligations"]]
    assert (asserts[0]["status"], asserts[0]["error_code"]) == ("tier3", "E535")
    warnings = [w for w in result["warnings"] if w.get("error_code") == "E535"]
    assert warnings, (
        "the assertion fell to a runtime check with no warning naming it"
    )
    assert "f" in warnings[0]["description"]


def test_1345_an_assumption_is_disclosed_once_per_site(tmp_path: Path) -> None:
    """§6.2.6: one warning per `assume`, and the summary counts them.

    Two things at once, because they fail apart.  A generic is verified once
    per INSTANTIATION, so the site-keyed disclosure would otherwise be
    re-emitted per instance and a reader would see an assumption count that
    tracked how many types a helper happened to be used at.  And the summary's
    `assumptions` field is DERIVED from the assembled diagnostics rather than
    kept as a counter — a counter drifted between the warm and cold paths,
    which is the class of bug this PR is about.
    """
    source = """\
public forall<T> fn pick(@T, @Int -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  assume(@Int.0 > 0);
  @T.0
}

public fn use_int(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ pick(@Int.0, 1) }

public fn use_bool(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ pick(@Bool.0, 1) }
"""
    result = _verify(tmp_path, source)
    w003 = [w for w in result["warnings"] if w.get("error_code") == "W003"]
    assert len(w003) == 1, (
        f"one `assume` SITE, {len(w003)} warnings — the disclosure is being "
        f"re-emitted per instantiation ({[w['location'] for w in w003]})"
    )
    # The premise: the generic really is instantiated more than once, so the
    # dedup above is doing work rather than describing a single instance.
    assert result["verification"]["tier1_verified"] == 6, result["verification"]
    assert result["verification"]["assumptions"] == 1, result["verification"]


def test_the_widening_reason_forwards_every_non_verdict() -> None:
    """A demotion says which event demoted it — including `disclosed`.

    `_int_widen_undischarged_reason` forwarded `unknown` and `opaque` to
    `_undecided_reason` and let everything else fall through to its default
    sentence, which describes an unconstrained `@Nat` leaving countermodels on
    both sides.  That is a fact about the PROGRAM, and it told a reader to go
    bound a value.  A `disclosed` widening is a fact about the PROOF — the
    goal holds only from something this run could neither prove nor guard —
    so inheriting that text sent the reader to fix the wrong thing, the exact
    misattribution `_undecided_reason` was factored out to prevent.

    Asserted against the DEFAULT rather than for a keyword, so a future
    status that silently inherits the default fails here.
    """
    from vera.verifier import ContractVerifier

    default = ContractVerifier._int_widen_undischarged_reason(
        "violated", "violated",
    )
    for status in ("unknown", "opaque", "disclosed"):
        reason = ContractVerifier._int_widen_undischarged_reason(
            status, "violated",
        )
        assert reason != default, (
            f"a {status!r} widening inherits the unconstrained-@Nat text, "
            f"which names a program problem for a proof event"
        )
        assert reason == ContractVerifier._undecided_reason(status)


_DISCLOSED_CALL_PRE = """\
public fn mk(@Int -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{
  int_to_nat(handle[Exn<Int>] { throw(@Nat) -> { nat_to_int(@Nat.0) } } in { throw(@Int.0) })
}

public fn needs_nonneg(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ @Int.0 }

public fn use_it(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match mk(@Int.0) {
    Some(@Nat) -> needs_nonneg(nat_to_int(@Nat.0)),
    None -> 0
  }
}
"""


def test_a_disclosed_precondition_is_demoted_not_refuted(
    tmp_path: Path,
) -> None:
    """A disclosed call precondition is Tier 3, never E501.

    `check_valid` gained a fifth outcome, and the call-precondition site read
    it as `!= "verified"` — so a precondition that HOLDS, just only from a
    declared-type fact this run disclosed, was recorded as a CallViolation and
    reported E501: a definite "may violate the callee's precondition" from a
    run that found no violating model, on a program that is fine.  It rejects
    valid code, which is the OPPOSITE misattribution from claiming Tier 1 and
    exactly as wrong.  The demotion vocabulary has a bucket for "holds, but
    not provably by this run" and this is it.
    """
    result = _verify(tmp_path, _DISCLOSED_CALL_PRE)
    assert result["ok"] is True, [d["description"] for d in result["diagnostics"]]
    pres = [o for o in result["obligations"] if o["kind"] == "call_pre"]
    assert len(pres) == 1, [(o["kind"], o["status"]) for o in result["obligations"]]
    assert (pres[0]["status"], pres[0]["error_code"]) == ("tier3", "E532"), pres
    assert "E501" not in [d.get("error_code") for d in result["diagnostics"]]
    # The premise: the callee really is disclosed, so this is the disclosed
    # path and not merely an untranslatable precondition taking the same exit.
    assert any(o["status"] == "tier3_unguarded" for o in result["obligations"])


def test_a_genuinely_violated_precondition_still_says_so(
    tmp_path: Path,
) -> None:
    """The over-suppression control for the cell above.

    Demoting on `disclosed` must not become "stop reporting E501".  Here the
    argument is an unconstrained parameter, the solver has a real violating
    model, and the error is the correct answer.
    """
    source = """\
public fn needs_nonneg(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ @Int.0 }

public fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_nonneg(@Int.0) }
"""
    result = _verify(tmp_path, source)
    assert result["ok"] is False
    assert "E501" in [d.get("error_code") for d in result["diagnostics"]]
    pres = [o for o in result["obligations"] if o["kind"] == "call_pre"]
    assert pres and pres[0]["status"] == "violated", pres


def test_the_guard_question_uses_codegen_s_nat_origin_oracle() -> None:
    """The verifier and codegen must ask the @Nat-provenance question alike.

    `narrows_into_nat` takes its oracles as PARAMETERS precisely so the two
    sides can supply their own type readings while sharing one rule.  A
    constant `False` stood in for the verifier's @Nat-provenance oracle,
    justified in a comment as conservative.  It is not: for
    `nat_to_int(@Nat.0 - 1)` the constant answers "this narrows" (so a guard
    is claimed) while codegen's `_has_nat_origin_codegen` suppresses the
    underflow leaf and emits none — a claimed guard that is not in the
    module, which is #1362 itself, in the code that fixes #1362.

    Asserted as AGREEMENT between the two oracles rather than against a
    hardcoded verdict, so the cell keeps meaning if the rule changes.  It is
    pinned here, at the derivation, rather than through a program: no shape
    was found where this alone flips an obligation's reported status, because
    the site records no `nat_bind` for a @Nat-origin argument by another
    route.  A divergence that is currently masked is still a divergence — the
    masking is not part of either side's contract.
    """
    from vera import narrowing
    from vera.parser import parse
    from vera.transform import transform

    source = """\
public fn f(@Nat -> @Int)
  requires(@Nat.0 > 0) ensures(true) effects(pure)
{ nat_to_int(@Nat.0 - 1) }
"""
    fn = transform(parse(source)).declarations[0].decl
    body = fn.body
    call = getattr(body, "expr", None) or body
    arg = call.args[0]
    def ret(c: object) -> str | None:
        """The declared-return oracle, standing in for the registry lookup."""
        return "Nat" if getattr(c, "name", "") == "nat_to_int" else None

    # Codegen's reading: a @Nat-origin subtraction has no underflow leaf to
    # guard, so nothing narrows here.
    codegen_says = narrowing.narrows_into_nat(arg, ret, lambda _e: True)
    # The constant that shipped, which is what the fix removed.
    constant_says = narrowing.narrows_into_nat(arg, ret, lambda _e: False)
    assert codegen_says != constant_says, (
        "the shape no longer distinguishes the two oracles, so this cell "
        "cannot show the divergence it exists for — pick a new shape"
    )

    from vera.verifier import ContractVerifier

    verifier = ContractVerifier(source=source, file="f.vera")
    assert verifier._call_arg_nat_guarded("nat_to_int", arg) == codegen_says, (
        "the verifier's `guarded` claim disagrees with codegen's own "
        "@Nat-provenance reading of the same expression"
    )


def test_a_disclosed_fact_does_not_survive_into_the_next_function() -> None:
    """`reset()` clears the taint, and this is what says so.

    `_tainted_facts` is PER-FUNCTION state on a solver the warm path reuses
    for a whole program.  A fact left behind is not inert: `check_valid` adds
    the tainted set on its second attempt, so a leaked fact can make the NEXT
    function's unprovable goal provable and turn a `violated` obligation into
    a `disclosed` one — a refuted contract reported as a Tier-3 truth, which
    is a false pass rather than a false alarm.

    Pinned at the context rather than through a two-function program: the
    leak needs the later function's goal to mention the same Z3 term the
    earlier one tainted, and the call-term naming makes that shape hard to
    write on purpose.  A property with no test is worse than one pinned at
    the level where it is decidable — replacing the `clear()` with `pass`
    left the whole verifier/SMT/session suite green (Reviewer-1), which is
    exactly the gap this closes.  The assertion is SEMANTIC: a goal provable
    only from the tainted fact must come back refuted after the reset, not
    merely absent from a list.
    """
    import z3

    from vera.smt import SmtContext

    smt = SmtContext()
    x = z3.Int("leaked_subject")
    goal = x >= 0

    # Before the reset: the goal is provable ONLY from the tainted fact, so
    # `check_valid` reports it disclosed rather than verified.  That is the
    # premise — without it the assertion after the reset proves nothing.
    smt._tainted_facts.append(x >= 0)
    assert smt.check_valid(goal, []).status == "disclosed", (
        "the fact is not actually carrying this goal, so the cell cannot "
        "show that clearing it matters"
    )

    smt.reset()

    after = smt.check_valid(goal, [])
    assert after.status != "disclosed", (
        "a fact tainted while verifying one function was still available to "
        "the next, so a goal that only it can carry is still reported as a "
        "Tier-3 truth"
    )
    assert not smt._tainted_facts


def test_a_shadowed_builtin_cannot_reach_the_guard_rule(tmp_path: Path) -> None:
    """The guard rule keys on the callee NAME, and E151 is why that is safe.

    Codegen resolves a bare call lexically — `bare_call_denotes_user_fn` — so a
    user declaration named `string_slice` would lower as an ordinary user call
    and take the unconditional `@Nat`-formal guard, while `_call_arg_nat_guarded`
    reading the name alone would answer "never guards" and disclose E504 for an
    argument the module does guard.  The two would invert (CR PR-review).

    They cannot, because E151 refuses the declaration at CHECK time, on both
    routes into codegen's scope table: a top-level function and a `where`
    helper.  So no accepted program reaches the disagreement, and the name is
    a sound key.  This cell exists because that soundness is BORROWED — it
    holds only while E151 does.  If E151 is ever relaxed to allow shadowing,
    this fails and says exactly which question to re-ask.
    """
    for label, source in (
        ("top-level", """\
private fn string_slice(@String, @Nat, @Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ @String.0 }

public fn f(@Int, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_slice(@String.0, @Int.0, 2) }
"""),
        ("where-helper", """\
public fn f(@Int, @String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_slice(@String.0, @Int.0, 2)
}
  where {
    fn string_slice(@String, @Nat, @Nat -> @String)
      requires(true)
      ensures(true)
      effects(pure)
    {
      @String.0
    }
  }
"""),
    ):
        p = tmp_path / f"{label}.vera"
        p.write_text(source, encoding="utf-8")
        proc = _cli("check", "--json", str(p))
        result = json.loads(proc.stdout)
        assert result["ok"] is False, (
            f"{label}: a builtin can now be shadowed, so codegen's lexical "
            f"resolution and the name-keyed guard rule can disagree — "
            f"`_call_arg_nat_guarded` must ask `bare_call_denotes_user_fn` "
            f"over the declaration's own scope before it classifies the callee"
        )
        assert "E151" in [d.get("error_code") for d in result["diagnostics"]], (
            f"{label}: rejected, but not by E151 — check what changed"
        )
