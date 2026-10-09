"""`vera test --distrust`: execute the functions the verifier proved.

Default `vera test` reports a function whose contracts the verifier proved as
`verified` and never runs it, so it cannot see a false Tier 1 — a proof the
compiled program contradicts.  Code generation emits a contract's runtime
check whatever its tier, wherever it can express one, so the module the
tester runs already carries the checks for a proved function; `--distrust` runs the trials on those functions too.
A trial that fails a check standing for an obligation the verifier PROVED is a
refutation (category `refuted`, E703, exit 1).  A check standing for an
obligation the verifier did not prove — a Tier-3 guard — firing on an input
the contract admits is a program finding, reported as a failing trial exactly
as for a Tier-3 function.

The red-first cases are open soundness bugs whose repros refute today:
#1587 (a literal-only expression below `Int`'s minimum proves
`ensures(@Int.result < 0)` and returns 1) and #1555 (`==` between two calls
returning a generic data type compares addresses).  Default mode is pinned
byte-for-byte on a fixed program (`TestDefaultModeUnchanged`); the corpus-wide
default-versus-distrust differential lives in `tests/test_distrust_corpus.py`.
"""

from __future__ import annotations

import importlib.util
import json
import re
import sys
from pathlib import Path
from types import ModuleType

import pytest

from vera import ast
from vera.checker import typecheck_with_artifacts
from vera.cli import USAGE, cmd_errors, cmd_test, main
from vera.errors import ERROR_CODES
from vera.introspect import errors_payload
from vera.obligations.core import ProofObligation
from vera.parser import parse
from vera.tester import FunctionTestResult, TestResult, TrialResult, _TrapIndex
from vera.tester import test as run_test
from vera.trap_registry import EmittedCheck
from vera.transform import transform

ROOT = Path(__file__).resolve().parent.parent
_FILE = "<distrust>"


# =====================================================================
# Helpers
# =====================================================================


def _run(
    source: str,
    *,
    distrust: bool,
    trials: int = 10,
    fn_name: str | None = None,
) -> TestResult:
    """Check *source* and test it in process, as `cmd_test` does.

    The artifact tables are threaded exactly as the CLI threads them, so the
    module the trials execute is the one `vera test` would build.  `distrust`
    reaches the engine only when set, so the default-mode tests below run the
    same call at any revision.
    """
    program = transform(parse(source, file=_FILE))
    diags, artifacts = typecheck_with_artifacts(program, source, file=_FILE)
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, errors[0].format()
    extra: dict[str, bool] = {"distrust": True} if distrust else {}
    return run_test(
        program, source=source, file=_FILE, trials=trials, fn_name=fn_name,
        expr_semantic_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
        alias_env=artifacts.alias_env,
        **extra,
    )


def _fn(result: TestResult, name: str) -> FunctionTestResult:
    for f in result.functions:
        if f.fn_name == name:
            return f
    raise KeyError(f"function {name!r} not in {[f.fn_name for f in result.functions]}")


def _codes(result: TestResult) -> list[str]:
    return [d.error_code for d in result.diagnostics]


def _write(tmp_path: Path, source: str, name: str = "prog.vera") -> str:
    path = tmp_path / name
    path.write_text(source, encoding="utf-8")
    return str(path)


def _cli_json(
    capsys: pytest.CaptureFixture[str], path: str, **kwargs: object,
) -> tuple[int, dict[str, object]]:
    rc = cmd_test(path, as_json=True, **kwargs)  # type: ignore[arg-type]
    return rc, json.loads(capsys.readouterr().out)


def _main(
    monkeypatch: pytest.MonkeyPatch, *argv: str,
) -> int:
    monkeypatch.setattr(sys, "argv", ["vera", *argv])
    with pytest.raises(SystemExit) as exc:
        main()
    return int(exc.value.code or 0)


# =====================================================================
# Fixtures
# =====================================================================

# #1587, verbatim: proved at Tier 1, and `vera run` reports the postcondition
# violated (the u64 literal is -1's bits, so the difference is 1).  `main` takes
# no parameter at all, so it is exercised exactly once.
SRC_1587 = """\
public fn main(-> @Int)
  requires(true)
  ensures(@Int.result < 0)
  effects(pure)
{
  0 - 18446744073709551615
}
"""

# The same false proof behind a parameter, so the generator's own inputs reach
# it: every one of them refutes, since the body ignores the argument.
SRC_1587_PARAM = """\
public fn below_min(@Int -> @Int)
  requires(true)
  ensures(@Int.result < 0)
  effects(pure)
{
  0 - 18446744073709551615
}
"""

# #1555's repro with the function under test made public: `duo(x) == duo(x)`
# compiles to an address comparison, so the proved `ensures(@Bool.result)` fails.
SRC_1555 = """\
private data Duo<A, B> {
  MkDuo(A, B)
}

private fn duo(@Int -> @Duo<Int, Int>)
  requires(true)
  ensures(@Duo<Int, Int>.result == MkDuo(@Int.0, 3))
  effects(pure)
{
  MkDuo(@Int.0, 3)
}

public fn same(@Int -> @Bool)
  requires(true)
  ensures(@Bool.result)
  effects(pure)
{
  duo(@Int.0) == duo(@Int.0)
}
"""

SRC_ADD1 = """\
public fn add1(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{
  @Int.0 + 1
}
"""

SRC_UNIT = """\
public fn answer(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 42)
  effects(pure)
{
  42
}
"""

# Every default-mode category at once: two proved functions (one of them
# #1587's false proof), a Tier-3 function, a verifier-refuted one, and the two
# skip reasons.  Pinned byte-for-byte below in default mode.
SRC_MIXED = """\
public fn add1(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{
  @Int.0 + 1
}

public fn below_min(@Int -> @Int)
  requires(true)
  ensures(@Int.result < 0)
  effects(pure)
{
  0 - 18446744073709551615
}

public fn identity(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(0)
  effects(pure)
{
  @Nat.0
}

public fn double(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + @Int.0)
  effects(pure)
{
  @Int.0 + @Int.0 + 1
}

public forall<T> fn same_value(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn trivial(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


# =====================================================================
# (a) Red-first: a false Tier 1 is refuted
# =====================================================================


class TestRefutedFalseProof:
    """A proof the run contradicts is `refuted`, with E703, and exits 1."""

    def test_default_mode_reports_the_false_proof_verified_and_never_runs_it(
        self,
    ) -> None:
        """The blindness `--distrust` exists for (#1587): default mode calls
        the false proof Tier 1 and runs no trial against it."""
        f = _fn(_run(SRC_1587, distrust=False), "main")
        assert (f.category, f.trials_run) == ("verified", 0)

    def test_1587_zero_parameter_main_is_refuted(self) -> None:
        result = _run(SRC_1587, distrust=True)
        f = _fn(result, "main")
        assert f.category == "refuted", (
            "vera test --distrust must refute #1587's proof: the run returns 1 "
            f"where the proved ensures says < 0; got {f.category!r} ({f.reason})"
        )
        # One trial: a function with no parameter has exactly one input.
        assert (f.trials_run, f.trials_passed, f.trials_failed) == (1, 0, 1)
        trial = f.failures[0]
        assert (trial.status, trial.trap_kind) == ("refuted", "contract_violation")
        assert [(o.fn_name, o.kind, o.expr_text, o.status) for o in trial.refutes] == [
            ("main", "ensures", "@Int.result < 0", "verified"),
        ]
        assert result.summary.refuted == 1
        assert result.summary.verified == 0
        assert _codes(result) == ["E703"]
        (diag,) = result.diagnostics
        assert diag.severity == "error"
        assert "'main'" in diag.description
        assert "ensures(@Int.result < 0)" in diag.description
        # The diagnostic points at the clause that was proved and failed.
        assert (diag.location.line, diag.location.column) == (3, 3)
        assert diag.source_line == "  ensures(@Int.result < 0)"

    def test_1587_behind_a_parameter_names_the_arguments_in_slot_form(
        self,
    ) -> None:
        result = _run(SRC_1587_PARAM, distrust=True, trials=12)
        f = _fn(result, "below_min")
        assert f.category == "refuted"
        # Nine boundary values for one @Int, then the diversity loop to 12.
        assert (f.trials_run, f.trials_failed) == (12, 12)
        assert all(t.status == "refuted" for t in f.failures)
        assert {tuple(t.args) for t in f.failures} == {("@Int.0",)}
        # At most three E703 per function, like E700 today.
        e703 = [d for d in result.diagnostics if d.error_code == "E703"]
        assert len(e703) == 3
        assert re.search(r"@Int\.0 = -?\d+", e703[0].description), e703[0].description

    def test_1555_generic_equality_by_address_is_refuted(self) -> None:
        result = _run(SRC_1555, distrust=True)
        f = _fn(result, "same")
        assert f.category == "refuted", f.reason
        assert f.trials_failed == f.trials_run > 0
        assert {o.expr_text for t in f.failures for o in t.refutes} == {"@Bool.result"}
        assert result.summary.refuted == 1

    def test_cli_exits_1_with_e703_and_a_refuted_function(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Through the real argument parser: `vera test --distrust --json`."""
        path = _write(tmp_path, SRC_1587)
        rc = _main(monkeypatch, "test", "--distrust", "--json", path)
        payload = json.loads(capsys.readouterr().out)
        assert "summary" in payload, (
            "vera test --distrust must run the tester and refute #1587's "
            f"false proof; got {payload}"
        )
        assert rc == 1
        assert payload["ok"] is False
        assert payload["summary"]["refuted"] == 1
        assert [f["category"] for f in payload["functions"]] == ["refuted"]
        assert [d["error_code"] for d in payload["diagnostics"]] == ["E703"]


# =====================================================================
# (b) A correct proof is exercised and holds
# =====================================================================


class TestProvedFunctionsExercised:
    """Under `--distrust` a proved function runs; a sound proof holds."""

    def test_a_correct_proof_is_tested_with_n_trials(self) -> None:
        # 20 is neither the 0 a verified result reports nor the 9 boundary
        # values one @Int seeds, so only a run of the full count passes.
        result = _run(SRC_ADD1, distrust=True, trials=20)
        f = _fn(result, "add1")
        assert f.category == "tested"
        assert (f.trials_run, f.trials_passed, f.trials_failed) == (20, 20, 0)
        assert f.proved is True
        assert "held under 20 trials" in f.reason
        s = result.summary
        assert (s.tested, s.passed, s.verified, s.refuted, s.failed) == (1, 1, 0, 0, 0)
        assert (s.total_trials, s.total_passes) == (20, 20)
        assert result.diagnostics == []

    def test_a_unit_only_proof_runs_once(self) -> None:
        f = _fn(_run(SRC_UNIT, distrust=True, trials=20), "answer")
        assert (f.category, f.trials_run, f.trials_passed) == ("tested", 1, 1)
        assert "held under 1 trial" in f.reason

    def test_cli_clean_run_exits_0(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        rc, payload = _cli_json(capsys, _write(tmp_path, SRC_ADD1),
                                trials=12, distrust=True)
        assert rc == 0
        assert payload["ok"] is True
        assert payload["summary"]["refuted"] == 0  # type: ignore[index]

    def test_text_output_marks_a_held_proof_and_a_refutation(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, SRC_ADD1 + "\n" + SRC_1587_PARAM)
        rc = cmd_test(path, trials=9, distrust=True)
        out = capsys.readouterr().out
        assert rc == 1
        assert re.search(r"add1 \.+ TESTED  \(9/9 passed, Tier 1 proof held\)", out), out
        assert re.search(
            r"below_min \.+ REFUTED \(9/9 trials contradict the Tier 1 proof\)",
            out), out
        assert "E703: " in out
        assert "1 refuted" in out


# =====================================================================
# (c) Default mode is unchanged
# =====================================================================

# `vera test --trials 5` on SRC_MIXED at a21bd281, before `--distrust`
# existed, with the file path replaced by <FILE> and each diagnostic's text
# reduced to its code (the text belongs to the verifier).
_PINNED_TEXT = (
    "\nTesting: <FILE>\n\n"
    "  add1 .................................... VERIFIED (Tier 1)\n"
    "  below_min ............................... VERIFIED (Tier 1)\n"
    "  identity ................................ TESTED  (5/5 passed)\n"
    "  double .................................. FAILED  (verification error (E500))\n"
    "  same_value .............................. SKIPPED (generic function)\n"
    "  trivial ................................. SKIPPED (trivial contracts only)\n"
    "\nDiagnostics:\n"
    "  E500:\n"
    "\nResults: 1 tested (1 passed), 1 failed, 2 verified, 2 skipped\n"
    "Trials:  5 run, 5 passed, 0 failed\n"
)


def _pinned_function(name: str, category: str, reason: str,
                     trials: int = 0) -> dict[str, object]:
    return {
        "name": name, "category": category, "reason": reason,
        "trials_run": trials, "trials_passed": trials, "trials_failed": 0,
        "failures": [],
    }


_PINNED_JSON: dict[str, object] = {
    "ok": False,
    "file": "<FILE>",
    "functions": [
        _pinned_function("add1", "verified", "Tier 1 (proved)"),
        _pinned_function("below_min", "verified", "Tier 1 (proved)"),
        _pinned_function("identity", "tested", "Tier 3 contract (runtime check)", 5),
        _pinned_function("double", "failed", "verification error (E500)"),
        _pinned_function("same_value", "skipped", "generic function"),
        _pinned_function("trivial", "skipped", "trivial contracts only"),
    ],
    "summary": {
        "verified": 2, "tested": 1, "passed": 1, "failed": 1, "skipped": 2,
        "total_trials": 5, "total_passes": 5, "total_failures": 0,
        "unlisted_errors": 0,
    },
    "diagnostics": [("error", "E500", 28, 3)],
}


class TestDefaultModeUnchanged:
    """Without `--distrust`, `vera test` says exactly what it said before."""

    def test_text_output_is_pinned(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, SRC_MIXED)
        rc = cmd_test(path, trials=5)
        out = capsys.readouterr().out.replace(path, "<FILE>")
        out = re.sub(r"(?m)^(  E\d{3}): .*$", r"\1:", out)
        assert (rc, out) == (1, _PINNED_TEXT)

    def test_json_output_is_pinned(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, SRC_MIXED)
        rc = cmd_test(path, as_json=True, trials=5)
        raw = capsys.readouterr().out.replace(path, "<FILE>")
        payload = json.loads(raw)
        payload["diagnostics"] = [
            (d["severity"], d["error_code"], d["location"]["line"],
             d["location"]["column"])
            for d in payload["diagnostics"]
        ]
        assert rc == 1
        # Key ORDER is part of the byte-identity claim, not only the values.
        assert list(json.loads(raw)) == list(_PINNED_JSON)
        assert payload == _PINNED_JSON

    def test_default_mode_never_exercises_a_proof(self) -> None:
        """The structural half: every function default mode calls proved has
        run no trial, and nothing is refuted — so a change that ran proofs by
        default could not pass by agreeing with a snapshot."""
        result = _run(SRC_MIXED, distrust=False, trials=5)
        proved = [f for f in result.functions if f.category == "verified"]
        assert [f.fn_name for f in proved] == ["add1", "below_min"]
        assert all(f.trials_run == 0 and f.failures == [] for f in proved)
        assert result.summary.refuted == 0
        assert "E703" not in _codes(result)


# =====================================================================
# (d) `--fn` narrows the distrust run
# =====================================================================


class TestDistrustFnFilter:

    def test_fn_selects_the_refuted_function_only(self) -> None:
        result = _run(SRC_MIXED, distrust=True, trials=5, fn_name="below_min")
        assert [(f.fn_name, f.category) for f in result.functions] == [
            ("below_min", "refuted"),
        ]
        assert result.summary.refuted == 1

    def test_fn_selects_a_sound_proof_only(self) -> None:
        result = _run(SRC_MIXED, distrust=True, trials=5, fn_name="add1")
        assert [(f.fn_name, f.category) for f in result.functions] == [
            ("add1", "tested"),
        ]
        # below_min is never run, so nothing refutes it.
        assert result.summary.refuted == 0
        assert "E703" not in _codes(result)

    def test_cli_fn_and_distrust_together(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        path = _write(tmp_path, SRC_ADD1 + "\n" + SRC_1587_PARAM)
        rc = _main(monkeypatch, "test", "--distrust", "--fn", "add1",
                   "--json", "--trials", "9", path)
        payload = json.loads(capsys.readouterr().out)
        assert rc == 0
        assert [(f["name"], f["category"]) for f in payload["functions"]] == [
            ("add1", "tested"),
        ]


# =====================================================================
# (f) A trap that refutes nothing stays a finding
# =====================================================================

# The index's obligation is Tier 3 (an unconstrained @Nat into a literal of
# length 3), so the guard is the evidence: the @Nat boundary inputs 10 and 100
# trap it, and that is the guard doing its job on inputs the contract admits.
SRC_INDEX_GUARD = """\
public fn pick(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.0)
  effects(pure)
{
  let @Array<Int> = [10, 20, 30];
  if @Array<Int>.0[@Nat.0] > 0 then {
    @Nat.0
  } else {
    @Nat.0
  }
}
"""

# f's ensures is proved from g's declared contract; g's own ensures is Tier 3
# (its body applies a closure) and false for a negative argument.  So f's
# trials trap on g's runtime check, which is not f's proof failing.
SRC_CALLEE_RUNTIME_ENSURES = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn g(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 };
  apply_fn(@IntFn.0, @Int.0)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  g(@Int.0)
}
"""

# h is proved, but its precondition calls a user function, which the
# generator's bare SMT context cannot translate (#1229).
SRC_USER_PREDICATE_REQUIRES = """\
private fn is_small(@Int -> @Bool)
  requires(true)
  ensures(@Bool.result == (@Int.0 >= 0 && @Int.0 < 100))
  effects(pure)
{
  @Int.0 >= 0 && @Int.0 < 100
}

public fn h(@Int -> @Int)
  requires(is_small(@Int.0))
  ensures(@Int.result > 0)
  effects(pure)
{
  @Int.0 + 1
}
"""


class TestTrapsThatRefuteNothing:
    """A Tier-3 guard firing in a proved function's trial is `error`/`fail`."""

    def test_a_tier3_guard_on_an_admitted_input_is_error_not_refuted(
        self,
    ) -> None:
        result = _run(SRC_INDEX_GUARD, distrust=True, trials=5)
        f = _fn(result, "pick")
        assert f.category == "tested"
        assert (f.trials_run, f.trials_failed) == (5, 2)
        assert {tuple(t.args.values()) for t in f.failures} == {(10,), (100,)}
        for trial in f.failures:
            assert (trial.status, trial.trap_kind) == ("error", "index_out_of_bounds")
            assert trial.refutes == []
            assert trial.attribution.startswith(
                "the runtime check of an obligation the verifier did not prove: "
                "the index_bounds obligation"), trial.attribution
        s = result.summary
        assert (s.refuted, s.unattributed, s.failed, s.tested) == (0, 0, 1, 1)
        assert _codes(result) == ["E700", "E700"]
        # The attribution rides on the E700, so the finding says why it is not
        # a refutation.
        assert "did not prove" in result.diagnostics[0].description

    def test_a_callees_runtime_checked_ensures_failing_is_not_refuted(
        self,
    ) -> None:
        result = _run(SRC_CALLEE_RUNTIME_ENSURES, distrust=True, trials=9)
        f = _fn(result, "f")
        assert f.proved and f.category == "tested"
        assert f.trials_failed > 0
        for trial in f.failures:
            assert (trial.status, trial.trap_kind) == ("fail", "contract_violation")
            assert trial.trap_frames[0] == ("g", False)
            assert trial.attribution == (
                "the runtime check of an obligation the verifier did not "
                "prove: ensures(@Int.result >= 0) of 'g'")
        assert result.summary.refuted == 0
        assert "E703" not in _codes(result)

    def test_a_proof_the_generator_cannot_serve_is_kept_and_disclosed(
        self,
    ) -> None:
        default = _run(SRC_USER_PREDICATE_REQUIRES, distrust=False)
        assert (_fn(default, "h").category, default.diagnostics) == ("verified", [])

        result = _run(SRC_USER_PREDICATE_REQUIRES, distrust=True)
        f = _fn(result, "h")
        assert (f.category, f.proved, f.trials_run) == ("verified", True, 0)
        assert f.reason == (
            "Tier 1, not exercised: cannot generate inputs satisfying "
            "`is_small(@Int.0)` (see #1229)")
        assert result.summary.verified == 1
        (diag,) = result.diagnostics
        assert (diag.error_code, diag.severity) == ("E701", "warning")


# A proof the run cannot exercise is disclosed where a diagnostics-only
# consumer looks: E701 when the generator has no input for it (here the
# precondition admits only values beyond its 2^53 bound), E702 when there is
# nothing to run (here a typed hole elsewhere stops the program compiling,
# E614, which `vera check` allows as W001).
SRC_BEYOND_BOUNDS = """\
public fn above_bound(@Int -> @Int)
  requires(@Int.0 > 10000000000000000)
  ensures(@Int.result > 0)
  effects(pure)
{
  @Int.0
}
"""

SRC_TYPED_HOLE = SRC_ADD1 + """
private fn later(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  ?
}
"""


class TestUnexercisedProofs:
    """A proof `--distrust` cannot run stays verified, and says why."""

    def test_a_precondition_beyond_the_generators_range_is_disclosed(
        self,
    ) -> None:
        default = _run(SRC_BEYOND_BOUNDS, distrust=False)
        assert (_fn(default, "above_bound").category, default.diagnostics) == (
            "verified", [])

        result = _run(SRC_BEYOND_BOUNDS, distrust=True)
        f = _fn(result, "above_bound")
        assert (f.category, f.proved, f.trials_run) == ("verified", True, 0)
        assert f.reason == (
            "Tier 1, not exercised: no input within the generator's bounds "
            "satisfies the precondition")
        (diag,) = result.diagnostics
        assert (diag.error_code, diag.severity) == ("E701", "warning")
        assert "'above_bound'" in diag.description
        assert "not exercised" in diag.description

    def test_a_proof_in_a_program_that_does_not_compile_is_disclosed(
        self,
    ) -> None:
        default = _run(SRC_TYPED_HOLE, distrust=False)
        assert (_fn(default, "add1").category, default.diagnostics) == (
            "verified", [])

        result = _run(SRC_TYPED_HOLE, distrust=True)
        f = _fn(result, "add1")
        assert (f.category, f.proved, f.trials_run, f.reason) == (
            "verified", True, 0, "Tier 1, not exercised: compilation errors")
        (diag,) = result.diagnostics
        assert (diag.error_code, diag.severity) == ("E702", "warning")
        assert diag.description == (
            "Cannot run 'add1' to test its proof: compilation errors.")


# #1598's shape, built from literals so the generator reaches it: the
# boundary value -1 makes the quotient INT_MIN / -1, which traps `overflow` at
# a check the verifier records no obligation for, beside a proved `overflow`
# check of the literal subtraction in the same function.
SRC_1598_QUOTIENT = """\
public fn divide_min(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(@Int.result == (0 - 9223372036854775807 - 1) / @Int.0)
  effects(pure)
{
  (0 - 9223372036854775807 - 1) / @Int.0
}
"""


class TestUnattributedTraps:
    """A trap the record cannot pin on either side is counted and said."""

    def test_1598_quotient_overflow_is_unattributed(self) -> None:
        result = _run(SRC_1598_QUOTIENT, distrust=True, trials=5)
        f = _fn(result, "divide_min")
        assert f.category == "tested"
        # Nine @Int boundaries less the 0 the precondition excludes.
        assert (f.trials_run, f.trials_failed) == (8, 1)
        (trial,) = f.failures
        assert (trial.status, trial.trap_kind, trial.args) == (
            "unattributed", "overflow", {"@Int.0": -1})
        assert trial.attribution.startswith(
            "trap not attributable to an obligation: overflow at ")
        assert "6:3 (no obligation recorded)" in trial.attribution
        assert "(proved)" in trial.attribution
        assert "(1 unattributed)" in f.reason
        s = result.summary
        assert (s.unattributed, s.refuted, s.failed) == (1, 0, 1)
        assert _codes(result) == ["E700"]
        assert trial.attribution in result.diagnostics[0].description

    def test_the_count_reaches_both_outputs(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, SRC_1598_QUOTIENT)
        rc, payload = _cli_json(capsys, path, trials=5, distrust=True)
        assert (rc, payload["ok"]) == (1, False)
        assert payload["summary"]["unattributed"] == 1  # type: ignore[index]
        (function,) = payload["functions"]  # type: ignore[misc]
        (failure,) = function["failures"]
        assert failure["status"] == "unattributed"
        assert failure["attribution"].startswith(
            "trap not attributable to an obligation")
        assert failure["refutes"] == []

        assert cmd_test(path, trials=5, distrust=True) == 1
        out = capsys.readouterr().out
        assert "      trap not attributable to an obligation: overflow" in out
        assert ("Proofs:  1 exercised, 0 refuted, 1 with an unattributed trap, "
                "0 not exercised") in out


# =====================================================================
# The attribution rule, cell by cell
# =====================================================================

_M_FILE = "<matrix>"
_PRE = "codegen/contracts.py:_compile_preconditions"
_POST = "codegen/contracts.py:_compile_postconditions"
_REFINE = "codegen/contracts.py:_emit_refinement_check"

# `f` takes a refined parameter, so a refinement guard can be spanned at it.
_M_DECL_SOURCE = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Pos.0
}
"""


def _matrix_decl() -> ast.FnDecl:
    program = transform(parse(_M_DECL_SOURCE, file=_M_FILE))
    (decl,) = [t.decl for t in program.declarations
               if isinstance(t.decl, ast.FnDecl)]
    return decl


def _cell(state: str, line: int) -> tuple[EmittedCheck, list[ProofObligation]]:
    """One candidate check reading as *state*, at its own line.

    A precondition check comes with the record it would join by span in a
    real module: the function's own `requires`, whose `verified` is the
    verifier's bookkeeping for a clause it assumes, not a proof that any call
    satisfies it.  That record must never make the check read as proved.
    """
    if state == "precondition":
        return EmittedCheck(
            _PRE, "contract_violation", ("requires", "call_pre"),
            "f", line, 3, line, 9, _M_FILE, False,
        ), [ProofObligation(
            fn_name="f", kind="requires", expr_text=f"pre {line}",
            status="verified", line=line, column=3, file=_M_FILE)]
    check = EmittedCheck(_POST, "contract_violation", ("ensures",), "f",
                         line, 3, line, 9, _M_FILE, False)
    status = {"proved": "verified", "not_proved": "tier3"}.get(state)
    records = [] if status is None else [ProofObligation(
        fn_name="f", kind="ensures", expr_text=f"clause {line}",
        status=status, line=line, column=3, file=_M_FILE)]  # type: ignore[arg-type]
    return check, records


def _trap(frames: list[tuple[str, bool]]) -> TrialResult:
    return TrialResult(
        fn_name="f", args={"@Int.0": 7}, status="fail",
        message="Postcondition violation", trap_kind="contract_violation",
        trap_frames=frames,
    )


_ENTRY = [("f", False)]
_NESTED = [("f", False), ("caller", False)]

# Every composition of one or two candidate checks over the four ways a check
# can read, with the verdict at the trial's own call and on a nested call.
# Written out rather than computed, so the table is the specification.
_VERDICTS: dict[tuple[str, ...], tuple[str, str]] = {
    ("proved",): ("refuted", "refuted"),
    ("not_proved",): ("guard", "guard"),
    ("unjoined",): ("unattributed", "unattributed"),
    ("precondition",): ("unattributed", "unattributed"),
    ("proved", "proved"): ("refuted", "refuted"),
    ("proved", "not_proved"): ("unattributed", "unattributed"),
    ("proved", "unjoined"): ("unattributed", "unattributed"),
    ("proved", "precondition"): ("refuted", "unattributed"),
    ("not_proved", "not_proved"): ("guard", "guard"),
    ("not_proved", "unjoined"): ("unattributed", "unattributed"),
    ("not_proved", "precondition"): ("guard", "unattributed"),
    ("unjoined", "unjoined"): ("unattributed", "unattributed"),
    ("unjoined", "precondition"): ("unattributed", "unattributed"),
    ("precondition", "precondition"): ("unattributed", "unattributed"),
}


def _assert_verdict(trial: TrialResult, verdict: str,
                    proved: list[ProofObligation]) -> None:
    if verdict == "refuted":
        assert trial.status == "refuted"
        assert trial.refutes == proved and proved
        assert trial.attribution.startswith("contradicts the Tier 1 proof of ")
    elif verdict == "guard":
        # The status a guard keeps is the one the trial came in with, so the
        # attribution is what tells this cell from one never attributed.
        assert trial.status == "fail"
        assert trial.refutes == []
        assert trial.attribution.startswith(
            "the runtime check of an obligation the verifier did not prove: ")
    else:
        assert trial.status == "unattributed"
        assert trial.refutes == []
        assert trial.attribution.startswith(
            "trap not attributable to an obligation: contract_violation")


@pytest.mark.parametrize("position", ["entry", "nested"])
@pytest.mark.parametrize("states", list(_VERDICTS), ids="+".join)
def test_attribution_matrix(states: tuple[str, ...], position: str) -> None:
    checks: list[EmittedCheck] = []
    records: list[ProofObligation] = []
    for n, state in enumerate(states):
        check, at = _cell(state, 10 + n)
        checks.append(check)
        records.extend(at)
    trial = _trap(_ENTRY if position == "entry" else _NESTED)
    _TrapIndex(checks, records).attribute(trial, _matrix_decl())
    verdict = _VERDICTS[states][0 if position == "entry" else 1]
    proved = [r for r in records
              if r.status == "verified" and r.kind == "ensures"]
    _assert_verdict(trial, verdict, proved)


def test_the_matrix_covers_every_composition() -> None:
    """No composition of up to two of the four readings is missing."""
    readings = ["proved", "not_proved", "unjoined", "precondition"]
    compositions = {(a,) for a in readings} | {
        tuple(sorted((a, b), key=readings.index))
        for a in readings for b in readings}
    assert set(_VERDICTS) == compositions


class TestAttributionEdges:
    """The cells outside the composition matrix."""

    def test_a_trap_with_no_frame_is_unattributed(self) -> None:
        check, records = _cell("proved", 10)
        trial = _trap([])
        _TrapIndex([check], records).attribute(trial, _matrix_decl())
        assert trial.status == "unattributed"
        assert "no frame" in trial.attribution

    def test_a_kind_no_obligation_describes_keeps_its_status(self) -> None:
        check, records = _cell("proved", 10)
        trial = _trap(_ENTRY)
        trial.status, trial.trap_kind = "error", "host_error"
        _TrapIndex([check], records).attribute(trial, _matrix_decl())
        assert (trial.status, trial.refutes) == ("error", [])
        assert trial.attribution == (
            "no obligation describes a trap of kind host_error")

    @pytest.mark.parametrize("kind", [
        "heap_exhausted", "uncaught_exception", "stack_exhausted",
        "out_of_bounds", "unreachable", "host_error", "unknown", ""])
    def test_every_kind_no_obligation_describes_is_left_alone(
        self, kind: str,
    ) -> None:
        """The kinds no emitter maps to an obligation: neither a refutation
        nor an attribution miss, whatever checks the function holds."""
        check, records = _cell("proved", 10)
        trial = _trap(_ENTRY)
        trial.status, trial.trap_kind = "error", kind
        _TrapIndex([check], records).attribute(trial, _matrix_decl())
        assert (trial.status, trial.refutes) == ("error", [])
        assert trial.attribution == (
            f"no obligation describes a trap of kind {kind or 'unknown'}")

    def test_a_proved_check_of_another_function_does_not_count(self) -> None:
        check, records = _cell("proved", 10)
        trial = _trap([("helper", False), ("f", False)])
        _TrapIndex([check], records).attribute(trial, _matrix_decl())
        assert trial.status == "unattributed"
        assert "in 'helper', where the module records no check" in trial.attribution

    def test_a_proved_check_of_another_kind_does_not_count(self) -> None:
        check = EmittedCheck("wasm/operators.py:_emit_overflow_guard", "overflow",
                             ("int_overflow",), "f", 10, 3, 10, 9, _M_FILE, False)
        record = ProofObligation(fn_name="f", kind="int_overflow", expr_text="x",
                                 status="verified", line=10, column=3, file=_M_FILE)
        trial = _trap(_ENTRY)
        _TrapIndex([check], [record]).attribute(trial, _matrix_decl())
        assert trial.status == "unattributed"

    def test_a_record_of_another_obligation_kind_does_not_join(self) -> None:
        check, _ = _cell("unjoined", 10)
        stray = ProofObligation(fn_name="f", kind="int_overflow", expr_text="x",
                                status="verified", line=10, column=3, file=_M_FILE)
        trial = _trap(_ENTRY)
        _TrapIndex([check], [stray]).attribute(trial, _matrix_decl())
        assert trial.status == "unattributed"
        assert "10:3 (no obligation recorded)" in trial.attribution

    def test_one_unproved_clone_at_the_span_is_enough_to_withhold(self) -> None:
        check, (proved,) = _cell("proved", 10)
        clone = ProofObligation(fn_name="f", kind="ensures", expr_text="clause 10",
                                status="timeout", line=10, column=3, file=_M_FILE)
        trial = _trap(_ENTRY)
        _TrapIndex([check], [proved, clone]).attribute(trial, _matrix_decl())
        assert (trial.status, trial.refutes) == ("fail", [])
        assert "did not prove" in trial.attribution

    def test_a_prelude_check_never_joins(self) -> None:
        check = EmittedCheck(_POST, "contract_violation", ("ensures",), "f",
                             10, 3, 10, 9, None, True)
        record = ProofObligation(fn_name="f", kind="ensures", expr_text="x",
                                 status="verified", line=10, column=3, file=None)
        trial = _trap(_ENTRY)
        _TrapIndex([check], [record]).attribute(trial, _matrix_decl())
        assert trial.status == "unattributed"

    def test_the_exn_boundary_frame_is_still_the_trials_own_call(self) -> None:
        proved, records = _cell("proved", 10)
        pre, _ = _cell("precondition", 11)
        trial = _trap([("f", False), ("f$exn_boundary", False)])
        _TrapIndex([proved, pre], records).attribute(trial, _matrix_decl())
        assert trial.status == "refuted"

    @pytest.mark.parametrize("position, status", [
        ("entry", "refuted"), ("nested", "unattributed")])
    def test_a_refined_parameters_guard_is_set_aside_only_at_entry(
        self, position: str, status: str,
    ) -> None:
        decl = _matrix_decl()
        param = decl.params[0].span
        assert param is not None
        guard = EmittedCheck(_REFINE, "contract_violation", ("refine_bind",),
                             "f", param.line, param.column, param.end_line,
                             param.end_column, _M_FILE, False)
        proved, records = _cell("proved", 10)
        trial = _trap(_ENTRY if position == "entry" else _NESTED)
        _TrapIndex([proved, guard], records).attribute(trial, decl)
        assert trial.status == status


# =====================================================================
# (e) The JSON schema under --distrust
# =====================================================================


class TestDistrustJson:

    def test_schema_adds_the_mode_the_category_and_the_count(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, SRC_MIXED)
        rc, payload = _cli_json(capsys, path, trials=5, distrust=True)
        assert rc == 1
        assert payload["distrust"] is True
        assert list(payload) == [
            "ok", "file", "distrust", "functions", "summary", "diagnostics"]
        summary = payload["summary"]
        assert isinstance(summary, dict)
        assert summary["refuted"] == 1
        functions = {f["name"]: f for f in payload["functions"]}  # type: ignore[union-attr]
        assert {n: (f["category"], f["proved"]) for n, f in functions.items()} == {
            "add1": ("tested", True),
            "below_min": ("refuted", True),
            "identity": ("tested", False),
            "double": ("failed", False),
            "same_value": ("skipped", False),
            "trivial": ("skipped", False),
        }
        refuted = functions["below_min"]
        assert refuted["trials_run"] == refuted["trials_failed"] == 9
        assert len(refuted["failures"]) == 5
        failure = refuted["failures"][0]
        assert failure["status"] == "refuted"
        assert failure["trap_kind"] == "contract_violation"
        assert failure["refutes"] == [{
            "function": "below_min", "kind": "ensures",
            "expr": "@Int.result < 0", "file": path, "line": 11, "column": 3,
        }]
        # The verifier's E500 on `double` stands beside the refutation.
        codes = [d["error_code"] for d in payload["diagnostics"]]  # type: ignore[union-attr]
        assert codes == ["E500", "E703", "E703", "E703"]

    def test_default_json_has_none_of_the_distrust_keys(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        _, payload = _cli_json(capsys, _write(tmp_path, SRC_ADD1), trials=5)
        assert "distrust" not in payload
        assert "refuted" not in payload["summary"]  # type: ignore[operator]
        assert all("proved" not in f for f in payload["functions"])  # type: ignore[union-attr]


# =====================================================================
# The flag itself
# =====================================================================


class TestDistrustFlag:

    def test_usage_names_the_flag(self) -> None:
        assert "--distrust" in USAGE

    @pytest.mark.parametrize("command", ["check", "verify", "compile", "run"])
    def test_other_commands_refuse_it(
        self,
        command: str,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        path = _write(tmp_path, SRC_ADD1)
        rc = _main(monkeypatch, command, "--distrust", path)
        err = capsys.readouterr().err
        assert rc == 1
        assert f"--distrust is only accepted by `vera test`, not `vera {command}`" in err

    def test_refusal_is_a_json_envelope_under_json(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        rc = _main(monkeypatch, "verify", "--json", "--distrust",
                   _write(tmp_path, SRC_ADD1))
        payload = json.loads(capsys.readouterr().out)
        assert rc == 1
        assert payload["ok"] is False
        assert "only accepted by `vera test`" in payload["diagnostics"][0]["description"]

    def test_after_a_double_dash_it_is_a_program_argument(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Everything after `--` belongs to the program `vera run` calls."""
        src = """\
public fn echo(@String -> @Nat)
  requires(true)
  ensures(@Nat.result == string_length(@String.0))
  effects(pure)
{
  string_length(@String.0)
}
"""
        path = _write(tmp_path, src)
        rc = _main(monkeypatch, "run", path, "--fn", "echo", "--", "--distrust")
        assert rc == 0
        assert capsys.readouterr().out.strip() == "10"


# =====================================================================
# (g) The code is registered and its diagnostic fully tagged
# =====================================================================


def _diagnostic_fields_gate() -> ModuleType:
    name = "check_diagnostic_fields_distrust"
    spec = importlib.util.spec_from_file_location(
        name, ROOT / "scripts" / "check_diagnostic_fields.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    # Registered before it runs: its dataclasses look their module up there.
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class TestE703Registered:

    def test_registered_with_its_phase_and_release(self) -> None:
        assert "E703" in ERROR_CODES
        items = {i["code"]: i for i in errors_payload()["items"]}  # type: ignore[union-attr, index]
        assert items["E703"]["phase"] == "test"
        assert items["E703"]["since"] == "0.2.1"

    def test_vera_errors_lists_it(self, capsys: pytest.CaptureFixture[str]) -> None:
        assert cmd_errors(as_json=True) == 0
        codes = [i["code"] for i in json.loads(capsys.readouterr().out)["items"]]
        assert "E703" in codes

    def test_the_tester_passes_the_diagnostic_fields_gate(self) -> None:
        gate = _diagnostic_fields_gate()
        tester = [ROOT / "vera" / "tester.py"]
        registry = gate._load_error_codes(ROOT / "vera" / "errors.py")
        assert "E703" in registry
        assert gate.check_paths(tester) == []
        assert gate.spec_ref_violations(tester) == []
        assert gate.error_code_registration_violations(tester, registry) == []
        # One site per code: E700 and E701 are still built in one place each,
        # so the distrust path shares them rather than copying them.
        assert gate.error_code_collision_violations(tester) == []

    def test_the_refutation_carries_every_field(self) -> None:
        (diag,) = _run(SRC_1587, distrust=True).diagnostics
        assert diag.error_code == "E703"
        assert diag.rationale and diag.fix
        assert diag.spec_ref == 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"'


# =====================================================================
# The obligation records a refutation names
# =====================================================================


def test_refutes_holds_the_streams_own_records() -> None:
    """`TrialResult.refutes` is the verifier's ProofObligation, not a copy."""
    f = _fn(_run(SRC_1587, distrust=True), "main")
    (obligation,) = f.failures[0].refutes
    assert isinstance(obligation, ProofObligation)
    assert (obligation.line, obligation.column, obligation.file) == (3, 3, _FILE)
