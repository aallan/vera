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
from typing import Any

import pytest
import z3

from vera import ast
from vera import tester as tester_module
from vera.smt import SmtContext
from vera.checker import typecheck_with_artifacts
from vera.cli import USAGE, cmd_errors, cmd_test, main
from vera.errors import ERROR_CODES
from vera.introspect import errors_payload
from vera.obligations.core import ProofObligation
from vera.parser import parse
from vera.codegen import compile as codegen_compile
from vera.tester import FunctionTestResult, TestResult, TrialResult, _TrapIndex
from vera.tester import test as run_test
from vera.trap_registry import KNOWN_TRAP_DEFECTS, TRAP_EMITTERS, EmittedCheck
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


def _checks(source: str) -> list[EmittedCheck]:
    """The module's record of its checks, compiled as `_run` compiles it."""
    program = transform(parse(source, file=_FILE))
    _, artifacts = typecheck_with_artifacts(program, source, file=_FILE)
    result = codegen_compile(
        program, source=source, file=_FILE,
        expr_semantic_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
    )
    assert result.ok, [d.description for d in result.diagnostics]
    return result.emitted_checks


def _index(source: str) -> _TrapIndex:
    """The engine's `_TrapIndex` for *source*: its checks, its obligations and
    its module text, built as `_run` builds them."""
    from vera.verifier import verify

    program = transform(parse(source, file=_FILE))
    _, artifacts = typecheck_with_artifacts(program, source, file=_FILE)
    verified = verify(
        program, source=source, file=_FILE,
        expr_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
    )
    compiled = codegen_compile(
        program, source=source, file=_FILE,
        expr_semantic_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
    )
    return _TrapIndex(
        compiled.emitted_checks, verified.obligations, compiled.wat)


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

    @pytest.mark.parametrize("subdir", ["plain", "back\\slash"])
    def test_json_output_is_pinned(
        self, subdir: str, tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        # The path is compared parsed, never as text: JSON escapes a
        # backslash, so a Windows path is not a substring of the envelope.
        # The `back\slash` cell holds that on every other platform too.
        if "\\" in subdir and sys.platform == "win32":
            pytest.skip("on Windows every path already holds a backslash")
        (tmp_path / subdir).mkdir()
        path = _write(tmp_path / subdir, SRC_MIXED)
        rc = cmd_test(path, as_json=True, trials=5)
        raw = capsys.readouterr().out
        payload = json.loads(raw)
        assert payload["file"] == path
        payload["file"] = "<FILE>"
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

    def test_an_inconclusive_search_is_not_reported_as_out_of_bounds(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A solver that gives up has shown nothing about the bounds.

        Only the generator's context is replaced, so the verifier still proves
        `add1` while every check the generator makes answers `unknown`.
        """
        class _GivesUp:
            def __init__(self, solver: z3.Solver) -> None:
                self._solver = solver

            def check(self, *assumptions: object) -> z3.CheckSatResult:
                return z3.unknown

            def __getattr__(self, name: str) -> object:
                return getattr(self._solver, name)

        class _GivingUpContext(SmtContext):
            def __init__(self, *args: Any, **kwargs: Any) -> None:
                super().__init__(*args, **kwargs)
                self.solver = _GivesUp(self.solver)  # type: ignore[assignment]

        monkeypatch.setattr(tester_module, "SmtContext", _GivingUpContext)
        result = _run(SRC_ADD1, distrust=True)
        f = _fn(result, "add1")
        assert (f.category, f.proved, f.trials_run) == ("verified", True, 0)
        assert f.reason == (
            "Tier 1, not exercised: the solver's search for an input within "
            "the generator's bounds was inconclusive")
        (diag,) = result.diagnostics
        assert diag.error_code == "E701"
        assert "inconclusive" in diag.description


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
# A trap is judged only by checks the record holds
# =====================================================================

# The class: a trap of a kind some obligation describes, at a site the
# module's record of its checks omits.  The attribution judges a trap by the
# record's checks of its kind in the function it fired in, so a site missing
# from the record is blamed on whichever checks are there, and a proved one
# reads as refuted.  The registry enumerates the natively trapping
# instructions a program reaches that are not checks the language means to
# make (`KNOWN_TRAP_DEFECTS`); each must be recorded by an emitter of its own.
#
# The one entry today is #1482: `float_to_string` takes the integer part it
# prints with an `i64.trunc_f64_s`, which traps on a finite magnitude of 2^63
# or more.  The verifier records the rendering's `float_to_int_domain`
# obligation (Tier 3 for a symbolic value) at the call, at a `show`, and at an
# interpolated part, so the check is spanned there too.  Each rendering is
# placed at line 6, column 17 of `_RENDER`, and its trials (all above 1e19,
# by the precondition) trap.

_RENDER = """\
public fn render(@Float64 -> @Int)
  requires(@Float64.0 > 10000000000000000000.0)
  ensures(@Int.result == 1)
  effects(pure)
{{
  let @String = {rendering};
  {tail}
}}
"""

#: Every way a program reaches the truncation: the rendering, and the
#: expression the verifier's record of it quotes.
_RENDERINGS: dict[str, tuple[str, str]] = {
    "float_to_string": (
        "float_to_string(@Float64.0)", "float_to_string(@Float64.0)"),
    "show": ("show(@Float64.0)", "show(@Float64.0)"),
    "show_of_a_composite": ("show(Some(@Float64.0))", "show(<expr>)"),
    "interpolation": ('"x = \\(@Float64.0)"', "@Float64.0"),
}

#: A program per known trap defect that reaches its site beside a proved
#: check of the same kind (`float_to_int(1.5)`, line 7), keyed by the
#: registry's own site name: a defect entered without one fails
#: `test_every_known_trap_defect_has_a_program`.
_DEFECT_PROGRAMS: dict[str, str] = {
    "wasm/calls_strings.py:_float_to_string_core": _RENDER.format(
        rendering="float_to_string(@Float64.0)", tail="float_to_int(1.5)"),
}


def _site_id(site: object) -> str:
    return str(getattr(site, "site", site))


# A recursive ADT's `show` helper is generated once and shared by every
# `show` of that type, so its truncation belongs to no one call.  Spanned at
# the call that produced it, a trap during another call's rendering named
# that other call: `deep`'s trial was told of `elsewhere`'s `show` at line 20.
SRC_SHARED_SHOW_HELPER = """\
private data FList {
  FNil,
  FCons(Float64, FList)
}

public fn deep(@Float64 -> @Int)
  requires(@Float64.0 > 10000000000000000000.0)
  ensures(@Int.result == 1)
  effects(pure)
{
  let @String = show(FCons(1.5, FCons(@Float64.0, FNil)));
  1
}

private fn elsewhere(@Float64 -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(FCons(1.5, FCons(@Float64.0, FNil)))
}
"""


class TestTrapsAtSitesTheRecordOmitted:
    """A trap at a known trap defect joins its own check, never another's."""

    def test_a_shared_show_helpers_trap_names_no_call(self) -> None:
        result = _run(SRC_SHARED_SHOW_HELPER, distrust=True, trials=3)
        f = _fn(result, "deep")
        assert f.category == "tested", (f.category, f.reason)
        assert f.trials_failed == f.trials_run > 0
        for trial in f.failures:
            assert trial.trap_frames[0][0].startswith("show_"), trial.trap_frames
            assert trial.status == "unattributed", trial.attribution
            assert "elsewhere" not in trial.attribution
            assert "an unlocated check (no obligation recorded)" in (
                trial.attribution)

    def test_every_known_trap_defect_has_a_program(self) -> None:
        assert set(_DEFECT_PROGRAMS) == {s.site for s in KNOWN_TRAP_DEFECTS}

    @pytest.mark.parametrize("site", KNOWN_TRAP_DEFECTS, ids=_site_id)
    def test_a_known_trap_defect_is_recorded_by_its_own_emitter(
        self, site: Any,
    ) -> None:
        """The registry names the emitter that records the site, its row
        states the site's kind and an obligation, and compiling a program
        that reaches the site lists that emitter's check."""
        assert site.emitter is not None, (
            f"{site.site}: a natively trapping site a program reaches must "
            "name the emitter that records it")
        row = TRAP_EMITTERS[site.emitter]
        assert row.kind == site.kind
        assert row.obligations, row
        assert row.per_site
        assert site.instruction in row.via.removeprefix("native:").split()
        recorded = [c for c in _checks(_DEFECT_PROGRAMS[site.site])
                    if c.emitter == site.emitter]
        assert [c.function for c in recorded] == ["render"], recorded

    @pytest.mark.parametrize("site", KNOWN_TRAP_DEFECTS, ids=_site_id)
    def test_a_trap_at_a_known_defect_refutes_no_proof(self, site: Any) -> None:
        """The reviewer's repro: the trap is the truncation, and the only
        other check of its kind in the function is a proved one.  Judged by
        that one alone, a correct proof read as refuted."""
        result = _run(_DEFECT_PROGRAMS[site.site], distrust=True, trials=5)
        f = _fn(result, "render")
        assert f.category == "tested", (f.category, f.reason)
        assert result.summary.refuted == 0
        assert "E703" not in _codes(result)
        assert f.trials_failed == f.trials_run == 5
        for trial in f.failures:
            assert (trial.status, trial.trap_kind, trial.refutes) == (
                "unattributed", site.kind, [])
            assert "6:17 (not proved)" in trial.attribution, trial.attribution
            assert "7:3 (proved)" in trial.attribution, trial.attribution

    @pytest.mark.parametrize("path", list(_RENDERINGS))
    def test_each_rendering_joins_the_record_of_its_obligation(
        self, path: str,
    ) -> None:
        """Alone, the truncation is the runtime check of the rendering's
        Tier-3 obligation: a guard firing on an input the contract admits,
        reported as a failing trial, at the site the verifier recorded."""
        rendering, quoted = _RENDERINGS[path]
        result = _run(_RENDER.format(rendering=rendering, tail="1"),
                      distrust=True, trials=5)
        f = _fn(result, "render")
        assert f.category == "tested", (f.category, f.reason)
        assert f.trials_failed == f.trials_run == 5
        for trial in f.failures:
            assert (trial.status, trial.trap_kind) == ("error", "float_conversion")
            assert trial.attribution == (
                "the runtime check of an obligation the verifier did not "
                "prove: the float_to_int_domain obligation on "
                f"`{quoted}` (line 6)"), trial.attribution
        s = result.summary
        assert (s.refuted, s.unattributed, s.failed) == (0, 0, 1)

    @pytest.mark.parametrize("path", list(_RENDERINGS))
    def test_each_rendering_beside_a_proved_check_is_unattributed(
        self, path: str,
    ) -> None:
        rendering, _ = _RENDERINGS[path]
        result = _run(
            _RENDER.format(rendering=rendering, tail="float_to_int(1.5)"),
            distrust=True, trials=5)
        f = _fn(result, "render")
        assert f.category == "tested", (f.category, f.reason)
        assert result.summary.refuted == 0
        for trial in f.failures:
            assert trial.status == "unattributed"
            assert "(not proved)" in trial.attribution
            assert "7:3 (proved)" in trial.attribution


# =====================================================================
# A proof no runtime check stands for is not exercised
# =====================================================================

# A proof can be tested only through checks that stand for what the verifier
# proved.  Code generation emits no `ensures` check for a `String` or `Array`
# result, and none for a clause it cannot compile, so no trial can contradict
# such a clause, and a run that passes says nothing about it: the reason names
# it.  A function is not run at all only when NO check its run reaches stands
# for a proved obligation — its contract clauses, the operations in its body,
# a callee's — since anything less would skip a run that can refute (the
# round-2 class below).

# The reviewer's repro: proved (#1587's literal reads as -1), yet `vera run
# --fn s -- 3` returns "pos", and nothing checks the `ensures`.
SRC_STRING_RETURN = """\
public fn s(@Int -> @String)
  requires(true)
  ensures(@String.result == "neg")
  effects(pure)
{
  if 0 - 18446744073709551615 < 0 then { "neg" } else { "pos" }
}
"""

# The `Array` case, and a caller whose proof rests on the unchecked clause:
# `wrap`'s own `ensures` is checked, and its trials refute it.
SRC_ARRAY_RETURN = """\
public fn pair_or_one(@Int -> @Array<Int>)
  requires(true)
  ensures(array_length(@Array<Int>.result) == 2)
  effects(pure)
{
  if 0 - 18446744073709551615 < 0 then { [1, 2] } else { [1] }
}

public fn wrap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 2)
  effects(pure)
{
  array_length(pair_or_one(@Int.0))
}
"""

# One proved clause is checked (the `assert`) and one is not (the `ensures`
# over a `String` result): the function runs, and its reason names the gap.
SRC_PARTLY_CHECKED = """\
public fn tag(@Int -> @String)
  requires(@Int.0 > 0)
  ensures(@String.result == "pos")
  effects(pure)
{
  assert(@Int.0 > 0);
  "pos"
}
"""

# A refined return is proved and checked, though the two records sit at
# different nodes: the verifier's `refine_bind` at the body, the guard at the
# return type.  Read by exact span alone it would join nothing.
SRC_REFINED_RETURN = """\
type Pos = { @Int | @Int.0 > 0 };

public fn succ_pos(@Int -> @Pos)
  requires(@Int.0 >= 0 && @Int.0 < 1000)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}
"""


class TestProofsNoCheckStandsFor:
    """A proof is exercised only through the checks that stand for it."""

    def test_a_proof_with_no_check_is_not_exercised(self) -> None:
        result = _run(SRC_STRING_RETURN, distrust=True, trials=9)
        f = _fn(result, "s")
        assert (f.category, f.proved, f.trials_run) == ("verified", True, 0), (
            f.category, f.reason)
        assert f.reason == (
            "Tier 1, not exercised: code generation emits no runtime check "
            'for `ensures(@String.result == "neg")`')
        (diag,) = result.diagnostics
        assert (diag.error_code, diag.severity) == ("E702", "warning")
        assert diag.description == (
            "Cannot test the proof of 's': code generation emits no runtime "
            'check for `ensures(@String.result == "neg")`.')
        s = result.summary
        assert (s.verified, s.tested, s.total_trials) == (1, 0, 0)

    def test_default_mode_reports_it_as_before(self) -> None:
        f = _fn(_run(SRC_STRING_RETURN, distrust=False), "s")
        assert (f.category, f.reason, f.trials_run) == (
            "verified", "Tier 1 (proved)", 0)

    def test_the_text_never_says_it_held(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, SRC_STRING_RETURN)
        assert cmd_test(path, trials=9, distrust=True) == 0
        out = capsys.readouterr().out
        assert "proof held" not in out
        assert re.search(
            r"s \.+ VERIFIED \(Tier 1, not exercised: code generation emits "
            r"no runtime check for", out), out
        assert ("Proofs:  0 exercised, 0 refuted, 0 with an unattributed "
                "trap, 1 not exercised") in out

    def test_an_array_result_and_a_caller_resting_on_it(self) -> None:
        result = _run(SRC_ARRAY_RETURN, distrust=True, trials=9)
        p = _fn(result, "pair_or_one")
        assert (p.category, p.trials_run) == ("verified", 0), p.reason
        # The clause as the verifier's record renders it, as E703 names one.
        assert p.reason.endswith(
            "`ensures(array_length(@Array<@Int>.result) == 2)`"), p.reason
        assert _fn(result, "wrap").category == "refuted"
        assert sorted(_codes(result)) == ["E702", "E703", "E703", "E703"]

    def test_a_partly_checked_proof_runs_and_names_the_gap(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        result = _run(SRC_PARTLY_CHECKED, distrust=True, trials=9)
        f = _fn(result, "tag")
        assert (f.category, f.trials_run, f.trials_failed) == ("tested", 9, 0)
        assert f.unchecked == ['ensures(@String.result == "pos")']
        assert f.reason == (
            "Tier 1, the proof held under 9 trials; code generation emits no "
            'runtime check for `ensures(@String.result == "pos")`, so no '
            "trial tests it")
        assert result.diagnostics == []

        path = _write(tmp_path, SRC_PARTLY_CHECKED)
        assert cmd_test(path, trials=9, distrust=True) == 0
        out = capsys.readouterr().out
        assert re.search(
            r'tag \.+ TESTED  \(9/9 passed, Tier 1 proof held; no runtime '
            r'check for `ensures\(@String\.result == "pos"\)`\)', out), out
        assert "Proofs:  1 exercised" in out

    def test_a_refined_return_is_a_checked_clause(self) -> None:
        result = _run(SRC_REFINED_RETURN, distrust=True, trials=9)
        f = _fn(result, "succ_pos")
        assert (f.category, f.unchecked) == ("tested", []), f.reason
        assert (f.trials_run, f.trials_failed) == (9, 0)
        assert f.reason == "Tier 1, the proof held under 9 trials"


# The class (round 2): a proved function a run of which reaches a check
# standing for a proved obligation, though none of its contract clauses has
# one.  Skipping it skips a run that can refute.

# The reviewer's repro: the `ensures` over a `String` result has no check, but
# the index at 7:14 is proved (#1587's literal reads it as 1) and checked, and
# every run indexes 7.
SRC_UNCHECKED_ENSURES_BESIDE_A_PROOF = """\
public fn label(@Int -> @String)
  requires(true)
  ensures(@String.result == "ok")
  effects(pure)
{
  let @Array<Int> = [10, 20, 30];
  let @Int = @Array<Int>.0[if 0 - 18446744073709551615 < 0 then { 1 } else { 7 }];
  "ok"
}
"""

# The `Array` case: nothing checks the `ensures` over the result, but each
# element's `Pos` is proved and guarded where the array is built, and the
# second element is 0 at run time.
SRC_REFINED_ELEMENTS = """\
type Pos = { @Int | @Int.0 > 0 };

public fn positives(@Int -> @Array<Pos>)
  requires(true)
  ensures(array_length(@Array<Pos>.result) == 2)
  effects(pure)
{
  [1, if 0 - 18446744073709551615 < 0 then { 1 } else { 0 }]
}
"""

# A tuple component's refinement is recorded, and guarded, at the component
# the function builds, not at the body; with #1587's literal the component is
# 0 at run time.
SRC_REFINED_COMPONENT = """\
type Pos = { @Int | @Int.0 > 0 };

public fn pos_pair(@Int -> @Tuple<Pos, Int>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  Tuple(if 0 - 18446744073709551615 < 0 then { @Int.0 } else { 0 }, 3)
}
"""

# A proof reached only through a callee: nothing of `s2`'s own has a check,
# and its private `helper`'s false `ensures` (#1587's literal) is checked
# inside `helper`, which every run of `s2` calls.
SRC_CALLEE_PROOF = """\
private fn helper(@Int -> @Int)
  requires(true)
  ensures(@Int.result < 0)
  effects(pure)
{
  0 - 18446744073709551615
}

public fn s2(@Int -> @String)
  requires(true)
  ensures(@String.result == "ok")
  effects(pure)
{
  let @Int = helper(@Int.0);
  "ok"
}
"""

# The proved `nat_bind` is recorded at the value (`Tuple(@Int.0, 5)`) and
# guarded at the binders, so the exact-span join places the guards nowhere
# (#1633); they may stand for the proof, so the function is run.
SRC_UNJOINED_GUARD = """\
public fn destruct_narrow(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = Tuple(@Int.0, 5);
  @Nat.0
}
"""

# The only check a run reaches guards an obligation the verifier did not
# prove (the index is Tier 3), and the `ensures` has none: nothing proved can
# be tested.
SRC_ONLY_A_TIER3_GUARD = """\
public fn pick_label(@Int -> @String)
  requires(true)
  ensures(@String.result == "x")
  effects(pure)
{
  let @Array<Int> = [1, 2, 3];
  let @Int = @Array<Int>.0[@Int.0];
  "x"
}
"""

# Nothing the verifier proved has a check: the only check is the `requires`,
# which the trial's arguments are generated to satisfy, so it is set aside.
SRC_ONLY_A_REQUIRES = """\
public fn keep(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


class TestAProofIsRunWhereverACheckStandsForIt:
    """Not exercised only when no check a run reaches stands for a proof."""

    def test_an_unchecked_ensures_beside_a_checked_false_proof_is_refuted(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        result = _run(SRC_UNCHECKED_ENSURES_BESIDE_A_PROOF, distrust=True,
                      trials=3)
        f = _fn(result, "label")
        assert f.category == "refuted", (f.category, f.reason)
        assert f.trials_failed == f.trials_run > 0
        assert {(o.kind, o.line, o.column) for t in f.failures
                for o in t.refutes} == {("index_bounds", 7, 14)}
        assert f.unchecked == ['ensures(@String.result == "ok")']
        assert f.reason.endswith(
            '; code generation emits no runtime check for '
            '`ensures(@String.result == "ok")`, so no trial tests it'), f.reason
        assert "E702" not in _codes(result)
        rc = cmd_test(_write(tmp_path, SRC_UNCHECKED_ENSURES_BESIDE_A_PROOF),
                      trials=3, distrust=True)
        assert rc == 1, capsys.readouterr().out

    def test_a_refined_element_proof_beside_an_unchecked_ensures_runs(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Run, as at 441c9bd9: every trial fails.  The element's proved
        guard and the return type's guard, which joins no record, are both
        candidates, so each trap is unattributed rather than refuting."""
        result = _run(SRC_REFINED_ELEMENTS, distrust=True, trials=3)
        f = _fn(result, "positives")
        assert f.category == "tested", (f.category, f.reason)
        assert f.trials_failed == f.trials_run > 0
        assert {t.status for t in f.failures} == {"unattributed"}
        assert f.unchecked == [
            "ensures(array_length(@Array<@Pos>.result) == 2)"]
        assert "E702" not in _codes(result)
        assert cmd_test(_write(tmp_path, SRC_REFINED_ELEMENTS), trials=3,
                        distrust=True) == 1, capsys.readouterr().out

    def test_a_component_refined_return_is_a_checked_clause(self) -> None:
        program = transform(parse(SRC_REFINED_COMPONENT, file=_FILE))
        (decl,) = [t.decl for t in program.declarations
                   if isinstance(t.decl, ast.FnDecl)]
        index = _index(SRC_REFINED_COMPONENT)
        assert index.proof_clauses(decl, _FILE) == (
            ["the refinement of its return type `@Tuple<@Pos, @Int>`"], [])
        f = _fn(_run(SRC_REFINED_COMPONENT, distrust=True, trials=3),
                "pos_pair")
        assert f.category == "tested", (f.category, f.reason)
        assert f.trials_failed == f.trials_run > 0
        assert {t.status for t in f.failures} == {"unattributed"}

    def test_a_proof_reached_through_a_callee_is_refuted(self) -> None:
        result = _run(SRC_CALLEE_PROOF, distrust=True, trials=3)
        f = _fn(result, "s2")
        assert f.category == "refuted", (f.category, f.reason)
        assert {(o.fn_name, o.kind) for t in f.failures
                for o in t.refutes} == {("helper", "ensures")}
        assert f.unchecked == ['ensures(@String.result == "ok")']

    def test_a_function_whose_only_check_is_its_requires_is_not_exercised(
        self,
    ) -> None:
        result = _run(SRC_ONLY_A_REQUIRES, distrust=True, trials=9)
        f = _fn(result, "keep")
        assert (f.category, f.proved, f.trials_run) == ("verified", True, 0), (
            f.category, f.reason)
        assert f.reason == (
            "Tier 1, not exercised: no runtime check a run of it reaches "
            "stands for an obligation the verifier proved")
        (diag,) = result.diagnostics
        assert (diag.error_code, diag.severity) == ("E702", "warning")

    def test_a_guard_the_join_places_nowhere_still_runs(self) -> None:
        f = _fn(_run(SRC_UNJOINED_GUARD, distrust=True, trials=5),
                "destruct_narrow")
        assert (f.category, f.trials_failed) == ("tested", 0), f.reason
        assert f.trials_run > 0

    def test_a_run_reaching_only_a_tier3_guard_is_not_exercised(self) -> None:
        result = _run(SRC_ONLY_A_TIER3_GUARD, distrust=True, trials=5)
        f = _fn(result, "pick_label")
        assert (f.category, f.trials_run) == ("verified", 0), f.reason
        assert f.reason == (
            "Tier 1, not exercised: code generation emits no runtime check "
            'for `ensures(@String.result == "x")`')
        assert _codes(result) == ["E702"]

    def test_the_closure_table_is_reached_through_call_indirect(self) -> None:
        """A closure body runs through the table, not a named call."""
        wat = (
            "  (table 1 funcref)\n"
            "  (elem (i32.const 0) func $anon_0)\n"
            "  (func $f (param $p0 i64) (result i64)\n"
            "    call_indirect (type $closure_sig_0)\n"
            "  )\n"
            "  (func $anon_0 (param $env i32) (result i64)\n"
            "    call $helper\n"
            "  )\n"
            "  (func $helper (result i64)\n"
            "    i64.const 1\n"
            "  )\n"
            "  (func $unrelated (result i64)\n"
            "    i64.const 2\n"
            "  )\n")
        index = _TrapIndex([], [], wat)
        assert index.reachable("f") == {"f", "anon_0", "helper"}
        assert index.reachable("helper") == {"helper"}


#: How one check a run of `f` reaches reads, whether it lets the run test a
#: proof, and where it sits: in `f` itself or in `g`, which `f` calls.
_EXERCISE_CELLS: dict[str, tuple[str, bool, bool]] = {
    # name: (where, a prelude function's, exercises)
    "proved_in_f": ("f", False, True),
    "proved_in_callee": ("g", False, True),
    "not_proved_in_f": ("f", False, False),
    "not_proved_in_callee": ("g", False, False),
    "unjoined_in_f": ("f", False, True),
    "unjoined_in_callee": ("g", False, True),
    "unjoined_in_a_prelude_function": ("g", True, False),
    "own_precondition": ("f", False, False),
    "own_refined_parameter_guard": ("f", False, False),
    "callee_precondition": ("g", False, True),
    "prelude_precondition": ("g", True, True),
    "in_an_unreached_function": ("h", False, False),
}

_EXERCISE_WAT = (
    "  (func $f (param $p0 i64) (result i64)\n    call $g\n  )\n"
    "  (func $g (param $p0 i64) (result i64)\n    i64.const 1\n  )\n"
    "  (func $h (result i64)\n    i64.const 2\n  )\n")


@pytest.mark.parametrize("cell", list(_EXERCISE_CELLS))
def test_what_lets_a_run_test_a_proof(cell: str) -> None:
    where, prelude, expected = _EXERCISE_CELLS[cell]
    decl = _matrix_decl()
    records: list[ProofObligation] = []
    if cell == "own_refined_parameter_guard":
        param = decl.params[0].span
        assert param is not None
        check = EmittedCheck(_REFINE, "contract_violation", ("refine_bind",),
                             "f", param.line, param.column, param.end_line,
                             param.end_column, _M_FILE, False)
    elif cell.endswith("precondition"):
        check, records = _cell("precondition", 10)
        check = EmittedCheck(check.emitter, check.kind, check.obligations,
                             where, check.line, check.column, check.end_line,
                             check.end_column, None if prelude else _M_FILE,
                             prelude)
    else:
        state = ("proved" if cell.startswith("proved")
                 else "not_proved" if cell.startswith("not_proved")
                 else "proved" if cell == "in_an_unreached_function"
                 else "unjoined")
        base, records = _cell(state, 10)
        check = EmittedCheck(base.emitter, base.kind, base.obligations, where,
                             base.line, base.column, base.end_line,
                             base.end_column, None if prelude else _M_FILE,
                             prelude)
    index = _TrapIndex([check], records, _EXERCISE_WAT)
    assert index.exercises(decl, _M_FILE) is expected


def test_the_exercise_matrix_covers_every_reading() -> None:
    """Every way `_TrapIndex._read` can read a check, in the function and in
    a callee, plus the prologue and a function the run never reaches."""
    assert {"proved", "not_proved", "unjoined", "precondition"} <= {
        part for cell in _EXERCISE_CELLS for part in (
            "proved", "not_proved", "unjoined", "precondition")
        if part in cell}
    assert {where for where, _, _ in _EXERCISE_CELLS.values()} == {
        "f", "g", "h"}


# The reviewer's repro: `opt_pos` and `same` are proved, but the generator
# encodes no `Option<Int>` and no type variable, so `vera test` skips both in
# either mode.  (A generic is verified through its instantiations, hence the
# private caller.)  The controls prove nothing, so leave nothing unexercised:
# `const_one`, never instantiated, has its `ensures` recorded Tier 3, and
# `safe_idx` has only trivial contracts.
SRC_SKIPPED_PROOFS = """\
public fn opt_pos(@Option<Int> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> if @Int.0 >= 0 then { @Int.0 } else { 0 },
    None -> 0
  }
}

public forall<T> fn same(@T -> @T)
  requires(true)
  ensures(@T.result == @T.0)
  effects(pure)
{
  @T.0
}

private fn use_same(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  same(@Int.0)
}

public forall<T> fn const_one(@T -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  1
}

public fn safe_idx(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [1, 2, 3];
  @Array<Int>.0[1]
}
"""


class TestProofsTheGeneratorCannotServe:
    """A proved function skipped for its parameters is a proof not exercised."""

    @pytest.mark.parametrize("distrust", [False, True])
    def test_proved_is_read_for_every_function(self, distrust: bool) -> None:
        result = _run(SRC_SKIPPED_PROOFS, distrust=distrust)
        assert {f.fn_name: f.proved for f in result.functions} == {
            "opt_pos": True, "same": True, "const_one": False,
            "safe_idx": False}

    def test_default_mode_skips_them_as_before(self) -> None:
        result = _run(SRC_SKIPPED_PROOFS, distrust=False)
        assert [(f.fn_name, f.category, f.reason)
                for f in result.functions] == [
            ("opt_pos", "skipped",
             "cannot generate Option<Int> inputs (see #169)"),
            ("same", "skipped", "generic function"),
            ("const_one", "skipped", "generic function"),
            ("safe_idx", "skipped", "trivial contracts only"),
        ]
        assert result.diagnostics == []
        assert (result.summary.skipped, result.summary.verified) == (4, 0)

    def test_under_distrust_each_is_a_proof_not_exercised(self) -> None:
        result = _run(SRC_SKIPPED_PROOFS, distrust=True)
        assert [(f.fn_name, f.category, f.trials_run, f.reason)
                for f in result.functions] == [
            ("opt_pos", "verified", 0, "Tier 1, not exercised: cannot "
             "generate Option<Int> inputs (see #169)"),
            ("same", "verified", 0,
             "Tier 1, not exercised: generic function"),
            ("const_one", "skipped", 0, "generic function"),
            ("safe_idx", "skipped", 0, "trivial contracts only"),
        ]
        assert [(d.error_code, d.severity, d.description)
                for d in result.diagnostics] == [
            ("E701", "warning",
             "Cannot generate test inputs for 'opt_pos': the generator "
             "encodes no Option<Int> value (see #169), so its proof is not "
             "exercised."),
            ("E701", "warning",
             "Cannot generate test inputs for 'same': it is generic, "
             "so its proof is not exercised."),
        ]
        s = result.summary
        assert (s.verified, s.skipped, s.tested) == (2, 2, 0)

    def test_both_outputs_count_them(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, SRC_SKIPPED_PROOFS)
        rc, payload = _cli_json(capsys, path, distrust=True)
        assert rc == 0
        assert {f["name"]: (f["category"], f["proved"])
                for f in payload["functions"]} == {  # type: ignore[union-attr]
            "opt_pos": ("verified", True),
            "same": ("verified", True),
            "const_one": ("skipped", False),
            "safe_idx": ("skipped", False),
        }
        assert cmd_test(path, distrust=True) == 0
        out = capsys.readouterr().out
        assert ("Proofs:  0 exercised, 0 refuted, 0 with an unattributed "
                "trap, 2 not exercised") in out

    def test_the_default_json_carries_no_proved_key(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        _, payload = _cli_json(capsys, _write(tmp_path, SRC_SKIPPED_PROOFS))
        assert all("proved" not in f for f in payload["functions"])  # type: ignore[union-attr]


# Every kind of proved clause, each with and without the check that stands
# for it.  Parsed only, for its spans: the records and checks are built here.
_CLAUSES_SOURCE = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Nat -> @Pos)
  requires(true)
  ensures(@Pos.result > 0)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  assert(@Nat.0 >= 0);
  1
}
"""


def _clauses_decl() -> ast.FnDecl:
    program = transform(parse(_CLAUSES_SOURCE, file=_M_FILE))
    (decl,) = [t.decl for t in program.declarations
               if isinstance(t.decl, ast.FnDecl)]
    return decl


def _span_of(node: ast.Node) -> tuple[int, int, int, int]:
    assert node.span is not None
    s = node.span
    return s.line, s.column, s.end_line, s.end_column


def _clause_parts(
    decl: ast.FnDecl,
) -> dict[str, tuple[ProofObligation, EmittedCheck]]:
    """Each clause kind's proved record, and the check that stands for it."""
    ensures, _trivial, decreases = (
        c for c in decl.contracts if isinstance(c, (ast.Ensures, ast.Decreases)))
    (assertion,) = [s.expr for s in decl.body.statements
                    if isinstance(s, ast.ExprStmt)]
    parts: dict[str, tuple[ProofObligation, EmittedCheck]] = {}
    for name, node, record_node, kind, emitter, trap in (
        ("ensures", ensures, ensures, "ensures", _POST, "contract_violation"),
        ("decreases", decreases, decreases, "decreases",
         "codegen/contracts.py:_compile_decreases_entry", "contract_violation"),
        ("assert", assertion, assertion, "assert",
         "wasm/operators.py:_translate_assert", "assertion_failed"),
        ("refined_return", decl.return_type, decl.body, "refine_bind",
         _REFINE, "contract_violation"),
    ):
        line, column, end_line, end_column = _span_of(node)
        r_line, r_column, _, _ = _span_of(record_node)
        record = ProofObligation(
            fn_name="f", kind=kind, expr_text=f"{name} clause",  # type: ignore[arg-type]
            status="verified", line=r_line, column=r_column, file=_M_FILE)
        check = EmittedCheck(
            emitter, trap, TRAP_EMITTERS[emitter].obligations, "f",
            line, column, end_line, end_column, _M_FILE, False)
        parts[name] = (record, check)
    return parts


_CLAUSE_KINDS = ["ensures", "decreases", "assert", "refined_return"]


@pytest.mark.parametrize("checked", [
    frozenset(k for n, k in enumerate(_CLAUSE_KINDS) if mask >> n & 1)
    for mask in range(2 ** len(_CLAUSE_KINDS))
], ids=lambda s: "+".join(sorted(s)) or "none")
def test_each_proved_clause_joins_the_check_that_stands_for_it(
    checked: frozenset[str],
) -> None:
    decl = _clauses_decl()
    parts = _clause_parts(decl)
    records = [record for record, _ in parts.values()]
    checks = [check for name, (_, check) in parts.items() if name in checked]
    have, lack = _TrapIndex(checks, records).proof_clauses(decl, _M_FILE)
    named = {
        "ensures": "ensures(ensures clause)",
        "decreases": "decreases(decreases clause)",
        "assert": "assert(assert clause)",
        "refined_return": "the refinement of its return type `@Pos`",
    }
    assert sorted(have) == sorted(named[k] for k in checked)
    assert sorted(lack) == sorted(
        named[k] for k in _CLAUSE_KINDS if k not in checked)


class TestProofClauseEdges:
    """What is not a proved clause, and what does not stand for one."""

    def test_a_trivial_ensures_is_no_clause(self) -> None:
        """`ensures(true)` needs no check, and code generation emits none,
        though the verifier records it verified."""
        decl = _clauses_decl()
        trivial = [c for c in decl.contracts if isinstance(c, ast.Ensures)][1]
        line, column, _, _ = _span_of(trivial)
        record = ProofObligation(
            fn_name="f", kind="ensures", expr_text="true", status="verified",
            line=line, column=column, file=_M_FILE)
        assert _TrapIndex([], [record]).proof_clauses(decl, _M_FILE) == ([], [])

    def test_a_clause_that_was_not_proved_is_not_a_proved_clause(self) -> None:
        decl = _clauses_decl()
        parts = _clause_parts(decl)
        records = [r for r, _ in parts.values()]
        for record in records:
            record.status = "tier3"
        assert _TrapIndex([], records).proof_clauses(decl, _M_FILE) == ([], [])

    def test_a_check_of_another_obligation_kind_does_not_stand_for_it(
        self,
    ) -> None:
        decl = _clauses_decl()
        record, check = _clause_parts(decl)["ensures"]
        stray = EmittedCheck(
            "wasm/operators.py:_emit_overflow_guard", "overflow",
            ("int_overflow",), "f", check.line, check.column, check.end_line,
            check.end_column, _M_FILE, False)
        have, lack = _TrapIndex([stray], [record]).proof_clauses(decl, _M_FILE)
        assert (have, lack) == ([], ["ensures(ensures clause)"])

    def test_a_prelude_check_does_not_stand_for_it(self) -> None:
        decl = _clauses_decl()
        record, check = _clause_parts(decl)["ensures"]
        prelude = EmittedCheck(
            check.emitter, check.kind, check.obligations, "f", check.line,
            check.column, check.end_line, check.end_column, None, True)
        have, lack = _TrapIndex([prelude], [record]).proof_clauses(decl, _M_FILE)
        assert (have, lack) == ([], ["ensures(ensures clause)"])

    def test_a_refinement_guard_outside_the_return_type_does_not_count(
        self,
    ) -> None:
        decl = _clauses_decl()
        record, _ = _clause_parts(decl)["refined_return"]
        line, column, end_line, end_column = _span_of(decl.params[0])
        guard = EmittedCheck(
            _REFINE, "contract_violation", ("refine_bind",), "f", line,
            column, end_line, end_column, _M_FILE, False)
        have, lack = _TrapIndex([guard], [record]).proof_clauses(decl, _M_FILE)
        assert (have, lack) == (
            [], ["the refinement of its return type `@Pos`"])


# =====================================================================
# A refutation whose proof rests on an `assume`
# =====================================================================

# The class: E703's text for a refuted proof whose premises include an
# `assume`, which the verifier takes on trust (W003).  A false `assume` lets
# it prove what the program then violates, which is no defect of the
# verifier, so the text says which `assume` the proof rests on, says that
# these arguments violate it only where the tester has evaluated it on them,
# and blames the verifier only where the `assume` held.

# The reviewer's repro.  `trusting` is proved from its own `assume`, which
# the generator's `@Int.0 = 0` violates; `via_callee` is proved from
# `helper`'s `ensures`, which rests on `helper`'s `assume`.
SRC_ASSUME = """\
public fn trusting(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  assume(@Int.0 > 0);
  @Int.0
}

private fn helper(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  assume(@Int.0 > 0);
  @Int.0
}

public fn via_callee(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  helper(@Int.0)
}
"""

_SOUNDNESS = (
    "the verifier proved something about a program other than the one that "
    "runs")

# Two `where` helpers of one name: `f1`'s rests on an `assume`, `f2`'s
# carries #1587's false proof and no `assume`.
SRC_SAME_NAMED_HELPERS = """\
public fn f1(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  h(@Int.0)
}
where {
  fn h(@Int -> @Int)
    requires(true)
    ensures(@Int.result > 0)
    effects(pure)
  {
    assume(@Int.0 > 0);
    @Int.0
  }
}

public fn f2(@Int -> @Int)
  requires(true)
  ensures(@Int.result < 0)
  effects(pure)
{
  h(@Int.0)
}
where {
  fn h(@Int -> @Int)
    requires(true)
    ensures(@Int.result < 0)
    effects(pure)
  {
    0 - 18446744073709551615
  }
}
"""

#: Where an `assume` sits relative to the refuted proof, and whether these
#: arguments violate it: the comparison `f`'s `ensures(@Int.result _ 0)`
#: makes (`<` where #1587's literal supplies the false proof), its body, and
#: what E703's description ends with.
_ASSUME_CELLS: dict[str, tuple[str, str, str]] = {
    # At the head of the body, evaluated on the arguments: they violate it.
    "head_violated": (
        ">", "assume(@Int.0 > 0);\n  @Int.0",
        "; the proof rests on `assume(@Int.0 > 0)` at line 6, which these "
        "arguments violate"),
    # At the head, and it holds: the false proof is the verifier's (#1587).
    "head_satisfied": (
        "<", "assume(@Int.0 == @Int.0);\n  0 - 18446744073709551615",
        "; the proof also rests on `assume(@Int.0 == @Int.0)` at line 6, "
        "which these arguments satisfy"),
    # After a binding the slots it reads may not be the parameters, so it
    # is not evaluated.
    "after_a_binding": (
        ">", "let @Int = @Int.0;\n  assume(@Int.0 > 0);\n  @Int.0",
        "; the proof rests on `assume(@Int.0 > 0)` at line 7, which the "
        "verifier takes on trust (W003)"),
    # Inside a branch it is not a statement of the body.  It reaches the
    # `assert` beside it, not the postcondition, so the `assert` is the
    # proof it refutes.
    "in_a_branch": (
        ">=", "if @Int.0 >= 0 then {\n    assume(@Int.0 > 0);\n"
        "    assert(@Int.0 > 0);\n    @Int.0\n  } else {\n    1\n  }",
        "; the proof rests on `assume(@Int.0 > 0)` at line 7, which the "
        "verifier takes on trust (W003)"),
}


def _assume_program(cell: str) -> str:
    sign, body, _ = _ASSUME_CELLS[cell]
    return (
        "public fn f(@Int -> @Int)\n"
        "  requires(true)\n"
        f"  ensures(@Int.result {sign} 0)\n"
        "  effects(pure)\n"
        "{\n"
        f"  {body}\n"
        "}\n")


def _refutations(result: TestResult) -> list[Any]:
    return [d for d in result.diagnostics if d.error_code == "E703"]


class TestRefutationsRestingOnAnAssume:
    """E703 names the `assume` a refuted proof rests on, and blames the
    verifier only where the `assume` held."""

    @pytest.mark.parametrize("cell", list(_ASSUME_CELLS))
    def test_each_position_of_the_assume(self, cell: str) -> None:
        result = _run(_assume_program(cell), distrust=True, trials=9)
        assert _fn(result, "f").category == "refuted"
        refutations = _refutations(result)
        assert refutations
        suffix = _ASSUME_CELLS[cell][2]
        for d in refutations:
            assert d.description.endswith(suffix), d.description
            assert (_SOUNDNESS in d.rationale) == (cell == "head_satisfied")

    def test_the_reviewers_own_assume(self) -> None:
        result = _run(SRC_ASSUME, distrust=True, fn_name="trusting")
        refutations = _refutations(result)
        assert len(refutations) == 3
        for d in refutations:
            assert d.description.endswith(
                "; the proof rests on `assume(@Int.0 > 0)` at line 6, which "
                "these arguments violate"), d.description
            assert _SOUNDNESS not in d.rationale
            assert "soundness defect" not in d.fix
            assert "`requires`" in d.fix

    def test_a_callees_assume_is_named_with_its_condition(self) -> None:
        result = _run(SRC_ASSUME, distrust=True, fn_name="via_callee")
        refutations = _refutations(result)
        assert refutations
        for d in refutations:
            assert d.description.endswith(
                "; the proof rests on `assume(@Int.0 > 0)` at line 15, in "
                "'helper', which the verifier takes on trust (W003)"), (
                d.description)
            assert _SOUNDNESS not in d.rationale
            # Not established either way, so both readings are stated.
            assert "soundness defect" in d.fix
            assert "`requires`" in d.fix

    def test_a_where_helper_is_found_under_its_own_owner(self) -> None:
        """Two functions each have a helper `h`; only `f1`'s has an `assume`.
        A refutation of `f2`'s `h` must not borrow it: a helper's record is
        named by its bare name, and its owner says whose helper it is."""
        result = _run(SRC_SAME_NAMED_HELPERS, distrust=True, fn_name="f2",
                      trials=3)
        refutations = _refutations(result)
        assert refutations, [(f.fn_name, f.category) for f in result.functions]
        for d in refutations:
            assert "assume(" not in d.description, d.description
            assert _SOUNDNESS in d.rationale

    def test_without_an_assume_the_rationale_still_names_the_case(
        self,
    ) -> None:
        (d,) = _run(SRC_1587, distrust=True).diagnostics
        assert "assume(" not in d.description
        assert "unless an `assume` the proof rests on is false" in d.rationale

    def test_every_variant_passes_the_diagnostic_fields_gate(self) -> None:
        gate = _diagnostic_fields_gate()
        assert gate.check_paths([ROOT / "vera" / "tester.py"]) == []


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

    @pytest.mark.parametrize("position", ["entry", "nested"])
    def test_no_check_of_the_kind_says_so_wherever_it_fired(
        self, position: str,
    ) -> None:
        """Nothing of the trap's kind is recorded in the function: that is
        the reason, at the trial's own call as on a nested one.  Before the
        fix the entry case gave the precondition reason, which claims a
        check the function does not hold."""
        trial = _trap(_ENTRY if position == "entry" else _NESTED)
        trial.status, trial.trap_kind = "error", "float_conversion"
        _TrapIndex([], []).attribute(trial, _matrix_decl())
        assert (trial.status, trial.refutes) == ("unattributed", [])
        assert trial.attribution == (
            "trap not attributable to an obligation: float_conversion in "
            "'f', where the module records no check of that kind")

    def test_the_precondition_reason_needs_a_prologue_check_set_aside(
        self,
    ) -> None:
        """The precondition reason is given only when the entry filter
        removed a candidate: here the function's own `requires` check."""
        pre, records = _cell("precondition", 10)
        trial = _trap(_ENTRY)
        _TrapIndex([pre], records).attribute(trial, _matrix_decl())
        assert trial.status == "unattributed"
        assert trial.attribution == (
            "trap not attributable to an obligation: contract_violation at "
            "the entry of 'f', whose arguments satisfy its precondition in "
            "the verifier's model and fail the compiled check of it")

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
