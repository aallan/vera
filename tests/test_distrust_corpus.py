"""`vera test --distrust` over the corpus: a Tier-1 proof must survive a run.

The audit's invariant 4 — a proof the verifier reports at Tier 1 is never
contradicted when the program runs — checked the one way a run can check it.
Every example in `examples/`, and every conformance program the manifest
declares at level `run`, is tested in process with `--distrust`: each public
function the verifier proved, and the generator can serve, is executed on
Z3-generated inputs against the runtime checks code generation emits for it.  A trial that
fails a check standing for a proved obligation refutes the proof (E703), and
fails its program's test with the diagnostic text.

What it can see, and what it cannot:

- A proved function with a parameter the generator cannot encode (an ADT, a
  function, a type variable) is skipped by default and reported not
  exercised under `--distrust`, as is a proved function whose precondition
  the generator cannot honour (#1229).  Neither is run.
- Inputs are bounded to |x| <= 2^53 for `@Int` and `@Nat`, so a false proof
  that needs a `@Nat` above i64.MAX is out of reach.
- A check code generation does not emit cannot trap, so a false Tier 3 or an
  unguarded obligation is invisible here: that is the reconciliation gate's
  class, not this one.
- A trap is attributed through the reconciliation's relation between a
  check and the records it stands for (`vera.reconcile.join`, read by
  `vera.tester._TrapIndex`, #1633), wherever the two sides locate them.
  Measured at c9235415 over the 1,561 non-prelude checks the 223 programs
  compile: the relation joins 1,364 to a record (657 to proved records
  alone, 707 to unproved ones) and 197 to none, which are 92 checks the
  reconciliation reports with no record at all (W004), 73 in imported bodies
  this run did not verify, and 32 `requires` checks whose calls' discharged
  preconditions the verifier does not record.  Read by exact span, as before
  #1633, 1,328 joined and 233 did not.  A trap at a check that joins nothing
  is `unattributed`, counted in the session line `tests/conftest.py` prints
  ("distrust corpus: ..."), and never asserted to be zero.

Each program also carries the default-mode differential: default `vera test`
runs no trial against a function the verifier proved, and every function it
did NOT prove has the same result under `--distrust`, so the mode changes
only what it was asked to change.

Known false Tier 1s are strict xfails in KNOWN_REFUTED, keyed by program and
naming their issue, so a fix flips its entry loud.  The list is empty: at
introduction no program refutes, at 5 trials or at 100 — 173 proofs run and
hold, 3 are not exercised, and the open soundness bugs that do refute (#1587,
#1555) have no shape in the corpus.

Trials per function come from VERA_DISTRUST_TRIALS (default 5, the pull
request's count); the nightly stress workflow runs this file at 1,000
(tests/test_nightly_stress_workflow.py reads the step).  The whole file adds
about 20 worker-seconds to the suite.
"""

from __future__ import annotations

import json
import os
from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest

from vera.tester import FunctionTestResult, TestResult

from tests import pipeline

ROOT = Path(__file__).resolve().parent.parent
CONFORMANCE = ROOT / "tests" / "conformance"
MANIFEST: list[dict[str, Any]] = json.loads(
    (CONFORMANCE / "manifest.json").read_text(encoding="utf-8"))

#: Trials per proved function in the pull request's suite.
DEFAULT_TRIALS = 5
TRIALS = int(os.environ.get("VERA_DISTRUST_TRIALS", str(DEFAULT_TRIALS)))

#: Programs whose run refutes a proof today: program id -> its open issue.
#: Each is a strict xfail, so the day its issue is fixed the program stops
#: refuting, the xfail passes, the strict mark fails the suite, and the entry
#: comes out.
KNOWN_REFUTED: dict[str, str] = {}


def _corpus() -> list[tuple[str, Path]]:
    """Every example, then every conformance program at level `run`."""
    programs = [
        (f"examples/{path.name}", path)
        for path in sorted((ROOT / "examples").glob("*.vera"))
    ]
    programs += [
        (f"conformance/{entry['id']}", CONFORMANCE / entry["file"])
        for entry in MANIFEST
        if entry["level"] == "run"
    ]
    return programs


CORPUS = _corpus()


def _params() -> list[Any]:
    return [
        pytest.param(
            path,
            id=program,
            marks=(
                [pytest.mark.xfail(strict=True, reason=KNOWN_REFUTED[program])]
                if program in KNOWN_REFUTED else []
            ),
        )
        for program, path in CORPUS
    ]


def _tested(path: Path, *, distrust: bool) -> TestResult:
    """Test *path* in process, threaded exactly as `cmd_test` threads it."""
    tested = pipeline.contract_test(path, trials=TRIALS, distrust=distrust)
    checked = tested.checked
    _ = checked.program  # raises the parse or transform error, if any
    errors = list(checked.errors)
    assert not errors, f"{path.name} must type-check:\n{errors[0].format()}"
    return tested.result


def _outcome(f: FunctionTestResult) -> tuple[object, ...]:
    """Everything a function's result reports, for the mode differential —
    its attribution too, which only a distrusted function may carry."""
    return (
        f.fn_name, f.category, f.reason, f.trials_run, f.trials_passed,
        f.trials_failed, f.proved,
        [(t.args, t.status, t.message, t.trap_kind, t.attribution,
          len(t.refutes)) for t in f.failures],
    )


def _distrust_program(
    path: Path, record: Callable[[str, object], None],
) -> None:
    """The per-program instrument: the differential, the counts, and no
    refutation.  Skips a program with nothing for `--distrust` to run."""
    default = _tested(path, distrust=False)
    # A proof the generator cannot serve is skipped by default, its `proved`
    # flag still set, so the flag and not the category says what is proved.
    proved = [f for f in default.functions if f.proved]
    assert all(f.trials_run == 0 and not f.failures for f in proved), (
        "default `vera test` ran a trial against a proof")
    if not proved:
        categories = sorted({f.category for f in default.functions})
        pytest.skip(
            f"no public function is proved ({', '.join(categories) or 'none'}"
            f" only), so --distrust runs nothing default `vera test` does not")

    distrust = _tested(path, distrust=True)
    assert [f.fn_name for f in distrust.functions] == [
        f.fn_name for f in default.functions]
    by_name = {f.fn_name: f for f in distrust.functions}
    for f in default.functions:
        d = by_name[f.fn_name]
        if not f.proved:
            assert _outcome(d) == _outcome(f), (
                f"--distrust changed '{f.fn_name}', which it does not "
                f"distrust:\n  default:  {_outcome(f)}\n  distrust: {_outcome(d)}")
            continue
        assert d.proved and d.category in ("tested", "refuted", "verified"), (
            d.category, d.reason)
        if d.category == "verified":
            assert d.trials_run == 0 and "not exercised" in d.reason, d.reason

    exercised = [d for d in distrust.functions if d.proved and d.trials_run]
    unexercised = [
        d for d in distrust.functions if d.proved and not d.trials_run]
    unattributed = [
        t for d in distrust.functions for t in d.failures
        if t.status == "unattributed"
    ]
    record("distrust_proofs_exercised", len(exercised))
    record("distrust_proofs_not_exercised", len(unexercised))
    record("distrust_refuted", distrust.summary.refuted)
    record("distrust_unattributed_traps", len(unattributed))
    record("distrust_functions_with_unattributed_traps",
           distrust.summary.unattributed)

    refutations = [d for d in distrust.diagnostics if d.error_code == "E703"]
    assert not refutations, "\n\n".join(d.format() for d in refutations)
    if not exercised:
        pytest.skip("no proved function can be run: " + "; ".join(
            f"{d.fn_name}: {d.reason}" for d in distrust.functions
            if d.proved))


@pytest.mark.parametrize("path", _params())
def test_no_proof_is_refuted(
    path: Path, record_property: Callable[[str, object], None],
) -> None:
    _distrust_program(path, record_property)


# =====================================================================
# Premises: the instrument can fail, and it reaches proofs
# =====================================================================

# #1555's address comparison: proved at Tier 1, refuted by its one run.
# `mo`'s own `ensures` is Tier 3, so the false proof brings no proved check of
# its own (tests/test_tester_distrust.py's `_MO`).
_FALSE_PROOF = """\
public fn main(-> @Int)
  requires(true)
  ensures(@Int.result < 0)
  effects(pure)
{
  if mo(7) == mo(7) then { 0 - 1 } else { 1 }
}

private fn mo(@Int -> @Option<Int>)
  requires(true)
  ensures(@Option<Int>.result == Some(@Int.0))
  effects(pure)
{
  match parse_int(show(@Int.0)) {
    Ok(@Int) -> Some(@Int.0),
    Err(@String) -> Some(@Int.0)
  }
}
"""


def test_the_instrument_fails_on_a_false_proof(tmp_path: Path) -> None:
    """A green corpus means something only if a refuted program goes red."""
    path = tmp_path / "false_proof.vera"
    path.write_text(_FALSE_PROOF, encoding="utf-8")
    recorded: dict[str, object] = {}
    with pytest.raises(AssertionError, match=r"\[E703\]"):
        _distrust_program(path, recorded.__setitem__)
    assert recorded["distrust_refuted"] == 1


@pytest.mark.parametrize("program, proofs", [
    ("examples/safe_divide.vera", 2),
    # The six operator tests; the run's `main` prints them and proves
    # nothing of its own (#1645).
    ("conformance/ch04_arithmetic", 6),
])
def test_the_corpus_reaches_its_proofs(program: str, proofs: int) -> None:
    """Every proof in these programs is run, so a change that stopped
    exercising proofs would show here, not as a corpus of quiet skips."""
    path = dict(CORPUS)[program]
    result = _tested(path, distrust=True)
    ran = [f for f in result.functions if f.proved and f.trials_run > 0]
    assert len(ran) == proofs, [(f.fn_name, f.category, f.reason)
                                for f in result.functions]


def test_known_refuted_names_corpus_programs() -> None:
    """A stale key would exempt nothing and say it exempts something."""
    assert set(KNOWN_REFUTED) <= {program for program, _ in CORPUS}
