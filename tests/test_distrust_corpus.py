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
  function, a type variable) is skipped by `vera test` in both modes, and a
  proved function whose precondition the generator cannot honour (#1229) is
  reported not exercised.  Neither is run.
- Inputs are bounded to |x| <= 2^53 for `@Int` and `@Nat`, so a false proof
  that needs a `@Nat` above i64.MAX is out of reach.
- A check code generation does not emit cannot trap, so a false Tier 3 or an
  unguarded obligation is invisible here: that is the reconciliation gate's
  class, not this one.
- A trap is attributed by joining the check it fired at to an obligation
  record by exact span (`vera.tester._TrapIndex`).  Measured when this file
  was introduced, over the 1,588 non-prelude checks the 219 programs compile:
  1,325 join an obligation that way, 221 join none, and the 42 precondition
  checks are read rather than joined.  A trap at a check that joins nothing
  is `unattributed`, counted in the session line `tests/conftest.py` prints
  ("distrust corpus: ..."), and never asserted to be zero.  #1630's join in
  `vera/reconcile.py`, which reads the relation between a record and its
  check from the program, is the mechanism the attribution switches to once
  it lands (#1633).

Each program also carries the default-mode differential: default `vera test`
runs no trial against a function it reports proved, and every function it
does NOT report proved has the same result under `--distrust`, so the mode
changes only what it was asked to change.

Known false Tier 1s are strict xfails in KNOWN_REFUTED, keyed by program and
naming their issue, so a fix flips its entry loud.  The list is empty: at
introduction no program refutes, at 5 trials or at 100 — 173 proofs run and
hold, and the open soundness bugs that do refute (#1587, #1555) have no shape
in the corpus.

Trials per function come from VERA_DISTRUST_TRIALS (default 5).  The whole
file adds about 20 worker-seconds to the suite.
"""

from __future__ import annotations

import json
import os
from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest

from vera.checker import typecheck_with_artifacts
from vera.parser import parse
from vera.resolver import ModuleResolver
from vera.tester import FunctionTestResult, TestResult
from vera.tester import test as run_test
from vera.transform import transform

ROOT = Path(__file__).resolve().parent.parent
CONFORMANCE = ROOT / "tests" / "conformance"
MANIFEST: list[dict[str, Any]] = json.loads(
    (CONFORMANCE / "manifest.json").read_text(encoding="utf-8"))

TRIALS = int(os.environ.get("VERA_DISTRUST_TRIALS", "5"))

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
    source = path.read_text(encoding="utf-8")
    program = transform(parse(source, file=str(path)))
    resolver = ModuleResolver(_root=path.parent)
    resolved = resolver.resolve_imports(program, path)
    diags, artifacts = typecheck_with_artifacts(
        program, source, file=str(path), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    errors = [d for d in resolver.errors + diags if d.severity == "error"]
    assert not errors, f"{path.name} must type-check:\n{errors[0].format()}"
    return run_test(
        program, source=source, file=str(path), trials=TRIALS,
        resolved_modules=resolved,
        expr_semantic_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
        alias_env=artifacts.alias_env,
        distrust=distrust,
    )


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
    proved = [f for f in default.functions if f.category == "verified"]
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
        if f.category != "verified":
            assert _outcome(d) == _outcome(f), (
                f"--distrust changed '{f.fn_name}', which it does not "
                f"distrust:\n  default:  {_outcome(f)}\n  distrust: {_outcome(d)}")
            continue
        assert d.proved and d.category in ("tested", "refuted", "verified"), (
            d.category, d.reason)
        if d.category == "verified":
            assert d.trials_run == 0 and "not exercised" in d.reason, d.reason

    exercised = [d for d in distrust.functions if d.proved and d.trials_run]
    unattributed = [
        t for d in distrust.functions for t in d.failures
        if t.status == "unattributed"
    ]
    record("distrust_proofs_exercised", len(exercised))
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

# #1587's repro: proved at Tier 1, refuted by its one run.
_FALSE_PROOF = """\
public fn main(-> @Int)
  requires(true)
  ensures(@Int.result < 0)
  effects(pure)
{
  0 - 18446744073709551615
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
    ("conformance/ch04_arithmetic", 7),
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
