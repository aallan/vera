"""The configurable Z3 budget (#1350).

Before this knob the per-query budget was hardcoded at 10 s, which made the
TIER of a borderline obligation a property of the host rather than of the
program: `examples/ephemeris.vera`'s `julian_century` refine_bind proves in
roughly 9-11 s, so it discharged at Tier 1 on a cold fast run and fell to
Tier 3 on a slower or warmer one.  The corpus-wide pin in
`test_verifier_adt_decreases.py` measured 413 T1 cold and 412 T1 after a
single prior verification in the same process.

Two things are pinned here.  The resolution ORDER — explicit argument, then
`VERA_Z3_TIMEOUT_MS`, then the default — with malformed values raising rather
than silently reverting, because a budget that quietly falls back is
indistinguishable from the host-sensitivity the knob exists to remove.  And
the REGRESSION itself: at a generous budget the boundary obligation proves
whether the process is cold or warm.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
import z3

from vera.checker.core import typecheck
from vera.obligations.session import VerificationSession
from vera.parser import parse_to_ast
from vera.smt import (
    DEFAULT_Z3_TIMEOUT_MS,
    Z3_TIMEOUT_ENV,
    Z3BudgetError,
    resolve_timeout_ms,
)
from vera.verifier import ContractVerifier, verify
from vera.verifier import _PREMISE_CHECK_TIMEOUT_MS

ROOT = Path(__file__).parent.parent
EXAMPLES = ROOT / "examples"


class TestBudgetResolution:
    """Explicit argument > environment > default."""

    def test_default_when_nothing_set(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.delenv(Z3_TIMEOUT_ENV, raising=False)
        assert resolve_timeout_ms() == DEFAULT_Z3_TIMEOUT_MS

    def test_environment_is_honoured(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "45000")
        assert resolve_timeout_ms() == 45_000

    def test_explicit_argument_beats_environment(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "45000")
        assert resolve_timeout_ms(7_000) == 7_000

    def test_unset_environment_falls_back(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """Only an ABSENT variable is "nobody chose"."""
        monkeypatch.delenv(Z3_TIMEOUT_ENV, raising=False)
        assert resolve_timeout_ms() == DEFAULT_Z3_TIMEOUT_MS

    @pytest.mark.parametrize("bad", ["abc", "0", "-5", "1.5", "", "   "])
    def test_malformed_environment_raises(
        self, monkeypatch: pytest.MonkeyPatch, bad: str
    ) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, bad)
        with pytest.raises(Z3BudgetError, match=Z3_TIMEOUT_ENV):
            resolve_timeout_ms()

    @pytest.mark.parametrize("bad", [0, -1])
    def test_non_positive_explicit_raises(self, bad: int) -> None:
        with pytest.raises(Z3BudgetError):
            resolve_timeout_ms(bad)


class TestBudgetReachesTheVerifier:
    """The seams that construct a solver consult the same resolution."""

    def test_verifier_reads_the_environment(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "31000")
        assert ContractVerifier().timeout_ms == 31_000

    def test_explicit_argument_beats_environment_at_the_seam(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "31000")
        assert ContractVerifier(timeout_ms=9_000).timeout_ms == 9_000


class TestCliFlag:
    """`vera verify --timeout-ms` — the measurement surface."""

    def _run(self, args: list[str], env_extra: dict[str, str] | None = None):
        env = os.environ.copy()
        env["PYTHONIOENCODING"] = "utf-8"
        env.pop(Z3_TIMEOUT_ENV, None)
        env.update(env_extra or {})
        return subprocess.run(
            [sys.executable, "-m", "vera.cli", *args],
            capture_output=True, text=True, encoding="utf-8",
            cwd=str(ROOT), env=env, timeout=180, check=False,
        )

    def test_json_reports_the_effective_budget(self) -> None:
        r = self._run(["verify", "--json", "--timeout-ms", "60000",
                       str(EXAMPLES / "factorial.vera")])
        assert r.returncode == 0, r.stderr
        assert json.loads(r.stdout)["verification"]["timeout_ms"] == 60_000

    def test_json_reports_the_default_when_unset(self) -> None:
        r = self._run(["verify", "--json", str(EXAMPLES / "factorial.vera")])
        assert r.returncode == 0, r.stderr
        got = json.loads(r.stdout)["verification"]["timeout_ms"]
        assert got == DEFAULT_Z3_TIMEOUT_MS

    def test_flag_beats_environment(self) -> None:
        r = self._run(["verify", "--json", "--timeout-ms", "12345",
                       str(EXAMPLES / "factorial.vera")],
                      {Z3_TIMEOUT_ENV: "60000"})
        assert r.returncode == 0, r.stderr
        assert json.loads(r.stdout)["verification"]["timeout_ms"] == 12_345

    def test_environment_reaches_verify_without_a_flag(self) -> None:
        r = self._run(["verify", "--json", str(EXAMPLES / "factorial.vera")],
                      {Z3_TIMEOUT_ENV: "60000"})
        assert r.returncode == 0, r.stderr
        assert json.loads(r.stdout)["verification"]["timeout_ms"] == 60_000

    @pytest.mark.parametrize("bad", ["abc", "0", "-5"])
    def test_malformed_flag_is_a_loud_error(self, bad: str) -> None:
        r = self._run(["verify", "--timeout-ms", bad,
                       str(EXAMPLES / "factorial.vera")])
        assert r.returncode == 1
        assert "--timeout-ms" in (r.stderr + r.stdout)

    def test_malformed_environment_is_a_loud_error(self) -> None:
        """Not a traceback out of the solver's construction seam."""
        r = self._run(["verify", str(EXAMPLES / "factorial.vera")],
                      {Z3_TIMEOUT_ENV: "abc"})
        assert r.returncode == 1
        out = r.stderr + r.stdout
        assert Z3_TIMEOUT_ENV in out
        assert "Traceback" not in out

    @pytest.mark.parametrize(
        "command", ["lsp", "version", "builtins", "effects", "errors"]
    )
    def test_no_file_commands_reject_the_flag(self, command: str) -> None:
        """The refusal must precede the commands that take no file argument.

        These dispatch early in `main()`, before the file-argument handling,
        so a refusal placed with the other flag parsing never runs for them:
        `vera lsp --timeout-ms 5000` would start the language server and
        ignore the flag, which is the silent no-op the refusal exists to
        prevent.  `lsp` is the one that matters most — it blocks until the
        client disconnects, so the ignored flag is invisible.
        """
        r = self._run([command, "--timeout-ms", "5000"])
        assert r.returncode == 1, (r.returncode, r.stdout, r.stderr)
        assert "--timeout-ms" in (r.stderr + r.stdout)

    @pytest.mark.parametrize("command", ["version", "builtins"])
    def test_no_file_commands_are_unaffected_without_the_flag(
        self, command: str
    ) -> None:
        """The guard must not disturb their ordinary path."""
        r = self._run([command])
        assert r.returncode == 0, (r.returncode, r.stderr)

    def test_a_stray_environment_value_does_not_break_compile(self) -> None:
        """`compile` never builds a solver, so it must be unaffected."""
        r = self._run(["compile", "--wat", str(EXAMPLES / "factorial.vera")],
                      {Z3_TIMEOUT_ENV: "abc"})
        assert r.returncode == 0, r.stderr


class TestBudgetReachesTheSolver:
    """PLUMBING: the resolved budget arrives at the Z3 solver's parameters.

    Deliberately introspective rather than timed.  A test that asserted a
    contract proves within N seconds measures the machine, which is the
    defect this knob exists to remove — it would fail on a loaded CI worker
    for the same reason the hardcoded budget did.  Spying on
    ``z3.Solver.set`` instead answers the only question the knob owns: does
    the number a caller chose reach the solver?
    """

    def _timeouts_set(self, fn) -> list[int]:
        """Every ``("timeout", n)`` the solver received while *fn* ran."""
        seen: list[int] = []
        original = z3.Solver.set

        def spy(self_, *args, **kwargs):
            if len(args) >= 2 and args[0] == "timeout":
                seen.append(args[1])
            kwargs_timeout = kwargs.get("timeout")
            if kwargs_timeout is not None:
                seen.append(kwargs_timeout)
            return original(self_, *args, **kwargs)

        z3.Solver.set = spy  # type: ignore[method-assign]
        try:
            fn()
        finally:
            z3.Solver.set = original  # type: ignore[method-assign]
        return seen

    def _assert_budget(self, seen: list[int], budget: int) -> None:
        """*budget* reached the solver, and only the screening budget beside it.

        Stronger than the `set(seen) == {budget}` this asserted before #1451
        added a second, documented number to the plumbing.  Three properties
        rather than one: the caller's budget is applied, the ONLY other value
        the solver ever sees is the premise-consistency screening budget
        (`min(_PREMISE_CHECK_TIMEOUT_MS, budget)` — a third number appearing
        here is a leak, which is what the old equality was really guarding),
        and the LAST value set is the caller's, so every obligation still to
        be discharged runs under the budget the caller chose rather than under
        a screening budget left standing.
        """
        assert seen, "the solver was never given a timeout"
        screening = min(_PREMISE_CHECK_TIMEOUT_MS, budget)
        assert budget in seen, (budget, seen)
        assert set(seen) <= {budget, screening}, (budget, screening, seen)
        assert seen[-1] == budget, (
            f"the run's budget was not restored after the #1451 screening "
            f"query: {seen}"
        )

    # A tiny program: this asks where the budget went, not what was proved.
    SOURCE = (
        "public fn f(@Int -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  @Int.0\n"
        "}\n"
    )

    def _cold(self, **kwargs) -> None:
        prog = parse_to_ast(self.SOURCE)
        typecheck(prog, self.SOURCE)
        verify(prog, self.SOURCE, **kwargs)

    def test_explicit_argument_reaches_the_solver_cold(self) -> None:
        seen = self._timeouts_set(lambda: self._cold(timeout_ms=33_000))
        self._assert_budget(seen, 33_000)

    def test_environment_reaches_the_solver_cold(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "27000")
        seen = self._timeouts_set(lambda: self._cold())
        self._assert_budget(seen, 27_000)

    def test_default_reaches_the_solver_cold(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.delenv(Z3_TIMEOUT_ENV, raising=False)
        seen = self._timeouts_set(lambda: self._cold())
        self._assert_budget(seen, DEFAULT_Z3_TIMEOUT_MS)

    def test_explicit_argument_reaches_the_solver_warm(self) -> None:
        """The warm session builds its own context — same budget, same place."""
        def run() -> None:
            session = VerificationSession(timeout_ms=41_000)
            session.verify_source(self.SOURCE, file="budget_warm.vera")
        seen = self._timeouts_set(run)
        self._assert_budget(seen, 41_000)

    def test_environment_reaches_the_solver_warm(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "23000")

        def run() -> None:
            session = VerificationSession()
            session.verify_source(self.SOURCE, file="budget_warm.vera")
        seen = self._timeouts_set(run)
        self._assert_budget(seen, 23_000)

    def test_warm_and_cold_agree_on_the_budget_they_apply(self) -> None:
        """The oracle's property, at the plumbing level.

        A warm session and a cold verify given the same budget must hand the
        solver the same number — if they diverged here, warm/cold tier
        equality would be luck rather than a property.
        """
        cold_seen = self._timeouts_set(lambda: self._cold(timeout_ms=17_000))

        def run_warm() -> None:
            VerificationSession(timeout_ms=17_000).verify_source(
                self.SOURCE, file="budget_warm.vera"
            )
        warm_seen = self._timeouts_set(run_warm)
        self._assert_budget(cold_seen, 17_000)
        self._assert_budget(warm_seen, 17_000)
        assert set(cold_seen) == set(warm_seen), (cold_seen, warm_seen)
