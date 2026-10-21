# Mutation testing

Runbook for [#387](https://github.com/aallan/vera/issues/387) — deliberately break each line of `vera/` and confirm a test flips RED. A surviving mutant is a test gap: either a **weak test** to strengthen or an **equivalent mutant** to annotate. This is the safety net under the [#421](https://github.com/aallan/vera/issues/421) runtime decomposition and every future change.

> A passing suite is necessary, not sufficient. The #680 audit found 8 green-for-the-wrong-reason tests in one 57-test battery; #734 had to mutation-validate its own harness. Mutation testing systematises that check.

**Baseline (soundness core):** 83.3% caught, 1,773 survivors. The committed score lives in `mutation-summary.csv` and the README badge; the **per-module chart and the full survivor inventory** are attached to the [baseline comment on #387](https://github.com/aallan/vera/issues/387#issuecomment-4779424892). The nightly sweep measures all of `vera/` over a cycle of nights, and its first closed cycle's score replaces this one (§ The measure-all baseline).

## Tool: mutmut (chosen over cosmic-ray)

Evaluated both on `vera/obligations/` (Phase 0 spike, 2026-06-22):

| | mutmut 3.6 | cosmic-ray 8.4.6 |
|---|---|---|
| Throughput | **~7–8 mut/s** (coverage-guided: runs only the tests covering each mutated line) | **~0.08 mut/s** (re-runs the full test command per mutant — [#498](https://github.com/sixty-north/cosmic-ray/issues/498)) |
| Working tree | copies the project to `./mutants/`, source untouched | mutates **in place** (apply → test → revert) — leaves the tree dirty if interrupted |
| Resume after a hard kill | verdicts persist as plain JSON; `mutmut run` resumes | session SQLite; resumable |

The ~90× speed gap (coverage-guided selection) is decisive for a slow Z3/WASM suite, and the copy-based model is safer for multi-day runs. mutmut also sidesteps the stale-`.pyc` hazard of an in-place bespoke driver.

That hazard is real whenever you mutate by hand instead: when validating a test by breaking the code it targets (see TESTING.md), purge `__pycache__` before re-running — a stale `.pyc` can serve the unmutated bytecode and false-green the mutant (this bit a hand-run oracle test during the v0.0.195 work; the kill was only confirmed RED after the purge).

## Install

```bash
pip install -e ".[mutation]"   # pulls [dev] + mutmut + pytest-timeout
```

Config lives in `[tool.mutmut]` in `pyproject.toml`. (Avoid `setup.cfg` — its list values split on **newlines**, not spaces, so `a.py b.py` becomes one bogus path. TOML arrays are unambiguous.)

## Oracle: in-process unit tests only

mutmut activates a mutant **in-process** via an import trampoline. Tests that spawn a **subprocess** — `test_conformance.py`, `test_cli.py`, and `test_browser.py` all run `python -m vera.cli` / Node, which imports the **un-mutated** installed package — therefore **cannot kill mutants**. The oracle for each module is its **in-process** unit tests:

| Module | In-process oracle |
|---|---|
| `verifier.py`, `smt.py` | `test_verifier_*.py`, `test_obligations.py` |
| `checker/` | `test_checker_*.py` |
| `obligations/` | `test_obligations.py`, `test_lsp.py` |
| `codegen/`, `wasm/` | `test_codegen*.py`, `test_wasm*.py` |

Consequence for the baseline: code exercised *only* via subprocess (much of `cli.py`) will score low **because mutations are invisible there, not because its tests are weak** — mark those `# pragma: no mutate` with that reason, don't chase them as gaps.

The copy holds `vera/`, `tests/`, the config files and `also_copy`, and mutmut's stats pass runs the whole selection there with `-x`, so one selected test that cannot pass in the copy stops every run. `also_copy` carries the repository files the selected tests read (`examples/`, `README.md`, `docs/`, `spec/`, `scripts/`, `AGENTS.md`), and `pytest_add_cli_args` deselects the three tests known to read the modules' source text, which in the copy is mutmut's generated file with every mutant inlined: two parse `vera/verifier.py`, and the collision gate in `test_checker_errors.py` runs `scripts/check_diagnostic_fields.py` over `vera/`, where each mutant repeats its function's error codes.

The oracle's boundary inside the copy: a test that starts a Python or `vera` process is skipped there (`tests/mutation_oracle.py`, a pytest plugin `[tool.mutmut]` loads). Each mutated module in the copy holds a copy of a mutated function for each of its mutants, so a mutated `TypeEnv._register_builtins` makes `vera/environment.py` 33.6 MB where it is 49 KB, and a process compiles every such module afresh (`vera check` of a one-line program: 2.3 s against 0.4 s) while recording nothing for the stats pass, so the test cannot be a mutant's oracle. The skipped test is out of the oracle entirely: mutmut's stats pass records the functions a test reached at the test's teardown, whatever its outcome, and runs a mutant against the tests recorded for its function, so the plugin takes a skipped test out of that record. A function that only such tests reach therefore has every mutant `no tests`, even when a test called it before starting its process, and is reported not observable in process; the lane lists every test skipped this way.

Every pytest session the lanes run carries `-p no:faulthandler` (`[tool.mutmut]`'s `pytest_add_cli_args`).  pytest's faulthandler plugin records the process's signal handlers when a session starts and restores them when it ends; wasmtime installs its trap handlers once per process, at the first `Engine`.  mutmut's fork runner runs the stats pass and the clean pass as two sessions in one process, so the first session's end put the pre-session handlers back over wasmtime's and the clean pass died on its first trap (SIGILL, exit -4) on each of the sweep's first two nights (#1745, #1747), every forked mutant run inheriting the loss.  With the plugin out nothing restores them; the price is that an engine crash leaves no Python traceback in the log.  `tests/test_wasmtime_traps_across_pytest_sessions_1747.py` shows both halves on Linux, where traps are signals.

## Run a module sweep

The committed config scopes the sweep to the **soundness core** via `only_mutate` (`verifier` / `smt` / `checker` / `obligations`), while `source_paths = ["vera/"]` keeps the whole compiler in range. To sweep a different module, point `only_mutate` at it (e.g. `only_mutate = ["vera/codegen/*"]`), then:

```bash
caffeinate -dims mutmut run        # macOS: keep awake; copies to ./mutants/, runs, stores verdicts
mutmut results                     # list survivors + not-checked
mutmut show <mutant-name>          # see the exact diff for one mutant
```

`mutmut run` is **safe to interrupt** — verified against a hard `SIGKILL` mid-run: completed verdicts persist (plain JSON, no DB-corruption window) and re-running resumes, re-doing only the unfinished mutants (39s vs ~100s from scratch in the spike). A power-off costs minutes, never the whole run. Only deleting `mutants/` forces a full restart (of compute, never of correctness).

## Reading verdicts

`🎉 killed` (a test caught it — good) · `🙁 survived` (gap — triage) · `⏰ timeout` (see Z3 note) · `🔇 no tests` / `not checked` (no covering test — often a coverage gap or subprocess-only code) · `🤔 suspicious`.

## Triaging a survivor

1. `mutmut show <name>` — read the mutation.
2. Classify:
   - **Weak test** → strengthen it (a discriminating assertion or a new killing test). Same discipline as #680/#734: pick inputs where the wrong behaviour flips the assertion.
   - **Equivalent mutant** (semantically identical to the original — e.g. `a < b` vs `a <= b` where the boundary is unreachable) → `# pragma: no mutate` on the line, with a one-line rationale.
   - **Genuine coverage gap** → add a test.
3. **Re-confirm** (Z3-flakiness guardrail): re-run the specific mutant ≥2× before trusting a survivor. A mutant that makes a verification *barely* unsolvable can hit the Z3 timeout → `unknown` → Tier-3 and survive nondeterministically. If a survivor flips between runs, it's timeout-flaky, not a weak test — raise the `--timeout` / Z3 timeout rather than "fixing" a test.

## The measure-all baseline

The whole of `vera/` is measured by the nightly sweep: `.github/workflows/mutation-nightly.yml` running `scripts/mutate_sweep.py`, a slice a night. No single run holds it. At 366bf326 mutmut 3.8 makes 110,025 mutants in the 2,371 functions it mutates in `vera/`, 29,320 of them in the soundness core, and a mutant costs from a twentieth of a second (killed by its first test) to most of an hour on a runner (a survivor runs every test that reaches its function). The one local marathon that tried, on mutmut 3.6 and Python 3.14, deadlocked four times, 30% to 55% of the way through; the sweep has no marathon, so it does not meet that hang, and its runners use Python 3.12, as the test shards do.

**A night.** At 21:00 UTC the `setup` job finds the state the last night left: the `mutation-sweep-state` artifact of the newest completed run of this workflow on this repository's own `main`, started by the schedule or a dispatch, that holds one unexpired. A fork's run on a branch named `main`, or another workflow's run, could upload an artifact of that name, so no other run's is taken, and the state is checked field by field before it is used. Seven `sweep` jobs (`JOBS` in the script) then each plan the same night from it and run their slice:

- The inventory: every function mutmut mutates, with a hash of its code (its `ast`, docstrings set aside). A function whose code changed since its mutants were decided starts afresh, one gone from the tree is dropped, and a new mutmut version starts every function afresh, since mutmut numbers a function's mutants by its own rules.
- The plan: the undecided work in the tree's order, in one bin a job, each bin one job's budget (4.5 h) less the passes before its first mutant (48 minutes), at an estimated cost a mutant: 25 s in the soundness core and 2.5 s elsewhere, times a factor each night measures. A function whose mutant count is known splits across bins by its mutants' numbers; one whose count is not yet known, because mutmut has not yet generated it, goes whole into one bin, its cost estimated from its size. A bin's first piece is taken whatever it costs, so a job with work open decides something.
- The run: a scratch tree of the head, narrowed to the bin's functions as the diff lane narrows a diff's (§ CI: the diff lane). mutmut's copy holds the whole tree, and the oracle is every `tests/test_*.py` file the lane's rule admits (235 of 266 today), the subprocess, Node and tooling families left out. A test that starts a Python or `vera` process is no oracle in the copy (§ Oracle), and one that fails there with no mutant active is dropped from the run and reported. A function's count is taken only from a listing `mutmut results` printed, and a count of zero only from a run that finished: mutmut lists nothing for a function it had not yet generated when the budget stopped it. On the measuring machine, beside another mutmut run, the stats pass over that oracle took 491 s and 588 s, and a sample bin of five functions spent 1,142 s before its first mutant, 546 s of it in the clean run of its covering tests; a runner is about 2.5 times slower.
- The `stitch` job folds the slices' records into the state and keeps it as the `mutation-sweep-state` artifact for 90 days.

**The cycle.** When every function's every mutant is decided, the cycle closes: its per-module totals and its survivors are kept in the state, and that night's artifact holds `mutation-summary.csv`, `mutation.json` and `mutation-survivors.csv`. Two measurements bound a cycle's length. The first samples (whole-file chunks outside the core at about 2 worker-seconds a mutant, the core at 0.05 to 0.2 mutants a second at four workers) project 160 to 250 runner hours of mutants: 43 to 68 job-nights at 3.7 h of mutants a job, so 6 to 10 nights at seven jobs. A bin of five functions measured under the sweep's own oracle cost 71 worker-seconds a mutant: 65 of its 114 mutants hung their first covering test until `tests/pipeline.py`'s 120 s stage budget ended it, each killed but only after 120 s. If that is the norm, a cycle is about 52 nights. The first week's nights decide between them: each night's measured cost moves the plan's factor halfway to it, and `JOBS` is the constant to raise (to `MAX_JOBS`, 12) if the cost holds. The follow-up that shortens a hung mutant four times over is a sweep-only stage budget, an environment knob in `tests/pipeline.py`, to be sized once the first nights report. A function that changes during a cycle is measured again within it, so a closed cycle holds every function's code as the sweep last found it.

**The score and the badge.** A module's total is its mutants an in-process test reaches with a known outcome: killed (`caught by type check` included), survived, and timeout, which counts as caught, the core baseline's convention. Its `no tests` mutants are not observable in process (§ Oracle) and are counted apart. A `segfault` or `suspicious` mutant, which a budget stop can leave behind, is taken only from a run the budget did not stop, and is counted apart too. The README badge reads `mutation.json` on `main`, so a closed cycle reaches the badge by a pull request, the release pull request as a rule:

```bash
gh run download <run-id> --name mutation-sweep-state --dir state   # the night that closed the cycle
python scripts/mutate_sweep.py summary --state state               # the three files, at the repository root
```

`mutation-summary.csv` and `mutation.json` are committed; `mutation-survivors.csv`, the triage inventory, is gitignored.

**The engine and a refused state.** The sweep installs mutmut 3.8.0, pinned in the workflow and held equal to `uv.lock`'s by a test: the state compares the engine's version exactly, and a new version starts every function afresh, so a version change is a reviewed pull request that restarts the cycle. A state the script refuses (another schema, or a field out of bounds) stops every night, each one red and noted on the tracking issue, until it is replaced: delete that run's `mutation-sweep-state` artifact (`gh api -X DELETE repos/<owner>/<repo>/actions/artifacts/<id>`), and the next night carries on from the newest run before it that holds one, or from no state.

**A night that stops short.** A night that decides no mutant and counts no function, and a slice whose engine or lane fails, end the run red, and on the schedule the `issue` job files or updates one tracking issue, labelled `mutation-sweep`, as `nightly-stress.yml` does. Survivors never do: they are the measurement. A step that fails before the sweep runs, while the runner is still there, writes a lane record in the sweep's place (`lane-failed`), reported like any other. A slice with no record is one whose runner was taken away before it could upload anything: the nights of 19 and 20 October 2026 each lost one slice of seven that way ([#1751](https://github.com/aallan/vera/issues/1751)). The stitch notes it, the night stays green, and the slice's work is planned again the next night; more than one slice without a record in a night, or more than three over the last seven nights, is a hazard rather than weather, and ends the run red. The sweep job's own failure never colours the run (`continue-on-error`): the stitch does. While the engine runs, a slice prints a heartbeat line every five minutes, the elapsed time, the runner's available memory, swap and load, and the engine's last status, so the job log, which outlives a lost runner, says what the runner was doing when it went. The next night plans from the newest state, which holds what the night's other slices decided.

**On demand.** A `workflow_dispatch` run is a night of as many jobs as it is given, one by default. Nights run one at a time, and a running night is never cancelled; a night still waiting gives way to a newer one, which loses nothing, since it has planned nothing yet. Locally, `python scripts/mutate_sweep.py night --out out --budget 600` plans a one-job night from no state and runs it, and `python scripts/mutate_sweep.py stitch --slices out --out state` folds it into a state.

**A module sweep by hand.** `scripts/mutation_report.py` turns a local sweep of one module (§ Run a module sweep) into the same three files, plus the per-module chart for an issue:

```bash
python scripts/mutation_report.py --label core
```

It **fails loud** rather than emit a number it can't stand behind: an empty corpus, a result line it can't parse (mutmut format drift), a `mutmut results` status it doesn't model (`not checked` / `suspicious` / `caught by type check` — `mutmut results` lists every non-killed mutant, and these must not be folded into the derived killed count), a module missing from the `mutants/` tree, or a per-module total below its survived+timeout count is a hard error, not a skewed score. The chart (`mutation-<label>.png`) needs matplotlib, which ships in the `[mutation]` extra; the script skips the PNG with a note if it is absent. Post the headline score + per-module table as a comment on [#387](https://github.com/aallan/vera/issues/387), and drag-drop the inventory CSV and the chart into that comment (`gh` can't upload binaries; GitHub CDN-hosts them).

The core baseline it wrote, still committed until the sweep's first cycle closes: 10,620 core mutants, **83.3% caught** (7,081 killed + 1,766 timeout), 1,773 survivors — `verifier.py` dominates the survivors (875); `checker/control.py` is the weakest-covered substantive module (60.6%).

## CI: the diff lane

`.github/workflows/mutation-diff.yml` runs `scripts/mutate_diff.py` on a pull request that changes a `vera/**/*.py` file, or the lane's own script, test file or workflow: mutmut over the functions the pull request changes, beside the other checks.

**What it mutates.** The diff from the pull request's merge base, mapped to the units mutmut mutates: a top-level function, or a method of a top-level class, a nested function belonging to the one that encloses it. A unit counts as changed when its code differs from the merge base's (its `ast`, docstrings set aside) or it is new, so a docstring, a comment or a layout change alone mutates nothing. The script extracts the head commit into a scratch tree (`git archive`; the checkout is never touched) and gives every unit the diff leaves alone in a changed file `# pragma: no mutate block` on its header, so mutmut generates the changed units' mutants and no others. A file's every mutant can be far more than the diff's: `vera/verifier.py`'s are a 213 MB module that took 447 s to generate, where the 16 functions [#1715](https://github.com/aallan/vera/pull/1715) changed in it and in `vera/smt.py` took 41 s.

**The oracle.** The repository's `[tool.mutmut]` selection, plus the pull request's own changed `tests/test_*.py` files that reach the compiler in process (they import `vera`, directly or through a `tests/` helper), bar the families the selection leaves out on purpose: the subprocess, Node and tooling suites. mutmut's stats pass records which tests reach each function, and each mutant runs only those, fastest first, stopping at the first failure. A test that starts a Python or `vera` process is skipped in the copy and listed (§ Oracle). Any other test that fails inside mutmut's copy with no mutant active stops the stats pass or the clean run of the covering tests; it is no oracle there, so the lane drops it, runs again (up to five drops), and lists it in the summary and the record.

**The verdict.** Exit 0 when no mutant of the diff survives and none is left undecided, the headline saying whether every mutant was killed or timed out or counting the functions no in-process test reaches, which the table names; 1 when one survives; 2 when the run stops short: the budget runs out, the engine fails, a mutant is left undecided (`not checked`, `suspicious`, `segfault`, interrupted), or mutmut reports a mutant of a function the lane did not map to the diff, which in the narrowed tree means the mapping or the narrowing went wrong. Exit 2 outranks exit 1: a run that left a mutant undecided has not measured the diff, whatever it found. A function no in-process test reaches has every mutant `no tests`; it is reported as not observable in process (§ Oracle) and does not fail the run. The job summary has a row per changed function, the first 60 survivors' `mutmut show` diffs (a step summary over 1 MiB is dropped whole), and what the diff changes that mutmut does not mutate; the JSON record, the `mutation-diff` artifact, lists every survivor.

**The budget is the designed limit.** mutmut gets 2,400 s and the job 55 minutes. A diff that touches the verifier's large walkers cannot finish inside a pull request's budget: [#1715](https://github.com/aallan/vera/pull/1715)'s diff holds 2,207 mutants, 1,256 of them in `_walk_for_nat_binding_obligations`, and each surviving mutant runs every test that reaches its function. Such a run ends with exit 2 and the partial table, the designed behaviour of a check that is not required: its red says the diff was not fully measured, never that it passed. Branch protection's required list is synced by hand and does not name the job.

**What it adds to a pull request's own mutants.** A fix pull request still runs its hand-written mutants, one per mechanism it adds, deletes or moves; the lane adds mutmut's systematic mutants over every function it changes. A survivor is triaged as in § Triaging a survivor: a weak test to strengthen, or an equivalent mutant to mark `# pragma: no mutate` with its reason.

**Blind spots of the engine.** mutmut 3 mutates no decorated function bar one whose only decorator is `@staticmethod` or `@classmethod` (a `@contextlib.contextmanager` helper has no mutants), no method of a nested class, no module-level or class-body code, no `__new__`, `__getattribute__` or `__setattr__`, and no triple-quoted string, so a docstring is never mutated. A function evaluated at import time (called by module-level code, or a dataclass field's default) is mutated, but its mutants can never be killed: mutmut 3 forks each mutant's worker after the modules are imported, so the mutated function never runs, and every such mutant scores as a survivor ([#1740](https://github.com/aallan/vera/issues/1740)). The lane lists a changed function of the kinds mutmut does not mutate as not mutated, with the reason, and counts the changed lines outside every function.

Run it locally:

```bash
pip install -e ".[mutation]"
python scripts/mutate_diff.py                                   # origin/main...HEAD, 2,400 s budget
python scripts/mutate_diff.py --base <sha> --budget 600 --json out.json
```

The whole of `vera/` is measured nightly (§ The measure-all baseline).
