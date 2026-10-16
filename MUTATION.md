# Mutation testing

Runbook for [#387](https://github.com/aallan/vera/issues/387) — deliberately break each line of `vera/` and confirm a test flips RED. A surviving mutant is a test gap: either a **weak test** to strengthen or an **equivalent mutant** to annotate. This is the safety net under the [#421](https://github.com/aallan/vera/issues/421) runtime decomposition and every future change.

> A passing suite is necessary, not sufficient. The #680 audit found 8 green-for-the-wrong-reason tests in one 57-test battery; #734 had to mutation-validate its own harness. Mutation testing systematises that check.

**Baseline (soundness core):** 83.3% caught, 1,773 survivors. The committed score lives in `mutation-summary.csv` and the README badge; the **per-module chart and the full survivor inventory** are attached to the [baseline comment on #387](https://github.com/aallan/vera/issues/387#issuecomment-4779424892).

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

The copy holds `vera/`, `tests/`, the config files and `also_copy`, and mutmut's stats pass runs the whole selection there with `-x`, so one selected test that cannot pass in the copy stops every run. `also_copy` carries the repository files the selected tests read (`examples/`, `README.md`, `docs/`, `spec/`, `scripts/`, `AGENTS.md`), and `pytest_add_cli_args` deselects the two tests that parse `vera/verifier.py`'s own text, which in the copy is mutmut's generated file with every mutant inlined.

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

## The measure-all baseline (Phase 2)

Run the sweep **locally** (CI's 6 h job cap can't hold a multi-day run); the committed config scopes the first pass to the soundness core:

```bash
caffeinate -dims mutmut run        # hours-to-days; resumable, leave it overnight
```

Turn the verdicts into the durable record with the reporting script:

```bash
python scripts/mutation_report.py --label core
```

It writes **`mutation-summary.csv`** (committed — per-module total / killed / survived / timeout / caught%, a diff-able score history across sweeps), **`mutation.json`** (the README shields.io badge), **`mutation-survivors.csv`** (the survivor + timeout inventory, gitignored), and **`mutation-<label>.png`** (the per-module chart, gitignored — needs matplotlib, which ships in the `[mutation]` extra; the script skips the PNG with a note if it is absent). The script **fails loud** rather than emit a number it can't stand behind: an empty corpus, a result line it can't parse (mutmut format drift), a `mutmut results` status it doesn't model (`not checked` / `suspicious` / `caught by type check` — `mutmut results` lists every non-killed mutant, and these must not be folded into the derived killed count), a module missing from the `mutants/` tree, or a per-module total below its survived+timeout count is a hard error, not a skewed score. Post the headline score + per-module table as a comment on [#387](https://github.com/aallan/vera/issues/387), and drag-drop the inventory CSV and the chart into that comment (`gh` can't upload binaries; GitHub CDN-hosts them). The soundness core (`verifier` / `smt` / `checker` / `obligations`, all in-process tested) is triaged first; remaining modules become tracked per-module follow-ups under the issue.

The committed score: 10,620 core mutants, **83.3% caught** (7,081 killed + 1,766 timeout), 1,773 survivors — `verifier.py` dominates the survivors (875); `checker/control.py` is the weakest-covered substantive module (60.6%).

## CI: the diff lane

`.github/workflows/mutation-diff.yml` runs `scripts/mutate_diff.py` on a pull request that changes a `vera/**/*.py` file, or the lane's own script, test file or workflow: mutmut over the functions the pull request changes, beside the other checks.

**What it mutates.** The diff from the pull request's merge base, mapped to the units mutmut mutates: a top-level function, or a method of a top-level class, a nested function belonging to the one that encloses it. A unit counts as changed when its code differs from the merge base's (its `ast`, docstrings set aside) or it is new, so a docstring, a comment or a layout change alone mutates nothing. The script extracts the head commit into a scratch tree (`git archive`; the checkout is never touched) and gives every unit the diff leaves alone in a changed file `# pragma: no mutate block` on its header, so mutmut generates the changed units' mutants and no others. A file's every mutant can be far more than the diff's: `vera/verifier.py`'s are a 213 MB module that took 447 s to generate, where the 16 functions [#1715](https://github.com/aallan/vera/pull/1715) changed in it and in `vera/smt.py` took 41 s.

**The oracle.** The repository's `[tool.mutmut]` selection, plus the pull request's own changed `tests/test_*.py` files that reach the compiler in process (they import `vera`, directly or through a `tests/` helper), bar the families the selection leaves out on purpose: the subprocess, Node and tooling suites. mutmut's stats pass records which tests reach each function, and each mutant runs only those, fastest first, stopping at the first failure.

**The verdict.** Exit 0 when every mutant of the diff is killed or timed out; 1 when one survives; 2 when the run stops short: the budget runs out, the engine fails, a mutant is left undecided (`not checked`, `suspicious`, `segfault`, interrupted), or mutmut reports a mutant of a function the lane did not map to the diff, which in the narrowed tree means the mapping or the narrowing went wrong. Exit 2 outranks exit 1: a run that left a mutant undecided has not measured the diff, whatever it found. A function no in-process test reaches has every mutant `no tests`; it is reported as not observable in process (§ Oracle) and does not fail the run. The job summary has a row per changed function, the first 60 survivors' `mutmut show` diffs (a step summary over 1 MiB is dropped whole), and what the diff changes that mutmut does not mutate; the JSON record, the `mutation-diff` artifact, lists every survivor.

**The budget is the designed limit.** mutmut gets 2,400 s and the job 55 minutes. A diff that touches the verifier's large walkers cannot finish inside a pull request's budget: [#1715](https://github.com/aallan/vera/pull/1715)'s diff holds 2,207 mutants, 1,256 of them in `_walk_for_nat_binding_obligations`, and each surviving mutant runs every test that reaches its function. Such a run ends with exit 2 and the partial table, the designed behaviour of a check that is not required: its red says the diff was not fully measured, never that it passed. Branch protection's required list is synced by hand and does not name the job.

**What it adds to a pull request's own mutants.** A fix pull request still runs its hand-written mutants, one per mechanism it adds, deletes or moves; the lane adds mutmut's systematic mutants over every function it changes. A survivor is triaged as in § Triaging a survivor: a weak test to strengthen, or an equivalent mutant to mark `# pragma: no mutate` with its reason.

**Blind spots of the engine.** mutmut 3 mutates no decorated function bar one whose only decorator is `@staticmethod` or `@classmethod` (a `@contextlib.contextmanager` helper has no mutants), no method of a nested class, no module-level or class-body code, no `__new__`, `__getattribute__` or `__setattr__`, and no triple-quoted string, so a docstring is never mutated. The lane lists a changed function of those kinds as not mutated, with the reason, and counts the changed lines outside every function.

Run it locally:

```bash
pip install -e ".[mutation]"
python scripts/mutate_diff.py                                   # origin/main...HEAD, 2,400 s budget
python scripts/mutate_diff.py --base <sha> --budget 600 --json out.json
```

The whole-`vera/` sweep stays local (§ The measure-all baseline); a nightly rotation of per-module chunks is the follow-up [#795](https://github.com/aallan/vera/issues/795) tracks.
