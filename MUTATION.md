# Mutation testing

Runbook for [#387](https://github.com/aallan/vera/issues/387) — deliberately break each line of `vera/` and confirm a test flips RED. A surviving mutant is a test gap: either a **weak test** to strengthen or an **equivalent mutant** to annotate. This is the safety net under the [#421](https://github.com/aallan/vera/issues/421) runtime decomposition and every future change.

> A passing suite is necessary, not sufficient. The #680 audit found 8 green-for-the-wrong-reason tests in one 57-test battery; #734 had to mutation-validate its own harness. Mutation testing systematises that check.

## Tool: mutmut (chosen over cosmic-ray)

Evaluated both on `vera/obligations/` (Phase 0 spike, 2026-06-22):

| | mutmut 3.6 | cosmic-ray 8.4.6 |
|---|---|---|
| Throughput | **~7–8 mut/s** (coverage-guided: runs only the tests covering each mutated line) | **~0.08 mut/s** (re-runs the full test command per mutant — [#498](https://github.com/sixty-north/cosmic-ray/issues/498)) |
| Working tree | copies the project to `./mutants/`, source untouched | mutates **in place** (apply → test → revert) — leaves the tree dirty if interrupted |
| Resume after a hard kill | verdicts persist as plain JSON; `mutmut run` resumes | session SQLite; resumable |

The ~90× speed gap (coverage-guided selection) is decisive for a slow Z3/WASM suite, and the copy-based model is safer for multi-day runs. mutmut also sidesteps the stale-`.pyc` hazard of an in-place bespoke driver.

## Install

```bash
pip install -e ".[mutation]"   # pulls [dev] + mutmut + pytest-timeout
```

Config lives in `[tool.mutmut]` in `pyproject.toml`. (Avoid `setup.cfg` — its list values split on **newlines**, not spaces, so `a.py b.py` becomes one bogus path. TOML arrays are unambiguous.)

## Oracle: in-process unit tests only

mutmut activates a mutant **in-process** via an import trampoline. Tests that spawn a **subprocess** — `test_conformance.py`, `test_cli.py`, and `test_browser.py` all run `python -m vera.cli` / Node, which imports the **un-mutated** installed package — therefore **cannot kill mutants**. The oracle for each module is its **in-process** unit tests:

| Module | In-process oracle |
|---|---|
| `verifier.py`, `smt.py` | `test_verifier.py`, `test_verifier_coverage.py`, `test_obligations.py` |
| `checker/` | `test_checker.py` |
| `obligations/` | `test_obligations.py`, `test_lsp.py` |
| `codegen/`, `wasm/` | `test_codegen*.py`, `test_wasm*.py` |

Consequence for the baseline: code exercised *only* via subprocess (much of `cli.py`) will score low **because mutations are invisible there, not because its tests are weak** — mark those `# pragma: no mutate` with that reason, don't chase them as gaps.

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

It writes **`mutation-summary.csv`** (committed — per-module total / killed / survived / timeout / caught%, a diff-able score history across sweeps), **`mutation.json`** (the README shields.io badge), and **`mutation-survivors.csv`** (the survivor + timeout inventory — too bulky for the repo, gitignored). Post the headline score + per-module table as a comment on [#387](https://github.com/aallan/vera/issues/387), and drag-drop the inventory CSV and the per-module chart into that comment (`gh` can't upload binaries; GitHub CDN-hosts them). The soundness core (`verifier` / `smt` / `checker` / `obligations`, all in-process tested) is triaged first; remaining modules become tracked per-module follow-ups under the issue.

The 2026-06 baseline: 10,620 core mutants, **80.8% caught** (6,816 killed + 1,766 timeout), 2,038 survivors — `verifier.py` dominates the survivors (1,132); `checker/control.py` is the weakest-covered (60.6%).

## CI (follow-up)

Mutation testing runs **locally** for now — the measure-all baseline is a multi-day job that CI's 6 h per-job cap cannot hold. Two CI pieces are deliberately deferred to a dedicated follow-up PR (workflow files warrant their own focused security review):

1. A **non-gating** on-demand sweep (`workflow_dispatch`) for running a bounded per-module sweep in CI when convenient.
2. The **diff-scoped PR gate** — mutate only the changed lines of a diff, run in parallel with the existing matrix, block on a survivor. Cheap because it only touches what a PR changed. It will need a matching entry in the branch-protection required-checks list (which is decoupled from the workflow YAML and synced by hand).

Both land once the baseline is stable and the soundness core is clean.
