# CLAUDE.md — Project orientation for Claude Code

Vera is a programming language designed for LLMs to write. It has mandatory contracts, algebraic effects, typed slot references (`@T.n`), and compiles to WebAssembly. The reference compiler is written in Python.

## Virtual environment

Always use the project venv. All commands below assume it is active:

```bash
source .venv/bin/activate
```

If the venv does not exist, create it first:

```bash
python -m venv .venv && source .venv/bin/activate && pip install -e ".[dev]"
```

If you prefer `uv`, use `uv sync --extra dev` (not plain `uv sync`). The `[dev]` extras group holds pytest, mypy, ruff, pre-commit, and pip-licenses; `uv sync` without `--extra dev` will quietly uninstall those and make `pytest` fall through to a non-venv copy that can't import `vera`.

## Key commands

```bash
vera check file.vera              # Parse and type-check
vera check --json file.vera       # Type-check with JSON diagnostics
vera check --quiet file.vera      # Type-check, suppress success output
vera check --explain-slots file.vera  # Show slot resolution table (which @T.n maps to which param)
vera verify file.vera             # Type-check + verify contracts via Z3
vera verify --json file.vera      # Verify with JSON diagnostics
vera verify --quiet file.vera     # Verify, suppress success output
vera compile file.vera                    # Compile to .wasm binary
vera compile --wat file.vera              # Print WAT text (human-readable WASM)
vera compile --target browser file.vera   # Compile + emit browser bundle
vera compile --target wasi-p2 file.vera   # Emit a WASI Preview 2 component (experimental, IO+Random; #237)
vera run file.vera                # Compile and execute (calls main)
vera run file.vera --fn f -- 42   # Call function f with argument 42
vera run --target wasi-p2 file.vera  # Execute under the built-in WASI 0.2 host (spec/13-wasi.md)
vera compile --target wasi-p2 --world server file.vera  # wasi:http server component for `wasmtime serve` (spec §13.7)
vera serve file.vera              # Serve handle(Request -> Response) over HTTP (#305)
vera serve --port 8080 file.vera  # Serve on a specific port (default 8000)
vera test file.vera               # Contract-driven testing via Z3 + WASM
vera test --json file.vera        # Test with JSON output
vera test --trials 50 file.vera   # Limit trials per function (default 100)
vera parse file.vera              # Print the parse tree
vera ast file.vera                # Print the typed AST
vera ast --json file.vera         # Print the AST as JSON
vera fmt file.vera                # Format to canonical form (stdout)
vera fmt --write file.vera        # Format in place
vera fmt --check file.vera        # Check if already canonical
vera lsp                          # Serve LSP over stdio (needs the [lsp] extra; see LSP_SERVER.md)
vera version                      # Print the installed version (also --version, -V)
vera builtins [--json]            # List the built-in function registry (no file needed)
vera effects [--json]             # List the effect and ability registry (no file needed)
vera errors [--json]              # List the diagnostic error-code registry E001–E702 (no file needed)

pytest tests/ -v                  # Run the test suite (see TESTING.md)
VERA_JS_COVERAGE=1 pytest tests/test_browser.py -v  # Browser tests with JS coverage
VERA_EAGER_GC=1 vera run file.vera  # Force GC on every alloc (see ENVIRONMENT.md, debug knob for #593-class GC-rooting bugs)
mypy vera/                        # Type-check the compiler itself

python scripts/check_conformance.py    # Verify all 104 conformance programs (positives pass their level; negatives fail with their expected_error E-code)
python scripts/check_examples.py      # Verify all 36 examples parse + check + verify
python scripts/check_examples_readme.py # Verify vera run commands in examples/README.md
python scripts/check_spec_examples.py # Verify spec code blocks parse
python scripts/check_readme_examples.py # Verify README code blocks parse
python scripts/check_examples_doc.py  # Verify EXAMPLES.md code blocks parse
python scripts/check_skill_examples.py # Verify SKILL.md code blocks parse
python scripts/check_faq_examples.py  # Verify FAQ code blocks parse
python scripts/check_html_examples.py # Verify HTML code blocks parse + check + verify
python scripts/check_doc_builtin_shadowing.py # Verify no doc example redefines a built-in (E151; #819)
python scripts/check_diagnostic_fields.py # Verify every diagnostic carries rationale + spec_ref (+ fix for errors; warnings exempt) or a # diag-fields-exempt reason (#682)
python scripts/check_explicit_encoding.py # Verify every text-mode open()/read_text()/write_text() passes explicit encoding='utf-8' (#645)
python scripts/build_site.py          # Regenerate AI-readable site assets (llms.txt, etc.)
python scripts/check_site_assets.py   # Verify site assets are up-to-date
python scripts/check_version_sync.py  # Verify version consistency
python scripts/check_doc_counts.py    # Verify documentation counts match codebase
python scripts/check_licenses.py      # Verify all package licenses are MIT-compatible
python scripts/check_wheel_availability.py # Verify every runtime dep has wheels for all supported platforms (README §Supported platforms)
python scripts/check_limitations_sync.py              # Verify limitation tables are in sync
python scripts/check_limitations_sync.py --check-states # Also verify issues are still open via GitHub API
python scripts/fix_allowlists.py      # Preview stale allowlist line numbers
python scripts/fix_allowlists.py --fix # Auto-fix stale allowlist line numbers
```

See [`TOOLCHAIN.md`](TOOLCHAIN.md) for the CLI cookbook — driving the toolchain to write, verify, test, run, and debug Vera, including the `builtins`/`effects`/`errors` introspection commands.

## Project layout

- `spec/` — Language specification (Chapters 0-13)
- `vera/` — Reference compiler: grammar, parser, AST, transformer, type checker, verifier, codegen, CLI
- `examples/` — 36 example Vera programs (all must pass `vera check` and `vera verify`)
- `tests/` — Test suite (unit tests + conformance suite)
- `tests/conformance/` — 104 conformance programs validating every language feature against the spec
- `scripts/` — CI and validation scripts

## Writing Vera code

Read `SKILL.md` for the full language reference. It covers syntax, slot references, contracts, effects, common mistakes, and working examples.

### De Bruijn slot references

See [`DE_BRUIJN.md`](DE_BRUIJN.md) for the full treatment. In brief: Vera uses De Bruijn indexing for slot references: `@T.0` = **most recent** (last) binding of type T, not the first. For a function `fn foo(@Int, @Int -> @Int)`:

- `@Int.0` = second parameter (most recent)
- `@Int.1` = first parameter

This matters when multiple parameters share a type. See `tests/conformance/ch03_slot_indexing.vera` for the canonical test. Commutative operations like `@Int.0 + @Int.1` mask the ordering, so be especially careful with non-commutative operations (division, comparison, subtraction) and recursive calls where parameter position determines semantics.

## Working on the compiler

Read `vera/README.md` for architecture docs, module map, and design patterns.

The compiler pipeline: source -> parse (`parser.py`) -> transform (`transform.py`) -> typecheck (`checker.py`) -> verify (`verifier.py`) -> compile (`codegen/` + `wasm/`) -> execute (wasmtime).

The language server (`vera/lsp/`, served by `vera lsp`) and the obligation core it sits on (`vera/obligations/`: reified `ProofObligation` records + the warm incremental `VerificationSession`) are documented in `LSP_SERVER.md` (user/agent surface, including the four custom proof-delta methods) and the `vera/README.md` module map (architecture). The custom methods are the agent-facing way to ask "does this edit still prove?" without round-tripping through `vera verify`.

Each stage is a module with a public API function and is independently testable. See `CONTRIBUTING.md` for contribution guidelines.

## Test-first: prove every change with a test

Before changing code — **adding or removing** — write the test that proves your hypothesis and confirm it **fails for the reason you care about**, then make the change and watch it flip. A passing suite is necessary, not sufficient: green *without* your change does not prove removed code was dead (the distinguishing case may simply be untested), and green *with* it does not prove added code does anything (nothing may exercise it). A test that is green both before and after the change proves nothing about the change.

- Removing code because "no test relies on it" is backwards — tests don't enumerate what the system needs. Write the test that *would* fail if the code is load-bearing; if you genuinely can't make it fail, that is itself the evidence.
- Choose inputs that **cannot coincide with a fallback/default value**. A default that happens to equal the right answer makes a real bug invisible — a `forall<T>` instantiation-discovery miss once passed CI because the test's where-helper returned `Bool`, the same value as the inference's phantom-var default, so wrong and right looked identical.
- For cross-component soundness invariants (e.g. the verifier must statically check exactly the set codegen emits), the proving check is a **differential** — run both sides and compare — not a unit test; a green unit suite can hide a desync between the two.

## What not to break

- Pre-commit hooks run mypy + pytest + conformance suite + example validation on every commit
- All 104 conformance programs in `tests/conformance/` must hold at their declared level — positive entries pass, and the negative fixtures (`ch08_circular_import`, `ch08_visibility_private`, `ch09_builtin_redefinition`) must *fail* `check` with their `expected_error` E-code
- All 36 examples in `examples/` must pass `vera check` and `vera verify`
- Version must stay in sync across `vera/__init__.py`, `pyproject.toml`, and `CHANGELOG.md`
- All tests must pass: `pytest tests/ -v`
- Type checking must be clean: `mypy vera/`
- Every runtime dep must have wheels for all supported platforms: `python scripts/check_wheel_availability.py` (CI gate; see README §Supported platforms for the policy this enforces)

## Common workflows

**Add a test:** Tests live in `tests/`. Use `_check_ok()` / `_check_err()` / `_verify_ok()` / `_verify_err()` helpers (see existing tests for patterns).

**Add a CLI command:** Edit `vera/cli.py`. Add a `cmd_<name>` function, wire it in `main()`, add tests in `tests/test_cli.py`.

**Extend the grammar:** Edit `vera/grammar.lark`, update `vera/transform.py` to handle new tree nodes, add AST nodes in `vera/ast.py`, add type-checking in `vera/checker.py`.

**Add an example:** Create a `.vera` file in `examples/`. It must pass both `vera check` and `vera verify`. The validation script `scripts/check_examples.py` tests all examples automatically.

**Add a conformance test:** Create a `.vera` file in `tests/conformance/` named `chNN_feature.vera`. Add a header comment with the spec chapter and features tested. Format it with `vera fmt --write`. Add a manifest entry in `manifest.json` with the appropriate level and feature tags. Run `python scripts/check_conformance.py` to validate. When implementing a new language feature, write the conformance test first.

## JSON diagnostics

`vera check --json` and `vera verify --json` output machine-readable diagnostics. The output is a single JSON object on stdout:

```json
{"ok": true, "file": "...", "diagnostics": [], "warnings": []}
```

Each diagnostic includes: `severity`, `description`, `location` (`file`, `line`, `column`), `source_line`, `rationale`, `fix`, `spec_ref`, and `error_code`. The `verify --json` output also includes a `verification` summary with `tier1_verified`, `tier3_runtime`, and `total` counts.

### Error codes

Every diagnostic has a stable error code (`E001`–`E702`). Codes are grouped by compiler phase:

| Range | Phase |
|-------|-------|
| E001–E009 | Parse & transform errors |
| E010 | Transform errors |
| E1xx | Type check: core + expressions |
| E2xx | Type check: calls |
| E3xx | Type check: control flow |
| E5xx | Verification |
| E6xx | Codegen |
| E7xx | Testing |

See `vera/errors.py` `ERROR_CODES` dict for the full registry.

## Git workflow

The `main` branch is protected — all changes require a PR with passing CI. Never commit directly to main; always create a feature branch, push it, and open a PR.

When creating commits, use this co-author trailer:

    Co-Authored-By: Claude <noreply@anthropic.invalid>

Do NOT use `noreply@anthropic.com` — that email resolves to an unrelated GitHub account. The `.invalid` TLD (RFC 2606) is reserved and will never resolve to a real address.

## Release workflow

- **Completed issues in the feature PR**: When an issue is closed by a PR, **delete** the entry from `ROADMAP.md` entirely and add a one-liner to the relevant version row in the **most recent Stage table in `HISTORY.md`**.  Stage numbers roll forward periodically — check `grep "^## Stage" HISTORY.md | tail -1` to confirm the current stage before writing (a stale "Stage 9" reference here caused a correction on 2026-05-11, by which point the project had moved through Stages 10, 11, and 12).  Do NOT use `<del>` strikethroughs in ROADMAP.md — completed items live in HISTORY.md, not as struck-through clutter in the roadmap.
- **No strikethroughs anywhere in docs**: Things are either future (in ROADMAP.md) or past (in HISTORY.md). Do NOT use `<del>` or `~~...~~` to strike through completed items in ROADMAP.md, spec chapters, SKILL.md limitation tables, or anywhere else in the documentation. Instead: delete completed items from wherever they appear as future work, and add a note in HISTORY.md or CHANGELOG.md. Limitation tables in the spec should only list current limitations — fixed items are removed, not struck through, with a reference to the CHANGELOG entry that fixed them.
- **CHANGELOG link references**: Keep a Changelog format requires `[version]: compare-url` link references at the bottom of CHANGELOG.md. These must be added for every new version. The `[Unreleased]` link must point to `latest-tag...HEAD`.
- **Roadmap is in ROADMAP.md**: The project roadmap (phase table, priority tiers, completed-phase details) lives in `ROADMAP.md`, not README.md. README.md links to it.
- **"No known bugs." convention**: When the `KNOWN_ISSUES.md` Bugs section is empty (or after removing the last entry), keep the `## Bugs` heading and use the literal text `No known bugs.` as the section body — do NOT leave an empty markdown table.  Apply the same convention to `SKILL.md`'s "Known Bugs and Workarounds" section when its table becomes empty.  This established at v0.0.155 (#673 merge) and re-applied at v0.0.156 (#685 merge, plus a sweep that found a stale row for the by-then-closed #602).
- **CHANGELOG gate (`Skip-changelog:` trailer)**: `scripts/check_changelog_updated.py` blocks any PR touching `vera/` or `spec/` unless `CHANGELOG.md` gains a new `[Unreleased]` bullet or a new version section.  Add the entry proactively when making substantive changes.  If a change genuinely doesn't merit a CHANGELOG entry (e.g. a comment-only edit to a `vera/` source file), include `Skip-changelog: <one-line reason>` in a commit message trailer to bypass the gate.  Don't paper-over with empty bullets — the gate exists to keep the release notes accurate.
- **Release mechanics (maintainer-side, after merge)**: tag the merge commit on `main` (`git tag vX.Y.Z <merge-sha> && git push origin vX.Y.Z`; if a tag was created on the feature branch during review, move it to the merge commit), extract the matching CHANGELOG section as the notes, and publish with `gh release create vX.Y.Z --verify-tag --title vX.Y.Z --notes-file <extracted-section>`.  Re-pointing an existing tag demotes its published release to draft — re-publish with `gh release edit vX.Y.Z --draft=false`.  The contributor-facing half (what a release-prep PR must contain) lives in CONTRIBUTING.md §Releases; #481 tracks automating this.
- **Fold-in releases**: a small immediate follow-up to a just-published release may fold into it rather than cutting a new version — add its bullets to the **latest released** CHANGELOG section (the changelog gate accepts new bullets there; older sections are frozen), merge, move the tag to the new merge commit, and re-publish the notes.
- **Merge style**: squash-merge multi-round PRs (review iterations don't need to land on `main` individually); a merge commit is fine for single-commit PRs.

## CodeRabbit

This repo uses [CodeRabbit](https://coderabbit.ai) for AI code review on pull requests. Configuration is in `.coderabbit.yaml`.

- **Reply with `@coderabbitai`**: When responding to CodeRabbit review comments on a PR, prefix your reply with `@coderabbitai` so the bot registers the interaction. You can discuss, argue against, or ask for clarification on any suggestion.
- **Commands**: Use `@coderabbitai pause`, `@coderabbitai review`, `@coderabbitai full review`, `@coderabbitai generate unit tests` in PR comments to control the bot.
- **Learning**: Tell CodeRabbit about project-specific rules and it will update its knowledge base for future reviews.

## Shell pitfalls

- **Heredocs with single quotes in `gh` commands**: `gh issue create --body "$(cat <<'EOF' ... EOF)"` breaks if the body contains single quotes (apostrophes, contractions). Use plain double-quoted `--body "..."` instead.

## Cross-platform pitfalls (test fixtures)

The CI matrix tests on `{ubuntu-latest, macos-15, macos-26, windows-latest} × {3.11, 3.12, 3.13}` (12 combinations; macOS pinned explicitly to insulate from silent `macos-latest` migration — see README §Supported platforms).  When writing test fixtures, three Windows-portability rules apply — see the **Test Fixture Conventions** section in `TESTING.md` for full examples:

- `tempfile.NamedTemporaryFile` handed off to a subprocess MUST use `delete=False` + manual `Path.unlink()` (Windows can't reopen a held file).
- Paths embedded into Vera string literals MUST be POSIX-form (`Path(tmp_path).as_posix()`); Windows backslashes trip Vera's `\U` escape grammar.
- Text I/O MUST pass `encoding="utf-8"` explicitly, enforced by `scripts/check_explicit_encoding.py` (pre-commit + CI lint, #645): every text-mode `open()` / `read_text()` / `write_text()` **and** every `subprocess.run/Popen/check_output(..., text=True)` capture. A deliberate non-UTF-8 site opts out with `# encoding-exempt: <reason>`. The `vera` CLI also reconfigures its stdout/stderr to UTF-8 at startup, so a Vera program printing `→` / `—` is UTF-8 on any locale. Together these replaced the `PYTHONUTF8=1` CI backstop (#641), which has been removed — no reliance on the runner's or a local Windows shell's locale.
