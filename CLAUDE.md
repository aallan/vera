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

## Key commands

```bash
vera check file.vera              # Parse and type-check
vera check --json file.vera       # Type-check with JSON diagnostics
vera verify file.vera             # Type-check + verify contracts via Z3
vera verify --json file.vera      # Verify with JSON diagnostics
vera compile file.vera            # Compile to .wasm binary
vera compile --wat file.vera      # Print WAT text (human-readable WASM)
vera run file.vera                # Compile and execute (calls main)
vera run file.vera --fn f -- 42   # Call function f with argument 42
vera test file.vera               # Contract-driven testing via Z3 + WASM
vera test --json file.vera        # Test with JSON output
vera test --trials 50 file.vera   # Limit trials per function (default 100)
vera parse file.vera              # Print the parse tree
vera ast file.vera                # Print the typed AST
vera ast --json file.vera         # Print the AST as JSON
vera fmt file.vera                # Format to canonical form (stdout)
vera fmt --write file.vera        # Format in place
vera fmt --check file.vera        # Check if already canonical

pytest tests/ -v                  # Run the test suite (see TESTING.md)
mypy vera/                        # Type-check the compiler itself

python scripts/check_conformance.py    # Verify all 48 conformance programs pass their declared level
python scripts/check_examples.py      # Verify all 20 examples parse + check + verify
python scripts/check_spec_examples.py # Verify spec code blocks parse
python scripts/check_readme_examples.py # Verify README code blocks parse
python scripts/check_skill_examples.py # Verify SKILL.md code blocks parse
python scripts/check_version_sync.py  # Verify version consistency
python scripts/fix_allowlists.py      # Preview stale allowlist line numbers
python scripts/fix_allowlists.py --fix # Auto-fix stale allowlist line numbers
```

## Project layout

- `spec/` — Language specification (Chapters 0-12)
- `vera/` — Reference compiler: grammar, parser, AST, transformer, type checker, verifier, codegen, CLI
- `examples/` — 20 example Vera programs (all must pass `vera check` and `vera verify`)
- `tests/` — Test suite (unit tests + conformance suite)
- `tests/conformance/` — 48 conformance programs validating every language feature against the spec
- `scripts/` — CI and validation scripts

## Writing Vera code

Read `SKILL.md` for the full language reference. It covers syntax, slot references, contracts, effects, common mistakes, and working examples.

## Working on the compiler

Read `vera/README.md` for architecture docs, module map, and design patterns.

The compiler pipeline: source -> parse (`parser.py`) -> transform (`transform.py`) -> typecheck (`checker.py`) -> verify (`verifier.py`) -> compile (`codegen/` + `wasm/`) -> execute (wasmtime).

Each stage is a module with a public API function and is independently testable. See `CONTRIBUTING.md` for contribution guidelines.

## What not to break

- Pre-commit hooks run mypy + pytest + conformance suite + example validation on every commit
- All 48 conformance programs in `tests/conformance/` must pass their declared level
- All 20 examples in `examples/` must pass `vera check` and `vera verify`
- Version must stay in sync across `vera/__init__.py`, `pyproject.toml`, and `CHANGELOG.md`
- All tests must pass: `pytest tests/ -v`
- Type checking must be clean: `mypy vera/`

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

## Git commits

When creating commits, use this co-author trailer:

    Co-Authored-By: Claude <noreply@anthropic.invalid>

Do NOT use `noreply@anthropic.com` — that email resolves to an unrelated GitHub account. The `.invalid` TLD (RFC 2606) is reserved and will never resolve to a real address.
