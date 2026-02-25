# CLAUDE.md — Project orientation for Claude Code

Vera is a programming language designed for LLMs to write. It has mandatory contracts, algebraic effects, typed slot references (`@T.n`), and compiles to WebAssembly. The reference compiler is written in Python.

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
vera parse file.vera              # Print the parse tree
vera ast file.vera                # Print the typed AST
vera ast --json file.vera         # Print the AST as JSON

pytest tests/ -v                  # Run the test suite (795 tests)
mypy vera/                        # Type-check the compiler itself

python scripts/check_examples.py      # Verify all 14 examples parse + check + verify
python scripts/check_spec_examples.py # Verify spec code blocks parse
python scripts/check_readme_examples.py # Verify README code blocks parse
python scripts/check_version_sync.py  # Verify version consistency
```

## Project layout

- `spec/` — Language specification (Chapters 0-7, 10-11)
- `vera/` — Reference compiler: grammar, parser, AST, transformer, type checker, verifier, codegen, CLI
- `examples/` — 14 example Vera programs (all must pass `vera check` and `vera verify`)
- `tests/` — Test suite
- `scripts/` — CI and validation scripts
- `runtime/` — WASM runtime support (future)

## Writing Vera code

Read `SKILLS.md` for the full language reference. It covers syntax, slot references, contracts, effects, common mistakes, and working examples.

## Working on the compiler

Read `vera/README.md` for architecture docs, module map, and design patterns.

The compiler pipeline: source -> parse (`parser.py`) -> transform (`transform.py`) -> typecheck (`checker.py`) -> verify (`verifier.py`) -> compile (`codegen.py` + `wasm.py`) -> execute (wasmtime).

Each stage is a module with a public API function and is independently testable. See `CONTRIBUTING.md` for contribution guidelines.

## What not to break

- Pre-commit hooks run mypy + pytest + example validation on every commit
- All 14 examples in `examples/` must pass `vera check` and `vera verify`
- Version must stay in sync across `vera/__init__.py`, `pyproject.toml`, and `CHANGELOG.md`
- All tests must pass: `pytest tests/ -v`
- Type checking must be clean: `mypy vera/`

## Common workflows

**Add a test:** Tests live in `tests/`. Use `_check_ok()` / `_check_err()` / `_verify_ok()` / `_verify_err()` helpers (see existing tests for patterns).

**Add a CLI command:** Edit `vera/cli.py`. Add a `cmd_<name>` function, wire it in `main()`, add tests in `tests/test_cli.py`.

**Extend the grammar:** Edit `vera/grammar.lark`, update `vera/transform.py` to handle new tree nodes, add AST nodes in `vera/ast.py`, add type-checking in `vera/checker.py`.

**Add an example:** Create a `.vera` file in `examples/`. It must pass both `vera check` and `vera verify`. The validation script `scripts/check_examples.py` tests all examples automatically.

## JSON diagnostics

`vera check --json` and `vera verify --json` output machine-readable diagnostics. The output is a single JSON object on stdout:

```json
{"ok": true, "file": "...", "diagnostics": [], "warnings": []}
```

Each diagnostic includes: `severity`, `description`, `location` (`file`, `line`, `column`), `source_line`, `rationale`, `fix`, and `spec_ref`. The `verify --json` output also includes a `verification` summary with `tier1_verified`, `tier3_runtime`, and `total` counts.
