# AGENTS.md — Instructions for AI agents

This document is for AI agents working with the Vera codebase. There are two audiences: agents writing Vera code, and agents working on the compiler.

## For agents writing Vera code

Read `SKILLS.md` for the full language reference. It covers syntax, slot references, contracts, effects, common mistakes, and working examples that all parse correctly.

### Workflow

```
write .vera file -> vera check -> fix errors -> vera verify -> fix errors -> done
```

### Commands

```bash
vera check file.vera              # Parse and type-check
vera check --json file.vera       # Type-check with JSON output (for parsing)
vera verify file.vera             # Type-check + verify contracts via Z3
vera verify --json file.vera      # Verify with JSON output (for parsing)
vera compile file.vera            # Compile to .wasm binary
vera compile --wat file.vera      # Print WAT text (human-readable WASM)
vera run file.vera                # Compile and execute (calls main)
vera run file.vera --fn f -- 42   # Call function f with argument 42
```

### Error handling

Error messages are natural language instructions explaining what went wrong and how to fix it. They include the offending source line, a rationale, a concrete code fix, and a spec reference. Feed the full error back into your context to correct the code.

For machine-parseable errors, use the `--json` flag:

```json
{
  "ok": false,
  "file": "example.vera",
  "diagnostics": [
    {
      "severity": "error",
      "description": "Function is missing its contract block...",
      "location": {"file": "example.vera", "line": 12, "column": 1},
      "source_line": "fn add(@Int, @Int -> @Int)",
      "rationale": "Vera requires all functions to have explicit contracts...",
      "fix": "Add a contract block after the signature:\n\n  fn example(@Int -> @Int)\n    requires(true)\n    ensures(@Int.result >= 0)\n    effects(pure)\n  {\n    ...\n  }",
      "spec_ref": "Chapter 5, Section 5.1 \"Function Structure\""
    }
  ],
  "warnings": []
}
```

The `verify --json` output includes a verification summary:

```json
{
  "ok": true,
  "file": "example.vera",
  "diagnostics": [],
  "warnings": [],
  "verification": {
    "tier1_verified": 2,
    "tier3_runtime": 0,
    "total": 2
  }
}
```

### Essential rules

1. Every function needs `requires()`, `ensures()`, and `effects()` between the signature and body
2. Use `@Type.index` to reference bindings (`@Int.0` = most recent Int, `@Int.1` = one before)
3. Declare all effects: `effects(pure)` for pure functions, `effects(<IO>)` for IO
4. Recursive functions need a `decreases()` clause
5. Match expressions must be exhaustive

## For agents working on the compiler

Read `vera/README.md` for architecture docs, module map, and design patterns.

### Pipeline

```
source -> parse (parser.py) -> transform (transform.py) -> typecheck (checker.py) -> verify (verifier.py) -> compile (codegen.py + wasm.py) -> execute (wasmtime)
```

Each stage is a module with a single public API function (`parse_file`, `transform`, `typecheck`, `verify`, `compile`, `execute`) and is independently testable.

### Key modules

| Module | Purpose |
|--------|---------|
| `vera/grammar.lark` | Lark LALR(1) grammar |
| `vera/parser.py` | Parser: source text to Lark parse tree |
| `vera/transform.py` | Lark tree to typed AST |
| `vera/ast.py` | AST node definitions |
| `vera/types.py` | Internal type representation |
| `vera/environment.py` | Type environment and slot resolution |
| `vera/checker.py` | Type checker |
| `vera/smt.py` | Z3 SMT translation layer |
| `vera/verifier.py` | Contract verifier |
| `vera/registration.py` | Shared function registration for checker and verifier |
| `vera/errors.py` | LLM-oriented diagnostics |
| `vera/wasm.py` | WASM translation layer |
| `vera/codegen.py` | Code generation orchestrator |
| `vera/cli.py` | Command-line interface |

### Testing

```bash
pytest tests/ -v                       # Run all tests (660 tests)
mypy vera/                             # Type-check the compiler
python scripts/check_examples.py       # All 14 examples must pass
```

Test helpers follow a pattern: `_check_ok(source)` / `_check_err(source, match)` / `_verify_ok(source)` / `_verify_err(source, match)`. See existing tests for examples.

### Invariants

- All 14 examples in `examples/` must pass `vera check` and `vera verify`
- `mypy vera/` must be clean
- `pytest tests/ -v` must pass (currently 660 tests)
- Version must be in sync across `vera/__init__.py`, `pyproject.toml`, and `CHANGELOG.md`

### Contributing

See `CONTRIBUTING.md` for guidelines. Pre-commit hooks run mypy, pytest, trailing whitespace checks, and validate all examples on every commit.
