# AGENTS.md — Instructions for AI agents

This document is for AI agents working with the Vera codebase. There are two audiences: agents writing Vera code, and agents working on the compiler.

## For agents writing Vera code

Read `SKILL.md` for the full language reference. It covers syntax, slot references, contracts, effects, common mistakes, and working examples that all parse correctly.

### Conformance programs as reference

The conformance suite in `tests/conformance/` contains 79 small, self-contained programs — one per language feature — that serve as minimal working examples. Each program must pass its declared verification level (see `manifest.json` for mappings: `parse`, `check`, `verify`, or `run`). When you need to see how a specific construct works (e.g. effect handlers, match expressions, closures), check the corresponding conformance program before reading the spec.

### Workflow

```text
write .vera file -> vera check -> fix errors -> vera verify -> fix errors -> done
```

Use **typed holes** (`?`) to build programs incrementally. A `?` in any expression position is valid — `vera check` reports a `W001` warning with the expected type and all available slot bindings:

```text
Warning [W001]: Typed hole: expected Int.
Fix: Replace ? with an expression of type Int. Available bindings: @Int.0: Int; @Int.1: Int.
```

Programs with holes type-check (`ok: true`) but cannot compile (`E614`). Iterative workflow:

```text
write skeleton with ? -> vera check (get W001 hints) -> fill holes -> vera check -> vera verify
```

### Commands

```bash
vera check file.vera              # Parse and type-check
vera check --json file.vera       # Type-check with JSON output (for parsing)
vera verify file.vera             # Type-check + verify contracts via Z3
vera verify --json file.vera      # Verify with JSON output (for parsing)
vera compile file.vera                    # Compile to .wasm binary
vera compile --wat file.vera              # Print WAT text (human-readable WASM)
vera compile --target browser file.vera   # Compile + emit browser bundle
vera run file.vera                # Compile and execute (calls main)
vera run file.vera --fn f -- 42   # Call function f with argument 42
vera test file.vera               # Contract-driven testing via Z3 + WASM
vera test --json file.vera        # Test with JSON output
vera test --trials 50 file.vera   # Limit trials per function (default 100)
vera fmt file.vera                # Format to canonical form (stdout)
vera fmt --write file.vera        # Format in place
vera fmt --check file.vera        # Check if already canonical
vera version                      # Print the installed version (also --version, -V)
```

### Error handling

Error messages are natural language instructions explaining what went wrong and how to fix it. They include the offending source line, a rationale, a concrete code fix, a spec reference, and a stable error code. Feed the full error back into your context to correct the code.

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
      "source_line": "private fn add(@Int, @Int -> @Int)",
      "rationale": "Vera requires all functions to have explicit contracts...",
      "fix": "Add a contract block after the signature:\n\n  private fn example(@Int -> @Int)\n    requires(true)\n    ensures(@Int.result >= 0)\n    effects(pure)\n  {\n    ...\n  }",
      "spec_ref": "Chapter 5, Section 5.1 \"Function Structure\"",
      "error_code": "E001"
    }
  ],
  "warnings": []
}
```

### Error codes

Every diagnostic has a stable error code. Common codes:

| Code | Meaning |
|------|---------|
| W001 | Typed hole (`?`) — expected type and available bindings reported |
| E001 | Missing contract block (requires/ensures/effects) |
| E121 | Function body type doesn't match return type |
| E130 | Unresolved slot reference (@T.n has no matching binding) |
| E140 | Arithmetic requires numeric operands |
| E170 | Let binding type mismatch |
| E200 | Unresolved function call |
| E300 | If condition is not Bool |
| E311 | Non-exhaustive match |
| E614 | Program contains typed holes — compile rejected until holes are filled |

Full code ranges: W0xx (warnings), E0xx (parse), E1xx (type/expressions), E2xx (calls), E3xx (control flow), E5xx (verification), E6xx (codegen), E7xx (testing). See `vera/errors.py` `ERROR_CODES` for the complete registry.

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
3. Declare all effects: `effects(pure)` for pure functions, `effects(<IO>)` for IO, `effects(<Http>)` for network, `effects(<Inference>)` for LLM calls
4. `Http.get(@String.0)` and `Http.post(@String.0, @String.1)` return `Result<String, String>`; match the result
5. `Inference.complete(@String.0)` returns `Result<String, String>`; requires `VERA_ANTHROPIC_API_KEY`, `VERA_OPENAI_API_KEY`, `VERA_MOONSHOT_API_KEY` (Kimi), or `VERA_MISTRAL_API_KEY` to run; provider auto-detected from whichever key is set
6. Recursive functions need a `decreases()` clause
7. Match expressions must be exhaustive

## For agents working on the compiler

Read `vera/README.md` for architecture docs, module map, and design patterns.

### Pipeline

```
source -> parse (parser.py) -> transform (transform.py) -> typecheck (checker.py) -> verify (verifier.py) -> compile (codegen/ + wasm/) -> execute (wasmtime or browser/runtime.mjs)
```

Each stage is a module with a single public API function (`parse_file`, `transform`, `typecheck`, `verify`, `compile`, `execute`, `test`) and is independently testable.

### Key modules

| Module | Purpose |
|--------|---------|
| `vera/grammar.lark` | Lark LALR(1) grammar |
| `vera/parser.py` | Parser: source text to Lark parse tree |
| `vera/transform.py` | Lark tree to typed AST |
| `vera/ast.py` | AST node definitions |
| `vera/types.py` | Internal type representation |
| `vera/environment.py` | Type environment and slot resolution |
| `vera/checker/` | Type checker (mixin package) |
| `vera/smt.py` | Z3 SMT translation layer |
| `vera/verifier.py` | Contract verifier |
| `vera/registration.py` | Shared function registration for checker and verifier |
| `vera/errors.py` | LLM-oriented diagnostics |
| `vera/wasm/` | WASM translation layer (mixin package) |
| `vera/codegen/` | Code generation orchestrator (mixin package) |
| `vera/tester.py` | Contract-driven testing engine |
| `vera/cli.py` | Command-line interface |
| `vera/markdown.py` | Markdown parser (host-side implementation) |
| `vera/browser/` | Browser runtime: JS host bindings, Node.js harness, bundle emission |

### Testing

```bash
pytest tests/ -v                       # Run all tests (see TESTING.md)
pytest tests/test_conformance.py -v    # Conformance suite only
mypy vera/                             # Type-check the compiler
python scripts/check_conformance.py    # All 79 conformance programs must pass
python scripts/check_examples.py       # All 32 examples must pass
```

Test helpers follow a pattern: `_check_ok(source)` / `_check_err(source, match)` / `_verify_ok(source)` / `_verify_err(source, match)`. See existing tests for examples.

When implementing a new language feature, write the conformance program *first* — add a `.vera` file and manifest entry in `tests/conformance/`, then implement the feature until the conformance test passes.

### Invariants

- All 79 conformance programs in `tests/conformance/` must pass their declared level
- All 32 examples in `examples/` must pass `vera check` and `vera verify`
- `mypy vera/` must be clean
- `pytest tests/ -v` must pass
- Version must be in sync across `vera/__init__.py`, `pyproject.toml`, and `CHANGELOG.md`

### Contributing

See `CONTRIBUTING.md` for guidelines. Pre-commit hooks run mypy, pytest, trailing whitespace checks, and validate all examples on every commit.
