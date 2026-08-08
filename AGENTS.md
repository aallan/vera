# AGENTS.md — Instructions for AI agents

This document is for AI agents working with the Vera codebase. There are two audiences: agents writing Vera code, and agents working on the compiler.

## For agents writing Vera code

Read `SKILL.md` for the full language reference. It covers syntax, slot references, contracts, effects, common mistakes, and working examples that all parse correctly.

### Conformance programs as reference

The conformance suite in `tests/conformance/` contains 179 small, self-contained programs — often one per language feature — that serve as minimal working examples (most are fully self-contained; the cross-module programs of Chapters 7–9 import companion `_lib`/module fixtures). Each positive program must pass its declared verification level (see `manifest.json` for mappings: `parse`, `check`, `verify`, or `run`); the twenty-five negative fixtures (`ch02_generic_over_unit_rejected`, `ch02_map_unit_value_rejected`, `ch04_let_unit_rejected`, `ch05_apply_fn_arity`, `ch05_decreases_float_rejected`, `ch05_reserved_fn_name_rejected`, `ch05_reserved_keyword_fn_rejected`, `ch05_where_helper_outer_slot_rejected`, `ch07_handler_state_body_scope_rejected`, `ch07_old_outside_ensures_rejected`, `ch07_state_unit_op_param_read_rejected`, `ch08_circular_import`, `ch08_reserved_vera_prefix_rejected`, `ch08_visibility_private`, `ch09_builtin_effect_redefinition_rejected`, `ch09_builtin_redefinition`, `ch09_ord_adt_rejected`, `ch09_eq_non_derivable_rejected`, `ch09_sql_injection_rejected`, `ch09_sql_placeholder_mismatch_rejected`, `ch09_sql_placeholder_let_mismatch_rejected`, `ch09_sql_numbered_placeholder_rejected`, `ch07_bare_effect_op_rejected`, `ch06_quantifier_array_domain_rejected`, `ch07_handler_state_type_mismatch_rejected`) instead must *fail* `check` with the E-code in their `expected_error` field. When you need to see how a specific construct works (e.g. effect handlers, match expressions, closures), check the corresponding conformance program before reading the spec.

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
vera serve file.vera              # Serve handle(Request -> Response) over HTTP (default :8000)
vera test file.vera               # Contract-driven testing via Z3 + WASM
vera test --json file.vera        # Test with JSON output
vera test --trials 50 file.vera   # Limit trials per function (default 100)
vera fmt file.vera                # Format to canonical form (stdout)
vera fmt --write file.vera        # Format in place
vera fmt --check file.vera        # Check if already canonical
vera version                      # Print the installed version (also --version, -V)
vera lsp                          # Serve LSP over stdio (needs the [lsp] extra; see LSP_SERVER.md)
vera builtins [--json]            # List the built-in function registry (no file needed)
vera effects [--json]             # List the effect and ability registry (no file needed)
vera errors [--json]              # List the diagnostic error-code registry E001–E702 (no file needed)
```

See [TOOLCHAIN.md](TOOLCHAIN.md) for the CLI cookbook — driving the toolchain to write, verify, test, run, and debug Vera, including the `builtins`/`effects`/`errors` introspection commands.

### The language server: proof deltas without re-running the CLI

For long editing sessions, `vera lsp` (install: `pip install -e ".[lsp]"`) keeps a warm incremental Z3 session alive, so verification feedback arrives at editor latency instead of cold-start latency. Any LSP client gets diagnostics (same error codes as `--json`), per-function verification-tier hints, hover types, slot go-to-definition, and typed-hole completion.

Four custom methods exist specifically for agents — full request/response shapes in [LSP_SERVER.md](LSP_SERVER.md):

| Method | Question it answers |
|---|---|
| `vera/speculativeEdit` | "Would this edit keep, break, or strengthen the proofs?" — in-memory verify, returns a proof delta, touches nothing |
| `vera/proposeEdit` | "Apply this edit *iff* it verifies" — the gate cannot be skipped; `force: true` overrides loudly |
| `vera/strengthenContract` | "Tighten this contract — do all call sites still satisfy it?" — refusals point at the breaking call sites |
| `vera/addEffect` | "Thread this effect through every transitive caller" — one verified multi-site rewrite, all-or-nothing |

The intended loop: draft → `speculativeEdit` → inspect the delta → `proposeEdit`. Prefer the two structured refactors over hand-editing contracts/effect rows — the server constructs the candidate and audits the blast radius for you.

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
      "spec_ref": "Chapter 5, Section 5.2 \"Function Declaration Syntax\"",
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
| E020 | Unterminated block comment — `{-` with no matching `-}` (they nest, so each needs its own closer) |
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
5. `Inference.complete(@String.0)` returns `Result<String, String>`; requires `VERA_ANTHROPIC_API_KEY`, `VERA_OPENAI_API_KEY`, `VERA_MOONSHOT_API_KEY` (Kimi), `VERA_MISTRAL_API_KEY`, or `VERA_XAI_API_KEY` (Grok) to run; provider auto-detected from whichever key is set.  See [`ENVIRONMENT.md`](ENVIRONMENT.md) for the full env-var reference, including `VERA_INFERENCE_PROVIDER` / `VERA_INFERENCE_MODEL` overrides
6. Recursive functions need a `decreases()` clause
7. Match expressions must be exhaustive
8. `DB.query` / `DB.execute` (effect `<DB>`) take a **literal** SQL string — a query assembled from a runtime value is a compile-time error (`E207`). Every runtime value goes through a `?` placeholder and the `Array<Option<String>>` params array (`DB.query("SELECT ... WHERE id = ?", [Some(@String.0)])`); a placeholder/params count mismatch with a literal params array is `E208`. The connection comes from `VERA_DB_URL` (default: in-memory SQLite) — see [`ENVIRONMENT.md`](ENVIRONMENT.md)

## For agents working on the compiler

Read `vera/README.md` for architecture docs, module map, and design patterns.

### Pipeline

```
source -> parse (parser.py) -> transform (transform.py) -> resolve (resolver.py) -> typecheck (checker.py) -> verify (verifier.py) -> compile (codegen/ + wasm/) -> execute (wasmtime or browser/runtime.mjs)
```

Each stage is a module with a single public API function (`parse_file`, `transform`, `resolve_imports`, `typecheck`, `verify`, `compile`, `execute`, `test`) and is independently testable.

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
python scripts/check_conformance.py    # All 179 conformance programs hold (positives pass; negatives fail with their E-code)
python scripts/check_examples.py       # All 42 examples must pass
python scripts/check_corpus_canonical.py # All 227 corpus programs in canonical form
```

Test helpers follow a pattern: `_check_ok(source)` / `_check_err(source, match)` / `_verify_ok(source)` / `_verify_err(source, match)`. See existing tests for examples.

When implementing a new language feature, write the conformance program *first* — add a `.vera` file and manifest entry in `tests/conformance/`, then implement the feature until the conformance test passes.

### Invariants

- All 179 conformance programs in `tests/conformance/` must hold at their declared level — positive entries pass, and the negative fixtures (`ch02_generic_over_unit_rejected`, `ch02_map_unit_value_rejected`, `ch04_let_unit_rejected`, `ch05_apply_fn_arity`, `ch05_decreases_float_rejected`, `ch05_reserved_fn_name_rejected`, `ch05_reserved_keyword_fn_rejected`, `ch05_where_helper_outer_slot_rejected`, `ch07_handler_state_body_scope_rejected`, `ch07_old_outside_ensures_rejected`, `ch07_state_unit_op_param_read_rejected`, `ch08_circular_import`, `ch08_reserved_vera_prefix_rejected`, `ch08_visibility_private`, `ch09_builtin_effect_redefinition_rejected`, `ch09_builtin_redefinition`, `ch09_ord_adt_rejected`, `ch09_eq_non_derivable_rejected`, `ch09_sql_injection_rejected`, `ch09_sql_placeholder_mismatch_rejected`, `ch09_sql_placeholder_let_mismatch_rejected`, `ch09_sql_numbered_placeholder_rejected`, `ch07_bare_effect_op_rejected`, `ch06_quantifier_array_domain_rejected`, `ch07_handler_state_type_mismatch_rejected`) must *fail* `check` with their `expected_error` E-code
- All 42 examples in `examples/` must pass `vera check` and `vera verify`
- `mypy vera/` must be clean
- `pytest tests/ -v` must pass
- Version must stay in sync across `pyproject.toml`, `vera/__init__.py`, `docs/index.html`, `README.md`, and `uv.lock` (gated by `scripts/check_version_sync.py`); CHANGELOG.md must also carry a matching `## [X.Y.Z]` section

### Releases and install docs

**Releases are automated after merge.** A version bump on `main` (synced across the `scripts/check_version_sync.py` surface, with a matching non-empty `CHANGELOG.md` section) triggers `.github/workflows/release.yml`: it builds, waits for the maintainer to approve the protected `pypi` environment, publishes to PyPI via Trusted Publishing, then creates the tag and GitHub Release at the merge SHA. Do NOT create tags, run `twine`, or `gh release create` — the maintainer and the workflow own that. See `CONTRIBUTING.md` §Releases and `RELEASING.md`.

**Install docs are circumstance-dependent — match `README.md`, `SKILL.md`, and `PYPI_README.md`; don't invent "the install route".** The GitHub source checkout (`pip install -e .`, plus `[lsp]` or `[dev]`) is the full environment — the toolchain alongside `examples/`, `tests/conformance/`, and `spec/` — and is the recommended route for agents; `pip install veralang` installs the toolchain only; the `[lsp]` extra adds the language server; never write `pip install vera` (an unrelated PyPI project). Only document a channel as an available install route once the artifact is live there **and** the install flow works end to end — check the registry, don't rely on what you remember. The VS Code extension meets that bar: [`veralang.vera-language`](https://marketplace.visualstudio.com/items?itemName=veralang.vera-language) installs from the Marketplace, in the Extensions view or via `code --install-extension veralang.vera-language`. The same gate applies to any future distribution channel.

### Contributing

See `CONTRIBUTING.md` for guidelines. Pre-commit hooks run mypy, pytest, trailing whitespace checks, and validate all examples on every commit.
