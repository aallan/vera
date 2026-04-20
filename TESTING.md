# Testing

This is the single source of truth for Vera's testing infrastructure, coverage data, and test conventions.

## Overview

| Metric | Value |
|--------|-------|
| **Tests** | 3,395 across 28 files (~34,000 lines of test code; 3,381 passed, 14 skipped) |
| **Compiler code coverage** | 96% of 15,149 statements (CI minimum: 80%) |
| **Conformance programs** | 77 programs across 9 spec chapters, validating every language feature |
| **Example programs** | 30, all validated through `vera check` + `vera verify` |
| **Spec code blocks** | 164 parseable blocks from 13 spec chapters: 86 parse, 72 type-check, 71 verify |
| **README code blocks** | 13 Vera blocks (12 validated, 1 allowlisted future syntax) |
| **FAQ code blocks** | 1 Vera block in FAQ.md (0 validated, 1 allowlisted snippet) |
| **HTML code blocks** | 5 Vera blocks in docs/index.html (5 validated: parse + check + verify) |
| **Contract verification** | 162 of 179 contracts (90.5%) verified statically (Tier 1) |
| **CI matrix** | 6 combinations (Python 3.11/3.12/3.13 x Ubuntu/macOS) + browser parity (Node.js 22) |

## Running Tests

All commands assume the virtual environment is active (`source .venv/bin/activate`).

```bash
# Test suite
pytest tests/ -v                                     # full suite, verbose
pytest tests/test_codegen.py                         # single file
pytest tests/test_codegen.py::TestArithmetic          # single class
pytest tests/test_conformance.py -v                  # conformance suite only
pytest tests/ --cov=vera --cov-report=term-missing   # with coverage

# JavaScript coverage (browser runtime)
VERA_JS_COVERAGE=1 pytest tests/test_browser.py -v  # V8 coverage via c8

# Type checking
mypy vera/                                           # strict mode

# Validation scripts
python scripts/check_conformance.py                  # conformance suite (77 programs, see manifest.json)
python scripts/check_examples.py                     # 30 example programs
python scripts/check_spec_examples.py                # spec code blocks
python scripts/check_readme_examples.py              # README code blocks
python scripts/check_skill_examples.py               # SKILL.md code blocks
python scripts/check_faq_examples.py                 # FAQ.md code blocks
python scripts/check_html_examples.py               # docs/index.html code blocks
python scripts/check_version_sync.py                 # version consistency
python scripts/fix_allowlists.py --fix               # auto-fix stale allowlists
```

## Test Files

| File | Tests | Lines | What it covers |
|------|------:|------:|----------------|
| `test_parser.py` | 124 | 968 | Grammar rules, operator precedence, parse errors |
| `test_ast.py` | 123 | 1,130 | AST transformation, node structure, serialisation, string escape sequences, ability declarations |
| `test_checker.py` | 508 | 5,656 | Type synthesis, slot resolution, effects, effect subtyping, contracts, exhaustiveness, cross-module typing, visibility, error codes, string built-ins, generic rejection, IO operation types, Markdown types, Regex types, abilities, Map collection, Set collection, Decimal type, Json type, Html type, Http effect, Inference effect, removed legacy name regression |
| `test_verifier.py` | 132 | 1,886 | Z3 verification, counterexamples, tier classification, call-site preconditions, branch-aware preconditions, pipe operator, cross-module contracts, match/ADT verification, decreases verification, mutual recursion, refined Bool/String/Float64 param sorts |
| `test_codegen.py` | 881 | 11,104 | WASM compilation, arithmetic, Float64, Byte, arrays (incl. compound element types), ADTs, match (incl. nested patterns), generics, State\<T\>, Exn\<E\> handlers, control flow, strings, string escape sequences, IO (read\_line, read\_file, write\_file, args, exit, get\_env, sleep, time, stderr), bounds checking, quantifiers, assert/assume, refinement type aliases, pipe operator, string built-ins, built-in shadowing, parse\_nat Result, GC, Markdown host bindings, Regex host bindings, Map collection, Set collection, Decimal type, Json type, Html type, Http effect, Inference effect, Random effect, example round-trips, GC shadow stack overflow |
| `test_codegen_contracts.py` | 32 | 576 | Runtime pre/postconditions, contract fail messages, old/new state postconditions |
| `test_codegen_monomorphize.py` | 71 | 1,326 | Generic instantiation, type inference, monomorphization edge cases, ability constraint satisfaction (Eq/Ord/Hash/Show), operation rewriting (eq/compare), show/hash dispatch, ADT auto-derivation, array operations (slice/map/filter/fold) |
| `test_codegen_closures.py` | 19 | 473 | Closure lifting, captured variables, higher-order functions |
| `test_codegen_modules.py` | 19 | 565 | Cross-module guard rail, cross-module codegen, name collision detection (E608/E609/E610) |
| `test_codegen_coverage.py` | 5 | 250 | Defensive error paths: E600, E601, E605, E606, unknown module calls  |
| `test_errors.py` | 52 | 525 | Error code registry, diagnostic formatting, serialisation, SourceLocation, error display sync (README/HTML/spec) |
| `test_formatter.py` | 114 | 1,075 | Comment extraction, interior comment positioning, expression/declaration formatting, match arm block bodies, idempotency, parenthesization, spec rules, ability declarations |
| `test_cli.py` | 217 | 3,021 | CLI commands (check, verify, compile, run, test, fmt, version, quiet), subprocess integration, JSON error paths, runtime traps, arg validation, multi-file resolution, IO exit codes, --explain-slots |
| `test_resolver.py` | 15 | 412 | Module resolution, path lookup, parse caching, circular import detection |
| `test_types.py` | 73 | 390 | Type operations: subtyping, effect subtyping, equality, substitution, pretty-printing, canonical names |
| `test_wasm.py` | 22 | 255 | WASM internals: StringPool, WasmSlotEnv, translation edge cases via full pipeline |
| `test_verifier_coverage.py` | 79 | 1,260 | Verifier/SMT coverage gaps: SMT encoding paths, verifier edge cases, defensive branches |
| `test_wasm_coverage.py` | 225 | 3,903 | WASM coverage gaps: helpers unit tests, inference branches, closure free-var walking, operator/data/context edge cases |
| `test_tester.py` | 14 | 369 | Contract-driven testing: tier classification, input generation, test execution, skip message content |
| `test_tester_coverage.py` | 34 | 901 | Tester coverage gaps: String/Float64/ADT parameter input generation, Bool/Byte parameters, unsatisfiable preconditions, type expression edge cases |
| `test_markdown.py` | 59 | 394 | Markdown parser: block/inline parsing, rendering, round-trips, edge cases |
| `test_browser.py` | 79 | 1,084 | Browser parity: Python/wasmtime vs Node.js/JS-runtime output equivalence across IO, State, contracts, Markdown, Regex, and all compilable examples |
| `test_conformance.py` | 385 | 102 | Parametrized conformance suite: parse, check, verify, run, format idempotency across 77 programs |
| `test_prelude.py` | 24 | 422 | Prelude injection: Option/Result/array operation detection, combinator shadowing, type aliases, end-to-end compilation |
| `test_readme.py` | 2 | 79 | README code sample parsing |
| `test_html.py` | 4 | 164 | HTML landing page code samples: parse, check, verify |
| `test_build_site.py` | 17 | 213 | `_abs_links` unit tests: relative link rewriting, fenced block immunity (backtick and tilde fences, inline backticks inside fences), http/https/fragment pass-through, Vera effect syntax not mis-parsed |
| `test_check_changelog_updated.py` | 66 | 638 | `check_changelog_updated.py` unit + end-to-end tests: file classification (incl. file-style exact-match vs directory-style prefix-match), CHANGELOG diff parsing with `[Unreleased]` section tracking, bare-heading rejection, and full-file context (regression test for bullets far below the heading), `Skip-changelog:` trailer detection, temp-repo integration covering substantive/exempt/label/trailer paths |

## Conformance Suite

The conformance suite is a collection of 77 small, focused programs in `tests/conformance/` that systematically validate every language feature against the spec. Each program is self-contained and imports nothing, with the single exception of `ch07_cross_module_contracts.vera` which depends on `ch07_cross_module_contracts_lib.vera`. Each program tests one feature or a small group of related features.

Simon Willison [argues](https://simonwillison.net/tags/conformance-suites/) that conformance suites are a "huge unlock" for language projects — they transform development from trust-based to verification-based. The conformance suite serves as the definitive specification artifact that any implementation (or agent) can validate against.

### Three-layer testing model

Vera has three distinct test layers, each serving a different purpose:

| Layer | Location | Purpose | What it tests |
|-------|----------|---------|---------------|
| **Unit tests** | `tests/test_*.py` | Test compiler internals | Error paths, edge cases, internal APIs |
| **Conformance suite** | `tests/conformance/` | Spec-anchored feature validation | Every language feature, one program per feature |
| **Example programs** | `examples/` | Showcase programs and demos | End-to-end usage, documentation |

Unit tests verify that the compiler works correctly. Conformance programs verify that the *language* works correctly. Examples demonstrate how to use the language. All three run in CI and pre-commit hooks.

### Test levels

Each conformance program declares the deepest pipeline stage it must pass:

| Level | What it validates | Count |
|-------|-------------------|------:|
| `parse` | Source text is syntactically valid | 0 |
| `check` | Parses and type-checks cleanly | 4 |
| `verify` | Type-checks and all contracts verified by Z3 | 6 |
| `run` | Compiles to WASM and executes correctly | 67 |

Almost all programs are at the `run` level — they compile and execute, producing correct results. Four programs (`ch07_cross_module_contracts_lib`, `ch09_http`, `ch09_inference`, `ch03_typed_holes`) are at the `check` level. Six programs (`ch03_slot_let_chains`, `ch03_slot_noncommutative`, `ch07_cross_module_contracts`, `ch07_io_sleep`, `ch07_random_effect`, `ch09_math_builtins`) are at the `verify` level, using Z3-provable contracts.

### Skipped tests

`pytest tests/ -v` reports 14 skipped tests across two categories:

**Level-limited skips** — the conformance framework only runs tests up to the declared level; stages beyond that level are automatically skipped. These are expected and correct.

| Test | Program | Declared level | Skipped stage | Reason |
|------|---------|---------------|--------------|--------|
| `test_run[ch03_slot_let_chains]` | `ch03_slot_let_chains.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_run[ch03_slot_noncommutative]` | `ch03_slot_noncommutative.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_verify[ch03_typed_holes]` | `ch03_typed_holes.vera` | `check` | `verify` | `check`-level program: verify stage not run |
| `test_run[ch03_typed_holes]` | `ch03_typed_holes.vera` | `check` | `run` | `check`-level program: no standalone `main` |
| `test_run[ch07_cross_module_contracts]` | `ch07_cross_module_contracts.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_verify[ch07_cross_module_contracts_lib]` | `ch07_cross_module_contracts_lib.vera` | `check` | `verify` | `check`-level program: verify stage not run |
| `test_run[ch07_cross_module_contracts_lib]` | `ch07_cross_module_contracts_lib.vera` | `check` | `run` | `check`-level library module: no standalone `main` |
| `test_run[ch07_io_sleep]` | `ch07_io_sleep.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_run[ch07_random_effect]` | `ch07_random_effect.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_run[ch09_math_builtins]` | `ch09_math_builtins.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |

**Environment-gated skips** — these programs require network access or a live API key that is not available in CI. They pass `vera check` (type-checking) but cannot be executed.

| Test | Program | Declared level | Skipped stage | Reason |
|------|---------|---------------|--------------|--------|
| `test_verify[ch09_http]` | `ch09_http.vera` | `check` | `verify` | Requires outbound HTTP; unavailable in CI sandbox |
| `test_run[ch09_http]` | `ch09_http.vera` | `check` | `run` | Requires outbound HTTP; unavailable in CI sandbox |
| `test_verify[ch09_inference]` | `ch09_inference.vera` | `check` | `verify` | Requires `VERA_*_API_KEY`; not set in CI |
| `test_run[ch09_inference]` | `ch09_inference.vera` | `check` | `run` | Requires `VERA_*_API_KEY`; not set in CI |

To run the environment-gated tests locally: set `VERA_ANTHROPIC_API_KEY` (or another provider key) and ensure outbound HTTP is available, then `vera run tests/conformance/ch09_http.vera` / `vera run tests/conformance/ch09_inference.vera`.

### Directory structure

```
tests/conformance/
├── manifest.json              # Machine-readable test metadata
├── ch01_int_literals.vera     # Chapter 1: Integer literals
├── ch01_float_literals.vera   # Chapter 1: Float64 literals
├── ch01_string_escapes.vera   # Chapter 1: String escape sequences
├── ...                        # 77 programs total, organized by spec chapter
├── ch07_state_handler.vera    # Chapter 7: State<T> effect handler
├── ch07_exn_handler.vera      # Chapter 7: Exn<E> effect handler
├── ch09_numeric_builtins.vera # Chapter 9: Numeric built-in functions
├── ch09_type_conversions.vera # Chapter 9: Numeric type conversions
├── ch09_markdown.vera         # Chapter 9: Markdown standard library
├── ch09_regex.vera            # Chapter 9: Regular expression matching
├── ch09_decimal.vera          # Chapter 9: Decimal type operations
├── ch09_json.vera             # Chapter 9: JSON standard library
├── ch09_http.vera             # Chapter 9: Http effect (check level)
└── ch10_float_predicates.vera # Chapter 9: Float64 predicates and constants
```

### Manifest

`manifest.json` maps each program to its spec chapter, test level, and feature tags:

```json
{
  "id": "ch04_arithmetic",
  "file": "ch04_arithmetic.vera",
  "chapter": 4,
  "title": "Arithmetic operators",
  "level": "run",
  "spec_ref": "Section 4.1",
  "features": ["add", "sub", "mul", "div", "mod", "unary_neg"]
}
```

The manifest is the machine-readable feature inventory — agents can query it to find which features exist and where they are tested.

### Running the conformance suite

```bash
# Via pytest (parametrized — 385 tests)
pytest tests/test_conformance.py -v

# Via standalone script (used in CI and pre-commit)
python scripts/check_conformance.py
```

The pytest runner (`test_conformance.py`) parametrizes over every manifest entry and runs five checks per program: parse, check, verify, run, and format idempotency.

### Adding a conformance test

1. Write a `.vera` program in `tests/conformance/` following the naming convention `chNN_feature_name.vera`
2. Include a header comment indicating the spec chapter and what the program tests
3. Ensure the program has a `main` function (for `run`-level tests)
4. Format it: `vera fmt --write tests/conformance/your_file.vera`
5. Add an entry to `manifest.json` with the appropriate level and feature tags
6. Run `python scripts/check_conformance.py` to validate

When implementing a new language feature, the conformance program should be written *first* — this is test-driven development against the spec.

## Compiler Code Coverage

Coverage by module, measured by `pytest --cov=vera`:

| Module | Stmts | Miss | Coverage |
|--------|------:|-----:|---------:|
| `codegen/` | 1,934 | 99 | 95% |
| `checker/` | 1,117 | 73 | 93% |
| `wasm/` | 7,473 | 268 | 96% |
| `browser/` | 21 | 0 | 100% |
| `verifier.py` | 429 | 0 | 100% |
| `transform.py` | 564 | 16 | 97% |
| `formatter.py` | 673 | 54 | 92% |
| `ast.py` | 460 | 30 | 93% |
| `smt.py` | 495 | 0 | 100% |
| `markdown.py` | 413 | 54 | 87% |
| `types.py` | 182 | 7 | 96% |
| `errors.py` | 126 | 1 | 99% |
| `environment.py` | 239 | 8 | 97% |
| `cli.py` | 474 | 0 | 100% |
| `parser.py` | 45 | 0 | 100% |
| `resolver.py` | 68 | 2 | 97% |
| `tester.py` | 312 | 0 | 100% |
| `prelude.py` | 106 | 0 | 100% |
| `registration.py` | 18 | 0 | 100% |
| **Total** | **15,149** | **612** | **96%** |

The lowest-coverage module is `markdown.py` at 87%, reflecting Markdown AST traversal edge cases. The `wasm/` subsystem was improved from 79% to 96% by [#156](https://github.com/aallan/vera/issues/156) and [#324](https://github.com/aallan/vera/issues/324); the remaining gaps are mostly in `wasm/inference.py` (85%) deep type-dispatch branches for specific builtin functions.

## Contract Verification Coverage

Vera's verifier classifies each contract into one of three tiers. **Tier 1** contracts are proved correct statically by Z3 — no runtime overhead. **Tier 3** contracts cannot be fully decided by the SMT solver and fall back to runtime assertion checks. The verifier never rejects a valid program; it simply warns when a contract drops to Tier 3.

Across all 30 example programs:

| Metric | Value |
|--------|-------|
| **Tier 1 (static)** | 162 contracts — proved automatically by Z3 |
| **Tier 3 (runtime)** | 16 contracts — verified at runtime via assertion checks |
| **Total** | 177 contracts (91.0% static) |

The 16 remaining Tier 3 contracts and why they cannot be promoted:

| Example | Contract | Reason |
|---------|----------|--------|
| async\_futures.vera | 2 contracts | Async/future combinators not in decidable fragment |
| collections.vera | 8 contracts | Collection operations (Map/Set) not modeled in Z3 |
| gc\_pressure.vera | `decreases` in `repeat` | Termination metric not in decidable fragment |
| generics.vera | `ensures(@T.result == @T.0)` | Generic type parameters have no Z3 sort |
| generics.vera | `ensures(@A.result == @A.0)` | Generic type parameters have no Z3 sort |
| increment.vera | `ensures(new(State<Int>) == old(State<Int>) + 1)` | `old`/`new` state modeling not yet implemented |
| json.vera | 2 contracts | Json ADT operations not modeled in Z3 |

The Tier 1 fragment covers: integer/boolean arithmetic, comparisons, if/else, let bindings, match expressions, ADT constructors, function calls (modular postcondition), `length`, and `decreases` clauses (self-recursive, mutual recursion via where-blocks, Nat and structural ADT measures).

## Language Feature Coverage

How Vera language features (by spec chapter) map to test files and example programs:

| Spec chapter | Feature | Test files | Conformance | Examples |
|-------------|---------|-----------|-------------|----------|
| Ch 1: Lexical | Literals (Int, Float64, Bool, Byte, String) | test_ast, test_codegen | ch01_int_literals, ch01_float_literals, ch01_bool_literals, ch01_byte_literals | most examples |
| Ch 1: Lexical | String escape sequences (`\n`, `\t`, `\\`, `\"`, `\r`, `\0`, `\u{XXXX}`) | test_ast, test_codegen | ch01_string_escapes | io_operations, file_io |
| Ch 1: Lexical | Comments | test_parser | ch01_comments | — |
| Ch 2: Types | Int, Nat, Bool, String, Float64, Byte, Unit | test_codegen, test_checker | ch02_builtin_types | most examples |
| Ch 2: Types | ADTs (algebraic data types), Option, Result | test_codegen, test_checker | ch02_adt_basic, ch02_adt_recursive, ch02_option_result | pattern_matching, list_ops |
| Ch 2: Types | Refinement types | test_codegen, test_verifier | ch02_refinement_types | refinement_types, safe_divide |
| Ch 2: Types | Generics (`forall<T>`) | test_codegen_monomorphize, test_checker | ch02_generics | generics |
| Ch 3: Slots | `@T.n` references, De Bruijn indexing | test_checker, test_codegen | ch03_slot_basic, ch03_slot_indexing, ch03_slot_result | all 30 examples |
| Ch 4: Expressions | Arithmetic, comparison, boolean, unary ops | test_codegen, test_checker | ch04_arithmetic, ch04_comparison, ch04_boolean_ops | factorial, absolute_value |
| Ch 4: Expressions | If/else, let, match, pipe operator | test_codegen, test_checker | ch04_if_else, ch04_let_binding, ch04_match_basic, ch04_match_nested, ch04_pipe_operator | pattern_matching |
| Ch 4: Expressions | String and array builtins | test_codegen | ch04_string_builtins, ch04_array_ops | string_ops |
| Ch 5: Functions | Declarations, recursion, mutual recursion | test_codegen, test_checker | ch05_basic_function, ch05_recursion, ch05_mutual_recursion | factorial, mutual_recursion |
| Ch 5: Functions | Closures, higher-order functions | test_codegen_closures | ch05_closures | closures |
| Ch 5: Functions | Visibility (`public`/`private`) | test_checker | ch05_visibility | modules |
| Ch 6: Contracts | Preconditions (`requires`) | test_codegen_contracts, test_verifier | ch06_requires | safe_divide |
| Ch 6: Contracts | Postconditions (`ensures`) | test_codegen_contracts, test_verifier | ch06_ensures | absolute_value |
| Ch 6: Contracts | Decreases clauses, assert/assume | test_verifier, test_codegen | ch06_decreases, ch06_assert_assume | factorial |
| Ch 6: Contracts | Quantifiers (forall, exists) | test_codegen, test_verifier | ch06_quantifiers | quantifiers |
| Ch 7: Effects | Pure, IO, State\<T\> | test_codegen, test_checker | ch07_pure, ch07_io, ch07_state_handler | hello_world, increment, io_operations, file_io |
| Ch 7: Effects | Effect handlers (State\<T\>, Exn\<E\>) | test_codegen, test_checker | ch07_state_handler, ch07_exn_handler | effect_handler |
| Ch 9: Stdlib | Numeric builtins (abs, min, max, floor, ceil, round, sqrt, pow) | test_codegen, test_checker | ch09_numeric_builtins | — |
| Ch 9: Stdlib | Type conversions (int_to_float, float_to_int, nat_to_int, int_to_nat, byte_to_int, int_to_byte) | test_codegen, test_checker | ch09_type_conversions | — |
| Ch 9: Stdlib | Float64 predicates (float_is_nan, float_is_infinite, nan, infinity) | test_codegen, test_checker | ch10_float_predicates | — |
| Ch 7: Effects | Effect subtyping (§7.8), call-site checking | test_types, test_checker | — | — |
| Ch 2: Types | Bidirectional type checking (local inference) | test_checker | — | — |
| Ch 4: Expressions | Nested constructor patterns in match | test_codegen | ch04_match_nested | pattern_matching |
| Ch 8: Modules | Imports, cross-module typing and codegen | test_codegen_modules, test_resolver | — | modules |
| Ch 11: Compilation | Cross-module name collision detection (E608/E609/E610) | test_codegen_modules | — | — |
| Ch 9: Stdlib | Markdown (md_parse, md_render, md_has_heading, md_has_code_block, md_extract_code_blocks) | test_codegen, test_markdown | ch09_markdown | markdown |
| Ch 9: Stdlib | Regex (regex_match, regex_find, regex_find_all, regex_replace) | test_codegen, test_checker | ch09_regex | regex |
| Ch 9: Stdlib | Map, Set, Decimal collections | test_codegen, test_checker | ch09_map, ch09_set, ch09_decimal, ch09_decimal_generics | collections |
| Ch 9: Stdlib | Json (json_parse, json_stringify, json_get, json_array_get, json_array_length, json_keys, json_has_field, json_type) | test_codegen, test_checker | ch09_json | json |
| Ch 9: Stdlib | Html (html_parse, html_to_string, html_query, html_text, html_attr) | test_codegen, test_checker | ch09_html | html |
| Ch 9: Stdlib | Http effect (Http.get, Http.post) | test_codegen, test_checker | ch09_http | http |
| Ch 11: Compilation | Contract-driven testing (Z3 input gen + WASM execution) | test_tester, test_cli | — | safe_divide, factorial |
| Ch 12: Runtime | Browser runtime parity (JS host bindings match Python) | test_browser | — | — |

## Test Helpers

Each test module defines module-level helper functions (no `conftest.py`):

```python
# test_checker.py pattern:
_check_ok(source)              # assert no type errors
_check_err(source, "match")    # assert at least one error matching substring

# test_verifier.py pattern:
_verify_ok(source)             # assert no verification errors
_verify_err(source, "match")   # assert at least one verification error
_verify_warn(source, "match")  # assert at least one warning

# test_codegen.py pattern:
_compile_ok(source)            # assert compilation succeeds
_run(source, fn, args)         # compile + execute, return result
_run_io(source, fn, args)      # compile + execute, return captured stdout
_run_trap(source, fn, args)    # compile + execute, assert WASM trap
```

## Round-Trip Testing

Every one of the 30 example programs in `examples/` is tested through **every pipeline stage** via parametrised tests: parsing, AST transformation, type checking, contract verification, WASM compilation, and execution. If you add a new `.vera` example, it is automatically included in the round-trip suite.

The formatter has **idempotency tests**: `format(format(x)) == format(x)` for all tested programs.

## Adding Tests

When extending the compiler, add tests following the existing patterns:

1. **New grammar construct:** Add parser tests to `test_parser.py` (positive and negative)
2. **New AST node:** Add transformation tests to `test_ast.py` (check node fields, spans, serialisation)
3. **New type rule:** Add checker tests to `test_checker.py` using `_check_ok()`/`_check_err()`
4. **New SMT support:** Add verifier tests to `test_verifier.py` using `_verify_ok()`/`_verify_err()`
5. **New codegen support:** Add compilation tests to `test_codegen.py` using `_compile_ok()`/`_run()`/`_run_trap()`
6. **New example program:** Add to `examples/` -- it is automatically included in round-trip tests
7. **New error pattern:** Add formatting tests to `test_errors.py`
8. **New tester feature:** Add tests to `test_tester.py` using `_test(source)` helper
9. **New host binding:** Add parity tests to `test_browser.py` to ensure the JavaScript runtime stays in sync with the Python runtime

## Validation Scripts

Twelve scripts in `scripts/` validate cross-cutting concerns beyond unit tests:

| Script | What it validates |
|--------|-------------------|
| `check_conformance.py` | All 77 conformance programs pass their declared level (parse/check/verify/run) |
| `check_examples.py` | All 30 `.vera` examples pass `vera check` + `vera verify` |
| `check_spec_examples.py` | 148 parseable code blocks from spec chapters: parse, type-check, and verify |
| `check_readme_examples.py` | All Vera code blocks in README.md parse correctly |
| `check_skill_examples.py` | All Vera code blocks in SKILL.md parse correctly |
| `check_faq_examples.py` | All Vera code blocks in FAQ.md parse correctly |
| `check_html_examples.py` | All Vera code blocks in docs/index.html pass parse + check + verify |
| `check_site_assets.py` | Generated site assets under `docs/` are up-to-date |
| `check_version_sync.py` | `pyproject.toml` and `vera/__init__.py` versions match |
| `check_doc_counts.py` | Counts cited in TESTING.md, CONTRIBUTING.md, and CLAUDE.md match live codebase |
| `check_licenses.py` | All installed packages have MIT-compatible licenses |
| `fix_allowlists.py` | Auto-fix stale allowlist line numbers after Markdown edits |

These run in both pre-commit hooks and CI, so issues are caught locally before they reach the remote.

### Spec validation pipeline

`check_spec_examples.py` pushes spec code blocks through three compiler stages, with allowlists at each level:

| Stage | Pass | Allowlisted | Categories |
|-------|-----:|------------:|------------|
| **Parse** | 81 | 67 | FUTURE (9), FRAGMENT (58) |
| **Type-check** | 67 | 14 | INCOMPLETE (13), FUTURE (1) |
| **Verify** | 66 | 1 | ILLUSTRATIVE (1) |

Allowlisted entries have stale-detection: when a feature lands or a spec edit shifts line numbers, CI flags the entry for removal or the `fix_allowlists.py` script auto-fixes the line numbers. The INCOMPLETE check entries reference functions, types, or imports not defined in the block (e.g. `abs`, `Tuple`, `array_map`, `parse_int`). The 1 FUTURE check entry uses `async/await`. The 1 ILLUSTRATIVE verify entry is a spec example demonstrating multiple postconditions syntax where the contract is intentionally imprecise.

## Pre-commit Hooks

Every push is checked by 25 configured hooks across two stages: 23 are configured at the commit stage (after `pre-commit install`), and 2 (`check-changelog-updated`, `uv-lock-check`) are configured at the push stage (after `pre-commit install --hook-type pre-push`). Many commit-stage hooks use per-hook `files:` / `types:` filters and only fire when matching files are staged — a docs-only commit triggers a small subset, a compiler-level commit triggers most. Full list:

| Hook | What it does |
|------|-------------|
| `trailing-whitespace` | Strip trailing whitespace |
| `end-of-file-fixer` | Ensure files end with a newline |
| `check-yaml` / `check-toml` | Validate config file syntax |
| `check-merge-conflict` | Detect conflict markers |
| `check-added-large-files` | Reject files >500 KB |
| `debug-statements` | Detect `pdb`/`ipdb` imports |
| `mypy vera/` | Type-check compiler in strict mode |
| `pytest tests/ -q` | Run full test suite |
| `fix_allowlists.py --fix` | Auto-fix stale allowlist line numbers |
| `check_conformance.py` | All 77 conformance programs pass their declared level |
| `check_examples.py` | All 30 examples pass `vera check` + `vera verify` |
| `check_examples_readme.py` | `vera run` commands in `examples/README.md` reference existing files and exported functions |
| `check_readme_examples.py` | README code blocks parse correctly |
| `check_examples_doc.py` | EXAMPLES.md code blocks parse correctly |
| `check_skill_examples.py` | SKILL.md code blocks parse correctly |
| `check_faq_examples.py` | FAQ.md code blocks parse correctly |
| `check_html_examples.py` | HTML landing page code blocks pass parse + check + verify |
| `check_doc_counts.py` | Counts in docs match live codebase |
| `check_limitations_sync.py` | Limitation tables consistent across KNOWN_ISSUES.md, vera/README, and spec |
| `check_licenses.py` | All package licenses are MIT-compatible |
| `build_site.py` | Regenerate AI-readable site assets (llms.txt, llms-full.txt, robots.txt, sitemap.xml, index.md) |
| `browser parity` | Browser runtime produces identical output to Python runtime |
| `check-changelog-updated` (pre-push) | CHANGELOG has a new entry when substantive files changed |
| `uv-lock-check` (pre-push) | `uv.lock` is in sync with `pyproject.toml` |

The validation hooks are smart about triggers -- they only run when relevant files change (`.vera`, `vera/**/*.py`, `grammar.lark`, the corresponding Markdown file, or `vera/browser/*` for browser parity). The two pre-push hooks only fire at push time.

## CI Pipeline

GitHub Actions ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs seven parallel jobs on every push and pull request to `main`:

| Job | Matrix / Runner | What it checks |
|-----|----------------|---------------|
| **test** | Python 3.11, 3.12, 3.13 x Ubuntu, macOS (6 combos) | `pytest -v` passes on all combinations |
| **test** (coverage) | Python 3.12 x Ubuntu only | `pytest --cov=vera --cov-fail-under=80` |
| **typecheck** | Python 3.12 x Ubuntu | `mypy vera/` clean in strict mode |
| **lint** | Python 3.12 x Ubuntu | `check_conformance.py`, `check_examples.py`, `check_examples_readme.py`, `check_version_sync.py`, `check_spec_examples.py`, `check_readme_examples.py`, `check_skill_examples.py`, `check_faq_examples.py`, `check_html_examples.py`, `check_site_assets.py`, `check_licenses.py`, `ruff check --select S vera/` (security rules) |
| **security** | Ubuntu | [Gitleaks](https://github.com/gitleaks/gitleaks-action) secret scanning on full history |
| **dependency-audit** | Python 3.12 x Ubuntu | `pip-audit --skip-editable --ignore-vuln CVE-2026-4539` — checks all installed packages against the OSV vulnerability database (skips the local editable `vera` package; `CVE-2026-4539` suppressed pending a pygments fix release) |
| **sbom** | Python 3.12 x Ubuntu | `cyclonedx-py environment` — generates a [CycloneDX](https://cyclonedx.org) JSON SBOM of the full installed dependency tree and uploads it as a 90-day CI artifact |
| **browser-parity** | Python 3.12 + Node.js 22 x Ubuntu | `pytest tests/test_browser.py -v` — verifies JS runtime matches Python runtime; collects V8 coverage via `NODE_V8_COVERAGE` and uploads to Codecov |

The coverage threshold of **80%** is enforced in CI. Current coverage is 96%. JavaScript coverage for `vera/browser/runtime.mjs` is collected separately using V8's built-in coverage and uploaded to Codecov with the `javascript` flag.

Each job uses scoped permissions (`contents: read`; the security job additionally has `security-events: write`) and all checkout steps set `persist-credentials: false` to prevent the `GITHUB_TOKEN` from being baked into `.git/config`. Actions without SHA-pinned version refs are tracked in [#390](https://github.com/aallan/vera/issues/390).

## Open CI/Tooling Issues

Tracked improvements to the testing and CI infrastructure:

| Issue | Description |
|-------|-------------|
| [#349](https://github.com/aallan/vera/issues/349) | Improve browser runtime (`runtime.mjs`) test coverage to >80% — JS code is invisible to pytest-cov, blocking codecov/patch on PRs that touch the runtime |

## Opportunities

Testing infrastructure that could be added in the future:

- **Property-based testing** -- `hypothesis` is installed as a dev dependency but not yet used. Could generate random programs to test parser robustness and formatter idempotency at scale.
- **Formatter round-trip invariant** -- verify `parse(format(parse(src))) == parse(src)` for all valid programs, not just the examples.
- **WASM inference.py coverage** -- `wasm/inference.py` at 85% has the most remaining gaps, mostly in deep type-dispatch branches for specific builtin function return types. These branches require very specific expression nesting patterns to reach.
- **Performance benchmarks** -- no benchmark infrastructure exists. Could track compilation time and Z3 verification time across releases.
