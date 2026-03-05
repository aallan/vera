# Testing

This is the single source of truth for Vera's testing infrastructure, coverage data, and test conventions.

## Overview

| Metric | Value |
|--------|-------|
| **Tests** | 1,418 across 19 files (~18,300 lines of test code) |
| **Compiler code coverage** | 90% of 8,788 statements (CI minimum: 80%) |
| **Example programs** | 18, all validated through `vera check` + `vera verify` |
| **Spec code blocks** | 96 parseable blocks from 13 spec chapters: 72 parse, 57 type-check, 56 verify |
| **README code blocks** | 6 Vera blocks (5 validated, 1 allowlisted future syntax) |
| **Contract verification** | 112 of 118 contracts (94.9%) verified statically (Tier 1) |
| **CI matrix** | 6 combinations (Python 3.11/3.12/3.13 x Ubuntu/macOS) |

## Running Tests

All commands assume the virtual environment is active (`source .venv/bin/activate`).

```bash
# Test suite
pytest tests/ -v                                     # full suite, verbose
pytest tests/test_codegen.py                         # single file
pytest tests/test_codegen.py::TestArithmetic          # single class
pytest tests/ --cov=vera --cov-report=term-missing   # with coverage

# Type checking
mypy vera/                                           # strict mode

# Validation scripts
python scripts/check_examples.py                     # 18 example programs
python scripts/check_spec_examples.py                # spec code blocks
python scripts/check_readme_examples.py              # README code blocks
python scripts/check_version_sync.py                 # version consistency
```

## Test Files

| File | Tests | Lines | What it covers |
|------|------:|------:|----------------|
| `test_parser.py` | 105 | 888 | Grammar rules, operator precedence, parse errors |
| `test_ast.py` | 89 | 935 | AST transformation, node structure, serialisation |
| `test_checker.py` | 211 | 2,707 | Type synthesis, slot resolution, effects, effect subtyping, contracts, exhaustiveness, cross-module typing, visibility, error codes, string built-ins, generic rejection |
| `test_verifier.py` | 101 | 1,580 | Z3 verification, counterexamples, tier classification, call-site preconditions, pipe operator, cross-module contracts, match/ADT verification, decreases verification, mutual recursion |
| `test_codegen.py` | 376 | 4,610 | WASM compilation, arithmetic, Float64, Byte, arrays (incl. compound element types), ADTs, match (incl. nested patterns), generics, State\<T\>, Exn\<E\> handlers, control flow, strings, IO, bounds checking, quantifiers, assert/assume, refinement type aliases, pipe operator, string built-ins, built-in shadowing, parse\_nat Result, GC, example round-trips |
| `test_codegen_contracts.py` | 32 | 576 | Runtime pre/postconditions, contract fail messages, old/new state postconditions |
| `test_codegen_monomorphize.py` | 17 | 361 | Generic instantiation, type inference, monomorphization edge cases |
| `test_codegen_closures.py` | 17 | 416 | Closure lifting, captured variables, higher-order functions |
| `test_codegen_modules.py` | 18 | 529 | Cross-module guard rail, cross-module codegen, name collision detection (E608/E609/E610) |
| `test_codegen_coverage.py` | 5 | 249 | Defensive error paths: E600, E601, E605, E606, unknown module calls |
| `test_errors.py` | 34 | 287 | Error code registry, diagnostic formatting, serialisation, SourceLocation |
| `test_formatter.py` | 66 | 554 | Comment extraction, expression/declaration formatting, idempotency, parenthesization, spec rules |
| `test_cli.py` | 109 | 1,401 | CLI commands (check, verify, compile, run, test, fmt), subprocess integration, JSON error paths, runtime traps, arg validation, multi-file resolution |
| `test_resolver.py` | 15 | 412 | Module resolution, path lookup, parse caching, circular import detection |
| `test_types.py` | 73 | 390 | Type operations: subtyping, effect subtyping, equality, substitution, pretty-printing, canonical names |
| `test_wasm.py` | 22 | 255 | WASM internals: StringPool, WasmSlotEnv, translation edge cases via full pipeline |
| `test_wasm_coverage.py` | 113 | 1,738 | WASM coverage gaps: helpers unit tests, inference branches, closure free-var walking, operator/data/context edge cases |
| `test_tester.py` | 13 | 345 | Contract-driven testing: tier classification, input generation, test execution |
| `test_readme.py` | 2 | 78 | README code sample parsing |

## Compiler Code Coverage

Coverage by module, measured by `pytest --cov=vera`:

| Module | Stmts | Miss | Coverage |
|--------|------:|-----:|---------:|
| `codegen/` | 1,349 | 103 | 92% |
| `checker/` | 1,036 | 144 | 86% |
| `wasm/` | 2,575 | 220 | 91% |
| `verifier.py` | 439 | 41 | 91% |
| `transform.py` | 451 | 15 | 97% |
| `formatter.py` | 605 | 70 | 88% |
| `ast.py` | 439 | 25 | 94% |
| `smt.py` | 502 | 54 | 89% |
| `types.py` | 182 | 8 | 96% |
| `errors.py` | 126 | 1 | 99% |
| `environment.py` | 139 | 8 | 94% |
| `cli.py` | 478 | 142 | 70% |
| `parser.py` | 45 | 16 | 64% |
| `resolver.py` | 68 | 2 | 97% |
| `tester.py` | 335 | 50 | 85% |
| `registration.py` | 18 | 0 | 100% |
| **Total** | **8,788** | **899** | **90%** |

The lowest-coverage modules (`parser.py` at 64%, `cli.py` at 70%) reflect auto-generated parser internals and CLI help/flag paths. The `wasm/` subsystem was improved from 79% to 91% by [#156](https://github.com/aallan/vera/issues/156) and subsequent work; the remaining gaps are mostly in `wasm/inference.py` (75%) deep utility branches.

## Contract Verification Coverage

Vera's verifier classifies each contract into one of three tiers. **Tier 1** contracts are proved correct statically by Z3 — no runtime overhead. **Tier 3** contracts cannot be fully decided by the SMT solver and fall back to runtime assertion checks. The verifier never rejects a valid program; it simply warns when a contract drops to Tier 3.

Across all 18 example programs:

| Metric | Value |
|--------|-------|
| **Tier 1 (static)** | 112 contracts — proved automatically by Z3 |
| **Tier 3 (runtime)** | 6 contracts — verified at runtime via assertion checks |
| **Total** | 118 contracts (94.9% static) |

The 6 remaining Tier 3 contracts and why they cannot be promoted:

| Example | Contract | Reason |
|---------|----------|--------|
| gc\_pressure.vera | `decreases` in `repeat` | Termination metric not in decidable fragment |
| generics.vera | `ensures(@T.result == @T.0)` | Generic type parameters have no Z3 sort |
| generics.vera | `ensures(@A.result == @A.0)` | Generic type parameters have no Z3 sort |
| increment.vera | `ensures(new(State<Int>) == old(State<Int>) + 1)` | `old`/`new` state modeling not yet implemented |
| modules.vera | postcondition in `abs_max` | Cross-module call outside decidable fragment |
| modules.vera | postcondition in `qualified_abs` | Cross-module call outside decidable fragment |

The Tier 1 fragment covers: integer/boolean arithmetic, comparisons, if/else, let bindings, match expressions, ADT constructors, function calls (modular postcondition), `length`, and `decreases` clauses (self-recursive, mutual recursion via where-blocks, Nat and structural ADT measures).

## Language Feature Coverage

How Vera language features (by spec chapter) map to test files and example programs:

| Spec chapter | Feature | Test files | Examples |
|-------------|---------|-----------|----------|
| Ch 2: Types | Int, Nat, Bool, String, Float64, Byte, Unit | test_codegen, test_checker | most examples |
| Ch 2: Types | ADTs (algebraic data types), Option, Result | test_codegen, test_checker | pattern_matching, list_ops |
| Ch 2: Types | Refinement types | test_codegen, test_verifier | refinement_types, safe_divide |
| Ch 2: Types | Generics (`forall<T>`) | test_codegen_monomorphize, test_checker | generics |
| Ch 3: Slots | `@T.n` references, De Bruijn indexing | test_checker, test_codegen | all 18 examples |
| Ch 4: Expressions | Arithmetic, comparison, boolean, unary ops | test_codegen, test_checker | factorial, absolute_value |
| Ch 4: Expressions | If/else, let, match, pipe operator | test_codegen, test_checker | pattern_matching |
| Ch 5: Functions | Declarations, recursion, mutual recursion | test_codegen, test_checker | factorial, mutual_recursion |
| Ch 5: Functions | Closures, higher-order functions | test_codegen_closures | closures |
| Ch 5: Functions | Visibility (`public`/`private`) | test_checker | modules |
| Ch 6: Contracts | Preconditions (`requires`) | test_codegen_contracts, test_verifier | safe_divide |
| Ch 6: Contracts | Postconditions (`ensures`) | test_codegen_contracts, test_verifier | absolute_value |
| Ch 6: Contracts | Decreases clauses, assert/assume | test_verifier, test_codegen | factorial |
| Ch 6: Contracts | Quantifiers (forall, exists) | test_codegen, test_verifier | quantifiers |
| Ch 7: Effects | Pure, IO, State\<T\> | test_codegen, test_checker | hello_world, increment, io_operations, file_io |
| Ch 7: Effects | Effect handlers (State\<T\>, Exn\<E\>) | test_codegen, test_checker | effect_handler |
| Ch 7: Effects | Effect subtyping (§7.8), call-site checking | test_types, test_checker | — |
| Ch 2: Types | Bidirectional type checking (local inference) | test_checker | — |
| Ch 4: Expressions | Nested constructor patterns in match | test_codegen | pattern_matching |
| Ch 8: Modules | Imports, cross-module typing and codegen | test_codegen_modules, test_resolver | modules |
| Ch 11: Compilation | Cross-module name collision detection (E608/E609/E610) | test_codegen_modules | — |
| Ch 11: Compilation | Contract-driven testing (Z3 input gen + WASM execution) | test_tester, test_cli | safe_divide, factorial |

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

Every one of the 18 example programs in `examples/` is tested through **every pipeline stage** via parametrised tests: parsing, AST transformation, type checking, contract verification, WASM compilation, and execution. If you add a new `.vera` example, it is automatically included in the round-trip suite.

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

## Validation Scripts

Four scripts in `scripts/` validate cross-cutting concerns beyond unit tests:

| Script | What it validates |
|--------|-------------------|
| `check_examples.py` | All 18 `.vera` examples pass `vera check` + `vera verify` |
| `check_spec_examples.py` | 96 parseable code blocks from spec chapters: parse, type-check, and verify |
| `check_readme_examples.py` | All Vera code blocks in README.md parse correctly |
| `check_version_sync.py` | `pyproject.toml` and `vera/__init__.py` versions match |

These run in both pre-commit hooks and CI, so issues are caught locally before they reach the remote.

### Spec validation pipeline

`check_spec_examples.py` pushes spec code blocks through three compiler stages, with allowlists at each level:

| Stage | Pass | Allowlisted | Categories |
|-------|-----:|------------:|------------|
| **Parse** | 72 | 24 | FUTURE (9), FRAGMENT (15) |
| **Type-check** | 57 | 15 | INCOMPLETE (14), FUTURE (1) |
| **Verify** | 56 | 1 | ILLUSTRATIVE (1) |

Allowlisted entries have stale-detection: when a feature lands or a spec edit shifts line numbers, CI flags the entry for removal. The 14 INCOMPLETE check entries reference functions, types, or imports not defined in the block (e.g. `abs`, `Tuple`, `IO.print`, `array_map`, `parse_int`). The 1 FUTURE check entry uses `async/await`. The 1 ILLUSTRATIVE verify entry is a spec example demonstrating multiple postconditions syntax where the contract is intentionally imprecise.

## Pre-commit Hooks

After running `pre-commit install`, every commit is checked by 11 hooks:

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
| `check_examples.py` | All 18 examples pass `vera check` + `vera verify` |
| `check_readme_examples.py` | README code blocks parse correctly |

The example and README hooks are smart about triggers -- they only run when `.vera` files, `vera/**/*.py`, or `grammar.lark` change.

## CI Pipeline

GitHub Actions ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs three parallel jobs on every push and pull request to `main`:

| Job | Matrix / Runner | What it checks |
|-----|----------------|---------------|
| **test** | Python 3.11, 3.12, 3.13 x Ubuntu, macOS (6 combos) | `pytest -v` passes on all combinations |
| **test** (coverage) | Python 3.12 x Ubuntu only | `pytest --cov=vera --cov-fail-under=80` |
| **typecheck** | Python 3.12 x Ubuntu | `mypy vera/` clean in strict mode |
| **lint** | Python 3.12 x Ubuntu | `check_examples.py`, `check_version_sync.py`, `check_spec_examples.py`, `check_readme_examples.py`, `check_skill_examples.py` |

The coverage threshold of **80%** is enforced in CI. Current coverage is 90%.

## Opportunities

Testing infrastructure that could be added in the future:

- **Property-based testing** -- `hypothesis` is installed as a dev dependency but not yet used. Could generate random programs to test parser robustness and formatter idempotency at scale.
- **Formatter round-trip invariant** -- verify `parse(format(parse(src))) == parse(src)` for all valid programs, not just the examples.
- **WASM inference.py coverage** -- `wasm/inference.py` at 75% has the most remaining gaps, mostly in deep utility branches (`_fn_type_param_wasm_types`, `_type_expr_name` with generics, `_infer_fncall_vera_type`). These branches require very specific expression nesting patterns to reach.
- **Performance benchmarks** -- no benchmark infrastructure exists. Could track compilation time and Z3 verification time across releases.
