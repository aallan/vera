# Testing

This is the single source of truth for Vera's testing infrastructure, coverage data, and test conventions.

## Overview

| Metric | Value |
|--------|-------|
| **Tests** | 1,076 across 17 files (~12,000 lines of test code) |
| **Compiler code coverage** | 87% of 6,446 statements (CI minimum: 80%) |
| **Example programs** | 14, all validated through `vera check` + `vera verify` |
| **Spec code blocks** | 96 parseable blocks from 13 spec chapters: 72 parse, 57 type-check, 56 verify |
| **README code blocks** | 6 Vera blocks (5 validated, 1 allowlisted future syntax) |
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
python scripts/check_examples.py                     # 14 example programs
python scripts/check_spec_examples.py                # spec code blocks
python scripts/check_readme_examples.py              # README code blocks
python scripts/check_version_sync.py                 # version consistency
```

## Test Files

| File | Tests | Lines | What it covers |
|------|------:|------:|----------------|
| `test_parser.py` | 103 | 888 | Grammar rules, operator precedence, parse errors |
| `test_ast.py` | 87 | 935 | AST transformation, node structure, serialisation |
| `test_checker.py` | 159 | 2,143 | Type synthesis, slot resolution, effects, contracts, exhaustiveness, cross-module typing, visibility, error codes |
| `test_verifier.py` | 77 | 1,118 | Z3 verification, counterexamples, tier classification, call-site preconditions, pipe operator, cross-module contracts |
| `test_codegen.py` | 280 | 3,352 | WASM compilation, arithmetic, Float64, Byte, arrays, ADTs, match, generics, State\<T\>, control flow, strings, IO, bounds checking, quantifiers, assert/assume, refinement type aliases, pipe operator, example round-trips |
| `test_codegen_contracts.py` | 32 | 576 | Runtime pre/postconditions, contract fail messages, old/new state postconditions |
| `test_codegen_monomorphize.py` | 17 | 360 | Generic instantiation, type inference, monomorphization edge cases |
| `test_codegen_closures.py` | 17 | 416 | Closure lifting, captured variables, higher-order functions |
| `test_codegen_modules.py` | 11 | 349 | Cross-module guard rail, cross-module codegen |
| `test_codegen_coverage.py` | 5 | 249 | Defensive error paths: E600, E601, E605, E606, unknown module calls |
| `test_errors.py` | 34 | 287 | Error code registry, diagnostic formatting, serialisation, SourceLocation |
| `test_formatter.py` | 62 | 554 | Comment extraction, expression/declaration formatting, idempotency, parenthesization, spec rules |
| `test_cli.py` | 98 | 1,299 | CLI commands (check, verify, compile, run, fmt), subprocess integration, JSON error paths, runtime traps, arg validation, multi-file resolution |
| `test_resolver.py` | 15 | 412 | Module resolution, path lookup, parse caching, circular import detection |
| `test_types.py` | 55 | 279 | Type operations: subtyping, equality, substitution, pretty-printing, canonical names |
| `test_wasm.py` | 22 | 255 | WASM internals: StringPool, WasmSlotEnv, translation edge cases via full pipeline |
| `test_readme.py` | 2 | 68 | README code sample parsing |

## Compiler Code Coverage

Coverage by module, measured by `pytest --cov=vera`:

| Module | Stmts | Miss | Coverage |
|--------|------:|-----:|---------:|
| `codegen/` | 1,154 | 85 | 93% |
| `checker/` | 986 | 137 | 86% |
| `wasm/` | 1,311 | 269 | 79% |
| `verifier.py` | 290 | 21 | 93% |
| `transform.py` | 451 | 15 | 97% |
| `formatter.py` | 605 | 82 | 86% |
| `ast.py` | 439 | 25 | 94% |
| `smt.py` | 283 | 47 | 83% |
| `types.py` | 146 | 3 | 98% |
| `errors.py` | 126 | 1 | 99% |
| `environment.py` | 125 | 9 | 93% |
| `cli.py` | 398 | 111 | 72% |
| `parser.py` | 45 | 16 | 64% |
| `resolver.py` | 68 | 2 | 97% |
| `registration.py` | 18 | 0 | 100% |
| **Total** | **6,446** | **823** | **87%** |

The lowest-coverage modules (`parser.py` at 64%, `cli.py` at 72%) reflect auto-generated parser internals and CLI help/flag paths. The `wasm/` subsystem at 79% has the most room for improvement, particularly `wasm/inference.py` (71%) and `wasm/helpers.py` (62%).

## Language Feature Coverage

How Vera language features (by spec chapter) map to test files and example programs:

| Spec chapter | Feature | Test files | Examples |
|-------------|---------|-----------|----------|
| Ch 2: Types | Int, Nat, Bool, String, Float64, Byte, Unit | test_codegen, test_checker | most examples |
| Ch 2: Types | ADTs (algebraic data types), Option, Result | test_codegen, test_checker | pattern_matching, list_ops |
| Ch 2: Types | Refinement types | test_codegen, test_verifier | refinement_types, safe_divide |
| Ch 2: Types | Generics (`forall<T>`) | test_codegen_monomorphize, test_checker | generics |
| Ch 3: Slots | `@T.n` references, De Bruijn indexing | test_checker, test_codegen | all 14 examples |
| Ch 4: Expressions | Arithmetic, comparison, boolean, unary ops | test_codegen, test_checker | factorial, absolute_value |
| Ch 4: Expressions | If/else, let, match, pipe operator | test_codegen, test_checker | pattern_matching |
| Ch 5: Functions | Declarations, recursion, mutual recursion | test_codegen, test_checker | factorial, mutual_recursion |
| Ch 5: Functions | Closures, higher-order functions | test_codegen_closures | closures |
| Ch 5: Functions | Visibility (`public`/`private`) | test_checker | modules |
| Ch 6: Contracts | Preconditions (`requires`) | test_codegen_contracts, test_verifier | safe_divide |
| Ch 6: Contracts | Postconditions (`ensures`) | test_codegen_contracts, test_verifier | absolute_value |
| Ch 6: Contracts | Decreases clauses, assert/assume | test_verifier, test_codegen | factorial |
| Ch 6: Contracts | Quantifiers (forall, exists) | test_codegen, test_verifier | quantifiers |
| Ch 7: Effects | Pure, IO, State\<T\> | test_codegen, test_checker | hello_world, increment |
| Ch 7: Effects | Effect handlers (handle/resume) | test_codegen, test_checker | effect_handler |
| Ch 8: Modules | Imports, cross-module typing and codegen | test_codegen_modules, test_resolver | modules |

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

Every one of the 14 example programs in `examples/` is tested through **every pipeline stage** via parametrised tests: parsing, AST transformation, type checking, contract verification, WASM compilation, and execution. If you add a new `.vera` example, it is automatically included in the round-trip suite.

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

## Validation Scripts

Four scripts in `scripts/` validate cross-cutting concerns beyond unit tests:

| Script | What it validates |
|--------|-------------------|
| `check_examples.py` | All 14 `.vera` examples pass `vera check` + `vera verify` |
| `check_spec_examples.py` | 96 parseable code blocks from spec chapters: parse, type-check, and verify |
| `check_readme_examples.py` | All Vera code blocks in README.md parse correctly |
| `check_version_sync.py` | `pyproject.toml` and `vera/__init__.py` versions match |

These run in both pre-commit hooks and CI, so issues are caught locally before they reach the remote.

### Spec validation pipeline

`check_spec_examples.py` pushes spec code blocks through three compiler stages, with allowlists at each level:

| Stage | Pass | Allowlisted | Categories |
|-------|-----:|------------:|------------|
| **Parse** | 72 | 24 | FUTURE (9), FRAGMENT (15) |
| **Type-check** | 57 | 15 | INCOMPLETE (13), FUTURE (2) |
| **Verify** | 56 | 1 | ILLUSTRATIVE (1) |

Allowlisted entries have stale-detection: when a feature lands or a spec edit shifts line numbers, CI flags the entry for removal. The 13 INCOMPLETE check entries reference functions, types, or imports not defined in the block (e.g. `abs`, `Tuple`, `IO.print`, `array_map`). The 2 FUTURE check entries use `Exn` exception handling and `async/await`. The 1 ILLUSTRATIVE verify entry is a spec example demonstrating multiple postconditions syntax where the contract is intentionally imprecise.

## Pre-commit Hooks

After running `pre-commit install`, every commit is checked by 10 hooks:

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
| `check_examples.py` | All 14 examples pass `vera check` + `vera verify` |
| `check_readme_examples.py` | README code blocks parse correctly |

The example and README hooks are smart about triggers -- they only run when `.vera` files, `vera/**/*.py`, or `grammar.lark` change.

## CI Pipeline

GitHub Actions ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs three parallel jobs on every push and pull request to `main`:

| Job | Matrix / Runner | What it checks |
|-----|----------------|---------------|
| **test** | Python 3.11, 3.12, 3.13 x Ubuntu, macOS (6 combos) | `pytest -v` passes on all combinations |
| **test** (coverage) | Python 3.12 x Ubuntu only | `pytest --cov=vera --cov-fail-under=80` |
| **typecheck** | Python 3.12 x Ubuntu | `mypy vera/` clean in strict mode |
| **lint** | Python 3.12 x Ubuntu | `check_examples.py`, `check_version_sync.py`, `check_spec_examples.py`, `check_readme_examples.py` |

The coverage threshold of **80%** is enforced in CI. Current coverage is 87%.

## Opportunities

Testing infrastructure that could be added in the future:

- **Property-based testing** -- `hypothesis` is installed as a dev dependency but not yet used. Could generate random programs to test parser robustness and formatter idempotency at scale.
- **Formatter round-trip invariant** -- verify `parse(format(parse(src))) == parse(src)` for all valid programs, not just the examples.
- **WASM coverage improvement** -- `wasm/` is the lowest-coverage subsystem at 79%. `wasm/inference.py` (71%) and `wasm/helpers.py` (62%) have the most gaps. See [#156](https://github.com/aallan/vera/issues/156).
- **Performance benchmarks** -- no benchmark infrastructure exists. Could track compilation time and Z3 verification time across releases.
