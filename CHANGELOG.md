# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

## [0.0.21] - 2026-02-26

### Added
- **Byte type compilation** (C6k): `Byte` maps to `i32` in WASM with unsigned comparison operators (`i32.lt_u`, `i32.gt_u`, `i32.le_u`, `i32.ge_u`); `i32.wrap_i64` coercion for Byte-returning functions with integer literal bodies
- **Array compilation** (C6k — closes [#30](https://github.com/aallan/vera/issues/30)): compile `Array<T>` literals, indexing, and `length()` to WASM via linear memory
  - Array representation: `(ptr: i32, len: i32)` pairs, allocated via bump allocator
  - Element types: `Byte` (1 byte, `i32.load8_u`/`i32.store8`), `Bool` (4 bytes), `Int`/`Nat` (8 bytes, `i64`), `Float64` (8 bytes, `f64`)
  - Bounds checking: `i32.ge_u` unsigned comparison + `unreachable` trap on out-of-bounds
  - `length()` built-in: extracts len from `(ptr, len)` pair, extends to `i64`
  - Array let bindings: two WASM locals (ptr at N, len at N+1)
  - Array slot refs: emit two `local.get` ops for `(ptr, len)` pair
  - Array function params/returns unsupported (skipped with warning, same as String)
- **Spec Section 11.12**: new "Array Compilation" section covering representation, allocation, indexing, bounds checking, length, let bindings, and scope
- **Codegen tests**: 26 new tests — Byte identity/zero/max/let/comparisons, array literals/indexing/bounds-check/length, WAT inspection (821 total, up from 795)

## [0.0.20] - 2026-02-25

### Fixed
- **Spec @T notation mismatch**: fixed 30 code blocks across 5 spec files where `@T` was used in data constructor fields and effect operation signatures (value-level `@` is for binding sites only); 16 blocks now parse, 14 recategorized as fragments for unrelated syntax reasons (empty effects, handler `with` clauses, inline function types)
- **Stale README limitation rows**: removed "No closure codegen" and "No effect handler codegen" rows (closed in v0.0.18 and v0.0.19 respectively)
- **Spec limitation issue tracking**: created GitHub issues [#50](https://github.com/aallan/vera/issues/50)–[#53](https://github.com/aallan/vera/issues/53) for all unlinked limitations in spec Chapter 11; updated spec and README tables

### Added
- **Test coverage**: 104 new tests across 4 modules (795 total, up from 691)
  - `tests/test_types.py` (new): 55 tests for `is_subtype`, `types_equal`, `substitute`, `pretty_type`, `canonical_type_name`, `base_type`
  - `tests/test_wasm.py` (new): 22 tests for `StringPool`, `WasmSlotEnv`, and translation edge cases via full compilation pipeline
  - `tests/test_errors.py`: 18 new tests for `SourceLocation`, `Diagnostic.to_dict`, `diagnose_lark_error`, `unclosed_block`, `unexpected_token`, `VeraError`
  - `tests/test_cli.py`: 10 new tests for compile/run/verify error paths in both text and JSON modes

### Changed
- **Spec allowlist**: removed all 30 MISMATCH entries from `check_spec_examples.py`; added 14 FRAGMENT entries for genuine syntax fragments; parsed blocks increased from 21 to 37

## [0.0.19] - 2026-02-25

### Added
- **Effect handler compilation** (C6j — closes [#28](https://github.com/aallan/vera/issues/28)): compile `handle[State<T>]` expressions to WASM via host imports
  - State handler translation: `handle[State<T>](@T = init) { get/put clauses } in { body }` compiles by initializing state via `state_put_T`, then compiling body with get/put mapped to host imports
  - Handler clauses serve as specifications (not compiled) — `resume()` calls describe the default State semantics, validated by type checker
  - Effect discharge: pure functions containing `handle[State<T>]` are compilable — state imports registered by scanning function body for handle expressions
  - Unsupported handlers (`Exn<E>`, custom effects) cause function to be skipped with warning
- **Reworked `examples/effect_handler.vera`**: removed `safe_parse` (uses String + undefined `parse_int`), added `test_state_init` and `test_put_get` (simple compilable tests)
- **Codegen tests**: 14 new tests — state initialization, put/get, increment pattern, run_counter, let bindings, Bool state, WAT inspection, unsupported handler skip, example file round-trips (691 total, up from 677)

## [0.0.18] - 2026-02-25

### Added
- **Closure compilation** (C6h — closes [#27](https://github.com/aallan/vera/issues/27)): compile anonymous functions and closures to WASM via function tables and `call_indirect`
  - Closure representation: heap-allocated struct `[func_table_idx: i32, capture_0, ...]` as `i32` pointer, using existing bump allocator
  - Function table infrastructure: `(type $closure_sig_N ...)`, `(table N funcref)`, `(elem ...)` for indirect calls
  - Closure lifting: anonymous functions compiled as module-level WASM functions with `$env` parameter for captured variables
  - Free variable capture: walk `AnonFn` body to detect `SlotRef` nodes referencing outer-scope bindings, store captured values in heap environment
  - `apply_fn` built-in: compiler-recognized function that emits `call_indirect` with closure's `func_table_idx`
  - Function type aliases (e.g. `type IntToInt = fn(Int -> Int) effects(pure)`) resolved to `i32` closure pointers
  - Functions with function-type parameters no longer skipped (recognized as compilable)
- **Reworked `examples/closures.vera`**: removed `Array<Int>`, undefined `map`, and `forall<T>` generic `map_option`; added `make_adder` (closure capture), `apply` (closure parameter), `map_option` (closure in match arm), `test_closure` and `test_map_option` (end-to-end round-trips)
- **Codegen tests**: 17 new tests — closure creation with/without capture, `apply_fn`, closures in let bindings and match arms, function-type parameters, WAT structure verification, example file round-trips (677 total, up from 660)

## [0.0.17] - 2026-02-24 ([#42](https://github.com/aallan/vera/pull/42))

### Added
- **Generics monomorphization** (C6i — closes [#29](https://github.com/aallan/vera/issues/29)): compile `forall<T>` functions to WASM via monomorphization
  - Collection pass: walk non-generic function bodies to find calls to generic functions, infer concrete type variable bindings
  - AST substitution: create monomorphized FnDecl copies with type variables replaced by concrete types (e.g. `@T.0` → `@Int.0`)
  - Name mangling: `identity` + `(Int,)` → `identity$Int`, `const` + `(Int, Bool)` → `const$Int_Bool`
  - Call rewriting: generic function calls resolve to mangled names at WASM translation time
  - FnCall type inference: infer WASM return types and Vera type names for function call expressions (improves if-branch and chained-call handling)
  - Supports: literal args, slot ref args, constructor args, chained generic calls, arithmetic expression args
- **Codegen tests**: 17 new tests — identity/const/is_some instantiation, two-instantiation exports, ADT match, chained calls, if-branches, let bindings, example files (660 total, up from 643)

## [0.0.16] - 2026-02-24 ([#41](https://github.com/aallan/vera/pull/41))

### Added
- **Match expression codegen** (C6g — closes [#26](https://github.com/aallan/vera/issues/26)): compile `MatchExpr` AST nodes to WASM chained if-else cascades
  - ADT tag dispatch: load tag from heap pointer, compare with constructor tag, branch
  - Field extraction: load constructor fields at computed offsets into locals, bind in environment
  - Monomorphized offsets: field offsets computed from concrete binding types (same approach as C6f constructor calls)
  - Pattern types: `ConstructorPattern`, `NullaryPattern`, `WildcardPattern`, `BindingPattern`, `BoolPattern`, `IntPattern`
  - Recursive if-else cascade: each arm generates a condition check and branches, last arm emits directly
  - Environment scoping: each arm gets fresh bindings from pattern extraction, no cross-arm leakage
- **Codegen tests**: 20 new tests — ADT tag dispatch, field extraction, wildcard catch-alls, Bool/Int literal patterns, binding patterns, composability (643 total, up from 623)

## [0.0.15] - 2026-02-24 ([#40](https://github.com/aallan/vera/pull/40))

### Added
- **ADT constructor codegen** (C6f): compile `ConstructorCall` and `NullaryConstructor` AST nodes to WASM heap-allocated tagged unions
  - Nullary constructors (e.g. `Red`, `None`): alloc → store tag → return pointer
  - Constructors with fields (e.g. `Some(42)`, `Wrap(@Int.0)`): alloc → store tag → store each field at computed offset → return pointer
  - Field offsets computed from concrete argument types at translation time — handles monomorphized generic constructors (e.g. `Some(T)` with `T=Int` stores i64)
  - ADT types compile to `i32` (heap pointer) in function signatures, slot references, and type inference
  - `WasmContext` accepts `ctor_layouts` and `adt_type_names` for constructor-aware translation
  - Functions using ADT constructors now compile (no longer skipped with warning)
- **Codegen tests**: 12 new tests — nullary/tagged constructors, Int/Bool fields, Option None/Some, WAT inspection, let bindings, if-then-else branches, ADT parameters (623 total, up from 611)

## [0.0.14] - 2026-02-24 ([#39](https://github.com/aallan/vera/pull/39))

### Added
- **Bump allocator infrastructure** (C6e): heap allocation support for upcoming ADT constructor codegen
  - `$heap_ptr` mutable global: initialized to first byte after string data, exported as `"heap_ptr"`
  - `$alloc` internal function: bump-allocates with 8-byte alignment, returns pointer to allocated block
  - ADT layout metadata: `ConstructorLayout` dataclass stores tag, field offsets, and total size per constructor
  - Layout computed eagerly during registration pass — available for C6f (constructor codegen) and C6g (match codegen)
  - Allocator and heap global emitted only when user-declared ADTs are present (no overhead for pure programs)
  - `StringPool.heap_offset` property exposes first free byte after string constants
- **Codegen tests**: 26 new tests — layout helpers, WAT output inspection, ADT metadata registration, conditional emission (611 total, up from 585)

## [0.0.13] - 2026-02-24 ([#38](https://github.com/aallan/vera/pull/38))

### Added
- **State\<T\> WASM host imports** (C6d): compile `get`/`put` operations for `State<T>` effects as WASM host imports
  - `State<Int>`, `State<Nat>`, `State<Bool>`, `State<Float64>` compile to typed host import pairs
  - `get(())` → `call $vera.state_get_{T}` (returns typed value); `put(x)` → `call $vera.state_put_{T}` (consumes typed value)
  - Host runtime maintains mutable state cells per type, initialized to zero
  - `execute()` accepts optional `initial_state` parameter and returns final `state` in `ExecuteResult`
  - Mixed effects supported: `effects(<State<Int>, IO>)` compiles correctly
  - `effect_ops` dict mechanism in `WasmContext` redirects bare `get`/`put` calls to host imports
  - `_is_void_expr` recognizes `put()` as void (no `drop` emitted in ExprStmt)
- **Codegen tests**: 15 new tests — get default, put-then-get, increment pattern, example file, Bool/Float64/Nat state, String rejection, mixed effects, WAT imports, multiple types, void semantics, initial state override, pure function purity (585 total, up from 570)
- `examples/increment.vera` now compiles and runs (7 of 14 examples compilable)

## [0.0.12] - 2026-02-24 ([#37](https://github.com/aallan/vera/pull/37))

### Added
- **Match exhaustiveness checking** (C6c — closes [#18](https://github.com/aallan/vera/issues/18)): compile-time verification that match expressions cover all possible values
  - ADT exhaustiveness: all constructors must be covered or a catch-all pattern must be present
  - Bool exhaustiveness: both `true` and `false` must be covered or a catch-all present
  - Infinite type exhaustiveness: `Int`, `String`, `Float64`, `Nat` matches require a wildcard `_` or binding pattern
  - Unreachable arm warnings: arms after a wildcard or binding catch-all produce warnings (Spec Section 4.9.3)
  - Refinement types properly stripped via `base_type()` before analysis
  - Error diagnostics include missing constructor/value names and fix suggestions
- **Type checker tests**: 17 new tests — ADT exhaustive/missing/wildcard/binding, Bool exhaustive/missing/wildcard, Int/String without wildcard, unreachable arms (single/multiple/after binding), wildcard only, refined type stripping (570 total, up from 553)

## [0.0.11] - 2026-02-24 ([#36](https://github.com/aallan/vera/pull/36))

### Added
- **Callee precondition verification** (C6b — closes [#19](https://github.com/aallan/vera/issues/19)): modular call-site contract checking
  - When function `f` calls function `g`, the verifier now checks that `g`'s `requires()` clauses hold at the call site given `f`'s assumptions
  - Callee postconditions (`ensures()`) are assumed at the call site, enabling symbolic reasoning about return values
  - Fresh Z3 variables created per call, with postconditions asserted — supports chained calls, let bindings, and recursive calls
  - Recursive functions (e.g., `factorial`) now verify `ensures()` at Tier 1 instead of falling to Tier 3
  - `CallViolation` dataclass in `smt.py` records call-site violations with callee name, precondition, and counterexample
  - `_report_call_violation()` in verifier produces LLM-oriented diagnostics with fix suggestions
  - `param_type_exprs` field added to `FunctionInfo` for callee parameter slot resolution
- **Verifier tests**: 13 new tests — satisfied/violated/forwarded preconditions, assumed postconditions, recursive calls, trivial preconditions, let bindings, where-block calls, generic call fallback, multiple preconditions, sequential calls, error message quality (553 total, up from 540)

### Changed
- Tier 3 warning rationale updated: "recursive calls" replaced with "generic calls" (recursive calls now handled via modular verification)
- `SmtContext` constructor accepts optional `fn_lookup` callback for callee contract resolution
- Caller precondition assumptions now asserted into the Z3 solver before body translation

## [0.0.10] - 2026-02-24 ([#35](https://github.com/aallan/vera/pull/35))

### Added
- **Float64 WASM codegen** (C6a — closes [#25](https://github.com/aallan/vera/issues/25)): compile Float64/Float values to WebAssembly `f64` instructions
  - Type mapping: Float64/Float → `f64` in `wasm_type()`, `_type_expr_to_wasm_type()`, `_slot_name_to_wasm_type()`, `_infer_expr_wasm_type()`, `_infer_block_result_type()`
  - `FloatLit` emission: `f64.const` literals
  - Float64 arithmetic: `f64.add`, `f64.sub`, `f64.mul`, `f64.div` (MOD unsupported — WASM has no `f64.rem`)
  - Float64 comparisons: `f64.eq`, `f64.ne`, `f64.lt`, `f64.gt`, `f64.le`, `f64.ge` (result is `i32`)
  - Float64 negation: `f64.neg`
  - Float64 slot references, let bindings, if/else branches, function parameters and returns all compile
  - `ExecuteResult.value` widened to `int | float | None`; `execute()` accepts `list[int | float]` args
- **Codegen tests**: 26 new tests — Float64 literals, slot references, arithmetic, comparisons, negation, if/else, let bindings, WAT output validation (540 total, up from 514)

### Changed
- `execute()` signature updated: `args` parameter accepts `list[int | float]` for Float64 arguments
- Warning messages updated to mention Float64 as a compilable type
- CLI `fn_args` type widened to `list[int | float]` for future float argument parsing

## [0.0.9] - 2026-02-23 ([#31](https://github.com/aallan/vera/pull/31))

### Added
- **WASM code generation** (`vera/codegen.py`, `vera/wasm.py`): compile verified Vera programs to WebAssembly and execute them via wasmtime — **first light** 🌅
  - Two-pass code generator: register functions (forward references, mutual recursion), then compile bodies
  - Expression compilation: integer/Boolean literals, arithmetic, comparisons, Boolean logic, if/else, let bindings, blocks, function calls, recursion, string literals, IO operations
  - `WasmSlotEnv` — maps De Bruijn slot references (`@T.n`) to WASM local indices (mirrors `SlotEnv` in `smt.py`)
  - `WasmContext` — manages local allocation, data section, imports, accumulates WAT instructions
  - `StringPool` — deduplicated string constants in the WASM data section
  - Type mapping: Int/Nat → i64, Bool → i32, Unit → void, String → (i32 ptr, i32 len) pair
  - IO effect as host imports: `IO.print` compiles to imported host function, host reads UTF-8 from linear memory
  - Where-block functions compiled as module-level WASM functions
  - Graceful degradation: functions with unsupported types/constructs are skipped with a warning
- **Runtime contract insertion**: Tier 3 (unverified) contracts compiled as runtime assertions
  - Preconditions checked at function entry, trap on violation via `unreachable`
  - Postconditions checked after body with result stored in temp local
  - Trivial contracts (`requires(true)`, `ensures(true)`) eliminated — no runtime overhead
  - Tier 1 (proven) contracts omitted — statically guaranteed
- **CLI commands**: `vera compile` and `vera run`
  - `vera compile <file>` — full pipeline, writes `.wasm` binary; `--wat` prints human-readable WAT; `--json` for diagnostics; `-o` for output path
  - `vera run <file>` — compile and execute; `--fn` to call specific function; `--` to pass arguments; `--json` for structured output
- **Spec Chapter 11** (`spec/11-compilation.md`): compilation model documentation — type mapping, expression compilation, string pool, IO host bindings, runtime contracts, CLI commands, limitations
- **Hello World example** (`examples/hello_world.vera`): IO effect with qualified `IO.print` call (14 examples total)
- **README code sample testing** (`scripts/check_readme_examples.py`, `tests/test_readme.py`): extracts Vera code blocks from README.md and verifies they parse; pre-commit hook added
- **Codegen tests**: 76 new tests — literals, arithmetic, comparisons, Boolean logic, control flow, let bindings, function calls, recursion, strings, IO, runtime contracts, CLI commands, subprocess integration (470 total, up from 372)

### Changed
- README: updated status table (WASM codegen: Working), advanced roadmap (C5 Done, What's next → C6), added `vera compile`/`vera run` docs, updated project structure with `wasm.py`, `codegen.py`, `spec/11-compilation.md`
- SKILLS.md: added `vera compile` and `vera run` to toolchain section, added Chapter 11 to spec reference table
- CLAUDE.md: added compile/run commands, updated pipeline, updated example/test counts
- AGENTS.md: added compile/run commands, updated pipeline, added `wasm.py` and `codegen.py` to module table, updated test counts
- vera/README.md: updated pipeline diagram (6 stages), added codegen/wasm to module map, updated line counts, added codegen section, updated test suite table, updated limitations

### Fixed
- Documentation consistency: all `print(...)` calls in README.md, spec/05-functions.md, spec/07-effects.md, and SKILLS.md corrected to use qualified `IO.print(...)` syntax (matching the language's "one canonical form" design principle)

## [0.0.8] - 2026-02-23 ([#10](https://github.com/aallan/vera/pull/10))

### Added
- **Contract verifier** (`vera/verifier.py`): Z3-backed verification of `requires`/`ensures` contracts on functions
  - Three-tier verification: Tier 1 (decidable, Z3 proves automatically), Tier 3 (runtime fallback with warning)
  - Forward symbolic execution — translates function body to Z3 expression, checks postconditions directly
  - Counterexample generation — when verification fails, shows concrete input values that break the contract
  - Trivial contract fast path — `requires(true)`/`ensures(true)` counted as verified without invoking Z3
  - Graceful Tier 3 fallback for unsupported constructs (match, effects, recursion, quantifiers)
  - LLM-oriented diagnostics with counterexample values, rationale, and spec references
- **SMT translation layer** (`vera/smt.py`): bridges Vera AST expressions to Z3 formulas
  - `SlotEnv` — De Bruijn slot stacks mapped to Z3 variables
  - Expression translation: integer/Boolean literals, arithmetic, comparisons, Boolean logic, if/else, let bindings, `length()` (uninterpreted function)
  - `SmtContext.check_valid()` — refutation-based validity checking with counterexample extraction
- **CLI command**: `vera verify <file>` — type-check and verify contracts, prints verification summary
- **Convenience API**: `verify_file(path)` in `vera/parser.py`
- **Verifier tests**: 51 new tests — round-trip verification of all 13 examples, trivial contracts, ensures verification, if/else bodies, let bindings, multiple contracts, counterexample extraction, tier classification, arithmetic, summary counts, edge cases (335 total, up from 284)

### Changed
- `FunctionInfo` in `vera/environment.py` now stores contract AST nodes (for modular verification)
- `_register_fn` in `vera/checker.py` passes contracts to `FunctionInfo`
- README: updated status table (Contract verifier: Working), added `vera verify` docs, updated project structure and test count, advanced roadmap (C4 Done, What's next → C5)
- SKILLS.md: added `vera verify` to toolchain section
- LICENSE converted to Markdown format

## [0.0.7] - 2026-02-23

### Added
- **Spec code block validator** (`scripts/check_spec_examples.py`) — extracts 154 code blocks from spec Markdown, classifies them as parseable/fragment/non-Vera, and verifies parseable blocks still parse with the current grammar. Categorised allowlist tracks 30 spec/parser mismatches (spec uses `@T` in data/effect declarations, parser expects bare `T`), 4 future-syntax design proposals, and 3 fragment overrides. Stale allowlist detection catches when spec edits shift line numbers.
- **Version sync check** (`scripts/check_version_sync.py`) — verifies `pyproject.toml` and `vera/__init__.py` agree on version number
- **Dependabot** (`.github/dependabot.yml`) — weekly automated PRs for pip and GitHub Actions dependency updates
- **CODEOWNERS** (`.github/CODEOWNERS`) — automatic review requests on PRs
- **CodeQL** (`.github/workflows/codeql.yml`) — security scanning on PRs and weekly schedule
- **macOS CI** — test matrix expanded from 3 jobs (ubuntu × 3 Python) to 6 jobs (ubuntu + macOS × 3 Python)
- **README narratives** — sub-headings and explanations for each code example in "What Vera Looks Like": Hello World (effects/contracts), absolute_value (postconditions/SMT verification), safe_divide (preconditions/compile-time guarantees), increment (algebraic effects/explicit state)

### Changed
- **CONTRIBUTING.md** — added pre-commit setup instructions, validation script documentation, branch protection rules
- **CI lint job** — now runs version sync check and spec code block validator alongside example validation

## [0.0.6] - 2026-02-23

### Added
- **Hello World example** in README — first example in "What Vera Looks Like" section, demonstrates IO effect and mandatory contracts
- **Spec design notes** in Chapter 0.8 (Section 0.8):
  - **Abilities**: Roc-style restricted type constraints — auto-derivable built-in set (`Eq`, `Ord`, `Hash`, `Encode`, `Decode`, `Show`), no higher-kinded types, `forall<T where Ability<T>>` syntax
  - **LLM Inference effect**: `<Inference>` as an algebraic effect for AI runtime calls — testable via mock handlers, explicit in type signatures, contracts still apply
  - **Standard library collections**: `Set<T>`, `Map<K, V>` (depend on abilities), `Decimal` (software implementation for WASM)

## [0.0.5] - 2026-02-23 ([#2](https://github.com/aallan/vera/pull/2))

### Added
- **Type checker**: Tier 1 decidable type checking — validates expression types, slot reference resolution, effect annotations, and contract well-formedness
  - Two-pass architecture: pass 1 registers all declarations (handles forward references and mutual recursion), pass 2 checks bodies
  - Expression type synthesis for all AST node types (literals, operators, calls, constructors, match/if, handlers, anonymous functions, quantifiers)
  - De Bruijn slot reference resolution with alias opacity
  - Function call type checking with generic type argument inference
  - ADT constructor validation and pattern type checking
  - Basic effect checking (pure functions can't call effectful operations)
  - Handler effect discharge (handlers eliminate their effect from the enclosing function's requirements)
  - Contract well-formedness (predicates must be Bool, `@T.result` only in ensures, `old`/`new` only in ensures)
  - Error accumulation — all type errors collected, never stops at first error
  - Unresolved name graceful handling (warning, not failure) with `UnknownType` propagation
  - LLM-oriented `TypeError` diagnostics with description, location, rationale, fix, and spec reference
- **Internal type representation** (`vera/types.py`): semantic `Type` objects separate from syntactic AST `TypeExpr` nodes — `PrimitiveType`, `AdtType`, `FunctionType`, `RefinedType`, `TypeVar`, `UnknownType`, effect row types
- **Type environment** (`vera/environment.py`): scope stack, slot resolution, built-in type/effect/function registrations (Option, Result, State with get/put, IO, length)
- **CLI command**: `vera typecheck <file>` as explicit alias for `vera check`
- **Convenience API**: `typecheck_file(path)` in `vera/parser.py`
- **Type checker tests**: 91 new tests — round-trip tests for all 13 examples, literal types, slot references, operators, function calls, generics, constructors, patterns, control flow, effects, contracts, higher-order functions, refinement types, error accumulation, where blocks, arrays, return types (284 total, up from 193)

### Changed
- `vera check` now runs the full pipeline: parse → AST → type check (previously parse only)
- README: updated status table (Type checker: Working), added type checker to project structure, documented `vera typecheck` alias
- SKILLS.md: added `vera typecheck` to toolchain section

## [0.0.4] - 2026-02-23 ([#1](https://github.com/aallan/vera/pull/1))

### Added
- **Typed AST layer**: frozen dataclass nodes with source spans, covering all grammar constructs (~50 node classes)
- **Lark→AST transformer**: bottom-up `Transformer` with ~86 methods converting parse trees to typed AST nodes
- **CLI command**: `vera ast <file>` prints indented text AST, `vera ast --json <file>` prints JSON
- **Convenience API**: `parse_to_ast(source, file)` in `vera/parser.py`
- **AST tests**: 83 new tests — round-trip tests for all 13 examples, node-specific tests for every construct, span tests, serialisation tests (193 total, up from 110)
- **TransformError**: new error class for AST transformation failures, subclass of `VeraError`

### Changed
- README: added AST to project status table, `vera ast` CLI docs, updated project structure
- SKILLS.md: added `vera ast` and `vera ast --json` to toolchain section

## [0.0.3] - 2026-02-23

### Added
- **Parser tests**: 40 new tests covering annotation comments, anonymous functions, generics, refinement types, tuple destructuring, quantifiers, assert/assume, qualified calls, function types, float literals, nested patterns, handler variations, and implies operator (110 total, up from 70)
- **Example programs**: 8 new examples — closures, generics, refinement types, effect handlers, modules, quantifiers, pattern matching, mutual recursion (13 total, up from 5)
- **Design notes**: network access as an effect (`<Http>`), JSON as a stdlib ADT, async promises/futures as an effect (`<Async>`) documented in spec Chapter 0

### Fixed
- Grammar: annotation comments (`/* ... */`) now correctly ignored by the parser
- Grammar: `vera/__init__.py` version was `0.1.0`, corrected to match pyproject.toml
- Spec Chapter 3: removed deliberation marker about `@Fn0` approach, kept settled type alias approach
- Spec Chapter 6: rewrote counterexample reporting section (removed incorrect example, added actionable fix suggestions)
- Spec Chapter 7: cleaned up effect-contract interaction section (removed problematic `get()` in contract example, kept settled `old()`/`new()` syntax)

## [0.0.2] - 2026-02-23

### Added
- **CI**: GitHub Actions workflow running pytest on Python 3.11/3.12/3.13 with coverage on 3.12
- **Social preview**: meerkat sentinel mascot using Negroni brand colour palette
- **Custom domain**: veralang.dev with GitHub Pages and HTTPS

### Changed
- CONTRIBUTING.md: point "Questions?" section at Issues instead of Discussions
- Issue template config: remove Discussions contact link (Discussions disabled)
- README: add social preview banner image linking to veralang.dev
- pyproject.toml: update Homepage/Documentation URLs to veralang.dev

## [0.0.1] - 2026-02-23

### Added
- **Parser**: Lark LALR(1) parser that validates `.vera` source files
  - `vera check <file>` — parse and report errors
  - `vera parse <file>` — print the parse tree
- **LLM-oriented diagnostics**: error messages are natural language instructions explaining what went wrong, why, how to fix it with a code example, and a spec reference
- **SKILLS.md**: complete language reference for LLM agents, following the agent skills format
- **Example programs**: `absolute_value.vera`, `safe_divide.vera`, `increment.vera`, `factorial.vera`, `list_ops.vera`
- **Test suite**: 70 tests (54 parser, 16 error diagnostics)
- **Language specification** chapters 0-7 and 10 (draft)
  - Chapter 0: Introduction, philosophy, and diagnostics-as-instructions
  - Chapter 1: Lexical structure
  - Chapter 2: Type system with refinement types
  - Chapter 3: Slot reference system (`@T.n` typed De Bruijn indices)
  - Chapter 4: Expressions and statements
  - Chapter 5: Function declarations
  - Chapter 6: Contract system (preconditions, postconditions, verification tiers)
  - Chapter 7: Algebraic effect system
  - Chapter 10: Formal EBNF grammar (LALR(1) compatible)
- Project structure with `spec/`, `vera/`, `runtime/`, `tests/`, `examples/`
- Python project configuration (`pyproject.toml`)
- Repository documentation (README, LICENSE, CONTRIBUTING, CODE_OF_CONDUCT, CHANGELOG)
- GitHub issue and pull request templates

### Fixed
- Grammar: operator precedence chain (pipe/implies ordering)
- Grammar: `old()`/`new()` accept parameterised types (`State<Int>`)
- Grammar: function signatures use `@Type` prefix to declare binding sites
- Grammar: handler body simplified to avoid LALR reduce/reduce conflict
- `pyproject.toml`: corrected build backend, package discovery, PEP 639 compliance

[Unreleased]: https://github.com/aallan/vera/compare/v0.0.20...HEAD
[0.0.20]: https://github.com/aallan/vera/compare/v0.0.19...v0.0.20
[0.0.19]: https://github.com/aallan/vera/compare/v0.0.18...v0.0.19
[0.0.18]: https://github.com/aallan/vera/compare/v0.0.17...v0.0.18
[0.0.17]: https://github.com/aallan/vera/compare/v0.0.16...v0.0.17
[0.0.16]: https://github.com/aallan/vera/compare/v0.0.15...v0.0.16
[0.0.15]: https://github.com/aallan/vera/compare/v0.0.14...v0.0.15
[0.0.14]: https://github.com/aallan/vera/compare/v0.0.13...v0.0.14
[0.0.13]: https://github.com/aallan/vera/compare/v0.0.12...v0.0.13
[0.0.12]: https://github.com/aallan/vera/compare/v0.0.11...v0.0.12
[0.0.11]: https://github.com/aallan/vera/compare/v0.0.10...v0.0.11
[0.0.10]: https://github.com/aallan/vera/compare/v0.0.9...v0.0.10
[0.0.9]: https://github.com/aallan/vera/compare/v0.0.8...v0.0.9
[0.0.8]: https://github.com/aallan/vera/compare/v0.0.7...v0.0.8
[0.0.7]: https://github.com/aallan/vera/compare/v0.0.6...v0.0.7
[0.0.6]: https://github.com/aallan/vera/compare/v0.0.5...v0.0.6
[0.0.5]: https://github.com/aallan/vera/compare/v0.0.4...v0.0.5
[0.0.4]: https://github.com/aallan/vera/compare/v0.0.3...v0.0.4
[0.0.3]: https://github.com/aallan/vera/compare/v0.0.2...v0.0.3
[0.0.2]: https://github.com/aallan/vera/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/aallan/vera/releases/tag/v0.0.1
