# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

(no entries yet)

## [0.0.115] - 2026-04-18

### Added
- **`Random` effect for non-deterministic value generation** ([#465](https://github.com/aallan/vera/issues/465)) — new built-in `Random` effect with three operations: `Random.random_int(@Int, @Int) -> @Int` (inclusive range), `Random.random_float(@Unit) -> @Float64` (uniform `[0.0, 1.0)`), `Random.random_bool(@Unit) -> @Bool`. Functions drawing random values must declare `effects(<Random>)`, making non-determinism visible in the type signature. Python runtime backs onto `random.randint` / `random.random()`; browser runtime backs all three onto `Math.random()` (fast, non-cryptographic, adequate for games and simulations). No seeding API yet — `handle[Random]`-based deterministic testing is future work. Unblocks games, simulations, shuffling, Monte Carlo methods, and randomized initial states (Conway's Life soup, etc.). Conformance: `ch07_random_effect.vera`. Closes [#465](https://github.com/aallan/vera/issues/465).

## [0.0.114] - 2026-04-17

### Added
- **`IO.sleep`, `IO.time`, `IO.stderr` operations** ([#463](https://github.com/aallan/vera/issues/463)) — three new operations on the built-in `IO` effect. `IO.sleep(@Nat) -> Unit` pauses execution for N milliseconds (used for animation frame budgets and rate-limiting). `IO.time(@Unit) -> @Nat` returns the current Unix time in milliseconds (used for elapsed-time measurement and timestamps). `IO.stderr(@String) -> Unit` writes to stderr separate from stdout (used for CLI tools that pipe stdout as data). Python runtime delegates to `time.sleep`, `time.time`, and `sys.stderr`; browser runtime busy-waits on `performance.now()` (no `Atomics.wait` on the main thread), uses `Date.now()`, and captures stderr into a separate buffer exposed via `getStderr()`. `execute()` gains a `capture_stderr: bool = False` parameter; `ExecuteResult` gains a `stderr: str` field (empty string by default to preserve the pre-#463 shape). Discovered missing while writing a Conway's Game of Life program. Conformance: `ch07_io_time_stderr.vera`.

### Fixed
- **GC object header size field widened from 16-bit to 31-bit** ([#484](https://github.com/aallan/vera/issues/484)) — `$alloc` has always stored the object size as `(size << 1) | mark` (bit 0 = mark, remaining bits = size), but the GC's sweep and free-list code was masking the size readback with `0xFFFF`, silently truncating any allocation ≥ 65536 bytes. The sweeper would then interpret middle-of-payload bytes as tiny zero-size headers and link each 8-byte chunk into the free list, shredding the live object. Removed the `0xFFFF` mask at all five read sites in `vera/codegen/assembly.py` (two in `$alloc` free-list walks, three in `$gc_collect` sweep/mark). Max single allocation is now ~2 GB (bounded by WASM's 4 GB memory ceiling and the leading mark bit). Stress tests for `array_map` and `array_filter` uncapped from 8K back to 10K elements. Discovered a separate memory-grow bug while testing the fix — filed as [#487](https://github.com/aallan/vera/issues/487).

### Changed
- **Iterative WASM `array_fold`** ([#480](https://github.com/aallan/vera/issues/480) PR 3) — `array_fold<T, U>(arr, init, fn)` is now emitted as a single WAT `loop` that runs a closure `(env, U, T) -> U` over each element, updating a running accumulator in-place. Structurally different from PRs 1 and 2: no output allocation (returns a scalar `U`), closure takes two value parameters, and for pair-typed / ADT accumulators the running pointer is kept rooted via an in-place shadow-stack slot overwrite (`global.get $gc_sp; i32.const 8; i32.sub; i32.store`) — avoiding per-iteration push/pop churn. Closes [#480](https://github.com/aallan/vera/issues/480). Also decouples `_ARRAY_TYPE_ALIASES` injection from the (now empty) `array_fn_names` set in `prelude.py` so `ArrayMapFn` / `ArrayFilterFn` / `ArrayFoldFn` aliases stay available for any user code that references them in type annotations.
- **Iterative WASM `array_filter`** ([#480](https://github.com/aallan/vera/issues/480) PR 2) — `array_filter<T>(arr, pred)` is now emitted as a single WAT `loop` with a separate `write_idx`, replacing the recursive prelude (`array_filter` / `array_filter_go`). Worst-case over-allocates `len * sizeof(T)` bytes and returns `(dst, write_idx)`; the unused tail is unreachable via the returned pair and gets reclaimed by the sweeper. Single-pass by design — the predicate is invoked exactly once per element. Shadow-stack usage is now O(1). Follows the same pattern as PR 1 (`array_map`); `array_fold` to follow in PR 3.
- **Iterative WASM `array_map`** ([#480](https://github.com/aallan/vera/issues/480) PR 1) — `array_map<A, B>(arr, fn)` is now emitted as a single WAT `loop` driven by a `call_indirect` on the closure, replacing the recursive prelude implementation (`array_map_go`). Shadow-stack usage is now O(1) regardless of input length — the old recursive version hit the 16K shadow-stack ceiling (post-[#464](https://github.com/aallan/vera/issues/464)) around 4K elements. The generic higher-order signature (`forall<A, B>`) is preserved via a `FunctionInfo` built-in registration, so source code is unchanged. Also discovered and filed [#484](https://github.com/aallan/vera/issues/484) — a pre-existing 16-bit GC-header size-field limits allocations to 65535 bytes; the stress test caps at 8K Int elements (64,000 bytes) until that's fixed.

### Added
- **CHANGELOG enforcement at pre-push and CI** ([#478](https://github.com/aallan/vera/issues/478)) — new `scripts/check_changelog_updated.py` fails a PR if any substantive file (`vera/`, `spec/`, `SKILL.md`) is changed without a matching new entry in `CHANGELOG.md`. Runs at the `pre-push` hook stage locally (opt in with `pre-commit install --hook-type pre-push`) and in the CI `lint` job. Escape hatches: a `Skip-changelog: <reason>` commit trailer (Git-native) or a `skip-changelog` PR label (CI-only). Prevents the kind of missed release-prep that happened on [#474](https://github.com/aallan/vera/pull/474).

### Documentation
- **Docs consistency sweep** — retroactively tag/release v0.0.113 (the release prep PR #477 merged but the tag+release finishing steps were never run); close [#418](https://github.com/aallan/vera/issues/418) manually (PR description lacked an auto-close keyword); refresh file-size tables in `vera/README.md` after the calls.py decomposition (`calls.py` 8,332 → 572 + 8 mixin rows; `wasm/` 4,273 → 12,998 across 17 modules; `codegen/` size drift); fix stale 3,253 → 3,318 test count in `README.md` and the HISTORY by-the-numbers table; add [#424](https://github.com/aallan/vera/issues/424), [#439](https://github.com/aallan/vera/issues/439), [#480](https://github.com/aallan/vera/issues/480) (iterative WASM higher-order array ops), and [#481](https://github.com/aallan/vera/issues/481) (auto-tag + auto-release on version bump) to ROADMAP; remove closed [#416](https://github.com/aallan/vera/issues/416) and [#417](https://github.com/aallan/vera/issues/417) from SKILL.md limitations.

## [0.0.113] - 2026-04-16

### Changed
- **Decompose `vera/wasm/calls.py` into 8 subsystem mixins** ([#418](https://github.com/aallan/vera/issues/418)) — the 8,390-line `calls.py` monolith is split into a small core dispatcher (572 lines) plus 8 domain-focused mixins: `calls_math.py` (numeric + conversions), `calls_markup.py` (JSON/HTML/Markdown/Regex/async), `calls_arrays.py`, `calls_handlers.py` (Show/Hash/handle), `calls_containers.py` (Map/Set/Decimal), `calls_parsing.py`, `calls_encoding.py` (base64/URL), `calls_strings.py`. Pure code motion — `WasmContext` continues to compose all mixins via Python MRO; no behavioral changes, runtime output identical. Makes `calls.py` 93% smaller and prepares ground for Stage 11 primitives additions. Closes [#418](https://github.com/aallan/vera/issues/418).

### Known issues
- **10 pre-existing bugs in WASM call translators** surfaced during review of [#474](https://github.com/aallan/vera/pull/474) — all predate this release; tracked in [#475](https://github.com/aallan/vera/issues/475). See `KNOWN_ISSUES.md` for the summary; the issue lists each bug with severity, location, and description.

## [0.0.112] - 2026-04-16

### Fixed
- **GC shadow stack overflow causing silent array corruption** ([#464](https://github.com/aallan/vera/issues/464)) — the GC shadow stack was 4K (4096 bytes). Recursive functions with multiple `Array` parameters push ~12 bytes per frame (2 pointer params + 1 `array_append` destination), overflowing at ~341 frames into the adjacent GC worklist region. When GC triggered during deep recursion, the worklist corruption caused intermediate arrays to be incorrectly freed, silently overwriting the first bytes of Bool arrays with free-list pointers. Shadow stack increased from 4K to 16K; worklist increased from 4K to 16K; overflow guard added to `gc_shadow_push` (traps instead of silent corruption). Closes [#464](https://github.com/aallan/vera/issues/464).

## [0.0.111] - 2026-04-10

### Fixed
- **SMT translator: String/Float64 parameters declared with correct Z3 sorts** — `String` and `Float64` function parameters were being declared as Z3 integers (the `else` fallback in `verifier.py`), causing `string_contains`, `string_starts_with`, `string_ends_with`, and `string_length` to receive Int-sorted Z3 variables instead of the expected SeqSort/RealSort. String parameters are now declared via `smt.declare_string()` (Z3 `SeqSort`) and Float64 via `smt.declare_float64()` (Z3 `RealSort`).
- **SMT translator: `StringLit` now translates to `z3.StringVal()`** — string literals in contract expressions (e.g. `requires(string_starts_with(@String.0, "https://"))`) were returning `None` from `translate_expr`, silently demoting the contract to Tier 3. Fixed by adding a `StringLit` branch that emits `z3.StringVal(expr.value)`.
- **SMT translator: `string_length` uses `z3.Length()` for String sorts** — the previous uninterpreted function implementation meant Z3 could not prove `string_length("literal") > 0` at call sites (even though it's obviously true), producing spurious E501 call-site precondition errors. `string_length` on a `SeqSort` argument now uses Z3's native `z3.Length()`, giving full string-theory semantics; the uninterpreted fallback is retained for non-string sorts.
- **SMT translator: `string_contains`, `string_starts_with`, `string_ends_with` now Tier 1** — these pure Boolean predicates on String arguments are now encoded via Z3's native string theory (`z3.Contains`, `z3.PrefixOf`, `z3.SuffixOf`) rather than falling through to Tier 3.
- **`float_is_nan` / `float_is_infinite` explicitly return `None`** — previously fell through to the function-lookup path; now explicitly return `None` with a comment explaining why encoding them as `BoolVal(False)` would be unsound (Float64 is modelled as Z3 reals, which have no NaN/infinity; returning `False` would cause the compiler to skip the runtime guard).

## [0.0.110] - 2026-04-10

### Added
- **Mistral AI provider for the Inference effect** ([#413](https://github.com/aallan/vera/issues/413)) — `Inference.complete` now supports Mistral models. Set `VERA_MISTRAL_API_KEY` to use; default model is `mistral-small-latest`. Closes [#413](https://github.com/aallan/vera/issues/413).

### Changed
- **Provider registry refactor** ([#413](https://github.com/aallan/vera/issues/413)) — `_call_inference_provider()` and the auto-detection logic in `execute()` are now table-driven via a `_ProviderConfig` dataclass and `_PROVIDERS` registry dict, replacing the `elif` chain. Adding further providers (Grok, DeepSeek, Gemini) is now a one-row change. The `_call_inference_provider` signature simplified from six parameters to four (`provider`, `prompt`, `model`, `api_key`).

## [0.0.109] - 2026-04-10

### Fixed
- **Closure `i32_pair` param/return type in WAT** ([#359](https://github.com/aallan/vera/issues/359)) — `String` and `Array` parameters and return types inside closures now emit correct two-slot WAT signatures (`(param i32 i32)` / `(result i32 i32)`). Previously the closure lifting path and the `call_indirect` type descriptor each omitted the second i32 slot, causing WAT compilation failures for closures that accept or return `String`/`Array` values. Three fixes: (1) `codegen/closures.py` lifted function declarations now emit `(param $p{i}_ptr i32) (param $p{i}_len i32)` for `i32_pair` params; (2) `wasm/closures.py` `call_indirect` type descriptor emits two params per `i32_pair` argument; (3) `wasm/inference.py` `_infer_apply_fn_return_type` handles `AnonFn` literals to return `"i32_pair"` for `String`/`Array` return types, preventing `$closure_sig_N` naming collisions.
- **Host imports not registered for closures** ([#359](https://github.com/aallan/vera/issues/359)) — Map/Set/Decimal/Json/Html host-import ops used inside closure bodies were not propagated to the module-level tracker, causing `unknown func` errors at runtime. `codegen/closures.py` `_compile_lifted_closure` now propagates all resource flags from the closure's `WasmContext` back to the module codegen.
- **`_infer_fncall_vera_type` truncating parameterised accumulator types** ([#359](https://github.com/aallan/vera/issues/359)) — when inferring the return type of `apply_fn` calls for `_resolve_generic_call`, parameterised types like `Map<String, Int>` were reduced to the bare name `"Map"`, producing wrong monomorphised call targets (e.g. `array_fold_go$String_Map` instead of `array_fold_go$String_Map_String_Int`). Fixed by calling `_format_named_type` instead of returning `ta.name`.

## [0.0.108] - 2026-04-07

### Added
- **`vera check --explain-slots`** ([#445](https://github.com/aallan/vera/issues/445)) — new flag prints a slot resolution table after a successful type-check, showing which parameter position each `@T.n` index refers to. Example: `fn divide(@Int, @Int -> @Int)` produces `@Int.0 = parameter 2 (last @Int)`, `@Int.1 = parameter 1 (first @Int)`. Also available in JSON mode via `--json` (adds `slot_environments` array to output). Closes [#445](https://github.com/aallan/vera/issues/445), closes [#183](https://github.com/aallan/vera/issues/183) (won't fix — see issue for design rationale).
- **SKILL.md prescriptive improvements** — five sections reworked from descriptive to action-oriented: De Bruijn intro now leads with a bold warning; new `--explain-slots` workflow subsection; new "Workflow: writing contracts incrementally" subsection in the Contracts section; Typed Holes intro reframed imperatively; Built-in function naming section adds a directive for handling unresolved names.
- **DE_BRUIJN.md** — new §9 "Debugging with `--explain-slots`" with worked examples.
- **`uv lock --check` in CI** ([#390](https://github.com/aallan/vera/issues/390)) — lint job now verifies `uv.lock` is consistent with `pyproject.toml` on every PR. `CONTRIBUTING.md` updated to document `uv sync` as the recommended install method. Closes [#390](https://github.com/aallan/vera/issues/390).

### Fixed
- **Z3 solver timeout documented** ([#391](https://github.com/aallan/vera/issues/391)) — the 10-second per-contract timeout was already implemented in `vera/smt.py` but undocumented. `spec/06-contracts.md` §6.4.3 now explicitly documents the default. Closes [#391](https://github.com/aallan/vera/issues/391).

## [0.0.107] - 2026-04-07

### Added
- **Validate `vera run` commands in `examples/README.md`** ([#361](https://github.com/aallan/vera/issues/361)) — new `scripts/check_examples_readme.py` parses every `vera run` command in the example index tables, verifies the referenced `.vera` file exists, and verifies any `--fn <name>` target is a public function in that file. Wired into pre-commit (triggers on `examples/README.md` or `.vera` changes) and CI. Closes [#361](https://github.com/aallan/vera/issues/361).

## [0.0.106] - 2026-03-31

### Added
- **`vera test` String and Float64 input generation** ([#169](https://github.com/aallan/vera/issues/169)) — `vera test` now generates Z3 inputs for `String` and `Float64` parameters, removing the `SKIPPED (cannot generate String inputs (see #169))` limitation for those types. String uses Z3's sequence sort with a 50-character length cap; Float64 uses Z3's mathematical real sort with boundary seeding (0.0, ±1.0, ±0.5, ±10.0, ±1e10, ±1e-10). Both types route through the `raw_args` calling convention so that String's two-i32 WASM ABI is handled correctly. IEEE 754 special values (NaN, ±∞, subnormals) are not generated — use explicit test inputs for those cases. ADT input generation remains unsupported ([#440](https://github.com/aallan/vera/issues/440)). Closes [#169](https://github.com/aallan/vera/issues/169).

## [0.0.105] - 2026-03-30

### Added
- **Typed holes** ([#226](https://github.com/aallan/vera/issues/226)) — `?` is now a valid expression placeholder for partial programs. `vera check` reports each hole as a `W001` warning (not an error) with the expected type and all available De Bruijn slot bindings. Programs with holes type-check successfully (`ok: true`) but cannot compile (`E614`). The `--json` output includes hole warnings in the `warnings` array with machine-readable expected type and fix hint. New error code `W001` (typed hole warning) and `E614` (holes block compilation). Conformance test `ch03_typed_holes.vera`. Closes [#226](https://github.com/aallan/vera/issues/226).
- SKILL.md: new [Typed Holes](SKILL.md#typed-holes) section with workflow examples; best-practices tip on incremental development with holes; error code table updated with `W001` and `E614`.
- AGENTS.md: workflow section updated with typed-holes iterative pattern; error code table updated.

## [0.0.104] - 2026-03-29

### Fixed
- **Type inference for bare `None`/`Err` constructors in generic combinator calls** ([#293](https://github.com/aallan/vera/issues/293)) — `option_unwrap_or(None, 99)`, `result_unwrap_or(Err("oops"), 0)`, and `option_map(None, fn(...) {...})` now type-check and compile correctly without requiring a typed `let` binding workaround. Three-layer fix: (1) the checker's fresh-TypeVar overwrite rule in `resolution.py` — later concrete resolutions now overwrite tentative fresh-TypeVar placeholders; (2) the monomorphizer's `_get_arg_type_info` now uses `_ctor_adt_tp_indices` to correctly map sparse constructor fields to their ADT type-param positions (e.g. `Err`'s single field maps to Result's `E`, not `T`); (3) added missing `StringLit` / `InterpolatedString` / `ArrayLit` cases to the monomorphizer's `_infer_vera_type_name`. Closes [#293](https://github.com/aallan/vera/issues/293).

### Added
- Conformance test `ch09_none_err_inference.vera` (level: run) covering all four bare-constructor inference cases.

## [0.0.103] - 2026-03-29

### Added
- **`--quiet` flag for `vera check` / `vera verify`** ([#382](https://github.com/aallan/vera/issues/382)) — suppresses the `OK: ...` and `Verification: ...` success output; errors still print normally. Useful for CI scripts that only need the exit code. Closes [#382](https://github.com/aallan/vera/issues/382).
- **De Bruijn conformance tests: deep let-chains** ([#393](https://github.com/aallan/vera/issues/393)) — `ch03_slot_let_chains.vera` at `verify` level: five sequential `let @Int =` bindings where each doubles the previous; `ensures(@Int.result == 32)` is proved by Z3. Confirms slot indices resolve correctly through deep same-typed `let` chains. Closes [#393](https://github.com/aallan/vera/issues/393).
- **De Bruijn conformance tests: non-commutative operations** ([#394](https://github.com/aallan/vera/issues/394)) — `ch03_slot_noncommutative.vera` at `verify` level: subtraction, division, and comparison with `ensures` contracts that encode the exact De Bruijn ordering. Swapping `@Int.0` / `@Int.1` produces a Z3 counterexample. Closes [#394](https://github.com/aallan/vera/issues/394).
- **Known Limitations section in SKILL.md** ([#404](https://github.com/aallan/vera/issues/404)) — table listing six current implementation limits with issue links: `vera test` String/Float64 skip (#169), bare `None`/`Err` type inference (#293), effect row variable unification (#294), `map_new()`/`set_new()` type context, Inference `max_tokens`/temperature (#370), Inference user-defined handlers (#372). Closes [#404](https://github.com/aallan/vera/issues/404).
- **Conformance test: nested effect handlers** ([#395](https://github.com/aallan/vera/issues/395)) — `ch07_nested_handlers.vera` at `check` level validates correct effect rows on functions that compose multiple algebraic effects. Closes [#395](https://github.com/aallan/vera/issues/395).
- **Conformance test: cross-module contracts** ([#396](https://github.com/aallan/vera/issues/396)) — `ch07_cross_module_contracts.vera` + `ch07_cross_module_contracts_lib.vera` at `check` level validates that contract declarations are visible and enforced across module boundaries. Closes [#396](https://github.com/aallan/vera/issues/396).
- **SKILL.md served from veralang.dev** ([#398](https://github.com/aallan/vera/issues/398)) — `docs/SKILL.md` is now a generated artefact (from root `SKILL.md`, via `build_site.py`), making the language reference available at `veralang.dev/SKILL.md` — on-domain, cacheable, stable. All `href` references in `docs/index.html` updated from raw GitHub URLs to `/SKILL.md`. JSON-LD TechArticle URL updated to `https://veralang.dev/SKILL.md`. Closes [#398](https://github.com/aallan/vera/issues/398).
- **`vera version` / `--version` / `-V` CLI command** ([#381](https://github.com/aallan/vera/issues/381)) — prints `vera X.Y.Z` on stdout. Closes [#381](https://github.com/aallan/vera/issues/381).
- **CycloneDX SBOM generation in CI** ([#389](https://github.com/aallan/vera/issues/389)) — new `sbom` job runs `cyclonedx-py environment --of JSON` on every push, uploading a CycloneDX JSON SBOM as a 90-day artifact. Closes [#389](https://github.com/aallan/vera/issues/389).

### Fixed
- **`Http.post` missing `Content-Type: application/json`** ([#354](https://github.com/aallan/vera/issues/354)) — the Python host function now sets the header on the `urllib.request.Request`; the browser runtime sets `xhr.setRequestHeader('Content-Type', 'application/json')`. `Http.post` is intentionally JSON-only at the Vera level; custom `Content-Type` headers tracked in [#351](https://github.com/aallan/vera/issues/351). Closes [#354](https://github.com/aallan/vera/issues/354).
- **`vera test` skip messages now name the unsupported type** ([#383](https://github.com/aallan/vera/issues/383)) — was `SKIPPED (unsupported parameter types)`; now `SKIPPED (cannot generate String inputs (see #169))`. The specific type name is extracted via the new `_unsupported_type_names` helper. Closes [#383](https://github.com/aallan/vera/issues/383).
- **HTTP host functions missing `timeout`** — `host_http_get` and `host_http_post` now pass `timeout=_INFERENCE_TIMEOUT` to `urllib.request.urlopen`, consistent with the Inference effect.

### Security
- **`ruff check --select S` added to lint job** ([#388](https://github.com/aallan/vera/issues/388)) — 32 Bandit-equivalent S-rule findings audited and suppressed with `# noqa` comments where appropriate (S310 intentional HTTPS calls, S101 compiler invariant asserts, S105 parse-token false positives). `ruff>=0.9` added to `[dev]` dependencies. Closes [#388](https://github.com/aallan/vera/issues/388).
- **`dependency-audit` CI job** ([#384](https://github.com/aallan/vera/issues/384)) — `pip-audit --skip-editable` checks all installed packages against the OSV database on every push. `pygments 2.19.2` has `CVE-2026-4539` (transitive via pytest/rich, no fix release yet) — suppressed with `--ignore-vuln`. Closes [#384](https://github.com/aallan/vera/issues/384).
- **CI workflow hardening** ([#385](https://github.com/aallan/vera/issues/385)) — `persist-credentials: false` on all checkout steps (`artipacked`); per-job `permissions: contents: read` with `security-events: write` on the security job (`excessive-permissions`). SHA pinning of action refs deferred to [#390](https://github.com/aallan/vera/issues/390). Closes [#385](https://github.com/aallan/vera/issues/385).

## [0.0.102] - 2026-03-28

### Added
- **Type-aware CLI argument passing** ([#263](https://github.com/aallan/vera/issues/263)) — `vera run file.vera --fn f -- arg` now accepts all Vera scalar and string types, not just integers. Arguments are parsed using the function's WASM signature: `Int`/`Nat` → integer literal, `Float64` → decimal literal, `Bool` → `true`/`false` (case-insensitive), `Byte` → integer 0–255, `String` → text (allocated into WASM linear memory). Type-mismatch errors identify the bad argument and expected type. `CompileResult.fn_param_types` (new field) exposes per-function WASM-level type tags (`i64`, `f64`, `i32`, `i32_pair`) so the host runtime can handle memory allocation and invocation correctly for each parameter kind. Closes [#263](https://github.com/aallan/vera/issues/263). Closes [#403](https://github.com/aallan/vera/issues/403).
- **Multi-layer agent discovery metadata** ([#400](https://github.com/aallan/vera/issues/400)) — veralang.dev now exposes `SKILL.md` through four machine-readable layers: `<head>` link elements (`rel="alternate" type="text/markdown"`, `rel="llms-txt"`, `rel="llms-full-txt"`), an inline `<script type="text/llms.txt">` block (Vercel convention), JSON-LD `TechArticle` entries for `SKILL.md` and `AGENTS.md`, and semantic attributes on the existing CTA button. HTTP headers skipped — GitHub Pages does not support custom response headers. Closes [#400](https://github.com/aallan/vera/issues/400).

### Fixed
- **E609 false positive on `Option<T>` return types across modules** ([#360](https://github.com/aallan/vera/issues/360)) — the name-collision checker incorrectly flagged `Option`, `Result`, and other built-in ADTs as user-defined names when they appeared as return types in imported modules. Fixed by pre-seeding `builtin_adt_names` before scanning module declarations. Closes [#360](https://github.com/aallan/vera/issues/360).
- **Pipe operator into module-qualified calls** ([#326](https://github.com/aallan/vera/issues/326)) — `value |> mod::fn(args)` previously type-checked the right-hand side in isolation, ignoring the piped argument. The checker now desugars to a `ModuleCall` with the LHS prepended to the argument list. Closes [#326](https://github.com/aallan/vera/issues/326).
- **`/dev/stdin` double-read** ([#335](https://github.com/aallan/vera/issues/335)) — all CLI commands (`check`, `verify`, `compile`, `run`, `ast`, `test`) previously called `p.read_text()` for the source string and then `parse_file(path)` which re-opened the same path. For `/dev/stdin` the second open returns empty content. Fixed by extracting `_load_and_parse(path)` which reads the source once and passes it directly to `parse()`. For stdin paths, returns `Path.cwd()/"stdin.vera"` so module resolution and compile output naming use CWD. Closes [#335](https://github.com/aallan/vera/issues/335).

## [0.0.101] - 2026-03-27

### Added
- **Inference effect** ([#61](https://github.com/aallan/vera/issues/61)) — built-in `<Inference>` algebraic effect with one operation: `Inference.complete(String → Result<String, String>)`. Sends a prompt to the configured LLM provider and returns `Ok(completion)` or `Err(message)`. Provider auto-detected from whichever API key is set; override with `VERA_INFERENCE_PROVIDER`. Model configurable via `VERA_INFERENCE_MODEL`. Default models: Anthropic → `claude-haiku-4-5-20251001`, OpenAI → `gpt-4o-mini`, Moonshot → `moonshot-v1-8k`. Implemented via host imports (Python `urllib.request`). Built-in effect — no `effect Inference { ... }` declaration needed. Browser runtime returns a detailed `Err` explaining why API keys cannot be embedded in client-side JavaScript. New conformance test `ch09_inference` (64 programs, was 63). New example `inference.vera`. Closes [#61](https://github.com/aallan/vera/issues/61).

### Known limitations
- `complete` only — `embed` (returning `Array<Float64>`) deferred to a follow-up
- No streaming responses — full completion only
- No system prompt — single `complete(user_prompt)` call; structured prompting via `string_concat`
- No token limits or temperature controls — Anthropic: `max_tokens` hardcoded to 1024; OpenAI and Moonshot use provider defaults ([#370](https://github.com/aallan/vera/issues/370))
- User-defined `handle[Inference]` handlers (for mocking, local models, replay) are planned for a future release

## [0.0.100] - 2026-03-26

### Added
- **Html standard library type** ([#311](https://github.com/aallan/vera/issues/311)) — built-in `HtmlNode` ADT (`HtmlElement`, `HtmlText`, `HtmlComment`) with 5 built-in functions: `html_parse`, `html_to_string`, `html_query`, `html_text`, `html_attr`. Lenient HTML parsing (like browsers). Simple CSS selector query support (tag, class, ID, attribute, descendant combinator). Implemented via host imports (Python `html.parser`). `html_attr` is a pure Vera prelude function using `map_get`. New conformance test `ch09_html` (63 programs, was 62). New example `html.vera`.

## [0.0.99] - 2026-03-25

### Added
- **Http effect** ([#57](https://github.com/aallan/vera/issues/57)) — built-in `<Http>` algebraic effect with two operations: `Http.get(url)` and `Http.post(url, body)`, both returning `Result<String, String>`. Implemented via host imports (Python `urllib.request` / JavaScript `fetch`). Composes with `json_parse` for typed API responses. Built-in effect — no `effect Http { ... }` declaration needed. New conformance test `ch09_http` (62 programs, was 61). New example `http.vera`. Browser runtime support. Closes #57.

### Known limitations
- No custom headers ([#351](https://github.com/aallan/vera/issues/351))
- No HTTP methods beyond GET/POST ([#352](https://github.com/aallan/vera/issues/352))
- No response status code access ([#353](https://github.com/aallan/vera/issues/353))
- No request timeout configuration ([#354](https://github.com/aallan/vera/issues/354))
- No streaming responses ([#355](https://github.com/aallan/vera/issues/355))
- No cookie/session management ([#356](https://github.com/aallan/vera/issues/356))

## [0.0.98] - 2026-03-25

### Added
- **Json standard library type** ([#58](https://github.com/aallan/vera/issues/58)) — built-in `Json` ADT (`JNull`, `JBool`, `JNumber`, `JString`, `JArray`, `JObject`) with 8 built-in functions: `json_parse`, `json_stringify`, `json_get`, `json_array_get`, `json_array_length`, `json_keys`, `json_has_field`, `json_type`. Implemented via host imports (Python `json` / JavaScript `JSON`). Opaque i32 handles following the Map/Set pattern. New conformance test `ch09_json` (61 programs, was 60). New example `json.vera`. Browser runtime support.
- New conformance test `ch09_decimal_generics` (60 programs, was 59) — exercises `option_unwrap_or`, `match`, and `decimal_compare` with Decimal.
- 12 new unit tests for opaque handle monomorphization paths (Decimal, Map, Set).

### Fixed
- **Monomorphization of opaque handle types** ([#341](https://github.com/aallan/vera/issues/341)) — generic prelude functions (`option_unwrap_or`, `match`) now work with all opaque handle types: `Option<Decimal>`, `Option<Map<K,V>>`, `Option<Set<T>>`, `Ordering` from `decimal_compare`. The monomorphizer now preserves full parameterized type names (e.g. `Map<String, Int>`) through type inference, substitution, and name mangling. Previously, type arguments were dropped during inference, causing `option_unwrap_or$Map` to fail codegen. Closes #341.

## [0.0.97] - 2026-03-24

### Added
- **Decimal type for exact arithmetic** ([#333](https://github.com/aallan/vera/issues/333)) — 14 built-in operations (`decimal_from_int`, `decimal_from_float`, `decimal_from_string`, `decimal_to_string`, `decimal_to_float`, `decimal_add`, `decimal_sub`, `decimal_mul`, `decimal_div`, `decimal_neg`, `decimal_compare`, `decimal_eq`, `decimal_round`, `decimal_abs`) via host imports (Python `decimal.Decimal` / JS string-based decimal). New conformance test `ch09_decimal` (59 programs, was 58). Browser runtime support. Closes #333.

## [0.0.96] - 2026-03-24

### Changed
- **Documentation sweep for collections** ([#62](https://github.com/aallan/vera/issues/62), PR 3/3) — fix stale "future collections" language in spec, update README version and Ch 9 description, add Map/Set to SKILL.md composite types and common mistakes, update example counts across all docs (25→28). New `examples/collections.vera` showcasing word-frequency analysis with Map and Set operations. Closes #62.

## [0.0.95] - 2026-03-24

### Added
- **Set\<T\> collection type** ([#62](https://github.com/aallan/vera/issues/62), PR 2/3) — six built-in operations (`set_new`, `set_add`, `set_contains`, `set_remove`, `set_size`, `set_to_array`) with `Eq<T> + Hash<T>` ability constraints. Host-import pattern (Python sets / JS Sets behind opaque i32 handles). Pure functional semantics. New conformance test `ch09_set` (58 programs, was 57). 25 unit tests.
- **Native JS coverage issue** ([#337](https://github.com/aallan/vera/issues/337)) — tracked for future c8 integration.
- **Stdin compilation bug** ([#335](https://github.com/aallan/vera/issues/335)) — filed and added to Known Bugs.

### Changed
- **README test counts** — removed hardcoded counts, TESTING.md is now the single source of truth.

## [0.0.94] - 2026-03-23

### Added
- **Map\<K, V\> collection type** ([#62](https://github.com/aallan/vera/issues/62), PR 1/3) — eight built-in operations (`map_new`, `map_insert`, `map_get`, `map_contains`, `map_remove`, `map_size`, `map_keys`, `map_values`) with `Eq<K> + Hash<K>` ability constraints. Implemented via host imports (Python dicts / JS Maps behind opaque i32 handles). Pure functional semantics — `map_insert` and `map_remove` return new maps. New conformance test `ch09_map` (57 programs, was 56). 40 new unit tests. Browser runtime support.
- **Decimal type issue** ([#333](https://github.com/aallan/vera/issues/333)) — split from #62 as independent future work.

### Fixed
- **Type inference for zero-argument generic functions** — `map_new()` and similar zero-arg generic calls now resolve type variables from expected type context (bidirectional coercion). Fixed unification to skip ADT args whose TypeVars match the callee's own forall vars.

## [0.0.93] - 2026-03-20

### Changed
- **Standard prelude — eliminate boilerplate** ([#289](https://github.com/aallan/vera/issues/289)) — `Option<T>`, `Result<T, E>`, `Ordering`, and `UrlParts` are now unconditionally injected by the prelude, eliminating 2–6 lines of identical `data` declarations from every program that uses these types. Option/Result combinators and array operations are also always available. User-defined `data` declarations with the same name shadow the prelude versions. Non-standard variants (e.g. `data Option<T> { None, Just(T) }`) correctly suppress combinator injection. New conformance test `ch09_prelude` (conformance suite: 55→56 programs). Boilerplate removed from 8 conformance programs and 8 examples. Closes #289.

## [0.0.92] - 2026-03-19

### Changed
- **BREAKING: Built-in function naming audit** ([#288](https://github.com/aallan/vera/issues/288)) — renamed 14 inconsistently-named built-in functions to follow the dominant `domain_verb` convention. String operations gain `string_` prefix (`strip` → `string_strip`, `upper` → `string_upper`, etc.), float predicates gain `float_` prefix (`is_nan` → `float_is_nan`, `is_infinite` → `float_is_infinite`), and `to_float` becomes `int_to_float`. Closes #288.

### Added
- **Naming convention documentation** — formal naming rules added to spec §9.1.1, SKILL.md, vera/README.md, and CONTRIBUTING.md. Four patterns: `domain_verb` (dominant), `source_to_target` (conversions), `domain_is_predicate` (boolean tests), prefix-less (math universals only).

## [0.0.91] - 2026-03-19

### Added
- **Array operations** ([#133](https://github.com/aallan/vera/issues/133)) — four new built-in array functions: `array_slice` (WASM intrinsic with index clamping), `array_map` (generic, element type can change), `array_filter` (predicate-based selection), and `array_fold` (left fold with arbitrary accumulator type). Higher-order operations implemented via prelude source injection with recursive helpers. 15 unit tests. Closes #133.

### Fixed
- **De Bruijn reindexing during monomorphization** ([#316](https://github.com/aallan/vera/issues/316)) — when distinct type variables collapse to the same concrete type, slot reference indices are now correctly adjusted
- **Transitive monomorphization** ([#317](https://github.com/aallan/vera/issues/317)) — generic functions calling other generic functions now correctly generate all required specializations via worklist-based closure
- **WASM type inference gaps** ([#313](https://github.com/aallan/vera/issues/313), [#314](https://github.com/aallan/vera/issues/314), [#315](https://github.com/aallan/vera/issues/315), [#318](https://github.com/aallan/vera/issues/318)) — `_is_pair_type_name` now matches bare `Array`, `_infer_vera_type` handles `IndexExpr` and `IfExpr`, `_infer_fncall_vera_type` handles `apply_fn`, `_get_arg_type_info` handles `ArrayLit` and `FnCall`

## [0.0.90] - 2026-03-13

### Added
- **Abilities release** ([#60](https://github.com/aallan/vera/issues/60)) — four built-in abilities (`Eq`, `Ord`, `Hash`, `Show`) with full codegen support. Includes the built-in `Ordering` ADT (`Less`, `Equal`, `Greater`), ADT auto-derivation for `Eq` (structural equality for simple enums and ADTs with primitive fields), `compare` rewriting via Pass 1.6 AST transformation, `show`/`hash` dispatch at WASM level (FNV-1a for String hashing), and string equality via byte-by-byte comparison. Constraint satisfaction checked for all four abilities (E613). 20 unit tests, extended conformance test with 20 test functions. Closes #60.

## [0.0.89] - 2026-03-12

### Added
- **Option/Result combinators** ([#211](https://github.com/aallan/vera/issues/211)) — five prelude functions that eliminate common match boilerplate: `option_unwrap_or`, `option_map`, `option_and_then`, `result_unwrap_or`, `result_map`. Implemented via source injection (parsed Vera AST, injected before codegen). Includes compiler fixes for generic type alias return type inference in closures, closure signature deduplication across functions, and AnonFn type variable inference in the monomorphizer. New conformance test, 12 unit tests, spec section 9.3.7.

### Changed
- **`map_option` renamed to `option_map`** — all references across spec, examples, and tests updated to follow the `domain_verb` naming convention ([#288](https://github.com/aallan/vera/issues/288)).

## [0.0.88] - 2026-03-12

### Fixed
- **Formatter comment repositioning** ([#274](https://github.com/aallan/vera/issues/274)) — comments inside function bodies were moved to the file footer during formatting. Extended the anchor system to collect interior AST spans (statements, result expressions) and emit comments at the correct positions within blocks, if/else branches, match arms, and handler bodies. Added `_collect_interior_anchors` recursive walker. 7 new tests, `examples/string_ops.vera` reformatted to canonical form. Closes #274.

## [0.0.87] - 2026-03-11

### Added
- **FizzBuzz example** — complete runnable program demonstrating recursion as iteration with IO effects (`examples/fizzbuzz.vera`)
- **"Recursion as iteration" section** in README "What Vera Looks Like" — explains the standard Vera pattern for counted iteration
- **"Iteration" section** in SKILL.md — documents the tail-recursive loop pattern for agents
- **De Bruijn slot reference reminder** in CLAUDE.md — documents that `@T.0` = most recent (last) parameter

### Fixed
- **Verifier branch-condition bug** documented ([#283](https://github.com/aallan/vera/issues/283)) — call-site precondition checking doesn't use if-guard path conditions; added to Known Bugs with workaround

## [0.0.86] - 2026-03-11

### Added
- **Regex support** ([#231](https://github.com/aallan/vera/issues/231)):
  Four new pure functions for regular expression matching on strings:
  `regex_match`, `regex_find`, `regex_find_all`, `regex_replace`.
  All return `Result` types for safe handling of invalid patterns.
  Implemented as WASM host imports — Python's `re` module for wasmtime,
  JavaScript's `RegExp` for the browser runtime. Browser parity verified.
- New conformance test `ch09_regex` (conformance suite: 52→53 programs)
- New example `examples/regex.vera` (example suite: 23→24 programs)
- Spec §9.6.15 "Regular Expressions"
- 16 new tests (10 codegen + 6 type checker) plus browser parity coverage

## [0.0.85] - 2026-03-11

### Added
- **Browser runtime for compiled WASM** ([#273](https://github.com/aallan/vera/issues/273)):
  A self-contained JavaScript runtime (`vera/browser/runtime.mjs`, ~730 lines) that
  runs any compiled Vera `.wasm` module in the browser or Node.js. Uses
  `WebAssembly.Module.imports()` to introspect the module's imports and dynamically
  builds the host binding object — no code generation needed. The same runtime file
  works with every compiled Vera program, from hello-world (1 import) to markdown-heavy
  programs (15+ imports).
  Includes JavaScript implementations of all host bindings: IO operations (print,
  read_line, args, exit, get_env, read_file/write_file with browser-appropriate
  adaptations), State\<T\> (dynamically pattern-matched from import names),
  contract_fail, and all 5 Markdown operations (with a bundled JS Markdown parser).
- New CLI flag: `vera compile --target browser` produces a ready-to-serve browser
  bundle (module.wasm + vera-runtime.mjs + index.html) in a single command
- New `vera/browser/` package: `runtime.mjs` (JS runtime), `harness.mjs` (Node.js
  test harness), `emit.py` (browser bundle emission)
- 56 new browser parity tests ensuring identical output between Python/wasmtime and
  Node.js/JS-runtime across IO, State, contracts, Markdown, and all compilable examples
- Browser parity CI job (Node.js 22) and pre-commit hook triggered by changes to
  host binding surface (`vera/browser/`, `vera/codegen/api.py`, `vera/wasm/markdown.py`,
  `vera/markdown.py`)
- Spec §12.4.3 (Contract Violations) and §12.4.4 (Markdown Operations) — host binding
  documentation missing from v0.0.84
- Spec §12.9 (Browser Runtime) — JavaScript runtime architecture and usage

## [0.0.84] - 2026-03-11

### Added
- **Markdown standard library** ([#147](https://github.com/aallan/vera/issues/147)):
  Two new built-in ADTs for typed Markdown document representation:
  `MdInline` (6 constructors: MdText, MdCode, MdEmph, MdStrong, MdLink, MdImage)
  and `MdBlock` (8 constructors: MdParagraph, MdHeading, MdCodeBlock, MdBlockQuote,
  MdList, MdThematicBreak, MdTable, MdDocument).
  Five new pure functions: `md_parse(String → Result<MdBlock, String>)`,
  `md_render(MdBlock → String)`, `md_has_heading(MdBlock, Nat → Bool)`,
  `md_has_code_block(MdBlock, String → Bool)`,
  `md_extract_code_blocks(MdBlock, String → Array<String>)`.
  All implemented as WASM host imports with a hand-written Python parser —
  the first pure functions using the host-binding pattern.
  The WASM import interface is the portability contract: the same `.wasm`
  binary works with any host runtime (Python, JavaScript, Rust) that provides
  matching implementations.
- New conformance test `ch09_markdown` (conformance suite: 51→52 programs)
- New example `examples/markdown.vera` — parse, query, extract, and render Markdown
- 78 new tests (59 parser/renderer + 6 type checker + 8 codegen + 5 conformance)

### Changed
- **Spec §9.3 reorganization:** UrlParts (from §9.6.13), Future\<T\> (from §9.5.4),
  MdInline, and MdBlock are now documented in §9.3 (Built-in ADTs) as §9.3.3–§9.3.6.
  Function specs remain in their original sections with cross-references.

## [0.0.83] - 2026-03-11

### Added
- **Tuple type WASM codegen** ([#267](https://github.com/aallan/vera/issues/267)):
  Tuple construction (`Tuple(1, "hello", true)`) and destructuring now compile to WASM.
  Match destructuring (`Tuple(@Int, @String) -> ...`) extracts fields from heap-allocated Tuples.
  `LetDestruct` (`let Tuple<@Int, @String> = expr;`) works for Tuples and all single-constructor
  ADTs (including UrlParts, Future, and user-defined types).
  Tuples are variadic — any arity from 1 field upward is supported.
- New conformance test `ch02_tuple_basic` (conformance suite: 50→51 programs)
- Updated `examples/url_parsing.vera` with LetDestruct demonstration
- 15 new tests (5 type checker + 10 codegen)

## [0.0.82] - 2026-03-11

### Added
- **`<Async>` effect with `Future<T>` type** ([#59](https://github.com/aallan/vera/issues/59)):
  New `Async` marker effect and `Future<T>` ADT for asynchronous computation.
  New `async(@T -> @Future<T>)` — wraps a value in a future (eager evaluation).
  New `await(@Future<T> -> @T)` — unwraps a future to its result.
  `Future<T>` is WASM-transparent — same runtime representation as `T`, zero overhead.
  The reference implementation uses sequential evaluation; true concurrency will be
  available via WASI 0.3 native `future<T>` support ([#237](https://github.com/aallan/vera/issues/237)).
- New conformance test `ch09_async` (conformance suite: 49→50 programs)
- New example `examples/async_futures.vera` — async/await roundtrip and composition demo
- 15 new tests (7 type checker + 8 codegen)

## [0.0.81] - 2026-03-10

### Added
- **URL parsing and joining** ([#232](https://github.com/aallan/vera/issues/232), Phase 2):
  New `url_parse(@String -> @Result<UrlParts, String>)` — RFC 3986 URL decomposition
  into scheme, authority, path, query, and fragment components.
  New `url_join(@UrlParts -> @String)` — reassembles a `UrlParts` value into a URL string.
  New built-in `UrlParts` ADT type with five String fields.
- New conformance test `ch09_url_parsing` (conformance suite: 48→49 programs)
- New example `examples/url_parsing.vera` — parse, extract components, join, and error demo
- 29 new tests (4 type checker + 25 codegen)

### Fixed
- **ADT constructors with String/Array fields** ([#266](https://github.com/aallan/vera/issues/266)):
  Layout computation (`_wasm_type_size`, `_wasm_type_align`) now handles `i32_pair`
  (String/Array representation). User-defined ADTs with String fields compile correctly.

## [0.0.80] - 2026-03-10

### Added
- **URL percent-encoding and decoding** ([#232](https://github.com/aallan/vera/issues/232)):
  New `url_encode(@String -> @String)` — RFC 3986 percent-encoding, leaving
  unreserved characters unchanged.
  New `url_decode(@String -> @Result<String, String>)` — percent-decoding with
  error handling for invalid `%XX` sequences.
- New conformance test `ch09_url_encoding` (conformance suite: 47→48 programs)
- New example `examples/url_encoding.vera` — encode, decode, and round-trip demo
- 21 new tests (4 type checker + 17 codegen)

## [0.0.79] - 2026-03-10

### Added
- **Close #234: Base64 encoding and decoding** ([#234](https://github.com/aallan/vera/issues/234)):
  New `base64_encode(@String -> @String)` — standard Base64 (RFC 4648) encoding.
  New `base64_decode(@String -> @Result<String, String>)` — Base64 decoding with
  error handling for invalid length or characters.
- New conformance test `ch09_base64` (conformance suite: 46→47 programs)
- New example `examples/base64.vera` — encode, decode, and round-trip demo
- 20 new tests (4 type checker + 16 codegen)

## [0.0.78] - 2026-03-10

### Added
- **Close #209: Array construction builtins** ([#209](https://github.com/aallan/vera/issues/209)):
  New `array_range(@Int, @Int -> @Array<Int>)` — integer range [start, end), empty
  if start >= end. New `array_concat(forall<T> @Array<T>, @Array<T> -> @Array<T>)` —
  merge two arrays into a new array.
- New conformance test `ch04_array_construction` (conformance suite: 45→46 programs)
- 17 new tests (4 type checker + 7 codegen array_range + 6 codegen array_concat)

### Changed
- **Breaking:** `length` renamed to `array_length`. The array length builtin now
  follows the same `array_` prefix convention used by string builtins (`string_length`,
  `string_concat`, etc.). All code using `length()` on arrays must be updated.
- **Breaking:** `array_push` renamed to `array_append`. Clearer intent and consistent
  naming with the new array builtins.

## [0.0.77] - 2026-03-10

### Added
- **Close #200: Parsing completeness** ([#200](https://github.com/aallan/vera/issues/200)):
  New `parse_int` (`String → Result<Int, String>`) and `parse_bool`
  (`String → Result<Bool, String>`) built-in functions. `parse_int` handles
  optional `+`/`-` sign. `parse_bool` is strict lowercase only — only `"true"`
  and `"false"` are valid.
- New conformance test `ch04_parse_completeness` (conformance suite: 44→45 programs)
- 22 new tests (6 type checker + 8 codegen parse_int + 6 codegen parse_bool + 2 codegen parse_float64 error cases)

### Changed
- **Breaking:** `parse_float64` return type changed from `Float64` to
  `Result<Float64, String>`. Previously returned `0.0` silently on invalid input;
  now returns `Err(msg)` with a descriptive error message. All four parse functions
  (`parse_nat`, `parse_int`, `parse_float64`, `parse_bool`) now consistently
  return `Result<T, String>`.

## [0.0.76] - 2026-03-10

### Added
- **Close #230: String interpolation** ([#230](https://github.com/aallan/vera/issues/230)):
  New `\(expr)` syntax inside double-quoted strings for ergonomic string building.
  Non-String expressions of type Int, Nat, Bool, Byte, and Float64 are automatically
  converted using the appropriate `*_to_string` built-in. `InterpolatedString` is a
  first-class AST node (canonical form, survives formatting). Touches every compiler
  stage: grammar, transformer, type checker, formatter, and WASM codegen.
- New conformance test `ch04_string_interpolation` (conformance suite: 43→44 programs)
- 18 new tests (9 type checker + 9 codegen end-to-end)
- Spec Sections 1.4 "String Interpolation" and 4.13.1 "String Interpolation"

## [0.0.75] - 2026-03-10

### Added
- **Close #213: string_repeat builtin** ([#213](https://github.com/aallan/vera/issues/213)):
  New `string_repeat` function (`String, Nat → String`) that repeats a string N
  times. Uses a single-allocation loop with modulo indexing. Pure, Tier 3
  (runtime-tested).
- 7 new tests (2 type checker + 5 codegen end-to-end)

## [0.0.74] - 2026-03-09

### Added
- **Close #210: from_char_code builtin** ([#210](https://github.com/aallan/vera/issues/210)):
  New `from_char_code` function (`Nat → String`) that creates a single-character
  string from an ASCII code point. Inverse of the existing `char_code`. Pure,
  Tier 3 (runtime-tested).
- 7 new tests (2 type checker + 5 codegen end-to-end)

## [0.0.73] - 2026-03-09

### Added
- **Close #198: String search and transformation builtins** ([#198](https://github.com/aallan/vera/issues/198)):
  Nine new built-in functions for string search and transformation:
  `string_contains` (String,String→Bool), `starts_with` (String,String→Bool),
  `ends_with` (String,String→Bool), `index_of` (String,String→Option\<Nat\>),
  `to_upper` (String→String), `to_lower` (String→String),
  `replace` (String,String,String→String), `split` (String,String→Array\<String\>),
  `join` (Array\<String\>,String→String). All are pure and Tier 3 (runtime-tested).
- New conformance test `ch09_string_search` (conformance suite: 42→43 programs)
- 55 new tests (18 type checker + 37 codegen end-to-end)
- Spec Sections 9.6.6 "String Search" and 9.6.7 "String Transformation"

## [0.0.72] - 2026-03-09

### Added
- **Close #212: Float64 special value operations** ([#212](https://github.com/aallan/vera/issues/212)):
  Four new built-in functions for detecting and constructing IEEE 754 special
  Float64 values: `is_nan` (Float64→Bool), `is_infinite` (Float64→Bool),
  `nan` (→Float64), and `infinity` (→Float64). All are Tier 3 (runtime-tested).
- New conformance test `ch10_float_predicates` (conformance suite: 41→42 programs)
- 25 new tests (8 type checker + 17 codegen end-to-end)
- Spec Section 9.6.5 "Float64 Predicates" with full signatures and contracts

## [0.0.71] - 2026-03-09

### Added
- **Close #208: Numeric type conversions** ([#208](https://github.com/aallan/vera/issues/208)):
  Six new built-in functions for explicit conversion between numeric types:
  `to_float` (Int→Float64), `float_to_int` (Float64→Int, truncation toward zero),
  `nat_to_int` (Nat→Int, identity), `int_to_nat` (Int→Option\<Nat\>, checked),
  `byte_to_int` (Byte→Int, zero-extension), and `int_to_byte` (Int→Option\<Byte\>,
  checked). Widening conversions always succeed; narrowing conversions return
  `Option` for safety. `nat_to_int` and `byte_to_int` are SMT-verifiable (Tier 1).
- New conformance test `ch09_type_conversions` (conformance suite: 40→41 programs)
- 38 new tests (12 type checker + 26 codegen end-to-end)
- Spec Section 9.6.4 "Type Conversions" with full signatures and contracts

## [0.0.70] - 2026-03-09

### Added
- **Close #199: Numeric math builtins** ([#199](https://github.com/aallan/vera/issues/199)):
  Eight new built-in functions for common mathematical operations: `abs` (Int→Nat),
  `min`/`max` (Int,Int→Int), `floor`/`ceil`/`round` (Float64→Int), `sqrt`
  (Float64→Float64), and `pow` (Float64,Int→Float64). All are pure and available
  without imports. Integer builtins (`abs`, `min`, `max`) are fully verifiable by
  Z3 (Tier 1). Float builtins use native WASM instructions. `round` uses IEEE 754
  banker's rounding. `pow` takes an integer exponent with negative exponent support.
- New conformance test `ch09_numeric_builtins` (conformance suite: 39→40 programs)
- 41 new tests (13 type checker + 28 codegen end-to-end)
- Spec Section 9.6.3 "Numeric Operations" with full signatures and contracts

## [0.0.69] - 2026-03-06

### Fixed
- **Close #241: Byte literal coercion** ([#241](https://github.com/aallan/vera/issues/241)):
  Integer literals 0–255 are now accepted as `Byte` when the expected type is
  `Byte` (bidirectional type checking). The `ch01_byte_literals` conformance test
  is promoted from `check` to `run` level.
- **Close #242: `array_push` codegen** ([#242](https://github.com/aallan/vera/issues/242)):
  `array_push(array, elem)` is now a fully implemented builtin — registered in the
  type environment with a generic `(Array<T>, T) -> Array<T>` signature and compiled
  to WASM with proper allocation, element copying, and GC shadow stack integration.
  The `ch04_array_ops` conformance test now exercises `array_push`.

### Changed
- Conformance suite: `ch01_byte_literals` promoted from `check` to `run` level;
  `ch04_array_ops` now includes `array_push` in its feature coverage
- Documentation updated across TESTING.md, SKILL.md, and README.md to reflect
  resolved bugs and new builtin

## [0.0.68] - 2026-03-05

### Added
- **Close #223: Conformance test suite** ([#223](https://github.com/aallan/vera/issues/223)):
  39 small, self-contained programs in `tests/conformance/` that systematically
  validate every language feature against the spec (Chapters 1-7). Each program
  tests one feature or a small group of related features.
- `tests/conformance/manifest.json` — machine-readable metadata mapping each
  program to its spec chapter, test level (parse/check/verify/run), and feature tags
- `tests/test_conformance.py` — parametrized pytest runner generating ~195 test
  cases across all 39 conformance programs
- `scripts/check_conformance.py` — standalone validation script for CI and
  pre-commit (same pattern as `check_examples.py`)
- Pre-commit hook `conformance-suite` and CI step in lint job
- Conformance suite documentation across TESTING.md, README.md, CLAUDE.md,
  AGENTS.md, SKILL.md, and vera/README.md
- Known Bugs section in README.md listing compiler issues discovered during
  conformance suite development

### Fixed
- Opened [#241](https://github.com/aallan/vera/issues/241) (Byte literal coercion),
  [#242](https://github.com/aallan/vera/issues/242) (array_push codegen), and
  [#243](https://github.com/aallan/vera/issues/243) (nested generic constructor
  type inference) — bugs discovered while building the conformance suite

## [0.0.67] - 2026-03-05

### Added
- **Close #216: String escape sequences** ([#216](https://github.com/aallan/vera/issues/216)):
  Fix grammar regex and add escape sequence decoder in `transform.py`.
  All 7 escape sequences from spec section 1 are now supported: `\\`, `\"`, `\n`, `\t`,
  `\r`, `\0`, `\u{XXXX}`. Invalid escapes produce error code E009.
- 19 new tests (14 AST + 5 codegen end-to-end) for escape sequence handling

### Fixed
- `STRING_LIT` grammar regex had too many backslashes, causing the lexer to
  reject single-backslash escape sequences like `\n` and `\t`

## [0.0.66] - 2026-03-05

### Added
- **Close #135: IO operations** (C8.5, [#135](https://github.com/aallan/vera/issues/135)):
  Six new IO operations: `read_line`, `read_file`, `write_file`, `args`,
  `exit`, and `get_env`. All seven IO operations (including `print`) are
  now registered as built-in effect operations with full type checking.
  Programs no longer need `effect IO { op print(String -> Unit); }` preambles.
- Host function implementations for all IO operations via wasmtime, with
  WASM-to-host string passing through exported `$alloc`
- `ExecuteResult.exit_code` field for `IO.exit` support
- `execute()` accepts `stdin`, `cli_args`, and `env_vars` parameters
- Two new example programs: `io_operations.vera` and `file_io.vera`
- 26 new tests across type checker, codegen, and CLI

### Changed
- IO effect is now a built-in with all 7 operations registered in the
  type environment (no user `effect IO` declaration required)
- Replaced `_needs_io_print: bool` with `_io_ops_used: set[str]` for
  per-operation WASM import tracking
- WASM modules export `$alloc` when IO operations need host-to-WASM
  string allocation
- `_is_void_expr` now recursively handles compound expressions
  (MatchExpr, IfExpr, Block) to prevent invalid `drop` instructions
- Fixed match dispatch for ADT constructors with String fields
  (`i32_pair` type in `_sub_pattern_wasm_type` and size/align dicts)

## [0.0.65] - 2026-03-04

### Added
- **Close #51: garbage collection for WASM linear memory** (C8e, [#51](https://github.com/aallan/vera/issues/51)):
  Conservative mark-sweep garbage collector implemented entirely in WASM.
  Shadow stack root tracking, free-list reuse, and automatic `memory.grow`
  ensure allocation-heavy programs survive beyond the initial 64 KiB page.
  New `gc_pressure.vera` example demonstrates GC under repeated allocation.

### Changed
- Memory layout now reserves 8192 bytes after string constants for GC
  shadow stack (4096 bytes) and mark worklist (4096 bytes)
- `$alloc` prepends a 4-byte header to every allocation (mark bit + size)
  and checks the free list before bump-allocating
- Functions that allocate heap data receive GC prologue/epilogue
  (save/restore `$gc_sp`, push pointer parameters and return values)
- `to_string` and `strip` now allocate exact-size result buffers instead
  of returning interior pointers into temporary buffers
- Removed "No garbage collection" from limitation tables in spec, README,
  and compiler architecture docs

## [0.0.64] - 2026-03-04

### Added
- **Close #106: universal to-string conversion** (C8e, [#106](https://github.com/aallan/vera/issues/106)):
  Added 5 new string conversion builtins for all primitive types:
  `bool_to_string(Bool -> String)`, `nat_to_string(Nat -> String)`,
  `byte_to_string(Byte -> String)`, `float_to_string(Float64 -> String)`,
  and `int_to_string(Int -> String)` (alias for existing `to_string`).
  ADT/compound type Show deferred to abilities (#60).

### Changed
- Moved #56 (incremental compilation) from C8e to C8.5 in the roadmap

## [0.0.63] - 2026-03-04

### Changed
- **Close #52: dynamic string construction** (C8e, [#52](https://github.com/aallan/vera/issues/52)):
  All 8 string built-in operations (`string_concat`, `to_string`, `string_slice`,
  `strip`, `parse_nat`, `parse_float64`, `char_code`, `string_length`) were
  implemented in WASM codegen across v0.0.50 (PR #173) and v0.0.60 (#174),
  providing full dynamic string construction via the bump allocator. This
  documentation-only release updates limitation tables across the spec, README,
  and compiler README to reflect the resolved status.
  - `spec/11-compilation.md` limitation table: struck through #52 row
  - `spec/12-runtime.md` limitation table: struck through #52 row; also fixed
    stale #53 and #110 rows to match `spec/11-compilation.md`
  - `README.md` roadmap: struck through #52 with version tag
  - `vera/README.md` limitations table: marked #52 as done
  - `spec/09-standard-library.md`: updated Markdown section dependency note
  - GC for string memory remains tracked separately in [#51](https://github.com/aallan/vera/issues/51)
  - Unblocks [#106](https://github.com/aallan/vera/issues/106) (Show/Display)

## [0.0.62] - 2026-03-04

### Added
- **Exn\<E\> exception handler compilation** (C8e, [#53](https://github.com/aallan/vera/issues/53)):
  `handle[Exn<E>]` expressions now compile to WASM using the exception handling
  proposal (`try_table`/`catch`/`throw`). Enables compile-and-run for programs
  using exception-style error handling.
  - Exception tags declared per `Exn<E>` type parameter
  - `throw(value)` compiles to WASM `throw` instruction
  - Cross-function throws work via WASM stack unwinding
  - Nested `handle[Exn<E>]` expressions with unique labels
  - `examples/effect_handler.vera` extended with safe division via `Exn<Int>`
  - 10 new tests, 1,380 tests total
- **Renamed `SKILLS.md` to `SKILL.md`**: matches the Claude Code skill file naming
  convention. All references updated across README, AGENTS.md, CLAUDE.md,
  docs site, and vera/README.md. CHANGELOG historic references preserved.
- **Added installation instructions to `SKILL.md`**: agents consuming the skill
  file now get setup instructions (clone, venv, pip install, verify)

## [0.0.61] - 2026-03-04

### Added
- **Arrays of compound types** (C8e, [#132](https://github.com/aallan/vera/issues/132)):
  Arrays now support all element types, not just the five primitives (`Int`,
  `Nat`, `Float64`, `Bool`, `Byte`).  This includes ADT types
  (`Array<Option<Int>>`, `Array<Result<Int, String>>`), `String`
  (`Array<String>`), and nested arrays (`Array<Array<Int>>`).
  - ADT elements are stored as i32 heap pointers (4 bytes each)
  - String and nested-array elements are stored as (ptr, len) pairs (8 bytes each)
  - Chained indexing works for nested arrays (`@Array<Array<Int>>.0[0][1]`)
  - Constructor pair-type field storage fixed (e.g. `Err("msg")` with String field)
  - 17 new tests, 1,370 tests total

## [0.0.60] - 2026-03-03

### Changed
- **`parse_nat` returns `Result<Nat, String>`** (C8e, [#174](https://github.com/aallan/vera/issues/174)):
  `parse_nat` now returns `Ok(n)` on valid decimal input and `Err(msg)` on
  empty or invalid input, matching the spec (Section 9).  Previously it
  returned bare `Nat` and silently produced garbage for non-numeric strings.
  - Digit validation: bytes must be in ASCII 48–57; leading/trailing spaces
    are tolerated; empty/whitespace-only strings return `Err("empty string")`
  - Built-in Result and Option ADT layouts are now registered in codegen so
    match on `Ok`/`Err` works without a user `data Result` declaration
  - Match extraction supports String pair bindings inside ADT constructors
    (e.g. `Err(@String)`)
  - 6 new tests, 1,353 tests total

## [0.0.59] - 2026-03-03

### Fixed
- **Stale spec cross-reference** ([#141](https://github.com/aallan/vera/issues/141)):
  Updated `spec/09-standard-library.md` reference from "Section 11.16" to
  "Section 11.17" (section numbering shifted after chapter edits). Added the
  compound-type array limitation ([#132](https://github.com/aallan/vera/issues/132))
  to the limitations table in `spec/11-compilation.md`.

### Removed
- **Unused `hypothesis` dependency** ([#138](https://github.com/aallan/vera/issues/138)):
  Removed `hypothesis>=6.0` from `pyproject.toml` dev dependencies — it was
  declared but never imported in the test suite.

## [0.0.58] - 2026-03-03

### Fixed
- **`list_ops.vera` runtime failure — built-in name shadowing** (C8e, [#154](https://github.com/aallan/vera/issues/154)):
  User-defined functions now take priority over built-in intrinsics in WASM
  codegen. Previously, a user-defined `length(@List<Int> -> @Nat)` was
  incorrectly intercepted by the array-length built-in handler, producing
  invalid WASM. The fix guards all 9 built-in handlers (`length`,
  `string_length`, `string_concat`, `string_slice`, `char_code`, `parse_nat`,
  `parse_float64`, `to_string`, `strip`) so they only activate when no
  user-defined function with the same name exists.
  - `examples/list_ops.vera` now compiles and runs correctly
  - 3 new tests, 1,347 tests total

## [0.0.57] - 2026-03-03

### Added
- **Name collision detection for flat module compilation** (C8e, [#110](https://github.com/aallan/vera/issues/110)):
  When two imported modules define a function, data type, or constructor with
  the same name, the compiler now reports a clear error (E608/E609/E610) listing
  both conflicting modules. Previously, the first module registered silently won
  and the second was ignored, producing silently wrong code.
  - Provenance tracking in `_register_modules` detects collisions across functions,
    ADT types, and constructors
  - New error codes: E608 (function collision), E609 (ADT type collision),
    E610 (constructor collision)
  - Local definitions continue to shadow imported names without error
  - Same-module duplicates (module imported twice) are not treated as collisions
  - 7 new tests, 1,344 tests total

## [0.0.56] - 2026-03-03

### Added
- **Nested constructor pattern codegen** (C8e, [#131](https://github.com/aallan/vera/issues/131)):
  Match expressions with nested constructor patterns (e.g. `Cons(Some(@Int), _)`)
  now compile to WASM correctly. Previously, any sub-pattern that was a
  `ConstructorPattern` or `NullaryPattern` caused the entire function to be
  silently skipped.
  - `_collect_nested_tag_checks` recursively emits tag comparisons for nested
    constructors, AND-chained into the arm condition
  - `_extract_constructor_fields` recursively loads nested field pointers and
    binds their sub-patterns
  - `_sub_pattern_wasm_type` helper resolves WASM types for offset computation
  - `examples/pattern_matching.vera` `first_some` now compiles and runs
  - 5 new tests (nested Some, nested None, multi-field, different arms, fallthrough)
  - 1,337 tests total

## [0.0.55] - 2026-03-03

### Added
- **Bidirectional type checking** (C8d, [#55](https://github.com/aallan/vera/issues/55)):
  Adds local type inference via an `expected` parameter threaded through
  expression synthesis. Nullary constructors of parameterised ADTs (`None`
  for `Option<T>`, `Nil` for `List<T>`) now resolve their TypeVars from
  context — return types, let bindings, if/match branches, and function
  arguments.
  - `_synth_expr` gains optional `expected: Type | None` parameter
  - Constructors resolve unresolved TypeVars from expected type in
    `_ctor_result_type` and `_check_constructor_call`
  - Nested constructors (`Some(None)` for `Option<Option<Int>>`) resolve
    via field-type propagation
  - Function call arguments with TypeVars are re-synthesised with the
    substituted parameter type as expected
  - If/match branches with TypeVars are re-synthesised using the concrete
    branch as expected, replacing the previous `contains_typevar` guards
  - `_check_fn` passes `expected=return_type` to body synthesis, removing
    the `contains_typevar` workaround guard from v0.0.53
  - No changes to function signatures, parser, AST, or spec
  - 12 new tests (TestBidirectionalInference)
  - 1,332 tests total

## [0.0.54] - 2026-03-02

### Added
- **Effect row subtyping and call-site effect checking** (C8d, [#21](https://github.com/aallan/vera/issues/21)):
  Implements the subeffecting rules from Spec Section 7.8: a function with fewer
  effects can be used where more effects are expected.
  - `is_effect_subtype()` function in `types.py` encodes subset semantics
    for effect rows (`effects(pure) <: effects(<IO>) <: effects(<IO, State<Int>>)`)
  - `FunctionType` subtyping now includes effect covariance: a pure function
    can be passed where `fn(A -> B) effects(<IO>)` is expected
  - Call-site check in `checker/calls.py`: calling a function whose effects
    exceed the caller's context is now an error (E125)
  - Handler bodies unaffected: handlers temporarily add their effect to the
    context before checking the body, then discharge it
  - Effect row variables (`forall<E>`) are permissive pending #55
  - `effects_equal()` function added for structural effect row comparison
  - `types_equal()` updated to compare effects in `FunctionType`
  - 20 new tests (13 unit tests, 7 integration tests)
  - 1,320 tests total

## [0.0.53] - 2026-03-02

### Changed
- **TypeVar subtyping is no longer permissive** (C8d, [#20](https://github.com/aallan/vera/issues/20)):
  Removes the blanket `TypeVar <: anything` rule from `is_subtype`.
  TypeVars now only match themselves via reflexive equality.
  - Generic function bodies are properly checked: returning a `T` where a
    concrete `Int` is expected is now an error (E121)
  - Call sites unaffected: existing inference + substitution resolves TypeVars
    before subtype checks; unresolved TypeVars are skipped
  - Nullary constructors of parameterised ADTs (e.g. `None` for `Option<T>`)
    produce types with unresolved TypeVars — these are tolerated at call sites
    and in non-generic function bodies
  - `contains_typevar` utility added to `types.py`
  - 13 new tests (5 subtyping unit tests, 3 rejection tests, 5 regression tests)
  - 1,300 tests total

## [0.0.52] - 2026-03-02

### Added
- **Mutual recursion termination verification** (C8c, [#45](https://github.com/aallan/vera/issues/45)):
  Verifies `decreases` clauses across mutually recursive `where`-block function groups,
  promoting the last E525 contract in `mutual_recursion.vera` from Tier 3 to Tier 1.
  - Where-block functions now have their contracts verified (requires, ensures, decreases)
  - Cross-function measure checking: callee measure evaluated in callee parameter env
  - Verification rate: 96 T1, 3 T3, 99 total (97.0% static)
  - 4 new verifier tests, 1,287 tests total

## [0.0.51] - 2026-03-02

### Added
- **Expand SMT decidable fragment** (C4/C6, [#13](https://github.com/aallan/vera/issues/13)):
  Promotes 4 Tier 3 (runtime) contracts to Tier 1 (statically verified), bringing
  the verification rate from 91.7% to 95.8% across all 15 examples (92 T1, 4 T3, 96 total).
  - **Match expression + ADT constructor Z3 translation**: `MatchExpr`, `NullaryConstructor`,
    and `ConstructorCall` are now translated to Z3 using `z3.Datatype` sorts, with pattern
    conditions mapped to recognizers and field bindings mapped to accessors.
  - **Termination verification for `decreases` clauses**: Simple `Nat` decreases (factorial)
    and structural ADT decreases (`List<T>` length/sum) are now verified via Z3. Uses a
    rank function with universal axioms for structural subterm ordering.
  - ADT sort creation with type parameter substitution and self-reference handling
  - Per-sort `length()` uninterpreted functions (supports both Int and ADT domains)
  - Recursive call collector with Z3 path conditions and slot env tracking
  - Verifier now populates constructor info for SMT translation
  - 16 new verifier tests across 3 test classes
  - 1,283 tests total

### Remaining Tier 3 contracts (4)
- 2 x E520: Generic type parameters in `generics.vera` (unfixable — fundamental SMT limitation)
- 1 x E522: `old`/`new` state modeling in `increment.vera` (deferred — requires symbolic effect execution)
- 1 x E525: Mutual recursion in `mutual_recursion.vera` (deferred — requires cross-function measure reasoning)

## [0.0.50] - 2026-03-02

### Added
- **Eight string/conversion built-in operations** (C8e, [#134](https://github.com/aallan/vera/issues/134), [#52](https://github.com/aallan/vera/issues/52)):
  First external contribution by [@rlseaman](https://github.com/rlseaman) in PR [#173](https://github.com/aallan/vera/pull/173).
  - `string_length(@String -> @Nat)` — byte length of a string
  - `string_concat(@String, @String -> @String)` — concatenation
  - `string_slice(@String, @Nat, @Nat -> @String)` — substring extraction
  - `char_code(@String, @Int -> @Nat)` — ASCII code at index
  - `parse_nat(@String -> @Nat)` — decimal string to natural number
  - `parse_float64(@String -> @Float64)` — decimal string to float
  - `to_string(@Int -> @String)` — integer to decimal string
  - `strip(@String -> @String)` — trim leading/trailing whitespace (zero-copy)
  - New example: `examples/string_ops.vera` (15 examples total)
  - 52 new tests: 10 type checker + 42 codegen/runtime
  - Uses bump allocator (`$alloc`); GC deferred to [#51](https://github.com/aallan/vera/issues/51)
  - `parse_nat` returns bare `Nat` pending [#174](https://github.com/aallan/vera/issues/174) (spec requires `Result<Nat, String>`)
  - 1,267 tests total

## [0.0.49] - 2026-03-01

### Added
- **Register `Diverge` as built-in effect** (C8c, [#136](https://github.com/aallan/vera/issues/136)):
  `effects(<Diverge>)` now resolves to the spec-defined marker effect
  (Chapter 7, Section 7.7.3). Diverge has no operations — it signals that a
  function may not terminate. Precursor to #45 (termination verification).

## [0.0.48] - 2026-03-01

### Added
- **Improve WASM translation test coverage** (C8.5, [#156](https://github.com/aallan/vera/issues/156)):
  - New `tests/test_wasm_coverage.py` with 109 tests targeting coverage gaps in `vera/wasm/`
  - Direct unit tests for `helpers.py` pure functions (`wasm_type`, `wasm_type_or_none`, `is_compilable_type`, element helpers)
  - Full pipeline tests for `inference.py` deep branches (block result type inference, Vera type inference, expression type propagation)
  - Closure free-variable walking coverage (`closures.py`): capture in binary, if, call, let, match contexts
  - Operator edge cases: Float64 comparisons, Byte unsigned comparisons, Boolean implies, AND/OR
  - Data/match coverage: nullary constructors, wildcard patterns, Bool/Int patterns, Option<T>
  - Effect handler coverage: State<Int> init/get/put/increment patterns
  - `wasm/` coverage improved from 79% to 86% (helpers.py 62%→96%, closures.py 72%→92%, inference.py 71%→74%)
  - Overall compiler coverage improved from 87% to 88% (6,861 stmts, 819 missed)
  - 1,209 tests (up from 1,100)

### Fixed
- Fixed approximate (`~`) coverage values for `tester.py` in TESTING.md (335/51/85%, not ~350/~60/~83%)

## [0.0.47] - 2026-03-01

### Added
- **`vera test` contract-driven testing** (C8b, [#79](https://github.com/aallan/vera/issues/79)):
  - New `vera test` command generates inputs from `requires()` clauses via Z3 and executes compiled WASM to validate `ensures()` at runtime
  - Z3-based input generation for Int, Nat, Bool parameters with boundary value seeding
  - Tier classification: Tier 1 functions reported as "verified", Tier 3 functions exercised with generated inputs, unsupported/generic functions skipped
  - `--json` flag for machine-readable test results
  - `--trials N` flag to configure trial count per function (default 100)
  - `--fn name` flag to test a single function
  - New `vera/tester.py` module (~530 lines) with public `test()` API
  - E7xx error code range for testing diagnostics (E700-E702)
  - 24 new tests: 13 unit tests in `test_tester.py`, 11 CLI tests in `test_cli.py`
  - 1,100 tests (up from 1,076)

## [0.0.46] - 2026-03-01

### Changed
- **Decompose `codegen.py` into `codegen/` mixin package** (C8a, [#155](https://github.com/aallan/vera/issues/155)):
  - Split the 2,140-line `codegen.py` monolith into 11 focused modules following the mixin pattern from `checker/` and `wasm/`
  - New modules: `api.py`, `core.py`, `modules.py`, `registration.py`, `monomorphize.py`, `functions.py`, `closures.py`, `contracts.py`, `assembly.py`, `compilability.py`
  - Added 5 coverage gap tests reaching defensive error paths (E600, E601, E605, E606, unknown module calls)
  - Split the 4,834-line `test_codegen.py` into 6 focused test files mirroring the module structure
  - 1,076 tests (up from 1,071)
  - Completes C8a refactoring: all three compiler monoliths (`checker.py`, `wasm.py`, `codegen.py`) are now mixin packages

## [0.0.45] - 2026-02-28

### Added
- **`vera fmt` canonical code formatter** ([#75](https://github.com/aallan/vera/issues/75)):
  - New `vera fmt` command formats Vera source to the canonical form defined in Spec §1.8
  - `--write` flag for in-place formatting, `--check` flag for CI (exit 1 if non-canonical)
  - AST-based formatter with pre-pass comment extraction and reattachment
  - Precedence-aware parenthesization for binary expressions
  - All 10 formatting rules enforced: indentation, braces, commas, operators, semicolons, parentheses, contracts, one-per-line, no trailing whitespace, final newline
  - New `vera/formatter.py` module (1,018 lines)
  - 75 new tests (1,071 total, up from 996)
  - All 14 examples reformatted to canonical form
  - SKILLS.md and spec examples updated to canonical form ([#150](https://github.com/aallan/vera/issues/150))

## [0.0.44] - 2026-02-28

### Changed
- **Module-qualified call syntax uses `::` delimiter** (C8b, [#95](https://github.com/aallan/vera/issues/95)):
  - Module-qualified calls now use `::` between module path and function name: `vera.math::abs(42)`
  - Resolves LALR(1) grammar ambiguity where `module_path` greedily consumed the function name
  - Old dot syntax (`vera.math.abs(42)`) is rejected with a targeted "did you mean `::` ?" error (E008)
  - Added `format_expr` support for `ModuleCall` AST nodes
  - Updated spec chapters 8 and 10, examples, and all documentation
  - 12 new tests (996 total, up from 984)

## [0.0.43] - 2026-02-27

### Added
- **Stable error code taxonomy for diagnostics** (C8b, [#80](https://github.com/aallan/vera/issues/80)):
  - Every diagnostic now carries a stable error code (`E001`–`E607`)
  - Codes are grouped by compiler phase: parse (E0xx), type check (E1xx–E3xx), verification (E5xx), codegen (E6xx)
  - 80 error codes across 8 files, covering all 77+ diagnostic emission sites
  - `Diagnostic` dataclass gains `error_code: str` field
  - `format()` output shows `[Exxx]` prefix when code is present
  - `to_dict()` includes `error_code` in JSON output
  - Central `ERROR_CODES` registry in `vera/errors.py` maps codes to short descriptions
  - 13 new tests (984 total, up from 971)

## [0.0.42] - 2026-02-27

### Changed
- **Informative runtime contract violation messages** (C8b, [#112](https://github.com/aallan/vera/issues/112)):
  - Contract violations now report which function, contract kind, and expression failed
  - Before: `Runtime contract violation: error while executing at wasm backtrace: ... wasm trap: wasm unreachable instruction executed`
  - After: `Precondition violation in clamp(@Int, @Int, @Int -> @Int)\n  requires(@Int.1 <= @Int.2) failed`
  - New `vera.contract_fail` host import passes pre-interned message strings from WASM to the runtime before trapping
  - Added `format_expr()`, `format_type_expr()`, `format_fn_signature()` to `vera/ast.py` for AST-to-source reconstruction
  - 20 new tests (971 total, up from 951)

## [0.0.41] - 2026-02-27

### Changed
- **Decompose wasm.py into wasm/ package** (C8a, [#100](https://github.com/aallan/vera/issues/100)):
  - Split 2,344-line monolith into 8 focused modules using mixin-based composition
  - `context.py` (369) — composed WasmContext class, expression dispatcher, block translation
  - `helpers.py` (211) — WasmSlotEnv, StringPool, type mapping, array element helpers
  - `inference.py` (527) — type inference, slot/type utilities, operator lookup tables
  - `operators.py` (430) — binary/unary operators, if, quantifiers, assert/assume, old/new
  - `calls.py` (223) — function calls, generic resolution, effect handlers
  - `closures.py` (248) — closures, anonymous functions, free variable analysis
  - `data.py` (460) — constructors, match expressions, arrays, indexing
  - Zero test changes — public API (`WasmContext`, `WasmSlotEnv`, `StringPool`, `wasm_type`) unchanged

## [0.0.40] - 2026-02-27

### Changed
- **Decompose checker.py into checker/ package** (C8a, [#99](https://github.com/aallan/vera/issues/99)):
  - Split 2,043-line monolith into 8 focused modules using mixin-based composition
  - `core.py` (349) — TypeChecker class, orchestration, diagnostics, contracts
  - `resolution.py` (190) — AST TypeExpr → semantic Type, type inference
  - `modules.py` (153) — cross-module registration (C7b/C7c)
  - `registration.py` (138) — Pass 1 forward declarations
  - `expressions.py` (530) — expression synthesis, operators, statements
  - `calls.py` (390) — function, constructor, and module-qualified calls
  - `control.py` (439) — if/match, patterns, exhaustiveness, effect handlers
  - Zero test changes — public API (`typecheck()`) unchanged

## [0.0.39] - 2026-02-27

### Added
- **Spec Chapter 8: Modules** (C7f):
  - New specification chapter covering module declarations, imports, visibility, name resolution, module resolution algorithm, cross-module type checking, verification, and compilation
  - Formal semantics for the flattening compilation strategy, transitive resolution, circular import detection, and shadowing rules
  - Clarification that type aliases and effect declarations are module-local (not importable)
  - Complete worked example with `vera/math.vera`, `vera/collections.vera`, and `modules.vera`
  - Limitations section tracking #95 (LALR grammar), #110 (name collisions), and future extensions

### Changed
- **Roadmap restructured**: C7 collapsed as complete (v0.0.31-v0.0.39), C8 defined as the polish phase with sub-phases C8a-C8e grouping all open issues by area
- Cross-references added from spec Chapters 5, 10, 11, and 12 pointing to Chapter 8
- `SKILLS.md` module section updated with type-alias/effect locality note and spec reference
- `vera/README.md` limitations table updated: module system marked complete
- `docs/index.html` feature grid updated with "Module system" entry
- README project status: Chapter 8 status changed from "Not started" to "Draft"

## [0.0.38] - 2026-02-27

### Added
- **Multi-module codegen** (C7e — [#50](https://github.com/aallan/vera/issues/50)):
  - Imported function bodies are now compiled into the WASM module via flattening
  - `vera compile` and `vera run` work with multi-module programs (previously blocked by C7e guard rail)
  - Private helper functions called by imported public functions are compiled automatically
  - `ModuleCall` nodes are desugared to flat `FnCall` in WASM translation (including pipe operator)
  - Guard rail updated: only truly undefined functions produce errors; imported functions pass through
  - `modules.vera` example now compiles and runs end-to-end
  - Spec Chapter 11 updated with cross-module compilation section (11.16)
- 8 new cross-module codegen tests (951 total, up from 943)

### Changed
- Error messages for undefined functions no longer reference C7e; instead they report "not found in any imported module"

## [0.0.37] - 2026-02-27

### Added
- **Cross-module contract verification** (C7d — [#14](https://github.com/aallan/vera/issues/14)):
  - Imported function preconditions are now checked at call sites by the SMT solver
  - Imported function postconditions are assumed, allowing callers to rely on them
  - Chained imported calls compose correctly (e.g. `abs(max(x, y)) >= 0`)
  - Only `public` functions from imported modules are available for verification
  - Selective imports are respected — only named imports are registered
  - Refactored SMT call translation into shared `_translate_call_with_info` for both local and cross-module calls
  - Added `ModuleCall` handling in SMT translator (including pipe operator desugaring)
  - `modules.vera` example now verifies `abs_max` postcondition (`ensures(@Int.result >= 0)`) at Tier 1
- 8 new cross-module verification tests (943 total, up from 935)

## [0.0.36] - 2026-02-27

### Fixed
- **WASM export visibility gate** (C7c — [#107](https://github.com/aallan/vera/pull/107)):
  - Only `public` functions are now exported as WASM entry points; `private` functions compile but are not accessible via `vera run`
  - Both the `exports` list and the WAT-level `(export ...)` annotation are gated on visibility
  - Monomorphized generic functions inherit visibility from the original generic declaration
- **Improved "no exports" error** ([#107](https://github.com/aallan/vera/pull/107)):
  - `vera run` on a file with no public functions now lists all declared functions with their visibility, any compilation warnings, and suggests making a function public
  - `vera run --fn <name>` targeting a private function gives a specific "declared private" error with fix suggestion
  - Both plain-text and `--json` output modes supported
- **Runnable examples** ([#107](https://github.com/aallan/vera/pull/107)):
  - All 13 non-module examples now have `public` test entry points (e.g. `vera run examples/factorial.vera --fn test_factorial`)
  - Entry-point functions in examples, README, SKILLS.md, spec chapters 5-7, and docs site updated from `private` to `public`
- 3 new tests (935 total, up from 932)

### Added
- **Roadmap**: [#106](https://github.com/aallan/vera/issues/106) (universal to-string conversion / Show for all types) added to codegen gaps

## [0.0.35] - 2026-02-27

### Fixed
- **Cross-module codegen guard rail** (C7c — partial [#14](https://github.com/aallan/vera/issues/14)):
  - `vera compile` and `vera run` on programs with imported functions now produce a proper Vera diagnostic instead of a raw wasmtime error (`unknown func: failed to find name $max`)
  - Pre-compilation AST scan detects `FnCall` to undefined names and `ModuleCall` nodes before WAT generation, emitting LLM-oriented diagnostics with rationale, fix suggestion, and spec reference
  - Belt-and-braces guard in `wasm.py` `_translate_call()` and explicit `ModuleCall` handler prevent any undefined call from reaching wasmtime
  - Diagnostic directs users to `vera check` / `vera verify` for multi-module programs until C7e (multi-module codegen) is implemented
- **Bare `fn`/`data` in error messages and docs** (merged in [#103](https://github.com/aallan/vera/pull/103)):
  - Fixed remaining bare `fn` declarations in compiler error message fix suggestions (`vera/errors.py`), spec chapters, README, AGENTS.md, `vera/README.md`, and `tests/test_resolver.py`
- **`vera run` parameter mismatch diagnostic**: when a function expects arguments but none are provided, the error now names the function, lists available exports, and shows the correct `--fn ... -- <args>` syntax (previously showed a raw "Runtime contract violation: too few parameters" wasmtime error)
- 5 new tests (932 total, up from 927)

## [0.0.34] - 2026-02-27

### Added
- **Visibility enforcement** (C7c — partial [#14](https://github.com/aallan/vera/issues/14)):
  - Every top-level `fn` and `data` declaration now requires an explicit `public` or `private` annotation — no implicit default, enforcing design principle 3 ("one canonical form")
  - Cross-module access control: only `public` declarations are importable; private names produce targeted "is private" errors with fix suggestions
  - Selective imports of private names caught at import site with clear diagnostics
  - Wildcard imports (`import m;`) automatically filter to public declarations only
  - Constructor visibility derived from parent ADT — private ADT means private constructors
  - `FunctionInfo` and `AdtInfo` now carry a `visibility` field threaded through the registration pipeline
  - Updated all 14 examples, all test inline sources, spec chapters, README, SKILLS.md, and docs site — no bare `fn`/`data` declarations remain anywhere in the repo
- 13 new tests (927 total, up from 914)

## [0.0.33] - 2026-02-27

### Removed
- **`Float` type alias** (closes [#76](https://github.com/aallan/vera/issues/76)): `Float` is no longer accepted as a type name — use `Float64` exclusively
  - Enforces design principle 3 ("one canonical form") from spec §1.8
  - Removed `"Float": FLOAT64` alias from `vera/types.py` PRIMITIVES dict
  - Simplified ~12 dual-name checks in `wasm.py` and `codegen.py`
  - Updated `examples/pattern_matching.vera` to use `Float64`
  - Updated spec chapters 4 and 11 to remove `Float` references
  - Decomposition issues tracked: [#99](https://github.com/aallan/vera/issues/99) (checker.py), [#100](https://github.com/aallan/vera/issues/100) (wasm.py)
- 1 new test (914 total, up from 913)

## [0.0.32] - 2026-02-27

### Added
- **Cross-module type checking** (C7b — partial [#14](https://github.com/aallan/vera/issues/14)):
  - Imported function signatures are now registered and type-checked: arity checking, argument type checking, generic inference, and effect propagation all work across module boundaries
  - **Bare calls**: `import vera.math(abs); abs(-5)` resolves `abs` from the imported module — immediately usable from source files
  - **Module-qualified calls**: `ModuleCall` AST nodes type-checked against imported module declarations (grammar limitation [#95](https://github.com/aallan/vera/issues/95) prevents parsing `path.fn(args)` from source)
  - Selective import enforcement: `import m(f)` restricts available names to `f` only; calls to unimported names produce errors with fix suggestions
  - Wildcard imports: `import m;` makes all module declarations available
  - Local declarations shadow imported names (standard rule)
  - Imported ADT constructors available via bare calls: `import col(List); Cons(1, Nil)` works
  - Module declarations registered in isolated `TypeChecker` instances to avoid namespace pollution
  - `examples/modules.vera` now exercises bare cross-module calls (`abs`, `max` from `vera.math`)
- LALR grammar limitation for module-qualified call syntax tracked as [#95](https://github.com/aallan/vera/issues/95)
- **Project website** ([veralang.dev](https://veralang.dev)): single-page site deployed via GitHub Pages ([#81](https://github.com/aallan/vera/pull/81))
- 13 new tests (913 total, up from 900)

## [0.0.31] - 2026-02-26

### Added
- **Module resolution** (C7a — partial [#14](https://github.com/aallan/vera/issues/14), [#50](https://github.com/aallan/vera/issues/50)): `import` paths now resolve to source files on disk
  - New `vera/resolver.py`: `ModuleResolver` maps import paths (e.g., `vera.math`) to `.vera` files relative to the importing file or project root
  - `ResolvedModule` dataclass: path tuple, file path, parsed Program AST, source text
  - Parse cache: each imported module parsed at most once per compilation session
  - Circular import detection via in-progress tracking set
  - Resolver wired into all CLI commands (`check`, `verify`, `compile`, `run`)
  - `typecheck()` accepts optional `resolved_modules` parameter; improved diagnostic messages distinguish "module resolved but type merging not yet implemented (C7b)" from "module not found"
  - `verify()` accepts `resolved_modules` for forward-compatibility with C7d
  - Stub modules `examples/vera/math.vera` and `examples/vera/collections.vera` for the `modules.vera` example
- README restructured: C6/C6.5 collapsed sections moved above "What's next"; new "Longer term" section with all 19 open issues linked by category
- 20 new tests (900 total, up from 880)

## [0.0.30] - 2026-02-26

### Added
- **old()/new() state expressions in postconditions** (C6.5f — closes [#70](https://github.com/aallan/vera/issues/70)): postconditions containing `old(State<T>)` and `new(State<T>)` now compile to WASM runtime checks
  - `old(State<T>)` snapshots the state value at function entry into a temp local
  - `new(State<T>)` reads the current state value at postcondition check time via `state_get`
  - `_snapshot_old_state()` in codegen.py walks ensures clauses to detect `OldExpr` nodes and emits snapshot instructions
  - `WasmContext._translate_old_expr()` and `_translate_new_expr()` handle the AST→WAT translation
  - Snapshot is only emitted when ensures clauses actually reference `old()` (trivial contracts skip it)
  - Completes the C6.5 codegen cleanup phase
- README restructured: C7 (Module System) is now the "What's next" section with sub-phase plan; C6.5 and C6 are collapsed
- 6 new codegen tests (880 total, up from 874)

## [0.0.29] - 2026-02-26

### Added
- **String and Array types in function signatures** (C6.5e — closes [#69](https://github.com/aallan/vera/issues/69)): functions with `String` or `Array<T>` parameters and return types now compile to WASM
  - Each String/Array parameter expands to two consecutive `i32` WASM parameters (pointer and length)
  - String/Array return types use WASM multi-value return `(result i32 i32)`
  - `_type_expr_to_wasm_type()` returns `"i32_pair"` sentinel instead of `"unsupported"` for String/Array
  - Generalised `_is_pair_type_name()` helper for String and Array<T> across slot refs, let bindings, and drop logic
  - `execute()` handles multi-value (list) returns from wasmtime
  - Postcondition checks skipped for pair return types (single-local save/restore pattern incompatible with two-value results)
  - `if` and `match` blocks emit `(result i32 i32)` for pair-typed branches
  - Functions previously skipped in `examples/pattern_matching.vera` and `examples/quantifiers.vera` now compile
- 8 new codegen tests (874 total, up from 866)

## [0.0.28] - 2026-02-26

### Added
- **Float64 modulo compilation** (C6.5d — closes [#46](https://github.com/aallan/vera/issues/46)): `%` on Float64 operands now compiles to WASM via the decomposition `a % b = a - trunc(a / b) * b`
  - Uses `f64.trunc` (truncation toward zero), matching C `fmod` semantics and consistent with `i64.rem_s` for integer modulo
  - Multi-instruction WAT sequence with temporary locals (same pattern as array indexing, closures)
  - WASM has no native `f64.rem` instruction; this was previously unsupported (function silently skipped)
- 4 new codegen tests: exact division, remainder, negative operand, parameterized (866 total, up from 862)

## [0.0.27] - 2026-02-26

### Added
- **Pipe operator compilation** (C6.5c — closes [#44](https://github.com/aallan/vera/issues/44)): `a |> f(x, y)` now compiles to WASM and verifies via Z3, desugaring to `f(a, x, y)` in both backends
  - WASM codegen: intercept `BinOp.PIPE` in `_translate_binary()`, construct synthetic `FnCall`, delegate to `_translate_call()`
  - SMT verifier: same desugaring pattern in `_translate_binary()`
  - No grammar, AST, transformer, or checker changes needed (pipe already parsed and type-checked)
- 4 new tests: 3 codegen, 1 verifier (862 total, up from 858)

## [0.0.26] - 2026-02-26

### Added
- **Handler `with` clause** (C6.5b — closes [#72](https://github.com/aallan/vera/issues/72)): handler operation clauses can now update handler state via `with @T = expr` after the clause body
  - Grammar: `with_clause` rule added to `handler_clause`
  - AST: `state_update` field on `HandlerClause`
  - Type checker: validates state update type matches handler state declaration
  - No codegen changes (handler clauses remain specifications per spec 11.11.2)
- 6 new tests: 2 parser, 4 checker (858 total, up from 852)

## [0.0.25] - 2026-02-26

### Fixed
- **`resume` recognized in handler scope** (C6.5a — closes [#74](https://github.com/aallan/vera/issues/74)): the type checker now binds `resume` as a function in handler clause bodies with the correct type (takes operation return type, returns Unit), eliminating spurious "Unresolved function 'resume'" warnings
- `effect_handler.vera` example now type-checks cleanly (moved from warn to clean examples)

### Added
- `_check_clean()` test helper asserts zero errors AND zero warnings
- 3 new tests: `test_resume_wrong_arg_type`, `test_resume_wrong_arity`, `test_resume_outside_handler` (852 total, up from 849)

## [0.0.24] - 2026-02-26

### Added
- **Spec Chapter 9: Standard Library** (C6n): documents all built-in types (`Option<T>`, `Result<T, E>`), collections (`Array<T>`), effects (`IO`, `State<T>`), and functions (`length`, future `similarity`); includes future features (Http, Async, Inference effects; Json, Decimal types; Set, Map collections; Abilities) with issue cross-references
- **Spec Chapter 12: Runtime and Execution** (C6n — closes [#63](https://github.com/aallan/vera/issues/63)): documents WASM module structure, wasmtime host runtime, host function bindings (IO.print, State\<T\>), linear memory model, bump allocator, execution flow, argument passing, error handling, and runtime limitations

### Changed
- **Spec Chapter 0**: condensed Section 0.8 design notes to a cross-reference table pointing to Chapter 9 sections (previously contained full feature designs inline)

## [0.0.23] - 2026-02-26

### Added
- **Refinement type alias compilation** (C6m): type aliases like `PosInt`, `Percentage`, `Nat` that resolve through refinement types now compile to their base WASM type
  - `_type_expr_to_wasm_type()` in codegen.py now recurses on any alias type (not just FnType)
  - `_resolve_base_type_name()` helper in wasm.py follows alias chains through refinement types to the underlying primitive (e.g. `PosInt` → `Int` → `i64`)
  - Applied uniformly to parameter types, return types, let bindings, and slot references
- **Spec Section 11.15**: new "Refinement Type Alias Compilation" section
- **Codegen tests**: 8 new tests — safe_divide, to_percentage (clamp low/pass/high), refined let bindings, refined return in expr, WAT exports (849 total, up from 841)

## [0.0.22] - 2026-02-26

### Added
- **Quantifier compilation** (C6l): compile `forall`/`exists` as runtime loops with short-circuit evaluation
  - Counted loop over `[0, domain)` with predicate inlined (no closure overhead)
  - `forall` returns true if all iterations satisfy predicate, short-circuits on first false
  - `exists` returns true if any iteration satisfies predicate, short-circuits on first true
  - Empty domain: `forall` → true (vacuously), `exists` → false
- **Assert compilation** (C6l): `assert(expr)` compiles to conditional `unreachable` trap
- **Assume compilation** (C6l): `assume(expr)` compiles to no-op at runtime (verifier-only construct)
- **Spec Sections 11.13-11.14**: new "Quantifier Compilation" and "Assert and Assume Compilation" sections
- **Codegen tests**: 20 new tests — assert/assume, forall, exists, WAT inspection (841 total, up from 821)

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

[Unreleased]: https://github.com/aallan/vera/compare/v0.0.115...HEAD
[0.0.115]: https://github.com/aallan/vera/compare/v0.0.114...v0.0.115
[0.0.114]: https://github.com/aallan/vera/compare/v0.0.113...v0.0.114
[0.0.113]: https://github.com/aallan/vera/compare/v0.0.112...v0.0.113
[0.0.112]: https://github.com/aallan/vera/compare/v0.0.111...v0.0.112
[0.0.111]: https://github.com/aallan/vera/compare/v0.0.110...v0.0.111
[0.0.110]: https://github.com/aallan/vera/compare/v0.0.109...v0.0.110
[0.0.109]: https://github.com/aallan/vera/compare/v0.0.108...v0.0.109
[0.0.108]: https://github.com/aallan/vera/compare/v0.0.107...v0.0.108
[0.0.107]: https://github.com/aallan/vera/compare/v0.0.106...v0.0.107
[0.0.106]: https://github.com/aallan/vera/compare/v0.0.105...v0.0.106
[0.0.105]: https://github.com/aallan/vera/compare/v0.0.104...v0.0.105
[0.0.104]: https://github.com/aallan/vera/compare/v0.0.103...v0.0.104
[0.0.103]: https://github.com/aallan/vera/compare/v0.0.102...v0.0.103
[0.0.102]: https://github.com/aallan/vera/compare/v0.0.101...v0.0.102
[0.0.101]: https://github.com/aallan/vera/compare/v0.0.100...v0.0.101
[0.0.100]: https://github.com/aallan/vera/compare/v0.0.99...v0.0.100
[0.0.99]: https://github.com/aallan/vera/compare/v0.0.98...v0.0.99
[0.0.98]: https://github.com/aallan/vera/compare/v0.0.97...v0.0.98
[0.0.97]: https://github.com/aallan/vera/compare/v0.0.96...v0.0.97
[0.0.96]: https://github.com/aallan/vera/compare/v0.0.95...v0.0.96
[0.0.95]: https://github.com/aallan/vera/compare/v0.0.94...v0.0.95
[0.0.94]: https://github.com/aallan/vera/compare/v0.0.93...v0.0.94
[0.0.93]: https://github.com/aallan/vera/compare/v0.0.92...v0.0.93
[0.0.92]: https://github.com/aallan/vera/compare/v0.0.91...v0.0.92
[0.0.91]: https://github.com/aallan/vera/compare/v0.0.90...v0.0.91
[0.0.90]: https://github.com/aallan/vera/compare/v0.0.89...v0.0.90
[0.0.89]: https://github.com/aallan/vera/compare/v0.0.88...v0.0.89
[0.0.88]: https://github.com/aallan/vera/compare/v0.0.87...v0.0.88
[0.0.87]: https://github.com/aallan/vera/compare/v0.0.86...v0.0.87
[0.0.86]: https://github.com/aallan/vera/compare/v0.0.85...v0.0.86
[0.0.85]: https://github.com/aallan/vera/compare/v0.0.84...v0.0.85
[0.0.84]: https://github.com/aallan/vera/compare/v0.0.83...v0.0.84
[0.0.83]: https://github.com/aallan/vera/compare/v0.0.82...v0.0.83
[0.0.82]: https://github.com/aallan/vera/compare/v0.0.81...v0.0.82
[0.0.81]: https://github.com/aallan/vera/compare/v0.0.80...v0.0.81
[0.0.80]: https://github.com/aallan/vera/compare/v0.0.79...v0.0.80
[0.0.79]: https://github.com/aallan/vera/compare/v0.0.78...v0.0.79
[0.0.78]: https://github.com/aallan/vera/compare/v0.0.77...v0.0.78
[0.0.77]: https://github.com/aallan/vera/compare/v0.0.76...v0.0.77
[0.0.76]: https://github.com/aallan/vera/compare/v0.0.75...v0.0.76
[0.0.75]: https://github.com/aallan/vera/compare/v0.0.74...v0.0.75
[0.0.74]: https://github.com/aallan/vera/compare/v0.0.73...v0.0.74
[0.0.73]: https://github.com/aallan/vera/compare/v0.0.72...v0.0.73
[0.0.72]: https://github.com/aallan/vera/compare/v0.0.71...v0.0.72
[0.0.71]: https://github.com/aallan/vera/compare/v0.0.70...v0.0.71
[0.0.70]: https://github.com/aallan/vera/compare/v0.0.69...v0.0.70
[0.0.69]: https://github.com/aallan/vera/compare/v0.0.68...v0.0.69
[0.0.68]: https://github.com/aallan/vera/compare/v0.0.67...v0.0.68
[0.0.67]: https://github.com/aallan/vera/compare/v0.0.66...v0.0.67
[0.0.66]: https://github.com/aallan/vera/compare/v0.0.65...v0.0.66
[0.0.65]: https://github.com/aallan/vera/compare/v0.0.64...v0.0.65
[0.0.64]: https://github.com/aallan/vera/compare/v0.0.63...v0.0.64
[0.0.63]: https://github.com/aallan/vera/compare/v0.0.62...v0.0.63
[0.0.62]: https://github.com/aallan/vera/compare/v0.0.61...v0.0.62
[0.0.61]: https://github.com/aallan/vera/compare/v0.0.60...v0.0.61
[0.0.60]: https://github.com/aallan/vera/compare/v0.0.59...v0.0.60
[0.0.59]: https://github.com/aallan/vera/compare/v0.0.58...v0.0.59
[0.0.58]: https://github.com/aallan/vera/compare/v0.0.57...v0.0.58
[0.0.57]: https://github.com/aallan/vera/compare/v0.0.56...v0.0.57
[0.0.56]: https://github.com/aallan/vera/compare/v0.0.55...v0.0.56
[0.0.55]: https://github.com/aallan/vera/compare/v0.0.54...v0.0.55
[0.0.54]: https://github.com/aallan/vera/compare/v0.0.53...v0.0.54
[0.0.53]: https://github.com/aallan/vera/compare/v0.0.52...v0.0.53
[0.0.52]: https://github.com/aallan/vera/compare/v0.0.51...v0.0.52
[0.0.51]: https://github.com/aallan/vera/compare/v0.0.50...v0.0.51
[0.0.50]: https://github.com/aallan/vera/compare/v0.0.49...v0.0.50
[0.0.49]: https://github.com/aallan/vera/compare/v0.0.48...v0.0.49
[0.0.48]: https://github.com/aallan/vera/compare/v0.0.47...v0.0.48
[0.0.47]: https://github.com/aallan/vera/compare/v0.0.46...v0.0.47
[0.0.46]: https://github.com/aallan/vera/compare/v0.0.45...v0.0.46
[0.0.45]: https://github.com/aallan/vera/compare/v0.0.44...v0.0.45
[0.0.44]: https://github.com/aallan/vera/compare/v0.0.43...v0.0.44
[0.0.43]: https://github.com/aallan/vera/compare/v0.0.42...v0.0.43
[0.0.42]: https://github.com/aallan/vera/compare/v0.0.41...v0.0.42
[0.0.41]: https://github.com/aallan/vera/compare/v0.0.40...v0.0.41
[0.0.40]: https://github.com/aallan/vera/compare/v0.0.39...v0.0.40
[0.0.39]: https://github.com/aallan/vera/compare/v0.0.38...v0.0.39
[0.0.38]: https://github.com/aallan/vera/compare/v0.0.37...v0.0.38
[0.0.37]: https://github.com/aallan/vera/compare/v0.0.36...v0.0.37
[0.0.36]: https://github.com/aallan/vera/compare/v0.0.35...v0.0.36
[0.0.35]: https://github.com/aallan/vera/compare/v0.0.34...v0.0.35
[0.0.34]: https://github.com/aallan/vera/compare/v0.0.33...v0.0.34
[0.0.33]: https://github.com/aallan/vera/compare/v0.0.32...v0.0.33
[0.0.32]: https://github.com/aallan/vera/compare/v0.0.31...v0.0.32
[0.0.31]: https://github.com/aallan/vera/compare/v0.0.30...v0.0.31
[0.0.30]: https://github.com/aallan/vera/compare/v0.0.29...v0.0.30
[0.0.29]: https://github.com/aallan/vera/compare/v0.0.28...v0.0.29
[0.0.28]: https://github.com/aallan/vera/compare/v0.0.27...v0.0.28
[0.0.27]: https://github.com/aallan/vera/compare/v0.0.26...v0.0.27
[0.0.26]: https://github.com/aallan/vera/compare/v0.0.25...v0.0.26
[0.0.25]: https://github.com/aallan/vera/compare/v0.0.24...v0.0.25
[0.0.24]: https://github.com/aallan/vera/compare/v0.0.23...v0.0.24
[0.0.23]: https://github.com/aallan/vera/compare/v0.0.22...v0.0.23
[0.0.22]: https://github.com/aallan/vera/compare/v0.0.21...v0.0.22
[0.0.21]: https://github.com/aallan/vera/compare/v0.0.20...v0.0.21
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
