# History

How the Vera compiler was built, from initial commit through Stage 11, across 40 active development days.

Vera was developed in an interleaved spiral — each phase added a complete compiler layer with tests, documentation, and working examples before moving to the next. The compiler was built by a single developer working with Claude Code, with CodeRabbit providing AI code review on pull requests from v0.0.80 onwards. The entire project — language design, specification, compiler, test suite, documentation, website — was built from scratch starting 22 February 2026.

---

## Stage 1: The core compiler (22–23 February)

*One day. Five compiler layers. From nothing to a working language.*

The first day of development produced the complete compiler pipeline: parser, AST, type checker, contract verifier, and WebAssembly code generator. By the end of 23 February, `vera run examples/hello_world.vera` printed "Hello, World!" from compiled WebAssembly.

| Version | Date | What shipped |
|---------|------|-------------|
| — | 22 Feb | Initial commit. Repository structure, licence, empty scaffolding. |
| v0.0.1 | 23 Feb | **Parser.** Lark LALR(1) grammar, natural-language error messages designed for LLM consumption, SKILL.md language reference, 13 example programs, first tests. The veralang.dev domain went live the same day. |
| v0.0.2 | 23 Feb | CI workflow, social preview, domain configuration. |
| v0.0.3 | 23 Feb | Full parser coverage — 110 tests, 13 examples, specification cleanup. |
| v0.0.4 | 23 Feb | **AST.** Typed syntax tree, Lark→AST transformer, `vera ast` command, 83 new tests. |
| v0.0.5 | 23 Feb | **Type checker.** Decidable type checking, slot reference resolution, effect tracking, `vera typecheck` command, 91 new tests. |
| v0.0.6–v0.0.7 | 23 Feb | Hello World example, specification design notes, housekeeping. |
| v0.0.8 | 23 Feb | **Contract verifier.** Z3 SMT solver integration, refinement types, counterexample generation for failed contracts. |
| v0.0.9 | 23 Feb | **WASM code generator.** Compile to WebAssembly, `vera compile` and `vera run` commands. First end-to-end execution. |

66 commits on 23 February alone — from an empty repository to a language that parses, type-checks, verifies contracts, compiles to WebAssembly, and runs. The specification (Chapters 0–7) was written in parallel with the compiler, not after it.

---

## Stage 2: Codegen completeness (24–26 February)

*Three days. Every language construct compiles to WASM.*

The parser and type checker handled the full language from day one, but the code generator initially only supported basic arithmetic and function calls. Stage 2 extended WASM compilation to every construct: ADTs, pattern matching, closures, generics, effect handlers, arrays, quantifiers, and refinement types.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.10 | 24 Feb | Float64 — `f64` literals, arithmetic, comparisons. |
| v0.0.11 | 24 Feb | Callee preconditions — verify `requires()` at call sites in WASM. |
| v0.0.12 | 24 Feb | Match exhaustiveness — verify all constructors covered. |
| v0.0.13 | 24 Feb | State\<T\> operations — get/put as host imports. |
| v0.0.14 | 24 Feb | Bump allocator — heap allocation for tagged values. |
| v0.0.15 | 24 Feb | ADT constructors — heap-allocated tagged unions. |
| v0.0.16 | 24 Feb | Match expressions — tag dispatch, field extraction. |
| v0.0.17 | 24 Feb | Generics — monomorphization of `forall<T>` functions. |
| v0.0.18 | 25 Feb | Closures — closure conversion, `call_indirect`. |
| v0.0.19 | 25 Feb | Effect handlers — handle/resume compilation. |
| v0.0.20 | 25 Feb | Housekeeping and test fixes. |
| v0.0.21 | 26 Feb | Byte type and arrays — linear memory arrays with bounds checking. |
| v0.0.22 | 26 Feb | Quantifiers — forall/exists compiled as runtime loops. |
| v0.0.23 | 26 Feb | Refinement type alias compilation. |
| v0.0.24 | 26 Feb | Specification Chapters 9 (Standard Library) and 12 (Runtime). |

After v0.0.24, all 15 example programs compiled and ran correctly. The language was feature-complete at the syntax level, though the standard library was minimal.

---

## Stage 3: Codegen cleanup (26 February)

*One day. Residual gaps closed before starting the module system.*

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.25 | 26 Feb | `resume` recognised as built-in in handler scope. |
| v0.0.26 | 26 Feb | Handler `with` clause for state updates added to grammar. |
| v0.0.27 | 26 Feb | Pipe operator (`\|>`) compilation. |
| v0.0.28 | 26 Feb | Float64 modulo — WASM has no `f64.rem`, so this required a host-import workaround. |
| v0.0.29 | 26 Feb | String and Array types in function signatures. |
| v0.0.30 | 26 Feb | `old()`/`new()` state expressions in contracts. |

---

## Stage 4: Module system (26–27 February)

*Two days. Cross-file imports, visibility, multi-module compilation.*

The module system was built in six sub-phases, each adding one layer: file resolution, cross-module type environment, visibility enforcement, cross-module contract verification, multi-module WASM compilation (using a flattening strategy), and the formal specification (Chapter 8).

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.31 | 26 Feb | Module resolution — map `import` paths to source files and parse them. |
| v0.0.32 | 27 Feb | Cross-module type environment — merge public declarations across files. |
| v0.0.33 | 27 Feb | Internal refactoring for visibility. |
| v0.0.34–v0.0.35 | 27 Feb | Visibility enforcement — `public`/`private` access control in the checker. |
| v0.0.36 | 27 Feb | Internal fixes. |
| v0.0.37 | 27 Feb | Cross-module verification — verify contracts that reference imported symbols. |
| v0.0.38 | 27 Feb | Multi-module codegen — flatten imported functions into the WASM module. |
| v0.0.39 | 27 Feb | Specification Chapter 8 — formal module semantics, resolution algorithm, examples. |

After v0.0.39, Vera programs could import functions and data types from other files, with visibility enforcement and cross-module contract verification.

---

## Stage 5: Polish (27 February – 4 March)

*Six days. Refactoring, tooling, diagnostics, verification depth, and the garbage collector.*

This was the longest phase, addressing accumulated technical debt and adding core tooling. The compiler source was refactored from monolithic files into subpackages (`checker.py` split into `checker/`, `wasm.py` into `wasm/`, `codegen.py` into `codegen/`). Major new tools shipped: the canonical formatter (`vera fmt`), contract-driven testing (`vera test`), stable error codes (E001–E702), and JSON diagnostics. The type system was extended with TypeVar subtyping, effect row unification, and minimal type inference.

The phase culminated with the garbage collector — a conservative mark-sweep GC for WASM linear memory that replaced the bump allocator, enabling long-running programs.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.40 | 27 Feb | Decompose `checker.py` (~1,900 lines) into `checker/` submodules. |
| v0.0.41 | 27 Feb | Decompose `wasm.py` (~2,300 lines) into `wasm/` submodules. |
| v0.0.42 | 27 Feb | Informative runtime contract violation error messages. |
| v0.0.43 | 27 Feb | Stable error code taxonomy (E001–E702). |
| v0.0.44 | 28 Feb | LALR grammar fix for module-qualified call syntax. |
| v0.0.45 | 28 Feb | **`vera fmt`** — canonical formatter. One textual representation for every construct. |
| v0.0.46 | 1 Mar | Decompose `codegen.py` (~2,140 lines) into `codegen/` submodules. |
| v0.0.47 | 1 Mar | **`vera test`** — contract-driven testing. Generate inputs from contracts via Z3, compile and run through WASM. |
| v0.0.48 | 1 Mar | Improved test coverage for WASM translation modules. |
| v0.0.49 | 1 Mar | Register `Diverge` as built-in effect. |
| v0.0.50 | 2 Mar | String built-in operations (length, concat, slice). |
| v0.0.51 | 2 Mar | Expand SMT decidable fragment (Tier 2 verification). |
| v0.0.52 | 2 Mar | `decreases` clause termination verification. |
| v0.0.53 | 2 Mar | TypeVar subtyping. |
| v0.0.54 | 2 Mar | Effect row unification and subeffecting. |
| v0.0.55 | 3 Mar | Minimal type inference. |
| v0.0.56 | 3 Mar | Nested constructor pattern codegen. |
| v0.0.57 | 3 Mar | Name collision detection for flat module compilation. |
| v0.0.58 | 3 Mar | Recursive generic ADT codegen (fixing `list_ops.vera` runtime failure). |
| v0.0.59 | 3 Mar | Internal fixes. |
| v0.0.60 | 3 Mar | `parse_nat` returns `Result<Nat, String>` per spec. |
| v0.0.61 | 4 Mar | Arrays of compound types in codegen. |
| v0.0.62 | 4 Mar | `Exn<E>` and custom effect handler compilation. |
| v0.0.63 | 4 Mar | Dynamic string construction. |
| v0.0.64 | 4 Mar | Universal to-string conversion. |
| v0.0.65 | 4 Mar | **Garbage collector.** Conservative mark-sweep GC for WASM linear memory. Programs can now allocate dynamically in loops without exhausting the heap. |

After v0.0.65, the compiler was structurally mature: three clean subpackages, a canonical formatter, contract-driven testing, stable error codes, a mark-sweep GC, and a type system with inference, subtyping, and termination verification.

---

## Stage 6: Standard library and runtime completeness (5–12 March)

*Eight days. Built-in functions, IO runtime, browser target, Markdown, Async, and the conformance suite.*

This phase built out the standard library from a handful of operations to over 100 built-in functions, added the full IO runtime (read_line, read_file, write_file, args, exit, get_env), shipped the browser runtime with mandatory parity tests, and added the Markdown standard library type.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.66 | 5 Mar | **IO runtime** — read_line, read_file, write_file, args, exit, get_env. |
| v0.0.67 | 5 Mar | String escape sequences (\n, \t, etc.) in string literals. |
| v0.0.68 | 5 Mar | **Conformance test suite** — the beginning of systematic spec validation. |
| v0.0.69 | 6 Mar | Internal fixes. |
| v0.0.70 | 9 Mar | Numeric math built-ins (abs, min, max, floor, ceil, round, sqrt, pow). |
| v0.0.71 | 9 Mar | Numeric type conversions (int_to_float, float_to_int, nat_to_int, etc.). |
| v0.0.72 | 9 Mar | Float64 special value operations (float_is_nan, float_is_infinite, nan(), infinity()). |
| v0.0.73 | 9 Mar | String search and transformation built-ins (contains, starts_with, upper, lower, replace, split, join). |
| v0.0.74 | 9 Mar | string_from_char_code built-in. |
| v0.0.75 | 10 Mar | string_repeat built-in. |
| v0.0.76 | 10 Mar | **String interpolation** — `"\(@Int.0)"` with auto-conversion for all primitive types. |
| v0.0.77 | 10 Mar | Parsing completeness (parse_int, parse_bool, safe parse_float64). |
| v0.0.78 | 10 Mar | Array construction built-ins (range, append, concat). |
| v0.0.79 | 10 Mar | Base64 encoding and decoding. |
| v0.0.80 | 10 Mar | Internal fixes. CodeRabbit AI code review configured from this point onwards. |
| v0.0.81 | 10 Mar | URL parsing and construction built-ins. |
| v0.0.82 | 11 Mar | **Async type infrastructure** — `<Async>` marker effect, `Future<T>`, `async`/`await` built-ins. Execution is eager/sequential; true concurrency deferred to WASI 0.3. |
| v0.0.83 | 11 Mar | Tuple type WASM codegen. |
| v0.0.84 | 11 Mar | **Markdown standard library** — `MdBlock` and `MdInline` ADTs (14 constructors), `md_parse`, `md_render`, `md_has_heading`, `md_has_code_block`, `md_extract_code_blocks`. Hand-written Python Markdown parser. 78 new tests. |
| v0.0.85 | 11 Mar | **Browser runtime** — self-contained JavaScript runtime (`runtime.mjs`, ~730 lines) that runs any compiled Vera `.wasm` module in the browser or Node.js. `vera compile --target browser` produces a ready-to-serve bundle. 56 browser parity tests. |
| v0.0.86 | 11 Mar | **Regex support** — regex_match, regex_find, regex_find_all, regex_replace. |
| v0.0.87 | 11 Mar | FizzBuzz example, iteration documentation. |
| v0.0.88 | 12 Mar | Formatter comment repositioning fix. |

11 March was the single most productive day for user-visible features: the Markdown standard library, the browser runtime with parity testing, and regex support all shipped in separate PRs on the same day.

---

## Stage 7: Abilities and the standard prelude (12–20 March)

*Eight days. Type constraints, constrained generics, combinators, higher-order array operations, naming conventions, and the standard prelude.*

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.89 | 12 Mar | **Option/Result combinators** — option_unwrap_or, option_map, option_and_then, result_unwrap_or, result_map. Implemented via source injection (parsed Vera AST). |
| v0.0.90 | 13 Mar | **Abilities** — four built-in abilities (Eq, Ord, Hash, Show) with `forall<T where Eq<T>>` constraint syntax, ADT auto-derivation, the Ordering ADT, and full WASM codegen. 20 unit tests. |
| v0.0.91 | 19 Mar | **Array operations** — array_slice, array_map, array_filter, array_fold. Six compiler bug fixes for monomorphization and WASM type inference. |
| v0.0.92 | 19 Mar | **BREAKING: naming audit** — 14 built-in functions renamed to follow the `domain_verb` convention. The last intentional breaking change before stabilisation. |
| v0.0.93 | 20 Mar | **Standard prelude** — Option\<T\>, Result\<T, E\>, Ordering, and UrlParts injected automatically. Eliminates 2–6 lines of boilerplate from every program. |

The abilities release (v0.0.90) was the last major type system feature. After v0.0.93, every Vera program had access to Option, Result, Ordering, combinators, and higher-order array operations without any boilerplate declarations.

---

## Stage 8: Data types and effects (23–27 March)

*Five days. Collections, JSON, HTML, HTTP, Decimal, and Inference — the features that make Vera an agent-viable language.*

This final stage delivered the critical dependency chain that had driven the roadmap from the beginning: Map → JSON → HTTP → Inference. Each item unlocked the next, culminating in LLM calls as typed algebraic effects.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.94 | 23 Mar | **Map\<K, V\>** — eight built-in operations with Eq + Hash ability constraints. Opaque i32 handles backed by Python dicts / JS Maps. 40 new tests. |
| v0.0.95 | 24 Mar | **Set\<T\>** — six built-in operations. |
| v0.0.96 | 24 Mar | Collections documentation sweep. **CI** — native JavaScript coverage for the browser runtime via `NODE_V8_COVERAGE` + c8 + Codecov (`javascript` flag); browser parity tests now have the same coverage visibility as Python-side tests (#337). |
| v0.0.97 | 24 Mar | **Decimal** — exact decimal arithmetic. 14 built-in operations. |
| v0.0.98 | 25 Mar | **JSON** — built-in `Json` ADT (6 constructors), 8 built-in functions. Parse, query, and serialise structured data. |
| v0.0.99 | 25 Mar | **HTTP** — built-in `<Http>` algebraic effect. `Http.get` and `Http.post` returning `Result<String, String>`. A Vera program can now make an HTTP request and parse the JSON response. |
| v0.0.100 | 26 Mar | **HTML** — built-in `HtmlNode` ADT, lenient parsing, CSS selector queries, text extraction. |
| v0.0.101 | 27 Mar | **Inference** — built-in `<Inference>` algebraic effect. `Inference.complete(String → Result<String, String>)` dispatches to Anthropic, OpenAI, or Moonshot. LLM calls are now explicit in the type system, contract-verifiable, and impossible to invoke from a pure function. |

v0.0.101 completed the chain. A Vera program can fetch data from the web, parse HTML or JSON, call an LLM, verify the response against contracts, and return typed results — all with every side effect tracked in the type system.

---

## Stage 9: Hardening and agent usability (28–31 March)

*Four days. Bug fixes, typed CLI arguments, AI agent discovery, security hardening, conformance improvements, and contract-driven testing extended to String and Float64.*

With the core language complete, Stage 9 focused on friction removal and polish — the small issues that would bias any benchmark or frustrate any agent trying to use the language seriously. [VeraBench](https://github.com/aallan/vera-bench) — a 50-problem benchmark suite built in a separate repository — began producing initial results during this stage.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.102 | 28 Mar | **Bug fixes** — stdin double-read (#335), E609 false positive on `Option<T>` across modules (#360), pipe into module-qualified calls (#326). |
| v0.0.103 | 29 Mar | **CI security hardening** — `pip-audit`, `ruff --select S`, `zizmor`, CycloneDX SBOM. **CLI** — `vera version`, `--quiet`. **Bug fixes** — HTTP post Content-Type header, `vera test` skip messages. **Conformance** — two verify-level De Bruijn tests (#393, #394). |
| v0.0.104 | 29 Mar | **Type inference fix** — `None`/`Err` bare constructors in generic calls now type-check without `let` workarounds (#293). Phase 1a complete. |
| v0.0.105 | 30 Mar | **Typed holes** — `?` placeholder for partial programs; `vera check` reports W001 with expected type and slot bindings; holes block compilation (E614). |
| v0.0.106 | 31 Mar | **`vera test` String & Float64 input generation** — Z3 testing extended to String (sequence sort, ≤50 chars) and Float64 (real sort, boundary seeding) (#169). |

## Stage 10: Evaluation and CI quality (7–11 April)

*After a week working in parallel on [VeraBench](https://github.com/aallan/vera-bench) evaluation, Stage 10 returns to the compiler with benchmark results informing priorities.*

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.107 | 7 Apr | **CI: validate `examples/README.md` run commands** ([#361](https://github.com/aallan/vera/issues/361)) — `check_examples_readme.py` verifies every `vera run` command references an existing file and exported function. |
| v0.0.108 | 7 Apr | **`vera check --explain-slots`** ([#445](https://github.com/aallan/vera/issues/445)) — slot resolution table showing which parameter each `@T.n` index refers to; addresses the dominant VeraBench failure mode. Plus SKILL.md prescriptive rework, `uv.lock` CI enforcement ([#390](https://github.com/aallan/vera/issues/390)), Z3 timeout documented ([#391](https://github.com/aallan/vera/issues/391)). |
| VeraBench v0.0.7 | 8 Apr | **Multi-model evaluation** — 6 models across 3 providers. Kimi K2.5 hits 100% run_correct on Vera, beating Python (86%) and TypeScript (91%); flagship tier averages 93% Vera vs 93% Python. |
| — | 9 Apr | **Bug fixes:** `Exn<String>` WASM tag encoding ([#416](https://github.com/aallan/vera/issues/416)) and nested `handle[State<T>]` isolation ([#417](https://github.com/aallan/vera/issues/417)). |
| v0.0.109 | 10 Apr | **Fix closure `i32_pair` param/return types** ([#359](https://github.com/aallan/vera/issues/359)) — `String`/`Array` params and returns in closures emit correct two-slot WAT; host imports inside closures propagate to module-level tracker. |
| v0.0.110 | 10 Apr | **Mistral AI provider** ([#413](https://github.com/aallan/vera/issues/413)) — `Inference.complete` adds Mistral; provider registry refactored to `_ProviderConfig` + `_PROVIDERS` dict so new providers are a one-row change. |
| v0.0.111 | 10 Apr | **SMT translator: String/Float64 parameter sorts** — params now declared with correct Z3 sorts (SeqSort/RealSort) instead of IntSort. `string_contains` / `string_starts_with` / `string_ends_with` now Tier 1 via Z3 native string theory. |

## Stage 11: Real-world programming (16 April onwards)

*Bug fixes and standard library depth — closing the gaps that trip up models and human programmers alike.*

Stage 11 shifts focus from evaluation infrastructure to the standard library and runtime correctness. The benchmark results from Stage 10 identified missing primitives as the dominant friction source: models reaching for `array_sort` or `string_reverse` and finding nothing, then writing fragile hand-rolled implementations. This stage adds the utility functions that any real program needs, alongside critical bug fixes.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.112 | 16 Apr | **Fix GC shadow stack overflow** ([#464](https://github.com/aallan/vera/issues/464)) — 4K shadow stack was overflowing into the GC worklist on deep recursive array accumulation. Bumped to 16K with an overflow guard trap. |
| v0.0.113 | 16 Apr | **Decompose `calls.py` into 8 subsystem mixins** ([#418](https://github.com/aallan/vera/issues/418)) — split the 8,390-line monolith into a 572-line dispatcher plus domain mixins. Pure code motion. Review surfaced 10 pre-existing bugs tracked in [#475](https://github.com/aallan/vera/issues/475). |
| — | 16 Apr | **CHANGELOG enforcement at pre-push and CI** ([#478](https://github.com/aallan/vera/issues/478)) — `check_changelog_updated.py` fails a PR if `vera/` / `spec/` / `SKILL.md` change without a matching CHANGELOG entry. Escape hatches via commit trailer or PR label. |
| — | 17 Apr | **Widen GC object header size field from 16-bit to 31-bit** ([#484](https://github.com/aallan/vera/issues/484)) — sweeper was masking size readback with `0xFFFF`, silently truncating allocations ≥65536 bytes. Max single allocation is now bounded by WASM's 4 GB ceiling. |
| — | 17 Apr | **Iterative WASM higher-order array ops** ([#480](https://github.com/aallan/vera/issues/480)) — `array_map`/`filter`/`fold` migrated from recursive prelude functions to iterative WAT loops with O(1) shadow-stack depth. Shipped across three PRs. |
| v0.0.114 | 17 Apr | **`IO.sleep`, `IO.time`, `IO.stderr`** ([#463](https://github.com/aallan/vera/issues/463)) — three new `IO` effect operations: pause for N ms, Unix time in ms, stderr separate from stdout. |
| v0.0.115 | 18 Apr | **`Random` effect** ([#465](https://github.com/aallan/vera/issues/465)) — `random_int`, `random_float`, `random_bool`. Functions declaring `effects(<Random>)` surface non-determinism in their signatures. No `handle[Random]` yet. |
| v0.0.116 | 20 Apr | **Math built-ins** ([#467](https://github.com/aallan/vera/issues/467)) — fifteen pure functions: logarithmic (`log`, `log2`, `log10`), trigonometric (`sin`..`atan2`), constants (`pi()`, `e()`), utilities (`sign`, `clamp`, `float_clamp`). Gated per-op. |
| — | 22 Apr | **Dependabot uv ecosystem + auto-uv-lock** ([#500](https://github.com/aallan/vera/pull/500), [#501](https://github.com/aallan/vera/pull/501)) — switched `dependabot.yml` to the `uv` ecosystem plus a workflow regenerating `uv.lock` on dependabot PRs. Resolves a recurring CI lint failure. |
| v0.0.117 | 22 Apr | **Array utility built-ins (phase 1)** ([#466](https://github.com/aallan/vera/issues/466)) — seven combinators: `array_mapi`, `array_reverse`, `array_find`, `array_any`/`all`, `array_flatten`, `array_sort_by`. All iterative WASM with O(1) shadow-stack depth. Phase 2 (Eq/Ord-dispatched) tracked separately as [#507](https://github.com/aallan/vera/issues/507). |
| v0.0.118 | 23 Apr | **String utilities + character classification** ([#470](https://github.com/aallan/vera/issues/470), [#471](https://github.com/aallan/vera/issues/471)) — sixteen new built-ins, all inline WAT. Eight string utilities (chars, lines, words, reverse, trim_start/end, pad_start/end); six character classifiers (`is_digit`/`alpha`/`alphanumeric`/`whitespace`/`upper`/`lower`); two first-byte case conversions (`char_to_upper`/`lower`). ASCII-only; Unicode variants tracked as [#509](https://github.com/aallan/vera/issues/509). |
| v0.0.119 | 23 Apr | **JSON typed accessors** ([#366](https://github.com/aallan/vera/issues/366)) — eleven pure-Vera prelude accessors on the `Json` ADT: six Layer-1 coercions (`json_as_string`/`_number`/`_bool`/`_int`/`_array`/`_object` → `Option<T>`) and five Layer-2 compound field accessors (`json_get_string`/`_number`/`_bool`/`_int`/`_array`). `json_as_int` guards all four `float_to_int` trap paths (NaN, ±inf, finite overflow). Collapses the two-level `match` every JSON consumer writes. |
| v0.0.120 | 26 Apr | **Crash-debugging UX: trap categorisation + stdout preserved on trap** ([#522](https://github.com/aallan/vera/issues/522), [#516](https://github.com/aallan/vera/issues/516) Stage 1) — first pair from the bug-killing campaign. New `WasmTrapError` (`RuntimeError` subclass) carries captured `stdout`/`stderr` and a stable `kind` (`divide_by_zero`/`out_of_bounds`/`stack_exhausted`/`unreachable`/`overflow`/`contract_violation`/`unknown`) so `IO.print` output preceding a trap reaches the user and traps stop being mis-labelled "Runtime contract violation". JSON envelope gains `trap_kind`. |
| v0.0.121 | 27 Apr | **Nested closures + ADT capture work end-to-end** ([#514](https://github.com/aallan/vera/issues/514), [#527](https://github.com/aallan/vera/issues/527)) — the natural 2D `array_map(rows, fn { array_map(cols, fn { ... }) })` shape compiles at arbitrary depth. Pair-type captures split into [#535](https://github.com/aallan/vera/issues/535); CVE-2026-3219 ignore dropped (pip 26.1 shipped). |
| v0.0.122 | 27 Apr | **Conservative GC bounds-checked against `$heap_ptr`** ([#515](https://github.com/aallan/vera/issues/515)) — `$gc_collect` no longer faults when a non-pointer i32 in payload data (e.g. a bit-packed `Nat` row in Conway-style code) happens to satisfy the worklist-seeding alignment + range guards. Layer 2 sanity-checks `obj_ptr + obj_size <= heap_ptr` before marking or scanning a worklist entry; Layer 1 adds a per-iteration bound check inside the conservative scan loop so any future caller that bypasses the upstream check still cannot read past the heap. 40×20×200 Conway now runs cleanly through every generation. |
| v0.0.123 | 27 Apr | **`IO.print` writes mirror live to `sys.stdout`** ([#543](https://github.com/aallan/vera/issues/543)) — `vera run` text mode now flushes per call, so animations, progress bars, REPL-style output, and any program using ANSI cursor / clear-screen escapes render in real time instead of dumping the whole transcript at exit. Tee preserves the in-memory capture, so trap preservation (#522) and JSON-envelope packaging still work. Discovered while watching the v0.0.122 GC fix run Conway end-to-end and seeing only the final frame. |

---

## Editor and tooling support

Alongside the compiler, editor support and AI discoverability infrastructure were developed:

| Date | What shipped |
|------|-------------|
| 23 Feb | veralang.dev domain, SKILL.md, initial website |
| 28 Feb | `vera fmt` canonical formatter |
| 1 Mar | `vera test` contract-driven testing |
| 5 Mar | Conformance test suite (grew from initial set to 64 programs) |
| 10 Mar | CodeRabbit AI code review configured (.coderabbit.yaml) |
| 11 Mar | Browser runtime with `vera compile --target browser` |
| 17 Mar | TextMate syntax highlighting bundle |
| 18 Mar | VS Code extension for Vera syntax highlighting |
| 20 Mar | AI discoverability: llms.txt, llms-full.txt, robots.txt, sitemap.xml, ai-plugin.json, index.md |
| 28 Mar | `vera run --fn f -- arg` typed argument passing — String, Float64, Bool, Byte alongside Int |
| 28 Mar | Agent discovery metadata — llms-txt link elements, JSON-LD TechArticle entries, inline script block on veralang.dev |
| 29 Mar | `vera version` CLI command; `--quiet` flag for `vera check`/`vera verify`; Known Limitations section in SKILL.md; skipped-tests table in TESTING.md |

---

## By the numbers

| Metric | v0.0.1 (23 Feb) | v0.0.9 (23 Feb) | v0.0.39 (27 Feb) | v0.0.65 (4 Mar) | v0.0.88 (12 Mar) | v0.0.101 (27 Mar) | v0.0.113 (16 Apr) |
|--------|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| Compiler layers | Parser | 5 (full pipeline) | 5 + modules | 5 + modules + GC | 5 + modules + GC + browser | 5 + modules + GC + browser | 5 + modules + GC + browser |
| Tests | ~50 | ~300 | ~600 | ~1,400 | ~2,300 | 3,095 | 3,319 |
| Examples | 13 | 15 | 16 | 18 | 24 | 30 | 30 |
| Built-in functions | 0 | 0 | ~5 | ~30 | ~80 | 122 | 122 |
| Conformance programs | 0 | 0 | 0 | 0 | ~50 | 64 | 73 |
| Spec chapters | 7 | 10 | 11 | 12 | 13 | 13 | 13 |
| Code coverage | — | — | — | 90% | 91% | 96% | 96% |

Total: **810+ commits, 123 tagged releases, 40 active development days.**
