# History

How the Vera compiler was built, from initial commit to v0.0.103, across 30 development days.

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

## Stage 9: Hardening and agent usability (28–29 March)

*Two days. Bug fixes, typed CLI arguments, AI agent discovery, security hardening, and conformance improvements.*

With the core language complete, Stage 9 focused on friction removal and polish — the small issues that would bias any benchmark or frustrate any agent trying to use the language seriously. [VeraBench](https://github.com/aallan/vera-bench) — a 50-problem benchmark suite built in a separate repository — began producing initial results during this stage.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.102 | 28 Mar | **Bug fixes** — stdin double-read on `/dev/stdin` resolved by a single `_load_and_parse` helper in the CLI (#335); E609 false positive on `Option<T>` return types across modules (#360); pipe operator into module-qualified calls (#326). |
| v0.0.103 | 29 Mar | **CI security hardening** — `pip-audit` dependency CVE scanning (#384), `ruff --select S` Bandit-equivalent lint rules (#388), `zizmor` workflow hardening (#385), CycloneDX SBOM generation (#389). **CLI improvements** — `vera version` command (#381), `--quiet` flag (#382). **Bug fixes** — `Http.post` `Content-Type: application/json` header (#354), `vera test` skip messages (#383). **Conformance** — two `verify`-level De Bruijn tests: deep let-chains (#393) and non-commutative operations (#394). **Documentation** — Known Limitations in SKILL.md (#404), skipped-tests table in TESTING.md, MIT licence text in README. |
| v0.0.104 | 29 Mar | **Type inference fix** — `option_unwrap_or(None, 99)`, `result_unwrap_or(Err("oops"), 0)`, and `option_map(None, fn(...){...})` now type-check without a typed `let` workaround (#293). Three-layer fix: checker fresh-TypeVar overwrite rule, monomorphizer sparse-constructor field→tp-index mapping, missing `StringLit` in monomorphizer type inferencer. Phase 1a complete. |
| v0.0.105 | 30 Mar | **Typed holes** — `?` placeholder expression for partial programs (#226). `vera check` reports W001 with expected type and available slot bindings; programs with holes cannot compile (E614). Iterative workflow: write skeleton with holes, read hints, fill in. |
| v0.0.106 | 31 Mar | **`vera test` String & Float64 input generation** — Z3-guided contract testing now covers `String` (sequence sort, ≤50 chars) and `Float64` (real sort, boundary seeding) parameters, removing the `SKIPPED (cannot generate … inputs (see #169))` limitation for those types (#169). ADT input generation tracked in #440. |

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

| Metric | v0.0.1 (23 Feb) | v0.0.9 (23 Feb) | v0.0.39 (27 Feb) | v0.0.65 (4 Mar) | v0.0.88 (12 Mar) | v0.0.101 (27 Mar) | v0.0.102 (28 Mar) | v0.0.103 (29 Mar) |
|--------|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| Compiler layers | Parser | 5 (full pipeline) | 5 + modules | 5 + modules + GC | 5 + modules + GC + browser | 5 + modules + GC + browser | 5 + modules + GC + browser | 5 + modules + GC + browser |
| Tests | ~50 | ~300 | ~600 | ~1,400 | ~2,300 | 3,095 | 3,121 | 3,184 |
| Examples | 13 | 15 | 16 | 18 | 24 | 30 | 30 | 30 |
| Built-in functions | 0 | 0 | ~5 | ~30 | ~80 | 122 | 122 | 122 |
| Conformance programs | 0 | 0 | 0 | 0 | ~50 | 64 | 65 | 71 |
| Spec chapters | 7 | 10 | 11 | 12 | 13 | 13 | 13 | 13 |
| Code coverage | — | — | — | 90% | 91% | 96% | 96% | 96% |

Total: **630+ commits, 106 tagged releases, 30 active development days.**
