# History

How the Vera compiler was built, from initial commit through Stage 14, across 77 active development days.

Vera was developed in an interleaved spiral — each phase added a complete compiler layer with tests, documentation, and working examples before moving to the next. The compiler was built by a single developer working with Claude Code, with CodeRabbit providing AI code review on pull requests from v0.0.80 onwards. The entire project — language design, specification, compiler, test suite, documentation, website — was built from scratch starting 22 February 2026.

Version rows follow one rule: one sentence, at most one issue link.  [CHANGELOG.md](CHANGELOG.md) is the per-release log of record; this file is the story.

## Stage index

| Stage | Dates | Theme | Versions |
|:---:|---|---|---|
| 1 | 22–23 Feb | The core compiler | v0.0.1–v0.0.9 |
| 2 | 24–26 Feb | Codegen completeness | v0.0.10–v0.0.24 |
| 3 | 26 Feb | Codegen cleanup | v0.0.25–v0.0.30 |
| 4 | 26–27 Feb | Module system | v0.0.31–v0.0.39 |
| 5 | 27 Feb – 4 Mar | Polish, tooling, and the GC | v0.0.40–v0.0.65 |
| 6 | 5–12 Mar | Standard library and runtime | v0.0.66–v0.0.88 |
| 7 | 12–20 Mar | Abilities and the prelude | v0.0.89–v0.0.93 |
| 8 | 23–27 Mar | Data types and effects | v0.0.94–v0.0.101 |
| 9 | 28–31 Mar | Hardening and agent usability | v0.0.102–v0.0.106 |
| 10 | 7–11 Apr | Evaluation and CI quality | v0.0.107–v0.0.111 |
| 11 | 16–23 Apr | Standard library depth | v0.0.112–v0.0.119 |
| 12 | 26 Apr – 8 May | The bug-killing campaign | v0.0.120–v0.0.142 |
| 13 | 10–29 May | Stabilisation and memory safety | v0.0.143–v0.0.160 |
| 14 | 10 Jun onwards | The language server | v0.0.161– |

---

## Stage 1: The core compiler (22–23 February)

*One day. Five compiler layers. From nothing to a working language.*

The first day of development produced the complete compiler pipeline: parser, AST, type checker, contract verifier, and WebAssembly code generator.

| Version | Date | What shipped |
|---------|------|-------------|
| — | 22 Feb | Initial commit: repository structure, licence, empty scaffolding. |
| v0.0.1 | 23 Feb | **Parser.** Lark LALR(1) grammar with natural-language errors designed for LLM consumption, SKILL.md, 13 example programs, and the veralang.dev domain live the same day. |
| v0.0.2 | 23 Feb | CI workflow, social preview, domain configuration. |
| v0.0.3 | 23 Feb | Full parser coverage: 110 tests, 13 examples, specification cleanup. |
| v0.0.4 | 23 Feb | **AST.** Typed syntax tree, Lark→AST transformer, `vera ast` command, 83 new tests. |
| v0.0.5 | 23 Feb | **Type checker.** Decidable type checking, slot reference resolution, effect tracking, `vera typecheck` command, 91 new tests. |
| v0.0.6–v0.0.7 | 23 Feb | Hello World example, specification design notes, housekeeping. |
| v0.0.8 | 23 Feb | **Contract verifier.** Z3 SMT solver integration, refinement types, counterexample generation for failed contracts. |
| v0.0.9 | 23 Feb | **WASM code generator.** `vera compile` and `vera run` deliver the first end-to-end execution. |

66 commits on 23 February alone — from an empty repository to a language that parses, type-checks, verifies contracts, compiles to WebAssembly, and runs. The specification (Chapters 0–7) was written in parallel with the compiler, not after it.

---

## Stage 2: Codegen completeness (24–26 February)

*Three days. Every language construct compiles to WASM.*

The parser and type checker handled the full language from day one; Stage 2 extended WASM compilation to every construct.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.10 | 24 Feb | Float64: `f64` literals, arithmetic, comparisons. |
| v0.0.11 | 24 Feb | Callee preconditions: `requires()` verified at call sites in WASM. |
| v0.0.12 | 24 Feb | Match exhaustiveness: every constructor must be covered. |
| v0.0.13 | 24 Feb | State\<T\> operations: get/put as host imports. |
| v0.0.14 | 24 Feb | Bump allocator: heap allocation for tagged values. |
| v0.0.15 | 24 Feb | ADT constructors: heap-allocated tagged unions. |
| v0.0.16 | 24 Feb | Match expressions: tag dispatch, field extraction. |
| v0.0.17 | 24 Feb | Generics: monomorphization of `forall<T>` functions. |
| v0.0.18 | 25 Feb | Closures: closure conversion, `call_indirect`. |
| v0.0.19 | 25 Feb | Effect handlers: handle/resume compilation. |
| v0.0.20 | 25 Feb | Housekeeping and test fixes. |
| v0.0.21 | 26 Feb | Byte type and arrays: linear memory arrays with bounds checking. |
| v0.0.22 | 26 Feb | Quantifiers: forall/exists compiled as runtime loops. |
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
| v0.0.28 | 26 Feb | Float64 modulo: WASM has no `f64.rem`, so a host-import workaround. |
| v0.0.29 | 26 Feb | String and Array types in function signatures. |
| v0.0.30 | 26 Feb | `old()`/`new()` state expressions in contracts. |

Six releases in a day cleared the residue; the module system could start on clean ground.

---

## Stage 4: Module system (26–27 February)

*Two days. Cross-file imports, visibility, multi-module compilation.*

The module system was built in six sub-phases, each adding one layer: file resolution, cross-module type environment, visibility enforcement, cross-module contract verification, multi-module WASM compilation, and the formal specification (Chapter 8).

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.31 | 26 Feb | Module resolution: map `import` paths to source files and parse them. |
| v0.0.32 | 27 Feb | Cross-module type environment: merge public declarations across files. |
| v0.0.33 | 27 Feb | Internal refactoring for visibility. |
| v0.0.34–v0.0.35 | 27 Feb | Visibility enforcement: `public`/`private` access control in the checker. |
| v0.0.36 | 27 Feb | Internal fixes. |
| v0.0.37 | 27 Feb | Cross-module verification: contracts that reference imported symbols. |
| v0.0.38 | 27 Feb | Multi-module codegen: imported functions flattened into the WASM module. |
| v0.0.39 | 27 Feb | Specification Chapter 8: formal module semantics, resolution algorithm, examples. |

After v0.0.39, Vera programs could import functions and data types from other files, with visibility enforcement and cross-module contract verification.

---

## Stage 5: Polish, tooling, and the GC (27 February – 4 March)

*Six days. Refactoring, tooling, diagnostics, verification depth, and the garbage collector.*

The longest early phase: the compiler refactored into subpackages, the canonical formatter, contract-driven testing, stable error codes, and a type system extended with subtyping, effect row unification, and inference. It culminated in the conservative mark-sweep GC that replaced the bump allocator.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.40 | 27 Feb | Decompose `checker.py` (~1,900 lines) into `checker/` submodules. |
| v0.0.41 | 27 Feb | Decompose `wasm.py` (~2,300 lines) into `wasm/` submodules. |
| v0.0.42 | 27 Feb | Informative runtime contract violation error messages. |
| v0.0.43 | 27 Feb | Stable error code taxonomy (E001–E702). |
| v0.0.44 | 28 Feb | LALR grammar fix for module-qualified call syntax. |
| v0.0.45 | 28 Feb | **`vera fmt`**: the canonical formatter, one textual representation for every construct. |
| v0.0.46 | 1 Mar | Decompose `codegen.py` (~2,140 lines) into `codegen/` submodules. |
| v0.0.47 | 1 Mar | **`vera test`**: contract-driven testing that generates inputs from contracts via Z3 and runs them through WASM. |
| v0.0.48 | 1 Mar | Improved test coverage for WASM translation modules. |
| v0.0.49 | 1 Mar | Register `Diverge` as built-in effect. |
| v0.0.50 | 2 Mar | String built-in operations (length, concat, slice). |
| v0.0.51 | 2 Mar | Expanded the SMT decidable fragment. |
| v0.0.52 | 2 Mar | `decreases` clause termination verification. |
| v0.0.53 | 2 Mar | TypeVar subtyping. |
| v0.0.54 | 2 Mar | Effect row unification and subeffecting. |
| v0.0.55 | 3 Mar | Minimal type inference. |
| v0.0.56 | 3 Mar | Nested constructor pattern codegen. |
| v0.0.57 | 3 Mar | Name collision detection for flat module compilation. |
| v0.0.58 | 3 Mar | Recursive generic ADT codegen, fixing the `list_ops.vera` runtime failure. |
| v0.0.59 | 3 Mar | Internal fixes. |
| v0.0.60 | 3 Mar | `parse_nat` returns `Result<Nat, String>` per spec. |
| v0.0.61 | 4 Mar | Arrays of compound types in codegen. |
| v0.0.62 | 4 Mar | `Exn<E>` and custom effect handler compilation. |
| v0.0.63 | 4 Mar | Dynamic string construction. |
| v0.0.64 | 4 Mar | Universal to-string conversion. |
| v0.0.65 | 4 Mar | **Garbage collector.** Conservative mark-sweep GC for WASM linear memory, so programs can allocate dynamically in loops without exhausting the heap. |

After v0.0.65, the compiler was structurally mature: three clean subpackages, a canonical formatter, contract-driven testing, stable error codes, a mark-sweep GC, and a type system with inference, subtyping, and termination verification.

---

## Stage 6: Standard library and runtime completeness (5–12 March)

*Eight days. Built-in functions, IO runtime, browser target, Markdown, Async, and the conformance suite.*

The standard library grew from a handful of operations to over 100 built-in functions, the full IO runtime landed, and the browser runtime shipped with mandatory parity tests.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.66 | 5 Mar | **IO runtime**: read_line, read_file, write_file, args, exit, get_env. |
| v0.0.67 | 5 Mar | String escape sequences (\n, \t, etc.) in string literals. |
| v0.0.68 | 5 Mar | **Conformance test suite**: the beginning of systematic spec validation. |
| v0.0.69 | 6 Mar | Internal fixes. |
| v0.0.70 | 9 Mar | Numeric math built-ins (abs, min, max, floor, ceil, round, sqrt, pow). |
| v0.0.71 | 9 Mar | Numeric type conversions (int_to_float, float_to_int, nat_to_int, etc.). |
| v0.0.72 | 9 Mar | Float64 special value operations (float_is_nan, float_is_infinite, nan(), infinity()). |
| v0.0.73 | 9 Mar | String search and transformation built-ins (contains, starts_with, upper, lower, replace, split, join). |
| v0.0.74 | 9 Mar | string_from_char_code built-in. |
| v0.0.75 | 10 Mar | string_repeat built-in. |
| v0.0.76 | 10 Mar | **String interpolation**: `"\(@Int.0)"` with auto-conversion for all primitive types. |
| v0.0.77 | 10 Mar | Parsing completeness (parse_int, parse_bool, safe parse_float64). |
| v0.0.78 | 10 Mar | Array construction built-ins (range, append, concat). |
| v0.0.79 | 10 Mar | Base64 encoding and decoding. |
| v0.0.80 | 10 Mar | Internal fixes, with CodeRabbit AI code review configured from this point onwards. |
| v0.0.81 | 10 Mar | URL parsing and construction built-ins. |
| v0.0.82 | 11 Mar | **Async type infrastructure**: `<Async>` marker effect and `Future<T>`, eager/sequential until WASI 0.3. |
| v0.0.83 | 11 Mar | Tuple type WASM codegen. |
| v0.0.84 | 11 Mar | **Markdown standard library**: `MdBlock` and `MdInline` ADTs with parse, render, and query built-ins, plus 78 new tests. |
| v0.0.85 | 11 Mar | **Browser runtime**: `vera compile --target browser` produces a ready-to-serve bundle backed by `runtime.mjs`, with 56 parity tests. |
| v0.0.86 | 11 Mar | **Regex support**: regex_match, regex_find, regex_find_all, regex_replace. |
| v0.0.87 | 11 Mar | FizzBuzz example, iteration documentation. |
| v0.0.88 | 12 Mar | Formatter comment repositioning fix. |

11 March was the single most productive day for user-visible features: the Markdown standard library, the browser runtime with parity testing, and regex support all shipped in separate PRs on the same day.

---

## Stage 7: Abilities and the standard prelude (12–20 March)

*Eight days. Type constraints, combinators, higher-order array operations, and the standard prelude.*

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.89 | 12 Mar | **Option/Result combinators**: option_unwrap_or, option_map, option_and_then, result_unwrap_or, result_map, implemented via source injection. |
| v0.0.90 | 13 Mar | **Abilities**: Eq, Ord, Hash, and Show with `forall<T where Eq<T>>` constraint syntax, ADT auto-derivation, and full WASM codegen. |
| — | 17 Mar | TextMate syntax highlighting bundle. |
| — | 18 Mar | VS Code extension for Vera syntax highlighting. |
| v0.0.91 | 19 Mar | **Array operations**: array_slice, array_map, array_filter, array_fold, plus six monomorphization and WASM type-inference bug fixes. |
| v0.0.92 | 19 Mar | **BREAKING naming audit**: 14 built-ins renamed to the `domain_verb` convention, the last intentional breaking change before stabilisation. |
| — | 20 Mar | AI discoverability assets on veralang.dev: llms.txt, llms-full.txt, robots.txt, sitemap.xml, ai-plugin.json. |
| v0.0.93 | 20 Mar | **Standard prelude**: Option\<T\>, Result\<T, E\>, Ordering, and UrlParts injected automatically into every program. |

The abilities release (v0.0.90) was the last major type system feature. After v0.0.93, every Vera program had access to Option, Result, Ordering, combinators, and higher-order array operations without any boilerplate declarations.

---

## Stage 8: Data types and effects (23–27 March)

*Five days. Collections, JSON, HTML, HTTP, Decimal, and Inference — the features that make Vera an agent-viable language.*

This stage delivered the critical dependency chain that had driven the roadmap from the beginning: Map → JSON → HTTP → Inference, culminating in LLM calls as typed algebraic effects.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.94 | 23 Mar | **Map\<K, V\>**: eight built-in operations with Eq + Hash ability constraints, backed by opaque i32 handles. |
| v0.0.95 | 24 Mar | **Set\<T\>**: six built-in operations. |
| v0.0.96 | 24 Mar | Collections documentation sweep plus native JavaScript coverage for the browser runtime ([#337](https://github.com/aallan/vera/issues/337)). |
| v0.0.97 | 24 Mar | **Decimal**: exact decimal arithmetic across 14 built-in operations. |
| v0.0.98 | 25 Mar | **JSON**: the built-in `Json` ADT and 8 built-in functions to parse, query, and serialise structured data. |
| v0.0.99 | 25 Mar | **HTTP**: the `<Http>` algebraic effect, with `Http.get` and `Http.post` returning `Result<String, String>`. |
| v0.0.100 | 26 Mar | **HTML**: the built-in `HtmlNode` ADT with lenient parsing, CSS selector queries, and text extraction. |
| v0.0.101 | 27 Mar | **Inference**: LLM calls as typed algebraic effects, dispatching to Anthropic, OpenAI, or Moonshot, impossible to invoke from a pure function. |

v0.0.101 completed the chain. A Vera program can fetch data from the web, parse HTML or JSON, call an LLM, verify the response against contracts, and return typed results — all with every side effect tracked in the type system.

---

## Stage 9: Hardening and agent usability (28–31 March)

*Four days. Friction removal: the small issues that would bias any benchmark or frustrate any agent.*

With the core language complete, this stage cleared the path for honest evaluation while [VeraBench](https://github.com/aallan/vera-bench) began producing initial results in a separate repository.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.102 | 28 Mar | **Bug fixes**: the stdin double-read ([#335](https://github.com/aallan/vera/issues/335)) plus cross-module Option and pipe-into-qualified-call fixes. |
| — | 28 Mar | Typed CLI argument passing for `vera run --fn f -- arg` (String, Float64, Bool, Byte alongside Int). |
| — | 28 Mar | Agent discovery metadata: llms-txt link elements and JSON-LD TechArticle entries on veralang.dev. |
| v0.0.103 | 29 Mar | **CI security hardening** (pip-audit, ruff security rules, zizmor, SBOM) plus `vera version`, `--quiet`, and conformance additions. |
| v0.0.104 | 29 Mar | Bare `None`/`Err` constructors in generic calls type-check without `let` workarounds ([#293](https://github.com/aallan/vera/issues/293)). |
| v0.0.105 | 30 Mar | **Typed holes**: the `?` placeholder reports W001 with expected type and slot bindings, and blocks compilation with E614. |
| v0.0.106 | 31 Mar | `vera test` input generation extended to String and Float64 ([#169](https://github.com/aallan/vera/issues/169)). |

By v0.0.106, contract-driven testing covered every primitive parameter type, and the friction list for the first full benchmark sweep was clear.

---

## Stage 10: Evaluation and CI quality (7–11 April)

*A week of VeraBench evaluation in parallel, then compiler fixes informed by the results.*

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.107 | 7 Apr | CI validation for `examples/README.md` run commands ([#361](https://github.com/aallan/vera/issues/361)). |
| v0.0.108 | 7 Apr | **`vera check --explain-slots`** ([#445](https://github.com/aallan/vera/issues/445)): the slot resolution table addressing the dominant VeraBench failure mode, plus a prescriptive SKILL.md rework. |
| — | 8 Apr | **Multi-model evaluation** (VeraBench v0.0.7): 6 models across 3 providers, with Kimi K2.5 hitting 100% run-correct on Vera against 86% on Python. |
| — | 9 Apr | Two effect-runtime bug fixes: `Exn<String>` WASM tag encoding ([#416](https://github.com/aallan/vera/issues/416)) and nested handler isolation. |
| v0.0.109 | 10 Apr | Closure `i32_pair` parameter and return types fixed so String/Array values in closures emit correct two-slot WAT ([#359](https://github.com/aallan/vera/issues/359)). |
| v0.0.110 | 10 Apr | **Mistral provider** for `Inference.complete`, with the provider registry refactored so new providers are a one-row change ([#413](https://github.com/aallan/vera/issues/413)). |
| v0.0.111 | 10 Apr | SMT translator declares String/Float64 parameters with correct Z3 sorts, promoting the string predicates to Tier 1. |

The evaluation verdict: flagship models held Vera even with Python, and the failure modes clustered on missing primitives — which set the agenda for Stage 11.

---

## Stage 11: Standard library depth (16–23 April)

*Eight days. The utility built-ins any real program needs.*

VeraBench identified missing primitives as the dominant friction: models reaching for `array_sort` or `string_reverse` and finding nothing, then hand-rolling fragile implementations. This stage added the math, string, array, and JSON surfaces that real programs assume.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.112 | 16 Apr | **Fix GC shadow stack overflow** ([#464](https://github.com/aallan/vera/issues/464)). |
| v0.0.113 | 16 Apr | **Decompose `calls.py` into 8 subsystem mixins** ([#418](https://github.com/aallan/vera/issues/418)). |
| — | 16 Apr | **CHANGELOG enforcement at pre-push and CI** ([#478](https://github.com/aallan/vera/issues/478)). |
| — | 17 Apr | **Widen GC object header size field from 16-bit to 31-bit** ([#484](https://github.com/aallan/vera/issues/484)). |
| — | 17 Apr | **Iterative WASM higher-order array ops** ([#480](https://github.com/aallan/vera/issues/480)). |
| v0.0.114 | 17 Apr | **`IO.sleep`, `IO.time`, `IO.stderr`** ([#463](https://github.com/aallan/vera/issues/463)). |
| v0.0.115 | 18 Apr | **`Random` effect** ([#465](https://github.com/aallan/vera/issues/465)). |
| v0.0.116 | 20 Apr | **Math built-ins** ([#467](https://github.com/aallan/vera/issues/467)). |
| — | 22 Apr | **Dependabot uv ecosystem + auto-uv-lock** ([#500](https://github.com/aallan/vera/pull/500)). |
| v0.0.117 | 22 Apr | **Array utility built-ins, phase 1** ([#466](https://github.com/aallan/vera/issues/466)). |
| v0.0.118 | 23 Apr | **String utilities + character classification** ([#470](https://github.com/aallan/vera/issues/470)). |
| v0.0.119 | 23 Apr | **JSON typed accessors** ([#366](https://github.com/aallan/vera/issues/366)). |

After v0.0.119 the missing-primitive complaints stopped; what remained was runtime correctness at scale.

---

## Stage 12: The bug-killing campaign (26 April – 8 May)

*Thirteen days. Sixteen runtime and codegen bugs, a Game of Life, and the debugging UX to match.*

Agent-written programs at real scale — capstone: Conway's Life — drove a sustained campaign through the closure, GC-rooting, and string-interpolation layers. Crash-debugging UX shipped alongside the fixes: trap kinds, source backtraces, fix suggestions, and live stdout.

| Version | Date | What shipped |
|---------|------|-------------|
| — | 26 Apr | veralang.dev homepage redesign: editorial-research aesthetic with the bilingual reading-path device. |
| v0.0.120 | 26 Apr | **Crash-debugging UX: trap categorisation + stdout preserved on trap** ([#522](https://github.com/aallan/vera/issues/522)). |
| v0.0.121 | 27 Apr | **Nested closures + ADT capture work end-to-end** ([#514](https://github.com/aallan/vera/issues/514)). |
| v0.0.122 | 27 Apr | **Conservative GC bounds-checked against `$heap_ptr`** ([#515](https://github.com/aallan/vera/issues/515)). |
| v0.0.123 | 27 Apr | **`IO.print` writes flush live to `sys.stdout`** ([#543](https://github.com/aallan/vera/issues/543)). |
| v0.0.124 | 27 Apr | **Runtime traps now include a source backtrace** ([#516](https://github.com/aallan/vera/issues/516)). |
| v0.0.125 | 28 Apr | **Runtime traps now include actionable fix suggestions** ([#547](https://github.com/aallan/vera/issues/547)). |
| v0.0.126 | 28 Apr | **Tail-recursive iteration runs in constant stack space** ([#517](https://github.com/aallan/vera/issues/517)). |
| v0.0.127 | 29 Apr | **`@Nat` subtraction soundness hole closed** ([#520](https://github.com/aallan/vera/issues/520)). |
| v0.0.128 | 5 May | **WASM call translator critical safety fixes** ([#475](https://github.com/aallan/vera/issues/475)). |
| v0.0.129 | 5 May | **WASM call translator major correctness fixes** ([#475](https://github.com/aallan/vera/issues/475)). |
| v0.0.130 | 5 May | **Pair-type closure captures preserve their len field** ([#535](https://github.com/aallan/vera/issues/535)). |
| v0.0.131 | 5 May | **GC infrastructure batch** ([#487](https://github.com/aallan/vera/issues/487)). |
| v0.0.132 | 5 May | **Opaque-handle GC-rooting hygiene** ([#347](https://github.com/aallan/vera/issues/347)). |
| v0.0.133 | 5 May | **Iterative array builders no longer leak closure return-value root** ([#570](https://github.com/aallan/vera/issues/570)). |
| v0.0.134 | 6 May | **Active reclamation of host-store handles via heap-wrap-as-ADT** ([#573](https://github.com/aallan/vera/issues/573)). |
| v0.0.135 | 6 May | **Three codegen bug fixes** ([#584](https://github.com/aallan/vera/issues/584)). |
| v0.0.136 | 6 May | **Two host-runtime hygiene fixes** ([#586](https://github.com/aallan/vera/issues/586)). |
| — | 7 May | `examples/life.vera`: Conway's Game of Life with nested array combinators, a recursive `<IO>` loop, ANSI rendering, and the formal B3/S23 rule on `next_cell`. |
| — | 7 May | `VERA_EAGER_GC=1` debug knob: GC on every `$alloc` so missing-shadow-root bugs surface immediately (documented in ENVIRONMENT.md). |
| v0.0.137 | 7 May | **Captured-`Array<T>` indexing inside closure body** ([#588](https://github.com/aallan/vera/issues/588)). |
| v0.0.138 | 7 May | **Closure-return shadow-push asymmetry** ([#593](https://github.com/aallan/vera/issues/593)). |
| v0.0.139 | 8 May | Closure codegen pair: `f()[i]` element-type inference ([#614](https://github.com/aallan/vera/issues/614)) and capture ordering. |
| v0.0.140 | 8 May | String-returning FnCall in interpolation ([#602](https://github.com/aallan/vera/issues/602)). |
| v0.0.141 | 8 May | Inline-refinement return types in interpolation, the third trigger in the same bug class. |
| v0.0.142 | 8 May | Structural close of the string-interpolation bug class across its four remaining sibling sites ([#630](https://github.com/aallan/vera/issues/630)). |

On 7 May the first agent-written Life ran 200+ generations of Gosper Glider Gun, R-pentomino, and Pentadecathlon with zero corruption; v0.0.142 closed the campaign's last bug class structurally.

---

## Stage 13: Stabilisation and memory safety (10–29 May)

*Twenty days. The enforcement infrastructure, then the end of the GC bug class.*

First the gates: Windows in CI, walker-completeness enforcement, the stress harness, fail-closed testing. Then the memory-safety arc that ended the conservative-GC retention and host-store reclamation bugs, emptying the runtime-workarounds table by v0.0.160.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.143 | 10 May | Windows joins the CI matrix fully strict ([#640](https://github.com/aallan/vera/issues/640)). |
| v0.0.144 | 11 May | Tier A bug burn-down closed four checker and codegen issues ([#633](https://github.com/aallan/vera/issues/633)). |
| v0.0.145 | 11 May | Mono-suffix bug fix plus template-warning suppression ([#604](https://github.com/aallan/vera/issues/604)). |
| v0.0.146 | 12 May | Refinement-of-Array element inference ([#655](https://github.com/aallan/vera/issues/655)). |
| v0.0.147 | 12 May | Cross-module `_fn_ret_type_exprs` propagation ([#628](https://github.com/aallan/vera/issues/628)). |
| v0.0.148 | 12 May | Type-alias arity check E133 ([#660](https://github.com/aallan/vera/issues/660)). |
| v0.0.149 | 12 May | Cyclic type aliases now produce E132 ([#648](https://github.com/aallan/vera/issues/648)). |
| v0.0.150 | 12 May | Nested type aliases through `Array<...>` compile and run ([#559](https://github.com/aallan/vera/issues/559)). |
| v0.0.151 | 12 May | Walker-completeness audit with pre-commit enforcement ([#597](https://github.com/aallan/vera/issues/597)). |
| v0.0.152 | 13 May | Stress-test harness for scale-dependent regression coverage ([#596](https://github.com/aallan/vera/issues/596)). |
| v0.0.153 | 13 May | SMT translator covers `FloatLit` / `IndexExpr` / `ArrayLit` in contracts ([#667](https://github.com/aallan/vera/issues/667)). |
| v0.0.154 | 13 May | GC-aware tail-call optimization for allocating functions ([#549](https://github.com/aallan/vera/issues/549)). |
| v0.0.155 | 13 May | Wrapper-handle bit-31 tagging closes the last conservative-GC retention bug ([#578](https://github.com/aallan/vera/issues/578)). |
| v0.0.156 | 19 May | `vera test` fails closed on verifier-refuted contracts ([#674](https://github.com/aallan/vera/issues/674)). |
| v0.0.157 | 19 May | `IO.read_char` effect operation for single-character input ([#618](https://github.com/aallan/vera/issues/618)). |
| v0.0.158 | 19 May | Host-side shadow-stack rooting closes the last `$gc_collect`-during-host-walk free-list-corruption bug ([#692](https://github.com/aallan/vera/issues/692)). |
| v0.0.159 | 28 May | `Map<K, T_heap>` and `Set<T_heap>` no longer drop heap-pointer values under GC pressure on either target ([#695](https://github.com/aallan/vera/issues/695)). |
| v0.0.160 | 29 May | Ctrl-C-during-host-import handling centralized on `wasmtime>=45.0.0`, removing the four per-import workaround guards ([#599](https://github.com/aallan/vera/issues/599)). |

After v0.0.160 the known GC bug surface was clear, the runtime-workarounds table was empty, and attention turned to the editor loop.

---

## Stage 14: The language server (10 June onwards)

*The compiler learns to hold a conversation.*

Proof obligations became first-class records with a warm Z3 session, and the LSP server grew from transport skeleton to proof-delta workflows that agents call directly.

| Version | Date | What shipped |
|---------|------|-------------|
| v0.0.161 | 10 Jun | Proof obligations reified as first-class records with a warm-Z3 `VerificationSession`, the semantic core for the LSP server ([#222](https://github.com/aallan/vera/issues/222) Phase A). |
| v0.0.162 | 10 Jun | Incremental verification: unchanged functions replay cached obligations instead of re-entering Z3 ([#222](https://github.com/aallan/vera/issues/222) Phase B). |
| v0.0.163 | 10 Jun | `vera lsp` serves LSP over stdio: transport skeleton, document sync, and the coordinate-conversion layer ([#222](https://github.com/aallan/vera/issues/222) Phase C). |
| v0.0.164 | 10 Jun | LSP language features: tier-annotated diagnostics, type hover, slot go-to-definition, and typed-hole completion ([#222](https://github.com/aallan/vera/issues/222) Phase D). |
| v0.0.165 | 11 Jun | `vera/speculativeEdit` proof-delta: agents learn whether an edit keeps, breaks, or strengthens the program's proofs before committing it ([#222](https://github.com/aallan/vera/issues/222) Phase E). |
| v0.0.166 | 11 Jun | `vera/proposeEdit`: edit, verify, and apply as one LSP method, applying only when the proof delta is non-breaking ([#222](https://github.com/aallan/vera/issues/222) Phase F1). |
| v0.0.167 | 11 Jun | `vera/strengthenContract`: contract changes with a call-site audit that refuses when a caller no longer satisfies a tightened precondition ([#222](https://github.com/aallan/vera/issues/222) Phase F2). |
| v0.0.168 | 11 Jun | `vera/addEffect` rewrites the `effects(...)` clauses of a function and its transitive callers in one verified multi-site edit, closing [#222](https://github.com/aallan/vera/issues/222). |
| v0.0.169 | 11 Jun | The language server gets its user manual (LSP_SERVER.md) and the VS Code extension gains an LSP client ([#222](https://github.com/aallan/vera/issues/222) follow-up). |
| v0.0.170 | 12 Jun | **Editor hovers now carry the same Fix: instructions as `--json`, exactly once per call site** ([#728](https://github.com/aallan/vera/issues/728)). |
| v0.0.171 | 15 Jun | **Map and Set host storage moved to bucket-as-truth across the CLI and browser runtimes, deleting the Python/JS mirror so collection contents live in one place** ([#706](https://github.com/aallan/vera/issues/706)). |
| v0.0.172 | 16 Jun | **The `@Nat >= 0` invariant is now obligation-checked at every binding site, not just `@Nat` subtractions** ([#552](https://github.com/aallan/vera/issues/552)). |
| v0.0.173 | 17 Jun | **The `@Nat >= 0` narrowing obligation now covers every projection and instantiation binding site (ADT sub-patterns, non-literal tuple destructures, generic and imported constructors), with runtime guards at the concrete sites, generic function calls, and builtin `@Nat` parameters** ([#747](https://github.com/aallan/vera/issues/747)). |
| v0.0.174 | 19 Jun | **General refinement-type predicates are now verified statically: a value narrowing into a `{ @T \| P }` slot or returned at a refined return position carries a Tier-1 obligation that the predicate holds (or a runtime guard at the function boundary where the predicate is untranslatable), generalising the `@Nat` machinery from the baked-in `>= 0` to an arbitrary predicate** ([#746](https://github.com/aallan/vera/issues/746)). |
| v0.0.175 | 21 Jun | **Generic function bodies are now statically verified at each concrete instantiation instead of being silently deferred to runtime** ([#732](https://github.com/aallan/vera/issues/732)). |
| v0.0.176 | 21 Jun | **A call's precondition is now checked even when the call's result is discarded** ([#730](https://github.com/aallan/vera/issues/730)). |
| v0.0.177 | 21 Jun | **Integer division/modulo by zero and array index bounds now carry auto-synthesised obligations, closing the last Tier-0 silent failure where `vera verify` passed a program that then trapped at runtime** ([#680](https://github.com/aallan/vera/issues/680)). |

---

## By the numbers

| Metric | v0.0.1 (23 Feb) | v0.0.9 (23 Feb) | v0.0.39 (27 Feb) | v0.0.65 (4 Mar) | v0.0.88 (12 Mar) | v0.0.101 (27 Mar) | v0.0.134 (6 May) | v0.0.170 (12 Jun) |
|--------|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| Compiler layers | Parser | 5 (full pipeline) | 5 + modules | 5 + modules + GC | 5 + modules + GC + browser | 5 + modules + GC + browser | 5 + modules + GC + browser | 5 + modules + GC + browser + LSP |
| Tests | ~50 | ~300 | ~600 | ~1,400 | ~2,300 | 3,095 | 3,716 | 4,342 |
| Examples | 13 | 15 | 16 | 18 | 24 | 30 | 33 | 35 |
| Built-in functions | 0 | 0 | ~5 | ~30 | ~80 | 122 | 164 | 164 |
| Conformance programs | 0 | 0 | 0 | 0 | ~50 | 64 | 82 | 89 |
| Spec chapters | 7 | 10 | 11 | 12 | 13 | 13 | 13 | 13 |
| Code coverage | — | — | — | 90% | 91% | 96% | 96% | 95% |

Total: **1,400+ commits, 174 tagged releases, 77 active development days.**
