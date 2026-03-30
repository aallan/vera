# Roadmap

Vera v0.0.105 delivers a complete compiler pipeline — parse, transform, type-check, verify contracts via Z3, compile to WebAssembly, execute at the command line or in the browser — with 122 built-in functions, algebraic effects (IO, Http, State, Exceptions, Async, Inference), constrained generics, a module system, contract-driven testing, and a canonical formatter. The core language is done. What follows is the path from "working language" to "the language agents actually use."

This roadmap is organised around four strategic milestones. Each milestone makes Vera meaningfully more useful to a concrete audience. Within each milestone, work is grouped into phases that can be executed roughly sequentially, though independent items can be interleaved.

See [HISTORY.md](HISTORY.md) for a narrative account of how the compiler was built.

## Where we are

The compiler is complete end-to-end: parse, type-check, verify contracts via Z3, compile to WebAssembly, and run — at the command line and in the browser. The language has 122 built-in functions, algebraic effects (IO, Http, State, Exceptions, Async, Inference), constrained generics, a module system, contract-driven testing, and a canonical formatter. Type inference for bare constructors (`None`, `Err`, `Ok`) now works correctly across all call sites. The compiler has 3,200 tests, 72 conformance programs, 30 examples, and a 13-chapter specification.

Significant progress has been made towards Vera being a viable agent target. [VeraBench](https://github.com/aallan/vera-bench) — a 50-problem benchmark across 5 difficulty tiers with canonical Vera and Python solutions — is complete and has produced initial results: Claude Sonnet 4 achieves 96% check@1 and 83% run_correct on Vera versus 92% on Python, a 9-percentage-point gap that is smaller than might be expected for a new language. The dominant failure mode is De Bruijn slot ordering, confirming the hypothesis that `@T.n` indexing is the main learning curve for models. The remaining gaps are empirical breadth (more model baselines, Phase 3 reporting), standard library depth (HTTP hardening, server effects), and tooling integration (LSP).

---

## Milestone 1: Prove the thesis

*Goal: answer the fundamental question — do LLMs write better code in Vera than in existing languages? Build the evidence base and fix the friction points that block honest evaluation.*

This is the most important milestone. Everything else — adoption, ecosystem, research credibility — depends on having data that supports (or refutes) the core claim. Simultaneously, fix the small issues that would distort any benchmark or frustrate any agent trying to use the language seriously.

Phase 1a (evaluation friction removal) is complete — see [HISTORY.md](HISTORY.md) Stage 9 for details.

### Phase 1b: Benchmark suite

**[VeraBench](https://github.com/aallan/vera-bench)** is a separate repository containing 50 problems across 5 difficulty tiers with canonical solutions written in Vera, Python, and Typescript.

- [#225](https://github.com/aallan/vera/issues/225) **Benchmark suite** — The benchmark covers five difficulty tiers:
  1. **Pure arithmetic** — functions with 1–2 parameters, simple contracts (the easy case for `@T.n`)
  2. **String and array manipulation** — functions using built-ins, testing whether agents find the right `domain_verb` names
  3. **ADTs and pattern matching** — custom data types, exhaustive match, testing De Bruijn indices in match arms
  4. **Recursive functions with termination proofs** — `decreases` clauses, testing whether agents produce provably terminating code
  5. **Multi-function programs with effects** — IO, State, Http, Inference, testing cross-function contract coherence

  All four evaluation modes run on Claude Sonnet 4 across 50 problems.

  Complete cross-language benchmark with Claude Sonnet 4 across 50 problems.

  ### Summary

  | Mode | check@1 | verify@1 | fix@1 | run_correct |
  |------|---------|----------|-------|-------------|
  | Vera (full-spec) | 94% | 98% | 67% | 83% |
  | Vera (spec-from-NL) | 94% | 88% | 33% | 78% |
  | Python (LLM) | 100% | - | - | 92% |
  | TypeScript (LLM) | 100% | - | - | 79% |
  | Python baseline | 100% | - | - | 100% |
  | TypeScript baseline | 100% | - | - | 100% |

  ### By Tier (run_correct)

  | Language | Tier 1 | Tier 4 | Tier 5 |
  |----------|--------|--------|--------|
  | Vera full-spec | 100% | 75% | 67% |
  | Vera spec-from-NL | 100% | 50% | 80% |
  | Python LLM | 100% | 100% | 67% |
  | TypeScript LLM | 100% | 88% | 33% |
  | Both baselines | 100% | 100% | 100% |

  ### Key findings

  **TypeScript is surprisingly worse than Vera.** Sonnet's TypeScript achieves only 79% run_correct — below Vera's 83% (full-spec). The damage is in Tier 5 where TypeScript drops to 33% vs Python's 67% and Vera's 67%. Sonnet struggles with stateful/effectful patterns in TypeScript more than in Python, likely because the problems describe Vera-style state handlers which map more naturally to Python's imperative state than TypeScript's class/closure patterns.

  **Python remains the strongest LLM target.** 92% run_correct, 100% check. Python's familiarity in training data and direct imperative style make it the easiest language for these problems.

  **Vera with contracts beats TypeScript without them.** Vera full-spec (83%) outperforms TypeScript (79%) despite being a novel language not in training data. The contract system provides guardrails that compensate for the syntactic unfamiliarity.

  **The ranking: Python (92%) > Vera full-spec (83%) > TypeScript (79%) > Vera spec-from-NL (78%).** Writing contracts from scratch is harder than writing in an unfamiliar language with contracts given.


### Phase 1c: Expand contract-driven testing

- [#169](https://github.com/aallan/vera/issues/169) → [#170](https://github.com/aallan/vera/issues/170) **`vera test` input generation for String, Float64, compound types** — currently `vera test` skips any function with non-Int/Nat/Bool parameters. String generation: empty, single char, ASCII printable, unicode edge cases. Float64: 0.0, -0.0, small, large, subnormals. This unblocks contract-driven testing for most real programs.
- [#170](https://github.com/aallan/vera/issues/170) **Hypothesis integration** — use Hypothesis strategies for input generation, enabling property-based contract testing with shrinking. This is the long-term path to replacing hand-written test generation with a mature fuzzing framework.

---

## Milestone 2: Verified agent orchestration

*Goal: a working MCP tool server written in Vera, with contracts guaranteeing tool schemas at compile time. This is the flagship demo — the thing that makes people understand why Vera exists.*

This milestone follows the critical dependency chain that has driven the project since the roadmap was first written. Map, JSON, HTTP, and Inference are complete. What remains is the server side.

### Phase 2a: Inference effect hardening

The `<Inference>` effect is the headline feature. Harden it before building on top of it.

- [#370](https://github.com/aallan/vera/issues/370) **Configurable `max_tokens` / `temperature`** — currently hardcoded; agent workloads need control over both.
- [#372](https://github.com/aallan/vera/issues/372) **User-defined `handle[Inference]` handlers** — currently the Inference effect cannot be handled in user code; full handler support enables mocking, caching, and routing strategies.
- [#371](https://github.com/aallan/vera/issues/371) **`Inference.embed` operation** — `Array<Float64>` vector embeddings for semantic search and retrieval. Depends on #373 (float array host-alloc infrastructure).
- [#373](https://github.com/aallan/vera/issues/373) **Float array host-alloc infrastructure** — `_alloc_result_ok_float_array` support for returning float arrays from host imports. Required by #371.
- [#413](https://github.com/aallan/vera/issues/413) **Add Mistral AI provider + provider registry refactor** — replace the `elif` chain in `_call_inference_provider()` with a `_ProviderConfig` dataclass and `_PROVIDERS` registry dict, then add Mistral as the fourth provider. At five providers (three structurally identical OpenAI-compatible endpoints) the table-driven approach collapses the dispatch to ~20 lines; adding further providers becomes a one-row change.
- [#425](https://github.com/aallan/vera/issues/425) **Add xAI Grok provider to the Inference effect** — one-row addition to the `_PROVIDERS` registry introduced in #413. Endpoint: `api.x.ai/v1/chat/completions`; env var: `VERA_XAI_API_KEY`. Depends on #413.
- [#379](https://github.com/aallan/vera/issues/379) **Add an Inference + JSON composition example** — demonstrate `Inference.complete` → `json_parse` → typed extraction. This is the pattern every real agent workload will use and it should be a first-class example.
- [#380](https://github.com/aallan/vera/issues/380) **Add an effect handler mocking example** — show `handle[Inference] { complete(@String) -> { resume(Ok("mock")) } } in { ... }` for deterministic testing. This demonstrates the key architectural advantage of modelling inference as an algebraic effect.

### Phase 2b: Server-side effects

**Http effect hardening** — the Http effect shipped in v0.0.99 with basic GET/POST. These issues extend it to production capability:

- [#351](https://github.com/aallan/vera/issues/351) Custom headers support
- [#352](https://github.com/aallan/vera/issues/352) HTTP status code access in responses
- [#353](https://github.com/aallan/vera/issues/353) Per-request timeout control
- [#355](https://github.com/aallan/vera/issues/355) Replace deprecated synchronous XHR in browser runtime
- [#356](https://github.com/aallan/vera/issues/356) PUT, PATCH, DELETE methods

**Server effects:**

- [#237](https://github.com/aallan/vera/issues/237) **WASI 0.2 compliance** — prerequisite for incoming-handler support. Audit the current wasmtime integration against the WASI 0.2 spec; identify gaps in filesystem, networking, and clock access.
- [#305](https://github.com/aallan/vera/issues/305) **HTTP Server effect** — `effects(<HttpServer>)` with `handle[HttpServer]` mapping incoming requests to effect operations. Contracts verify response schemas. Depends on WASI 0.2.
- [#306](https://github.com/aallan/vera/issues/306) **MCP Server effect** — `effects(<McpServer>)` implementing the JSON-RPC protocol over HTTP. Contracts guarantee tool input/output schemas at compile time. Depends on HTTP Server + JSON. **This is the flagship use case.**
- [#239](https://github.com/aallan/vera/issues/239) **Resource limit configuration** — fuel, memory, and timeout limits for WASM execution. Essential for server workloads where untrusted input could trigger pathological computation.

### Phase 2c: Server-adjacent capabilities

These are not strictly required for the MCP demo but would make it more compelling.

- [#233](https://github.com/aallan/vera/issues/233) **Date and time** (ISO 8601) — agent workloads frequently need timestamps for logging, cache expiry, and scheduling.
- [#235](https://github.com/aallan/vera/issues/235) **Cryptographic hashing** (SHA-256, HMAC) — needed for API authentication (webhook signatures, OAuth).
- [#229](https://github.com/aallan/vera/issues/229) **Database access effect** — `<DB>` with `query`/`execute` operations, parameterised queries only. Phase 1: positional rows, SQLite. Phase 2: named columns. Phase 3: JSON columns. See [#309](https://github.com/aallan/vera/issues/309) for contract-verified SQL injection prevention.
- [#236](https://github.com/aallan/vera/issues/236) **CSV parsing and generation** — common data interchange format for agent workloads.

---

## Milestone 3: Tooling for real-world adoption

*Goal: agents can discover Vera, learn it from documentation, write code with real-time feedback, and integrate it into existing workflows. Vera becomes a practical choice, not just an interesting experiment.*

### Phase 3a: Agent integration

- [#222](https://github.com/aallan/vera/issues/222) **LSP server** — the standard integration protocol for production coding agents (Claude Code, Cursor, Copilot, Windsurf). The existing `--json` infrastructure provides most of what's needed. An LSP enables real-time feedback as agents write code — diagnostics, hover information, completion suggestions. This is the single highest-leverage adoption enabler.
- [#329](https://github.com/aallan/vera/issues/329) **Plumbing integration** — Vera WASM modules as verified tool calls in [Plumbing](https://arxiv.org/abs/2602.13275) agent graphs. Typed port interface maps Plumbing stream types to Vera ADTs at the JSON serialisation boundary.
- [#183](https://github.com/aallan/vera/issues/183) **Human-readable slot annotations** — optional `-- name` annotations on slot references that are preserved by the formatter but ignored by the compiler. Bridges the readability gap for human reviewers of agent-generated code without compromising the De Bruijn system.
- [#181](https://github.com/aallan/vera/issues/181) **Signature refactoring** — mechanical slot index rewriting when function signatures change. Essential for any refactoring workflow, whether human or agent-driven.

### Phase 3b: Discoverability improvements

- **Register with llms.txt directories** — submit to [llms-txt-hub](https://github.com/thedaviddias/llms-txt-hub) and [llmstxthub.com](https://llmstxthub.com). Manual task, no code change required.
- [#401](https://github.com/aallan/vera/issues/401) **MCP documentation endpoint** — a static MCP server (via mcpdoc or similar) that serves Vera documentation to MCP-aware tools. Low lift, high discoverability for the growing MCP ecosystem.

### Phase 3c: Developer experience

- [#224](https://github.com/aallan/vera/issues/224) **REPL** — interactive exploration for both agents and humans. Useful for rapid prototyping and debugging.
- [#143](https://github.com/aallan/vera/issues/143) **Comprehensive example programs** — expand from 30 to 50+ examples covering every major pattern: API clients, data pipelines, text processing, LLM orchestration, effect composition.
- [#337](https://github.com/aallan/vera/issues/337) **Native JavaScript coverage** — c8 + Codecov for the browser runtime, ensuring parity testing has the same visibility as Python-side coverage.

---

## Milestone 4: Language maturity

*Goal: Vera handles the long tail of real-world requirements — concurrency, streaming, packages, incremental compilation. The language is not just viable but competitive.*

### Phase 4a: Concurrency and streaming

- [#59](https://github.com/aallan/vera/issues/59) **True async concurrency** — the type-level infrastructure (`Future<T>`, `async`/`await`, `<Async>` effect) shipped in v0.0.82, but execution is eager/sequential. True concurrency requires WASI 0.3 for native `future<T>`/`stream<T>` support.
- [#406](https://github.com/aallan/vera/issues/406) **WASI 0.3** — native async I/O, required for concurrent request handling in server effects. Depends on #237.
- [#270](https://github.com/aallan/vera/issues/270) **`handle[Async]`** — custom scheduling strategies for async effect handlers.
- [#228](https://github.com/aallan/vera/issues/228) **WebSocket/SSE** — streaming clients for real-time data feeds and LLM streaming responses.
- [#227](https://github.com/aallan/vera/issues/227) **Timeout effect** — `<Timeout>` for cancellation and deadline management.

### Phase 4b: Ecosystem

- [#130](https://github.com/aallan/vera/issues/130) **Package system and registry** — the ability to share and reuse Vera libraries. This is the transition from "a language" to "a platform."
- [#163](https://github.com/aallan/vera/issues/163) **Standalone WASM runtime package** — distribute Vera programs as self-contained WASM binaries without requiring the Python compiler.
- [#238](https://github.com/aallan/vera/issues/238) **Component Model (WIT) interop** — expose Vera functions as WASM components that other languages can call, and call components written in other languages from Vera.
- [#56](https://github.com/aallan/vera/issues/56) **Incremental compilation** — essential for large codebases and fast feedback loops in agent workflows.
- [#294](https://github.com/aallan/vera/issues/294) **Effect row variable unification** — full effect polymorphism. Extends the current effect system to support higher-order functions that are polymorphic over their effect rows.

### Phase 4c: Standard library completeness

- [#366](https://github.com/aallan/vera/issues/366) **JSON typed accessors** — `json_as_string`, `json_get_number`, etc. Eliminates the two-level pattern match every JSON API consumer currently writes.
- [#367](https://github.com/aallan/vera/issues/367) **Markdown content extractors** — `md_blocks`, `md_inline_text`, `md_extract_headings`, `md_extract_links`, `md_filter_blocks`.
- [#368](https://github.com/aallan/vera/issues/368) **HTML convenience accessors** — `html_query_one`, `html_tag`, `html_children`.
- [#187](https://github.com/aallan/vera/issues/187) → [#127](https://github.com/aallan/vera/issues/127) **Module-qualified call disambiguation → module re-exports** — sequential dependency; completes the module system.

---

## Continuous: quality and security hardening

These are not milestone-gated — they should be addressed continuously alongside feature work. Prioritised by impact.

### CI tooling

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Add property-based testing with Hypothesis | [#386](https://github.com/aallan/vera/issues/386) | 2–4 hours | Catches parser/formatter edge cases via round-trip properties |
| Add mutation testing with mutmut (detection only) | [#387](https://github.com/aallan/vera/issues/387) | 2–4 hours | Measures whether 3,200 tests catch real bugs, not just execute paths |
| Investigate parser fuzzing with Atheris | [#402](https://github.com/aallan/vera/issues/402) | 4–8 hours | Crash-inducing inputs for parser and type checker |
| Add hash-pinned lockfile (pip-compile or uv lock) | [#390](https://github.com/aallan/vera/issues/390) | 30 min | Prevents dependency confusion attacks |
| Improve browser runtime test coverage to >80% | [#349](https://github.com/aallan/vera/issues/349) | 2–4 hours | Parity with Python-side coverage gate |
| Validate examples/README.md run commands in CI | [#361](https://github.com/aallan/vera/issues/361) | 1–2 hours | Prevents stale example invocations |

### Verification depth

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Tier 2 verification — Z3 with hints from `assert` and lemma functions | [#427](https://github.com/aallan/vera/issues/427) | 2–4 days | Promotes function-call and quantifier contracts from runtime to statically proved; completes the three-tier pipeline specified in §6.3.2 |

### Security

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Add Z3 solver timeout per contract | [#391](https://github.com/aallan/vera/issues/391) | 30 min | Prevents DoS via pathological contracts |
| Audit `smt.py` for soundness | [#392](https://github.com/aallan/vera/issues/392) | 4–8 hours | A bug here silently bypasses verification |

### Testing gaps

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|

---

## Completed phases

The compiler was built through ten development phases from February to March 2026. Each phase added a complete compiler layer with tests, documentation, and working examples. See [HISTORY.md](HISTORY.md) for the full narrative.

| Phase | Version | Layer | Status |
|-------|---------|-------|--------|
| C1 | v0.0.1–v0.0.3 | **Parser** — Lark LALR(1) grammar, LLM diagnostics, 13 examples | Done |
| C2 | v0.0.4 | **AST** — typed syntax tree, Lark→AST transformer | Done |
| C3 | v0.0.5 | **Type checker** — decidable type checking, slot resolution, effect tracking | Done |
| C4 | v0.0.8 | **Contract verifier** — Z3 integration, refinement types, counterexamples | Done |
| C5 | v0.0.9 | **WASM codegen** — compile to WebAssembly, `vera compile` / `vera run` | Done |
| C6 | v0.0.10–v0.0.24 | **Codegen completeness** — ADTs, match, closures, effects, generics in WASM | Done |
| C6.5 | v0.0.25–v0.0.30 | **Codegen cleanup** — handler fixes, missing operators, String/Array support | Done |
| C7 | v0.0.31–v0.0.39 | **Module system** — cross-file imports, visibility, multi-module compilation | Done |
| C8 | v0.0.40–v0.0.65 | **Polish** — refactoring, tooling, diagnostics, verification depth, codegen gaps | Done |
| C8.5 | v0.0.66–v0.0.88 | **Completeness** — builtins, IO runtime, types, effects, browser target | Done |
| C9 | v0.0.89–v0.0.101 | **Abilities, standard library, data types, effects** — Eq/Ord/Hash/Show, Map/Set, JSON, HTML, Markdown, Http, Decimal, Inference, standard prelude, combinators, higher-order array ops | Done |

**630+ commits, 105 tagged releases, 3,200 tests, 96% coverage, 72 conformance programs, 30 examples, 13 spec chapters.** See [HISTORY.md](HISTORY.md) for the full narrative of how the compiler was built.
