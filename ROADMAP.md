# Roadmap

Vera v0.0.102 delivers a complete compiler pipeline — parse, transform, type-check, verify contracts via Z3, compile to WebAssembly, execute at the command line or in the browser — with 122 built-in functions, algebraic effects (IO, Http, State, Exceptions, Async, Inference), constrained generics, a module system, contract-driven testing, and a canonical formatter. The core language is done. What follows is the path from "working language" to "the language agents actually use."

This roadmap is organised around four strategic milestones. Each milestone makes Vera meaningfully more useful to a concrete audience. Within each milestone, work is grouped into phases that can be executed roughly sequentially, though independent items can be interleaved.

See [HISTORY.md](HISTORY.md) for a narrative account of how the compiler was built.

## Where we are

**v0.0.102** — Phase 1a (evaluation friction removal) is underway. Three blocking bugs fixed (#360, #326, #335). CLI argument passing now supports all Vera types — Int, Float64, Bool, Byte, String (#263). Agent discovery metadata added to veralang.dev (#400). The compiler now has 3,121 tests, 65 conformance programs, 30 examples, and a 13-chapter specification.

**v0.0.101** — the reference compiler completed eleven development phases (C1–C9, including C6.5 and C8.5), with 3,095 tests, 96% code coverage of 15,149 statements, 64 conformance programs, 30 examples, and a 13-chapter specification. The `<Inference>` algebraic effect makes LLM calls explicit in the type system — the headline feature that distinguishes Vera from every other verified language. A Vera program can make an HTTP request, parse JSON, call an LLM, and return typed, contract-verified results. AI discoverability (llms.txt, llms-full.txt, robots.txt, sitemap.xml, ai-plugin.json) is deployed on veralang.dev.

An independent assessment rates the project at **60–70% of the way to being a viable agent target.** The remaining 30–40% is standard library breadth, tooling integration, empirical validation, and the server-side effect chain that unlocks the flagship use case.

---

## Milestone 1: Prove the thesis

*Goal: answer the fundamental question — do LLMs write better code in Vera than in existing languages? Build the evidence base and fix the friction points that block honest evaluation.*

This is the most important milestone. Everything else — adoption, ecosystem, research credibility — depends on having data that supports (or refutes) the core claim. Simultaneously, fix the small issues that would distort any benchmark or frustrate any agent trying to use the language seriously.

### Phase 1a: Remove friction from evaluation

These are quick fixes that would bias any benchmark or frustrate any evaluator. Do them first.

- [#293](https://github.com/aallan/vera/issues/293) **Type inference for bare `None`/`Err` in generic calls** — `option_map(None, fn(...) { ... })` fails because the type checker can't infer `T` from `None` alone. The workaround (typed let binding) is documented but clunky. Investigate bidirectional inference from the callback's parameter type.
- [#404](https://github.com/aallan/vera/issues/404) **Add "Known Limitations" section to SKILL.md** — consolidate the limitations an agent will encounter: `vera test` String/Float64 skip, bare `None`/`Err` inference gap, effect row variable unification (#294). Saves agents from discovering these the hard way.

### Phase 1b: Build the benchmark suite

- [#225](https://github.com/aallan/vera/issues/225) **Benchmark suite** — design a HumanEval/MBPP-style benchmark adapted for Vera. This is the single highest-value work item for the project's scientific credibility.

  The benchmark should cover five difficulty tiers:
  1. **Pure arithmetic** — functions with 1–2 parameters, simple contracts (the easy case for `@T.n`)
  2. **String and array manipulation** — functions using built-ins, testing whether agents find the right `domain_verb` names
  3. **ADTs and pattern matching** — custom data types, exhaustive match, testing De Bruijn indices in match arms
  4. **Recursive functions with termination proofs** — `decreases` clauses, testing whether agents produce provably terminating code
  5. **Multi-function programs with effects** — IO, State, Http, Inference, testing cross-function contract coherence

  For each problem, measure: first-attempt correctness (does `vera check` pass?), verification rate (does `vera verify` pass at Tier 1?), and fix-from-error rate (given the error message, does the agent fix it in one turn?). Run the same problems in Python and TypeScript as baselines.

  DafnyBench demonstrated that tracking verification success rates over time (68% → 96% in one year) attracts genuine research attention. Publish the benchmark, track it across model releases, and the research community will find you.

### Phase 1c: Expand contract-driven testing

- [#169](https://github.com/aallan/vera/issues/169) → [#170](https://github.com/aallan/vera/issues/170) **`vera test` input generation for String, Float64, compound types** — currently `vera test` skips any function with non-Int/Nat/Bool parameters. String generation: empty, single char, ASCII printable, unicode edge cases. Float64: 0.0, -0.0, small, large, subnormals. This unblocks contract-driven testing for most real programs.
- [#383](https://github.com/aallan/vera/issues/383) **Improve `vera test` skip messages** — show the specific unsupported type, not a generic message. "SKIPPED (cannot generate String inputs — see #169)" helps agents understand what they can and can't test.
- [#170](https://github.com/aallan/vera/issues/170) **Hypothesis integration** — use Hypothesis strategies for input generation, enabling property-based contract testing with shrinking. This is the long-term path to replacing hand-written test generation with a mature fuzzing framework.

---

## Milestone 2: Verified agent orchestration

*Goal: a working MCP tool server written in Vera, with contracts guaranteeing tool schemas at compile time. This is the flagship demo — the thing that makes people understand why Vera exists.*

This milestone follows the critical dependency chain that has driven the project since the roadmap was first written. Map, JSON, HTTP, and Inference are complete. What remains is the server side.

### Phase 2a: Inference effect hardening

The `<Inference>` effect is the headline feature. Harden it before building on top of it.

- [#378](https://github.com/aallan/vera/issues/378) **Add timeout to `Inference.complete`** — the current implementation uses `urllib.request` with no timeout. A hung provider hangs the runtime indefinitely. Add a configurable timeout (default 30s, overridable via `VERA_INFERENCE_TIMEOUT`), returning `Err("inference timeout")` on expiry.
- [#370](https://github.com/aallan/vera/issues/370) **Configurable `max_tokens` / `temperature`** — currently hardcoded; agent workloads need control over both.
- [#372](https://github.com/aallan/vera/issues/372) **User-defined `handle[Inference]` handlers** — currently the Inference effect cannot be handled in user code; full handler support enables mocking, caching, and routing strategies.
- [#371](https://github.com/aallan/vera/issues/371) **`Inference.embed` operation** — `Array<Float64>` vector embeddings for semantic search and retrieval. Depends on #373 (float array host-alloc infrastructure).
- [#373](https://github.com/aallan/vera/issues/373) **Float array host-alloc infrastructure** — `_alloc_result_ok_float_array` support for returning float arrays from host imports. Required by #371.
- [#413](https://github.com/aallan/vera/issues/413) **Add Mistral AI provider to the Inference effect** — extend the `<Inference>` effect runtime with Mistral API support alongside the existing Anthropic, OpenAI, and Moonshot providers.
- [#379](https://github.com/aallan/vera/issues/379) **Add an Inference + JSON composition example** — demonstrate `Inference.complete` → `json_parse` → typed extraction. This is the pattern every real agent workload will use and it should be a first-class example.
- [#380](https://github.com/aallan/vera/issues/380) **Add an effect handler mocking example** — show `handle[Inference] { complete(@String) -> { resume(Ok("mock")) } } in { ... }` for deterministic testing. This demonstrates the key architectural advantage of modelling inference as an algebraic effect.

### Phase 2b: Server-side effects

**Http effect hardening** — the Http effect shipped in v0.0.99 with basic GET/POST. These issues extend it to production capability:

- [#351](https://github.com/aallan/vera/issues/351) Custom headers support
- [#352](https://github.com/aallan/vera/issues/352) HTTP status code access in responses
- [#353](https://github.com/aallan/vera/issues/353) Per-request timeout control
- [#354](https://github.com/aallan/vera/issues/354) Correct `Content-Type` header on POST
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
- [#226](https://github.com/aallan/vera/issues/226) **Typed holes** — partial program generation where the agent leaves `?` placeholders and the compiler reports the expected type at each hole site. Improves LLM completion quality by providing type context mid-generation.
- [#329](https://github.com/aallan/vera/issues/329) **Plumbing integration** — Vera WASM modules as verified tool calls in [Plumbing](https://arxiv.org/abs/2602.13275) agent graphs. Typed port interface maps Plumbing stream types to Vera ADTs at the JSON serialisation boundary.
- [#183](https://github.com/aallan/vera/issues/183) **Human-readable slot annotations** — optional `-- name` annotations on slot references that are preserved by the formatter but ignored by the compiler. Bridges the readability gap for human reviewers of agent-generated code without compromising the De Bruijn system.
- [#181](https://github.com/aallan/vera/issues/181) **Signature refactoring** — mechanical slot index rewriting when function signatures change. Essential for any refactoring workflow, whether human or agent-driven.

### Phase 3b: Discoverability improvements

- [#397](https://github.com/aallan/vera/issues/397) **Add `<link>` tags to docs/index.html** — `<link rel="alternate" type="text/markdown" href="/llms.txt">` and equivalents for llms-full.txt and index.md. Standard HTML link discovery for agents parsing the DOM.
- [#398](https://github.com/aallan/vera/issues/398) **Serve SKILL.md from veralang.dev** — copy to `docs/SKILL.md` via `build_site.py` so the primary agent reference is on the same domain as the website. Add to sitemap.xml.
- **Register with llms.txt directories** — submit to [llms-txt-hub](https://github.com/thedaviddias/llms-txt-hub) and [llmstxthub.com](https://llmstxthub.com). Manual task, no code change required.
- [#399](https://github.com/aallan/vera/issues/399) **Add JSON-LD structured data** — `SoftwareApplication` schema with documentation links to llms.txt and SKILL.md.
- [#400](https://github.com/aallan/vera/issues/400) **Move "For Agents" section above the fold** — currently below the installation instructions; should be more prominent for a language whose primary audience is AI agents.
- [#401](https://github.com/aallan/vera/issues/401) **MCP documentation endpoint** — a static MCP server (via mcpdoc or similar) that serves Vera documentation to MCP-aware tools. Low lift, high discoverability for the growing MCP ecosystem.

### Phase 3c: Developer experience

- [#224](https://github.com/aallan/vera/issues/224) **REPL** — interactive exploration for both agents and humans. Useful for rapid prototyping and debugging.
- [#381](https://github.com/aallan/vera/issues/381) **`vera version` command** — print the installed version. Basic hygiene for bug reports and CI scripts.
- [#382](https://github.com/aallan/vera/issues/382) **`--quiet` flag for `vera check`/`vera verify`** — suppress "OK" output for CI scripts that only care about the exit code.
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
| Add `pip-audit` to CI for CVE scanning | [#384](https://github.com/aallan/vera/issues/384) | 15 min | Catches dependency vulnerabilities |
| Add `zizmor` for GitHub Actions security audit | [#385](https://github.com/aallan/vera/issues/385) | 15 min | Audits CI workflow files for injection risks |
| Add `ruff check --select S` to lint job | [#388](https://github.com/aallan/vera/issues/388) | 15 min | Bandit-equivalent security rules on compiler code |
| Add property-based testing with Hypothesis | [#386](https://github.com/aallan/vera/issues/386) | 2–4 hours | Catches parser/formatter edge cases via round-trip properties |
| Add mutation testing with mutmut (detection only) | [#387](https://github.com/aallan/vera/issues/387) | 2–4 hours | Measures whether 3,095 tests catch real bugs, not just execute paths |
| Investigate parser fuzzing with Atheris | [#402](https://github.com/aallan/vera/issues/402) | 4–8 hours | Crash-inducing inputs for parser and type checker |
| Generate CycloneDX SBOM on release | [#389](https://github.com/aallan/vera/issues/389) | 30 min | Supply chain transparency for downstream consumers |
| Add hash-pinned lockfile (pip-compile or uv lock) | [#390](https://github.com/aallan/vera/issues/390) | 30 min | Prevents dependency confusion attacks |
| Improve browser runtime test coverage to >80% | [#349](https://github.com/aallan/vera/issues/349) | 2–4 hours | Parity with Python-side coverage gate |
| Validate examples/README.md run commands in CI | [#361](https://github.com/aallan/vera/issues/361) | 1–2 hours | Prevents stale example invocations |

### Security

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Add Z3 solver timeout per contract | [#391](https://github.com/aallan/vera/issues/391) | 30 min | Prevents DoS via pathological contracts |
| Audit `smt.py` for soundness | [#392](https://github.com/aallan/vera/issues/392) | 4–8 hours | A bug here silently bypasses verification |
| Add `Inference.complete` timeout | [#378](https://github.com/aallan/vera/issues/378) | 30 min | Prevents runtime hang on unresponsive LLM provider |

### Testing gaps

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Deep let-chain conformance tests (5+ same-typed bindings) | [#393](https://github.com/aallan/vera/issues/393) | 1 hour | Exercises the hardest De Bruijn case |
| Non-commutative operation tests (subtraction, division with swapped indices) | [#394](https://github.com/aallan/vera/issues/394) | 1 hour | Catches silent index errors that commutative ops mask |
| Effect handler composition tests (nested handlers) | [#395](https://github.com/aallan/vera/issues/395) | 2 hours | Where algebraic effect systems typically have subtle bugs |
| Cross-module contract verification stress test | [#396](https://github.com/aallan/vera/issues/396) | 2 hours | Verifies postcondition chains work across module boundaries |

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

**630+ commits, 103 tagged releases, 3,121 tests, 96% coverage, 65 conformance programs, 30 examples, 13 spec chapters.** See [HISTORY.md](HISTORY.md) for the full narrative of how the compiler was built.
