# Roadmap

Vera v0.0.108 delivers a complete compiler pipeline — parse, transform, type-check, verify contracts via Z3, compile to WebAssembly, execute at the command line or in the browser — with 122 built-in functions, algebraic effects (IO, Http, State, Exceptions, Async, Inference), constrained generics, a module system, contract-driven testing, and a canonical formatter. The core language is done. What follows is the path from "working language" to "the language agents actually use."

This roadmap is organised around four strategic milestones. Each milestone makes Vera meaningfully more useful to a concrete audience. Within each milestone, work is grouped into phases that can be executed roughly sequentially, though independent items can be interleaved.

See [HISTORY.md](HISTORY.md) for a narrative account of how the compiler was built.

## Where we are

The compiler is complete end-to-end: parse, type-check, verify contracts via Z3, compile to WebAssembly, and run — at the command line and in the browser. The language has 122 built-in functions, algebraic effects (IO, Http, State, Exceptions, Async, Inference, Random), constrained generics, a module system, contract-driven testing, and a canonical formatter. Type inference for bare constructors (`None`, `Err`, `Ok`) now works correctly across all call sites. The compiler has 3,368 tests, 76 conformance programs, 30 examples, and a 13-chapter specification.

Significant progress has been made towards Vera being a viable agent target. [VeraBench](https://github.com/aallan/vera-bench) — a 50-problem benchmark across 5 difficulty tiers — now covers 6 models across 3 providers (v0.0.7). The headline result: Kimi K2.5 achieves 100% run_correct on Vera, beating both Python (86%) and TypeScript (91%). Three models beat TypeScript on Vera. The flagship tier averages 93% Vera run_correct vs 93% Python — essentially parity. These are single-run results with high variance; stable rates will require pass@k evaluation. The remaining gaps are empirical breadth (repeated trials, more models), standard library depth (HTTP hardening, server effects), and tooling integration (LSP).

---

## What's next — short-term priorities

This section captures the concrete **implementation order** for the next few weeks of work. The phase numbering in the milestones below (Phase 4a/4b/4c etc.) reflects **strategic grouping** — what kind of feature it is and which broader goal it serves — and is stable across releases. Implementation order shifts as empirical evidence arrives, so it lives here rather than as a reordering of the milestones.

### The ordering principle

The near-term queue mixes issues from two categories:

- **Capability-expansion** — unlocks *new kinds of programs that aren't possible today*. No hand-rolled workaround exists; the language literally can't do the thing. Examples: [#467](https://github.com/aallan/vera/issues/467) (log/sin/cos/constants).
- **Error-reduction / ergonomic** — the program is already possible but verbose, bug-prone, or fragile. Hand-rolled recursive accumulators, manual ASCII range checks, nested Option/Json unwraps. Examples: [#466](https://github.com/aallan/vera/issues/466) (array utilities), [#470](https://github.com/aallan/vera/issues/470) / [#471](https://github.com/aallan/vera/issues/471) (string + char), [#366](https://github.com/aallan/vera/issues/366) (JSON accessors).

Both matter, but they're asymmetric in timing: capability gaps are *blocking* (entire program categories don't exist), ergonomic gaps are *annoying* (programs compound verbosity). Blocking issues front-load more value per hour because they unlock whole genres of program. The current state of the language is "most programs possible, some categories blocked" — so capability-expansion goes first, ergonomic polish follows.

Empirical confirmation from a model writing Conway's Game of Life in Vera while this queue was being planned:

> "The bug fix plus `IO.sleep` and Random are transformative. With `IO.sleep` I can write a proper animation loop… With Random I can generate a random soup initial state instead of hardcoding a glider and blinker, which is dramatically more interesting to watch. The program goes from 'dump 20 static frames' to 'animated random cellular automaton that runs in your terminal.' From [#466](https://github.com/aallan/vera/issues/466), `array_any` is useful for detecting extinction, and `array_contains` could simplify some checks, but neither is essential. From [#470](https://github.com/aallan/vera/issues/470), `string_pad_start` would let me right-align the generation counter — minor polish."

This reshaped the ordering: capability issues move up, ergonomic issues move down. Completed items are noted in [HISTORY.md](HISTORY.md).

### Implementation order

| Order | Issue | Why now |
|:---:|---|---|
| 1 | [#467](https://github.com/aallan/vera/issues/467) — Math built-ins (log, sin, cos, …) | **Capability unlock, bulk addition.** ~14 pure host imports following the same pattern. Unlocks graphics, physics, statistics. |
| 2 | [#466](https://github.com/aallan/vera/issues/466) — Array utilities (sort, mapi, reverse, …) | **Highest benchmark-score win.** Eliminates the recursive-accumulator-with-indexed-state pattern — the dominant LLM failure mode per VeraBench. New combinators follow the iterative WASM pattern shared by `array_map` / `array_filter` / `array_fold`. |
| 3 | [#470](https://github.com/aallan/vera/issues/470) — String utilities | `string_chars` is a bridge primitive (unlocks array-combinator approach to string processing). Rest is polish. |
| 4 | [#471](https://github.com/aallan/vera/issues/471) — Character classification | Tiny, can ship alongside any of the above. Eliminates brittle ASCII range checks. |
| 5 | [#366](https://github.com/aallan/vera/issues/366) — JSON typed accessors | Replaces nested Option/Json unwrap ceremony. Polish tier for the Inference/Http pipeline. |

### What moves when

Completed items get deleted from this table and noted in [HISTORY.md](HISTORY.md) as usual. When the table shrinks to ~3 items the section should be re-evaluated and repopulated from the next batch of priorities — it's intended to be a rolling view of the next few weeks, not a permanent roadmap layer.

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

  Six models across three providers evaluated on all four modes (v0.0.7).

  ### Summary (run_correct — Vera vs Python vs TypeScript)

  **Flagship tier:**

  | Model | Vera | Python | TypeScript |
  |-------|------|--------|------------|
  | **Kimi K2.5** | **100%** | 86% | 91% |
  | GPT-4.1 | 91% | 96% | 96% |
  | Claude Opus 4 | 88% | 96% | 96% |

  **Sonnet tier:**

  | Model | Vera | Python | TypeScript |
  |-------|------|--------|------------|
  | **Kimi K2 Turbo** | **83%** | 88% | 79% |
  | Claude Sonnet 4 | 79% | 96% | 88% |
  | GPT-4o | 78% | 93% | 83% |

  ### Key findings

  **Kimi K2.5 writes perfect Vera code.** 100% run_correct on both full-spec and spec-from-NL modes, beating Python (86%) and TypeScript (91%). This is the first model where Vera is the best language across the board.

  **Three models beat TypeScript on Vera.** Kimi K2.5 (+9pp), Kimi K2 Turbo (+4pp), and in the initial v0.0.4 benchmark Claude Sonnet 4 also beat TypeScript (83% vs 79%). The pattern is consistent across providers.

  **Python remains the strongest target for most models.** The gap between Python and Vera varies from 0pp (Kimi K2.5) to 17pp (Claude Sonnet 4). The flagship tier averages 93% Vera vs 93% Python — essentially parity.

  **These are early, single-run results.** The v0.0.4 Claude Sonnet 4 result (83% Vera, 79% TypeScript) shifted to 79%/88% in the v0.0.7 re-run, illustrating the variance inherent in single-run evaluation. Stable rates will require pass@k evaluation with multiple trials.


### Phase 1c: Expand contract-driven testing

- [#440](https://github.com/aallan/vera/issues/440) **`vera test` input generation for ADT types** — functions with ADT (algebraic data type) parameters are still skipped. ADT generation requires constructor synthesis: selecting from known constructors and recursively generating field values.
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
- [#425](https://github.com/aallan/vera/issues/425) **Add xAI Grok provider to the Inference effect** — one-row addition to `_PROVIDERS`. Endpoint: `https://api.x.ai/v1/chat/completions`; env var: `VERA_XAI_API_KEY`.
- [#450](https://github.com/aallan/vera/issues/450) **Add DeepSeek V3/R1 provider to the Inference effect** — one-row addition to `_PROVIDERS`; OpenAI-compatible endpoint (`https://api.deepseek.com/v1/chat/completions`); env var `VERA_DEEPSEEK_API_KEY`; default model `deepseek-chat` (V3), selectable to `deepseek-reasoner` (R1) via `VERA_INFERENCE_MODEL`.
- [#451](https://github.com/aallan/vera/issues/451) **Add Google Gemini 2.5 Pro provider to the Inference effect** — Gemini uses a distinct API shape requiring a custom request/response path; endpoint `https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent`; env var `VERA_GEMINI_API_KEY`; default model `gemini-2.5-pro`.
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
- [#181](https://github.com/aallan/vera/issues/181) **Signature refactoring** — mechanical slot index rewriting when function signatures change. Essential for any refactoring workflow, whether human or agent-driven.

### Phase 3b: Discoverability improvements

- [#424](https://github.com/aallan/vera/issues/424) **Register veralang.dev with llms.txt directories** — submit to [llms-txt-hub](https://github.com/thedaviddias/llms-txt-hub) and [llmstxthub.com](https://llmstxthub.com). Manual task, no code change required.
- [#401](https://github.com/aallan/vera/issues/401) **MCP documentation endpoint** — a static MCP server (via mcpdoc or similar) that serves Vera documentation to MCP-aware tools. Low lift, high discoverability for the growing MCP ecosystem.

### Phase 3c: Developer experience

- [#224](https://github.com/aallan/vera/issues/224) **REPL** — interactive exploration for both agents and humans. Useful for rapid prototyping and debugging.
- [#143](https://github.com/aallan/vera/issues/143) **Comprehensive example programs** — expand from 30 to 50+ examples covering every major pattern: API clients, data pipelines, text processing, LLM orchestration, effect composition.

---

## Milestone 4: Language maturity

*Goal: Vera handles the long tail of real-world requirements — concurrency, streaming, packages, incremental compilation. The language is not just viable but competitive.*

### Phase 4a: Concurrency and streaming

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
- [#466](https://github.com/aallan/vera/issues/466) **Array utility built-ins** — `array_sort`, `array_reverse`, `array_mapi`, `array_contains`, `array_find`, `array_any`, `array_all`, `array_index_of`, `array_sort_by`, `array_flatten`. Highest-impact gap — sorting requires a hand-written merge sort today, and the lack of `array_mapi` forces recursive-accumulator-with-index patterns (the dominant LLM failure mode, and the one that triggered #464). New combinators should follow the iterative WASM pattern shared by `array_map` / `array_filter` / `array_fold` rather than recursive prelude helpers.
- [#467](https://github.com/aallan/vera/issues/467) **Math built-ins** — `log`, `log2`, `log10`, `sin`, `cos`, `tan`, `atan2`, `pi`, `e`, `sign`, `clamp`. Standard numeric library functions.
- [#470](https://github.com/aallan/vera/issues/470) **String utility built-ins** — `string_reverse`, `string_pad_start`, `string_pad_end`, `string_chars`, `string_trim_start`, `string_trim_end`.
- [#471](https://github.com/aallan/vera/issues/471) **Character classification built-ins** — `is_digit`, `is_alpha`, `is_alphanumeric`, `is_whitespace`, `is_upper`, `is_lower`. Operate on first character of a string (Vera has no `Char` type).
- [#187](https://github.com/aallan/vera/issues/187) → [#127](https://github.com/aallan/vera/issues/127) **Module-qualified call disambiguation → module re-exports** — sequential dependency; completes the module system.

---

## Continuous: quality and security hardening

These are not milestone-gated — they should be addressed continuously alongside feature work. Prioritised by impact.

### CI tooling

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Add property-based testing with Hypothesis | [#386](https://github.com/aallan/vera/issues/386) | 2–4 hours | Catches parser/formatter edge cases via round-trip properties |
| Add mutation testing with mutmut (detection only) | [#387](https://github.com/aallan/vera/issues/387) | 2–4 hours | Measures whether 3,368 tests catch real bugs, not just execute paths |
| Investigate parser fuzzing with Atheris | [#402](https://github.com/aallan/vera/issues/402) | 4–8 hours | Crash-inducing inputs for parser and type checker |
| Improve browser runtime test coverage to >80% | [#349](https://github.com/aallan/vera/issues/349) | 2–4 hours | Parity with Python-side coverage gate |
| Add `check_changelog_updated.py` pre-push hook + CI check | [#478](https://github.com/aallan/vera/issues/478) | 30–60 min | Fails PRs that touch `vera/`/`spec/`/`SKILL.md` without a CHANGELOG entry; prevents the #474 miss from recurring |
| Auto-tag + auto-release on version bump in `pyproject.toml` | [#481](https://github.com/aallan/vera/issues/481) | 1–2 hours | Closes the tag/release gap that hit v0.0.113 — a GitHub Actions workflow detects the version change, tags `main`, and creates the release using the matching CHANGELOG section as notes |


### Verification depth

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Tier 2 verification — Z3 with hints from `assert` and lemma functions | [#427](https://github.com/aallan/vera/issues/427) | 2–4 days | Promotes function-call and quantifier contracts from runtime to statically proved; completes the three-tier pipeline specified in §6.3.2 |
| Lift effect handler bodies out of Tier 3 | [#439](https://github.com/aallan/vera/issues/439) | 1–2 days | Handler bodies currently always fall to runtime even when their contracts are statically decidable; removes a false negative in Tier 1 coverage |

### Security

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Audit `smt.py` for soundness | [#392](https://github.com/aallan/vera/issues/392) | 4–8 hours | A bug here silently bypasses verification |

### Compiler internals

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Tighten GC-rooting heuristic in iterative combinators | [#490](https://github.com/aallan/vera/issues/490) | 1–2 hours | Replaces `u_wasm == "i32" and not Bool/Byte` with a positive `is_gc_managed(type)` predicate. Currently over-roots host-managed handles (Map/Set/Decimal/Regex) — safe but wasteful; spotted during #489 review. Unblocks cleaner rooting decisions for any future combinator or host-handle addition. |

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

**810+ commits, 113 tagged releases, 3,368 tests, 96% coverage, 76 conformance programs, 30 examples, 13 spec chapters.** See [HISTORY.md](HISTORY.md) for the full narrative of how the compiler was built.
