# Roadmap

Where the project is going.  See [HISTORY.md](HISTORY.md) for what's been built and [CHANGELOG.md](CHANGELOG.md) for per-release detail.

## Where we are

3,784 tests, 86 conformance programs, 34 examples, 13 spec chapters.

## What's next

**Stabilisation tier** — close these out before resuming agent-integration:

| Order | Issue | Why now |
|:---:|---|---|
| 1 | [#604](https://github.com/aallan/vera/issues/604) — Five prelude combinators silently skipped from WASM compile | `option_map` / `option_and_then` / `option_unwrap_or` / `result_map` / `result_unwrap_or` all emit `[E602]` warnings during every WASM compile and are then absent from the output module.  Two distinct backend gaps (param-type and body-expression).  Easy to dismiss as "noise" but means agents writing monadic Option/Result code on the browser target hit silent feature loss.  Cleanest concrete instance of the "silent-skip" pattern tracked by [#626](https://github.com/aallan/vera/issues/626). |
| 2 | [#626](https://github.com/aallan/vera/issues/626) — Convert "translate returns None → silent skip" failures into loud diagnostics | Cross-cutting failure-shape pattern observed in #583, #604, #614, and #615 (closure case).  A WASM translator returns None on an unsupported case; the caller silently degrades by either dropping the function with an [E602] warning (top-level) or producing a `call_indirect` to a non-existent table entry (closure → WASM validation trap).  Layer 1 (pre-commit gate on [E602]) is independently shippable; layer 2 (closure-lift fail-fast) and layer 3 (audit `return None` → structured `CodegenSkip`) are the bigger commits.  Closes the *category* of "silent translator failures" that has produced multiple bugs. |
| 3 | [#630](https://github.com/aallan/vera/issues/630) — Centralise canonical Vera-type-name resolution (close the #602 bug class structurally) | Eight distinct triggers of the same `i32_pair`-into-`i64` mismatch shape across #602, #614, #627, and #629 — each one fixed locally, each fix added one more isinstance-handler.  Five overlapping canonicalisation helpers have accumulated in `vera/wasm/inference.py` (`_format_named_type`, `_format_named_type_canonical`, `_resolve_i32_pair_ret_te`, `_resolve_base_type_name`, plus ad-hoc `while`-loops at apply_fn / FnType-helper sites), none of which does the full job.  Tier 1: fold them into a single `_canonical_vera_type` covering RefinementType unwrap + alias-chain follow + generic substitution + format-with-args, applied at every type-walking inference site.  Tier 2: convert the silent fallthrough at `operators.py:482` to a hard compile-time error (dovetails with #626 Layer 1).  Together they make the 9th trigger either impossible (T1) or instantly diagnosable (T2) — pure refactor + diagnostic conversion, no behavioural change for valid programs. |
| 4 | [#596](https://github.com/aallan/vera/issues/596) — Stress-test harness | `tests/test_stress.py` exercising programs at scale (10K-element `array_map`, 1K-deep recursion with allocating arg, 20×20×100 Conway's Life, long-running State handlers, etc.) — under a `@pytest.mark.stress` flag so it runs nightly rather than per-PR.  Should run a subset under `VERA_EAGER_GC=1` to catch GC-rooting regressions on the very first iteration rather than only at scale.  Surfaces the next scale-only GC bug before users do. |
| 5 | [#597](https://github.com/aallan/vera/issues/597) — Walker-completeness audit | Audit every `isinstance(expr, ast.X)` dispatch chain in the codebase against the full set of `Expr` subclasses.  Document each walker's coverage as a checklist comment; optional companion script (`scripts/check_walker_coverage.py`) for pre-commit enforcement.  Converts "we hope our walkers are complete" to "we've audited every walker".  Pairs with #626 — #597 is the *static* dispatch-chain coverage audit, #626 is the *runtime* failure-handling audit; both close adjacent halves of the "translation silently no-ops" failure shape. |
| 6 | [#609](https://github.com/aallan/vera/issues/609) — Browser runtime: `IO.sleep` via JSPI | The timing half of the terminal-vs-browser seam.  `IO.sleep` currently busy-waits the main thread, so any animation or paced simulation freezes the tab for its full duration.  Implement against the [WebAssembly JSPI proposal](https://github.com/WebAssembly/js-promise-integration) — `WebAssembly.promising` wraps `setTimeout(resolve, ms)`, the WASM call suspends and resumes after the timer fires.  Asyncify is the fallback for browsers without JSPI.  No language change required.  Closing this lets terminal Vera programs animate in the browser without forking the source. |
| 7 | [#610](https://github.com/aallan/vera/issues/610) — Browser runtime: ANSI subset interpreter | The rendering half of the same seam.  ANSI escape sequences (cursor positioning, screen clear, line erase) currently render as literal control characters in the DOM.  Implement a small subset interpreter (~200 lines of JS) in `runtime.mjs` that maintains a virtual screen buffer and applies the canonical cursor-addressable subset (`ESC[H`, `ESC[2J`, `ESC[K`, basic colors) into a target `<pre>` element.  Pairs with #609 — together they let `life.vera` (the terminal version) run unchanged on `vera compile --target browser`.  Bounded scope, well-defined acceptance criteria. |
| 8 | [#618](https://github.com/aallan/vera/issues/618) — `IO.read_char` portable across terminal and browser | The input half of the same write-once-run-anywhere seam.  Single-character input is currently impossible at any target — `IO.read_line` is line-buffered, so real-time CLI games (Tetris-class) can't be written in Vera at all.  Add `IO.read_char` to the existing `IO` effect with two host implementations: `termios` / `msvcrt` for terminal (raw mode entered implicitly per call), keypress event listener via JSPI for browser.  Pairs with #609 (timing) and #610 (rendering) — together those three close the input/timing/rendering trio that real-time programs need.  Symmetric to #609's argument: just as Game of Life shouldn't be terminal-only because sleep doesn't work in the browser, Tetris shouldn't be browser-only because read_char doesn't work in the terminal. |

**Agent-integration tier** — resumes once stabilisation is done:

| Order | Issue | Why now |
|:---:|---|---|
| 9 | [#222](https://github.com/aallan/vera/issues/222) — LSP server | Standard integration protocol for production coding agents (Claude Code, Cursor, Copilot, Windsurf).  The `--json` infrastructure provides most of what's needed.  Real-time feedback as agents write — diagnostics, hover, completion — turns Vera from "compile-and-pray" into the tight loop agents are calibrated for.  Single highest-leverage adoption enabler. |
| 10 | [#523](https://github.com/aallan/vera/issues/523) — `vera context` token-budgeted project export | New CLI command that walks a project's dependency graph and emits a compact LLM-consumable summary of public signatures, contracts, effects, and ADTs.  Mandatory contracts carry the semantic payload that named-variable languages convey via identifiers and docstrings, so the output is denser per byte than equivalent Python/TS exports.  Estimated 1–2 days; module system and function registry already exist internally. |
| 11 | [#370](https://github.com/aallan/vera/issues/370) — Configurable `Inference.complete` `max_tokens` / `temperature` | Currently hardcoded.  Agent workloads need control over both — for cost gates, deterministic replays, and routing strategies.  Smallest of the Inference-hardening items but also the one that blocks the most concrete user requests. |

Completed items get deleted from these tables and noted in [HISTORY.md](HISTORY.md).  When a tier shrinks the section gets repopulated from the milestones below.

---

## Milestone 1: Prove the thesis

*Goal: answer the fundamental question — do LLMs write better code in Vera than in existing languages? Build the evidence base and fix the friction points that block honest evaluation.*

### Phase 1b: Benchmark suite

[VeraBench](https://github.com/aallan/vera-bench) — 50 problems across 5 difficulty tiers with canonical solutions in Vera, Python, and TypeScript.  See the vera-bench repository for current results.

- [#225](https://github.com/aallan/vera/issues/225) **Expand benchmark coverage** — pass@k evaluation with multiple trials (single-run results have high variance), additional models, additional difficulty tiers as the suite grows.

### Phase 1c: Expand contract-driven testing

- [#440](https://github.com/aallan/vera/issues/440) **`vera test` input generation for ADT types** — functions with ADT (algebraic data type) parameters are still skipped. ADT generation requires constructor synthesis: selecting from known constructors and recursively generating field values.
- [#562](https://github.com/aallan/vera/issues/562) **Advanced testing features** — input shrinking (find the smallest failing input from large counterexamples), cross-function scenarios (test sequences like `put` then `get` for stateful contracts), and coverage-guided generation (use WASM execution paths to steer the generator). The active backlog for `vera test` beyond ADT input generation.
- [#170](https://github.com/aallan/vera/issues/170) **Hypothesis as input-generation backend** (bookmark) — evaluate adopting Hypothesis to handle types Z3 can't encode (String, Array, ADT, nested structures). Deferred until `vera test`'s Z3 backend hits its ceiling on a real Vera program; trigger condition is sustained "cannot generate inputs" warnings on String/Array contracts. Tool choice (#170) is the deferred decision; the feature work it would unblock is #562.

---

## Milestone 2: Verified agent orchestration

*Goal: a working MCP tool server written in Vera, with contracts guaranteeing tool schemas at compile time. This is the flagship demo — the thing that makes people understand why Vera exists.*

### Phase 2a: Inference effect hardening

Harden `<Inference>` — the headline feature — before building on top of it.

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

**Http effect hardening** — extend the existing GET/POST surface to production capability:

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
- [#523](https://github.com/aallan/vera/issues/523) **`vera context` — token-budgeted project context export** — new CLI command that walks a project's dependency graph and emits a compact summary of public signatures, contracts, effects, ADTs, and imports for LLM consumption. `--depth auto --budget 10kb` by default; the budget is a first-class navigation primitive so agents can zoom from architecture map to specific modules. Directly inspired by [Aver](https://averlang.dev)'s [`aver context` command](https://github.com/jasisz/aver#context-export); richer per byte in Vera because mandatory contracts carry the semantic payload that named-variable languages have to convey via identifiers and docstrings. Complements SKILL.md (teaches the language) and CLAUDE.md/AGENTS.md (teach the development workflow) — `vera context` teaches a specific project. Estimated 1–2 days; the module system and function registry already exist internally.
- [#181](https://github.com/aallan/vera/issues/181) **Signature refactoring** — mechanical slot index rewriting when function signatures change. Essential for any refactoring workflow, whether human or agent-driven.
- [#539](https://github.com/aallan/vera/issues/539) **`vera builtins/effects/errors --json` — compiler introspection subcommands** — three thin CLI wrappers around the compiler's built-in / effect / error-code registries. Makes Vera the source of truth for "164 built-in functions" instead of doc files being canon and drifting silently when built-ins are added. Independent half-day units; ship one at a time. `vera errors --json` highest value (unblocks generated error-reference table in spec); `vera builtins --json` next; `vera effects --json` cheapest.

### Phase 3b: Discoverability improvements

- [#424](https://github.com/aallan/vera/issues/424) **Register veralang.dev with llms.txt directories** — submit to [llms-txt-hub](https://github.com/thedaviddias/llms-txt-hub) and [llmstxthub.com](https://llmstxthub.com). Manual task, no code change required.
- [#401](https://github.com/aallan/vera/issues/401) **MCP documentation endpoint** — a static MCP server (via mcpdoc or similar) that serves Vera documentation to MCP-aware tools. Low lift, high discoverability for the growing MCP ecosystem. Test harness recommendation captured in [#529](https://github.com/aallan/vera/issues/529) ([mcp-assert](https://github.com/blackwell-systems/mcp-assert) — deterministic-tool assertions in YAML, language-agnostic on the server side).
- [#525](https://github.com/aallan/vera/issues/525) **Close remaining [Agent Score](https://buildwithfern.com/agent-score) gaps on veralang.dev** — current state is 2 failures + 1 warning. The two failures: `content-negotiation` (GitHub Pages can't honour `Accept: text/markdown` natively — needs a Cloudflare Worker edge rule or a move to a host that supports `_redirects`); `markdown-content-parity` (residual 21% gap is interface chrome — CTA labels, readpath device, eyebrows — that doesn't translate naturally to markdown). The warning: `content-start-position` (inline `<style>` consumes agent truncation budget; partial fix is moving JSON-LD `<script>` to end of `<body>`).
- [#528](https://github.com/aallan/vera/issues/528) **Auto-generate or gate homepage numbers** — `docs/index.html` embeds hardcoded project facts (built-in count, effects list, conformance count, examples count, version) that drift silently. PR #526 review surfaced two already-stale values ("six algebraic effects" missing Random; "77-program conformance suite" when actual was 80). Extend `scripts/check_doc_counts.py` to scan `docs/index.html` against live counts, following the pattern already in use for `TESTING.md`/`CLAUDE.md`/etc. Preserves the "HTML is hand-edited" convention while catching drift at commit time.

### Phase 3c: Developer experience

- [#224](https://github.com/aallan/vera/issues/224) **REPL** — interactive exploration for both agents and humans. Useful for rapid prototyping and debugging.
- [#143](https://github.com/aallan/vera/issues/143) **Comprehensive example programs** — expand to 50+ examples covering every major pattern: API clients, data pipelines, text processing, LLM orchestration, effect composition.

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

- [#367](https://github.com/aallan/vera/issues/367) **Markdown content extractors** — `md_blocks`, `md_inline_text`, `md_extract_headings`, `md_extract_links`, `md_filter_blocks`.
- [#368](https://github.com/aallan/vera/issues/368) **HTML convenience accessors** — `html_query_one`, `html_tag`, `html_children`.
- [#507](https://github.com/aallan/vera/issues/507) **Array utility built-ins (phase 2)** — `array_sort` (with `Ord<T>` ability dispatch), `array_contains`, `array_index_of` (both with `Eq<T>` dispatch). Phase 2 of [#466](https://github.com/aallan/vera/issues/466); needs the dispatch infrastructure to invoke `compare$T` / `eq$T` from inside an iterative WASM loop. See issue body for the architectural sketch.
- [#509](https://github.com/aallan/vera/issues/509) **String + character built-ins (phase 2, Unicode)** — `string_codepoints`, `string_graphemes`, whole-string `string_to_upper` / `string_to_lower`, Unicode-aware classifiers, codepoint-level reverse. Phase 2 of [#470](https://github.com/aallan/vera/issues/470) + [#471](https://github.com/aallan/vera/issues/471); requires host imports (Python `unicodedata`, browser `Intl.Segmenter`) and is not blocking any current program.
- [#187](https://github.com/aallan/vera/issues/187) → [#127](https://github.com/aallan/vera/issues/127) **Module-qualified call disambiguation → module re-exports** — sequential dependency; completes the module system.

---

## Continuous: quality and security hardening

Addressed alongside feature work, not milestone-gated.  Prioritised by impact.

### CI tooling

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Add property-based testing with Hypothesis | [#386](https://github.com/aallan/vera/issues/386) | 2–4 hours | Catches parser/formatter edge cases via round-trip properties |
| Add mutation testing with mutmut (detection only) | [#387](https://github.com/aallan/vera/issues/387) | 2–4 hours | Measures whether the test suite catches real bugs, not just execute paths |
| Investigate parser fuzzing with Atheris | [#402](https://github.com/aallan/vera/issues/402) | 4–8 hours | Crash-inducing inputs for parser and type checker |
| Improve browser runtime test coverage to >80% | [#349](https://github.com/aallan/vera/issues/349) | 2–4 hours | Parity with Python-side coverage gate |
| Auto-tag + auto-release on version bump in `pyproject.toml` | [#481](https://github.com/aallan/vera/issues/481) | 1–2 hours | A GitHub Actions workflow detects the version change, tags `main`, and creates the release using the matching CHANGELOG section as notes |
| Replace line-numbered allowlists with inline HTML-comment fence annotations | [#538](https://github.com/aallan/vera/issues/538) | 4–6 hours | Removes `fix_allowlists.py` entirely — the recurring source of silent-duplicate-key bugs and the line-shift tax on every doc PR. One-shot migration script + check-script rewrite |
| Add `lychee` + `markdownlint-cli2` MD051 for cross-doc anchor validation | [#540](https://github.com/aallan/vera/issues/540) | 30–60 min | Catches broken `file.md#anchor` references across the 30+ markdown files; today these break silently when headings are renamed |


### Verification depth

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Tier 2 verification — Z3 with hints from `assert` and lemma functions | [#427](https://github.com/aallan/vera/issues/427) | 2–4 days | Promotes function-call and quantifier contracts from runtime to statically proved; completes the three-tier pipeline specified in §6.3.2 |
| Lift effect handler bodies out of Tier 3 | [#439](https://github.com/aallan/vera/issues/439) | 1–2 days | Handler bodies currently always fall to runtime even when their contracts are statically decidable; removes a false negative in Tier 1 coverage |
| Generalize `@Nat` invariant check to all binding sites (let / arg / match-bind) | [#552](https://github.com/aallan/vera/issues/552) | 1–2 days | The `@Nat >= 0` invariant is currently checked only at function return positions.  Narrowing from `@Int` into a `@Nat`-typed let binding or argument silently propagates negative values through subsequent expressions.  Generalises the obligation-discharge infrastructure to every binding site. |

### Security

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|
| Audit `smt.py` for soundness | [#392](https://github.com/aallan/vera/issues/392) | 4–8 hours | A bug here silently bypasses verification |

### Testing gaps

| Item | Issue | Effort | Impact |
|------|-------|--------|--------|

---

## Speculative

Deferred decisions — features without a current driver, captured here so the design analysis isn't re-derived if one shows up.  Promotes into a milestone phase or the stabilisation queue when a real trigger appears.

| Item | Issue | Trigger condition |
|------|-------|-------------------|
| Allow `@Byte` arithmetic with verified underflow + overflow guards | [#564](https://github.com/aallan/vera/issues/564) | A real Vera program (or proposed feature) requires byte arithmetic at the user-code level — e.g., a binary-format parser the stdlib doesn't cover; or VeraBench shows a measurable adoption tax from `byte_to_int` round-trips on byte-heavy benchmarks.  Today: the type checker excludes `Byte` from `NUMERIC_TYPES`, so `@Byte - @Byte` etc. produce E140; the round-trip via `byte_to_int` / `int_to_byte` is the canonical idiom. |
