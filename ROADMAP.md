# Roadmap

Where the project is going.  See [HISTORY.md](HISTORY.md) for what's been built and [CHANGELOG.md](CHANGELOG.md) for per-release detail.

The goal is unchanged: **a stable, working, usable language that doesn't silently fail under the agents using it** — and, on that foundation, the flagship demonstration that an agent can write verified tools in it.

## How this file works

The roadmap is a sequence of **stages** — concentrated sprints over a coherent class of issues — continuing the numbering from [HISTORY.md](HISTORY.md).  A stage is a campaign: pick a themed set, drive it to zero, release, move on.  When a stage's table empties, the stage moves to HISTORY.md with its releases and the next one starts.

Ordering derives from the design principles ([DESIGN.md](DESIGN.md)): verification truth first, then structural drift-proofing, then the capabilities the flagship needs, then the experience around them.  Priority lives in this file and nowhere else — issues carry kind and area labels, not priority labels.  Completed items are deleted from these tables and noted in HISTORY.md.  Stages beyond the next one or two are a forecast, not a commitment — they reorder freely as reality intervenes, and a new bug class outranks everything and becomes its own burndown.

## Where we are

12,972 tests, 248 conformance programs, 43 examples, 14 spec chapters.  [KNOWN_ISSUES.md](KNOWN_ISSUES.md) tracks the open bugs (burndown material rather than stage work), plus the *limitations* the stages below retire.

## The v0.1.14 burndown

*One open bugs, driven to zero.*

A bug class outranks stage work, so the next release takes the open `bug`-labelled set as its queue.  [KNOWN_ISSUES.md](KNOWN_ISSUES.md) carries each row's full account and stays the one place the detail lives; this table is the order of attack.  The rows where the compiler reports success and is wrong anyway — a proof that does not hold, an accounting that misstates what was checked — lead it; the rest are grouped by root-cause family.

| Issue | What |
|---|---|
| [#1317](https://github.com/aallan/vera/issues/1317) | `E609` and `E610` refuse two modules' same-named declarations by declaration rather than by use. |

## Stage 19 — The verification completeness sprint

*`vera verify` tells the whole truth.*

Verification-completeness gaps — an obligation not emitted, a guard not planted — individually small; the `@Nat`-narrowing rows ([#754](https://github.com/aallan/vera/issues/754), [#757](https://github.com/aallan/vera/issues/757), [#765](https://github.com/aallan/vera/issues/765)) reuse the per-component target-type metadata the [#820](https://github.com/aallan/vera/issues/820) enabler provides, while the reporting-completeness row carries its own root cause:

| Issue | What |
|---|---|
| [#909](https://github.com/aallan/vera/issues/909) | A value's postcondition / refinement is forgotten through an ADT field (box then unbox loses the fact), degrading provable programs to Tier 3. |
| [#754](https://github.com/aallan/vera/issues/754) | Effect-operation-argument runtime guard for `@Nat` narrowing, with a dedicated trap kind — first consumer of the per-component metadata enabler. |
| [#757](https://github.com/aallan/vera/issues/757) | Generic-instantiated constructor-field runtime guard — second consumer of the same enabler. |
| [#765](https://github.com/aallan/vera/issues/765) | Nested constructor sub-pattern binds (`Some(Some(@PosInt))`) runtime-guarded to match their static obligation. |

## Stage 20 — The single-source sprint

*One fact, one home, drift caught by a gate.*

This stage makes drift-prone consistency classes structural — each gets a generator or a gate, so a doc fact lives in one place and the next consistency pass finds nothing. A gate that doesn't check its own premise is itself drift waiting to happen. Release-process automation rides here too: automation is single-sourcing for process.

Exit criterion: each listed drift class has a generator or a gate, and a release requires no manual tag/publish steps.

| Issue | What |
|---|---|
| [#1344](https://github.com/aallan/vera/issues/1344) | **Single-source registries umbrella** — one typed source of truth for built-ins, diagnostics, and doc mirrors.  The next three rows are its parts, and it is what makes them one campaign rather than three coincidences. |
| [#735](https://github.com/aallan/vera/issues/735) | **Builtin dispatch table** — replace the 475-line `_translate_call` if-chain with a `{name: BuiltinSpec}` table, then have checker registration and the spec §9 tables consume it.  One table, three consumers. |
| [#1342](https://github.com/aallan/vera/issues/1342) | Conformance matrix — generate a construct × phase × target support table, so which constructs `check`, `verify`, and each compile target accept is read off the suite rather than asserted in prose. |
| [#653](https://github.com/aallan/vera/issues/653) | Spec audit for §0.2 / §0.3 design-principle violations — the spec held to its own principles. |
| [#540](https://github.com/aallan/vera/issues/540) | lychee + markdownlint MD051 cross-doc anchor validation. |

## Stage 21 — The effect hardening sprint

*Production controls for the headline effects.*

Before the flagship builds on them, `Http` and `Inference` get the controls real agent workloads need: auth headers, status codes, timeouts and verbs on one side; cost gates, deterministic replays, mocking, and provider breadth on the other.  The Http and Inference control rows are current KNOWN_ISSUES limitations; the provider and example rows are supporting work on the same effect surface.

Exit criterion: the Http and Inference limitation rows are retired; an agent can call an authenticated API and mock the model call in tests.

| Issue | What |
|---|---|
| [#351](https://github.com/aallan/vera/issues/351) | Http: custom request headers (`Authorization` is the blocking case). |
| [#352](https://github.com/aallan/vera/issues/352) | Http: status-code access — distinguish a 404 from a 500. |
| [#353](https://github.com/aallan/vera/issues/353) | Http: per-request timeout control. |
| [#356](https://github.com/aallan/vera/issues/356) | Http: PUT / PATCH / DELETE. |
| [#370](https://github.com/aallan/vera/issues/370) | Inference: configurable `max_tokens` / `temperature` — cost gates and deterministic replays. |
| [#372](https://github.com/aallan/vera/issues/372) | Inference: user-defined `handle[Inference]` handlers — mocking, caching, routing. |
| [#373](https://github.com/aallan/vera/issues/373) | Host-import `Array<Float64>` returns (`alloc_result_ok_float_array`) — the infrastructure #371 needs. |
| [#371](https://github.com/aallan/vera/issues/371) | `Inference.embed` — vector embeddings, unblocked by #373. |
| [#451](https://github.com/aallan/vera/issues/451) | Provider: Google Gemini. |
| [#1289](https://github.com/aallan/vera/issues/1289) | Provider registry — a model name reaches the toolchain as data rather than a compiler-source edit to `_PROVIDERS`. |
| [#380](https://github.com/aallan/vera/issues/380) | Example: handler mocking for Inference (unblocked by #372). |

## Stage 22 — The verified tool server

*The flagship: an MCP tool server whose tool schemas are compile-time guarantees.*

The thesis demo.  The `<HttpServer>` effect, the WASI Preview 2 target, and its `wasi:http` serve backend shipped in the server-effects sprint (Stage 16); Stage 21 hardens the effects it consumes.  What remains is the `<McpServer>` effect itself, the safety rails a server on untrusted input needs, and the small stdlib surface real tools keep reaching for.

Exit criterion: a working MCP tool server written in Vera, serving contract-verified tools to a real agent, with the demo documented end to end.

| Issue | What |
|---|---|
| [#306](https://github.com/aallan/vera/issues/306) | **`<McpServer>` effect** — verified MCP tool server; contracts guarantee tool schemas at compile time.  The flagship use case. |
| [#239](https://github.com/aallan/vera/issues/239) | Resource limits (fuel, memory, timeout) — essential for untrusted inputs. |
| [#235](https://github.com/aallan/vera/issues/235) | SHA-256 / HMAC — webhook signatures and API authentication patterns. |
| [#233](https://github.com/aallan/vera/issues/233) | Date and time handling beyond `IO.time`. |
| [#236](https://github.com/aallan/vera/issues/236) | CSV parsing and generation. |
| [#440](https://github.com/aallan/vera/issues/440) | `vera test` ADT input generation — tool payloads are ADTs; testing verified tools needs constructor synthesis. |
| [#401](https://github.com/aallan/vera/issues/401) | Static MCP documentation endpoint for Vera itself. |
| [#529](https://github.com/aallan/vera/issues/529) | Use mcp-assert as the test harness for the Vera MCP server. |
| [#329](https://github.com/aallan/vera/issues/329) | Explore Plumbing integration — Vera WASM modules as verified agent tool calls (the exploration item; this sprint is its trigger). |

## Stage 23 — The agent experience sprint

*The loop the model lives in.*

With the flagship standing, invest in the write–verify–fix loop agents actually experience: the language server's remaining seams, the context tools that keep a project inside a token budget, the discoverability surface, and the evidence base — this is where VeraBench's pass@k re-run lands, measuring whether all of the above moved the number.

Exit criterion: the LSP limitation rows are retired, and a fresh VeraBench run (pass@k, current models) is published.

| Issue | What |
|---|---|
| [#724](https://github.com/aallan/vera/issues/724) | LSP: buffer-aware module resolution (imports currently resolve from disk, not open buffers). |
| [#181](https://github.com/aallan/vera/issues/181) | Slot go-to-definition and mechanical slot-index rewriting beyond parameters (`let`/`match` bindings). |
| [#558](https://github.com/aallan/vera/issues/558) | `--explain-slots-at <line>:<col>` — query the slot table at any position, not only where a diagnostic already fires. |
| [#1292](https://github.com/aallan/vera/issues/1292) | LSP: `vera/addEffect` bounds handlers by resolved effect instance, so an alias-spelled `handle[State<MyAlias>]` prunes what `State<Int>` prunes. |
| [#523](https://github.com/aallan/vera/issues/523) | `vera context` — token-budgeted project export for agents. |
| [#698](https://github.com/aallan/vera/issues/698) | `vera shape` — function-archetype histograms per module. |
| [#224](https://github.com/aallan/vera/issues/224) | REPL — the shortest feedback path is currently `vera run` on a file. |
| [#562](https://github.com/aallan/vera/issues/562) | `vera test` advanced features — input shrinking, cross-function scenarios, coverage-guided generation. |
| [#143](https://github.com/aallan/vera/issues/143) | Expand to 50+ examples. |
| [#519](https://github.com/aallan/vera/issues/519) | SKILL.md documentation gap inventory. |
| [#424](https://github.com/aallan/vera/issues/424) | Register veralang.dev with llms.txt directories. |
| [#525](https://github.com/aallan/vera/issues/525) | Close the remaining Agent Score gaps on veralang.dev. |
| [#225](https://github.com/aallan/vera/issues/225) | VeraBench: pass@k evaluation, more models, more tiers — the sprint's measurement. |
| [#1139](https://github.com/aallan/vera/issues/1139) | Formatter internals: parse-time comment ownership and a single recursive renderer, making comment preservation and one-canonical-form structural properties rather than invariants spread across the emitters; retires the remaining relocation cases and the inline/multi-line dual paths. |

## Stage 24 — The browser sprint

*Demos that move.*

The browser seam was deliberately demoted below correctness work (June 2026); it comes due after the flagship.  One suspend/resume mechanism (JSPI) unblocks the three biggest items — sleep-driven animation, async `fetch`, and (with the ANSI interpreter) terminal-style programs rendering unchanged.

Exit criterion: the browser limitation rows are retired and an animated demo runs on veralang.dev.

| Issue | What |
|---|---|
| [#609](https://github.com/aallan/vera/issues/609) | `IO.sleep` via JSPI (or Asyncify fallback) so animations don't freeze the tab; unblocks the browser half of `IO.read_char`. |
| [#355](https://github.com/aallan/vera/issues/355) | Replace sync XHR with `fetch` — every fix option is an async-to-sync bridge, so it shares the JSPI machinery. |
| [#610](https://github.com/aallan/vera/issues/610) | Minimal ANSI-subset interpreter so terminal-style programs render unchanged. |
| [#603](https://github.com/aallan/vera/issues/603) | Export string-marshalling helpers so JS can pass `String` arguments into Vera functions. |

## The horizon

Beyond the staged sprints — grouped by arc, each pulled forward by its trigger, not before.

**Verification depth** — [#427](https://github.com/aallan/vera/issues/427) Tier 2 verification (Z3 with `assert`/lemma hints; its differential oracle — per-monomorphization results from #732 — has shipped, so this is unblocked but outranked), [#439](https://github.com/aallan/vera/issues/439) lifting effect-handler bodies out of Tier 3 (research-grade; approach 3 depends on #427), [#686](https://github.com/aallan/vera/issues/686) `data invariant(...)` clauses (blocked; refinement types are the working alternative).

**Testing depth** — [#795](https://github.com/aallan/vera/issues/795) mutation testing beyond the soundness core (needs the full-sweep deadlock on mutmut 3.6 / Python 3.14 resolved first), [#792](https://github.com/aallan/vera/issues/792) feedback-driven hardening for the deep verifier/smt layers, [#170](https://github.com/aallan/vera/issues/170) Hypothesis as `vera test` generation backend (bookmark; trigger is sustained "cannot generate inputs" warnings).

**Concurrency and WASI** — [#406](https://github.com/aallan/vera/issues/406) WASI 0.3 native async (gated on wasmtime-py exposing component async), [#853](https://github.com/aallan/vera/issues/853) extend wasi-p2 beyond IO+Random (Http via `wasi:http` outgoing-handler, streaming filesystem, sockets), [#270](https://github.com/aallan/vera/issues/270) `handle[Async]` scheduling strategies, [#227](https://github.com/aallan/vera/issues/227) timeout/cancellation effects, [#228](https://github.com/aallan/vera/issues/228) WebSocket/SSE, [#770](https://github.com/aallan/vera/issues/770) non-blocking / timed stdin, [#844](https://github.com/aallan/vera/issues/844) advisory diagnostic for shape-unfusable `async` arguments.

**Modules and ecosystem** — [#187](https://github.com/aallan/vera/issues/187) module-qualified call disambiguation for data types and constructors (the function namespace is settled by spec §8.5.2.2's refusal) → [#127](https://github.com/aallan/vera/issues/127) module re-exports, [#130](https://github.com/aallan/vera/issues/130) package system and registry, [#163](https://github.com/aallan/vera/issues/163) standalone WASM runtime package, [#238](https://github.com/aallan/vera/issues/238) Component Model interop, [#56](https://github.com/aallan/vera/issues/56) incremental compilation, [#294](https://github.com/aallan/vera/issues/294) effect row variable unification, [#785](https://github.com/aallan/vera/issues/785) GitHits MCP (bookmark; trial at the next dependency-facing milestone).

**Standard library long tail** — [#367](https://github.com/aallan/vera/issues/367) Markdown extractors, [#368](https://github.com/aallan/vera/issues/368) HTML accessors, [#507](https://github.com/aallan/vera/issues/507) ability-dispatched array operations, [#509](https://github.com/aallan/vera/issues/509) Unicode-aware string built-ins phase 2, [#1143](https://github.com/aallan/vera/issues/1143) `<DB>` effect phases 2–3 — named columns (via Map), typed rows (via JSON), and further backends.

**Compiler internals** — [#672](https://github.com/aallan/vera/issues/672) canonical WAT formatter, [#745](https://github.com/aallan/vera/issues/745) narrow the wrap-table / Phase 2c emission to `decimal_ops_used` only, [#739](https://github.com/aallan/vera/issues/739) typed `Protocol` interfaces for the mixin mypy carve-outs, [#1275](https://github.com/aallan/vera/issues/1275) memoise module registration so `check`/`verify` stop re-running the per-module harvest checker once per module, [#1343](https://github.com/aallan/vera/issues/1343) decompose `vera/verifier.py` and `smt.py` around explicit obligation generators and translators — sequenced after the [#1344](https://github.com/aallan/vera/issues/1344) umbrella, whose typed registries the generators are meant to consume.

## Ongoing threads

Not stage-gated; advanced alongside whatever stage is active.

- **VeraBench** ([vera-bench](https://github.com/aallan/vera-bench)) — the suite is its own thread; the compiler-side pass@k re-run is staged as Stage 23's measurement ([#225](https://github.com/aallan/vera/issues/225)).
- **CI, process, and tooling** — [#386](https://github.com/aallan/vera/issues/386) Hypothesis round-trip properties (bookmark), [#712](https://github.com/aallan/vera/issues/712) Codecov → Harness migration watch, [#753](https://github.com/aallan/vera/issues/753) pygls / Python 3.16 watch, [#1126](https://github.com/aallan/vera/issues/1126) z3-solver 5.0 bake period, then re-run the obligation differential, [#1103](https://github.com/aallan/vera/issues/1103) migrate GitHub Pages off legacy branch-deploy to a self-owned Actions workflow, [#1295](https://github.com/aallan/vera/issues/1295) decide whether the four abilities (`Eq`/`Hash`/`Ord`/`Show`) highlight distinctly from ordinary types in the editor grammars, [#1263](https://github.com/aallan/vera/issues/1263) detect `_PROVIDERS` model IDs that a vendor has stopped documenting — every provider test pins the ID to a literal, which catches a registry edit but not rot at the vendor, so the signal needs a network-allowed probe.

## Not doing now

Deliberate trade-offs, recorded so they aren't re-litigated by accident.

- **No typed IR for WAT emission.**  The cost-benefit doesn't clear while string-based emission is held safe by the walker-completeness gate and the planned canonical WAT formatter ([#672](https://github.com/aallan/vera/issues/672)).
- **No parser fuzzing yet** ([#402](https://github.com/aallan/vera/issues/402), bookmark).  Trigger: a parser crash from the wild, or spare CI budget.
- **No full Tier 2 verification yet** ([#427](https://github.com/aallan/vera/issues/427)).  Its old blocker is gone — per-monomorphization verification shipped and provides the differential oracle — but the staged sprints above outrank it; it stays on the horizon by priority, not dependency.

## Speculative

Deferred decisions — features without a current driver, captured so the design analysis isn't re-derived if one shows up.  Promotes into a stage when a real trigger appears.

| Item | Issue | Trigger condition |
|------|-------|-------------------|
| Allow `@Byte` arithmetic with verified underflow + overflow guards | [#564](https://github.com/aallan/vera/issues/564) | A real Vera program (or proposed feature) requires byte arithmetic at the user-code level — e.g., a binary-format parser the stdlib doesn't cover; or VeraBench shows a measurable adoption tax from `byte_to_int` round-trips on byte-heavy benchmarks.  Today: the type checker excludes `Byte` from `NUMERIC_TYPES`, so `@Byte - @Byte` etc. produce E140; the round-trip via `byte_to_int` / `int_to_byte` is the canonical idiom. |
