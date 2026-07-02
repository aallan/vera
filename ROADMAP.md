# Roadmap

Where the project is going.  See [HISTORY.md](HISTORY.md) for what's been built and [CHANGELOG.md](CHANGELOG.md) for per-release detail.

The goal is **a stable, working, usable language that doesn't silently fail under the agents using it.**  The near-term tiers below are shaped by the June 2026 external repo audit, which concentrated the risk in three places: the collections runtime keeping data in two stores, the size of the execution runtime, and verification gaps that downgrade silently instead of failing loudly.

Priority lives in this file and nowhere else — issues carry kind and area labels, not priority labels.  Completed items get deleted from these tables and noted in [HISTORY.md](HISTORY.md).

## Where we are

5,806 tests, 104 conformance programs, 36 examples, 14 spec chapters.

## The roadmap

Tier 0 which closed every silent failure is done: no known case remains where Vera accepts a program and quietly does something weaker than it promised. Tier 1 which was around building a safety net and runtime robustness is done: the mutation sweep hardened the soundness core, the execution runtime was decomposed into testable modules, and the oversized test oracles were split into feature-focused files. See [HISTORY.md](HISTORY.md) for more details.  The two remaining tiers are worked roughly top to bottom; small lower-tier items ride along when convenient, but nothing in a lower tier justifies delaying a higher one.

### Tier 2 — Single source of truth

One fact, one home, with drift caught by a gate.  The audit's second theme: most of the repo already works this way; these are the holdouts.

| Issue | What |
|---|---|
| [#735](https://github.com/aallan/vera/issues/735) | Builtin dispatch table — replace the 475-line `_translate_call` if-chain with a `{name: BuiltinSpec}` table, then have checker registration and the spec §9 tables consume it. |
| [#828](https://github.com/aallan/vera/issues/828) | Make `error_code` one-concept-per-code: `ERROR_CODES` names codes but doesn't stop two unrelated diagnostics sharing one (4 such collisions surfaced in #682).  A cheap emission-side registration check shipped; the proper fix is a collision-detection gate + making the registry the single home of each code's concept. |
| [#829](https://github.com/aallan/vera/issues/829) | Extend `TestErrorDisplaySync` to the two unguarded `E001` `spec_ref` mirrors (`AGENTS.md` + the `build_site.py` generator): the example lives in six places, only four are test-guarded, and #826 drifted the ungated pair.  Deeper option: single-source the example so nothing can drift. |
| [#481](https://github.com/aallan/vera/issues/481) | Auto-tag and auto-release on version bump — removes the forgettable manual release steps.  The current manual ordering is documented in [CONTRIBUTING.md](CONTRIBUTING.md) until this lands. |
| [#528](https://github.com/aallan/vera/issues/528) | Gate the hand-edited numbers on the veralang.dev homepage against live counts. |
| [#538](https://github.com/aallan/vera/issues/538) | Replace line-numbered allowlists with inline fence annotations — retires `fix_allowlists.py` and with it the [#606](https://github.com/aallan/vera/issues/606) bulk-shift bug. |
| [#683](https://github.com/aallan/vera/issues/683) | Align spec EBNF and Lark grammar rule names, with a check script to hold the alignment. |

### Tier 3 — Usability and polish

Real improvements that still rank below correctness and robustness.  The browser seam was explicitly demoted here (June 2026 decision): it matters, but not before the language stops failing silently.

| Issue | What |
|---|---|
| [#609](https://github.com/aallan/vera/issues/609) | Browser runtime: `IO.sleep` via JSPI so animations don't freeze the tab.  Also unblocks the browser half of `IO.read_char` (terminal half shipped in v0.0.157). |
| [#610](https://github.com/aallan/vera/issues/610) | Browser runtime: minimal ANSI-subset interpreter so terminal-style programs render unchanged. |
| [#603](https://github.com/aallan/vera/issues/603) | Browser runtime: export string-marshalling helpers so JS can pass `String` arguments into Vera functions. |
| [#349](https://github.com/aallan/vera/issues/349) | Browser runtime (`runtime.mjs`) test coverage to >80%, matching the Python-side gate. |
| [#724](https://github.com/aallan/vera/issues/724) | LSP: buffer-aware module resolution (imports currently resolve from disk, not open buffers). |
| [#725](https://github.com/aallan/vera/issues/725) | LSP: handler-aware `vera/addEffect` propagation bounding. |
| [#181](https://github.com/aallan/vera/issues/181) | Slot go-to-definition and mechanical slot-index rewriting beyond parameters (`let`/`match` bindings). |
| [#739](https://github.com/aallan/vera/issues/739) | Typed `Protocol` interfaces for the mixin mypy carve-outs — unblocked now that the #421 decomposition has reshaped the mixin sets. |
| [#737](https://github.com/aallan/vera/issues/737) | Document the distribution policy (git-clone now; PyPI `veralang` publication gated on #481). |
| [#745](https://github.com/aallan/vera/issues/745) | Narrow the wrap-table / Phase 2c emission to `decimal_ops_used` only — post-#706 only Decimal registers wrappers, but the machinery (`$register_wrapper`, `host_decref_handle`, the Phase 2c walk) is still emitted dead for any Map/Set/JSON/HTML module.  Coupled to Phase 2c emission, so de-gating needs care. |
| [#795](https://github.com/aallan/vera/issues/795) | **Extend mutation testing beyond the soundness core.**  #387 hardened the trust root (`verifier`/`smt`/`checker`/`obligations`, 80.8% → 83.3% caught); this extends the sweep to `codegen`/`wasm`/`transform`/`parser`/CLI, where a surviving mutant is a weak test for an already-*loud* failure (wrong output / trap, already caught by the `test_codegen_*.py` suite + conformance + execution tests) rather than a silent verification gap — so it ranked below the Tier 1 soundness work (now complete).  Needs the full marathon sweep made reliable first: it deadlocks on `mutmut` 3.6 / Python 3.14 (targeted per-function runs are fine).  The deep `smt.py` translate-layer hardening + the verifier timeout probe are tracked in [#792](https://github.com/aallan/vera/issues/792). |
| [#827](https://github.com/aallan/vera/issues/827) | Narrow the diagnostic-fields gate's plumbing-skip: it keys on function name, so a stray/second `Diagnostic` in an `_error`/`_warning` helper would escape both gate passes (latent — no live escape; from the #826 adversarial review). |

### Not doing now

Deliberate trade-offs, recorded so they aren't re-litigated by accident.

- **No typed IR for WAT emission.**  The audit floated one; the cost-benefit doesn't clear while string-based emission is held safe by the walker-completeness gate and the planned canonical WAT formatter ([#672](https://github.com/aallan/vera/issues/672)).
- **No parser fuzzing yet** ([#402](https://github.com/aallan/vera/issues/402), bookmark).  Trigger: a parser crash from the wild, or spare CI budget after the Tier 1 gates land.
- **No full Tier 2 verification before per-monomorphization** ([#427](https://github.com/aallan/vera/issues/427)).  Per-mono ships the agent-visible win now with far less machinery; #427 stays on the milestone horizon (see Milestone 4) and will use per-mono results as its differential oracle.

## Ongoing threads

Not milestone-gated; advanced alongside whatever tier is active.

- **VeraBench** ([vera-bench](https://github.com/aallan/vera-bench)) — the benchmark suite is its own thread, no longer inside Milestone 1.  Compiler-side: [#225](https://github.com/aallan/vera/issues/225) (pass@k, more models, more tiers).
- **CI and process** — [#386](https://github.com/aallan/vera/issues/386) Hypothesis round-trip properties, [#540](https://github.com/aallan/vera/issues/540) cross-doc anchor validation, [#672](https://github.com/aallan/vera/issues/672) canonical WAT formatter, [#702](https://github.com/aallan/vera/issues/702) Linux aarch64 CI matrix entry.
- **Spec and doc audits** — [#653](https://github.com/aallan/vera/issues/653) §0.2/§0.3 design-principle violations, [#519](https://github.com/aallan/vera/issues/519) SKILL.md gap inventory.

## Milestones — beyond the roadmap

The longer arcs.  Each pulls forward when the tiers above empty out, not before.

### Milestone 1: Prove the thesis

*Do LLMs write better code in Vera than in existing languages?  Build the evidence base and remove the friction that blocks honest evaluation.*  The benchmark suite itself moved to Ongoing threads; what remains is contract-driven testing completeness:

- [#440](https://github.com/aallan/vera/issues/440) **`vera test` ADT input generation** — constructor synthesis with recursive field generation; the last skipped parameter category.
- [#562](https://github.com/aallan/vera/issues/562) **Advanced testing features** — input shrinking, cross-function scenarios, coverage-guided generation.
- [#170](https://github.com/aallan/vera/issues/170) **Hypothesis as generation backend** (bookmark) — trigger is sustained "cannot generate inputs" warnings on String/Array contracts.

### Milestone 2: Verified agent orchestration

*A working MCP tool server written in Vera, with contracts guaranteeing tool schemas at compile time — the flagship demo.*

**Inference hardening** (the headline effect gets production controls before anything builds on it):

- [#370](https://github.com/aallan/vera/issues/370) configurable `max_tokens` / `temperature` · [#372](https://github.com/aallan/vera/issues/372) user-defined `handle[Inference]` handlers · [#371](https://github.com/aallan/vera/issues/371) `Inference.embed` (depends on [#373](https://github.com/aallan/vera/issues/373) float-array host-alloc) · providers: [#425](https://github.com/aallan/vera/issues/425) Grok, [#450](https://github.com/aallan/vera/issues/450) DeepSeek, [#451](https://github.com/aallan/vera/issues/451) Gemini · examples: [#379](https://github.com/aallan/vera/issues/379) Inference + JSON composition, [#380](https://github.com/aallan/vera/issues/380) handler mocking.

**Http hardening** — [#351](https://github.com/aallan/vera/issues/351) custom headers, [#352](https://github.com/aallan/vera/issues/352) status codes, [#353](https://github.com/aallan/vera/issues/353) timeouts, [#355](https://github.com/aallan/vera/issues/355) replace sync XHR in the browser runtime, [#356](https://github.com/aallan/vera/issues/356) PUT/PATCH/DELETE.

**Server effects** — [#306](https://github.com/aallan/vera/issues/306) `<McpServer>` effect (**the flagship use case**; the `<HttpServer>` effect shipped in v0.0.193, the experimental WASI Preview 2 target in v0.0.194, and its `wasi:http` serve backend — `--world server` — in v0.0.195), plus [#239](https://github.com/aallan/vera/issues/239) resource limits (fuel, memory, timeout) for untrusted inputs.

**Server-adjacent** — [#233](https://github.com/aallan/vera/issues/233) date/time, [#235](https://github.com/aallan/vera/issues/235) SHA-256/HMAC, [#229](https://github.com/aallan/vera/issues/229) database effect (parameterised queries only; [#309](https://github.com/aallan/vera/issues/309) tracks contract-verified SQL), [#236](https://github.com/aallan/vera/issues/236) CSV.

### Milestone 3: Tooling for real-world adoption

*Agents can discover Vera, learn it from documentation, write it with real-time feedback, and wire it into existing workflows.*

**Agent integration** — [#329](https://github.com/aallan/vera/issues/329) Plumbing integration (Vera WASM modules as verified tool calls), [#523](https://github.com/aallan/vera/issues/523) `vera context` token-budgeted project export, [#698](https://github.com/aallan/vera/issues/698) `vera shape` function-archetype histograms, [#558](https://github.com/aallan/vera/issues/558) `--explain-slots` beyond signatures (match arms, W001 holes).

**Discoverability** — [#424](https://github.com/aallan/vera/issues/424) llms.txt directory registration, [#401](https://github.com/aallan/vera/issues/401) static MCP documentation endpoint (test harness recommendation in [#529](https://github.com/aallan/vera/issues/529)), [#525](https://github.com/aallan/vera/issues/525) remaining Agent Score gaps on veralang.dev, [#143](https://github.com/aallan/vera/issues/143) expand to 50+ examples.

**Developer experience** — [#224](https://github.com/aallan/vera/issues/224) REPL.

### Milestone 4: Language maturity

*The long tail of real-world requirements; the language becomes competitive, not just viable.*

**Verification depth** — [#427](https://github.com/aallan/vera/issues/427) Tier 2 verification (Z3 with `assert`/lemma hints), validated differentially against the per-monomorphization results from [#732](https://github.com/aallan/vera/issues/732); [#439](https://github.com/aallan/vera/issues/439) lifting effect-handler bodies out of Tier 3 (research-grade; approach 3 in the issue depends on #427); [#686](https://github.com/aallan/vera/issues/686) `data invariant(...)` clauses (blocked; refinement types are the working alternative).

**Concurrency and streaming** — [#406](https://github.com/aallan/vera/issues/406) WASI 0.3 native async (builds on the v0.0.194 WASI 0.2 target; gated on wasmtime-py exposing component async), [#270](https://github.com/aallan/vera/issues/270) `handle[Async]` scheduling strategies, [#228](https://github.com/aallan/vera/issues/228) WebSocket/SSE, [#227](https://github.com/aallan/vera/issues/227) timeout/cancellation effects, [#844](https://github.com/aallan/vera/issues/844) advisory diagnostic for effect-eligible but shape-unfusable `async` arguments, [#770](https://github.com/aallan/vera/issues/770) non-blocking / timed stdin + input concurrency (wait on a key and a clock at once).

**Ecosystem** — [#130](https://github.com/aallan/vera/issues/130) package system and registry, [#163](https://github.com/aallan/vera/issues/163) standalone WASM runtime package, [#238](https://github.com/aallan/vera/issues/238) Component Model interop, [#56](https://github.com/aallan/vera/issues/56) incremental compilation, [#294](https://github.com/aallan/vera/issues/294) effect row variable unification, [#785](https://github.com/aallan/vera/issues/785) GitHits MCP for dependency-reference retrieval (bookmark — trial when the dependency-facing package work lands).

**Standard library completeness** — [#367](https://github.com/aallan/vera/issues/367) Markdown extractors, [#368](https://github.com/aallan/vera/issues/368) HTML accessors, [#507](https://github.com/aallan/vera/issues/507) ability-dispatched array operations, [#509](https://github.com/aallan/vera/issues/509) Unicode-aware string built-ins, [#187](https://github.com/aallan/vera/issues/187) → [#127](https://github.com/aallan/vera/issues/127) module-qualified call disambiguation → module re-exports.

## Speculative

Deferred decisions — features without a current driver, captured so the design analysis isn't re-derived if one shows up.  Promotes into a tier or milestone when a real trigger appears.

| Item | Issue | Trigger condition |
|------|-------|-------------------|
| Allow `@Byte` arithmetic with verified underflow + overflow guards | [#564](https://github.com/aallan/vera/issues/564) | A real Vera program (or proposed feature) requires byte arithmetic at the user-code level — e.g., a binary-format parser the stdlib doesn't cover; or VeraBench shows a measurable adoption tax from `byte_to_int` round-trips on byte-heavy benchmarks.  Today: the type checker excludes `Byte` from `NUMERIC_TYPES`, so `@Byte - @Byte` etc. produce E140; the round-trip via `byte_to_int` / `int_to_byte` is the canonical idiom. |
