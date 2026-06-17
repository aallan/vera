# Roadmap

Where the project is going.  See [HISTORY.md](HISTORY.md) for what's been built and [CHANGELOG.md](CHANGELOG.md) for per-release detail.

The goal is **a stable, working, usable language that doesn't silently fail under the agents using it.**  The near-term tiers below are shaped by the June 2026 external repo audit, which concentrated the risk in three places: the collections runtime keeping data in two stores, the size of the execution runtime, and verification gaps that downgrade silently instead of failing loudly.

Priority lives in this file and nowhere else — issues carry kind and area labels, not priority labels.  Completed items get deleted from these tables and noted in [HISTORY.md](HISTORY.md).

## Where we are

4,440 tests, 90 conformance programs, 35 examples, 13 spec chapters.

## The roadmap

Four tiers, worked roughly top to bottom.  Small lower-tier items ride along when convenient, but nothing in a lower tier justifies delaying a Tier 0 item.

### Tier 0 — Close the silent failures

The cases where Vera accepts a program and quietly does something weaker than it promised.  These contradict the language's core claim and go first.

| Issue | What | Why it's first |
|---|---|---|
| [#747](https://github.com/aallan/vera/issues/747) | `@Nat` narrowing at projection binding sites | `let`/argument/effect-operation-argument/constructor-field/match-bind/literal-destructure narrowing is now obligation-checked (#552); ADT sub-pattern binds, non-literal destructures, generic constructor fields, effect-operation formals, and function formals instantiated to `@Nat`, and imported ADT constructors still need scrutinee/call-site type inference or imported-module constructor lookup to obligate, and the Tier-3 runtime guard backs only the `let` site. |
| [#746](https://github.com/aallan/vera/issues/746) | Refinement-type predicate verification | User refinement predicates (`{ @Int \| p }`) are parsed but verified nowhere — a value violating the predicate is accepted silently.  Needs predicate→Z3 translation, binder substitution, and discharge at every binding site. |
| [#732](https://github.com/aallan/vera/issues/732) | Per-monomorphization static verification for generic functions | Generic (`forall<T>`) bodies skip all static verification today — a silent downgrade from Tier 1 to Tier 3.  Verifying each concrete instantiation reuses the existing pipeline; closes the static half of [#555](https://github.com/aallan/vera/issues/555). |
| [#730](https://github.com/aallan/vera/issues/730) | Precondition-check calls in statement position | E501 fires only for calls in value position; a call whose result is discarded is never checked against its `requires(...)`. |
| [#680](https://github.com/aallan/vera/issues/680) | Auto-inject obligations for primitive operations (division, modulo, array index) | Aligns the implementation with the README's "compiler proves primitive safety" claim, generalising the #520 obligation-discharge pattern. |

### Tier 1 — Safety net and runtime robustness

The infrastructure that catches the next regression before a user does, plus the decomposition that makes the runtime testable.

| Issue | What |
|---|---|
| [#734](https://github.com/aallan/vera/issues/734) | Characterization harness for `execute()` — pin the observable contract (every `ExecuteResult` field × normal/trap/interrupt) before decomposing.  Sequenced after #706 (bucket-as-truth, now landed); lands **before** #421. |
| [#421](https://github.com/aallan/vera/issues/421) | Decompose `vera/codegen/api.py` into a `vera/runtime/` package, one host-binding family per PR.  The file has doubled since the issue was filed (now 4,253 lines); the issue carries a supersession comment with the current scope. |
| [#392](https://github.com/aallan/vera/issues/392) | Audit the `smt.py` Z3 translation layer for soundness — a bug here silently bypasses verification. |
| [#592](https://github.com/aallan/vera/issues/592) | End-to-end behavioural tests for the five UTF-8 decode sites currently pinned only by structural greps. |
| [#645](https://github.com/aallan/vera/issues/645) | Explicit `encoding='utf-8'` at every text-mode file call, with a pre-commit check to hold the line. |
| [#657](https://github.com/aallan/vera/issues/657) | Convert `INVARIANT_DEFENSIVE` sites and audit `PROPAGATE` cleanup (follow-up to the #626 error-handling taxonomy). |
| [#679](https://github.com/aallan/vera/issues/679) | Chapter 8 (modules) conformance programs — the only spec chapter with no `chNN_*.vera` coverage. |
| [#738](https://github.com/aallan/vera/issues/738) | Mark the `TestHostHandleReclamation573` trio as stress tests so the local inner loop stops paying ~12 minutes per run. |

### Tier 2 — Single source of truth

One fact, one home, with drift caught by a gate.  The audit's second theme: most of the repo already works this way; these are the holdouts.

| Issue | What |
|---|---|
| [#735](https://github.com/aallan/vera/issues/735) | Builtin dispatch table — replace the 475-line `_translate_call` if-chain with a `{name: BuiltinSpec}` table, then have checker registration and the spec §9 tables consume it. |
| [#481](https://github.com/aallan/vera/issues/481) | Auto-tag and auto-release on version bump — removes the forgettable manual release steps.  The current manual ordering is documented in [CONTRIBUTING.md](CONTRIBUTING.md) until this lands. |
| [#539](https://github.com/aallan/vera/issues/539) | `vera builtins/effects/errors --json` introspection subcommands — the compiler becomes the source of truth for its own counts. |
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
| [#419](https://github.com/aallan/vera/issues/419) | Split `tests/test_codegen.py` (19,570 lines) into feature-focused files. |
| [#739](https://github.com/aallan/vera/issues/739) | Typed `Protocol` interfaces for the mixin mypy carve-outs — sequenced after the #421 decomposition reshapes the mixin sets. |
| [#737](https://github.com/aallan/vera/issues/737) | Document the distribution policy (git-clone now; PyPI `veralang` publication gated on #481). |
| [#745](https://github.com/aallan/vera/issues/745) | Narrow the wrap-table / Phase 2c emission to `decimal_ops_used` only — post-#706 only Decimal registers wrappers, but the machinery (`$register_wrapper`, `host_decref_handle`, the Phase 2c walk) is still emitted dead for any Map/Set/JSON/HTML module.  Coupled to Phase 2c emission, so de-gating needs care. |
| [#749](https://github.com/aallan/vera/issues/749) | `@Nat`-narrowing review follow-ups from #748 — container `IndexExpr`/`InterpolatedString` test pins, a `_fresh_slot_var` alias unit-test, a verifier/codegen `_narrows_into_nat` differential test, and a dedicated `@Nat`-guard trap kind.  Polish / test-debt; no correctness gap. |

### Not doing now

Deliberate trade-offs, recorded so they aren't re-litigated by accident.

- **No typed IR for WAT emission.**  The audit floated one; the cost-benefit doesn't clear while string-based emission is held safe by the walker-completeness gate and the planned canonical WAT formatter ([#672](https://github.com/aallan/vera/issues/672)).
- **No `tests/test_checker.py` split** ([#420](https://github.com/aallan/vera/issues/420)).  At 5,939 lines it is half the size of `test_codegen.py` and not where the pain is; a closure proposal is pending.
- **No parser fuzzing yet** ([#402](https://github.com/aallan/vera/issues/402), bookmark).  Trigger: a parser crash from the wild, or spare CI budget after the Tier 1 gates land.
- **No full Tier 2 verification before per-monomorphization** ([#427](https://github.com/aallan/vera/issues/427)).  Per-mono ships the agent-visible win now with far less machinery; #427 stays on the milestone horizon (see Milestone 4) and will use per-mono results as its differential oracle.

## Ongoing threads

Not milestone-gated; advanced alongside whatever tier is active.

- **VeraBench** ([vera-bench](https://github.com/aallan/vera-bench)) — the benchmark suite is its own thread, no longer inside Milestone 1.  Compiler-side: [#225](https://github.com/aallan/vera/issues/225) (pass@k, more models, more tiers).
- **CI and process** — [#386](https://github.com/aallan/vera/issues/386) Hypothesis round-trip properties, [#387](https://github.com/aallan/vera/issues/387) mutation testing, [#540](https://github.com/aallan/vera/issues/540) cross-doc anchor validation, [#672](https://github.com/aallan/vera/issues/672) canonical WAT formatter, [#682](https://github.com/aallan/vera/issues/682) diagnostic-tagging enforcement + backfill, [#702](https://github.com/aallan/vera/issues/702) Linux aarch64 CI matrix entry.
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

**Server effects** — [#237](https://github.com/aallan/vera/issues/237) WASI 0.2 compliance → [#305](https://github.com/aallan/vera/issues/305) `<HttpServer>` effect → [#306](https://github.com/aallan/vera/issues/306) `<McpServer>` effect (**the flagship use case**), plus [#239](https://github.com/aallan/vera/issues/239) resource limits (fuel, memory, timeout) for untrusted inputs.

**Server-adjacent** — [#233](https://github.com/aallan/vera/issues/233) date/time, [#235](https://github.com/aallan/vera/issues/235) SHA-256/HMAC, [#229](https://github.com/aallan/vera/issues/229) database effect (parameterised queries only; [#309](https://github.com/aallan/vera/issues/309) tracks contract-verified SQL), [#236](https://github.com/aallan/vera/issues/236) CSV.

### Milestone 3: Tooling for real-world adoption

*Agents can discover Vera, learn it from documentation, write it with real-time feedback, and wire it into existing workflows.*

**Agent integration** — [#329](https://github.com/aallan/vera/issues/329) Plumbing integration (Vera WASM modules as verified tool calls), [#523](https://github.com/aallan/vera/issues/523) `vera context` token-budgeted project export, [#698](https://github.com/aallan/vera/issues/698) `vera shape` function-archetype histograms, [#558](https://github.com/aallan/vera/issues/558) `--explain-slots` beyond signatures (match arms, W001 holes).

**Discoverability** — [#424](https://github.com/aallan/vera/issues/424) llms.txt directory registration, [#401](https://github.com/aallan/vera/issues/401) static MCP documentation endpoint (test harness recommendation in [#529](https://github.com/aallan/vera/issues/529)), [#525](https://github.com/aallan/vera/issues/525) remaining Agent Score gaps on veralang.dev, [#143](https://github.com/aallan/vera/issues/143) expand to 50+ examples.

**Developer experience** — [#224](https://github.com/aallan/vera/issues/224) REPL.

### Milestone 4: Language maturity

*The long tail of real-world requirements; the language becomes competitive, not just viable.*

**Verification depth** — [#427](https://github.com/aallan/vera/issues/427) Tier 2 verification (Z3 with `assert`/lemma hints), validated differentially against the per-monomorphization results from [#732](https://github.com/aallan/vera/issues/732); [#439](https://github.com/aallan/vera/issues/439) lifting effect-handler bodies out of Tier 3 (research-grade; approach 3 in the issue depends on #427); [#686](https://github.com/aallan/vera/issues/686) `data invariant(...)` clauses (blocked; refinement types are the working alternative).

**Concurrency and streaming** — [#406](https://github.com/aallan/vera/issues/406) WASI 0.3 native async (depends on #237), [#270](https://github.com/aallan/vera/issues/270) `handle[Async]` scheduling strategies, [#228](https://github.com/aallan/vera/issues/228) WebSocket/SSE, [#227](https://github.com/aallan/vera/issues/227) timeout/cancellation effects.

**Ecosystem** — [#130](https://github.com/aallan/vera/issues/130) package system and registry, [#163](https://github.com/aallan/vera/issues/163) standalone WASM runtime package, [#238](https://github.com/aallan/vera/issues/238) Component Model interop, [#56](https://github.com/aallan/vera/issues/56) incremental compilation, [#294](https://github.com/aallan/vera/issues/294) effect row variable unification.

**Standard library completeness** — [#367](https://github.com/aallan/vera/issues/367) Markdown extractors, [#368](https://github.com/aallan/vera/issues/368) HTML accessors, [#507](https://github.com/aallan/vera/issues/507) ability-dispatched array operations, [#509](https://github.com/aallan/vera/issues/509) Unicode-aware string built-ins, [#187](https://github.com/aallan/vera/issues/187) → [#127](https://github.com/aallan/vera/issues/127) module-qualified call disambiguation → module re-exports.

## Speculative

Deferred decisions — features without a current driver, captured so the design analysis isn't re-derived if one shows up.  Promotes into a tier or milestone when a real trigger appears.

| Item | Issue | Trigger condition |
|------|-------|-------------------|
| Allow `@Byte` arithmetic with verified underflow + overflow guards | [#564](https://github.com/aallan/vera/issues/564) | A real Vera program (or proposed feature) requires byte arithmetic at the user-code level — e.g., a binary-format parser the stdlib doesn't cover; or VeraBench shows a measurable adoption tax from `byte_to_int` round-trips on byte-heavy benchmarks.  Today: the type checker excludes `Byte` from `NUMERIC_TYPES`, so `@Byte - @Byte` etc. produce E140; the round-trip via `byte_to_int` / `int_to_byte` is the canonical idiom. |
