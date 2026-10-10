# Roadmap

Where the project is going.  See [HISTORY.md](HISTORY.md) for what's been built and [CHANGELOG.md](CHANGELOG.md) for per-release detail.

The goal is unchanged: **a stable, working, usable language that doesn't silently fail under the agents using it** — and, on that foundation, the flagship demonstration that an agent can write verified tools in it.

## How this file works

The roadmap is a sequence of **stages** — concentrated sprints over a coherent class of issues — continuing the numbering from [HISTORY.md](HISTORY.md).  A stage is a campaign: pick a themed set, drive it to zero, release, move on.  When a stage's table empties, the stage moves to HISTORY.md with its releases and the next one starts.

Ordering derives from the design principles ([DESIGN.md](DESIGN.md)): verification truth first, then structural drift-proofing, then the capabilities the flagship needs, then the experience around them.  Priority lives in this file and nowhere else — issues carry kind and area labels, not priority labels.  Completed items are deleted from these tables and noted in HISTORY.md.  Stages beyond the next one or two are a forecast, not a commitment — they reorder freely as reality intervenes, and a new bug class outranks everything and becomes its own burndown.

## Where we are

[TESTING.md](TESTING.md#overview) counts the tests, the conformance programs and the examples.  [KNOWN_ISSUES.md](KNOWN_ISSUES.md) tracks the open bugs, plus the *limitations* the stages below retire.

v0.3.0 is the sound base (Stage 29), reached through v0.2.2 to v0.2.8 (Stages 22 to 28).  The feature release follows it in Stage 30: the `Decision` effect ([#1467](https://github.com/aallan/vera/issues/1467)) and its blockers, [#351](https://github.com/aallan/vera/issues/351), [#352](https://github.com/aallan/vera/issues/352), [#372](https://github.com/aallan/vera/issues/372) and [#373](https://github.com/aallan/vera/issues/373).

## The bug queue

A bug class outranks stage work, so the open [`bug`-labelled issues](https://github.com/aallan/vera/issues?q=is%3Aissue%20state%3Aopen%20label%3Abug) are the queue the fix releases work from, soundness defects first, and [KNOWN_ISSUES.md](KNOWN_ISSUES.md) carries each one's full account.

Bugs in a mechanism cluster close in the stage that removes their mechanism and carry that release's [milestone](https://github.com/aallan/vera/milestones); the rest are the [debt track](https://github.com/aallan/vera/milestone/10), burned down alongside the stages in small pull requests.

## Stage 19 — The verification completeness sprint

*`vera verify` tells the whole truth.*

Verification-completeness gaps — an obligation not emitted, a guard not planted — individually small:

| Issue | What |
|---|---|
| [#909](https://github.com/aallan/vera/issues/909) | A value's postcondition / refinement is forgotten through an ADT field (box then unbox loses the fact), degrading provable programs to Tier 3. |
| [#1561](https://github.com/aallan/vera/issues/1561) | A generic function's `decreases` stays Tier 3 when it calls a non-recursive helper, where the monomorphic form is proved. |
| [#1585](https://github.com/aallan/vera/issues/1585) | A generic `where` helper on a recursion cycle with its generic parent leaves its own `decreases` at Tier 3, though the parent's is proved. |
| [#1577](https://github.com/aallan/vera/issues/1577) | An imported generic whose `decreases` measure is one of its module's data types is proved in the module's own run and falls to Tier 3 through an importer. |
| [#1177](https://github.com/aallan/vera/issues/1177) | A parameterized ADT `decreases` measure (`List<Int>`) is ranked at run time through per-instantiation size helpers, so it gets a runtime guard. |
| [#1450](https://github.com/aallan/vera/issues/1450) | The boundary guard composes a refinement over a refined base, so such a type compiles instead of being refused with **E618**. |

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
| [#1525](https://github.com/aallan/vera/issues/1525) | **Derive each fact once** — a resolved program representation shared by the checker, the verifier and code generation, so no two of them re-derive a fact and disagree. |
| [#1396](https://github.com/aallan/vera/issues/1396) | Spec question: whether a repeated contract clause (two identical `requires`) is refused, warned about or accepted — decide it and state it in the spec. |
| [#1529](https://github.com/aallan/vera/issues/1529) | Each fix PR carries its own CHANGELOG fragment, assembled at release, so fix PRs share no lines. |
| [#1531](https://github.com/aallan/vera/issues/1531) | Close two more ways a CI gate line can exit 0 unseen by the gate-placement test. |
| [#1532](https://github.com/aallan/vera/issues/1532) | Pin the nested refused-constructor search in the #1433 duplicate-name tests. |
| [#1611](https://github.com/aallan/vera/issues/1611) | Five test cells that can pass without exercising what they assert — each shown by a mutation or a direct run. |
| [#1612](https://github.com/aallan/vera/issues/1612) | Stale comments and docstrings in tests and two compiler helpers, a test cache that never hits, and a mis-positioned constructor call. |

## Stage 22 — The fast lane and single sources (v0.2.2)

*A fix merges in under an hour.*

The pull-request gate becomes a fast lane with the full matrix after merge, and the lists the docs copy by hand render from their sources.  Four rows carry over from v0.2.1: the distrust tester's nightly trials, its attribution through the reconciliation ([#1633](https://github.com/aallan/vera/issues/1633)), the desugar of a module's call by its own path, and three CI changes.

Exit criterion: a pull request's CI finishes in 20 minutes or less, and every hand-copied list renders from its source.

| Change | What |
|---|---|
| The fast lane | A pull request's required checks become lint, sharded Python 3.12 runs on Linux and Windows, eager-GC, browser parity, CodeQL and the supply-chain jobs.  The full platform matrix runs after merge, nightly and on a version-raising pull request; a failure files an issue, and the release waits for the post-merge run. |
| Rendered lists | Each hand-copied list renders from its source and retires the gate that compared the copies: the effect lists from `vera effects --json`, the spec's grammar listing from `grammar.lark`, the limitation tables from one data file beside KNOWN_ISSUES.md, `examples/README.md` from the examples' headers, and the landing page's status paragraph from `scripts/render_status.py`. |
| CHANGELOG fragments | Each pull request adds its own file under `changelog.d/`, and the release assembles the section ([#1529](https://github.com/aallan/vera/issues/1529)), so fix pull requests share no line. |
| The scorecard | `scripts/render_status.py` also measures the Stage 29 scorecard, so every release pull request re-measures it without hand work. |
| One pipeline driver | `tests/pipeline.py` runs check, verify, compile and run in process and returns structured results.  The per-file drivers and the CLI subprocesses move to it, leaving `test_cli.py` and a few corpus programs as the CLI smoke test, and tests that read WAT text read instead a guard-and-trap manifest that code generation emits beside it. |
| `vera test --distrust`, nightly | The nightly lane runs the distrust corpus test with many trials per function (`VERA_DISTRUST_TRIALS`); the pull-request run uses five. |
| [#1633](https://github.com/aallan/vera/issues/1633) | `vera test --distrust` attributes a trap through the reconciliation join instead of by exact span, so a check whose obligation record sits at another node is attributed rather than unattributed. |
| Desugar once | A module's call by its own path becomes the bare call, so no later phase meets it. |
| CI | Path filters, a 94% coverage floor, and a CHANGELOG gate that reads the pull request's base. |
| [#1645](https://github.com/aallan/vera/issues/1645) | Each run-level conformance program whose run reaches less than its header claims gets a `main` that reaches every feature the header names, and a check holds every function such a program defines reachable from the one `vera run` executes. |

## Stage 23 — `Nat` and the lowering boundary (v0.2.3)

*`Nat` is the type the spec defines, and what checks compiles.*

The `Nat` change is a language change, so the release carries an upgrade note that names what breaks and how to fix it.  The stage closes the `Nat`-width and literal-typing clusters and the constructs code generation cannot lower ([milestone v0.2.3](https://github.com/aallan/vera/milestone/3)).

Exit criterion: the corpus differential names every program whose verdict or output moves, and the distrust tester is green.

| Change | What |
|---|---|
| `Nat` as the non-negative i64 | `Nat` becomes the non-negative i64 that spec §2.2 defines.  Every integer literal is `Int`, narrowing into `@Nat` stays obligated and is Tier 1 for a literal, and the u64 range, `nat_to_int_coerce`, the sign-provenance classifiers and §4.2's typing-by-value rules go.  A program that held a `@Nat` above i64.MAX breaks, and a literal above it draws a diagnostic. |
| `can_lower` | One module answers whether code generation can lower a construct, and the checker refuses what it cannot, in place of mirrored gates such as E339.  A handler for an effect other than `State` or `Exn` is refused at check, general handlers become feature work after v0.3.0, and DESIGN.md's effects paragraph is restated to match. |
| Debt, first batch | Local-debt bugs from the verifier, checker, termination, runtime and tooling clusters, in small pull requests. |

## Stage 24 — Hosts, the generator and the fold (v0.2.4)

*One source where there were many.*

The host bindings, the tree walks and the test inputs each get one source: a registry, a fold and a generator.

Exit criterion: the fold leaves WAT byte-identical over the corpus, and the generator runs nightly.

| Change | What |
|---|---|
| Host bindings from the registry | The built-in registry gains implementation metadata and generates the import declarations, the set of host imports used, the `api.py` registration table, the `runtime.mjs` dispatch skeleton and the WASI refusal list, so a host operation is added in one place. |
| One fold | One `Expr` fold and one binder-aware scope walker; the hand-written dispatchers and scope implementations port to them one at a time, and the walker-coverage gate retires. |
| A program generator | A type-directed generator feeds three nightly differentials: what checks compiles and loads with every public function exported; every obligation record has its guard and every guard its record; a Tier 1 proof meets no runtime violation on generated inputs. |
| A mutation lane | Mutation testing scoped to a pull request's diff. |

## Stage 25 — One resolver (v0.2.5)

*Every name resolved once.*

Stages 25 to 27 build the shared representation [#1525](https://github.com/aallan/vera/issues/1525) asks for, one fact at a time: names, then types, then obligations, each derived once and read by every later phase.

A resolver pass owns names.  Every declaration gets a `DeclId`, every occurrence maps to one exactly once, and code generation's symbols derive from them in a namespace no generated name can reach.  The prelude becomes a real module with reserved names ([#1469](https://github.com/aallan/vera/issues/1469)), so a program cannot redeclare `Option`, `Result` or `Json`, and the upgrade note says so.  E608–E623 move to check time, and the verifier and code generation stop registering declarations of their own.  The stage closes the ownership and prelude cluster ([milestone v0.2.5](https://github.com/aallan/vera/milestone/5)).

Exit criterion: `check` and `verify` verdicts are identical over the corpus except where the pull request names a change, and WAT differs only in symbol names.

## Stage 26 — One typed program (v0.2.6)

*Every type derived once.*

Monomorphisation runs once, before verify and compile, and every node of every clone carries its type in a table keyed by node identity; literal typing is sound for the value and carries its sign.  The backend's own inference (the `_infer_*` functions), both clone namers, code generation's AST fallbacks for `Nat` and the verifier's `_resolve_type` go, and so does the roster of readers allowed into the checker's tables.  Clone names change, so WAT moves across the corpus.  The stage closes the re-derived-type cluster ([milestone v0.2.6](https://github.com/aallan/vera/milestone/6)).

Exit criterion: the corpus differential names every mover, and the existing matrices and the generator's differentials are green.

## Stage 27 — One obligation table (v0.2.7)

*Every obligation listed once.*

One pass lists every obligation site; the verifier discharges what it can and code generation guards the rest, so whether an obligation is `tier3` or `tier3_unguarded` is read from its record rather than predicted.  `_walk_for_nat_binding_obligations`, code generation's hand-down, the verifier's `guarded=` claims and the mirror predicates go.  Once coverage is complete, `tier3_unguarded` becomes an error, §6.4.2's taint rules go, and `test_nested_container_guards` moves wholly to the nightly lane.  The table wants node types, so this stage may ship inside Stage 26's release.  It closes the guard-agreement cluster ([milestone v0.2.7](https://github.com/aallan/vera/milestone/7)).

Exit criterion: every obligation record and every emitted guard come from one table entry, by construction.

## Stage 28 — Decomposition and the spec (v0.2.8)

*Readable parts, and a spec that states the language.*

The large classes split once Stages 25 to 27 have deleted what they duplicate, and the spec hands its implementation status to the documents that track it.  The stage closes what remains of the [debt track](https://github.com/aallan/vera/milestone/10).

Exit criterion: no function is over 500 lines, and the spec carries no implementation status.

| Change | What |
|---|---|
| Decomposition | `ContractVerifier`, `WasmContext` and `CodeGenerator` split along the seams Stages 25 to 27 create. |
| The spec states the language | Implementation status moves out of the spec to KNOWN_ISSUES.md and the limitation data file. |
| Fixes that clear | A gate applies each diagnostic's `Fix` template to its repro, and the diagnostic must no longer fire. |
| Debt, second batch | Whatever remains of the debt track. |

## Stage 29 — The sound base (v0.3.0)

*Declared sound by measurement.*

A release only.  Its pull request re-measures the scorecard below, and v0.3.0 ships when every target is met.  VeraBench re-runs on v0.3.0 with fresh generation, verify@1 beside pass@1 and adversarial inputs, and the landing page quotes that run.

Exit criterion: every target in the scorecard is met.

| Measure | Target |
|---|---|
| Open `soundness` bugs | 0 |
| Open bugs | The debt track's residue only, each with an instrument |
| Backend `_infer_*` functions | 0 |
| Same-named `Nat`/`Int` helpers in `vera/verifier.py` and `vera/wasm/` | 0 |
| Explicit `guarded=` claims by the verifier | 0 |
| Obligation kinds with one record both sides read | All of them |
| Modules that resolve a name or decide an owner | 1 |
| Hand-rolled `isinstance` dispatchers over `Expr` | None: the fold |
| Functions over 500 lines | 0 |
| Host built-ins hand-mirrored across hosts | 0: generated |
| Gate scripts that exist only to sync copies | 0 |
| Hand-mirrored facts | 0 |
| CI wall time per pull-request push | ≤ 20 minutes |
| Runner-minutes per pull-request push | ≤ 100 |
| Fix pull requests, median: CI runs; hours to merge | ≤ 2; ≤ 2 |
| Suite in the pull-request gate: tests; worker-seconds | ≤ 15,000; ≤ 3,000 |
| Subprocess share of suite time | ≤ 5% |
| Conformance entries with golden output | All of them |
| Program generator with differentials | Nightly |
| `vera test` executes proved functions | Yes, in CI |
| Statement / branch coverage | ≥ 96% / ≥ 92%, measured after merge |
| Spec words; issue links in the spec | Fewer than v0.2.0's; 0 |

## Stage 30 — The effect hardening sprint

*Production controls for the headline effects.*

Before the flagship builds on them, `Http` and `Inference` get the controls real agent workloads need: auth headers, status codes, timeouts and verbs on one side; cost gates, deterministic replays, mocking, and provider breadth on the other.  A second model tier joins the same surface: typed decisions carrying a confidence value ([#1467](https://github.com/aallan/vera/issues/1467)), which begin as a user-declared effect and are promoted to a built-in only once their calibration is measured.  The Http and Inference control rows are KNOWN_ISSUES limitations; the provider and example rows are supporting work on the same effect surface.

Exit criterion: the Http and Inference limitation rows are retired; an agent can call an authenticated API and mock the model call in tests.

| Issue | What |
|---|---|
| [#351](https://github.com/aallan/vera/issues/351) | Http: custom request headers (`Authorization` is the blocking case). |
| [#352](https://github.com/aallan/vera/issues/352) | Http: status-code access — distinguish a 404 from a 500. |
| [#353](https://github.com/aallan/vera/issues/353) | Http: per-request timeout control. |
| [#356](https://github.com/aallan/vera/issues/356) | Http: PUT / PATCH / DELETE. |
| [#370](https://github.com/aallan/vera/issues/370) | Inference: configurable `max_tokens` / `temperature` — cost gates and deterministic replays. |
| [#372](https://github.com/aallan/vera/issues/372) | Inference: user-defined `handle[Inference]` handlers — mocking, caching, routing. |
| [#1467](https://github.com/aallan/vera/issues/1467) | `Decision` effect — typed probabilistic decisions from System One models: `noul` / `choice` / `score` return a value already in the type system with a `Confidence` refinement, a fast tier beside `Inference` so a function's effect row states what it may spend.  Userland first (a declared effect with a handler over `Http.post`), then a calibration measurement as a hard gate, then promotion to a built-in host effect mirroring `Http` and `DB` with the `async` whitelist entry; a batch `Decision.ask` and handler support follow, the latter decided with #372. |
| [#373](https://github.com/aallan/vera/issues/373) | Host-import `Array<Float64>` returns (`alloc_result_ok_float_array`) — the infrastructure #371 needs. |
| [#371](https://github.com/aallan/vera/issues/371) | `Inference.embed` — vector embeddings, unblocked by #373. |
| [#451](https://github.com/aallan/vera/issues/451) | Provider: Google Gemini. |
| [#1289](https://github.com/aallan/vera/issues/1289) | Provider registry — a model name reaches the toolchain as data rather than a compiler-source edit to `_PROVIDERS`. |
| [#380](https://github.com/aallan/vera/issues/380) | Example: handler mocking for Inference (unblocked by #372). |

## Stage 31 — The verified tool server

*The flagship: an MCP tool server whose tool schemas are compile-time guarantees.*

The thesis demo.  The `<HttpServer>` effect, the WASI Preview 2 target, and its `wasi:http` serve backend shipped in the server-effects sprint (Stage 16); Stage 30 hardens the effects it consumes.  What remains is the `<McpServer>` effect itself, the safety rails a server on untrusted input needs, and the small stdlib surface real tools keep reaching for.

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

## Stage 32 — The agent experience sprint

*The loop the model lives in.*

With the flagship standing, invest in the write–verify–fix loop agents actually experience: the language server's remaining seams, the context tools that keep a project inside a token budget, the discoverability surface, and the evidence base — this is where VeraBench's pass@k re-run lands, measuring whether all of the above moved the number.

Exit criterion: the LSP limitation rows are retired, and a fresh VeraBench run (pass@k, current models) is published.

| Issue | What |
|---|---|
| [#724](https://github.com/aallan/vera/issues/724) | LSP: buffer-aware module resolution (imports resolve from disk, not open buffers). |
| [#181](https://github.com/aallan/vera/issues/181) | Slot go-to-definition and mechanical slot-index rewriting beyond parameters (`let`/`match` bindings). |
| [#558](https://github.com/aallan/vera/issues/558) | `--explain-slots-at <line>:<col>` — query the slot table at any position, not only where a diagnostic already fires. |
| [#1292](https://github.com/aallan/vera/issues/1292) | LSP: `vera/addEffect` bounds handlers by resolved effect instance, so an alias-spelled `handle[State<MyAlias>]` prunes what `State<Int>` prunes. |
| [#1471](https://github.com/aallan/vera/issues/1471) | **E538** names the premise that contributes the contradiction (an unsat core over the author's premises), not the first `assume`. |
| [#523](https://github.com/aallan/vera/issues/523) | `vera context` — token-budgeted project export for agents. |
| [#698](https://github.com/aallan/vera/issues/698) | `vera shape` — function-archetype histograms per module. |
| [#224](https://github.com/aallan/vera/issues/224) | REPL — the shortest feedback path is `vera run` on a file. |
| [#562](https://github.com/aallan/vera/issues/562) | `vera test` advanced features — input shrinking, cross-function scenarios, coverage-guided generation. |
| [#143](https://github.com/aallan/vera/issues/143) | Expand to 50+ examples. |
| [#519](https://github.com/aallan/vera/issues/519) | SKILL.md documentation gap inventory. |
| [#424](https://github.com/aallan/vera/issues/424) | Register veralang.dev with llms.txt directories. |
| [#525](https://github.com/aallan/vera/issues/525) | Close the remaining Agent Score gaps on veralang.dev. |
| [#225](https://github.com/aallan/vera/issues/225) | VeraBench: pass@k evaluation, more models, more tiers — the sprint's measurement. |
| [#1139](https://github.com/aallan/vera/issues/1139) | Formatter internals: parse-time comment ownership and a single recursive renderer, making comment preservation and one-canonical-form structural properties rather than invariants spread across the emitters; retires the remaining relocation cases and the inline/multi-line dual paths. |

## Stage 33 — The browser sprint

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

**Nominal types** — [#1358](https://github.com/aallan/vera/issues/1358) `newtype`: nominal scalar types, checked at use (the issue carries the design, a validation plan and an estimate).

**Testing depth** — [#795](https://github.com/aallan/vera/issues/795) mutation testing beyond the soundness core (needs the full-sweep deadlock on mutmut 3.6 / Python 3.14 resolved first), [#792](https://github.com/aallan/vera/issues/792) feedback-driven hardening for the deep verifier/smt layers, [#170](https://github.com/aallan/vera/issues/170) Hypothesis as `vera test` generation backend (bookmark; trigger is sustained "cannot generate inputs" warnings).

**Concurrency and WASI** — [#406](https://github.com/aallan/vera/issues/406) WASI 0.3 native async (gated on wasmtime-py exposing component async), [#853](https://github.com/aallan/vera/issues/853) extend wasi-p2 beyond IO+Random (Http via `wasi:http` outgoing-handler, streaming filesystem, sockets), [#270](https://github.com/aallan/vera/issues/270) `handle[Async]` scheduling strategies, [#227](https://github.com/aallan/vera/issues/227) timeout/cancellation effects, [#228](https://github.com/aallan/vera/issues/228) WebSocket/SSE, [#770](https://github.com/aallan/vera/issues/770) non-blocking / timed stdin, [#844](https://github.com/aallan/vera/issues/844) advisory diagnostic for shape-unfusable `async` arguments.

**Modules and ecosystem** — [#127](https://github.com/aallan/vera/issues/127) module re-exports, [#130](https://github.com/aallan/vera/issues/130) package system and registry, [#163](https://github.com/aallan/vera/issues/163) standalone WASM runtime package, [#238](https://github.com/aallan/vera/issues/238) Component Model interop, [#56](https://github.com/aallan/vera/issues/56) incremental compilation, [#294](https://github.com/aallan/vera/issues/294) effect row variable unification, [#1469](https://github.com/aallan/vera/issues/1469) reserve the prelude ADT names uniformly, so a redefinition is refused at its declaration rather than where a use of it becomes ambiguous, [#785](https://github.com/aallan/vera/issues/785) GitHits MCP (bookmark; trial at the next dependency-facing milestone).

**Standard library long tail** — [#367](https://github.com/aallan/vera/issues/367) Markdown extractors, [#368](https://github.com/aallan/vera/issues/368) HTML accessors, [#507](https://github.com/aallan/vera/issues/507) ability-dispatched array operations, [#509](https://github.com/aallan/vera/issues/509) Unicode-aware string built-ins phase 2, [#1143](https://github.com/aallan/vera/issues/1143) `<DB>` effect phases 2–3 — named columns (via Map), typed rows (via JSON), and further backends.

**Compiler internals** — [#672](https://github.com/aallan/vera/issues/672) canonical WAT formatter, [#745](https://github.com/aallan/vera/issues/745) narrow the wrap-table / Phase 2c emission to `decimal_ops_used` only, [#739](https://github.com/aallan/vera/issues/739) typed `Protocol` interfaces for the mixin mypy carve-outs, [#1343](https://github.com/aallan/vera/issues/1343) decompose `vera/verifier.py` and `smt.py` around explicit obligation generators and translators — sequenced after the [#1344](https://github.com/aallan/vera/issues/1344) umbrella, whose typed registries the generators consume.

## Ongoing threads

Not stage-gated; advanced alongside whatever stage is active.

- **VeraBench** ([vera-bench](https://github.com/aallan/vera-bench)) — the suite is its own thread; the compiler-side pass@k re-run is staged as Stage 32's measurement ([#225](https://github.com/aallan/vera/issues/225)).
- **CI, process, and tooling** — [#386](https://github.com/aallan/vera/issues/386) Hypothesis round-trip properties (bookmark), [#712](https://github.com/aallan/vera/issues/712) Codecov → Harness migration watch, [#753](https://github.com/aallan/vera/issues/753) pygls / Python 3.16 watch, [#1126](https://github.com/aallan/vera/issues/1126) z3-solver 5.0 bake period, then re-run the obligation differential, [#1103](https://github.com/aallan/vera/issues/1103) migrate GitHub Pages off legacy branch-deploy to a self-owned Actions workflow, [#1295](https://github.com/aallan/vera/issues/1295) decide whether the four abilities (`Eq`/`Hash`/`Ord`/`Show`) highlight distinctly from ordinary types in the editor grammars, [#1263](https://github.com/aallan/vera/issues/1263) detect `_PROVIDERS` model IDs that a vendor has stopped documenting — every provider test pins the ID to a literal, which catches a registry edit but not rot at the vendor, so the signal needs a network-allowed probe.

## Not doing now

Deliberate trade-offs, recorded so they aren't re-litigated by accident.

- **No typed IR for WAT emission.**  The cost-benefit doesn't clear while string-based emission is held safe by the walker-completeness gate and the planned canonical WAT formatter ([#672](https://github.com/aallan/vera/issues/672)).
- **No parser fuzzing** ([#402](https://github.com/aallan/vera/issues/402), bookmark).  Trigger: a parser crash from the wild, or spare CI budget.
- **No full Tier 2 verification** ([#427](https://github.com/aallan/vera/issues/427)).  Its old blocker is gone — per-monomorphization verification shipped and provides the differential oracle — but the staged sprints above outrank it; it stays on the horizon by priority, not dependency.

## Speculative

Deferred decisions — features without a driver, captured so the design analysis isn't re-derived if one shows up.  Promotes into a stage when a real trigger appears.

| Item | Issue | Trigger condition |
|------|-------|-------------------|
| Allow `@Byte` arithmetic with verified underflow + overflow guards | [#564](https://github.com/aallan/vera/issues/564) | A real Vera program (or proposed feature) requires byte arithmetic at the user-code level — e.g., a binary-format parser the stdlib doesn't cover; or VeraBench shows a measurable adoption tax from `byte_to_int` round-trips on byte-heavy benchmarks.  The type checker excludes `Byte` from `NUMERIC_TYPES`, so `@Byte - @Byte` etc. produce E140; the round-trip via `byte_to_int` / `int_to_byte` is the canonical idiom. |
