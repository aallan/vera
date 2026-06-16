# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

## [0.0.172] - 2026-06-16

### Added

- **The `@Nat >= 0` invariant is now obligation-checked at binding sites** ([#552](https://github.com/aallan/vera/issues/552)).  Generalises the #520 subtraction obligation: a value narrowing from `@Int` into a `@Nat` slot carries a Tier-1 `value >= 0` proof obligation (`E503`) at `let` bindings, call arguments, effect-operation arguments (built-in `IO.sleep` and user-declared effects), constructor fields, top-level match binds, and literal-tuple destructures, discharged from preconditions and path conditions.  The pure-literal `let @Nat = 0 - 1` idiom the #520 obligation deliberately defers is now caught.  Codegen emits a runtime guard at the `let` site so programs compiled without `vera verify` still trap rather than store a negative `@Nat`.  At a non-`let` site a narrowing the solver cannot discharge has no runtime guard, so it surfaces an `E504` warning rather than being silently counted as runtime-covered.  Narrowing through ADT sub-pattern binds, non-literal destructures, generic-instantiated or imported constructor fields, and generic effect-operation formals (the projected source / call-site / module type is not statically resolved) is deferred to [#747](https://github.com/aallan/vera/issues/747); general refinement-predicate verification is [#746](https://github.com/aallan/vera/issues/746).

### Fixed

- **Verification counterexamples now witness the violation.**  `SmtContext.check_valid` extracted the Z3 model *after* popping the assertion scope, so the counterexample described the base context — `model_completion` filled the now-unconstrained slots with arbitrary defaults (e.g. `@Int.0 = 0` for the goal `@Int.0 >= 0`) instead of the violating assignment.  Extracting the model before the pop fixes `E502` (@Nat subtraction), `E503` (@Nat binding-site narrowing), and call-site precondition diagnostics alike.

## [0.0.171] - 2026-06-15

### Added

- **`peak_heap_bytes` on `ExecuteResult`** ([#706](https://github.com/aallan/vera/issues/706)) — the exported `$heap_ptr` bump high-water mark, read after execution (no new WAT).  The Map / Set reclamation tests now assert it grows ~O(N) across a 1 000- vs 10 000-element insert chain (≈6× with reclamation working; a leak would be ~O(N²) ≈100×), replacing the deleted Python-store-size assertion.  New `TestBucketOccupancy706` pins empty-string and Int-`0` keys plus empty-string Set elements through the occupancy flag.
- **Planning-document gates** ([#736](https://github.com/aallan/vera/issues/736)).  `check_doc_counts.py` now verifies the KNOWN_ISSUES.md "Refactoring needed" line counts against the measured files (±10% tolerance — the counts convey scale, and the gate trips into a re-cite rather than taxing every PR that touches a large file) and enforces the HISTORY.md version-row template (at most one issue link, no ` — ` separator per row).  `check_limitations_sync.py` now nets SKILL.md (Known Limitations + Known Bugs tables) and LSP_SERVER.md (limitations bullets converted to the standard table) alongside KNOWN_ISSUES.md, vera/README.md, and the spec chapters — and a configured section heading that goes missing now fails loudly instead of silently shrinking coverage, which surfaced the phantom spec §9.9 reference the script had been skipping since it was written: Chapter 9 now has a real Limitations section covering the Http, Inference, and missing-domain standard-library gaps.  17 new unit tests cover both checks.
- **Release process written down, split by audience** — CONTRIBUTING.md §Releases documents what a release-prep PR must contain (contributors don't cut releases); the maintainer-side mechanics (tag-after-merge ordering, the retag-demotes-release gotcha, the fold-in release pattern, the squash-vs-merge convention) live in CLAUDE.md's release-workflow section (manual until [#481](https://github.com/aallan/vera/issues/481) automates them).

### Changed

- **Map and Set host storage moved to bucket-as-truth across the CLI and browser runtimes** ([#706](https://github.com/aallan/vera/issues/706)).  The WASM-resident bucket array is now the sole source of truth for `Map<K, V>` and `Set<T>` contents on both runtimes; the Python-side `_map_store` / `_set_store` and the browser's `mapStore` / `setStore` are deleted.  Host imports take the wrapper pointer and read/write the bucket directly (8-byte header + 20-byte slots with an explicit occupancy flag), so there is no second copy that can silently drift — the audit's top architectural risk.  The compiled WASM shares one host-import contract, so codegen and both host runtimes migrate together.  Decimal stays value-typed on its Python store and keeps the wrap-table Phase 2c destructor; Map / Set wrappers are now plain heap objects reclaimed by ordinary mark-sweep, so `host_decref_handle` is Decimal-only.  The occupancy flag closes the empty-string-key / Int-`0`-key sentinel collision the old write-only mirror left latent (PR #707 review).
- **Power-of-two bucket capacity bounds copy-on-write heap usage** ([#706](https://github.com/aallan/vera/issues/706)).  Each persistent insert builds a fresh, larger bucket; a non-coalescing free list cannot reuse a freed size-N bucket for a size-(N+1) request, so the heap frontier climbed ~O(N²) regardless of GC — a 10 000-element insert chain peaked at 2.0 GB against the 2 GB heap ceiling.  Rounding capacity up to a power of two lets same-size-class inserts reuse freed buckets, dropping that chain's high-water mark to 3.0 MB (660×) and restoring ~O(N) growth.
- **ROADMAP.md rewritten around the June 2026 repo audit.**  The near-term plan is now four tiers ordered by the project's goal — close the silent failures, build the safety net, single-source the truth, then polish — with an explicit "Not doing now" section recording declined trade-offs, an "Ongoing threads" section (VeraBench leaves Milestone 1 to live there), and all four milestones rewritten.  Per-monomorphization generic verification ([#732](https://github.com/aallan/vera/issues/732)) is the chosen verification-depth path, with Tier 2 ([#427](https://github.com/aallan/vera/issues/427)) reframed as the Milestone 4 horizon upgrade that will use per-mono results as its differential oracle; the browser seam ([#609](https://github.com/aallan/vera/issues/609)/[#610](https://github.com/aallan/vera/issues/610)) is demoted below correctness work.  All 81 issue references in the old ROADMAP were explicitly re-homed (77 open issues) or consciously dropped (4 closed ones), and priority now lives in the ROADMAP tiers and nowhere else.
- **KNOWN_ISSUES.md normalized to two sentences per row** — every row in every section now states what the issue is and then its impact and path forward, no more and no less.  The 781-character browser-seam row split into per-issue [#609](https://github.com/aallan/vera/issues/609)/[#610](https://github.com/aallan/vera/issues/610) rows, the Refactoring-needed line counts were re-measured (19,570 / 5,939 / 4,253 — the old citations had drifted up to 2×), the Bugs table is documented as 1:1 with the open `bug`-labelled issues, and the new bug row for [#606](https://github.com/aallan/vera/issues/606) landed with it.
- **HISTORY.md re-staged and normalized.**  The two oversized stages split into four along their natural seams — standard-library depth (16–23 Apr), the bug-killing campaign (26 Apr – 8 May), stabilisation and memory safety (10–29 May), and the language server (10 Jun onwards) — with a stage index up top, every version row rewritten to one sentence with at most one issue link (76 of 173 rows violated the template), the parallel "Editor and tooling support" table folded into the stages it duplicated, and "By the numbers" extended with a current snapshot column.
- **Limitation wording re-synced from the canonical KNOWN_ISSUES rows** at every site: vera/README.md gains a verification-soundness row ([#552](https://github.com/aallan/vera/issues/552)/[#555](https://github.com/aallan/vera/issues/555)/[#730](https://github.com/aallan/vera/issues/730)) and splits its browser row; SKILL.md splits its browser row the same way; project-status counts (commits, releases, coverage) were re-measured everywhere they appear.

### Fixed

- **Host-side ADT result builders now root freshly-allocated heap payloads across the enclosing struct/array allocation** ([#706](https://github.com/aallan/vera/issues/706)).  The `Option` / `Result` / `Array<String>` constructors on both runtimes allocated a payload — a string, an `Array<String>` backing, or a freshly-built `Option` / `Json` / `HtmlNode` / `Decimal` / regex-match block — then the wrapping struct, and a garbage collection triggered by the second allocation could sweep the still-host-local pointer and store a dangling reference.  Surfaced under `VERA_EAGER_GC=1` or heap pressure (e.g. `map_get` on a `Map<K, String>`, `regex_find`, or `json_parse` returning a corrupted value).  A pre-existing gap the #692 / #695 rooting work left in these simpler builders; both runtimes now root via `_ShadowGuard` / a new JS `gcRooted` helper.  Surfaced by the CodeRabbit review.
- **`Float64` `Map` keys and `Set` elements compare under SameValueZero** ([#706](https://github.com/aallan/vera/issues/706)), so a `NaN` key/element round-trips (NaN equals NaN) and deduplicates.  The CLI Python dict and the browser `decodeColumn` comparison used `==` / `===`, which treat NaN as unequal to itself, so a NaN key could never be found, removed, or deduped — and `0.0 / 0.0` verifies and runs to NaN, so this was reachable.  Surfaced by the CodeRabbit review.

## [0.0.170] - 2026-06-12

### Fixed

- **[#727](https://github.com/aallan/vera/issues/727) — duplicate E501 diagnostics.**  A violating call site could be recorded once per translation pass: the primary body translation, the `@Nat`-subtraction walker's let-RHS environment rebuild, and the walker's operand discharge each re-translate the same call (a `@Nat`-subtraction operand in a `let` RHS recorded **three** identical E501s).  The SMT layer now dedups at recording time by (call node, precondition) identity, so every topology collapses to exactly one diagnostic and one `call_pre` obligation per violating site — while sites that only the walker ever translates — a violating call inside a `@Nat`-subtraction operand in statement position, checked via the walker's operand discharge — keep their single recording rather than being suppressed.  (Bare statement-position calls with no enclosing subtraction remain unchecked either way; that pre-existing gap is tracked as [#730](https://github.com/aallan/vera/issues/730).)  Translation behaviour is unchanged and the warm/cold differential oracle is untouched.
- **[#728](https://github.com/aallan/vera/issues/728) — LSP diagnostics now carry the full instruction contract.**  The language server's diagnostic mapping put only the description into the LSP message, so editor hovers said what broke but not how to fix it.  The message now appends the rationale paragraph and the `Fix:` paragraph exactly as `--json` carries them; diagnostics without those fields map to the bare description, unchanged.
- **E501 messages now speak in call-site terms.**  The precondition is rendered with the actual arguments substituted for the callee's parameter slots (`At this call site: string_length("") > 0`), and the `Fix:` text shows concrete code — the guard with the rendered call (`if string_length("") > 0 then { classify_sentiment("") } else { ... }`) and the exact `requires(...)` to add — instead of generic advice.  Substitution honours De Bruijn most-recent-first resolution; module-qualified callees and unmappable slots keep the generic wording.

## [0.0.169] - 2026-06-11

### Added

- **[LSP_SERVER.md](LSP_SERVER.md)** — the language server's user manual: what an LSP server is, install (`pip install -e ".[lsp]"`) and editor wiring, the standard feature surface (tier-annotated diagnostics, per-function verification-tier hints, hover, slot go-to-definition, typed-hole completion), the warm incremental verification core, and full request/response shapes for the four agent-facing custom methods (`vera/speculativeEdit`, `vera/proposeEdit`, `vera/strengthenContract`, `vera/addEffect`) with the typical speculate → inspect → propose loop.
- **VS Code extension 0.2.0** — the extension now starts `vera lsp` automatically for `.vera` files (settings `vera.lsp.enabled` / `vera.lsp.path`, command *Vera: Restart Language Server*), degrading gracefully to syntax-highlighting-only when the binary or the `npm install` is absent. Binary resolution prefers an explicit `vera.lsp.path`, then a workspace-local venv (`.venv/bin/vera` — GUI-launched VS Code does not inherit a shell `PATH`, so a from-source clone works with zero configuration), then `PATH`; spawn failure surfaces one warning with an Open Settings action. Requires VS Code 1.82+.

### Changed

- **veralang.dev** — the landing page's audience-addressed sections both gain the language server: §06 *Get Started* (the VS Code row starts `vera lsp` automatically; the `[lsp]` install path) and §07 *for machines*, reframed around read vs interrogate — the markdown set is how machines *read* Vera, the server is how they *interrogate* it, with a fourth agent-card and a `speculativeEdit` proof-delta sample.  `LSP_SERVER.md` is indexed in `llms.txt` and embedded in full in `llms-full.txt`.
- Documentation sweep after [#222](https://github.com/aallan/vera/issues/222): `vera lsp` joins the command lists in README/CLAUDE/AGENTS/SKILL; README's editor-support section, feature list, install notes, and project tree now cover the language server, `vera/obligations/`, and `vera/lsp/`; AGENTS.md gains an agent-facing section on the custom proof-delta methods; KNOWN_ISSUES drops the stale "LSP server" limitation row (shipped v0.0.161–v0.0.168) and gains three real ones — the single-file editor model ([#724](https://github.com/aallan/vera/issues/724)), parameter-only slot go-to-definition ([#181](https://github.com/aallan/vera/issues/181)), and handler-unaware `vera/addEffect` propagation ([#725](https://github.com/aallan/vera/issues/725)); `llms.txt` indexes LSP_SERVER.md; the compiler README module map's `lsp/` line count is corrected (a v0.0.168 update had silently failed); the release-count figures in README and the HISTORY footer now reflect the actual tag count (the v0.0.24.1 hotfix made releases = version + 1, uncounted since then).

## [0.0.168] - 2026-06-11

### Added

- **[#222](https://github.com/aallan/vera/issues/222) Phase F3 — `vera/addEffect`**, the multi-site workflow that completes the skill layer: `{uri, fn, effect}` computes the transitive-caller closure over the Phase B call walker (plain calls only — module-qualified calls never propagate across the file boundary), rewrites every affected `effects(...)` clause by span (`pure` → `<E>`; `<A>` → `<A, E>` appending after the original source verbatim; functions already naming the effect are skipped, with identity the base name before type arguments so `State<Int>` is not added next to `State<Bool>`), and runs ONE candidate through the proposeEdit pipeline.  The response lists `rewritten` functions in declaration order; a row state that is already satisfied short-circuits to the documented no-op shape without touching the verifier.  Propagation is handler-unaware by design — a caller that handles the effect in a `handle[E]` block is still rewritten; bounding the closure at handlers is noted as a refinement.  This closes the #222 LSP arc: the three skill-layer methods (`proposeEdit`, `strengthenContract`, `addEffect`) shipped in v0.0.166–v0.0.168 on the obligation core and proof-delta machinery from v0.0.161–v0.0.165.

## [0.0.167] - 2026-06-11

### Added

- **[#222](https://github.com/aallan/vera/issues/222) Phase F2 — `vera/strengthenContract`**, the contract-change workflow with a call-site audit: `{uri, fn, kind: requires|ensures, expr}` locates the first clause of that kind on the named top-level function, splices the new expression over the clause's span in the canonical document, and runs the candidate through the proposeEdit pipeline.  The audit is the proof delta itself — a tightened precondition some caller no longer satisfies surfaces as `newly_undischarged` `call_pre` items at the call sites (Phase A keys obligations by call-site span precisely for this) and the gate refuses; a strengthened postcondition the body proves discharges and applies.  No `force` parameter — the dedicated workflow exists to make the audited path the easy one (an agent that wants to push through a breaking change can construct the full text and call `vera/proposeEdit` with `force` explicitly).  Requests that cannot name a splice target (unknown function, unopened or unparseable document, bad `kind`) refuse with JSON-RPC InvalidParams at the boundary.

## [0.0.166] - 2026-06-11

### Added

- **[#222](https://github.com/aallan/vera/issues/222) Phase F1 — `vera/proposeEdit`**, the first skill-layer workflow: the whole edit → verify → apply sequence as one LSP method, so an agent cannot apply an unverified edit — applying *is* the final step of verifying.  The proposed text runs through the Phase E speculative verify; the gate applies it iff the proof delta has no `newly_undischarged` obligations and the proposed state has no error diagnostics (`force: true` overrides both, loudly — the delta still reports the damage).  On apply: a `workspace/applyEdit` request (the client owns the buffer, so the server round-trips the edit rather than silently diverging), the canonical `DocumentStore` updates, and diagnostics republish — the client's echoed `didChange` then replays from the warm discharge cache.  On refuse, canonical state is untouched, same isolation as `vera/speculativeEdit`.  New `vera/lsp/workflows.py` with the pure decision function separated from the effectful orchestration; ROADMAP regains a Phase F row while the reopened #222 is in flight.

## [0.0.165] - 2026-06-11

### Added

- **[#222](https://github.com/aallan/vera/issues/222) Phase E — `vera/speculativeEdit`**, the one custom LSP method and the reason the obligation core was built first: apply an edit in memory, re-verify on the warm incremental session, and return a `proof_delta` — `newly_discharged` / `newly_undischarged` / `timed_out` / `removed` / `unchanged`, each item carrying the obligation's function, kind, expression, position, and before/after status.  An agent proposing an edit learns whether it keeps, breaks, or strengthens the program's proofs before committing it.  Speculative runs share the warm session and discharge cache (pre-warming by design) under the same lock, but never touch the canonical per-URI analyses or published diagnostics.  Parse/type errors in the speculative state report `ok: false` with the error count.  This completes the #222 plan: Phases A (reified obligations + warm Z3), B (incremental invalidation + discharge cache), C (stdio transport + coordinate layer), D (diagnostics/hover/goto/completion), and E shipped across v0.0.161–v0.0.165; the "No LSP server" row leaves the compiler limitation table and the ROADMAP.

## [0.0.164] - 2026-06-10

### Added

- **[#222](https://github.com/aallan/vera/issues/222) Phase D** — `vera lsp` now serves language features over the obligation core: `publishDiagnostics` on open/change (parse, type-check, and verification diagnostics, plus a synthesised per-function verification-tier Hint — "Tier 1 — all contracts proven by Z3" / "Tier 3 — N of M obligations fall back to runtime checks" — computed from the obligation stream and suppressed for functions with violated obligations); hover showing the type of the smallest expression span under the cursor; go-to-definition on `@T.n` jumping to the parameter it names (De Bruijn most-recent-first via `slots.slot_table`; references binding through `let`/`match` return no definition — signature-level scope, with full binding resolution tracked by [#181](https://github.com/aallan/vera/issues/181)); and typed-hole completion listing the in-scope bindings with their types.  All verification is serialised through one warm `VerificationSession` under a lock.  The checker gains opt-in artifact collection (`typecheck_with_artifacts`: a `Span`→type side-table recorded by a thin `_synth_expr` wrapper, and structured `HoleSite` records factored out of the W001 hole diagnostic) at zero cost to existing callers.  `Diagnostic` gains an optional `tier` field (surfaced in `--json` only when set); the verifier's six Tier-3 fallback warnings (E520–E525) now carry `tier=3`.

## [0.0.163] - 2026-06-10

### Added

- **[#222](https://github.com/aallan/vera/issues/222) Phase C** — `vera lsp` serves the Language Server Protocol over stdio: handshake with `serverInfo`, full-text document sync into an in-memory `DocumentStore` (the source of truth for open files — features never read disk), and the coordinate-conversion layer in `vera/lsp/convert.py` where the three coordinate systems meet (Vera `Span`: 1-based line + 1-based code-point column with exclusive end; `SourceLocation`: 1-based line but 0-based column; LSP: 0-based line + UTF-16 code units, with astral-plane transcoding and surrogate-pair snapping per the spec).  Deliberately featureless — Phase D wires diagnostics/hover/completion onto this transport so the advertised capability surface never promises something unimplemented.  The transport dependencies live in a new optional `[lsp]` extra (`pygls>=2.0`, `lsprotocol`; both pure-Python, mirrored into `[dev]` for CI) so the base install is unchanged; `vera lsp` without the extra prints an actionable install message.

## [0.0.162] - 2026-06-10

### Added

- **[#222](https://github.com/aallan/vera/issues/222) Phase B** — incremental verification: `VerificationSession` now caches each top-level function's verification output (obligations, diagnostics, summary deltas) under an invalidation key covering everything its verification reads, and replays unchanged functions instead of re-entering Z3.  The soundness model (documented in the new `vera/obligations/cache.py`): a callee *contract or signature* change invalidates its callers (call sites check preconditions and assume postconditions); a callee *body* change does not (bodies are never read across the call boundary); span shifts, ADT / type-alias / effect / import / timeout changes invalidate conservatively.  Functions whose output contains a solver-timeout obligation are never cached.  `SessionRunStats` (replayed vs verified counts) added for cache observability.  Pinned by the corpus-wide differential oracle (replay == re-verify == cold `verify()` across all 35 examples and every verify/run-level conformance program) plus targeted invalidation-rule tests, including a span-shift test that caught the structural hash being position-blind (`Node.span` is `repr=False`) before it shipped.

## [0.0.161] - 2026-06-10

### Added

- **[#222](https://github.com/aallan/vera/issues/222) Phase A** — proof obligations are now first-class: new `vera/obligations/` package with a `ProofObligation` record (owning function, kind, expression text, source span, stable `content_key()` digest, discharge outcome with counterexample) and a `VerificationSession` daemon that re-verifies full programs on one long-lived Z3 solver via the previously-unused `SmtContext.reset()` warm path.  `VerifyResult` gains an `obligations` field (default-empty, source-compatible); `ContractVerifier` gains a `shared_smt` hook (the cold path is unchanged: fresh context per function).  Obligation kinds cover `requires` / `ensures` / `decreases` / `@Nat`-subtraction sites / call-site preconditions (the latter recorded on violation only in Phase A — successful call-site checks discharge inside the SMT layer and are enumerated in Phase B).  Reification is observational: records are created at the existing discharge sites in discharge order, never altering solver state.  Behaviour is pinned by a 250-test differential oracle (`tests/test_obligations.py`): warm session == cold `verify()` on diagnostics, summary, and the obligation stream — plus warm-twice determinism — across all 35 examples and every verify/run-level conformance program.  This is the semantic core the #222 LSP server builds on; Phase B (incremental invalidation + discharge cache) slots in behind the same API.

### Fixed

- **`SmtContext.reset()` warm-reuse staleness** — `reset()` (previously dead code) kept `_length_fns` / `_index_fns` / `_array_element_sorts` / `_path_conditions` across solver resets.  `get_rank_fn` asserts its `ForAll rank(x) >= 0` axiom only at dict-miss, so a surviving cache entry after `solver.reset()` silently skipped re-asserting the axiom and ADT-measure `decreases` checks would diverge from a fresh context.  `reset()` now clears all four (re-seeding the `Int` length function) and re-applies the solver timeout.  Latent-only before this release — nothing called `reset()`; the new warm session is its first caller, and the differential oracle now pins the equivalence.

### Security

- **[#712](https://github.com/aallan/vera/issues/712)** — SHA-pinned `codecov/codecov-action` to a commit (`e79a696` = v6.0.1) instead of the floating `@v6` tag, as targeted supply-chain hardening following the Codecov → Harness acquisition (announced 2026-06-02).  An ownership change is the canonical scenario where a major-version tag could be repointed by the new owner and silently flow into CI; pinning to a reviewed commit closes that, while Dependabot continues to propose bumps under review.  Coverage is unaffected either way — the 80% gate is the on-runner `pytest --cov-fail-under=80` and the upload is `fail_ci_if_error: false`.  Also corrected a stale `SECURITY.md` cross-reference that attributed action SHA-pinning to #390 (a closed Python dependency-lockfile issue).

## [0.0.160] - 2026-05-29

### Changed

- **[#599](https://github.com/aallan/vera/issues/599)** — bumped the `wasmtime` floor from `>=44.0.0` to `>=45.0.0`.  45.0.0 (released 2026-05-26) is the first PyPI release whose host-import trampoline catches `BaseException` rather than `Exception` ([bytecodealliance/wasmtime-py#337](https://github.com/bytecodealliance/wasmtime-py/pull/337), merged 2026-05-07 — the 44.0.0 tag predates it).  Vera filed the upstream issue ([#336](https://github.com/bytecodealliance/wasmtime-py/issues/336)) after a Ctrl-C during `IO.sleep` in a Conway's Life animation aborted with a libmalloc SIGABRT ([#595](https://github.com/aallan/vera/issues/595)): a raw `KeyboardInterrupt` (a `BaseException`) escaped the `except Exception` trampoline into Rust with an undefined ABI return value.  45.0.0 makes the raw propagation safe — the wasm call unwinds and the original `KeyboardInterrupt` re-raises in Python at the call site.

### Removed

- **[#599](https://github.com/aallan/vera/issues/599) / [#595](https://github.com/aallan/vera/issues/595)** — removed the four per-host-import `except KeyboardInterrupt: raise _VeraExit(130)` workaround guards (one in `host_sleep`, three across `host_read_char`'s Unix-non-TTY / Unix-TTY-cbreak / Windows-getwch branches).  These laundered `KeyboardInterrupt` into `_VeraExit` (an `Exception`) so the pre-45 buggy trampoline would catch it.  With `wasmtime>=45.0.0` the launder is unnecessary: a single `except KeyboardInterrupt` handler at the `func(store, ...)` call site in `execute()` now maps a Ctrl-C in any host import to the conventional SIGINT exit code (130), preserving captured stdout/stderr/state exactly as the `IO.exit` path does.  One source of truth replaces four duplicated guards.  The Unix-TTY path's terminal restore stays correct — it lives in a `finally`, so the terminal is returned to canonical mode before the interrupt propagates.  Net behaviour is unchanged (clean exit 130, pre-interrupt output preserved); the end-to-end test that pins this contract passes identically before and after the relocation.

## [0.0.159] - 2026-05-28

### Fixed

- **[#695](https://github.com/aallan/vera/issues/695) and [#705](https://github.com/aallan/vera/issues/705)** — closed the silent use-after-free in `Map<K, T_heap>` and `Set<T_heap>` where heap-pointer values stored in Python-side `_map_store` / `_set_store` were invisible to the conservative GC scan.  Fix: every `Map` / `Set` wrapper now points (at body offset +8) to a WASM-resident bucket array that mirrors the store's (key, value) pairs as i32 slot words.  The conservative scan reaches the values via shadow stack → wrapper → bucket → val_ptr, so a `$gc_collect` between map / set construction and value access no longer reclaims the heap blocks.  Bucket population happens in three paths: the WAT-emitted `attach_bucket_to_wrapper` import (dispatching to `host_attach_bucket` for both CLI and browser targets), the host-side `_alloc_map_wrapper` (used by `write_json`'s `JObject` branch and `write_html`'s `HtmlElement` attrs), and match-arm / let-binding shadow-rooting for heap-pointer bindings in `vera/wasm/data.py` and `vera/wasm/context.py` (the orthogonal #695-root cause: parameter shadow-pushing already covered function calls, but `match` and `let` binding sites did not).  Decimal wrappers stay exempt — `PyDecimal` is value-typed and cannot contain heap pointers.  This is the **mirror** approach: the Python store remains the source of truth and the bucket array is a write-only reachability anchor.  Follow-up [#706](https://github.com/aallan/vera/issues/706) tracks the architectural "move" cleanup (single source of truth in the bucket array, deleting `_map_store` / `_set_store`, across CLI Map / CLI Set / browser runtime).
- **[#708](https://github.com/aallan/vera/issues/708)** — closed the browser-runtime parallel of the #692 silent-UAF in `vera/browser/runtime.mjs`'s `writeJson` / `writeHtml` walkers.  Surfaced by the new browser-side EAGER_GC regression tests added in this PR: `writeJson` allocates a tree of `Json` heap blocks via repeated `alloc()` and JS-local pointer holding, but never shadow-pushed intermediates (`arrPtr` for a `JArray`'s backing, recursive child results, string ptrs) — so under `VERA_EAGER_GC=1` each subsequent alloc fires `$gc_collect`, reclaims the in-progress tree, and the writes scribble freed memory.  Empirically the constructed `JArray`'s body ended up with `tag=0` (JNull) and `payload=self` (looked like `Result.Ok(self)`) — a `Result.Ok` shape allocated on the same address after `JArray` got reclaimed.  Fix: added JS-side `gcGuard(fn)` helper that mirrors the CLI `_ShadowGuard` discipline (save `$gc_sp` at entry, restore on exit), and `gcShadowPush` for each intermediate in `writeJson`'s JString / JArray / JObject branches, `writeHtml`'s comment / text / element branches, `json_parse`, and `html_parse`.  The CLI side already had this fix from v0.0.158 (#692); the browser side was missing it, exposing the latent bug at higher GC pressure.
- **[#694](https://github.com/aallan/vera/issues/694)** — bumped the `subprocess.run` timeout in `tests/test_browser.py` from 30s to 60s at both call sites.  The previous 30s budget was insufficient for cold Node startup on Windows GitHub Actions runners when combined with the `--experimental-wasm-exnref` flag's first-execution V8 codegen cost.  Symptom was an intermittent `subprocess.TimeoutExpired` on `test (windows-latest, 3.12)` only, asymmetric across the matrix — `3.11` and `3.13` running back-to-back on the same runner benefited from a warm cache.  60s gives ~2× the median budget without making real hangs painful to detect.

### Changed

- **[#691](https://github.com/aallan/vera/issues/691)** — Supported platforms are now documented explicitly in `README.md` Installation: macOS 15+ (Sequoia, Tahoe), Ubuntu x86_64 (manylinux_2_27+), Ubuntu aarch64 (manylinux_2_38+, i.e. Ubuntu 23.10+), Windows x86_64.  The macOS 15+ baseline reflects [TelemetryDeck distribution data](https://telemetrydeck.com/survey/apple/macOS/versions/) — macOS 26 (~75%) + macOS 15 (~24%) covers ~99% of the install base.  macOS 14 (Sonoma) and earlier are out of scope ([#691](https://github.com/aallan/vera/issues/691)); Ubuntu 22.04 LTS aarch64 is out of scope ([#701](https://github.com/aallan/vera/issues/701)).
- **CI matrix**: replaced `macos-latest` with explicit pins for `macos-15` and `macos-26` (12 test combinations total).  Insulates against silent `-latest` migration when GitHub flips the alias.  First repo run on macOS 26 (Tahoe).
- **`z3-solver` lower bound** tightened from `>=4.12` to `>=4.15.5`.  Expresses the macOS 15+ baseline structurally — unsupported platforms now fail at dependency resolution with a clear "no matching distribution" error instead of a cryptic source-build failure 20 minutes later.  Resolved version stays at 4.16.0.0 (no functional change).

### Added

- **`scripts/check_wheel_availability.py`** — pre-flight check that every runtime dep has prebuilt wheels for every (platform, Python-version) tuple documented in README §Supported platforms.  Runs as the new `wheel-preflight` CI job.  Structural backstop for #691-class install regressions: catches upstream platform-tag bumps before they reach users.

## [0.0.158] - 2026-05-19

### Fixed

- **[#692](https://github.com/aallan/vera/issues/692)** — `html_parse`, `json_parse`, and `md_parse` no longer trap with `Out-of-bounds memory access` on inputs large enough to pressure GC during host-side tree marshalling.  Root cause: missing-shadow-stack rooting in `vera/wasm/html_serde.py::write_html`, `vera/wasm/json_serde.py::write_json`, and `vera/wasm/markdown.py::write_md_block`/`write_md_inline` — same #570 / #515 / #593 bug class but on the host side rather than WAT-emitted user code.  The Python-held intermediate pointers (`arr_ptr` / `name_ptr` / `wrapper_ptr`) were invisible to the conservative GC scan; if a sub-walk triggered `$gc_collect`, those blocks were reclaimed and subsequent writes corrupted the free list (concrete trap signature: out-of-bounds access at `0xfffffffd` from inside `$alloc`'s free-list traversal).  Externally reported with a `summarise_urls` example that ran `html_parse` over the current `FAQ.md` body; same shape proven empirically in `write_json` (large nested JArray) and `write_md_block` (many headings).

### Added

- **`$gc_sp` and `$gc_stack_limit` are now exported** from the emitted WAT module, allowing host imports to read and advance the GC shadow stack pointer.  Inline export syntax on the globals; the existing WAT-side push helper (`gc_shadow_push` in `vera/wasm/helpers.py`) continues to work unchanged for user-code pushes.
- **`_ShadowGuard` context manager** in `vera/codegen/api.py` — exception-safe push/pop discipline for host walkers.  On `__enter__` snapshots `$gc_sp`; on `__exit__` resets it to the snapshot (atomically pops every push from the block, on both success and exception paths).  Used by `host_html_parse`, `host_html_query`, `host_json_parse`, and `host_md_parse` to root intermediate WASM heap pointers across sub-tree recursion and the final Result wrapper alloc.
- **Field-allocation-then-body-allocation convention** applied throughout `markdown.py` — every match arm now allocates its field contents first (rooting via the guard), then allocates the body last.  This eliminates the secondary bug shape where the body pointer would be held in a Python local across a subsequent string or array allocation.

### Tests

- New `tests/conformance/ch09_host_walker_gc_rooting.vera` (run-level, 4 sub-tests) pinning post-fix behaviour for `html_parse` (500 element siblings), `json_parse` (1000-element number array, 500-element string array), and `md_parse` (200 H1 + paragraph blocks).  All sizes selected to provoke real heap growth and multiple `$gc_collect` cycles during the walk while staying under Python's default recursion limit on tear-down paths.
- New `tests/test_codegen.py::TestHostWalkerGCRooting692` (6 tests) — in-process regression for the same scenarios at the codegen layer, alongside the existing host-side GC-rooting regression classes for #570 / #515 / #593.  Two extra tests added per the pr-review-toolkit pr-test-analyzer review: `test_html_query_30_matches` covers the `host_html_query` `_ShadowGuard` path (re-walks each matched subtree via `write_html` in a single guard window), and `test_json_parse_500_key_object` covers the JObject branch of `write_json` (the val_ptr-pushed-per-iteration pattern that motivated the whole fix).

### Documentation

- Structural test in `test_codegen.py::TestWorklistOverflow348` updated to match the new `(global $gc_stack_limit (export "gc_stack_limit") ...)` WAT shape.

### Fixed (post-review)

- **PR #693 CodeRabbit findings** (commit `4b8c127`): narrowed `host_md_parse`'s broad `except Exception` to wrap only the parse step — shadow-stack work and `write_md_block` now sit outside, so host-side invariant violations propagate as wasmtime traps.  Removed redundant `guard.push(arr_ptr)` calls in markdown walkers after `_write_inline_array` / `_write_block_array` / `_write_array_of_block_arrays` / `_write_table_data` (the helpers already root their backing internally; the duplicate pushes were doubling shadow-stack consumption).  TESTING.md L193 count: `435 → 440`.  Added `#694` (Windows test_browser timeout flake) to `KNOWN_ISSUES.md` per the PR-generated-new-issues-must-be-tracked rule.
- **PR #693 pr-review-toolkit findings**: same parse-only-in-try restructure applied to `host_html_parse` — the previous round had narrowed `host_md_parse` but left `host_html_parse`'s `_ShadowGuard` block inside its narrow `except (ValueError, TypeError, AttributeError)`, contradicting the in-file comment that claimed the catch matched `host_json_parse`.  Now all three host walkers structurally match: parse-only-in-try, shadow-stack work outside.  `_ShadowGuard.__init__` re-raises a missing-export `KeyError` as a clearer `RuntimeError` naming `$gc_sp` / `$gc_stack_limit` and `#692` — diagnostic-quality fix for hand-crafted-WAT scenarios.  `_ShadowGuard.__exit__` `if self._initial_sp is not None` guard tightened to an `assert` (the only way the None case is reachable is misuse of the context manager outside a `with` block; the assert pins the invariant).  Misleading `host_html_query` comment about "WASM codegen at the call site shadow-pushes via the standard mechanism" softened — the codegen does shadow-push the consuming local, but the guard's protection doesn't extend past the function boundary.  Added rooting-contract docstrings to all four markdown array helpers (`_write_inline_array`, `_write_block_array`, `_write_array_of_block_arrays`, `_write_table_data`) so future maintainers see the convention from the function signature.  Added an exception-safety note to `write_json`'s JObject branch documenting why `map_dict` partial state is safe to discard on mid-loop raise (function exits via the raise before `map_alloc` is called).  Documented the markdown helpers' `alloc-then-push` allocation order intent (a future "fix" must NOT try to push before alloc or wrap the push in try/except — both would break the trap-on-overflow invariant).

## [0.0.157] - 2026-05-19

### Added

- **[#618](https://github.com/aallan/vera/issues/618)** — new `IO.read_char` effect operation for single-character input.  Signature: `op read_char(Unit -> @Result<String, String>)`.  Returns one Unicode character from stdin, or `Err("EOF")` when the stream closes (Ctrl-D on a Unix TTY also maps to EOF).  Terminal target uses termios cbreak mode via `tty.setcbreak()` (Unix TTY — cbreak preserves ISIG so Ctrl-C still raises SIGINT, unlike raw mode which would suppress it), `msvcrt.getwch()` (Windows TTY), or buffered `sys.stdin.read(1)` (piped/redirected stdin on either platform).  Browser target returns `Result.Err` pending JSPI suspend/resume (depends on [#609](https://github.com/aallan/vera/issues/609); same primitive `IO.sleep` will use).  Unblocks real-time CLI programs (paced REPLs, terminal games) that couldn't be written before because `IO.read_line` is line-buffered.  Added per the same `IO`-effect-extension pattern as `IO.sleep` / `IO.time` / `IO.stderr` ([#463](https://github.com/aallan/vera/issues/463)): a single new op on the existing effect, not a new `<Terminal>` effect.

### Tests

- New `tests/conformance/ch07_io_read_char.vera` (verify-level — pins the type signature and effect-row wiring).  New `tests/test_cli.py::TestIOOperations::test_run_io_read_char_piped_input` / `test_run_io_read_char_eof` / `test_run_io_read_char_utf8` covering the piped-input path (no termios needed), EOF handling, and multi-byte UTF-8 round-trip (`sys.stdin.read(1)` returns one Unicode character, not one byte).

### Documentation

- `spec/07-effects.md` — added `read_char` row to the IO operation table; bumped IO operation count "ten → eleven" in the section intro.
- `spec/12-runtime.md` — added `vera.read_char` import row and the browser-runtime IO behaviour table entry.
- `SKILL.md` — added `IO.read_char` row to the IO operations table; updated the browser-runtime summary sentence to mention the pending JSPI dependency; bumped IO operation count "ten → eleven" in two places.
- `examples/read_char.vera` — new example demonstrating the read-one-char pattern with full failure-mode handling.
- `TESTING.md` — finished the 34→35 example-count sweep across six remaining call sites (validation-script comment, verification-coverage section, slot-feature row, round-trip section, validation-scripts table, pre-commit-hooks table) — caught by CodeRabbit on PR #689 after the initial header-row update.

### Fixed (post-review)

- **PR #689 CodeRabbit findings (round 1)**: wrapped `sys.stdin.fileno()` / `sys.stdin.read(1)` / `termios.tcgetattr` / `tty.setraw` / `termios.tcsetattr` in `except Exception` blocks in `host_read_char` so system errors (closed stdin, monkey-patched stream without `fileno()`, `termios.error` on weird devices) become `Result.Err` rather than propagating as wasmtime traps.  `Exception` excludes `KeyboardInterrupt` and `SystemExit` (direct `BaseException` subclasses), so Ctrl-C still terminates interactive prompts — same stance as `host_sleep`.  Added explicit `encoding="utf-8"` to the three new `subprocess.run` calls in `test_cli.py` (matches CLAUDE.md cross-platform pitfalls section: CI sets `PYTHONUTF8=1` as a backstop, but the explicit form is portable to local Windows shells without that variable).
- **PR #689 CodeRabbit findings (round 4)**: two final clean-ups.
  - **Important**: Unix TTY cbreak mode now maps `\x04` (Ctrl-D / ASCII EOT) to `Err("EOF")`.  Without this mapping, a user pressing Ctrl-D in a real-time CLI program would get `Ok("\x04")` and the program would have to know to interpret the literal byte as end-of-input — surprising and platform-specific (cbreak disables ICANON, which is what normally turns Ctrl-D-at-start-of-line into an empty read in canonical mode).  Now Ctrl-D produces the expected EOF semantics in cbreak mode.  The mapping is restricted to the Unix TTY cbreak branch only — piped `\x04` on the non-TTY shared path stays a literal byte (a pipe is a byte stream, the producer chose to include `\x04`), and the Windows `msvcrt.getwch()` branch has its own end-of-input convention (Ctrl-Z `\x1A`) which is left untouched for now.  New regression test pins the non-TTY asymmetry.
  - **Documentation**: CHANGELOG entry for #618 now says "termios cbreak mode via `tty.setcbreak()`" with the ISIG-preservation rationale, rather than the stale "termios raw-mode" wording that survived from before the round-3 fix.
- **PR #689 CodeRabbit findings (round 3)**: caught two more correctness bugs that the previous rounds (CodeRabbit ×2 + internal multi-agent review) missed.
  - **Critical**: `tty.setraw()` clears the termios `ISIG` flag, which suppresses SIGINT generation — meaning the `except KeyboardInterrupt` clause added in the previous round was actually **unreachable** in TTY mode.  Ctrl-C would arrive in the read buffer as the literal byte `\x03` instead of raising `KeyboardInterrupt`, so a Tetris-style game would receive `\x03` as input and the user could never exit the program.  Switched to `tty.setcbreak()`, which disables ICANON + ECHO (still gets one character without waiting for Enter and without echoing) but PRESERVES ISIG, so Ctrl-C → SIGINT → `KeyboardInterrupt` → `_VeraExit(130)` works as intended.  Verified empirically that `cfmakecbreak` keeps the ISIG bit set while `cfmakeraw` clears it.
  - **Important**: termios restore failure no longer silently swallowed.  The previous round wrapped the `tcsetattr(...)` call inside the inner `finally` in a bare `except Exception: pass`, which surfaced the read error correctly but lost the restore error entirely.  Now captures the restore exception into a local `restore_exc` variable: if the read itself failed, the read error wins (more actionable); if the read succeeded but restore failed, surfaces a distinct "raw-mode restore failed: ..." error; if both failed, the read error still wins.  No silent failures from this path now.
- **PR #689 pr-review findings (round 3, internal multi-agent review)**: caught two correctness bugs and three quality issues that CodeRabbit missed.
  - **Critical**: `host_read_char` no longer lets `KeyboardInterrupt` escape through the wasmtime trampoline.  Each blocking call (`sys.stdin.read(1)` in both branches, `msvcrt.getwch()` on Windows) now catches `KeyboardInterrupt` and raises `_VeraExit(130)` — the same fix `host_sleep` already applies for the same reason (#589-class WasmTrapError contract violation when a raw Python `KeyboardInterrupt` unwinds through the host import).  The prior comment claimed parity with `host_sleep`'s "let it propagate" stance, but `host_sleep` actually *catches* `KeyboardInterrupt`; the comment was factually wrong and the missing catch was a real bug.  User-facing behaviour is unchanged: Ctrl-C still terminates the program with exit code 130.
  - **Important**: termios restore failure can no longer silently mask the original read error.  The `tcsetattr` call in the inner `finally` is now wrapped in its own `try/except` — if restore fails (rare; same fd just worked) the terminal stays in raw mode but the original read error still surfaces, which is more useful for debugging.
  - **Important**: `tcgetattr` failure now reports a distinct error message ("tcgetattr failed: ...") rather than the misleading "raw-mode read failed: ..." — raw mode never started in that case.
  - **Minor**: removed a redundant local `import os` inside `host_read_char` (`os` is already imported at module level).
  - **Minor**: fixed a stale cross-reference in `tests/conformance/ch07_io_read_char.vera`'s header comment (pointed at `tests/test_codegen.py` instead of `tests/test_cli.py`).
- **PR #689 pr-review findings (test coverage)**: added 5 new `execute(stdin=...)` tests in `test_codegen.py::TestIOOperations` covering the `stdin_buf` fixture path that subprocess-based tests can't reach: single-character read, empty-buf EOF, sequential reads advance cursor, read-then-EOF, and 2-byte UTF-8 round-trip (platform-independent — no reliance on host stdin encoding).  Tightened the three existing `test_cli.py` `read_char` tests: `result.stdout.rstrip() == "<expected>"` rather than substring `in`, plus `assert result.stderr == ""` (catches a class of regression where a future host accidentally prints to stderr on the way to a clean exit).
- **PR #689 CodeRabbit findings (round 2)**: lifted the `os.isatty(fd)` check above the platform fork in `host_read_char`.  Previously the Windows branch went straight to `msvcrt.getwch()` regardless of whether stdin was a real console or a redirected pipe.  `msvcrt.getwch()` technically works on redirected stdin via Win32's `_getch` fallback but decodes raw bytes rather than honouring Python's stdin encoding, so a piped `é` would round-trip differently from the Unix path.  Now the non-TTY (pipe/redirect) branch is shared across platforms: both use `sys.stdin.read(1)` for identical encoding behaviour.  Only TTY stdin goes through `msvcrt.getwch()` (Windows) or termios raw mode (Unix).  Also wrapped `msvcrt.getwch()` in `except Exception` for symmetry with the Unix path's defensive handling, and finished a stale 86→87 sweep in TESTING.md (L92 conformance suite description, L193 parametrized test count) + ROADMAP.md (#679 row description).

## [0.0.156] - 2026-05-19

### Added

- **`TestSummary.unlisted_errors: int`** — new field on the `vera.tester.TestSummary` dataclass that counts verifier-error diagnostics whose attributable function isn't in the displayed `functions` list.  This happens when `--fn` filters to a subset, or when a private helper fails verification (private functions aren't displayed by `vera test`).  Exposed in `vera test --json` output under `summary.unlisted_errors` so downstream CI consumers can read the structured count instead of re-running regex attribution against the diagnostics array.  Introduced as part of [#674](https://github.com/aallan/vera/issues/674)'s fix to keep `vera/cli.py` purely presentational — the engine is the source of truth for attribution, `cli.py` reads structured fields.

### Fixed

- **[#675](https://github.com/aallan/vera/issues/675)** — E500 (`Postcondition does not hold`) `fix=` text now names all three repair classes neutrally, with implementation-repair first.  Pre-fix the text named only two classes (strengthen `requires(...)`, weaken `ensures(...)`) — implicitly biasing the user away from the most common repair when E500 catches a typo in the function body.  External report from @rzyns.  Tightened `tests/test_verifier.py::TestCounterexamples::test_violation_has_fix_suggestion` to pin all three classes (pre-existing assertion would have survived the rewrite without catching a regression dropping "implementation").

- **[#674](https://github.com/aallan/vera/issues/674)** — `vera test` now fails closed when the verifier reports E500/E501/E502 diagnostics instead of treating verifier-refuted contracts as successful Tier 1 results.  JSON output now sets `ok: false`, preserves the verifier diagnostics, and exits non-zero; human output displays failed functions and a diagnostics section so verifier failures cannot be hidden behind green rows.
  - `E501` call-site precondition failures are attributed to the caller rather than the callee, while `E500` postcondition failures and `E502` `@Nat` subtraction underflow diagnostics are attributed to their responsible function.
  - `--fn` keeps function rows filtered to the selected target, but whole-file verifier errors still fail closed and remain visible in diagnostics; private/non-displayed verifier failures likewise surface as unlisted verifier errors instead of disappearing.
  - Human summaries distinguish static verifier failures from Tier 3 runtime trial failures, keep E700 runtime contract violations out of verifier-error counts, and avoid double-counting multiple verifier diagnostics already represented by a displayed failed function.

### Tests

- Added regression coverage for `vera test` verifier-error handling across JSON and human output, private helper failures, `--fn` filtering, E501 caller attribution, E502 underflow attribution, mixed static/Tier 3 summaries, E700 runtime failures, multiple diagnostics on one failed function, and CLI dispatch return codes.

### Documentation

- **Docs sweep addressing 2026-05-18 compiler-review findings** ([PR #684](https://github.com/aallan/vera/pull/684)) —
  - `README.md` "Contracts the compiler proves" section reworded — the previous unqualified claim ("Division by zero is not a runtime error — it is a type error.  The compiler checks every call site to prove the divisor is non-zero.") overclaimed; the verifier checks contracts the programmer wrote, not auto-synthesised obligations on primitives.  New wording correctly describes static-vs-runtime split with forward reference to [#680](https://github.com/aallan/vera/issues/680) (auto-injection follow-up).
  - `FAQ.md` — new Q&A "Does the compiler prove division-by-zero, out-of-bounds indexing, etc. can't happen?" walking through the static/runtime split.
  - `spec/06-contracts.md` — new §6.4.3 "Primitive Operation Safety" between Call Site Verification and SMT Solver Integration.  Subsequent sections renumbered.  States explicitly that obligations on `a / b`, `a % b`, `arr[i]`, `string_at(s, i)` are not auto-synthesised; `@Nat` subtraction ([#520](https://github.com/aallan/vera/issues/520)) is the one exception today.
  - `KNOWN_ISSUES.md` — PR #684 restored the [#674](https://github.com/aallan/vera/issues/674) bug row with the external report from @rzyns and duplicate #681 provenance; this fixing PR removes that row because `vera test` now fails closed on verifier-refuted contracts.
  - `ROADMAP.md` — four new tracking items: [#679](https://github.com/aallan/vera/issues/679) (Ch 8 conformance gap), [#680](https://github.com/aallan/vera/issues/680) (auto-inject primitive obligations, cross-referenced from #427), [#682](https://github.com/aallan/vera/issues/682) (diagnostic-tagging discipline), [#683](https://github.com/aallan/vera/issues/683) (spec/Lark grammar nominal drift).

## [0.0.155] - 2026-05-13

### Fixed

- **[#578](https://github.com/aallan/vera/issues/578)** — wrapper-handle bit-31 tagging closes the last latent conservative-GC retention bug.  Pre-fix, `Map<K, V>` / `Set<T>` / `Decimal` wrapper ADTs stored their raw host-store handle as an i32 at body offset 4.  Phase 2b of `$gc_collect` does a conservative word-by-word scan of every reachable object's payload, checking each i32 against the heap-range predicate (`val >= gc_heap_start + 4 && val < heap_ptr && (val - gc_heap_start) & 7 == 4`).  For typical programs the handle counter stays well below `gc_heap_start` (~147 KiB) so the heap-range check rejects it, but a long-running program allocating >100K host-store entries in a single `execute()` call could see a handle exceed that threshold and (with the right alignment) be falsely classified as a heap pointer — silently retaining an unrelated heap object.  Retention bug, not correctness (no use-after-free, no corruption), but unbounded retention for long sessions.
  - **Fix**: store the handle ORed with `0x80000000` at body offset 4 (Option 1 from the issue body, "self-describing wrappers").  The in-heap field is now always `>= 2 GB`, structurally outside any plausible heap-range check.  Unwrap recovers the raw handle by ANDing with `0x7FFFFFFF`.  Two-instruction overhead on each wrap and unwrap; no GC-code changes.
  - **Heap-ceiling guard** in `$alloc`: traps if `heap_ptr + total >= 0x80000000`, so the disjointness invariant (`heap_ptr < 2 GB` ⇒ tagged handles `>= 2 GB` never collide with heap pointers) holds by construction.  Practical Vera programs use <100 MB; this trap fires only on egregious heap pressure.
  - **Host-side mirrors**: `vera/wasm/json_serde.py::read_json` and `vera/wasm/html_serde.py::read_html` read the wrapper's handle field directly via wasmtime memory access (bypassing the WAT `_emit_unwrap_handle` helper) when parsing `JObject` / `HtmlElement` attributes.  Both now AND with `0x7FFFFFFF` to recover the raw handle for `map_store` lookup.  `_wrap_handle` in `vera/codegen/api.py` (host-side allocator for Option<Decimal>.Some payloads etc.) writes the tagged value to match.

### Tests

- `tests/test_codegen.py::TestWrapperHandleTagging578` — 6 new tests pinning the contract: (1) wrap site emits `i32.const 0x80000000; i32.or`, (2) unwrap site emits `i32.load offset=4; i32.const 0x7FFFFFFF; i32.and`, (3) `$alloc` body contains the heap-ceiling guard (ordered 8-instruction sequence pinned by adjacent-sequence regex), (4) end-to-end wrap/unwrap round trip preserves the original handle (a Map insert + lookup), (5) `html_to_string` produces the correct length output — pinning that the host-side `read_html` mask is in place (without it the attribute dict lookup would miss and the rendered HTML would be missing the `title="..."` attribute), (6) `json_stringify(JObject(...))` produces the correct length — sibling test for the host-side `read_json` mask (which lives in `vera/wasm/json_serde.py` and bypasses the WAT unwrap helper just like `read_html` does).

### Documentation

- **`KNOWN_ISSUES.md`** — removed the #578 bug row.  The bug-tracker section is now empty for the first time since ~v0.0.80.

## [0.0.154] - 2026-05-13

### Fixed

- **[#549](https://github.com/aallan/vera/issues/549)** — GC-aware tail-call optimization for allocating functions.  Pre-fix, the post-process in `vera/codegen/functions.py::_compile_fn` reverted every `return_call` → plain `call` whenever `ctx.needs_alloc` was True, because WASM `return_call` discards the current frame and would skip the GC epilogue (`global.set $gc_sp` to restore the shadow-stack pointer), leaking shadow-stack slots once per iteration and eventually trapping on the next `$alloc` once gc_sp passed the worklist boundary.  This forced agents to restructure tail-recursive code that allocates per iteration into `array_fold` / `array_map` shapes or to hoist allocations outside the recursion.
  - **The fix** preserves TCO and the shadow-stack invariant simultaneously: instead of reverting, the post-process now PREPENDS a two-instruction `$gc_sp` restore (`local.get $gc_sp_save; global.set $gc_sp`) immediately before each `return_call` in an allocating function.  The args for the recursive call are already on the WASM operand stack at the return_call site; the restore only touches the `$gc_sp` global, so args transfer atomically to the callee.  The callee's prologue then saves a clean new `$gc_sp` baseline, so per-iteration shadow-stack usage stays bounded at `caller's entry + n_arg_roots` regardless of iteration count.
  - **Postcondition-bearing functions still revert** to plain `call` — `return_call` would skip the runtime postcondition check (`local.set $ret; <check>; trap on failure; local.get $ret`).  The dispatch is: if `post_instrs` revert; elif `needs_alloc` patch with GC-restore; else keep `return_call` as-is.  Precedence: postcondition-revert > GC-aware-TCO-patch > untouched.
  - **Local pre-allocation** — the `$gc_sp_save` local is allocated BEFORE the dispatch so both the per-`return_call` restore site AND the function's GC prologue (`global.get $gc_sp; local.set $gc_sp_save`) share the same local index.

### Tests

- `tests/test_codegen.py::TestTailCallOptimization517` — renamed `test_allocating_function_falls_back_to_plain_call` to `test_allocating_function_uses_gc_aware_tco_549` and inverted its assertions: it now verifies that an allocating tail-recursive function emits `return_call $foo` (TCO preserved) AND that every such site is preceded by `local.get <N>; global.set $gc_sp` (shadow-stack invariant preserved).  Added a new sibling test `test_allocating_function_with_postcondition_still_reverts` to pin the postcondition-revert precedence.
- `tests/test_codegen.py::TestGCShadowStackOverflow::test_shadow_stack_overflow_traps` — rewritten to use a non-tail-recursive shape (recursive call wrapped in `array_append`).  Pre-#549 the tail-recursive form would leak shadow-stack slots and trap on the overflow guard at ~1300 iterations; post-#549 the same form runs cleanly to completion.  To still exercise the overflow guard, the non-tail form stacks WASM frames whose shadow-stack roots survive across iterations.
- `tests/test_stress.py::test_deep_tail_recursion_with_allocating_arg` — body switched from string-pool literals (which don't set `needs_alloc`) to a per-iteration `let @Array<Int> = [_, _]` heap allocation, so the test now actually exercises `#549`'s GC-aware TCO path.  The pre-fix body was passing trivially.
- `tests/test_stress.py::test_tco_with_allocation_1m_iterations` — new 1M-iteration companion, parametrised over default-GC and eager-GC modes (~190ms wall-clock in both).  Pre-fix this would have been impossible: 1M plain `call`s blow the WASM call stack at ~30K frames.  Post-fix the `return_call` + `$gc_sp` restore keeps shadow-stack usage flat, so 1M iterations complete in constant memory.

### Documentation

- **`KNOWN_ISSUES.md`** — removed the #549 bug row.

## [0.0.153] - 2026-05-13

### Added

- **[#667](https://github.com/aallan/vera/issues/667)** — SMT translator coverage for `FloatLit`, `IndexExpr`, and `ArrayLit` in contract predicates.  Pre-fix all three returned `None` from `vera/smt.py::translate_expr`, dropping every affected contract to Tier 3 (runtime check).  The issue body claimed the parser would reject these shapes; reality-check against `vera check` showed the parser and type checker already accepted them — only the SMT translator was missing the cases.
  - `FloatLit` → `z3.RealVal(value)`.  Float64 already maps to Z3's `Real` sort (sound for relational properties; not a full IEEE-754 model).  One-line addition.
  - `IndexExpr` → uninterpreted `index_<sort>(arr, i)` function call, parallel to the existing `length_<sort>` pattern.  Sound (function congruence — two references to `arr[i]` with the same `i` produce the same value) but partial — the verifier can't reason about element structure beyond what explicit predicates assert.  Quantified contracts ("for all valid i, arr[i] > 0") remain Tier 2 / Tier 3 territory.
  - `ArrayLit` → fresh `Array_<elt>` constant with `length(lit) == N` and per-element `index(lit, i) == element_i` axioms asserted to the solver.  Element types that can't be sorted (e.g. function-typed) fail cleanly via `None`.
- **Array-sort infrastructure** in `vera/smt.py`: `_get_array_sort`, `_get_index_fn`, `declare_array_var`.  `Array<T>` parameters are now declared as constants of uninterpreted `Array_<T>` sorts; pre-fix they fell through to `declare_int(z3_name)` because `Array` isn't in the SMT layer's `_adt_registry`, making `Array<Int>` slots numerically-typed in Z3.  The new path routes through `_is_array_type` + `_declare_array_var` helpers in `vera/verifier.py`.

### Fixed

- **Two overstrong example contracts honestly relaxed.**  Closing the FloatLit / ArrayLit gaps in the SMT translator changed two pre-fix Tier-3-with-warning postconditions into E500 verification errors — the verifier could now fully translate the body and reach the contradiction.  The pre-fix behaviour was *not* unsound (the verifier had honestly emitted E522 warnings "Cannot statically verify postcondition…") — only more precise post-fix.  Both contracts relaxed to match what's statically provable from the helpers' existing `ensures(true)` clauses:
  - `examples/json.vera::main` — `ensures(@Int.result == 0)` → `ensures(true)` with explanatory comment.  None of `parse_current_temp` / `parse_average_temp` / `round1` carries a postcondition strong enough to let the verifier conclude `@Int.result == 0` statically.
  - `tests/conformance/ch06_quantifiers.vera::main` and `::test_has_zero` — both `ensures(@Bool.result == true)` → `ensures(true)`.  Helpers `all_positive` / `has_zero` carry `ensures(true)`; the static verifier can't conclude the postcondition from the specific array literals.

### Tests

- `tests/test_verifier_coverage.py::TestSmtCoverage667` — 9 new tests in two clusters: 5 for the core translation cases (FloatLit in pre/postconditions, IndexExpr, ArrayLit, ArrayLit-element-access), plus 4 for the call-result-typing follow-up (ADT-element-array indexing, String/Float64/Array return type propagation through `_translate_call_with_info`).  Each asserts not just "no errors" but also `tier1_verified >= N` so a regression that drops back to Tier 3 fails the test (Tier 3 is also error-free).
- Three pre-existing edge-case tests (`test_translate_expr_returns_none_for_unsupported`, `test_binary_with_none_operand`, `test_unary_with_none_operand`, `test_if_with_untranslatable_condition`) swapped their `FloatLit` sentinel (now Handled) for `UnitLit` (still intentionally-unsupported — predicates are Bool, not Unit).
- `test_overall_tier_counts` updated: 252/26/278 → 253/25/278.  The +1/-1 shift comes entirely from the `json.vera::main` relaxation (pre-fix: counted in T3 with warning; post-relaxation: counted in T1 trivially), **not** from any SMT-widening-driven T3→T1 movement.  No other example contract changed tier.

## [0.0.152] - 2026-05-13

### Added

- **[#596](https://github.com/aallan/vera/issues/596)** — stress-test harness landing as `tests/test_stress.py` with 8 logical scale-dependent regression tests covering the bug classes the standard test suite couldn't catch.  Pre-#596 the project relied on user-reported real-world programs to surface scale-dependent codegen/runtime bugs (#570 iterative-builder shadow-stack overflow at ~4000 elements, #515 GC self-fault under sustained allocation, #593 Conway's Life corruption at 12×30+).  The harness exercises each scale axis at the smallest size where the bug class historically manifested with ~2-3x safety margin: 10K `array_map`, 5K nested-array `array_map`, 1K-deep tail recursion with allocating arg, 20×20 nested array-fold-of-array-fold (#593 territory), 100K `array_fold`, 10K String allocations through interpolation, 1K `State<Int>` get/put cycles in a single handler scope, 10K `IO.print` calls with stdout-capture buffer growth.  Each test asserts on a SPECIFIC observable (closed-form sum, exact line count, etc.), not just "completed without crashing", so a future regression that silently short-circuits or skips iterations would still fail.
- **[#596](https://github.com/aallan/vera/issues/596) eager-GC lane** — six of the eight stress tests (the GC-rooting-targeted subset: #570 / #515 / #549 / #573 / #593 / captured-frame State handlers) are parametrised over `[False, True]` for the `eager_gc` flag.  The `True` mode sets `VERA_EAGER_GC=1` via `pytest.MonkeyPatch.setenv` before the compile call, so the runtime's `$alloc` function emits a `call $gc_collect` as its first instruction — forcing a full GC pass on every allocation.  This converts latent missing-shadow-root bugs from "fires occasionally at scale" to "fires on the very next allocation," so a regression that would normally need thousands of iterations to surface fails on the first or second iteration.  The pattern was used to diagnose #593 originally; the eager lane embeds that diagnostic capability as ongoing regression coverage.  Total test count: 8 logical × eager lane parametrisation on 6 of them = 14 test instances.  Wall-clock: 0.66s in-process for the full suite.
- **`stress` pytest marker** registered in `pyproject.toml` with default `addopts = "-m 'not stress'"` — stress tests are skipped from the per-PR pytest run.  Local invocation: `pytest -m stress`.
- **`.github/workflows/nightly-stress.yml`** with three triggers: (1) nightly cron at 06:00 UTC as primary safety net, (2) path-filtered PRs touching `vera/codegen/**`/`vera/wasm/**`/`tests/test_stress.py` for fail-fast on PRs likely to break stress invariants, (3) manual `workflow_dispatch` from the Actions tab.
- **Failure reporting on cron failures** — when the nightly cron fails, the workflow uses `actions/github-script@v7` to open (or comment on, if one is already open) a tracking issue labelled `stress-regression`, with the commit SHA and run URL.  Deduplicates across days: the first failure opens a fresh issue, subsequent failures comment on it.  Skipped on `pull_request` triggers (PR's own checks tab is the reporting surface) and `workflow_dispatch` (whoever triggered is already paying attention).  Converts cron failures from "visible only to whoever opens the Actions tab" to "visible in the issue feed where Vera work is already triaged."

### Documentation

- New "Stress tests" subsection in `TESTING.md` documenting the harness, the 8 initial test programs with their scale axes and target bug classes, the default-skip behaviour, the three CI triggers, and the assertion-shape convention.

## [0.0.151] - 2026-05-12

### Added

- **[#597](https://github.com/aallan/vera/issues/597)** — walker-completeness audit.  Nine `Expr`-dispatching walker functions in the compiler now carry `# WALKER_COVERAGE:` checklist comments classifying every one of the 29 `Expr` subclasses with one of four dispositions: **Handled** (explicit `isinstance` branch), **Intentionally ignored** (default fall-through is correct — e.g. literals in a sub-expression walker), **Cannot occur** (structurally impossible — e.g. `OldExpr` in body-only contexts, `HoleExpr` post-typecheck), or **MISSING** (open bug, branch should exist).  A new `scripts/check_walker_coverage.py` enforces coverage mechanically — it parses each walker's `isinstance(expr, ast.X)` calls AND its checklist text, then verifies the union covers every `Expr` subclass declared in `vera/ast.py`.  Wired into pre-commit as the `walker-coverage` hook, so a new `Expr` subclass added to `vera/ast.py` forces every walker to either handle it or document its disposition.  Closes the bug class responsible for `#588` (closure-lift), `#604` (prelude combinators), `#559` (nested aliases), and `#648` (cyclic aliases) — all five PRs from this stabilisation cycle had the same shape: a walker handled N of N+1 subclasses, missing case silently fell through.  The convention is documented in `vera/README.md` under "Walker-completeness convention".  Closes `#597`.

### Fixed

- **[#597](https://github.com/aallan/vera/issues/597) defensive adds** — 11 `isinstance` branches added across `vera/codegen/compilability.py::_scan_io_ops` (4: `IndexExpr`, `ArrayLit`, `InterpolatedString`, `AnonFn`), `vera/codegen/compilability.py::_scan_expr_for_handlers` (5: `QualifiedCall`, `IndexExpr`, `ArrayLit`, `InterpolatedString`, `AnonFn`), and `vera/wasm/inference.py::_infer_expr_wasm_type` (2: `AnonFn`, `ModuleCall`).  Plus 8 defensive branches in `_infer_vera_type` (`Block`, `MatchExpr`, `HandleExpr`, `AssertExpr`, `AssumeExpr`, `AnonFn`, `QualifiedCall`, `ModuleCall`).  No user-visible behaviour change today — every defensive add was masked by an upstream guard (type checker rejection, `[E602]` codegen-skip, closure-pipeline sibling scan, translator-side registration in `calls_math.py`/`calls_containers.py`/etc.).  Plugs the gap if any upstream mechanism is relaxed in the future, preventing the silent-skip class from reappearing.

- **[#597](https://github.com/aallan/vera/issues/597) pr-review-toolkit follow-ups** (CodeRabbit + multi-agent audit) — five additional fixes landed in the same PR after the initial commit:
  - `scripts/check_walker_coverage.py` — replaced hardcoded `WALKER_FILES` list with `_discover_walker_files()` globbing `vera/**/*.py` for the `WALKER_COVERAGE:` marker.  The hardcoded list silently skipped any new walker file added without manually updating it — replicating the exact silent-skip class this script was written to close.
  - `scripts/check_walker_coverage.py` — anchored `extract_checklist_classes` to the WALKER_COVERAGE block (marker to next `"""`).  Pre-fix the regex ran over the whole function body so a `# Foo → bar`-shaped comment outside the block could silently count as coverage.
  - `vera/wasm/inference.py::_infer_vera_type` — `AnonFn` / `QualifiedCall` / `ModuleCall` defensive branches now return `None` instead of synthesising a fake `FnCall(name, args)` (which dropped the `qualifier` / `path` field and could match a same-name local fn from a different module).  `_infer_expr_wasm_type::ModuleCall` also returns `None` for the same reason.
  - `vera/wasm/inference.py::_infer_vera_type` — removed dead `if expr.expr is not None` guards on `Block`/`HandleExpr` defensive branches.  Both fields are non-Optional in the AST schema (`vera/ast.py:470, 481`); the guards were unreachable defensive code that hid the schema invariant.
  - `vera/codegen/compilability.py` — corrected misleading "masked by closure pipeline" comments on the `AnonFn` defensive branches of `_scan_io_ops` and `_scan_expr_for_handlers`.  `_compile_lifted_closure` does NOT call these scanners on lifted bodies, so the `AnonFn` branch is the PRIMARY defence (not redundant); the comment now states this directly.

### Tests

- **[#597](https://github.com/aallan/vera/issues/597) regression coverage** — two new test files pinning the audit machinery:
  - `tests/test_walker_defensive_branches_597.py` — 21 synthetic-AST tests covering all 11 defensive `isinstance` branches plus the 5 fixed-then-pinned `_infer_vera_type` cases.  Without these, a future refactor breaking a defensive branch would land silently (no production path exercises them today).
  - `tests/test_check_walker_coverage_597.py` — 12 unit tests for the enforcement script's parsing logic (Expr subclass extraction, isinstance flattening, checklist-block anchoring including the CR-3 regression case, auto-discovery invariants, end-to-end main).

### Internal

- **ROADMAP cleanup** — removed the stale `#604` row (Stabilisation tier Order 1) that PR `#659` had closed via code fix but not deleted from the roadmap.  Stabilisation tier renumbered 1-6; Agent-integration tier renumbered 7-9.  Added `#667` ("SMT translator coverage expansion: FloatLit/ArrayLit/IndexExpr") as new Stabilisation tier Order 6 — surfaced during the walker audit as a latent gap in `smt.translate_expr`, deferred from this PR per Option A scope decision because closing it requires extending the contract grammar (parser + checker work) beyond the audit-scope brief.

## [0.0.150] - 2026-05-12

### Fixed

- **[#559](https://github.com/aallan/vera/issues/559)** — nested type aliases (alias-of-alias via `Array<…>`, e.g. `type Row = Array<Int>; type Grid = Array<Row>;`) now compile and run correctly when indexed through both layers.  Pre-fix `vera/wasm/inference.py::_alias_array_element` extracted the array element type but did not canonicalise it — for `@Grid.0`, it walked `Grid → Array<Row>` and returned `NamedType("Row")` rather than the canonical `NamedType("Array", (Int,))`.  Downstream consumers saw the opaque alias name and either fell through (chained-indexing branch in `_infer_index_element_type_expr` checks `inner_te.name == "Array"`, fails on `"Row"`) or emitted a load-as-i32 + `i64.extend_i32_u` against what is actually a heap pointer to an (`Array<Int>`) pair — producing `type mismatch: expected a type but nothing on stack` at WASM validation (or, when the bug surfaced on a private helper, the misleading `unknown func: $caller` symptom described in the issue body).  Post-fix the helper runs the extracted element through the existing `_canonical_named_type` walker (the #630 canonicalisation seam), so a `Row` element resolves to `Array<Int>` and downstream lookups see the real shape.  Falls back to the original unresolved NamedType when the canonical walk terminates at a non-NamedType (e.g. `FnType` element), preserving the pre-fix contract for the direct `Array<T>` path.  Two new regression tests in `tests/test_codegen.py::TestCompoundArrays` pin the `array_length(@Grid.0[0])` and `@Grid.0[1][0]` shapes.  Closes `#559`.

## [0.0.149] - 2026-05-12

### Fixed

- **[#648](https://github.com/aallan/vera/issues/648)** — cyclic type aliases now produce a clean `[E132]` diagnostic at `vera check` time instead of crashing `vera compile` with `RecursionError`.  Pre-fix `vera/checker/registration.py::_register_alias` resolved aliases one at a time; when `type A = B` was processed before `B` was registered, the forward-reference fallback in `_resolve_type` returned a placeholder rather than chasing the chain, so the resolved-type representation reached the post-registration state with no observable cycle.  Codegen later stored the raw AST `type_expr` and `vera/codegen/core.py::_type_expr_to_wasm_type` chased the chain through the AST, blowing the stack with `RecursionError: maximum recursion depth exceeded`.  Post-fix `_register_all` calls a new `_check_alias_cycles` pass that walks every alias's AST `type_expr` chain (following `NamedType`-of-alias references through `RefinementType` wrappers, mirroring codegen's recursion shape) and emits `[E132]` ("Cyclic type alias") with the originating decl location, the full cycle path (`A -> B -> C -> A`), and a `Fix:` paragraph pointing at `data`-declared ADTs as the alternative for self-referential types.  Defensive cycle guards on the alias-walking helpers in `vera/wasm/inference.py` (closed in #633) remain as belt-and-braces.  Closes `#648`.

## [0.0.148] - 2026-05-12

### Fixed

- **[#660](https://github.com/aallan/vera/issues/660)** — `vera check` now rejects parameterised type-alias references with wrong arity.  Pre-fix `vera/checker/resolution.py::_resolve_type` silently truncated `zip(alias.type_params, te.type_args)` on length mismatch, leaving alias-local type-vars unsubstituted; downstream codegen leaked literal alias-local names into mono suffixes (`option_map$Int_B` instead of `option_map$Int_Int`) and the call site referenced a non-existent function-table entry → `unknown table 0: table index out of bounds` at runtime.  Surfaced by the #659 multi-agent review when the #604 fix happened to surface the same bug class via a different entry point (a `SlotRef` typed as a parameterised alias with too few type-args).  Post-fix the checker emits `[E133]` ("Type alias arity mismatch") with a precise diagnostic naming the alias, expected/supplied counts, and a `Fix:` paragraph suggesting the missing or extra type arguments.  Two defensive comments in `vera/codegen/monomorphize.py::_resolve_arg_fn_shape` and `vera/wasm/calls.py::_resolve_arg_fn_shape_wasm` (left in PR #659 to document the latent gap) are now trimmed to one-line "arity enforced upstream by checker" cross-references.

### Internal

- **[#661](https://github.com/aallan/vera/issues/661)** — investigated and confirmed the `compiled_mono_bases` cross-module name-collision concern is not reachable today.  Pass 2.5 in `vera/codegen/core.py::compile_program` (lines 519-530) explicitly skips imported FnDecls whose names are already in `fn_visibility` (= local declarations), so an imported forall decl with the same name as a local one is dropped before its template warning could be emitted.  And `forall_decl_names` is built from `program.declarations` only, never from imports — only local forall decls are eligible for suppression.  Net effect: at most one template warning per base name lands in `self.diagnostics`, so a bare-name match in the suppression filter cannot cross-suppress between modules.  Added an explanatory block comment at the suppression site documenting why bare-name keying is safe AND naming the trigger conditions that would invalidate the invariant (loosened Pass 2.5 dedup, or mono pipeline starting to carry module attribution).  Added `tests/test_codegen_modules.py::TestCrossModuleNameCollision661` with two tests pinning the invariant — compiles a name-shadowing fixture and asserts no over-broad suppression.

## [0.0.147] - 2026-05-12

### Fixed

- **[#628](https://github.com/aallan/vera/issues/628)** — cross-module imports now propagate `_fn_ret_type_exprs` alongside `_fn_sigs`.  Pre-fix `vera/codegen/modules.py`'s cross-module harvest only populated `_fn_sigs` (carrying WASM type info — sufficient for call-validation), but the `_fn_ret_type_exprs` registry (added in #614, re-used by #602) was never harvested across modules.  A `String`- or `Array<T>`-returning fn defined in module A and called from module B then hit `_fn_ret_type_exprs.get(name) → None` and fell through to the silent-skip path that #602 / #614 had already closed in-module.  Two failure shapes: (1) `make_arr(())[0]` where `make_arr` is cross-module — IndexExpr element-type inference returned None, enclosing function dropped via `[E602]`; (2) `IO.print("\(make_str(()))\n")` where `make_str` is cross-module — interpolation segment fell through to the `to_string(...)` silent wrapper, tripping `expected i64, found i32` at WASM validation.  Post-fix the cross-module harvest in `vera/codegen/modules.py` populates `_fn_ret_type_exprs` with the same `setdefault` shape as `_fn_sigs`.  Closes `#628`.

## [0.0.146] - 2026-05-12

### Fixed

- **[#655](https://github.com/aallan/vera/issues/655) Shape B** — array indexing through a refinement-of-Array alias (e.g. `type NonEmptyArray = { @Array<Int> | array_length(@Array<Int>.0) > 0 }` plus `fn head(@NonEmptyArray -> @Int) { @NonEmptyArray.0[0] }`) now compiles cleanly and runs correctly.  Pre-fix `vera/wasm/inference.py::_alias_array_element` only followed `isinstance(target, ast.NamedType)` chains when resolving an alias to its underlying `Array<T>`; if the alias target was a `RefinementType` (which the user's refinement syntax produces), the helper returned `None`.  Downstream `_infer_index_element_type` then returned `None` for `@NonEmptyArray.0[0]`, the `head` function got dropped via `[E602]` with "body contains unsupported expressions — skipped", and any call site referenced a non-existent `$head` → `unknown func: $head` at WASM validation.  Post-fix the alias-target lookup peels any `RefinementType` layers before checking for a `NamedType` base, so refinement-of-Array aliases resolve their element type the same as a bare `Array<T>`.  Closes `#655` (Shape A was closed in v0.0.145; Shape B is this fix).  Allowlist in `scripts/check_e602_clean.py` shrinks from 6 to 5 entries.

## [0.0.145] - 2026-05-11

### Fixed

- **[#604](https://github.com/aallan/vera/issues/604) / [#655](https://github.com/aallan/vera/issues/655) Shape A** — generic prelude combinator mono clones now produce the correct type-arg suffix when the closure argument is a `SlotRef` typed as an FnType alias (e.g. `@Doubler.0` where `type Doubler = fn(Int -> Int)`).  Pre-fix `_unify_param_arg` in `vera/codegen/monomorphize.py` had an `AnonFn`-specific alias-resolution path; `SlotRef` args typed as FnType aliases skipped that path and left the closure's return type variable unbound.  The unbound type var fell to the `"Bool"` phantom-var fallback at result-building time, producing mono suffixes like `option_map$Int_Bool` instead of `option_map$Int_Int` and trapping at runtime with `wasm trap: indirect call type mismatch`.  Post-fix: both `AnonFn` literals and `SlotRef`-typed-as-FnType-alias args flow through a shared `_resolve_arg_fn_shape` helper, binding the closure's return type uniformly.  Same fix applied at the WASM call-site rewriting layer (`vera/wasm/calls.py::_infer_fn_alias_type_args_wasm`).  Three of the five `[E602]`/`[E604]` prelude-skip cases (`option_map`, `option_and_then`, `result_map`) close at runtime; the other two (`option_unwrap_or`, `result_unwrap_or`) were already working via mono and only emitted misleading template warnings.

- **[#604](https://github.com/aallan/vera/issues/604) / [#655](https://github.com/aallan/vera/issues/655) Shape A — template-warning suppression** — audit recommendation 2 from the #604 investigation comment: post-compile suppression pass in `vera/codegen/core.py::compile_program` drops `[E602]` / `[E604]` / `[E605]` template-only warnings on generic `forall<T>` decls whose mono clones successfully compile.  Pre-fix every program importing the prelude saw 5 spurious warnings about `option_unwrap_or` / `option_map` / `option_and_then` / `result_unwrap_or` / `result_map` even when those functions worked end-to-end via mono.  Post-fix the warnings only fire for forall decls whose generic body cannot be compiled AND has no working mono clone — preserving the "this generic can never compile and you're never using a mono clone of it" signal for genuinely-broken or unused user generics, while removing the prelude-noise.  Allowlist shrinks from 11 to 6 entries (5 user-code generics from #655 Shape A removed; the 6 remaining are the prelude generics still firing in test files that don't call them, plus the `head` real codegen gap).

- **Documentation fix in `CLAUDE.md` release-workflow section** — "Stage 9 table" reference (stale since the project moved through Stages 10, 11, 12) replaced with a stage-agnostic instruction: "the **most recent Stage table** in `HISTORY.md`" with a `grep "^## Stage" HISTORY.md | tail -1` hint for confirming the current stage before writing.  Caught during the 2026-05-11 review cycle.

### Added

- **Layer 3 of [#626](https://github.com/aallan/vera/issues/626)** — new `vera/skip.py` with two control-flow exception classes: `CodegenSkip(node, reason)` (raised when a translator hits an unsupported AST shape; caught at the `_compile_fn` / `_compile_lifted_closure` boundary and converted to a structured `[E602]` diagnostic with the unsupported-node's source span) and `CodegenInvariantError(msg, node=None)` (raised on states that type-check should have rejected; surfaced as a new `[E699]` "Internal compiler error" at severity=`error` so `vera compile` exits non-zero — compiler bugs shouldn't be maskable as soft warnings in CI logs).  An audit of all 372 `return None` sites in `vera/codegen/**` and `vera/wasm/**` classified each into SILENT_SKIP / PROPAGATE / OPTIONAL_RETURN / INVARIANT_DEFENSIVE buckets; **104 SILENT_SKIP sites converted to `raise CodegenSkip`** in this PR (55 in `calls_arrays.py` via a shared `_array_elem_triad_or_skip` helper, 24 in `data.py`, 11 in `calls_containers.py`, 9 in `calls_handlers.py`, 4 in `context.py`, 1 in `calls.py`).  Pre-conversion these all silently dropped to a generic enclosing-function-level `[E602]`; post-conversion they each emit a source-located diagnostic pointing at the specific unsupported expression.  The remaining 39 INVARIANT_DEFENSIVE sites and the 154 PROPAGATE sites that may now be unreachable are tracked in [#657](https://github.com/aallan/vera/issues/657).

- **New `_error()` API on the codegen builder** (`vera/codegen/core.py`) parallel to the existing `_warning()` method, hardcoding `severity="error"`.  Used by the `[E699]` catch handlers in `_compile_fn` (`vera/codegen/functions.py`) and `_compile_lifted_closure` (`vera/codegen/closures.py`) — both updated in this PR to route `CodegenInvariantError` through `_error()` rather than `_warning()` so internal-compiler-error diagnostics propagate to a non-zero CLI exit code rather than a swallowable warning.  Only those two internal handlers changed; no user-facing API surface or other `_warning()` call sites were modified.

- **Layer 1 of [#626](https://github.com/aallan/vera/issues/626)** — new `scripts/check_e602_clean.py` pre-commit + CI gate that fails when any compile of an example or conformance program emits `[E602]` (body unsupported) or `[E604]` (param unsupported) outside an explicit allowlist.  The `[E602]` warning channel was the project's only signal for silent translator-skip failures, and several long-standing instances of it were buried in every WASM compile — making it impossible to spot a new genuine skip without manually sifting through expected noise.  The gate makes a new silent skip a hard build failure unless explicitly allowlisted with a tracking-issue reference.
- **Allowlist of 11 currently-expected silent skips**, each tagged with a tracking issue: 5 prelude combinators (`option_unwrap_or` / `result_unwrap_or` / `option_map` / `option_and_then` / `result_map` — [#604](https://github.com/aallan/vera/issues/604)), 6 user-code cases surfaced by the new gate's first run (5 generic-decl spurious warnings + 1 real codegen gap — [#655](https://github.com/aallan/vera/issues/655)).

### Documentation

Small docs sweep — closes six aging documentation issues in one PR.  No code changes; touches `spec/02-types.md`, `spec/03-slot-references.md`, `spec/06-contracts.md`, `SKILL.md`, `README.md`, and `HISTORY.md`.

- **[#557](https://github.com/aallan/vera/issues/557)** — `spec/03-slot-references.md` Example 9 said the match-arm pattern binding "shadows the function parameter" without defining "shadow".  Two readings were equally consistent with the prose (replace vs push-on-top); the compiler implements push-on-top.  Replaced the one-liner with an explicit paragraph spelling out push-on-binding semantics, the resulting De Bruijn ordering for multi-field constructors (leftmost = deepest = highest index, rightmost = shallowest), and the non-commutative-operations caveat that exposes the rule.

- **[#561](https://github.com/aallan/vera/issues/561)** — two tier-accuracy bugs in `spec/06-contracts.md`.  (1) §6.3.1 (Tier 1) was missing pure-fn calls in `ensures` / `@T.result` / `if/then/else`, which actually verify at Tier 1 today; §6.3.2 (Tier 2 NYI) incorrectly listed them.  Moved all three from §6.3.2 to §6.3.1.  (2) §6.3.3 said "Bounded quantification is decidable for finite bounds and is handled by Z3 via finite unrolling" — that reads as Tier 1, but Tier 2 (the tier that would handle quantifier unrolling) is [#427](https://github.com/aallan/vera/issues/427) NYI.  Clarified that every `forall`/`exists` in a contract falls to Tier 3 today, both for `forall` and the symmetric `exists` text.

- **[#560](https://github.com/aallan/vera/issues/560)** — the `invariant(...)` clause on `data` declarations is documented in `spec/02-types.md` §2.4.1, `spec/06-contracts.md` §6.2.3, and `SKILL.md`, but every documented form fails with `[E130] no <DataName> bindings in scope` at v0.0.144.  Added inline NYI markers at all three sites pointing at #560, with the working alternative (refinement types).  Added the limitation to `spec/06-contracts.md`'s §6.9 Limitations table.

- **[#607](https://github.com/aallan/vera/issues/607)** — added a new `spec/02-types.md` §2.2.1 "`Int` and `Nat` compatibility" subsection covering the bidirectional subtyping (`Nat <: Int` always; `Int <: Nat` permitted with verifier-discharged obligation).  Practical-implication note tells agents not to insert `nat_to_int` defensively when calling `array_length` etc. into `@Nat` positions.  Cross-reference added to `SKILL.md`'s "Primitive types" listing.

- **[#608](https://github.com/aallan/vera/issues/608)** — added `SKILL.md` "IO model: terminal vs browser" subsection (under §Browser compilation) explaining that programs using `IO.sleep` + ANSI escapes for terminal pacing/rendering compile cleanly to `--target browser` but render escapes as literal text and busy-wait the main thread.  The recommended browser pattern is "Vera pure simulation core + JS driver via `requestAnimationFrame`".  Two runtime gaps that would make the recommended pattern more ergonomic are tracked separately ([#609](https://github.com/aallan/vera/issues/609) JSPI sleep, [#610](https://github.com/aallan/vera/issues/610) ANSI subset interpreter).  `README.md`'s "write once, run anywhere" line qualified to acknowledge the IO seam.

- **[#512](https://github.com/aallan/vera/issues/512)** — trimmed all 31 Stage 11 rows in `HISTORY.md` (v0.0.112 → v0.0.138) to match the early-stage one-sentence format established in Stage 1–8.  Per the canonical template now in long-term memory: `**X** ([#N]).` per row, no em-dash separator, no secondary clauses, no implementation detail.  Detailed mechanism descriptions for each version stay in CHANGELOG under their respective `## [0.0.X]` section.

### Changed

- **mypy 1.20.2 → 2.0.0** (`pyproject.toml`, `uv.lock`).  Mypy 2.0 enables three flags by default that were opt-in under 1.x: `--local-partial-types` (changes inference of types based on assignments in other scopes), `--strict-bytes` (per [PEP 688](https://peps.python.org/pep-0688): `bytearray` and `memoryview` no longer assignable to `bytes`), and `--allow-redefinition` behaves like 1.x's `--allow-redefinition-new` (more flexible variable redefinition across blocks).  Running mypy 2.0 against `vera/` produced **zero errors** with the existing source — no compiler-source changes needed to clear the upgrade.  Manual upgrade in favour of dependabot PR #647 (closed in favour of this change).

## [0.0.144] - 2026-05-11

### Fixed

- **[#633](https://github.com/aallan/vera/issues/633)** — `_resolve_base_type_name` (in `vera/wasm/inference.py`) now carries an explicit `_seen` cycle-detection accumulator, restoring consistency with the post-#630 `_canonical_named_type` walker that already had one.  Defence-in-depth: cyclic type aliases are user errors that should be rejected upfront by the type checker (tracked separately as [#648](https://github.com/aallan/vera/issues/648)), but a bug in the upstream rejection must not turn into a `RecursionError` inside codegen.

- **[#634](https://github.com/aallan/vera/issues/634)** — `SlotRef` and other AST nodes constructed inside `InterpolatedString.parts` now carry source spans in **original-source coordinates** instead of synthetic-wrapper coordinates.  `_parse_interp_expr` previously wrapped each interpolation expression in a dummy `private fn interpExpr(...) { <SEGMENT> }` function for parsing, with the segment placed at wrapper line 3, column 3 — and Lark-emitted spans inside the parsed body were never translated back to the original source.  The result: `[E615]` (and other) diagnostics on interpolated expressions landed on line 3 of the user's file, regardless of where the offending string literal actually was.  `_split_interpolation` now records each segment's offset within the raw string, `string_lit` computes the segment's original line/column from the outer string-literal span, and `_parse_interp_expr` walks the parsed AST and remaps every `Span` field via a new `_remap_spans_inplace` helper.  The previously-softened assertion in `TestE615LoudInterpolationFallthrough630::test_e615_fires_on_adt_in_interpolation` is tightened to pin both line **and** column of the diagnostic at the SlotRef's position, and `test_multiple_e615_in_one_interpolation` now pins per-segment column fidelity (two SlotRefs in the same string get two distinct, correct columns).

- **[#556](https://github.com/aallan/vera/issues/556)** — the user-visible bug class (calling a user-defined `@Unit`-returning function in statement position trips a WASM `type mismatch: expected a type but nothing on stack` validation error) was already fixed by #584's `_is_void_expr` work in v0.0.135.  The specific repro shape from the original #556 report — a *pure* helper (no IO effect) followed by a unit-literal final expression — wasn't pinned by the existing conformance test (which covered IO-effect variants only).  Added `TestUserUnitFnInStatementPosition556` to `tests/test_codegen.py` with two cases: the exact #556 repro plus the where-block variant from the follow-up comment.  Pinning the specific shape so it can't silently regress.

- **[#591](https://github.com/aallan/vera/issues/591)** — three network-response UTF-8 decode sites in `vera/codegen/api.py` no longer leak Python `UnicodeDecodeError` text into Vera-level `Result::Err` strings.  Two strategies, chosen per-site based on user intent:
  - **`Http.get` / `Http.post`** — now decode response bodies with `errors="replace"`.  A remote server returning non-UTF-8 bytes (rare but real with misconfigured `Content-Type`) surfaces as U+FFFD substitutions inside the Ok-branch string, preserving the data.  User intent for these calls is "fetch this URL"; preserving the body beats preserving the (already-rare) signal that bytes weren't cleanly UTF-8.
  - **`Inference.complete`** — `_call_inference_provider` now catches `UnicodeDecodeError` explicitly and re-raises as `RuntimeError("Inference provider '<name>' returned a response body that is not valid UTF-8 (invalid byte at position N).")`.  The `host_inference_complete` wrapper's existing `except Exception` catches this and writes the Vera-shaped message into the Err branch.  Non-UTF-8 from an LLM API is genuinely broken; we want loud failure with a Vera-native message, not the `codec can't decode byte 0x...` Python form.  Three structural assertions added in `tests/test_runtime_traps.py::TestNetworkResponseUtf8Hygiene591`, mirroring the #589 coverage shape.

### Documentation

- **KNOWN_ISSUES.md** — removed entries for #633, #634, and #591 (closed in this release); added entry for the newly-filed [#648](https://github.com/aallan/vera/issues/648) (cyclic-alias `RecursionError` — the upstream bug discovered while implementing #633).

## [0.0.143] - 2026-05-10

### Fixed

- **Windows compatibility** — three Windows-specific bugs surfaced when PR #639 added `windows-latest` to the CI test matrix in advisory mode (`continue-on-error`).  All three close in this release, and the matrix flips to fully strict (Windows entries are now merge gates alongside Ubuntu / macOS):

  - **[#640](https://github.com/aallan/vera/issues/640)** — Vera CLI's `/dev/stdin` path is Unix-only.  `_load_and_parse(path)` in `vera/cli.py` previously called `Path('/dev/stdin').read_text()`; on Windows the path doesn't exist as a filesystem entry and `vera <subcmd> /dev/stdin` failed with `Error: file not found: /dev/stdin`.  Now reads from `sys.stdin` directly when `path in _STDIN_PATHS` — portable across Unix and Windows, and more semantically correct (the user's intent is "read from stdin", not "read from a specific file path").  Closes 6 failing tests in `tests/test_cli.py::TestStdinInput`.

  - **[#641](https://github.com/aallan/vera/issues/641)** — default cp1252 file I/O encoding caused `UnicodeEncodeError` / `UnicodeDecodeError` on Windows for tests reading or writing files containing `→` or `—` characters.  Set `PYTHONUTF8=1` in the CI test job environment so Python's text-mode `open()` defaults to UTF-8 regardless of locale (PEP 540), and added explicit `encoding='utf-8'` to `vera/parser.py`'s grammar load (the load-bearing site that runs on every parse).  Closes ~9 failing tests across `test_codegen.py`, `test_codegen_monomorphize.py`, `test_codegen_closures.py`, `test_html.py`.  Broader audit of `open()` / `read_text()` / `write_text()` call sites for explicit `encoding='utf-8'` queued as a follow-up — for now CI is covered via `PYTHONUTF8=1`, and locally users on Windows without `PYTHONUTF8=1` may still hit the bug on individual files.

  - **[#642](https://github.com/aallan/vera/issues/642)** — `tests/test_codegen.py::TestIOOperations::test_io_read_file_success` and `test_io_read_file_roundtrip` embedded Windows tempfile paths (e.g. `C:\Users\runner\AppData\...`) into Vera string literals via f-string interpolation.  Vera's grammar correctly rejected `\U` as an invalid escape sequence, producing `[E009]` at parse time.  Fix in test fixtures: convert the path to POSIX form via `tmp_path.replace(os.sep, '/')` before embedding (Windows file APIs accept forward slashes).

### Changed

- **CI test matrix is now fully strict on Windows.**  PR #639's advisory `continue-on-error: ${{ matrix.os == 'windows-latest' }}` is removed in this release — the three Windows entries (`{3.11, 3.12, 3.13}`) now block merges alongside Ubuntu and macOS.  Total matrix coverage: 9 entries (3 OSes × 3 Python versions).

## [0.0.142] - 2026-05-08

### Fixed

- **[#630](https://github.com/aallan/vera/issues/630)** + **[#632](https://github.com/aallan/vera/issues/632)** + **[#635](https://github.com/aallan/vera/issues/635)** + **[#636](https://github.com/aallan/vera/issues/636)** — close the #602 bug class structurally across all four sites.  After ten distinct triggers across PRs #627 and #629, each fixed locally with one more `isinstance` handler or one more inference site, the discovery rate (9th and 10th triggers landing within hours of #630 being filed) outpaced reactive fixing.  This release consolidates the canonicalisation surface into a single walker, makes the silent amplifier loud at every site (interpolation, apply_fn / call_indirect), substitutes parameterised aliases in both inference and compilability paths, and propagates closure-body failures up to drop enclosing functions cleanly.

  **Tier 1 — centralised canonicalisation.** The pre-#630 codebase carried six overlapping canonicalisation helpers in `vera/wasm/inference.py` (plus an unaudited seventh in `vera/wasm/calls_arrays.py`), each handling a subset of (a) `RefinementType` unwrap, (b) alias-chain follow, (c) generic substitution, (d) `type_args` formatting.  Site by site, ad-hoc walks at the apply_fn dispatchers, FnType-return helpers, and IndexExpr branch independently re-implemented combinations of these concerns and missed the rest — accumulating triggers 1–10 of the i32_pair-into-i64 mismatch bug class.

  Replaced with two helpers — `_canonical_named_type` (the core walker: iteratively unwraps RefinementType, applies optional alias_map for generic substitution, follows NamedType alias chains, returns canonical `NamedType` or None) and `_canonical_wasm_type` (thin convenience wrapper that maps the canonical name to a WASM type).  Migrated all callers:

  - `_format_named_type_canonical` — now a 3-line delegate.
  - `_resolve_i32_pair_ret_te` — now a 2-line delegate (kept for #628 cross-module work; otherwise inline-able).
  - `_fn_type_return_wasm` — single-line delegate.
  - `_resolve_generic_fn_return` — builds `alias_map` from the generic params + concrete args, single delegate call.
  - `_infer_fncall_vera_type` apply_fn dispatcher — collapsed from a 75-line nested `isinstance` ladder over `(SlotRef, AnonFn)` × `(generic, non-generic)` × `(NamedType, RefinementType)` shapes to 18 lines: extract closure return TypeExpr + alias_map, call walker once.  Future closure-arg shapes (`FnCall` returning a closure, `IfExpr` selecting between closures, etc.) plug into the same dispatch with no new isinstance ladder.
  - `_infer_apply_fn_return_type` — same consolidation as above.
  - `_infer_index_element_type_expr` FnCall branch — now uses the canonical `NamedType` (with `type_args` preserved) directly to feed `_alias_array_element`.
  - `_infer_closure_return_vera_type` (in `calls_arrays.py`, used by `array_map`) — previously bare-`NamedType`-only; now handles refinements and alias chains.

  Deleted `_resolve_type_name_to_wasm_canonical` — functionally identical to `_resolve_base_type_name`, an unnoticed duplicate that had evolved in parallel.  All callers redirected.

  **Tier 2 — loud diagnostic on the silent amplifier.** The actual silent failure for ten triggers wasn't the inference miss itself — it was `vera/wasm/operators.py:482-486`, the `else` branch in `_translate_interpolated_string` that wrapped any unrecognised-type segment with `to_string(...)`.  `to_string` reads its argument as `i64`; an `i32_pair` (String/Array) value then tripped `expected i64, found i32` at WASM validation.  That fallthrough turned every canonicalisation gap into invalid emission rather than a clean compile-time skip.

  Added new error code [E615] "Cannot interpolate value of unknown type — type inference failed".  Converted the silent fallthrough to record the offending segment on `WasmContext._interp_inference_failures`, then return None.  `CodeGenerator._compile_fn` harvests the failures and emits [E615] for each before falling through to the existing [E602] skip — same loud-skip mechanism that any other unsupported expression triggers, but now with a specific E-code pointing at the actual inference gap rather than a generic "unsupported expressions".

  **Net effect.** Six canonicalisation helpers → two.  Seventy-five-line apply_fn dispatcher × two sites → eighteen lines × two.  Silent miscompilation on inference miss → clean compile-time skip with specific [E615] diagnostic.  All ten existing #602-class regression tests in `TestStringInterpolation` continue to pass — pure refactor + diagnostic conversion, no behavioural change for valid programs.  Seven new regression tests under `TestE615LoudInterpolationFallthrough630` cover: ADT interpolation (the canonical E615 trigger), `Result<T,E>` interpolation (parallel ADT shape), closure-body E615 (the silent-failure-hunter C1 finding — without harvest in `closures.py` the closure was silently dropped), per-function isolation of `_interp_inference_failures`, multiple-failures-per-function (UX — one [E615] per failing segment instead of N round-trips), terminal-NamedType type_args propagation (the CodeRabbit + code-reviewer flagged latent bug — alias-bound type_args propagate through the walker), and `array_map` over a refinement-returning closure (previously-unaudited `_infer_closure_return_vera_type` path now handling refinements).

  PR review pass found four additional review-pass items addressed in the same PR.  CodeRabbit + the code-reviewer agent independently identified that `_canonical_named_type`'s `outer_type_args` capture rule (always read from the *first* NamedType) lost type_args when an `alias_map` substitution bound a generic param to a parameterised type — fixed by always reading from the *terminal* NamedType.  The silent-failure-hunter agent caught the closure-body harvest gap — fixed by extracting the harvest into `CodeGenerator._harvest_interp_inference_failures` and calling it from both `_compile_fn` and `_compile_lifted_closure`.  Comment-analyzer flagged trigger-count drift in `operators.py` and a "plug in here" overstatement — both corrected.  Multiple-failures-per-function was added as a UX improvement (`had_failure` flag in `_translate_interpolated_string` so all failing segments surface in one compile pass).

  A second CodeRabbit review pass added five more findings, all addressed.  The `_canonical_named_type` walker gained: (a) a unified cycle guard via a single `seen` set covering both `alias_map` substitution and `_type_aliases` chain following, so a self-referential alias_map (`{T: NamedType("T")}`) can no longer loop forever; (b) `Future<T>` transparency in the `_canonical_wasm_type` convenience wrapper, parallel to `_slot_name_to_wasm_type`'s existing `Future<T>` strip-and-recurse handling; (c) parameterised-alias substitution via a new `_substitute_type_vars` helper, so following `type Box<T> = Array<T>` with a concrete `Box<Int>` substitutes `T → Int` in the alias body before continuing the walk.  Tests strengthened: `test_canonical_named_type_terminal_args_propagation` switched from a non-parameterised alias (`type IntList = Array<Int>`) to a parameterised one (`type Box<T> = Array<T>`) so it actually exercises the substitution path; `test_per_function_isolation_of_failures_list` added a `clean_after` function so the test catches forward leakage from `dirty` rather than only backward.

  Pragma audit closed for the canonicalisation cluster — the disproved `# pragma: no cover` on closure-return-RefinementType (PR #629) was removed during the cluster migration, plus a `# pragma: no cover — defensive` claim on `_compile_lifted_closure`'s body-instrs-None path (now provably reachable through the new E615 path).  Broader audit (verifying every prose-bearing pragma claim across the WASM codegen) is queued as a follow-up.

  Final review pass closed three more sites in the same PR rather than landing them as follow-ups.  **#635** (parameterised-alias substitution in `_type_expr_to_wasm_type` — the compilability check's parallel of the walker fix): extracted `substitute_type_vars` as a module-level free function so both `InferenceMixin` and `CodeGenerator` can use it; `type Id<T> = T; @Id<Array<Int>>` now compiles end-to-end.  **#632** (apply_fn / call_indirect E616 diagnostic): `_translate_apply_fn` now records unhandled closure-arg shapes on `_apply_fn_inference_failures`, harvested as `[E616]` before the function-skip `[E602]`, so `apply_fn(make_mapper(()), 7)` (where `make_mapper` is a FnCall returning a closure) now produces a source-located diagnostic instead of a WASM-validation trap.  **#636** (closure-body fail drops enclosing fn): `_lift_pending_closures` now reports whether any closure body failed; `_compile_fn` checks the flag and drops the enclosing top-level fn with a specific `[E602]`, so the module no longer carries a `call_indirect` to a missing function-table entry.

  **Final state.** Six canonicalisation helpers → two; ten triggers structurally closed at four sites (interpolation `[E615]`, IndexExpr-of-FnCall, FnType-alias / generic FnType return, apply_fn `[E616]`, compilability `_type_expr_to_wasm_type`, closure-body propagation).  Every silent miscompilation in the bug class is now either structurally impossible or surfaces as a source-located diagnostic + clean function skip.  Eleven regression tests in `TestE615LoudInterpolationFallthrough630` pin the closures.

  Remaining follow-ups (out of scope for this PR, smaller polish items): [#628](https://github.com/aallan/vera/issues/628) (cross-module `_fn_ret_type_exprs` propagation), [#626](https://github.com/aallan/vera/issues/626) Layer 1 (pre-commit gate on `[E602]` across the conformance suite), [#633](https://github.com/aallan/vera/issues/633) (cycle-guard alignment for `_resolve_base_type_name`), [#634](https://github.com/aallan/vera/issues/634) (SlotRef-in-interpolation source-span fidelity), and the duplicate `_type_expr_name` / `_type_expr_to_slot_name` in `inference.py`.

## [0.0.141] - 2026-05-08

### Fixed

- **Inline-refinement return types** in `_infer_fncall_vera_type` and `_infer_index_element_type_expr` — third trigger of the same bug class as #602 (i64/i32 mismatch at WASM validation) and the type-alias case fixed in v0.0.140.  Surfaced during PR #627's review (CodeRabbit duplicate-comment escalation, merged before the fix landed in #627 itself).

  When a fn declares an inline refinement return type (`@{ @String | predicate }`), `_register_fn` stores the literal `RefinementType` AST in `_fn_ret_type_exprs`.  v0.0.140's fix only handled the `NamedType` case via `isinstance` — `RefinementType` fell through to None, `_translate_interpolated_string` substituted `to_string(...)` for an `i32_pair` value, same #602 trap with a different trigger.  Same gap also lived in `_infer_index_element_type_expr`'s FnCall branch (the path #614 added) for refinement-`Array<T>` returns indexed via `f()[i]`.

  Fix: extracted the i32_pair return-type resolution into a helper `_resolve_i32_pair_ret_te` that handles both `NamedType` (with alias resolution via `_resolve_base_type_name`) and `RefinementType` (recursive unwrap of arbitrary nesting depth, then resolve).  Applied to both i32_pair branches (non-generic + generic-mono) and to the parallel IndexExpr inference path.

  PR review pass surfaced five more triggers of the same bug class.  **Nested refinements** (`@{ @{ @String | p1 } | p2 }`) are reachable per the grammar; the single-layer `if isinstance(...): unwrap` in the initial v0.0.141 fix fell through to None for nested forms.  Replaced with a `while isinstance(ret_te, ast.RefinementType): ret_te = ret_te.base_type` loop covering arbitrary nesting depth, applied to both `_resolve_i32_pair_ret_te` and the parallel IndexExpr branch.  The **`apply_fn` / `FnType`-alias** path (`apply_fn(@FnAlias.0, ())` where `FnAlias`'s return type wraps refinements) had three separate inference sites that walked `FnType.return_type` and only handled `NamedType` directly: `_infer_fncall_vera_type`'s apply_fn branch, `_resolve_generic_fn_return`, and `_fn_type_return_wasm`.  Same `while`-loop unwrap applied symmetrically at all three.  And the **`apply_fn`-over-aliased-`FnType`** path (e.g. `type Str = String; type Maker = fn(Unit -> Str) effects(pure);`) called `_format_named_type` directly on `NamedType("Str")`, returning the alias name; downstream interpolation's `vera_type == "String"` check missed and re-triggered the same trap.  Introduced `_format_named_type_canonical` (resolves `te.name` through the alias chain via `_resolve_base_type_name`, then formats with original `type_args`) and applied it to both branches of the apply_fn substitution.

  And the **inline `AnonFn` to `apply_fn`** path (`apply_fn(fn(@Unit -> @String) effects(pure) { ... }, ())`) — the SlotRef branch above was the only `apply_fn` arg shape handled; an inline anonymous closure literal fell through, `_infer_fncall_vera_type` returned None, and downstream interpolation re-triggered the same trap.  Added an `elif isinstance(closure_arg, ast.AnonFn)` branch alongside the SlotRef branch, simpler than the SlotRef path (no alias substitution — AnonFn carries `return_type` directly) but with the same RefinementType-unwrap + `_format_named_type_canonical` shape.

  And finally the **nested-refinement-`AnonFn`-on-the-WASM-side** path — same `apply_fn(fn(@Unit -> @{ @{ @String | p1 } | p2 }) ...)` shape but exercising `_infer_apply_fn_return_type` (call_indirect sig inference) rather than `_infer_fncall_vera_type` (Vera-type-name inference).  Inverse surface: `expected i32, found i64` rather than `expected i64, found i32`.  Pre-fix the AnonFn branch in `_infer_apply_fn_return_type` carried `# pragma: no cover — closure returns are not refinement types` with a single-level unwrap; the pragma was empirically disproved by the 9th and 10th triggers (an inline AnonFn *can* declare RefinementType returns per the grammar, and the type checker accepts nested forms).  Replaced single-level unwrap with the established `while`-loop shape and removed the disproven pragma.

  Eight new regression tests in `TestStringInterpolation` cover the inline-refinement String, the nested-refinement String, the refinement-over-alias String, the nested-refinement Array indexed via FnCall, the apply_fn-with-FnType-nested-refinement path, the apply_fn-over-`FnType`-aliased-String path, the apply_fn-over-inline-`AnonFn` path, and the apply_fn-over-nested-refinement-`AnonFn` (WASM-side) path.  All ten return-type shapes now verified — `f()` baseline (#602), type alias over String, inline refinement over String, nested refinement over String, refinement-over-alias, nested refinement over Array indexed via FnCall, `apply_fn` over a `FnType`-aliased nested refinement, `apply_fn` over an aliased `FnType` return, `apply_fn` over an inline `AnonFn`, and `apply_fn` over a nested-refinement inline `AnonFn` (WASM-side).

  The 9th and 10th triggers landing within hours of filing [#630](https://github.com/aallan/vera/issues/630) (the structural close-out tracking issue for this bug class) is the empirical argument for that issue: trigger discovery velocity outpaces local fix throughput.  Each new shape added to either dispatcher (Vera-type-name half or WASM-type half) is a fresh opportunity for the same bug.  The structural fix in #630 (centralised `_canonical_vera_type` + loud diagnostic on the silent fallthrough) is the queued close-out.

## [0.0.140] - 2026-05-08

### Fixed

- **[#602](https://github.com/aallan/vera/issues/602)** — `IO.print("\(make())")` (a `String`-returning function call as an interpolation segment) produced invalid WASM with `expected i64, found i32` at instantiation.  Root cause: `_infer_fncall_vera_type` in `vera/wasm/inference.py` mapped user-fn WAT return types back to Vera-type names for the `i64` / `i32` / `f64` cases but had no `i32_pair` branch; a fn returning `String` mapped to `None` here.  `_translate_interpolated_string` then fell through to the `to_string(...)` Int-conversion fallback wrapper, which reads its arg as `i64` — but the FnCall pushed `i32_pair`.  Same inference-gap shape as #614 (which was the *element-type* of an indexed FnCall result; this is the *return-type* inference half).

  Fix: extend the WAT-type → Vera-type fallback to consult `_fn_ret_type_exprs` (the registry added by #614) when the WAT type is `i32_pair`, so `String` and `Array<T>` returns are disambiguated.  Same registry, same pattern, same load-bearing infrastructure paying off twice.

  Two new tests in `TestStringInterpolation` cover the String-returning FnCall and an Array-returning FnCall indexed in interpolation — both classes of `i32_pair` return.

## [0.0.139] - 2026-05-08

### Fixed

- **[#614](https://github.com/aallan/vera/issues/614)** — `f()[i]` (indexing into a function-call result) silently dropped the enclosing function from the WAT output.  Root cause: `_infer_index_element_type_expr` in `vera/wasm/inference.py` only handled SlotRef and nested-IndexExpr collections; FnCall collections fell through to `return None`, propagating up until either `_compile_fn` skipped the function with an [E602] warning (top-level case — the same shape as #604) or `_compile_lifted_closure` returned None (closure case — silent: the registered closure_id was never added to the function table, so the call_indirect at the use site referenced a missing entry and WASM validation rejected the module with "unknown table 0: table index out of bounds at offset N").  Both manifestations close together.

  Fix: register each FnDecl's full Vera return-type expression in a new `_fn_ret_type_exprs` dict on `CodeGenerator` (alongside the WAT-type `_fn_sigs`), propagate it to the per-function and closure WasmContexts, and extend `_infer_index_element_type_expr` to look up the called fn's return type and extract the `Array<T>` element when applicable.

- **[#615](https://github.com/aallan/vera/issues/615)** — closure capture order miscompile, two failure shapes both rooted in `_collect_free_vars` returning captures unsorted and unfilled:

  1. **Non-contiguous outer slot.**  Closure body refs `@Int.k` while skipping `@Int.j` (j<k).  The lift-side env had no entry for the unreferenced outer index, so `env.resolve("Int", k)` returned None inside the closure body, body translation failed, the closure was dropped from the function table, and the call_indirect at the use site referenced a missing entry — WASM validation trap.  Concrete repro: a closure capturing `@Int.2` from outer scope while having a `@Int.1` (which the body doesn't reference) in the same scope.

  2. **Ascending walker-order silent miscompute.**  Even with contiguous captures, when source order put the lower outer_idx first (e.g. body `@Int.1 - @Int.2`), the walker added (Int,0) before (Int,1) → ascending lift-side push order → wrong stack layout under `WasmSlotEnv.resolve` (which uses `pos = len-1-index`) → body's slot refs resolved to the WRONG captured locals.  No trap, just wrong output.  This was independent of #615's original reproducer but shares the root cause.

  Fix: in `_collect_free_vars`, after walking the body for free vars, group captures by type, fill the prefix [0, max] per type with synthetic entries (their `wasm_type` matches the type's other captures since `type_name` deterministically maps to a single WAT type), and sort each group descending by outer_idx so the lift-side push lands the highest outer_idx at the deepest stack position.  No changes needed to the per-call serialisation (`_translate_anon_fn`) or the lift-side env construction (`_compile_lifted_closure`) — both already iterate the captures list in order; the fix is to make that order correct.

  New test classes `TestIndexExprOfFnCall614` (3 tests) and `TestNonContiguousCapture615` (4 tests) in `tests/test_codegen_closures.py` cover all five concrete failure shapes plus a baseline that prevents regression of the case that was previously coincidentally working.

### Added
- **`examples/life.vera`** — Conway's Game of Life as a real-world Vera program: 80×22 grid, three classic patterns (Gosper Glider Gun, R-pentomino, Pentadecathlon) interacting, recursive `run_loop` driven by `<IO>` for animation timing, ANSI cursor-control rendering.  Demonstrates the canonical iterative shape (nested `array_mapi` over `array_mapi`, capturing the whole grid into the closure so `count_neighbors` can read each cell's eight neighbours), and carries the formal Conway B3/S23 transition rule on `next_cell`'s `ensures` clause — the verifier discharges all 32 contracts at Tier 1 by symbolic substitution, so any future edit that breaks the rule fails verification before it can run.  The first agent-written Conway's Life that runs cleanly end-to-end on Vera.

### Changed
- **ROADMAP.md** — stabilisation tier reworked: added [#602](https://github.com/aallan/vera/issues/602) (String-interp WASM `i64`/`i32` mismatch) and [#604](https://github.com/aallan/vera/issues/604) (five prelude combinators silently skipped from WASM compile) at the top of the queue as the codegen residue from the life.vera campaign.  Existing items renumbered; agent-integration tier deferred behind seven stabilisation items rather than five.  Also dropped closed entries for [#595](https://github.com/aallan/vera/issues/595) (upstream [wasmtime-py#337](https://github.com/bytecodealliance/wasmtime-py/pull/337) merged 2026-05-07) and [#478](https://github.com/aallan/vera/issues/478) (closed 2026-04-16; HISTORY entry existed but ROADMAP row had not been pruned at close time).
- **HISTORY.md** — opened **Stage 12: After the Game of Life** with framing intro covering the four campaign-residue patterns (scale-only bugs, walker-completeness gaps, browser-runtime gaps, codegen-side silent feature gaps); trimmed the v0.0.135–v0.0.138 Stage 11 entries to the Stage 1/5/9 single-sentence style.

### Documentation
- **SKILL.md** — three doc fixes surfaced by an agent writing Conway's Game of Life from scratch on current main.  `array_length`'s SKILL comment updated from *"returns Int (always >= 0)"* to *"returns Nat (the array length, flows to either Nat or Int positions)"* to match user-visible behaviour (the type checker permits `Int <: Nat` via verifier-enforced refinement, so the result flows freely into either).  `array_fold` example gains a three-line comment making the closure shape explicit (`fn(@Acc, @Elem -> @Acc)` with the rightmost-is-`.0` derivation), so agents no longer have to write a probe to determine the parameter order.  New "Tuples" subsection under "Composite types" showing `Tuple(...)` construction and `match` destructuring — previously SKILL mentioned `@Tuple<Int, String>` only as a type with no construction example, leading agents to hunt for tuple-literal syntax that doesn't exist and abandon valid approaches.

### Tooling
- **`scripts/check_skill_examples.py`** allowlist re-anchored after the SKILL line offsets shifted; one stale redundant entry pruned (the Non-exhaustive Match section had three allowlist entries but only two actual code blocks); one mis-anchored entry corrected (a "bare `@Int + @Int`" allowlist entry was parked on a parseable full-function example, suppressing it).

### CI
- **Test job parallelised with `pytest-xdist`** — added `pytest-xdist>=3.6` to `[dev]` extras; CI's `pytest` invocation now uses `-n auto` to fan tests across worker processes.  Local measurement (8-core Mac): full 3,752-test suite drops from **90.7s → 15.6s** (5.8× speedup, all tests pass).  GitHub Actions 2-core runners will see roughly half that.
- **Eliminated duplicate suite run on the coverage cell.**  The `test (ubuntu-latest, 3.12) + coverage` cell previously ran `pytest -v` (full suite, ~3–4 min) followed by `pytest --cov=vera ...` (full suite again, ~5 min) — the entire suite executed twice.  Restructured to run a single `pytest -v -n auto --cov=vera ...` invocation on that cell, keeping coverage instrumentation but cutting the wall time roughly in half.  Combined with xdist, the gating cell is expected to drop from ~8 min to ~3 min.

## [0.0.138] - 2026-05-07

### Fixed
- **[#593](https://github.com/aallan/vera/issues/593)** — Conway's Life string corruption from generation 1+ at 12×30 (the residual bug acknowledged at v0.0.137 release).  Root cause: `_compile_lifted_closure` in `vera/codegen/closures.py` only emitted the closure's return-value `gc_shadow_push` when the closure body itself allocated (`ctx.needs_alloc=True`).  But `_translate_array_map` and `_translate_array_mapi` in `vera/wasm/calls_arrays.py` *always* emit a per-iteration `global.get $gc_sp; i32.const 4; i32.sub; global.set $gc_sp` after each `call_indirect` when the element type is heap-pointer-like (the `b_needs_unwind` path at lines 649-655 and 1430-1439).  That pop assumed the closure pushed.  When a closure body is non-allocating but returns a heap pointer — e.g. `fn(@Bool -> @String) { render_cell(@Bool.0) }` where `render_cell` returns String literals from the data segment — there was no push, but the loop popped anyway, dropping `$gc_sp` *below* the surrounding function's prologue baseline.  Subsequent shadow-stack pushes then overwrote slots that were holding still-live roots, so the next GC mark phase missed those roots and swept their referents.  Manifested as silent string corruption (the original Conway's Life symptom — strings render with NULL or U+FFFD bytes interleaved) or as `call_indirect` "out of bounds table access" trap at smaller scales (the nested `array_map` of String-returning closure landed differently depending on heap layout).

  Fix: lift the return-value push out of the `if ctx.needs_alloc:` branch in `_compile_lifted_closure`.  Always push the return-value root when the return type is a heap pointer (i32_pair or i32 ADT), regardless of whether the body allocated.  The non-allocating branch needs no `gc_sp` save/restore — the body has nothing to clean up — it just intercepts the return value to publish it as a root, balancing the caller's per-iteration unwind.

  New `TestClosureReturnShadowPushBalance` test class in `tests/test_codegen_closures.py` covers four shapes: positive regression (correct output at small scale), behavioural under `VERA_EAGER_GC=1` for both flat `array_map` and recursive Life-style nested rendering, and a structural assertion that the WAT for a non-allocating String-returning closure contains the `gc_shadow_push` epilogue.  Both the agent-rebuilt minimal reproducer and the user's original 12×30 `life_full_program.vera` now run all 200 generations cleanly with zero U+FFFD corruption.

### Added
- **`VERA_EAGER_GC=1`** environment variable — diagnostic build knob that prepends an unconditional `call $gc_collect` to every `$alloc` invocation, surfacing latent missing-shadow-root bugs immediately rather than only at scale.  Documented in the new top-level [`ENVIRONMENT.md`](ENVIRONMENT.md) along with the full catalogue of `VERA_*` environment variables (eight total: four Inference provider keys, two Inference selection knobs, the existing `VERA_JS_COVERAGE` browser-test knob, and the new `VERA_EAGER_GC` debug knob).  This was the diagnostic that converted the #593 investigation from "static analysis can't find a smoking gun" to "the very first iteration of the rebuilt Life crashes with a clear root-imbalance signature".  Worth keeping permanently as a debugging aid for any future GC-rooting regression.

### Documentation
- New top-level **[`ENVIRONMENT.md`](ENVIRONMENT.md)** centralising the eight `VERA_*` environment variables (previously scattered across `README.md`, `AGENTS.md`, `TESTING.md`, `CONTRIBUTING.md`, and `CLAUDE.md`).  Cross-linked from the documents that previously had only one-line mentions, so future env vars have one canonical home.

## [0.0.137] - 2026-05-07

### Fixed
- **[#588](https://github.com/aallan/vera/issues/588)** — Indexing a *captured* `Array<T>` inside a closure body no longer produces invalid WASM.  Pre-fix the `_walk_free_vars` free-variable detector in `vera/wasm/closures.py` had no `IndexExpr` branch — when the walker hit `coll[idx]` inside a closure body, the `coll` SlotRef referencing a captured outer slot was never recognised as a free variable.  The closure-lift's `captures` list came back empty, body translation failed (the SlotRef couldn't be resolved against an empty capture-only env), and `_compile_lifted_closure` returned `None` — but the call site at `_translate_apply_fn` had already emitted a `call_indirect` to the now-absent function-table entry.  Result: `unknown table 0: table index out of bounds` at WASM validation (flat case) or `undefined element: out of bounds table access` / `indirect call type mismatch` at runtime (nested case where the dispatch landed in-bounds on a wrong-typed function).  Fix adds the missing `IndexExpr` branch plus seven other AST node types that were silently falling through with the same bug class: `ArrayLit`, `InterpolatedString`, `HandleExpr` (with handler-clause param scoping), `AssertExpr` / `AssumeExpr`, `ForallExpr` / `ExistsExpr`, and `ModuleCall`.  Each silently dropped capture references inside its sub-expressions.  New conformance test `ch05_capture_array_index.vera` covers flat, nested, and combined-with-FnCall positions.

  Note: the issue body acknowledged that scaling to a full Conway's Game of Life implementation may have additional triggers beyond captured-array indexing.  Both documented `repro_min.vera` and `repro_nested.vera` reproducers pass post-fix.  The remaining full-Life corruption (string-output corruption appearing from generation 1+ at 12×30 grid scale) is a separate not-yet-isolated bug class tracked separately as a follow-up, and is masked from the user as a Python traceback by the v0.0.136 `errors="replace"` defensive layer (surfaces as U+FFFD chars in output rather than crashing).

- **`IO.sleep` no longer escapes `KeyboardInterrupt` as a raw Python traceback** when Ctrl-C arrives during the wait.  Pre-fix, `host_sleep`'s `time.sleep(ms / 1000.0)` let `KeyboardInterrupt` propagate up through wasmtime's trampoline as a "python exception" cause and the user saw a multi-line Python traceback ending in `KeyboardInterrupt`.  Same `WasmTrapError` contract violation class as #589's `UnicodeDecodeError` escape (#516 / #522 / #547 — runtime traps must surface as Vera-native errors).  Discovered when a user Ctrl-C'd a Conway's Life animation that uses `IO.sleep(120)` between frames.  Fix: `host_sleep` catches `KeyboardInterrupt` and raises `_VeraExit(130)` (conventional SIGINT exit code, 128 + signal-2) which is unwrapped at the top of `execute()` as a clean `ExecuteResult` with `exit_code=130`.  New `TestHostSleepKeyboardInterrupt` test class in `tests/test_runtime_traps.py` with one structural assertion (the guard is wired up at the source level) plus one behavioural test (synthetic `KeyboardInterrupt` → `_VeraExit(130)` conversion verified end-to-end with `unittest.mock.patch`).  A separate macOS malloc abort can still fire during wasmtime/ctypes cleanup after the clean exit; that's tracked as [#595](https://github.com/aallan/vera/issues/595) (cleanup-path issue, not data-integrity).

## [0.0.136] - 2026-05-06

### Fixed
- **[#586](https://github.com/aallan/vera/issues/586)** — `apply_fn(closure, ())` on a `(Unit -> X)` closure no longer trips a WASM type mismatch.  Pre-fix, `_translate_apply_fn` in `vera/wasm/closures.py` defaulted the value-arg's WASM type to `i64` whenever `_infer_expr_wasm_type` returned `None` — but it returns `None` for both "couldn't infer" and "Unit has no representation", conflating the two cases.  A `UnitLit` arg pushed nothing onto the stack but registered a phantom `i64` param in the call_indirect signature.  The closure-lift side correctly skips Unit params, so the two ends disagreed and validation rejected the call with `expected i64, found i32` (the `func_table_idx` landing where the phantom value-arg was expected).  Fix is three lines: change `arg_wasm_types.append(wt or "i64")` to `elif wt is not None: arg_wasm_types.append(wt)` so Unit args contribute zero entries to the sig.  Same falsy-pitfall pattern as #584's `_fn_ret_types` filter.  New conformance test `ch05_unit_arg_closure.vera` covers no-capture, Int-capture, and Array-capture variants.
- **[#589](https://github.com/aallan/vera/issues/589)** — `host_print` / `host_stderr` / `host_contract_fail` / `_read_wasm_string` / `vera/wasm/markdown.py::_read_string` no longer crash with a raw Python `UnicodeDecodeError` when an upstream codegen bug produces a corrupt String `(ptr, len)` pair pointing at non-UTF-8 bytes.  Pre-fix, the unhandled exception escaped through wasmtime's trampoline as a "python exception" cause and the user's CLI saw a 30+ line Python traceback ending in `UnicodeDecodeError: 'utf-8' codec can't decode byte 0xc1`.  A user-level program must never produce a Python traceback regardless of what the program does — this is the WasmTrapError contract from #516 / #522 / #547 applied to the UTF-8-decode paths.  Fix is per-site `errors="replace"` so invalid bytes surface as U+FFFD replacement characters in the user's output instead.  The String-return decoder in `execute()` (added by v0.0.135) was previously try/except → pointer fallback, which silently mutated the return type from `str` to `int` when bytes weren't valid UTF-8 — that fallback was a worse silent failure than visible U+FFFD chars (downstream consumers printed an integer where a string was expected) and is now also `errors="replace"`.  Surfaced by [#588](https://github.com/aallan/vera/issues/588) (captured-Array-indexing in closure produces corrupt String pointers); fixing #588 removes the most common trigger but the defensive-coding hygiene applies regardless of source.  New `TestHostPrintInvalidUtf8589` test class in `tests/test_runtime_traps.py` covers all six affected sites with structural assertions plus an end-to-end wasmtime-trampoline contract test using a synthetic WAT module that imports `vera.print` and calls it with raw invalid UTF-8 bytes.

## [0.0.135] - 2026-05-06

### Fixed
- **`vera run` on String-returning `main` now prints the actual string** instead of a heap pointer.  Pre-fix, a public `main(@Unit -> @String)` returning `"hello"` printed e.g. `147492` (the first half of the i32_pair return — the data pointer in linear memory).  Post-fix, `execute()` decodes the UTF-8 bytes from `memory[ptr:ptr+len]` and stores the decoded `str` in `ExecuteResult.value`, which the CLI then prints directly.  Implementation: new `CompileResult.fn_string_returns: set[str]` populated by `compile_program` from each FnDecl's return type (resolving aliases via `_return_type_is_string` so `type Greeting = String` participates), checked in `execute()` to decide whether to decode.  Array<T> returns deliberately keep the bare-pointer fallback — their bytes-at-ptr aren't UTF-8 and would need element-aware formatting to render meaningfully (separate scope).  `ExecuteResult.value` type widens to `int | float | str | None`; no test breakage outside the one assertion that was checking for the pre-fix pointer value (now updated to assert the decoded str).
- **[#568](https://github.com/aallan/vera/issues/568)** — `url_parse(":foo")` now returns `Err("missing scheme")` instead of `Ok` with an empty scheme that round-tripped through `url_join` as bare `"foo"` (losing the leading colon).  Fix is RFC 3986 §3.1-aligned: rejects `colon_pos == 0` in `_translate_url_parse` (`vera/wasm/calls_encoding.py`) right after the colon-scan loop, before any further processing.  Five lines of WAT plus comment; no changes to `url_join` (the `s_len > 0` gate stays, since post-fix it can never see an empty scheme).  We don't yet enforce the full ALPHA / [ALPHA / DIGIT / "+" / "-" / "."]* scheme grammar — that's a wider RFC-conformance follow-up — but the empty-scheme case alone is the only one that lost its leading colon in the round-trip.  Existing `ch09_url_parsing.vera` extended with a `test_parse_empty_scheme` case asserting the new Err return.
- **[#584](https://github.com/aallan/vera/issues/584)** — User-defined `@Unit`-returning fn call in non-tail block-statement position no longer emits invalid WAT.  `vera/wasm/context.py::_is_void_expr` previously recognised `IO.*` qualified calls, `UnitLit`, effect-op `FnCall`s, and compound expressions as void but missed `FnCall` to user-declared `@Unit` fns — the surrounding statement-sequencer fell through to "produces a value", emitted a stray `drop`, and failed WASM validation with `expected a type but nothing on stack`.  Fix expands the codegen registry (`_fn_ret_types` filter in `vera/codegen/functions.py`) to include Unit-returning fns explicitly with `None`, then adds a clause to `_is_void_expr` that recognises them.  Recursive cases (Unit fn nested inside `if`/`match` arms in non-tail position) come for free via the existing recursion.  The natural `render(grid); IO.sleep(120); recurse(...)` shape now compiles cleanly whenever `render` is a user helper.
- **[#583](https://github.com/aallan/vera/issues/583)** — Type aliases over `Array<T>` no longer break WASM codegen.  `_is_pair_type_name` in `vera/wasm/inference.py` did string-pattern matching on unresolved alias names, so `type Row = Array<Bool>` left "Row" unrecognised as a pair type — SlotRefs to `@Row.0` only emitted the pointer (not pointer + length), and let-bindings or parameters typed `@Row` fell through to silent E602 skips.  Fix converts `_is_pair_type_name` to an instance method that resolves aliases via `_resolve_base_type_name` first; complementary alias resolution added in `_translate_array_lit` (so `[@Row.0, @Row.0]` lays out elements at the correct stride) and `_infer_index_element_type_expr` (so `@Row.0[1]` resolves the element type correctly).  Aliases in parameter, let-binding, indexing, and array-literal-element positions all work now.

### Documentation
- **SKILL.md sandbox-install affordance** — observed in the wild that a Claude.ai sandboxed instance reading the existing Installation section concluded "Vera isn't available in this sandbox" and fell back to "write code the user can run locally" without trying the install steps.  Added an explicit note in the Installation section telling agents running in sandboxes (Claude.ai, Code Interpreter, container-based execution environments) that the standard `git clone + pip install -e .` works there too — sandboxes typically have Python, `git`, `pip`, and outbound network — and to run + verify before concluding the toolchain is unavailable.  Also flagged the `pip install vera` PyPI footgun: that name resolves to an unrelated ERAV citizen-science library, not us; install from the GitHub source clone.

## [0.0.134] - 2026-05-06

### Documentation
- **Post-campaign consistency sweep** — `ROADMAP.md` near-term-priorities section reframed from the now-closed bug-killing campaign to an agent-integration push (LSP server [#222](https://github.com/aallan/vera/issues/222), `vera context` [#523](https://github.com/aallan/vera/issues/523), `Inference.complete` token/temperature controls [#370](https://github.com/aallan/vera/issues/370)).  `HISTORY.md` Stage 11 release table compacted — entries v0.0.119–v0.0.134 had drifted to 2–3× the density of Stage 5–9 entries with implementation details and parenthetical asides that didn't match the established style.  `SKILL.md` "Known Bugs and Workarounds" cleaned: dropped three closed-issue rows ([#475](https://github.com/aallan/vera/issues/475) / [#487](https://github.com/aallan/vera/issues/487) / [#535](https://github.com/aallan/vera/issues/535) all closed in v0.0.129–v0.0.131), rewrote the closure-capture subsection that was telling agents to use a now-obsolete "lift to a helper" workaround for pair-type captures (#535 closed in v0.0.130), added the still-open [#568](https://github.com/aallan/vera/issues/568) (`url_parse` leading-colon drop) for parity with `KNOWN_ISSUES.md`.  Net delta across the three commits: −108 lines, with SKILL.md no longer leading agents to write workarounds for bugs that no longer exist.

### Fixed
- **Active reclamation of host-store handles — closes [#573](https://github.com/aallan/vera/issues/573), [#575](https://github.com/aallan/vera/issues/575), [#576](https://github.com/aallan/vera/issues/576), [#579](https://github.com/aallan/vera/issues/579)**.  Pre-fix, every `map_new` / `map_insert` / `map_remove`, every `set_new` / `set_add` / `set_remove`, and every Decimal arithmetic op allocated a fresh entry in the corresponding Python-side store (`_map_store` / `_set_store` / `_decimal_store` in `vera/codegen/api.py`) and never released transient predecessors *within a single `execute()` call*.  A 10 000-iteration `array_fold` over `map_insert` left 10 001 entries in the store at `execute()` exit.  Each store is local to one `execute()`, so the leak doesn't accumulate across separate calls — but a single long-running call (a server's request loop running inside one `execute()`, an interactive session, a Game-of-Life-style program with many generations) could exhaust memory monotonically.

  Post-fix: the heap-wrap-as-ADT design from #573's body, applied to all three types in one PR.  Every `Map<K, V>` / `Set<T>` / `Decimal` value is now a pointer to an 8-byte wrapper ADT on the GC heap (tag at offset 0, raw host handle at offset 4).  Wrappers register with a new 64 KiB wrap-table region in linear memory at allocation; Phase 2c of `$gc_collect` walks the wrap table and fires a new `host_decref_handle(kind, handle)` host import for every wrapper that was unmarked, evicting the corresponding entry from the appropriate store.  Survivors are compacted in place so the table tracks live wrappers, not total allocations.

  **Infrastructure** (one-time, shared across all three types):
  - `vera/codegen/assembly.py` — new wrap-table region (gated on `_needs_wrap_table`), `$register_wrapper` helper, Phase 2c walk in `$gc_collect`, `host_decref_handle` import declaration, `register_wrapper` export so host-side JSON/HTML parsers and Decimal helpers can register wrappers from Python.
  - `vera/codegen/api.py` — `host_decref_handle(kind, handle)` Python implementation dispatching on `kind` (1=Map, 2=Set, 3=Decimal) to the appropriate `*_store.pop`.  New `_wrap_handle(caller, kind, raw)` helper for cases where the host has already obtained a raw handle (e.g. `decimal_from_string` constructing `Option<Decimal>`).
  - `vera/browser/runtime.mjs` — full mirror: `host_decref_handle` dispatcher, `wrapHandle(kind, raw)`, all three kinds.
  - `ExecuteResult.host_store_sizes` — new field exposing post-execution store population so tests can verify reclamation without linker introspection.

  **Per-type call-site migration** (`vera/wasm/calls_containers.py`):
  - **Map** (8 ops): wrap on `map_new` / `map_insert` / `map_remove`; unwrap on `map_get` / `map_contains` / `map_size` / `map_keys` / `map_values` (closes #573 phase 1).
  - **Set** (6 ops): wrap on `set_new` / `set_add` / `set_remove`; unwrap on `set_contains` / `set_size` / `set_to_array` (closes #575).
  - **Decimal** (10 ops): wrap on `decimal_from_int` / `_from_float` / `_neg` / `_add` / `_sub` / `_mul` / `_round`; unwrap on `_to_string` / `_to_float` / `_eq` / `_compare`.  `decimal_from_string` and `decimal_div` return `Option<Decimal>` constructed host-side; their inner Decimal handle is wrapped via `_wrap_handle` before being stuffed into the Some payload (closes #576).

  **GC-rooting hygiene**:
  - `vera/wasm/helpers.py` — `_HOST_HANDLE_TYPES` is now empty (was `{Map, Set, Decimal}`).  All three are real Vera-heap pointers post-#573 and MUST be shadow-stack-rooted across allocating calls; the `_is_host_handle_type` exclusion would have left them vulnerable to mid-call sweep.
  - The wrapper-allocation helper (`_emit_wrap_handle` in `calls_containers.py`) now shadow-pushes the new wrapper pointer immediately after construction, matching the existing ADT-constructor pattern in `vera/wasm/data.py`.  Without this, nested expressions like `decimal_add(decimal_from_int(a), decimal_from_int(b))` would be unsafe — the inner wrapper sits on the operand stack while the second `decimal_from_int` invokes `$alloc`, and a GC fire there would sweep the unmarked wrapper.

  **JSON / HTML internal Map wrapping** (closes a JObject / HtmlElement coupling):
  - `vera/codegen/api.py` — `_alloc_map_wrapper(caller, dict)` allocates the dict in `_map_store` AND wraps the resulting handle.  Used by `write_json` (JObject) and `write_html` (HtmlElement attrs) so the i32 stored in those ADT fields is a wrapper pointer, type-compatible with user-level `map_get` / `map_contains` calls (which now expect wrappers and unwrap with `i32.load offset=4`).
  - `vera/wasm/json_serde.py`, `vera/wasm/html_serde.py` — `write_*` use the wrapping `map_alloc(caller, dict)` signature; `read_*` unwrap before looking up the host store.

  **Tests** (`tests/test_codegen.py::TestHostHandleReclamation573`): ten regression tests covering all three types — chain-reclaims-transients (10K Map, 10K Set, 5K Decimal) plus value-correct-after-pressure (Map, Set, Decimal) plus the JObject case proving JSON/HTML internal Maps are reclaimed too plus a structural pin (`test_register_wrapper_has_compaction_slow_path`) that the slow-path WAT is wired up correctly.

  **#579 — `$register_wrapper` slow path before trap.**  Pre-fix the function trapped with `unreachable` the moment the wrap-table filled (4 096 simultaneously-live entries) — even if compaction would have freed thousands of dead entries.  Post-fix the slow path roots the in-flight wrapper on the shadow stack, calls `$gc_collect` (which runs Phase 2c compaction), pops the root, and re-checks; only if the table is still full after compaction does it trap.  Bounded in practice by heap fill rate, but the slow path covers wrapper-heavy workloads with low heap pressure (e.g. tight loops creating throwaway Map/Set/Decimal values that go dead before the next iteration).  Adds ~20 lines of WAT plus a structural test pinning the wiring.

### Updated
- `tests/test_codegen.py::TestOpaqueHandleParamRooting347` — three rooting tests flipped from "param 0 must NOT be shadow-pushed" to "param 0 MUST be shadow-pushed after #573".  All three host-handle types (Map, Set, Decimal) lower to wrapper-ADT pointers post-fix and require GC rooting.
- `tests/test_codegen.py::TestArrayFoldHandleRooting490` — `_assert_handle_not_extra_rooted` flipped to `_assert_handle_extra_rooted_after_573`.  `array_fold` and `array_map` accumulators / elements of type Decimal now MUST emit per-iteration root pushes (was: must not).

## [0.0.133] - 2026-05-05

### Fixed
- **Iterative array builders no longer leak the closure return-value root — closes [#570](https://github.com/aallan/vera/issues/570)**.  The lifted-closure epilogue (`vera/codegen/closures.py`) restores its entry `$gc_sp` and then, when the return type is a heap pointer (Vera ADT, `String`, `Array<T>`), pushes the return as a fresh root so generic stash-then-GC callers stay sound.  The iterative array builders consume the return synchronously (store into a rooted `dst[idx]`, or in-place overwrite a rooted accumulator slot), so the per-call root is redundant — and accumulating one leaked slot per iteration overflowed the 16 KiB / 4 096-entry shadow stack.  Pre-fix symptom: a 5 000-element `array_map<_, ADT>` trapped at `unreachable` inside `gc_shadow_push` around iteration 4 000.  Fix is per-callsite (`vera/wasm/calls_arrays.py`):
  - **`array_map`** and **`array_mapi`**: emit a 4-byte `$gc_sp` decrement after storing the return into `dst[idx]`.
  - **`array_fold`**: emit the same 4-byte unwind *before* the `gc_sp - 8` overwrite math that updates the rooted-accumulator slot.  Without this, the second iteration's overwrite addressed the previous-call's leaked slot instead of the accumulator's pre-call slot — a second symptom of the same bug class that this fix incidentally closes.
  - **`array_sort_by`**: same 4-byte unwind after the comparator's `Ordering` tag is read via `i32.load offset=0`.  Insertion sort issues up to `n*(n-1)/2` comparisons, so the leak surfaces at ~200 reverse-sorted elements (well past the shadow-stack budget).
  Builders that take a Bool-returning predicate (`array_filter`, `array_find`, `array_any`, `array_all`) and builders without a callback (`array_flatten`, `array_reverse`, `array_range`) are unaffected — `Bool` is excluded from the closure's `ret_is_pointer` flag, so no post-restore root push happens.  New `TestIterativeBuilderShadowStack` (4 tests in `tests/test_codegen_closures.py`) covers each fixed builder at the size that previously overflowed.

## [0.0.132] - 2026-05-05

### Fixed
- **Opaque-handle GC-rooting hygiene — closes [#347](https://github.com/aallan/vera/issues/347) and [#490](https://github.com/aallan/vera/issues/490)** (#346 closed as superseded by [#573](https://github.com/aallan/vera/issues/573) — see Note below).  Two related cleanups around how `Map`, `Set`, and `Decimal` opaque handles are treated by the codegen's GC-rooting heuristics.  Shared infrastructure: a new `_is_host_handle_type` classifier in `vera/wasm/helpers.py` distinguishes types that lower to i32 indices into Python-side host stores from real Vera-heap pointers.
  - **#347 — opaque handle parameters no longer pushed onto the GC shadow stack**.  Pre-fix `vera/codegen/functions.py` and `vera/codegen/closures.py` excluded only `Bool` / `Byte` from `gc_pointer_params`, so a `Map<K, V>` / `Set<T>` / `Decimal` parameter (i32 handle index) was treated as a heap pointer and pushed onto the shadow stack at every function entry.  Wasted shadow-stack space; a handle value that landed in the heap-pointer range with valid alignment would have caused the conservative mark phase to spuriously mark an unrelated heap object as live (memory retention, not corruption).  Post-fix the new classifier excludes opaque handles at four rooting decision sites: top-level params + return type in `functions.py`, closure params + captures + return type in `closures.py`.  New `TestOpaqueHandleParamRooting347` regression test pins the fix structurally — a function taking a `Map<K, V>` parameter no longer contains the canonical `local.get $p0; i32.store` shadow-push idiom in its WAT.
  - **#490 — `array_fold` and `array_map` no longer over-root opaque-handle accumulators**.  Pre-fix the `u_is_adt`/`t_is_adt` heuristics in `vera/wasm/calls_arrays.py` (`u_wasm == "i32" and u_type not in ("Bool", "Byte") and not u_is_pair`) classified `Map`/`Set`/`Decimal` accumulators as ADT pointers and emitted shadow-stack rooting around the loop body.  Post-fix the same `_is_host_handle_type` classifier excludes them.  New `TestArrayFoldHandleRooting490` (2 tests): a structural pin via `global.set $gc_sp` count parity between Int and Decimal accumulators, plus a functional regression that the fold still produces the right result.

### Note — `#346` superseded by `#573`
- The original issue tracker grouped `#346 (host-store leak)` with `#347` and `#490` under "opaque-handle hygiene", but `#346` is a fundamentally different problem: it requires *active reclamation* of unreachable handles from Python-side stores, while `#347` and `#490` are purely *codegen-time* decisions about which i32 values to push to the shadow stack.  An earlier draft of this PR attempted to close all three by adding a `host_gc_sweep` host import that walked the live heap + shadow stack to identify reachable handle indices, but the resulting design (six interlocking pieces — heap walk, shadow-stack scan, transitive closure, re-entrancy guard, let-binding shadow_push, JSON/HTML emission gates) had too much complexity for the practical impact.  Per-`execute()` handle leaks are bounded (Python GC reclaims at `execute()` exit), and Vera doesn't yet have long-running execution contexts where the leak would matter in practice.  `#346` was closed as superseded by [#573](https://github.com/aallan/vera/issues/573), which tracks the recommended follow-up: heap-wrap-as-ADT (return a Vera-heap `MapHandle(i32)` from each handle-creating op so the existing mark-sweep GC handles reclamation via a destructor callback) — a single mechanism that integrates with mature infrastructure rather than running parallel to it.

## [0.0.131] - 2026-05-05

### Fixed
- **GC infrastructure batch — `$alloc` multi-page grow + worklist size + overflow trap (closes [#487](https://github.com/aallan/vera/issues/487) and [#348](https://github.com/aallan/vera/issues/348))**.
  - **`$alloc` computes pages-needed for `memory.grow`** (`vera/codegen/assembly.py` `_emit_alloc`, fixes #487). Pre-fix, when `heap_ptr + total > memory.size * 65536`, `$alloc` unconditionally called `memory.grow 1` regardless of how many pages were actually needed; a single allocation request more than ~64 KB past the current memory boundary fell through to the bump-allocate and trapped on out-of-bounds memory access. Post-fix: compute `pages_needed = ceil(((heap_ptr + total) - memory.size * 65536) / 65536)` and grow by that many pages in a single call. Verified against the issue's reproducer (two 50K-element `Array<Int>`s, ~800 KB total) which now allocates cleanly. New `TestLargeAllocGrow487` (2 tests) covers the 50K case and a small-allocation regression pin.
  - **GC mark-phase worklist quadrupled to 64 KiB + trap on overflow** (`vera/codegen/assembly.py` `_emit_gc_collect` + `gc_worklist_size` constant, fixes #348). Pre-fix the worklist was 16 KiB / 4096 entries; both push branches (Phase 2 seed and Phase 2b mark scan) silently dropped pushes when full, leaving reachable objects unmarked which the sweep phase then freed — a real use-after-free hole for object graphs holding more than ~4 K reachable pointers. Post-fix: worklist increased to 64 KiB / 16 384 entries (covers reasonable program shapes), and both push branches now `unreachable` on overflow rather than silently dropping. The combined effect: most programs that previously fit have ~4× headroom, and any residual overflow is a clean WASM trap rather than silent corruption. New `TestWorklistOverflow348` (3 tests) covers a moderate-graph runtime case plus structural pins on the new GC region size and trap shape. Two existing tests (`test_heap_ptr_starts_after_strings`, `test_heap_ptr_zero_without_strings`) updated for the new heap base offset (32 768 → 81 920 bytes from the worklist resize).
- **Surfaced separately**: `array_map` (and likely sibling iterative builders) overflow the GC shadow stack at ~4 000 heap-allocating elements ([#570](https://github.com/aallan/vera/issues/570)). Found while writing the natural runtime regression test for #348 (a 5 000-element `Array<Box>`); the failure was on the shadow-stack-overflow `unreachable` inside the lifted closure, not the worklist trap. Pre-existing, separate subsystem — tracked for follow-up; the #348 runtime regression is covered by a 1 000-element graph (within the shadow-stack budget) plus structural WAT pins.

## [0.0.130] - 2026-05-05

### Fixed
- **Pair-type closure captures (`String`, `Array<T>`) preserve their length field — closes [#535](https://github.com/aallan/vera/issues/535)** (residual of [#514](https://github.com/aallan/vera/issues/514); v0.0.121 fixed nested closures and primitive/ADT captures, this release closes the residual pair-type subset).
  Pre-fix, `vera/wasm/closures.py::_walk_free_vars` resolved the wasm type of every capture via `_type_name_to_wasm`, which collapses any composite type to a single `"i32"`. `_translate_anon_fn` then allocated 4 bytes per capture and stored only the ptr half of pair-typed values; `_compile_lifted_closure` read back only the ptr and the body got the len from adjacent struct memory (typically zero). Operations on a captured `Array<T>` or `String` therefore silently saw an empty value — `array_length(@Array<Int>.0)` returned 0, `string_length(@String.0)` returned 0, and any indexed read into a captured pair worked off ptr=correct/len=0.
  Post-fix, all three sites carry an `"i32_pair"` tag for these captures: `_walk_free_vars` detects `String` / `Array<T>` and overrides the wasm type (without changing `_type_name_to_wasm`, which other callers like `handle_state` and `handle_exn` still need to return the single-slot form); `_translate_anon_fn` allocates 8 bytes per pair field (two consecutive i32 stores at `cap_offset` / `cap_offset + 4`); `_compile_lifted_closure` allocates two consecutive i32 locals (ptr, len), loads both halves, and pushes only the ptr into the slot env — matching the let-binding and parameter conventions so the closure body resolves the pair correctly. GC shadow-push was extended to root the ptr field of pair captures (the len is a byte count, not a heap pointer). New `TestPairCapture535` (5 tests) covers `Array<Int>` capture (returns 21 not 0), `String` capture (returns 15 not 0), ADT capture regression (still works), primitive capture regression (still works), and a mixed-layout test that captures both an `Int` (i64) and an `Array<Int>` (i32_pair) to exercise the field-packing order.

## [0.0.129] - 2026-05-05

### Fixed
- **WASM call translator major bugs — seven correctness fixes close out [#475](https://github.com/aallan/vera/issues/475)** (PR 2 of 2 — Major findings 4-10; Critical findings 1-3 shipped in v0.0.128). All seven fixes were CodeRabbit findings on PR #474's calls.py decomposition; with this release the issue is fully closed.
  - **`array_slice` clamps in i64 before wrapping** (`vera/wasm/calls_arrays.py` `_translate_array_slice`) — same shape as the v0.0.128 `string_slice` fix. Pre-fix, start/end indices were narrowed via `i32.wrap_i64` first and then compared with `arr_len` as i32; a huge positive i64 (e.g. 2^32 + 5) wrapped to a small in-range-looking i32 and the byte-copy read past the array. Post-fix: widen `arr_len` to i64 and use the cross-mixin `_clamp_i64_to_range_then_wrap` helper (shared via Python MRO with `CallsStringsMixin`) to clamp before narrowing. New `TestArraySliceClamp475` (4 tests) covers normal, negative-start, end-beyond-length, and the i64-overflow cases.
  - **`Map<K, Array<T>>` rejected at codegen** (`vera/wasm/calls_containers.py` `_map_wasm_tag` and 11 call sites) — pre-fix, `_map_wasm_tag` returned a placeholder string for any unknown value type, so `Map<K, Array<T>>` would compile but silently treat array values as opaque pointers. `Map<K, Array<T>>.get` returned a raw pointer i32 not a properly-tagged Array, opening a type-system hole downstream. Post-fix: return type changed to `str | None`, with `Array` detection added (`if vera_type.startswith("Array"): return None`). 11 call sites guard against `None` and surface the unsupported feature as a controlled codegen error. New `TestMapArrayValueRejected475` regression test pins the rejection.
  - **`url_parse` / `url_join` round-trip preserves URL shape** (`vera/wasm/calls_encoding.py` `_translate_url_parse` and `_translate_url_join`) — pre-fix, `url_parse` discarded the `has_auth`, `has_query`, and `has_frag` delimiter bits after using them to set component bounds; `url_join` then re-derived delimiter presence from `len > 0`. This conflated `http:path` (no authority) with `http://path` (empty authority) — both joined as `http:///path` — and dropped trailing `?` / `#` when the body was empty. Post-fix: `url_parse` packs the three flag bits plus an explicit-mode sentinel into a previously unused i32 word at struct offset 44; `url_join` reads them back and uses the bits when the sentinel is set, falling back to the legacy `len > 0` heuristic when the sentinel is clear (so direct `UrlParts(...)` data-constructor callers preserve their pre-fix behaviour). New `TestUrlParseJoinRoundTrip475` (5 tests) covers `http:path`, full URLs, query-with-body, empty `?`, and empty `#`.
  - **`base64_decode` rejects `=` outside the padding region** (`vera/wasm/calls_encoding.py` `_translate_base64_decode`) — RFC 4648 only allows `=` in the final 1-2 positions and only when total length % 4 ∈ {2, 3}. Pre-fix the decoder accepted `=` anywhere; `AB=C` decoded with the embedded `=` treated as zero bits, silently producing corrupted output. Post-fix: a position-based check verifies any `=` byte sits at index ≥ `slen - pad`, surfacing a controlled error otherwise. New `TestBase64DecodePadding475` (3 tests).
  - **`parse_nat` / `parse_int` reject embedded spaces** (`vera/wasm/calls_parsing.py` `_translate_parse_nat` and `_translate_parse_int`) — pre-fix the digit loop unconditionally skipped ASCII space bytes mid-number (a misleading "trailing space" comment hid the embedded-space accept). `"1 2"` parsed as 12, `"-1 0"` parsed as -10. Post-fix: leading whitespace is still trimmed (preserving the documented contract) and trailing whitespace is still allowed via a separate post-digit-loop tail-validation block, but a space encountered between digits breaks the digit loop and the tail-validator's "every remaining byte must be a space" check fires. New `TestParseEmbeddedSpaces475` (4 tests) covers normal, leading-space-OK, embedded-space-rejected for both nat and int.
  - **`int_to_string(INT64_MIN)` correct** (`vera/wasm/calls_strings.py` `_translate_to_string`) — pre-fix the digit-extraction loop break used signed `i64.le_s 0`. On the first iteration of negation `-INT64_MIN` overflows back to `INT64_MIN` (still `< 0`) and the loop terminated immediately, printing partial garbage. Post-fix: the loop break uses unsigned `i64.eqz` after extracting digits via `i64.div_u` / `i64.rem_u`, so the unsigned bit pattern walks down to zero correctly. New `TestToStringInt64Min475` (2 tests) covers INT64_MIN and a negative-basic sanity check.
  - **`float_to_string` handles fraction-rounding carry** (`vera/wasm/calls_strings.py` `_translate_float_to_string`) — pre-fix the integer part was emitted first, then `frac_val = round((f - floor(f)) * 1_000_000)` was computed. When the fraction rounded up to exactly 1_000_000 (e.g. `1.9999996`), the integer part `1` was already on the page so output was `1.0` instead of `2.0`. Post-fix: `frac_val` is computed first; when it equals 1_000_000 the integer is incremented and `frac_val` reset to 0 *before* any digits are emitted. New `TestFloatToStringCarry475` (3 tests) covers the carry case, normal fractions, and the full-six-decimals case.

## [0.0.128] - 2026-05-05

### Fixed
- **WASM call translator critical bugs — three safety fixes** ([#475](https://github.com/aallan/vera/issues/475), partial — Critical findings 1, 2, 3 of 10; Major findings 4-10 remain for the next release). Each was a pre-existing bug surfaced by CodeRabbit during PR #474's calls.py decomposition review and tracked since mid-April; this release ships PR 1 of 2 (Criticals) so the safety holes close immediately, with the seven Major correctness fixes following as PR 2.
  - **Memory-safety hole in `string_char_code` closed** (`vera/wasm/calls_strings.py` `_translate_char_code`) — pre-fix, no bounds check before `i32.load8_u`; out-of-range indices read arbitrary WASM linear memory at `ptr_s + (wrapped index)`. The placeholder `_ = len_s  # reserved for future bounds checking` documented the gap. Post-fix: bounds check operates in i64 (`idx < 0 || idx >= len_s_i64`) and traps with `unreachable` *before* narrowing to i32 — so a huge positive i64 value cannot wrap to a small in-range-looking i32 and bypass the check. New `TestCharCodeBoundsCheck475` (5 tests) covers the in-range, negative, at-length, huge-positive, and last-valid-index cases.
  - **`string_slice` clamp-before-narrow** (`vera/wasm/calls_strings.py` `_translate_string_slice`) — pre-fix had no clamping at all (the same `_ = len_s` placeholder pattern). Indices were narrowed via `i32.wrap_i64` first; large positive i64 values silently turned into negative i32 values, which then drove the byte-copy loop into out-of-range memory or produced garbled output. Post-fix: clamp in i64 space (via the new `_clamp_i64_to_range_then_wrap` helper that widens `len_s` to i64, clamps, then wraps) before narrowing. Negative starts clamp to 0, ends past length clamp to length, swapped indices produce empty slices, huge positive indices clamp to length cleanly. New `TestStringSliceClampBefore475` (5 tests).
  - **Expression-bodied `Exn<E>` handler result type** (`vera/wasm/calls_handlers.py` `_translate_handle_exn`) — pre-fix, catch-arm result type was inferred only when `clause.body` was an `ast.Block`; expression-bodied handlers (e.g. `throw(@String) -> None`, `throw(@Int) -> @Int.0 + 1`) left `result_wt = None` and the emitted WAT omitted the `(result T)` annotation, producing invalid WAT that failed validation when the body type was anything other than Unit. Post-fix: use `_infer_expr_wasm_type` (which handles all Expr types including `ast.Block`) for both the catch clause and the body. New `TestExpressionBodiedExnHandler475` (3 tests) covers `Option`-returning, `Int`-returning, and trap-path catch arms.

### Shared infrastructure
- New `_clamp_i64_to_range_then_wrap(max_local_i64)` helper on `CallsStringsMixin` emits the canonical "clamp i64 to [0, max] then wrap to i32" sequence. Used by both `_translate_string_slice` and `_translate_char_code`; will be promoted to a shared location when PR 2 fixes finding 4 (`array_slice` same shape, in `calls_arrays.py`).

### Documentation
- **`@Byte` arithmetic exclusion documented in spec** ([#551](https://github.com/aallan/vera/issues/551) closed as not-a-bug; [#564](https://github.com/aallan/vera/issues/564) filed speculatively) — `vera/types.py` excludes `Byte` from `NUMERIC_TYPES`, so `@Byte - @Byte` (and similar) produce E140 at type-check time. The original #551 framing assumed a runtime underflow hole; investigation showed the checker prevents the construct entirely. Spec §4.4 and §11.2.1 updated to drop the previous "Byte enforcement tracked as #551" caveat in favour of a clear note that Byte arithmetic isn't permitted; user code that needs byte-level arithmetic uses `byte_to_int` / `int_to_byte` round-trip. The forward-looking *feature* (allow Byte arithmetic with verified underflow + overflow guards) is preserved as #564 with full design analysis (pros, cons, trigger conditions, action checklist) under a new ROADMAP `## Speculative` section. New `TestByteArithmeticRejection551` regression test (5 cases) pins the checker behaviour so a future widening of `NUMERIC_TYPES` can't silently re-open the underflow hole without a corresponding extension of the verifier obligation + codegen guard from #520.

## [0.0.127] - 2026-04-29

### Fixed
- **`@Nat` subtraction silent underflow — soundness hole closed** ([#520](https://github.com/aallan/vera/issues/520), closes) — pre-fix, the type system accepted `@Nat - @Nat : @Nat` but the runtime emitted a plain `i64.sub` with no underflow check, so a negative i64 could end up in a `@Nat` slot, undermining any Tier-1-verified contract that relied on `Nat >= 0` (and turning `@Array<T>[@Nat.0]` indexing with a bad `@Nat` into a memory-safety issue). The fix is two-sided: (a) the verifier emits a Tier-1 proof obligation `lhs >= rhs` at every `@Nat - @Nat` site whose result is statically `@Nat` AND at least one operand has `@Nat` *provenance* (slot ref or function return), discharged from preconditions and path conditions via Z3; (b) the codegen emits a runtime guard (`local.set $rhs; local.tee $lhs; local.get $rhs; i64.lt_s; if unreachable end; ...; i64.sub`) on the same set of sites so programs that skip `vera verify` still trap cleanly on underflow rather than silently producing negative `@Nat` values. The two analyses share the helper logic (`_is_static_nat_typed` + `_has_nat_origin_codegen` mirror the verifier's `_is_nat_typed` + `_has_nat_origin`) so the verifier's Tier-1-discharged sites and the codegen-guarded sites agree exactly.

### Path-A scope and follow-ups
- **Pure-literal subtractions like `0 - 1` are intentionally not flagged.** The corpus uses this idiom widely (e.g. `Err(_) -> 0 - 1` and `throw(0 - 1)`) where the result is consumed at `@Int` positions and the upcast is well-defined. The verifier and codegen both require at least one operand to have `@Nat` *provenance* (a slot ref to a `@Nat` slot or a function returning `@Nat`), distinguishing real `@Nat`-flowed subtractions from pure-literal "I want -1 as a literal" idioms.
- **`@Byte` follow-up tracked as [#551](https://github.com/aallan/vera/issues/551)** — the same underflow shape applies to `@Byte - @Byte` (`0..=255` range). Mechanical follow-up once the verifier helper and codegen guard are reusable.
- **Binding-site narrowing tracked as [#552](https://github.com/aallan/vera/issues/552)** — the verifier currently checks the `@Nat >= 0` invariant only at function return positions and at subtraction sites. Narrowing from `@Int` into a `@Nat`-typed let binding or function argument (e.g. `let @Nat = 0 - 1`) is not yet obligation-checked. Architectural generalisation; ships separately so the obligation infrastructure stays focused.

### New error code
- **E502** — `@Nat subtraction underflow obligation not discharged`. Counterexample-bearing diagnostic with rationale, fix suggestion (`requires(@Nat.0 >= @Nat.1)` or guarded if-branch), and spec ref to §4.4 + §11.2.1.

### Spec
- **`spec/04-expressions.md` §4.4** — short clause mirroring the divide-by-zero language: subtraction on unsigned types is undefined behaviour when it would underflow; the compiler SHOULD verify `lhs >= rhs` and MUST insert a runtime check otherwise.
- **`spec/11-compilation.md` §11.2.1** — full treatment with the Tier-1 proof obligation, Tier-3 fallback codegen (`(if (i64.lt_s lhs rhs) (then unreachable))`), the lift-back path via `requires`, and references to #551 (@Byte) and #552 (binding-site generalisation).
- **`spec/11-compilation.md` §11.3.3** — footnote on the operator table pointing back to §11.2.1 so readers of the canonical "what does each operator compile to" reference learn that `@Nat - @Nat` is conditionally guarded.

### Tests
- New `TestNatSubtractionObligation520` in `tests/test_verifier.py` (9 tests): requires-clause discharge, if-guard / path-condition discharge (canonical recursion shape), trivial discharges (`@Nat.0 - 0`, `@Nat.0 - @Nat.0`), unguarded-subtract counterexample, `@Int - @Int` and `@Nat - @Int → @Int` exclusions, partial-requires non-discharge, pure-literal exclusion documenting Path-A scope.
- New `TestNatSubtractionRuntimeGuard520` in `tests/test_codegen.py` (6 tests): underflow traps at runtime, safe subtraction passes through, structural WAT assertions that the guard appears for `@Nat - @Nat` and is absent for `@Int - @Int` and pure-literal `0 - 1`, deep-recursion path-discharged site runs without spurious traps.
- New `tests/conformance/ch04_nat_subtraction.vera` (Section 4.4 / 11.2.1) demonstrating the canonical discharge patterns: explicit `requires`, `if`-guarded recursion, trivial discharges (`a - 0`, `a - a`), and `@Nat - @Int → @Int` exclusion. Verifies at Tier 1 with 17 contracts; corpus is now 82 conformance programs.
- Existing tier-count assertions updated where the new obligations land: `test_recursive_call_decreases_verified` and `test_mixed_tiers` (3 → 4 T1), `test_overall_tier_counts` aggregate (219/26/245 → 222/26/248), `test_mutual_recursion_example_all_t1` (8 → 10 T1).

### Migration
- **Zero corpus migration needed.** Every existing `@Nat - @Nat` site in `examples/` and `tests/conformance/` is guarded by `if @Nat.0 == 0 then base else recursive(@Nat.0 - 1)` and Z3 discharges the obligation from the path condition automatically. External programs that previously verified at Tier 1 may now require explicit `requires(lhs >= rhs)` clauses on functions doing `@Nat - @Nat`; the diagnostic (E502) names the fix and shows the counterexample inputs.

## [0.0.126] - 2026-04-28

### Fixed
- **Tail-call optimization for non-allocating tail-recursive functions** ([#517](https://github.com/aallan/vera/issues/517), closes) — pre-fix, every Vera `call` site emitted a plain WASM `call` regardless of tail-position status, so a tail-recursive function pushed one WASM frame per iteration and trapped with `call stack exhausted` at ~tens of thousands of frames. The documented "iteration is tail recursion" idiom from `SKILL.md` thus silently failed past ~5–10K iterations. The fix is a per-fn analyzer (`vera/codegen/tail_position.py`) that marks `id(FnCall)` AST nodes in syntactic tail position; `_translate_call` emits `return_call $foo` instead of `call $foo` when the call's id is in the marked set AND the callee's WASM return type matches the caller's (required for WASM `return_call` semantics — the signature must match). Non-allocating tail-recursive functions now run in **constant stack space**: the canonical `count_down(50000)` reproducer succeeds, as does a 1M-iteration stress test.

### Tail-position analysis
- **Marking rules** (recursive on the function body):
  - The body's trailing expression IS in tail position.
  - If a sub-expression is in tail position and is an `IfExpr`, both branch bodies are in tail position. The condition is NOT.
  - If a sub-expression is in tail position and is a `MatchExpr`, every arm body is in tail position. The scrutinee is NOT.
  - If a sub-expression is in tail position and is a `Block`, only the trailing expression is in tail position. Statement values (`let` initialisers, `ExprStmt` expressions) are NOT.
  - All other constructs (call arguments, quantifier bodies, `assert`/`assume`, `handle` bodies, `AnonFn`, indexing) are NOT tail-transparent — calls inside them are not in tail position regardless of the parent's status.
- **Type-safety guard at emit time:** WASM `return_call` requires the callee's signature to match the caller's, so the translator falls back to plain `call` whenever the resolved callee's WASM return type doesn't match the current function's return type. The recursive case (call to the same function) trivially matches; cross-function tail calls match when signatures align.

### Allocating-function fallback
- **Allocating functions revert `return_call` → `call`** in a post-process step at the end of `_compile_fn`. WASM `return_call` discards the current frame, which means the GC epilogue (restore `$gc_sp`, unwind shadow-stack pointer slots) never runs. For an allocating function with tail calls, that leaks shadow-stack slots once per iteration and would eventually trap on the next `$alloc` once `gc_sp` passes the worklist boundary — strictly worse than the pre-fix "stack exhausted" trap. Until full GC-aware tail-call support lands ([#549](https://github.com/aallan/vera/issues/549) tracks the follow-up), allocating functions pay the WASM frame cost in exchange for correct shadow-stack management. Non-allocating functions (the common iteration-style tail recursion case) keep the optimization.

### Tests
- New `TestTailCallOptimization517` in `tests/test_codegen.py` (9 tests): 50K-iteration behavioural test (the issue's canonical reproducer), 1M-iteration stress test (pins constant-stack-space behaviour rather than just "deeper than the broken limit"), structural assertion that `return_call $count_down` appears in WAT for the recursive call, structural assertion that a let-bound (non-tail) call emits plain `call`, allocating-function fallback assertion (allocating tail-recursive function emits plain `call` not `return_call`), plus 4 analyzer unit tests covering each tail-transparent construct (Block trailing, both branches of IfExpr, let-value NOT marked, call args NOT marked).
- Existing fixtures in `tests/test_runtime_traps.py` updated for the TCO interaction: the `_DIVIDE_BY_ZERO_USER_FN`, `_CONTRACT_VIOLATION_PROGRAM`, and `_DIVZERO_FOR_FIX` test programs originally had `main` calling the trapping function in tail position, which #517 would now optimize away — discarding `main`'s frame and shortening the backtrace assertions expect to see. The fixtures now bind the call result with `let` and produce it via slot reference, keeping the call non-tail and preserving `main`'s frame on the WASM call stack. Comments document the intentional non-tail shape so a future contributor doesn't "simplify" them back into tail position.

### Improved
- **`stack_exhausted` trap Fix paragraph rewritten** to reflect the v0.0.126 reality. Pre-rewrite: "Vera doesn't yet emit `return_call` ... wait for #517 to ship". Post-rewrite: "Vera compiles tail-position calls to WASM `return_call` ... if you're still hitting this trap the recursion isn't actually in tail position. Restructure with an accumulator parameter so the recursive call is the LAST thing the function does (no work after it, no `let`-binding of its result, no enclosing arithmetic). Allocating functions are an exception ... iterate via `array_fold` / `array_map` (which compile to WASM loops rather than recursion)."

### Documentation
- **KNOWN_ISSUES.md** — #517 row removed (closed); new row added pointing at [#549](https://github.com/aallan/vera/issues/549) (GC-aware TCO follow-up for allocating functions, with restructure/array-fold workarounds).
- **ROADMAP.md** — #517 dropped from the bug-killing campaign queue (closed by this release); intro updated to "eight remain"; priority rows renumbered (#520 promoted to position 1).

## [0.0.125] - 2026-04-28

### Improved
- **Runtime traps now carry per-`kind` `Fix:` suggestion paragraphs** ([#547](https://github.com/aallan/vera/issues/547), closes; finishes [#516](https://github.com/aallan/vera/issues/516) Stage 3) — pre-fix, runtime traps surfaced kind + description + structured backtrace (Stages 1+2), but no actionable remediation paragraph.  Compile-time errors have always carried `description` / `rationale` / `fix` / `spec_ref`; runtime traps now match that surface with a Vera-native Fix paragraph appended after the source backtrace.
- **Refactor: `_classify_trap` returns `(kind, description, fix)`** instead of `(kind, message)`.  The previous shape crammed Fix-shaped hints inline in the message (e.g. `"Out-of-bounds memory access (if the trapping frame is gc_collect, see #515; otherwise check array indexing or string slicing)"`); Stage 3 splits them into clean fields so consumers can render description and fix independently.  New per-kind table `_TRAP_FIX_PARAGRAPHS` in `vera/codegen/api.py` carries the canonical content; empty string for `contract_violation` (the contract message itself already explains what failed) and `unknown` (no specific suggestion possible).
- **`WasmTrapError` gains a `fix: str` field** alongside the existing `kind` / `frames` / `stdout` / `stderr`.  Default `""` for backward compatibility with direct `WasmTrapError(...)` constructors that don't pass the keyword.
- **CLI surface**: text mode appends a `Fix:` block after the `Source backtrace:` block, with the paragraph wrapped to ~76 columns (matching the compile-time `Diagnostic` rendering style).  JSON mode adds a `fix` key to each trap diagnostic alongside `description` / `trap_kind` / `frames` — always present for schema stability, possibly empty.  Empty-string Fix paragraphs suppress the text-mode block entirely (no empty `Fix:` header noise) but still surface as `""` in JSON for shape stability.

### Per-kind Fix paragraph content
- `divide_by_zero` — "Add a precondition `requires(divisor != 0)` on the function performing the division, or guard the division site with a non-zero check.  The Z3 verifier will then prove the division is safe at every call site at compile time."
- `out_of_bounds` — names the two most-likely user causes (array indexing, string slicing) and the runtime-helper escape hatch (file an issue if the trap is inside `gc_collect` / `alloc` / etc.).
- `stack_exhausted` — references [#517](https://github.com/aallan/vera/issues/517) (the open TCO issue) so an agent reading the Fix knows this is a known limitation rather than a bug they should report; will be rewritten to reference `return_call` as a supported feature once #517 lands.
- `unreachable` — names the most-likely cause (non-exhaustive `match`) and the resolution path (add the missing arm explicitly).
- `overflow` — names the i64 range and the canonical remediation (precondition guarded by Z3).

### Tests
- New `TestTrapFixParagraphs547` (6 tests) — text-mode Fix-block surfacing with position-ordering invariant (Fix appears after backtrace), text-mode block suppression for `contract_violation`, JSON-mode `fix` field always-present, JSON `fix` field empty-but-present for `contract_violation`, table-completeness assertion (every kind in the taxonomy has a `_TRAP_FIX_PARAGRAPHS` entry — adding a new kind without its Fix paragraph fails this test immediately), and column-wrap invariant (~76 chars max per line, two-space indent under `Fix:` heading).
- Existing `TestClassifyTrap` (7 tests) updated for the new 3-tuple return shape; per-kind assertions now also verify the Fix paragraph content matches expected substrings (`"requires(divisor != 0)"` for `divide_by_zero`, `"#517"` + `"return_call"` for `stack_exhausted`, etc.).
- `TestWasmTrapError` extended to verify the `fix` field round-trips through the constructor and defaults to `""`.

### Documentation
- **KNOWN_ISSUES.md** — #516 row removed (Stage 3 closes it; the parent #516 was closed by the v0.0.124 PR's "Closes #516 Stage 2" wording, but the doc kept the row open against #516; with #547 closed too the entire row is gone).
- **ROADMAP.md** — #516 / #547 dropped from the bug-killing campaign queue (closed by this release); intro string updated to reflect "nine remain" instead of "ten remain".

## [0.0.124] - 2026-04-27

### Improved
- **Runtime traps now carry a source backtrace** ([#516](https://github.com/aallan/vera/issues/516) Stage 2) — pre-fix, `WasmTrapError` carried only the classified `kind` and the trap message; the user got "Integer division by zero" with no indication of *which* of their functions divided by zero. Stage 2 walks `wasmtime.Trap.frames` after classification, looks each frame's WAT name up in a new `CompileResult.fn_source_map` (built during codegen by `_register_fn` and the closure-lifting pass), and produces a structured backtrace: `[{func, file, line_start, line_end, is_builtin}, …]`, outermost (leaf) frame first to match wasmtime / gdb / Python convention. Per-function granularity, not per-line — wasmtime-py doesn't expose WAT-to-WASM debug-info plumbing, so byte-offset → line mapping isn't viable; "trap inside `divide` (foo.vera:1-5)" is exactly the success criterion the issue calls out.
- **Resolution rules for the trap-frame walker** (`_resolve_trap_frames` in `vera/codegen/api.py`):
  - **Built-ins are tagged, not dropped.** WAT functions named `alloc` / `gc_collect` / `contract_fail`, plus anything starting with `exn_` / `vera.` / `closure_sig_`, are runtime infrastructure with no Vera source. They're surfaced as `<builtin>` rather than reported as missing-source-map entries (which would look like a regression).
  - **Monomorphized generics suffix-strip at the rightmost `$`.** `identity$Int` looks up `identity` because `$` cannot appear in user-written Vera identifiers, so any `$` in a WAT name was inserted by the monomorphizer (`vera/codegen/monomorphize.py::_mangle_fn_name`).
  - **Lifted closures register under `anon_N`.** The closure-lifting pass tags each `$anon_N` with the source span of the original `fn(...)` syntactic site, so a trap inside a closure points at the closure body, not at the synthetic top-level wrapper.
  - **Unknown user-named frames are surfaced with `<unknown>` location, not dropped.** Better to show the WAT name with no location than lose the frame entirely — the user still benefits from knowing which function trapped, and any future source-map gap is diagnosable from the unknown markers.
- **`cmd_run` text-mode rendering** appends a `Source backtrace:` block after the error line. Leading runtime-helper frames (the ones the user can't act on — they trapped inside `$alloc` while serving a user request) are collapsed with a `(suppressed N runtime-helper frames above first user code)` marker so the user sees their own code at the top of the trace. JSON mode adds a `frames` array to each diagnostic with the full structured backtrace (including built-ins, so machine consumers see the full picture).

### Tests
- New `TestResolveTrapFrames516` (7 tests) — unit tests for the resolver in isolation using a `_FakeFrame` shim: user-fn resolution, built-in tagging, built-in-prefix matching, monomorphized base-name fallback, unknown-name surfacing, defensive empty-frames behaviour, leaf-first ordering preservation.
- New `TestTrapSourceBacktrace516` (5 tests) — end-to-end via `cmd_run`: text-mode backtrace surfaces, leaf-first ordering preserved across stream output, JSON envelope includes `frames` array, contract violations carry the same backtrace, direct `execute()` callers also get `WasmTrapError.frames`.
- New `TestSourceMapPopulation516` (3 tests) — light-weight inspection of `CompileResult.fn_source_map`: top-level fns registered, lifted closures registered under `anon_N`, built-in helpers NOT registered (would yield bogus user-frame entries).

### Documentation
- **KNOWN_ISSUES.md** — #516 row updated to note Stage 2 shipped (Stage 3 remains).
- **ROADMAP.md** — #516 row in the bug-killing campaign queue updated; intro string unchanged (the row stays in the queue until Stage 3 ships).

### Stage 3 follow-up
- Tracked as [#547](https://github.com/aallan/vera/issues/547) — per-`kind` `Fix:` suggestion paragraphs to match the compile-time `Diagnostic` shape (description / rationale / fix / spec_ref).  Will be picked up after #517 (TCO) lands so the `stack_exhausted` Fix paragraph can reference `return_call` as shipped rather than as "see #517 for the planned fix".

## [0.0.123] - 2026-04-27

### Fixed
- **`IO.print` writes mirror live to `sys.stdout` in `vera run` text mode** ([#543](https://github.com/aallan/vera/issues/543), closes) — `IO.print` output was buffered in an in-memory `output_buf` (the v0.0.120 implementation of #522 trap preservation) and only flushed to `sys.stdout` after `execute()` returned. That was correct for trap preservation and for `--json` output (where the transcript packs into the envelope), but it had an unintended side effect: any program using ANSI escape sequences for animation (cursor home `ESC[H`, clear screen `ESC[J`), progress bars, REPLs, or any other interactive pattern was invisible until exit. The 470-line Conway implementation that surfaced #515 made it visible: ~16 seconds of `IO.sleep(80)` × 200 generations with nothing on screen, then exit fired and only the final frame was visible because the 199 preceding cursor-home + clear-screen sequences processed within microseconds and the eye couldn't resolve them.
- Fix is a tee in `host_print` (`vera/codegen/api.py`): the in-memory `output_buf` still receives every byte (so `WasmTrapError.stdout`, `ExecuteResult.stdout`, and the `--json` envelope's `stdout` field are unchanged), and *also* writes go to `sys.stdout` with an explicit per-write `flush()` when `execute(tee_stdout=True)`. New `tee_stdout: bool = False` parameter on `execute()` defaults *off* — preserves test-helper silence (`_run_io`, `_run` in `tests/test_codegen.py` rely on `ExecuteResult.stdout` and would pollute pytest's `capsys` if the default flipped). `cmd_run` text mode opts in (`tee_stdout=not as_json`); JSON mode stays off (live writes would split the envelope for downstream consumers parsing our stdout). The `cmd_run` text-mode and `WasmTrapError`-handler paths now skip re-writing `exec_result.stdout` / `exc.stdout` (those bytes already streamed live), only emitting a closing `\n` if the program's last write didn't include one — without that change every program's transcript would have double-printed.

### Tests
- New `TestStdoutTee543` class in `tests/test_runtime_traps.py` (6 tests): live streaming in text mode, write count and order preservation, JSON-mode tee suppression (envelope-corruption prevention), trap-preservation invariant still holds (#522 regression guard), per-call flush count matches per-call `IO.print` count, default `execute()` behaviour stays silent for the test suite.

### Documentation
- **SKILL.md** — IO operation table cell for `IO.print` notes "no implicit newline; flushes per call". New paragraph after the table explains output buffering: under `vera run` text mode every write is live and flushed; under `vera run --json` the transcript lives only in the envelope; in both cases the in-memory capture survives traps so `WasmTrapError.stdout` and the JSON `stdout` field are complete. Pre-v0.0.123 the whole transcript was buffered until exit — note included so anyone reading the doc with an older Vera installed isn't surprised.

## [0.0.122] - 2026-04-27

### Fixed
- **Conservative GC bounds-checked against `$heap_ptr`** ([#515](https://github.com/aallan/vera/issues/515), closes) — `$gc_collect` no longer faults under sustained allocation pressure. Root cause: the Phase 2 worklist-seeding code accepts a shadow-stack value as a heap pointer if it satisfies three guards — in heap range (`val >= gc_heap_start + 4`), aligned (`(val - gc_heap_start) % 8 == 4`), and below `$heap_ptr`. None of those guards prove the word at `val - 4` is an actual object header. A non-pointer i32 in payload data (a bit-packed `Nat` row in Conway-style code, a hash, anything else with bits in heap range) can satisfy all three; Phase 2b then reads garbage as `obj_size = header >> 1`, sets the mark bit (corrupting a random word!), and walks `obj_ptr + 0..obj_size` past `$heap_ptr` and past the linear-memory boundary, trapping with `memory fault at wasm address 0x... in linear memory of size 0x...` — `gc_collect` itself at the top of the stack. Two layers of defence emitted in `_emit_gc_collect` (`vera/codegen/assembly.py`):
  - **Layer 2 (early skip)** — before either marking or scanning a worklist entry, compute `obj_size` and verify `obj_ptr + obj_size <= heap_ptr`. If not, the entry is a Phase 2 false positive: skip it entirely (no mark store, no scan loop). This catches the bug at the cheapest possible point and prevents the mark-bit corruption that would otherwise persist across the cycle.
  - **Layer 1 (per-iter)** — inside the conservative scan loop, also check `obj_ptr + scan_ptr + 4 <= heap_ptr` before each `i32.load`. Costs a single `i32.add` + `global.get` + `i32.gt_u` per iteration relative to the load itself — negligible — and protects any future caller that reaches this loop without the Layer-2 check (e.g. a precise scan path added later, or a refactor that bypasses the early skip).
  Verified end-to-end with a 470-line Conway implementation that pre-fix reliably crashed at generation 56 (heap saturated with rendered-frame strings, bit-packed `Nat` row values matching the alignment + range guards): runs cleanly through every generation post-fix. Structural regression test in `tests/test_codegen.py::TestGarbageCollection::test_gc_collect_bounds_check_against_heap_ptr` asserts both bound checks survive in the emitted WAT — behavioural reproducers for #515 are heavily layout-sensitive (string-pool offsets, allocation order), so a structural assertion is the durable regression guard.

### Documentation
- **KNOWN_ISSUES.md** — #515 row removed from the Bugs table.
- **ROADMAP.md** — #515 dropped from the bug-killing campaign queue (closed by this release); intro updated to reflect "ten remain" instead of "eleven remain"; the "[#487](#487) likely also alleviates pressure on #515" note removed (now moot).

## [0.0.121] - 2026-04-27

### Fixed
- **Nested closures work end-to-end** ([#514](https://github.com/aallan/vera/issues/514), closes) — closures inside closure bodies (the natural 2D `array_map(rows, fn(row) { array_map(cols, fn(col) { ... }) })` shape) failed WASM validation pre-fix because only the outermost closure was lifted to a top-level function. The closure-lifting pass at `vera/codegen/closures.py:_lift_pending_closures` iterated only the outer `WasmContext`'s `_pending_closures` list; `_compile_lifted_closure` created a fresh inner ctx to translate the body, and any `fn { ... }` discovered during that translation registered on the inner ctx — never bubbled back. Result: only `$anon_0` ended up in the function table, and the inner call_indirect targeted a missing entry, surfacing as `type mismatch: expected i64, found i32` (validation) when the inner returned a pair type, or `unreachable` (runtime) otherwise. Fix is a worklist: `_lift_pending_closures` now pops closures one at a time, collects any inner pending discovered during each lift via a new `collect_pending` parameter on `_compile_lifted_closure`, and feeds them back. Inner ctx's `_closure_sigs` and `_next_closure_id` are now shared by reference with the module-level state to avoid `$closure_sig_0` / `$anon_0` name collisions across contexts. The lifter now handles arbitrary nesting depth (verified at three levels). Also fixes `_walk_free_vars` to recurse into nested `AnonFn` expressions so captures from the outer scope referenced inside an inner closure resolve correctly — pre-fix the recursion case was missing entirely; the bug was latent because nested closures didn't make it through lifting in the first place.

### Improved
- **Closure capture works for ADTs** — same fix scope. The historical [#514](https://github.com/aallan/vera/issues/514) framing claimed "all heap captures broken"; investigation showed ADT captures (`Option<T>`, `Result<T, E>`, user `data` types, `Map`/`Set`/`Decimal`/`Regex`) actually work because they're single-i32-pointer values, not pairs. Only `String` and `Array<T>` are still broken (the closure-struct serialiser drops the len field) — this residual is now scoped to its own issue [#535](https://github.com/aallan/vera/issues/535) with a pointer-only fix path. SKILL.md "Capturing outer bindings" rewritten to reflect this accurate picture; the over-broad "primitives only" claim is gone.

### Tests
- New `TestNestedClosures` class in `tests/test_codegen_closures.py` (5 tests): nested closure with primitive return, nested with pair return (the original #514 reproducer), nested with outer-param capture, three-level nesting (worklist depth), white-box check that the lifted function table contains both `$anon_0` and `$anon_1`.

### Examples + conformance
- New `examples/nested_closures.vera` — `build_grid` (3×4 multiplication-style grid via 2D `array_map`), `grid_sum` (two-layer `array_fold` that uses inner closures), `three_d_count` (3D nesting). Verifies all 6 contracts at Tier 1.
- New `tests/conformance/ch05_nested_closures.vera` (level: `run`) — covers 2D no-capture, 2D with-capture across the nesting boundary, 3D nesting, all in one program.

### Documentation
- **SKILL.md: Capturing outer bindings rewritten** — the old "primitives only" framing was inaccurate (ADTs work too). New text: primitives + ADTs work; only pair types (`String`, `Array<T>`) remain broken, scoped to [#535](https://github.com/aallan/vera/issues/535). The "Known limitation: nested closures" subsection is removed entirely (no longer broken). The Known Bugs table row for #514 is replaced with a row for #535. The #522 row is removed (closed in v0.0.120). The #516 row is updated to clarify that Stage 1 (categorisation) shipped in v0.0.120 and Stages 2-3 (source mapping + Fix paragraphs) remain.
- **KNOWN_ISSUES.md** parallel updates to the SKILL changes.
- **ROADMAP**: removed #514 row from the bug-killing campaign queue (closed by this release); inserted #535 at the bottom of the active queue (workaround exists, lower urgency); intro updated to reflect "ten remain" instead of "eleven remain".

### CI
- **Drop the CVE-2026-3219 ignore in `dependency-audit`** ([#527](https://github.com/aallan/vera/issues/527), closes) — pip 26.1 shipped on 2026-04-26 with the [pypa/pip#13870](https://github.com/pypa/pip/pull/13870) fix that addresses the concatenated-tar+ZIP archive-handling bug ([CVE-2026-3219](https://nvd.nist.gov/vuln/detail/CVE-2026-3219), [GHSA-58qw-9mgm-455v](https://github.com/advisories/GHSA-58qw-9mgm-455v)). Verified locally that `pip-audit --skip-editable` against pip 26.1 returns "No known vulnerabilities found" without the ignore. Removed the `--ignore-vuln CVE-2026-3219` flag from the workflow, the corresponding row from KNOWN_ISSUES.md's "CI ignores" table, and the per-flag annotation from TESTING.md's command example. The pygments CVE-2026-4539 ignore stays in place pending an upstream fix release.

## [0.0.120] - 2026-04-26

### Fixed
- **`IO.print` output preserved on trap** ([#522](https://github.com/aallan/vera/issues/522), closes) — the `host_print` implementation in `vera/codegen/api.py` appends to a Python `io.StringIO` that was only surfaced to the CLI on the success path. On the trap path the buffer was discarded as the exception unwound out of `execute()`, so any `IO.print` calls preceding a runtime crash were lost — exactly when an agent had inserted them to instrument the suspected crash site. Fixed by introducing `WasmTrapError` (a `RuntimeError` subclass carrying `stdout`, `stderr`, and `kind`); `execute()` now raises it on every trap path with the captured buffers attached, and `cmd_run` writes them to `sys.stdout` / `sys.stderr` (text mode) or includes them in the JSON envelope (JSON mode) before reporting the error. Order is preserved under `2>&1` redirects via an explicit `sys.stdout.flush()` after the captured-output write.
- **`IO.stderr` capture wired through to `cmd_run`** — sibling fix completing the `WasmTrapError.stderr` and JSON-envelope `stderr` contracts. `cmd_run` now passes `capture_stderr=True` to `execute()` (was always defaulting to `False`), so `IO.stderr` writes are buffered into `ExecuteResult.stderr` rather than falling through to live `sys.stderr` writes. The success path now also replays `exec_result.stderr` to `sys.stderr` (text mode) or includes it in the JSON envelope (JSON mode), parallel to the existing stdout treatment. Without this, the `WasmTrapError.stderr` field documented in the previous bullet was permanently empty in production, even though the host-side infrastructure (`host_stderr` writing to `stderr_buf`) had been in place since #463. New regression test `test_json_mode_includes_stderr_in_envelope` pins the contract.

### Improved
- **Runtime trap categorisation — Stage 1 of [#516](https://github.com/aallan/vera/issues/516)** — every WASM trap was previously relabelled `Runtime contract violation` by the CLI's catch-all, even when the actual cause was integer division by zero, out-of-bounds memory access, call stack exhaustion, or the `unreachable` instruction. The new `_classify_trap` helper in `vera/codegen/api.py` inspects the wasmtime exception message and maps it to a stable `kind` plus a Vera-native description: `divide_by_zero`, `out_of_bounds`, `stack_exhausted`, `unreachable`, `overflow`, `contract_violation`, or `unknown`. The contract-violation path remains via the existing `last_violation` host-import channel, which always wins over the wasmtime trap reason. JSON mode now includes `trap_kind` in each diagnostic so downstream consumers (LSP, agents, future tooling) can branch on the structured value instead of pattern-matching free text. Stages 2 (source mapping the trapping function) and 3 (per-`kind` `Fix:` paragraphs) remain open under #516.

### Tests
- New `tests/test_runtime_traps.py` — 16 tests covering the classifier (every documented `kind` in isolation), the `WasmTrapError` shape, the end-to-end stdout-on-trap fix in both text and JSON modes, and trap-kind reporting in both modes. Pure-helper tests use a `_FakeTrap` exception class — the classifier is stringly-typed against the wasmtime trap message format, so it can be exercised without a wasmtime runtime, and we benefit from that decoupling for tests.

### Website
- **Mobile overflow fixes in `docs/index.html`** (folded in from PR #532) — three iOS Safari overflow bugs at iPhone widths: (a) hero meerkat image overflowed because `.hero-image` had `max-width:640px` but no `width:100%` (global `img{max-width:100%}` was beaten on specificity); (b) the VeraBench `vera-bench` GitHub button was stretched into a full-width pill because the mobile `.btn{width:100%}` rule (intended for hero CTA stacking) matched every `.btn`, so the bench button got scoped to `.cta-bar .btn`; (c) shell-command code blocks in the "Runs Everywhere" section ran past the viewport edge because `<pre>` defaults to `white-space:pre`, so a mobile-only `.code-block pre{white-space:pre-wrap;word-break:break-word}` rule was added (Vera sample blocks intentionally keep `pre` to preserve syntax indentation). Verified at 375×812 viewport: all three elements fit cleanly.

### Tooling notes
- **[mcp-assert](https://github.com/blackwell-systems/mcp-assert) bookmarked as the test harness for any future Vera MCP server** ([#529](https://github.com/aallan/vera/issues/529)) — Go binary (also pip / npm / brew) that connects to MCP servers over stdio/SSE/HTTP, calls their tools, and asserts results against YAML-defined expectations. Language-agnostic on the server side, MIT-licensed, GitHub Action available. Scope is deterministic tools (data retrieval, state changes, validation) — exactly the shape Vera would expose (`vera_check`, `vera_verify`, `vera_compile`, `vera_context`). Not adopted today (no MCP server to test yet); cross-referenced from [#401](https://github.com/aallan/vera/issues/401) so whoever picks up the documentation MCP endpoint inherits the harness recommendation.

### CI
- **Ignore [CVE-2026-3219](https://nvd.nist.gov/vuln/detail/CVE-2026-3219) in `dependency-audit`** ([#527](https://github.com/aallan/vera/issues/527)) — pip 26.0.1 is flagged for an archive-handling bug (GHSA-58qw-9mgm-455v) where concatenated tar+ZIP files are parsed as ZIP regardless of the filename. Upstream fix merged in [pypa/pip#13870](https://github.com/pypa/pip/pull/13870) under the pip 26.1 milestone but not yet released; no patched version exists to upgrade to. Threat model (installing untrusted ambiguously-formatted archives) does not apply to our CI. The ignore is bridging until pip 26.1 lands on PyPI; removal is tracked as an action item on #527 and in the new "CI ignores" section of KNOWN_ISSUES.md.

### Website fixes (follow-up to PR #526 review)
- **`research_topic` homepage sample: URL-encode query** — the DuckDuckGo sample interpolated the raw `@String.0` parameter into the query string, so any input with a space, `&`, `%`, or unicode character would have been rejected by the server. Added a `let @String = url_encode(@String.0)` before the `Http.get` call; verified via `vera check`. The fix also demonstrates Vera's `url_encode` built-in in a realistic position, a small bonus for agents reading the homepage.
- **Status-paragraph fact drift** — two numbers in the status paragraph were already stale before this PR: "six algebraic effects (IO, Http, State, Exceptions, Async, Inference)" was missing `Random` (actual count: seven); "77-program conformance suite" was actually 80; HTML's "30 worked examples" was actually 32. Corrected in both `docs/index.html` and `scripts/build_site.py::build_index_md()`. The markdown generator now also uses `{n_conformance}` dynamically (previously only `{n_examples}` was dynamic). The structural fix (auto-generate or gate all homepage numbers via `check_doc_counts.py`) is tracked as [#528](https://github.com/aallan/vera/issues/528) and placed in ROADMAP Phase 3b.

### Website
- **veralang.dev homepage redesign** — full-page redesign of `docs/index.html` with an editorial-research aesthetic. Structural changes: bilingual reading-path device at the top of the page (`@reader.0 → humans` / `@reader.1 → agents` using Vera's own slot-reference syntax to acknowledge the dual audience), "Why?" thesis promoted to a weighty anchor with a serif-display callout, four-sample code showcase with commentary stacked below each block (rather than a side-by-side column that clipped long lines like `research_topic`'s URL concat), VeraBench lifted above the reference grid with a masthead stat ("Kimi K2.5 writes 100% correct Vera…") paired to the mascot in a baseline-aligned lockup, reference grid condensed from 17 features to 9 (typed-stdlib entries merged; "Full contracts" and "Contract-driven testing" merged), dark "For Agents" section framing the page as a machine-readable specification with the three agent-facing documents (SKILL.md, AGENTS.md, CLAUDE.md) as discrete cards. Visual system: three-font hierarchy committed — DM Serif Display for statements the site is making, Inter for explanations, JetBrains Mono for machine surfaces (code, eyebrows, readpath); cream/brown/orange palette aligned to Negroni's Vermouth + Campari scales (`#FFECD1` matches the hero meerkat's baked cream, `#FEEAD1` pinned to the VeraBench section to match its chart/mascot assets, `#FFE2CE` used as contrast surface). Meerkat hero, briefing-mandated font stack, and single-file HTML preserved; no frameworks, no trackers, no analytics. All load-bearing agent metadata preserved: `<link rel="alternate">` entries, `rel="llms-txt"`/`rel="llms-full-txt"` directives, schema.org JSON-LD block, and the inline `<script type="text/llms.txt">` hand-off at the bottom of `<body>`.
- **[Agent Score](https://buildwithfern.com/agent-score) improvements** — score moved from **3 failures + 2 warnings** to **2 failures + 1 warning**. Cleared: `page-size-html` (52.9K → 44.9K, under the 50K edge), `page-size-markdown` (13K, under 50K), `llms-txt-directive` (was failing), `llms-txt-freshness` (was 1/2 sitemap doc pages covered; now 2/2). Improved: `markdown-content-parity` miss rate 90% → 21% (4× reduction). `scripts/build_site.py`'s `build_llms_txt()` gained a `## Homepage` section referencing `/index.md`; `build_index_md()` rewritten to mirror the HTML section-for-section (thesis, code samples, VeraBench stat + table, runtime, install, For Agents, status) — `/index.md` grew from 4,019 to 13,491 chars. Remaining gaps (content negotiation, inline-CSS truncation budget, final 21% parity) tracked in [#525](https://github.com/aallan/vera/issues/525) and added to ROADMAP Phase 3b.

### Planned
- **`vera context` — token-budgeted project context export** ([#523](https://github.com/aallan/vera/issues/523)) — new CLI command that walks a project's dependency graph and emits a compact summary of public signatures, contracts, effects, ADTs, and imports for LLM consumption. Directly inspired by [Aver](https://averlang.dev)'s [`aver context`](https://github.com/jasisz/aver#context-export); credit retained through implementation, commit messages, and CLI help text. Placed in Milestone 3 Phase 3a alongside the LSP server and Plumbing integration.

### Documentation
- **SKILL.md documentation sweep** ([#513](https://github.com/aallan/vera/issues/513)) — eight sections added or rewritten to close agent-surfaced documentation gaps: Array literals (`[]` / `[1, 2, 3]` / type inference), Closures and captured bindings (syntax + De Bruijn shift rule + the primitives-only capture limitation + tail-recursion-with-explicit-parameters workaround), full string escape-sequence table (`\n` / `\t` / `\r` / `\0` / `\\` / `\"` / `\u{XXXX}`) with explicit unsupported list and fallback notes, Nullary vs Unit-taking function signature variants, Stored function values and `apply_fn`, Known Bugs and Workarounds section pointing at KNOWN_ISSUES.md. Additions validated against `scripts/check_skill_examples.py`; ALLOWLIST regenerated (68 unique entries, AST-verified zero duplicate keys).

### Tracked bugs
- Five compiler/runtime bugs surfaced by an agent writing Conway's Game of Life against v0.0.119, filed + added to KNOWN_ISSUES.md + reprioritised in ROADMAP.md's implementation-order table:
  - [#514](https://github.com/aallan/vera/issues/514) — closure codegen mis-emits environment when capturing heap-allocated outer bindings (Array, String, ADT). Primitive captures work; any heap capture fails at WASM validation. Root cause refined from earlier "nested closures" symptom.
  - [#515](https://github.com/aallan/vera/issues/515) — `$gc_collect` walks past `$heap_ptr` to the linear-memory bound and traps mid-sweep.
  - [#516](https://github.com/aallan/vera/issues/516) — runtime traps bubble up as raw wasmtime stack traces; CLI mis-labels every trap as "Runtime contract violation".
  - [#517](https://github.com/aallan/vera/issues/517) — no tail-call optimization; the documented tail-recursion iteration idiom blows the WASM call stack at ~tens of thousands of frames.
  - [#522](https://github.com/aallan/vera/issues/522) — `IO.print` output lost on trap. **Filed early in this cycle and fixed by this release** — see the `### Fixed` section above for the implementation (`WasmTrapError` carrying captured `stdout`/`stderr`/`kind`). Paired with #516 Stage 1 (also in `### Improved` above) — both close the "type-checks clean, runtime crashes opaque, can't even instrument" gap.

## [0.0.119] - 2026-04-23

### Added
- **JSON typed accessors** ([#366](https://github.com/aallan/vera/issues/366)) — eleven new accessor functions for the built-in `Json` ADT that eliminate the two-level pattern-match boilerplate every JSON API consumer would otherwise write (`match option ... { Some(@Json) -> match @Json.0 { JNumber(@Float64) -> ... } }`). Six Layer-1 type-coercion accessors (`Json → Option<T>`): `json_as_string`, `json_as_number`, `json_as_bool`, `json_as_int`, `json_as_array`, `json_as_object`. Five Layer-2 compound field accessors (`Json, String → Option<T>`): `json_get_string`, `json_get_number`, `json_get_bool`, `json_get_int`, `json_get_array` — each collapses `json_get` + the matching `json_as_*` into one call, so missing fields and wrong-typed fields both return `None`. `json_as_int` guards every `float_to_int` trap path — NaN, infinity, AND finite overflow (|f| ≥ 2^63) — returning `None` for all four non-representable-as-Int cases. Closes [#366](https://github.com/aallan/vera/issues/366).

### Implementation
- Unlike the v0.0.118 batch, these are **pure-Vera prelude functions**, not WASM translators. All eleven bodies live in `vera/prelude.py` `_JSON_COMBINATORS` as match expressions over `Json`; the compiler already injects the prelude into every module that references `Json` values. No new host imports, no new WASM emit, no new WASM bytes in compiled modules that don't use them.
- `vera/environment.py` registers the eleven new `FunctionInfo` entries next to the existing `json_get` / `json_type` registrations. Layer-1 accessors emitted from a tight Python loop (six identical `Json → Option<T>` shapes differ only in element type).
- `vera/prelude.py` extended in three places: `_JSON_COMBINATORS` (bodies), `_source_mentions_json` (detection names set), and the injection site's `json_fn_names` shadow-check set.

### Example rewrite
- `examples/json.vera` rewritten to showcase the new accessors — the gradebook weather-API scenario that previously used a helper-per-field pattern now uses Layer-2 accessors directly. Line count stayed roughly similar (the rewrite is a style change, not a pure reduction) but the per-field boilerplate disappeared: `json_get_array(obj, "hourly")` replaces the two-level `match json_get(obj, "hourly") { Some(@Json) -> match @Json.0 { JArray(@Array<Json>) -> ... } }` pattern.

### Tests
- 19 new unit tests in `tests/test_codegen.py::TestJsonTypedAccessors` covering every Layer-1 accessor (matching + mismatched constructors), every Layer-2 accessor (hit + missing field + wrong type), plus targeted edge cases: `json_as_int` NaN guard, `json_as_int` infinity guard, `json_as_int` toward-zero truncation for negative floats, and `json_as_coercions_are_disjoint` pinning the invariant that at most one Layer-1 accessor returns `Some` for any given Json.
- 2 new browser parity tests in `tests/test_browser.py::TestBrowserJsonAccessors` — one exhaustive Layer-1 sweep, one exhaustive Layer-2 sweep.
- New conformance program `tests/conformance/ch09_json_accessors.vera` (level: `run`) with 15 test functions.

## [0.0.118] - 2026-04-23

### Added
- **String utility built-ins** ([#470](https://github.com/aallan/vera/issues/470)) — eight pure string operations implemented entirely as inline WAT. Splits: `string_chars` (1-byte strings, the canonical bridge from `String` to `Array<String>`), `string_lines` (`\n` / `\r\n` / `\r` terminators, Python `splitlines()` semantics — trailing terminator does not add empty segment), `string_words` (whitespace-run splits, Python `split()` semantics — runs collapse, empty segments discarded). Transformations: `string_reverse`, `string_trim_start`, `string_trim_end`. Padding: `string_pad_start(s, n, fill)` / `string_pad_end(s, n, fill)` with JavaScript `padStart`/`padEnd` semantics — fill cycles left-to-right and is truncated to exactly the padding length, empty fill is a no-op, target shorter than input returns input unchanged. The three split operations return `Array<String>` whose elements are each independently `$alloc`-ed and copied — interior pointers into a shared backing buffer would fail the GC mark phase's alignment check (`(val - gc_heap_start) % 8 == 4` in `_emit_gc_collect`) and become unreachable after the function returns. Conformance: `ch09_string_char_utilities.vera`. Example: `examples/string_utilities.vera` exercises every operation in a coherent log-line-processor scenario. Closes [#470](https://github.com/aallan/vera/issues/470).
- **Character classification built-ins** ([#471](https://github.com/aallan/vera/issues/471)) — eight pure first-byte ASCII operations implemented as inline WAT (no host calls). Six classifiers: `is_digit` (`'0'..'9'`), `is_alpha` (`'A'..'Z'`, `'a'..'z'`), `is_alphanumeric` (union), `is_whitespace` (Python `str.isspace()` ASCII set — tab/LF/VT/FF/CR/space), `is_upper`, `is_lower`. Each inspects the **first byte** of the input and returns `false` for the empty string. Two case-conversion: `char_to_upper` / `char_to_lower` transform only the first byte, leaving remaining bytes untouched (useful for title-casing tokens). Eliminates the brittle hand-rolled `byte == 48 || byte == 49 || ...` patterns. ASCII-only — Unicode-aware variants tracked separately. Closes [#471](https://github.com/aallan/vera/issues/471).

### Compiler
- `vera/wasm/calls_strings.py` grew with sixteen new translators (~600 lines added). Shared helpers: `_translate_classifier(arg, env, *, body)` factors the predicate scaffolding for the six classifiers; `_translate_char_case(arg, env, *, to_upper)` factors `char_to_upper`/`char_to_lower`; `_translate_trim(arg, env, *, trim_start, trim_end)` factors both trim variants; `_translate_pad(...)` factors both pad variants; `_translate_structural_split(arg, env, *, mode)` factors `string_lines` and `string_words` via a two-pass count-then-emit shape that mirrors the existing `string_split` implementation.
- ASCII range tricks reused throughout: `(byte - 48) < 10` for digit, `((byte | 0x20) - 97) < 26` for case-folded alpha. Branchless and idiomatic across the classifiers.
- `vera/wasm/calls.py` dispatch table extended with sixteen new branches, plus `_infer_concat_elem_type` now returns `"String"` for `string_chars` / `string_lines` / `string_words` so monomorphization picks up the array element type correctly.
- `vera/wasm/inference.py` extended in both `_infer_fncall_wasm_type` and `_infer_fncall_vera_type` for the new return-type shapes (`i32_pair` for the string and array returns, `i32` for the bool returns).
- `vera/codegen/modules.py` known-names allowlist extended.
- `vera/environment.py` registers the sixteen new `FunctionInfo` entries in a tight block — the six classifiers are emitted via a Python loop because their `(STRING,) -> BOOL` signatures are identical.

### Tests
- 33 new unit tests across `TestCharClassification` and `TestStringUtilities` in `tests/test_codegen.py`.
- 9 new browser parity tests across `TestBrowserStringUtilities` and `TestBrowserCharClassification` in `tests/test_browser.py`. All sixteen built-ins produce bit-identical output under `wasmtime` and Node.js — they're inline WAT, no host imports.
- New conformance program `tests/conformance/ch09_string_char_utilities.vera` (level: `run`) with 14 test functions covering classifier, transform, pad, and split semantics including all the empty-string and edge-case shapes.

## [0.0.117] - 2026-04-22

### Added
- **Array utility built-ins (phase 1)** ([#466](https://github.com/aallan/vera/issues/466)) — seven new array combinators that complete the higher-order array operations suite without requiring ability dispatch on the polymorphic element type. `array_mapi<A, B>(arr, fn(A, Nat → B))` maps with a zero-based index — collapses the recursive-accumulator-with-index pattern that had been a leading source of De Bruijn indexing mistakes. `array_reverse<T>(arr)` reverses element order. `array_find<T>(arr, pred) → Option<T>` returns the first match, short-circuiting. `array_any<T>` and `array_all<T>` are existential / universal predicates with short-circuit evaluation and correct vacuous-truth on empty input (`any([], _) == false`, `all([], _) == true`). `array_flatten<T>(Array<Array<T>>)` concatenates one level of nesting via a two-pass length-then-copy. `array_sort_by<T>(arr, cmp)` returns a stable insertion sort using a caller-supplied `Ordering`-returning comparator. All seven are iterative WASM with O(1) shadow-stack depth, mirroring the `array_map`/`filter`/`fold` pattern from [#480](https://github.com/aallan/vera/issues/480). Conformance: `ch09_array_utilities.vera`. Example: `examples/array_utilities.vera` exercises every operation in a single coherent gradebook scenario. Phase 1 of [#466](https://github.com/aallan/vera/issues/466); `array_sort<T> where Ord<T>`, `array_contains<T> where Eq<T>`, and `array_index_of<T> where Eq<T>` are tracked separately as a phase 2 follow-up that requires reifying monomorphized `compare$T`/`eq$T` as first-class function handles.

### Compiler
- `vera/wasm/calls_arrays.py` grew from 1,214 → 2,291 lines with the seven new translators, all following the existing `_translate_array_filter` shape (call_indirect callback, GC-shadow-pushed pointers across every `$alloc`, pair-typed element handling for `String` and nested `Array`).
- `vera/wasm/inference.py` extended for the new return types (Array, Option, Bool).
- `vera/wasm/calls.py` dispatch table extended with seven new branches.
- `vera/codegen/modules.py` known-names allowlist extended.

### Bug fix during implementation
- Discovered and fixed an `Ordering`-tag dispatch bug in the initial `array_sort_by` WAT: niladic ADT variants (`Less` / `Equal` / `Greater`) are heap-allocated boxes with the tag at offset 0, not raw i32 tags. The first version of the sort compared the comparator's return value (a heap pointer) directly against the literal `2`, causing every comparison to evaluate as "not Greater" and the sort to no-op. Caught by the `test_array_sort_by_ascending_ints` unit test before the conformance suite could run; fix is a single `i32.load offset=0` to dereference the box before tag comparison.

## [0.0.116] - 2026-04-20

### Added
- **Math built-ins: log, trig, constants, numeric utilities** ([#467](https://github.com/aallan/vera/issues/467)) — fifteen new pure functions across four groups. Logarithmic: `log`, `log2`, `log10`. Trigonometric: `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2` (quadrant-correct `(y, x)` argument order matching POSIX / Python / JS). Constants: `pi()` and `e()` (inlined as `f64.const 3.141592653589793` / `f64.const 2.718281828459045`, no host call). Numeric utilities: `sign(@Int)` returns `-1`/`0`/`1`; `clamp(@Int, @Int, @Int)` and `float_clamp(@Float64, @Float64, @Float64)` enforce `min(max(v, lo), hi)`. The 10 log/trig functions use host imports (wrapped Python `math.*` in the Python runtime, `Math.*` in the browser); the 5 constants/utilities are inlined as WAT for zero host-call overhead. Gated emission — modules that don't use a given op don't import it. Unlocks scientific computing, graphics, audio, physics, statistics. Conformance: `ch09_math_builtins.vera`. Closes [#467](https://github.com/aallan/vera/issues/467).

## [0.0.115] - 2026-04-18

### Added
- **`Random` effect for non-deterministic value generation** ([#465](https://github.com/aallan/vera/issues/465)) — new built-in `Random` effect with three operations: `Random.random_int(@Int, @Int) -> @Int` (inclusive range), `Random.random_float(@Unit) -> @Float64` (uniform `[0.0, 1.0)`), `Random.random_bool(@Unit) -> @Bool`. Functions drawing random values must declare `effects(<Random>)`, making non-determinism visible in the type signature. Python runtime backs onto `random.randint` / `random.random()`; browser runtime backs all three onto `Math.random()` (fast, non-cryptographic, adequate for games and simulations). No seeding API yet — `handle[Random]`-based deterministic testing is future work. Unblocks games, simulations, shuffling, Monte Carlo methods, and randomized initial states (Conway's Life soup, etc.). Conformance: `ch07_random_effect.vera`. Closes [#465](https://github.com/aallan/vera/issues/465).

## [0.0.114] - 2026-04-17

### Added
- **`IO.sleep`, `IO.time`, `IO.stderr` operations** ([#463](https://github.com/aallan/vera/issues/463)) — three new operations on the built-in `IO` effect. `IO.sleep(@Nat) -> Unit` pauses execution for N milliseconds (used for animation frame budgets and rate-limiting). `IO.time(@Unit) -> @Nat` returns the current Unix time in milliseconds (used for elapsed-time measurement and timestamps). `IO.stderr(@String) -> Unit` writes to stderr separate from stdout (used for CLI tools that pipe stdout as data). Python runtime delegates to `time.sleep`, `time.time`, and `sys.stderr`; browser runtime busy-waits on `performance.now()` (no `Atomics.wait` on the main thread), uses `Date.now()`, and captures stderr into a separate buffer exposed via `getStderr()`. `execute()` gains a `capture_stderr: bool = False` parameter; `ExecuteResult` gains a `stderr: str` field (empty string by default to preserve the pre-#463 shape). Discovered missing while writing a Conway's Game of Life program. Conformance: `ch07_io_time_stderr.vera`.

### Fixed
- **GC object header size field widened from 16-bit to 31-bit** ([#484](https://github.com/aallan/vera/issues/484)) — `$alloc` has always stored the object size as `(size << 1) | mark` (bit 0 = mark, remaining bits = size), but the GC's sweep and free-list code was masking the size readback with `0xFFFF`, silently truncating any allocation ≥ 65536 bytes. The sweeper would then interpret middle-of-payload bytes as tiny zero-size headers and link each 8-byte chunk into the free list, shredding the live object. Removed the `0xFFFF` mask at all five read sites in `vera/codegen/assembly.py` (two in `$alloc` free-list walks, three in `$gc_collect` sweep/mark). Max single allocation is now ~2 GB (bounded by WASM's 4 GB memory ceiling and the leading mark bit). Stress tests for `array_map` and `array_filter` uncapped from 8K back to 10K elements. Discovered a separate memory-grow bug while testing the fix — filed as [#487](https://github.com/aallan/vera/issues/487).

### Changed
- **Iterative WASM `array_fold`** ([#480](https://github.com/aallan/vera/issues/480) PR 3) — `array_fold<T, U>(arr, init, fn)` is now emitted as a single WAT `loop` that runs a closure `(env, U, T) -> U` over each element, updating a running accumulator in-place. Structurally different from PRs 1 and 2: no output allocation (returns a scalar `U`), closure takes two value parameters, and for pair-typed / ADT accumulators the running pointer is kept rooted via an in-place shadow-stack slot overwrite (`global.get $gc_sp; i32.const 8; i32.sub; i32.store`) — avoiding per-iteration push/pop churn. Closes [#480](https://github.com/aallan/vera/issues/480). Also decouples `_ARRAY_TYPE_ALIASES` injection from the (now empty) `array_fn_names` set in `prelude.py` so `ArrayMapFn` / `ArrayFilterFn` / `ArrayFoldFn` aliases stay available for any user code that references them in type annotations.
- **Iterative WASM `array_filter`** ([#480](https://github.com/aallan/vera/issues/480) PR 2) — `array_filter<T>(arr, pred)` is now emitted as a single WAT `loop` with a separate `write_idx`, replacing the recursive prelude (`array_filter` / `array_filter_go`). Worst-case over-allocates `len * sizeof(T)` bytes and returns `(dst, write_idx)`; the unused tail is unreachable via the returned pair and gets reclaimed by the sweeper. Single-pass by design — the predicate is invoked exactly once per element. Shadow-stack usage is now O(1). Follows the same pattern as PR 1 (`array_map`); `array_fold` to follow in PR 3.
- **Iterative WASM `array_map`** ([#480](https://github.com/aallan/vera/issues/480) PR 1) — `array_map<A, B>(arr, fn)` is now emitted as a single WAT `loop` driven by a `call_indirect` on the closure, replacing the recursive prelude implementation (`array_map_go`). Shadow-stack usage is now O(1) regardless of input length — the old recursive version hit the 16K shadow-stack ceiling (post-[#464](https://github.com/aallan/vera/issues/464)) around 4K elements. The generic higher-order signature (`forall<A, B>`) is preserved via a `FunctionInfo` built-in registration, so source code is unchanged. Also discovered and filed [#484](https://github.com/aallan/vera/issues/484) — a pre-existing 16-bit GC-header size-field limits allocations to 65535 bytes; the stress test caps at 8K Int elements (64,000 bytes) until that's fixed.

### Added
- **CHANGELOG enforcement at pre-push and CI** ([#478](https://github.com/aallan/vera/issues/478)) — new `scripts/check_changelog_updated.py` fails a PR if any substantive file (`vera/`, `spec/`, `SKILL.md`) is changed without a matching new entry in `CHANGELOG.md`. Runs at the `pre-push` hook stage locally (opt in with `pre-commit install --hook-type pre-push`) and in the CI `lint` job. Escape hatches: a `Skip-changelog: <reason>` commit trailer (Git-native) or a `skip-changelog` PR label (CI-only). Prevents the kind of missed release-prep that happened on [#474](https://github.com/aallan/vera/pull/474).

### Documentation
- **Docs consistency sweep** — retroactively tag/release v0.0.113 (the release prep PR #477 merged but the tag+release finishing steps were never run); close [#418](https://github.com/aallan/vera/issues/418) manually (PR description lacked an auto-close keyword); refresh file-size tables in `vera/README.md` after the calls.py decomposition (`calls.py` 8,332 → 572 + 8 mixin rows; `wasm/` 4,273 → 12,998 across 17 modules; `codegen/` size drift); fix stale 3,253 → 3,318 test count in `README.md` and the HISTORY by-the-numbers table; add [#424](https://github.com/aallan/vera/issues/424), [#439](https://github.com/aallan/vera/issues/439), [#480](https://github.com/aallan/vera/issues/480) (iterative WASM higher-order array ops), and [#481](https://github.com/aallan/vera/issues/481) (auto-tag + auto-release on version bump) to ROADMAP; remove closed [#416](https://github.com/aallan/vera/issues/416) and [#417](https://github.com/aallan/vera/issues/417) from SKILL.md limitations.

## [0.0.113] - 2026-04-16

### Changed
- **Decompose `vera/wasm/calls.py` into 8 subsystem mixins** ([#418](https://github.com/aallan/vera/issues/418)) — the 8,390-line `calls.py` monolith is split into a small core dispatcher (572 lines) plus 8 domain-focused mixins: `calls_math.py` (numeric + conversions), `calls_markup.py` (JSON/HTML/Markdown/Regex/async), `calls_arrays.py`, `calls_handlers.py` (Show/Hash/handle), `calls_containers.py` (Map/Set/Decimal), `calls_parsing.py`, `calls_encoding.py` (base64/URL), `calls_strings.py`. Pure code motion — `WasmContext` continues to compose all mixins via Python MRO; no behavioral changes, runtime output identical. Makes `calls.py` 93% smaller and prepares ground for Stage 11 primitives additions. Closes [#418](https://github.com/aallan/vera/issues/418).

### Known issues
- **10 pre-existing bugs in WASM call translators** surfaced during review of [#474](https://github.com/aallan/vera/pull/474) — all predate this release; tracked in [#475](https://github.com/aallan/vera/issues/475). See `KNOWN_ISSUES.md` for the summary; the issue lists each bug with severity, location, and description.

## [0.0.112] - 2026-04-16

### Fixed
- **GC shadow stack overflow causing silent array corruption** ([#464](https://github.com/aallan/vera/issues/464)) — the GC shadow stack was 4K (4096 bytes). Recursive functions with multiple `Array` parameters push ~12 bytes per frame (2 pointer params + 1 `array_append` destination), overflowing at ~341 frames into the adjacent GC worklist region. When GC triggered during deep recursion, the worklist corruption caused intermediate arrays to be incorrectly freed, silently overwriting the first bytes of Bool arrays with free-list pointers. Shadow stack increased from 4K to 16K; worklist increased from 4K to 16K; overflow guard added to `gc_shadow_push` (traps instead of silent corruption). Closes [#464](https://github.com/aallan/vera/issues/464).

## [0.0.111] - 2026-04-10

### Fixed
- **SMT translator: String/Float64 parameters declared with correct Z3 sorts** — `String` and `Float64` function parameters were being declared as Z3 integers (the `else` fallback in `verifier.py`), causing `string_contains`, `string_starts_with`, `string_ends_with`, and `string_length` to receive Int-sorted Z3 variables instead of the expected SeqSort/RealSort. String parameters are now declared via `smt.declare_string()` (Z3 `SeqSort`) and Float64 via `smt.declare_float64()` (Z3 `RealSort`).
- **SMT translator: `StringLit` now translates to `z3.StringVal()`** — string literals in contract expressions (e.g. `requires(string_starts_with(@String.0, "https://"))`) were returning `None` from `translate_expr`, silently demoting the contract to Tier 3. Fixed by adding a `StringLit` branch that emits `z3.StringVal(expr.value)`.
- **SMT translator: `string_length` uses `z3.Length()` for String sorts** — the previous uninterpreted function implementation meant Z3 could not prove `string_length("literal") > 0` at call sites (even though it's obviously true), producing spurious E501 call-site precondition errors. `string_length` on a `SeqSort` argument now uses Z3's native `z3.Length()`, giving full string-theory semantics; the uninterpreted fallback is retained for non-string sorts.
- **SMT translator: `string_contains`, `string_starts_with`, `string_ends_with` now Tier 1** — these pure Boolean predicates on String arguments are now encoded via Z3's native string theory (`z3.Contains`, `z3.PrefixOf`, `z3.SuffixOf`) rather than falling through to Tier 3.
- **`float_is_nan` / `float_is_infinite` explicitly return `None`** — previously fell through to the function-lookup path; now explicitly return `None` with a comment explaining why encoding them as `BoolVal(False)` would be unsound (Float64 is modelled as Z3 reals, which have no NaN/infinity; returning `False` would cause the compiler to skip the runtime guard).

## [0.0.110] - 2026-04-10

### Added
- **Mistral AI provider for the Inference effect** ([#413](https://github.com/aallan/vera/issues/413)) — `Inference.complete` now supports Mistral models. Set `VERA_MISTRAL_API_KEY` to use; default model is `mistral-small-latest`. Closes [#413](https://github.com/aallan/vera/issues/413).

### Changed
- **Provider registry refactor** ([#413](https://github.com/aallan/vera/issues/413)) — `_call_inference_provider()` and the auto-detection logic in `execute()` are now table-driven via a `_ProviderConfig` dataclass and `_PROVIDERS` registry dict, replacing the `elif` chain. Adding further providers (Grok, DeepSeek, Gemini) is now a one-row change. The `_call_inference_provider` signature simplified from six parameters to four (`provider`, `prompt`, `model`, `api_key`).

## [0.0.109] - 2026-04-10

### Fixed
- **Closure `i32_pair` param/return type in WAT** ([#359](https://github.com/aallan/vera/issues/359)) — `String` and `Array` parameters and return types inside closures now emit correct two-slot WAT signatures (`(param i32 i32)` / `(result i32 i32)`). Previously the closure lifting path and the `call_indirect` type descriptor each omitted the second i32 slot, causing WAT compilation failures for closures that accept or return `String`/`Array` values. Three fixes: (1) `codegen/closures.py` lifted function declarations now emit `(param $p{i}_ptr i32) (param $p{i}_len i32)` for `i32_pair` params; (2) `wasm/closures.py` `call_indirect` type descriptor emits two params per `i32_pair` argument; (3) `wasm/inference.py` `_infer_apply_fn_return_type` handles `AnonFn` literals to return `"i32_pair"` for `String`/`Array` return types, preventing `$closure_sig_N` naming collisions.
- **Host imports not registered for closures** ([#359](https://github.com/aallan/vera/issues/359)) — Map/Set/Decimal/Json/Html host-import ops used inside closure bodies were not propagated to the module-level tracker, causing `unknown func` errors at runtime. `codegen/closures.py` `_compile_lifted_closure` now propagates all resource flags from the closure's `WasmContext` back to the module codegen.
- **`_infer_fncall_vera_type` truncating parameterised accumulator types** ([#359](https://github.com/aallan/vera/issues/359)) — when inferring the return type of `apply_fn` calls for `_resolve_generic_call`, parameterised types like `Map<String, Int>` were reduced to the bare name `"Map"`, producing wrong monomorphised call targets (e.g. `array_fold_go$String_Map` instead of `array_fold_go$String_Map_String_Int`). Fixed by calling `_format_named_type` instead of returning `ta.name`.

## [0.0.108] - 2026-04-07

### Added
- **`vera check --explain-slots`** ([#445](https://github.com/aallan/vera/issues/445)) — new flag prints a slot resolution table after a successful type-check, showing which parameter position each `@T.n` index refers to. Example: `fn divide(@Int, @Int -> @Int)` produces `@Int.0 = parameter 2 (last @Int)`, `@Int.1 = parameter 1 (first @Int)`. Also available in JSON mode via `--json` (adds `slot_environments` array to output). Closes [#445](https://github.com/aallan/vera/issues/445), closes [#183](https://github.com/aallan/vera/issues/183) (won't fix — see issue for design rationale).
- **SKILL.md prescriptive improvements** — five sections reworked from descriptive to action-oriented: De Bruijn intro now leads with a bold warning; new `--explain-slots` workflow subsection; new "Workflow: writing contracts incrementally" subsection in the Contracts section; Typed Holes intro reframed imperatively; Built-in function naming section adds a directive for handling unresolved names.
- **DE_BRUIJN.md** — new §9 "Debugging with `--explain-slots`" with worked examples.
- **`uv lock --check` in CI** ([#390](https://github.com/aallan/vera/issues/390)) — lint job now verifies `uv.lock` is consistent with `pyproject.toml` on every PR. `CONTRIBUTING.md` updated to document `uv sync` as the recommended install method. Closes [#390](https://github.com/aallan/vera/issues/390).

### Fixed
- **Z3 solver timeout documented** ([#391](https://github.com/aallan/vera/issues/391)) — the 10-second per-contract timeout was already implemented in `vera/smt.py` but undocumented. `spec/06-contracts.md` §6.4.3 now explicitly documents the default. Closes [#391](https://github.com/aallan/vera/issues/391).

## [0.0.107] - 2026-04-07

### Added
- **Validate `vera run` commands in `examples/README.md`** ([#361](https://github.com/aallan/vera/issues/361)) — new `scripts/check_examples_readme.py` parses every `vera run` command in the example index tables, verifies the referenced `.vera` file exists, and verifies any `--fn <name>` target is a public function in that file. Wired into pre-commit (triggers on `examples/README.md` or `.vera` changes) and CI. Closes [#361](https://github.com/aallan/vera/issues/361).

## [0.0.106] - 2026-03-31

### Added
- **`vera test` String and Float64 input generation** ([#169](https://github.com/aallan/vera/issues/169)) — `vera test` now generates Z3 inputs for `String` and `Float64` parameters, removing the `SKIPPED (cannot generate String inputs (see #169))` limitation for those types. String uses Z3's sequence sort with a 50-character length cap; Float64 uses Z3's mathematical real sort with boundary seeding (0.0, ±1.0, ±0.5, ±10.0, ±1e10, ±1e-10). Both types route through the `raw_args` calling convention so that String's two-i32 WASM ABI is handled correctly. IEEE 754 special values (NaN, ±∞, subnormals) are not generated — use explicit test inputs for those cases. ADT input generation remains unsupported ([#440](https://github.com/aallan/vera/issues/440)). Closes [#169](https://github.com/aallan/vera/issues/169).

## [0.0.105] - 2026-03-30

### Added
- **Typed holes** ([#226](https://github.com/aallan/vera/issues/226)) — `?` is now a valid expression placeholder for partial programs. `vera check` reports each hole as a `W001` warning (not an error) with the expected type and all available De Bruijn slot bindings. Programs with holes type-check successfully (`ok: true`) but cannot compile (`E614`). The `--json` output includes hole warnings in the `warnings` array with machine-readable expected type and fix hint. New error code `W001` (typed hole warning) and `E614` (holes block compilation). Conformance test `ch03_typed_holes.vera`. Closes [#226](https://github.com/aallan/vera/issues/226).
- SKILL.md: new [Typed Holes](SKILL.md#typed-holes) section with workflow examples; best-practices tip on incremental development with holes; error code table updated with `W001` and `E614`.
- AGENTS.md: workflow section updated with typed-holes iterative pattern; error code table updated.

## [0.0.104] - 2026-03-29

### Fixed
- **Type inference for bare `None`/`Err` constructors in generic combinator calls** ([#293](https://github.com/aallan/vera/issues/293)) — `option_unwrap_or(None, 99)`, `result_unwrap_or(Err("oops"), 0)`, and `option_map(None, fn(...) {...})` now type-check and compile correctly without requiring a typed `let` binding workaround. Three-layer fix: (1) the checker's fresh-TypeVar overwrite rule in `resolution.py` — later concrete resolutions now overwrite tentative fresh-TypeVar placeholders; (2) the monomorphizer's `_get_arg_type_info` now uses `_ctor_adt_tp_indices` to correctly map sparse constructor fields to their ADT type-param positions (e.g. `Err`'s single field maps to Result's `E`, not `T`); (3) added missing `StringLit` / `InterpolatedString` / `ArrayLit` cases to the monomorphizer's `_infer_vera_type_name`. Closes [#293](https://github.com/aallan/vera/issues/293).

### Added
- Conformance test `ch09_none_err_inference.vera` (level: run) covering all four bare-constructor inference cases.

## [0.0.103] - 2026-03-29

### Added
- **`--quiet` flag for `vera check` / `vera verify`** ([#382](https://github.com/aallan/vera/issues/382)) — suppresses the `OK: ...` and `Verification: ...` success output; errors still print normally. Useful for CI scripts that only need the exit code. Closes [#382](https://github.com/aallan/vera/issues/382).
- **De Bruijn conformance tests: deep let-chains** ([#393](https://github.com/aallan/vera/issues/393)) — `ch03_slot_let_chains.vera` at `verify` level: five sequential `let @Int =` bindings where each doubles the previous; `ensures(@Int.result == 32)` is proved by Z3. Confirms slot indices resolve correctly through deep same-typed `let` chains. Closes [#393](https://github.com/aallan/vera/issues/393).
- **De Bruijn conformance tests: non-commutative operations** ([#394](https://github.com/aallan/vera/issues/394)) — `ch03_slot_noncommutative.vera` at `verify` level: subtraction, division, and comparison with `ensures` contracts that encode the exact De Bruijn ordering. Swapping `@Int.0` / `@Int.1` produces a Z3 counterexample. Closes [#394](https://github.com/aallan/vera/issues/394).
- **Known Limitations section in SKILL.md** ([#404](https://github.com/aallan/vera/issues/404)) — table listing six current implementation limits with issue links: `vera test` String/Float64 skip (#169), bare `None`/`Err` type inference (#293), effect row variable unification (#294), `map_new()`/`set_new()` type context, Inference `max_tokens`/temperature (#370), Inference user-defined handlers (#372). Closes [#404](https://github.com/aallan/vera/issues/404).
- **Conformance test: nested effect handlers** ([#395](https://github.com/aallan/vera/issues/395)) — `ch07_nested_handlers.vera` at `check` level validates correct effect rows on functions that compose multiple algebraic effects. Closes [#395](https://github.com/aallan/vera/issues/395).
- **Conformance test: cross-module contracts** ([#396](https://github.com/aallan/vera/issues/396)) — `ch07_cross_module_contracts.vera` + `ch07_cross_module_contracts_lib.vera` at `check` level validates that contract declarations are visible and enforced across module boundaries. Closes [#396](https://github.com/aallan/vera/issues/396).
- **SKILL.md served from veralang.dev** ([#398](https://github.com/aallan/vera/issues/398)) — `docs/SKILL.md` is now a generated artefact (from root `SKILL.md`, via `build_site.py`), making the language reference available at `veralang.dev/SKILL.md` — on-domain, cacheable, stable. All `href` references in `docs/index.html` updated from raw GitHub URLs to `/SKILL.md`. JSON-LD TechArticle URL updated to `https://veralang.dev/SKILL.md`. Closes [#398](https://github.com/aallan/vera/issues/398).
- **`vera version` / `--version` / `-V` CLI command** ([#381](https://github.com/aallan/vera/issues/381)) — prints `vera X.Y.Z` on stdout. Closes [#381](https://github.com/aallan/vera/issues/381).
- **CycloneDX SBOM generation in CI** ([#389](https://github.com/aallan/vera/issues/389)) — new `sbom` job runs `cyclonedx-py environment --of JSON` on every push, uploading a CycloneDX JSON SBOM as a 90-day artifact. Closes [#389](https://github.com/aallan/vera/issues/389).

### Fixed
- **`Http.post` missing `Content-Type: application/json`** ([#354](https://github.com/aallan/vera/issues/354)) — the Python host function now sets the header on the `urllib.request.Request`; the browser runtime sets `xhr.setRequestHeader('Content-Type', 'application/json')`. `Http.post` is intentionally JSON-only at the Vera level; custom `Content-Type` headers tracked in [#351](https://github.com/aallan/vera/issues/351). Closes [#354](https://github.com/aallan/vera/issues/354).
- **`vera test` skip messages now name the unsupported type** ([#383](https://github.com/aallan/vera/issues/383)) — was `SKIPPED (unsupported parameter types)`; now `SKIPPED (cannot generate String inputs (see #169))`. The specific type name is extracted via the new `_unsupported_type_names` helper. Closes [#383](https://github.com/aallan/vera/issues/383).
- **HTTP host functions missing `timeout`** — `host_http_get` and `host_http_post` now pass `timeout=_INFERENCE_TIMEOUT` to `urllib.request.urlopen`, consistent with the Inference effect.

### Security
- **`ruff check --select S` added to lint job** ([#388](https://github.com/aallan/vera/issues/388)) — 32 Bandit-equivalent S-rule findings audited and suppressed with `# noqa` comments where appropriate (S310 intentional HTTPS calls, S101 compiler invariant asserts, S105 parse-token false positives). `ruff>=0.9` added to `[dev]` dependencies. Closes [#388](https://github.com/aallan/vera/issues/388).
- **`dependency-audit` CI job** ([#384](https://github.com/aallan/vera/issues/384)) — `pip-audit --skip-editable` checks all installed packages against the OSV database on every push. `pygments 2.19.2` has `CVE-2026-4539` (transitive via pytest/rich, no fix release yet) — suppressed with `--ignore-vuln`. Closes [#384](https://github.com/aallan/vera/issues/384).
- **CI workflow hardening** ([#385](https://github.com/aallan/vera/issues/385)) — `persist-credentials: false` on all checkout steps (`artipacked`); per-job `permissions: contents: read` with `security-events: write` on the security job (`excessive-permissions`). SHA pinning of action refs deferred to [#390](https://github.com/aallan/vera/issues/390). Closes [#385](https://github.com/aallan/vera/issues/385).

## [0.0.102] - 2026-03-28

### Added
- **Type-aware CLI argument passing** ([#263](https://github.com/aallan/vera/issues/263)) — `vera run file.vera --fn f -- arg` now accepts all Vera scalar and string types, not just integers. Arguments are parsed using the function's WASM signature: `Int`/`Nat` → integer literal, `Float64` → decimal literal, `Bool` → `true`/`false` (case-insensitive), `Byte` → integer 0–255, `String` → text (allocated into WASM linear memory). Type-mismatch errors identify the bad argument and expected type. `CompileResult.fn_param_types` (new field) exposes per-function WASM-level type tags (`i64`, `f64`, `i32`, `i32_pair`) so the host runtime can handle memory allocation and invocation correctly for each parameter kind. Closes [#263](https://github.com/aallan/vera/issues/263). Closes [#403](https://github.com/aallan/vera/issues/403).
- **Multi-layer agent discovery metadata** ([#400](https://github.com/aallan/vera/issues/400)) — veralang.dev now exposes `SKILL.md` through four machine-readable layers: `<head>` link elements (`rel="alternate" type="text/markdown"`, `rel="llms-txt"`, `rel="llms-full-txt"`), an inline `<script type="text/llms.txt">` block (Vercel convention), JSON-LD `TechArticle` entries for `SKILL.md` and `AGENTS.md`, and semantic attributes on the existing CTA button. HTTP headers skipped — GitHub Pages does not support custom response headers. Closes [#400](https://github.com/aallan/vera/issues/400).

### Fixed
- **E609 false positive on `Option<T>` return types across modules** ([#360](https://github.com/aallan/vera/issues/360)) — the name-collision checker incorrectly flagged `Option`, `Result`, and other built-in ADTs as user-defined names when they appeared as return types in imported modules. Fixed by pre-seeding `builtin_adt_names` before scanning module declarations. Closes [#360](https://github.com/aallan/vera/issues/360).
- **Pipe operator into module-qualified calls** ([#326](https://github.com/aallan/vera/issues/326)) — `value |> mod::fn(args)` previously type-checked the right-hand side in isolation, ignoring the piped argument. The checker now desugars to a `ModuleCall` with the LHS prepended to the argument list. Closes [#326](https://github.com/aallan/vera/issues/326).
- **`/dev/stdin` double-read** ([#335](https://github.com/aallan/vera/issues/335)) — all CLI commands (`check`, `verify`, `compile`, `run`, `ast`, `test`) previously called `p.read_text()` for the source string and then `parse_file(path)` which re-opened the same path. For `/dev/stdin` the second open returns empty content. Fixed by extracting `_load_and_parse(path)` which reads the source once and passes it directly to `parse()`. For stdin paths, returns `Path.cwd()/"stdin.vera"` so module resolution and compile output naming use CWD. Closes [#335](https://github.com/aallan/vera/issues/335).

## [0.0.101] - 2026-03-27

### Added
- **Inference effect** ([#61](https://github.com/aallan/vera/issues/61)) — built-in `<Inference>` algebraic effect with one operation: `Inference.complete(String → Result<String, String>)`. Sends a prompt to the configured LLM provider and returns `Ok(completion)` or `Err(message)`. Provider auto-detected from whichever API key is set; override with `VERA_INFERENCE_PROVIDER`. Model configurable via `VERA_INFERENCE_MODEL`. Default models: Anthropic → `claude-haiku-4-5-20251001`, OpenAI → `gpt-4o-mini`, Moonshot → `moonshot-v1-8k`. Implemented via host imports (Python `urllib.request`). Built-in effect — no `effect Inference { ... }` declaration needed. Browser runtime returns a detailed `Err` explaining why API keys cannot be embedded in client-side JavaScript. New conformance test `ch09_inference` (64 programs, was 63). New example `inference.vera`. Closes [#61](https://github.com/aallan/vera/issues/61).

### Known limitations
- `complete` only — `embed` (returning `Array<Float64>`) deferred to a follow-up
- No streaming responses — full completion only
- No system prompt — single `complete(user_prompt)` call; structured prompting via `string_concat`
- No token limits or temperature controls — Anthropic: `max_tokens` hardcoded to 1024; OpenAI and Moonshot use provider defaults ([#370](https://github.com/aallan/vera/issues/370))
- User-defined `handle[Inference]` handlers (for mocking, local models, replay) are planned for a future release

## [0.0.100] - 2026-03-26

### Added
- **Html standard library type** ([#311](https://github.com/aallan/vera/issues/311)) — built-in `HtmlNode` ADT (`HtmlElement`, `HtmlText`, `HtmlComment`) with 5 built-in functions: `html_parse`, `html_to_string`, `html_query`, `html_text`, `html_attr`. Lenient HTML parsing (like browsers). Simple CSS selector query support (tag, class, ID, attribute, descendant combinator). Implemented via host imports (Python `html.parser`). `html_attr` is a pure Vera prelude function using `map_get`. New conformance test `ch09_html` (63 programs, was 62). New example `html.vera`.

## [0.0.99] - 2026-03-25

### Added
- **Http effect** ([#57](https://github.com/aallan/vera/issues/57)) — built-in `<Http>` algebraic effect with two operations: `Http.get(url)` and `Http.post(url, body)`, both returning `Result<String, String>`. Implemented via host imports (Python `urllib.request` / JavaScript `fetch`). Composes with `json_parse` for typed API responses. Built-in effect — no `effect Http { ... }` declaration needed. New conformance test `ch09_http` (62 programs, was 61). New example `http.vera`. Browser runtime support. Closes #57.

### Known limitations
- No custom headers ([#351](https://github.com/aallan/vera/issues/351))
- No HTTP methods beyond GET/POST ([#352](https://github.com/aallan/vera/issues/352))
- No response status code access ([#353](https://github.com/aallan/vera/issues/353))
- No request timeout configuration ([#354](https://github.com/aallan/vera/issues/354))
- No streaming responses ([#355](https://github.com/aallan/vera/issues/355))
- No cookie/session management ([#356](https://github.com/aallan/vera/issues/356))

## [0.0.98] - 2026-03-25

### Added
- **Json standard library type** ([#58](https://github.com/aallan/vera/issues/58)) — built-in `Json` ADT (`JNull`, `JBool`, `JNumber`, `JString`, `JArray`, `JObject`) with 8 built-in functions: `json_parse`, `json_stringify`, `json_get`, `json_array_get`, `json_array_length`, `json_keys`, `json_has_field`, `json_type`. Implemented via host imports (Python `json` / JavaScript `JSON`). Opaque i32 handles following the Map/Set pattern. New conformance test `ch09_json` (61 programs, was 60). New example `json.vera`. Browser runtime support.
- New conformance test `ch09_decimal_generics` (60 programs, was 59) — exercises `option_unwrap_or`, `match`, and `decimal_compare` with Decimal.
- 12 new unit tests for opaque handle monomorphization paths (Decimal, Map, Set).

### Fixed
- **Monomorphization of opaque handle types** ([#341](https://github.com/aallan/vera/issues/341)) — generic prelude functions (`option_unwrap_or`, `match`) now work with all opaque handle types: `Option<Decimal>`, `Option<Map<K,V>>`, `Option<Set<T>>`, `Ordering` from `decimal_compare`. The monomorphizer now preserves full parameterized type names (e.g. `Map<String, Int>`) through type inference, substitution, and name mangling. Previously, type arguments were dropped during inference, causing `option_unwrap_or$Map` to fail codegen. Closes #341.

## [0.0.97] - 2026-03-24

### Added
- **Decimal type for exact arithmetic** ([#333](https://github.com/aallan/vera/issues/333)) — 14 built-in operations (`decimal_from_int`, `decimal_from_float`, `decimal_from_string`, `decimal_to_string`, `decimal_to_float`, `decimal_add`, `decimal_sub`, `decimal_mul`, `decimal_div`, `decimal_neg`, `decimal_compare`, `decimal_eq`, `decimal_round`, `decimal_abs`) via host imports (Python `decimal.Decimal` / JS string-based decimal). New conformance test `ch09_decimal` (59 programs, was 58). Browser runtime support. Closes #333.

## [0.0.96] - 2026-03-24

### Changed
- **Documentation sweep for collections** ([#62](https://github.com/aallan/vera/issues/62), PR 3/3) — fix stale "future collections" language in spec, update README version and Ch 9 description, add Map/Set to SKILL.md composite types and common mistakes, update example counts across all docs (25→28). New `examples/collections.vera` showcasing word-frequency analysis with Map and Set operations. Closes #62.

## [0.0.95] - 2026-03-24

### Added
- **Set\<T\> collection type** ([#62](https://github.com/aallan/vera/issues/62), PR 2/3) — six built-in operations (`set_new`, `set_add`, `set_contains`, `set_remove`, `set_size`, `set_to_array`) with `Eq<T> + Hash<T>` ability constraints. Host-import pattern (Python sets / JS Sets behind opaque i32 handles). Pure functional semantics. New conformance test `ch09_set` (58 programs, was 57). 25 unit tests.
- **Native JS coverage issue** ([#337](https://github.com/aallan/vera/issues/337)) — tracked for future c8 integration.
- **Stdin compilation bug** ([#335](https://github.com/aallan/vera/issues/335)) — filed and added to Known Bugs.

### Changed
- **README test counts** — removed hardcoded counts, TESTING.md is now the single source of truth.

## [0.0.94] - 2026-03-23

### Added
- **Map\<K, V\> collection type** ([#62](https://github.com/aallan/vera/issues/62), PR 1/3) — eight built-in operations (`map_new`, `map_insert`, `map_get`, `map_contains`, `map_remove`, `map_size`, `map_keys`, `map_values`) with `Eq<K> + Hash<K>` ability constraints. Implemented via host imports (Python dicts / JS Maps behind opaque i32 handles). Pure functional semantics — `map_insert` and `map_remove` return new maps. New conformance test `ch09_map` (57 programs, was 56). 40 new unit tests. Browser runtime support.
- **Decimal type issue** ([#333](https://github.com/aallan/vera/issues/333)) — split from #62 as independent future work.

### Fixed
- **Type inference for zero-argument generic functions** — `map_new()` and similar zero-arg generic calls now resolve type variables from expected type context (bidirectional coercion). Fixed unification to skip ADT args whose TypeVars match the callee's own forall vars.

## [0.0.93] - 2026-03-20

### Changed
- **Standard prelude — eliminate boilerplate** ([#289](https://github.com/aallan/vera/issues/289)) — `Option<T>`, `Result<T, E>`, `Ordering`, and `UrlParts` are now unconditionally injected by the prelude, eliminating 2–6 lines of identical `data` declarations from every program that uses these types. Option/Result combinators and array operations are also always available. User-defined `data` declarations with the same name shadow the prelude versions. Non-standard variants (e.g. `data Option<T> { None, Just(T) }`) correctly suppress combinator injection. New conformance test `ch09_prelude` (conformance suite: 55→56 programs). Boilerplate removed from 8 conformance programs and 8 examples. Closes #289.

## [0.0.92] - 2026-03-19

### Changed
- **BREAKING: Built-in function naming audit** ([#288](https://github.com/aallan/vera/issues/288)) — renamed 14 inconsistently-named built-in functions to follow the dominant `domain_verb` convention. String operations gain `string_` prefix (`strip` → `string_strip`, `upper` → `string_upper`, etc.), float predicates gain `float_` prefix (`is_nan` → `float_is_nan`, `is_infinite` → `float_is_infinite`), and `to_float` becomes `int_to_float`. Closes #288.

### Added
- **Naming convention documentation** — formal naming rules added to spec §9.1.1, SKILL.md, vera/README.md, and CONTRIBUTING.md. Four patterns: `domain_verb` (dominant), `source_to_target` (conversions), `domain_is_predicate` (boolean tests), prefix-less (math universals only).

## [0.0.91] - 2026-03-19

### Added
- **Array operations** ([#133](https://github.com/aallan/vera/issues/133)) — four new built-in array functions: `array_slice` (WASM intrinsic with index clamping), `array_map` (generic, element type can change), `array_filter` (predicate-based selection), and `array_fold` (left fold with arbitrary accumulator type). Higher-order operations implemented via prelude source injection with recursive helpers. 15 unit tests. Closes #133.

### Fixed
- **De Bruijn reindexing during monomorphization** ([#316](https://github.com/aallan/vera/issues/316)) — when distinct type variables collapse to the same concrete type, slot reference indices are now correctly adjusted
- **Transitive monomorphization** ([#317](https://github.com/aallan/vera/issues/317)) — generic functions calling other generic functions now correctly generate all required specializations via worklist-based closure
- **WASM type inference gaps** ([#313](https://github.com/aallan/vera/issues/313), [#314](https://github.com/aallan/vera/issues/314), [#315](https://github.com/aallan/vera/issues/315), [#318](https://github.com/aallan/vera/issues/318)) — `_is_pair_type_name` now matches bare `Array`, `_infer_vera_type` handles `IndexExpr` and `IfExpr`, `_infer_fncall_vera_type` handles `apply_fn`, `_get_arg_type_info` handles `ArrayLit` and `FnCall`

## [0.0.90] - 2026-03-13

### Added
- **Abilities release** ([#60](https://github.com/aallan/vera/issues/60)) — four built-in abilities (`Eq`, `Ord`, `Hash`, `Show`) with full codegen support. Includes the built-in `Ordering` ADT (`Less`, `Equal`, `Greater`), ADT auto-derivation for `Eq` (structural equality for simple enums and ADTs with primitive fields), `compare` rewriting via Pass 1.6 AST transformation, `show`/`hash` dispatch at WASM level (FNV-1a for String hashing), and string equality via byte-by-byte comparison. Constraint satisfaction checked for all four abilities (E613). 20 unit tests, extended conformance test with 20 test functions. Closes #60.

## [0.0.89] - 2026-03-12

### Added
- **Option/Result combinators** ([#211](https://github.com/aallan/vera/issues/211)) — five prelude functions that eliminate common match boilerplate: `option_unwrap_or`, `option_map`, `option_and_then`, `result_unwrap_or`, `result_map`. Implemented via source injection (parsed Vera AST, injected before codegen). Includes compiler fixes for generic type alias return type inference in closures, closure signature deduplication across functions, and AnonFn type variable inference in the monomorphizer. New conformance test, 12 unit tests, spec section 9.3.7.

### Changed
- **`map_option` renamed to `option_map`** — all references across spec, examples, and tests updated to follow the `domain_verb` naming convention ([#288](https://github.com/aallan/vera/issues/288)).

## [0.0.88] - 2026-03-12

### Fixed
- **Formatter comment repositioning** ([#274](https://github.com/aallan/vera/issues/274)) — comments inside function bodies were moved to the file footer during formatting. Extended the anchor system to collect interior AST spans (statements, result expressions) and emit comments at the correct positions within blocks, if/else branches, match arms, and handler bodies. Added `_collect_interior_anchors` recursive walker. 7 new tests, `examples/string_ops.vera` reformatted to canonical form. Closes #274.

## [0.0.87] - 2026-03-11

### Added
- **FizzBuzz example** — complete runnable program demonstrating recursion as iteration with IO effects (`examples/fizzbuzz.vera`)
- **"Recursion as iteration" section** in README "What Vera Looks Like" — explains the standard Vera pattern for counted iteration
- **"Iteration" section** in SKILL.md — documents the tail-recursive loop pattern for agents
- **De Bruijn slot reference reminder** in CLAUDE.md — documents that `@T.0` = most recent (last) parameter

### Fixed
- **Verifier branch-condition bug** documented ([#283](https://github.com/aallan/vera/issues/283)) — call-site precondition checking doesn't use if-guard path conditions; added to Known Bugs with workaround

## [0.0.86] - 2026-03-11

### Added
- **Regex support** ([#231](https://github.com/aallan/vera/issues/231)):
  Four new pure functions for regular expression matching on strings:
  `regex_match`, `regex_find`, `regex_find_all`, `regex_replace`.
  All return `Result` types for safe handling of invalid patterns.
  Implemented as WASM host imports — Python's `re` module for wasmtime,
  JavaScript's `RegExp` for the browser runtime. Browser parity verified.
- New conformance test `ch09_regex` (conformance suite: 52→53 programs)
- New example `examples/regex.vera` (example suite: 23→24 programs)
- Spec §9.6.15 "Regular Expressions"
- 16 new tests (10 codegen + 6 type checker) plus browser parity coverage

## [0.0.85] - 2026-03-11

### Added
- **Browser runtime for compiled WASM** ([#273](https://github.com/aallan/vera/issues/273)):
  A self-contained JavaScript runtime (`vera/browser/runtime.mjs`, ~730 lines) that
  runs any compiled Vera `.wasm` module in the browser or Node.js. Uses
  `WebAssembly.Module.imports()` to introspect the module's imports and dynamically
  builds the host binding object — no code generation needed. The same runtime file
  works with every compiled Vera program, from hello-world (1 import) to markdown-heavy
  programs (15+ imports).
  Includes JavaScript implementations of all host bindings: IO operations (print,
  read_line, args, exit, get_env, read_file/write_file with browser-appropriate
  adaptations), State\<T\> (dynamically pattern-matched from import names),
  contract_fail, and all 5 Markdown operations (with a bundled JS Markdown parser).
- New CLI flag: `vera compile --target browser` produces a ready-to-serve browser
  bundle (module.wasm + vera-runtime.mjs + index.html) in a single command
- New `vera/browser/` package: `runtime.mjs` (JS runtime), `harness.mjs` (Node.js
  test harness), `emit.py` (browser bundle emission)
- 56 new browser parity tests ensuring identical output between Python/wasmtime and
  Node.js/JS-runtime across IO, State, contracts, Markdown, and all compilable examples
- Browser parity CI job (Node.js 22) and pre-commit hook triggered by changes to
  host binding surface (`vera/browser/`, `vera/codegen/api.py`, `vera/wasm/markdown.py`,
  `vera/markdown.py`)
- Spec §12.4.3 (Contract Violations) and §12.4.4 (Markdown Operations) — host binding
  documentation missing from v0.0.84
- Spec §12.9 (Browser Runtime) — JavaScript runtime architecture and usage

## [0.0.84] - 2026-03-11

### Added
- **Markdown standard library** ([#147](https://github.com/aallan/vera/issues/147)):
  Two new built-in ADTs for typed Markdown document representation:
  `MdInline` (6 constructors: MdText, MdCode, MdEmph, MdStrong, MdLink, MdImage)
  and `MdBlock` (8 constructors: MdParagraph, MdHeading, MdCodeBlock, MdBlockQuote,
  MdList, MdThematicBreak, MdTable, MdDocument).
  Five new pure functions: `md_parse(String → Result<MdBlock, String>)`,
  `md_render(MdBlock → String)`, `md_has_heading(MdBlock, Nat → Bool)`,
  `md_has_code_block(MdBlock, String → Bool)`,
  `md_extract_code_blocks(MdBlock, String → Array<String>)`.
  All implemented as WASM host imports with a hand-written Python parser —
  the first pure functions using the host-binding pattern.
  The WASM import interface is the portability contract: the same `.wasm`
  binary works with any host runtime (Python, JavaScript, Rust) that provides
  matching implementations.
- New conformance test `ch09_markdown` (conformance suite: 51→52 programs)
- New example `examples/markdown.vera` — parse, query, extract, and render Markdown
- 78 new tests (59 parser/renderer + 6 type checker + 8 codegen + 5 conformance)

### Changed
- **Spec §9.3 reorganization:** UrlParts (from §9.6.13), Future\<T\> (from §9.5.4),
  MdInline, and MdBlock are now documented in §9.3 (Built-in ADTs) as §9.3.3–§9.3.6.
  Function specs remain in their original sections with cross-references.

## [0.0.83] - 2026-03-11

### Added
- **Tuple type WASM codegen** ([#267](https://github.com/aallan/vera/issues/267)):
  Tuple construction (`Tuple(1, "hello", true)`) and destructuring now compile to WASM.
  Match destructuring (`Tuple(@Int, @String) -> ...`) extracts fields from heap-allocated Tuples.
  `LetDestruct` (`let Tuple<@Int, @String> = expr;`) works for Tuples and all single-constructor
  ADTs (including UrlParts, Future, and user-defined types).
  Tuples are variadic — any arity from 1 field upward is supported.
- New conformance test `ch02_tuple_basic` (conformance suite: 50→51 programs)
- Updated `examples/url_parsing.vera` with LetDestruct demonstration
- 15 new tests (5 type checker + 10 codegen)

## [0.0.82] - 2026-03-11

### Added
- **`<Async>` effect with `Future<T>` type** ([#59](https://github.com/aallan/vera/issues/59)):
  New `Async` marker effect and `Future<T>` ADT for asynchronous computation.
  New `async(@T -> @Future<T>)` — wraps a value in a future (eager evaluation).
  New `await(@Future<T> -> @T)` — unwraps a future to its result.
  `Future<T>` is WASM-transparent — same runtime representation as `T`, zero overhead.
  The reference implementation uses sequential evaluation; true concurrency will be
  available via WASI 0.3 native `future<T>` support ([#237](https://github.com/aallan/vera/issues/237)).
- New conformance test `ch09_async` (conformance suite: 49→50 programs)
- New example `examples/async_futures.vera` — async/await roundtrip and composition demo
- 15 new tests (7 type checker + 8 codegen)

## [0.0.81] - 2026-03-10

### Added
- **URL parsing and joining** ([#232](https://github.com/aallan/vera/issues/232), Phase 2):
  New `url_parse(@String -> @Result<UrlParts, String>)` — RFC 3986 URL decomposition
  into scheme, authority, path, query, and fragment components.
  New `url_join(@UrlParts -> @String)` — reassembles a `UrlParts` value into a URL string.
  New built-in `UrlParts` ADT type with five String fields.
- New conformance test `ch09_url_parsing` (conformance suite: 48→49 programs)
- New example `examples/url_parsing.vera` — parse, extract components, join, and error demo
- 29 new tests (4 type checker + 25 codegen)

### Fixed
- **ADT constructors with String/Array fields** ([#266](https://github.com/aallan/vera/issues/266)):
  Layout computation (`_wasm_type_size`, `_wasm_type_align`) now handles `i32_pair`
  (String/Array representation). User-defined ADTs with String fields compile correctly.

## [0.0.80] - 2026-03-10

### Added
- **URL percent-encoding and decoding** ([#232](https://github.com/aallan/vera/issues/232)):
  New `url_encode(@String -> @String)` — RFC 3986 percent-encoding, leaving
  unreserved characters unchanged.
  New `url_decode(@String -> @Result<String, String>)` — percent-decoding with
  error handling for invalid `%XX` sequences.
- New conformance test `ch09_url_encoding` (conformance suite: 47→48 programs)
- New example `examples/url_encoding.vera` — encode, decode, and round-trip demo
- 21 new tests (4 type checker + 17 codegen)

## [0.0.79] - 2026-03-10

### Added
- **Close #234: Base64 encoding and decoding** ([#234](https://github.com/aallan/vera/issues/234)):
  New `base64_encode(@String -> @String)` — standard Base64 (RFC 4648) encoding.
  New `base64_decode(@String -> @Result<String, String>)` — Base64 decoding with
  error handling for invalid length or characters.
- New conformance test `ch09_base64` (conformance suite: 46→47 programs)
- New example `examples/base64.vera` — encode, decode, and round-trip demo
- 20 new tests (4 type checker + 16 codegen)

## [0.0.78] - 2026-03-10

### Added
- **Close #209: Array construction builtins** ([#209](https://github.com/aallan/vera/issues/209)):
  New `array_range(@Int, @Int -> @Array<Int>)` — integer range [start, end), empty
  if start >= end. New `array_concat(forall<T> @Array<T>, @Array<T> -> @Array<T>)` —
  merge two arrays into a new array.
- New conformance test `ch04_array_construction` (conformance suite: 45→46 programs)
- 17 new tests (4 type checker + 7 codegen array_range + 6 codegen array_concat)

### Changed
- **Breaking:** `length` renamed to `array_length`. The array length builtin now
  follows the same `array_` prefix convention used by string builtins (`string_length`,
  `string_concat`, etc.). All code using `length()` on arrays must be updated.
- **Breaking:** `array_push` renamed to `array_append`. Clearer intent and consistent
  naming with the new array builtins.

## [0.0.77] - 2026-03-10

### Added
- **Close #200: Parsing completeness** ([#200](https://github.com/aallan/vera/issues/200)):
  New `parse_int` (`String → Result<Int, String>`) and `parse_bool`
  (`String → Result<Bool, String>`) built-in functions. `parse_int` handles
  optional `+`/`-` sign. `parse_bool` is strict lowercase only — only `"true"`
  and `"false"` are valid.
- New conformance test `ch04_parse_completeness` (conformance suite: 44→45 programs)
- 22 new tests (6 type checker + 8 codegen parse_int + 6 codegen parse_bool + 2 codegen parse_float64 error cases)

### Changed
- **Breaking:** `parse_float64` return type changed from `Float64` to
  `Result<Float64, String>`. Previously returned `0.0` silently on invalid input;
  now returns `Err(msg)` with a descriptive error message. All four parse functions
  (`parse_nat`, `parse_int`, `parse_float64`, `parse_bool`) now consistently
  return `Result<T, String>`.

## [0.0.76] - 2026-03-10

### Added
- **Close #230: String interpolation** ([#230](https://github.com/aallan/vera/issues/230)):
  New `\(expr)` syntax inside double-quoted strings for ergonomic string building.
  Non-String expressions of type Int, Nat, Bool, Byte, and Float64 are automatically
  converted using the appropriate `*_to_string` built-in. `InterpolatedString` is a
  first-class AST node (canonical form, survives formatting). Touches every compiler
  stage: grammar, transformer, type checker, formatter, and WASM codegen.
- New conformance test `ch04_string_interpolation` (conformance suite: 43→44 programs)
- 18 new tests (9 type checker + 9 codegen end-to-end)
- Spec Sections 1.4 "String Interpolation" and 4.13.1 "String Interpolation"

## [0.0.75] - 2026-03-10

### Added
- **Close #213: string_repeat builtin** ([#213](https://github.com/aallan/vera/issues/213)):
  New `string_repeat` function (`String, Nat → String`) that repeats a string N
  times. Uses a single-allocation loop with modulo indexing. Pure, Tier 3
  (runtime-tested).
- 7 new tests (2 type checker + 5 codegen end-to-end)

## [0.0.74] - 2026-03-09

### Added
- **Close #210: from_char_code builtin** ([#210](https://github.com/aallan/vera/issues/210)):
  New `from_char_code` function (`Nat → String`) that creates a single-character
  string from an ASCII code point. Inverse of the existing `char_code`. Pure,
  Tier 3 (runtime-tested).
- 7 new tests (2 type checker + 5 codegen end-to-end)

## [0.0.73] - 2026-03-09

### Added
- **Close #198: String search and transformation builtins** ([#198](https://github.com/aallan/vera/issues/198)):
  Nine new built-in functions for string search and transformation:
  `string_contains` (String,String→Bool), `starts_with` (String,String→Bool),
  `ends_with` (String,String→Bool), `index_of` (String,String→Option\<Nat\>),
  `to_upper` (String→String), `to_lower` (String→String),
  `replace` (String,String,String→String), `split` (String,String→Array\<String\>),
  `join` (Array\<String\>,String→String). All are pure and Tier 3 (runtime-tested).
- New conformance test `ch09_string_search` (conformance suite: 42→43 programs)
- 55 new tests (18 type checker + 37 codegen end-to-end)
- Spec Sections 9.6.6 "String Search" and 9.6.7 "String Transformation"

## [0.0.72] - 2026-03-09

### Added
- **Close #212: Float64 special value operations** ([#212](https://github.com/aallan/vera/issues/212)):
  Four new built-in functions for detecting and constructing IEEE 754 special
  Float64 values: `is_nan` (Float64→Bool), `is_infinite` (Float64→Bool),
  `nan` (→Float64), and `infinity` (→Float64). All are Tier 3 (runtime-tested).
- New conformance test `ch10_float_predicates` (conformance suite: 41→42 programs)
- 25 new tests (8 type checker + 17 codegen end-to-end)
- Spec Section 9.6.5 "Float64 Predicates" with full signatures and contracts

## [0.0.71] - 2026-03-09

### Added
- **Close #208: Numeric type conversions** ([#208](https://github.com/aallan/vera/issues/208)):
  Six new built-in functions for explicit conversion between numeric types:
  `to_float` (Int→Float64), `float_to_int` (Float64→Int, truncation toward zero),
  `nat_to_int` (Nat→Int, identity), `int_to_nat` (Int→Option\<Nat\>, checked),
  `byte_to_int` (Byte→Int, zero-extension), and `int_to_byte` (Int→Option\<Byte\>,
  checked). Widening conversions always succeed; narrowing conversions return
  `Option` for safety. `nat_to_int` and `byte_to_int` are SMT-verifiable (Tier 1).
- New conformance test `ch09_type_conversions` (conformance suite: 40→41 programs)
- 38 new tests (12 type checker + 26 codegen end-to-end)
- Spec Section 9.6.4 "Type Conversions" with full signatures and contracts

## [0.0.70] - 2026-03-09

### Added
- **Close #199: Numeric math builtins** ([#199](https://github.com/aallan/vera/issues/199)):
  Eight new built-in functions for common mathematical operations: `abs` (Int→Nat),
  `min`/`max` (Int,Int→Int), `floor`/`ceil`/`round` (Float64→Int), `sqrt`
  (Float64→Float64), and `pow` (Float64,Int→Float64). All are pure and available
  without imports. Integer builtins (`abs`, `min`, `max`) are fully verifiable by
  Z3 (Tier 1). Float builtins use native WASM instructions. `round` uses IEEE 754
  banker's rounding. `pow` takes an integer exponent with negative exponent support.
- New conformance test `ch09_numeric_builtins` (conformance suite: 39→40 programs)
- 41 new tests (13 type checker + 28 codegen end-to-end)
- Spec Section 9.6.3 "Numeric Operations" with full signatures and contracts

## [0.0.69] - 2026-03-06

### Fixed
- **Close #241: Byte literal coercion** ([#241](https://github.com/aallan/vera/issues/241)):
  Integer literals 0–255 are now accepted as `Byte` when the expected type is
  `Byte` (bidirectional type checking). The `ch01_byte_literals` conformance test
  is promoted from `check` to `run` level.
- **Close #242: `array_push` codegen** ([#242](https://github.com/aallan/vera/issues/242)):
  `array_push(array, elem)` is now a fully implemented builtin — registered in the
  type environment with a generic `(Array<T>, T) -> Array<T>` signature and compiled
  to WASM with proper allocation, element copying, and GC shadow stack integration.
  The `ch04_array_ops` conformance test now exercises `array_push`.

### Changed
- Conformance suite: `ch01_byte_literals` promoted from `check` to `run` level;
  `ch04_array_ops` now includes `array_push` in its feature coverage
- Documentation updated across TESTING.md, SKILL.md, and README.md to reflect
  resolved bugs and new builtin

## [0.0.68] - 2026-03-05

### Added
- **Close #223: Conformance test suite** ([#223](https://github.com/aallan/vera/issues/223)):
  39 small, self-contained programs in `tests/conformance/` that systematically
  validate every language feature against the spec (Chapters 1-7). Each program
  tests one feature or a small group of related features.
- `tests/conformance/manifest.json` — machine-readable metadata mapping each
  program to its spec chapter, test level (parse/check/verify/run), and feature tags
- `tests/test_conformance.py` — parametrized pytest runner generating ~195 test
  cases across all 39 conformance programs
- `scripts/check_conformance.py` — standalone validation script for CI and
  pre-commit (same pattern as `check_examples.py`)
- Pre-commit hook `conformance-suite` and CI step in lint job
- Conformance suite documentation across TESTING.md, README.md, CLAUDE.md,
  AGENTS.md, SKILL.md, and vera/README.md
- Known Bugs section in README.md listing compiler issues discovered during
  conformance suite development

### Fixed
- Opened [#241](https://github.com/aallan/vera/issues/241) (Byte literal coercion),
  [#242](https://github.com/aallan/vera/issues/242) (array_push codegen), and
  [#243](https://github.com/aallan/vera/issues/243) (nested generic constructor
  type inference) — bugs discovered while building the conformance suite

## [0.0.67] - 2026-03-05

### Added
- **Close #216: String escape sequences** ([#216](https://github.com/aallan/vera/issues/216)):
  Fix grammar regex and add escape sequence decoder in `transform.py`.
  All 7 escape sequences from spec section 1 are now supported: `\\`, `\"`, `\n`, `\t`,
  `\r`, `\0`, `\u{XXXX}`. Invalid escapes produce error code E009.
- 19 new tests (14 AST + 5 codegen end-to-end) for escape sequence handling

### Fixed
- `STRING_LIT` grammar regex had too many backslashes, causing the lexer to
  reject single-backslash escape sequences like `\n` and `\t`

## [0.0.66] - 2026-03-05

### Added
- **Close #135: IO operations** (C8.5, [#135](https://github.com/aallan/vera/issues/135)):
  Six new IO operations: `read_line`, `read_file`, `write_file`, `args`,
  `exit`, and `get_env`. All seven IO operations (including `print`) are
  now registered as built-in effect operations with full type checking.
  Programs no longer need `effect IO { op print(String -> Unit); }` preambles.
- Host function implementations for all IO operations via wasmtime, with
  WASM-to-host string passing through exported `$alloc`
- `ExecuteResult.exit_code` field for `IO.exit` support
- `execute()` accepts `stdin`, `cli_args`, and `env_vars` parameters
- Two new example programs: `io_operations.vera` and `file_io.vera`
- 26 new tests across type checker, codegen, and CLI

### Changed
- IO effect is now a built-in with all 7 operations registered in the
  type environment (no user `effect IO` declaration required)
- Replaced `_needs_io_print: bool` with `_io_ops_used: set[str]` for
  per-operation WASM import tracking
- WASM modules export `$alloc` when IO operations need host-to-WASM
  string allocation
- `_is_void_expr` now recursively handles compound expressions
  (MatchExpr, IfExpr, Block) to prevent invalid `drop` instructions
- Fixed match dispatch for ADT constructors with String fields
  (`i32_pair` type in `_sub_pattern_wasm_type` and size/align dicts)

## [0.0.65] - 2026-03-04

### Added
- **Close #51: garbage collection for WASM linear memory** (C8e, [#51](https://github.com/aallan/vera/issues/51)):
  Conservative mark-sweep garbage collector implemented entirely in WASM.
  Shadow stack root tracking, free-list reuse, and automatic `memory.grow`
  ensure allocation-heavy programs survive beyond the initial 64 KiB page.
  New `gc_pressure.vera` example demonstrates GC under repeated allocation.

### Changed
- Memory layout now reserves 8192 bytes after string constants for GC
  shadow stack (4096 bytes) and mark worklist (4096 bytes)
- `$alloc` prepends a 4-byte header to every allocation (mark bit + size)
  and checks the free list before bump-allocating
- Functions that allocate heap data receive GC prologue/epilogue
  (save/restore `$gc_sp`, push pointer parameters and return values)
- `to_string` and `strip` now allocate exact-size result buffers instead
  of returning interior pointers into temporary buffers
- Removed "No garbage collection" from limitation tables in spec, README,
  and compiler architecture docs

## [0.0.64] - 2026-03-04

### Added
- **Close #106: universal to-string conversion** (C8e, [#106](https://github.com/aallan/vera/issues/106)):
  Added 5 new string conversion builtins for all primitive types:
  `bool_to_string(Bool -> String)`, `nat_to_string(Nat -> String)`,
  `byte_to_string(Byte -> String)`, `float_to_string(Float64 -> String)`,
  and `int_to_string(Int -> String)` (alias for existing `to_string`).
  ADT/compound type Show deferred to abilities (#60).

### Changed
- Moved #56 (incremental compilation) from C8e to C8.5 in the roadmap

## [0.0.63] - 2026-03-04

### Changed
- **Close #52: dynamic string construction** (C8e, [#52](https://github.com/aallan/vera/issues/52)):
  All 8 string built-in operations (`string_concat`, `to_string`, `string_slice`,
  `strip`, `parse_nat`, `parse_float64`, `char_code`, `string_length`) were
  implemented in WASM codegen across v0.0.50 (PR #173) and v0.0.60 (#174),
  providing full dynamic string construction via the bump allocator. This
  documentation-only release updates limitation tables across the spec, README,
  and compiler README to reflect the resolved status.
  - `spec/11-compilation.md` limitation table: struck through #52 row
  - `spec/12-runtime.md` limitation table: struck through #52 row; also fixed
    stale #53 and #110 rows to match `spec/11-compilation.md`
  - `README.md` roadmap: struck through #52 with version tag
  - `vera/README.md` limitations table: marked #52 as done
  - `spec/09-standard-library.md`: updated Markdown section dependency note
  - GC for string memory remains tracked separately in [#51](https://github.com/aallan/vera/issues/51)
  - Unblocks [#106](https://github.com/aallan/vera/issues/106) (Show/Display)

## [0.0.62] - 2026-03-04

### Added
- **Exn\<E\> exception handler compilation** (C8e, [#53](https://github.com/aallan/vera/issues/53)):
  `handle[Exn<E>]` expressions now compile to WASM using the exception handling
  proposal (`try_table`/`catch`/`throw`). Enables compile-and-run for programs
  using exception-style error handling.
  - Exception tags declared per `Exn<E>` type parameter
  - `throw(value)` compiles to WASM `throw` instruction
  - Cross-function throws work via WASM stack unwinding
  - Nested `handle[Exn<E>]` expressions with unique labels
  - `examples/effect_handler.vera` extended with safe division via `Exn<Int>`
  - 10 new tests, 1,380 tests total
- **Renamed `SKILLS.md` to `SKILL.md`**: matches the Claude Code skill file naming
  convention. All references updated across README, AGENTS.md, CLAUDE.md,
  docs site, and vera/README.md. CHANGELOG historic references preserved.
- **Added installation instructions to `SKILL.md`**: agents consuming the skill
  file now get setup instructions (clone, venv, pip install, verify)

## [0.0.61] - 2026-03-04

### Added
- **Arrays of compound types** (C8e, [#132](https://github.com/aallan/vera/issues/132)):
  Arrays now support all element types, not just the five primitives (`Int`,
  `Nat`, `Float64`, `Bool`, `Byte`).  This includes ADT types
  (`Array<Option<Int>>`, `Array<Result<Int, String>>`), `String`
  (`Array<String>`), and nested arrays (`Array<Array<Int>>`).
  - ADT elements are stored as i32 heap pointers (4 bytes each)
  - String and nested-array elements are stored as (ptr, len) pairs (8 bytes each)
  - Chained indexing works for nested arrays (`@Array<Array<Int>>.0[0][1]`)
  - Constructor pair-type field storage fixed (e.g. `Err("msg")` with String field)
  - 17 new tests, 1,370 tests total

## [0.0.60] - 2026-03-03

### Changed
- **`parse_nat` returns `Result<Nat, String>`** (C8e, [#174](https://github.com/aallan/vera/issues/174)):
  `parse_nat` now returns `Ok(n)` on valid decimal input and `Err(msg)` on
  empty or invalid input, matching the spec (Section 9).  Previously it
  returned bare `Nat` and silently produced garbage for non-numeric strings.
  - Digit validation: bytes must be in ASCII 48–57; leading/trailing spaces
    are tolerated; empty/whitespace-only strings return `Err("empty string")`
  - Built-in Result and Option ADT layouts are now registered in codegen so
    match on `Ok`/`Err` works without a user `data Result` declaration
  - Match extraction supports String pair bindings inside ADT constructors
    (e.g. `Err(@String)`)
  - 6 new tests, 1,353 tests total

## [0.0.59] - 2026-03-03

### Fixed
- **Stale spec cross-reference** ([#141](https://github.com/aallan/vera/issues/141)):
  Updated `spec/09-standard-library.md` reference from "Section 11.16" to
  "Section 11.17" (section numbering shifted after chapter edits). Added the
  compound-type array limitation ([#132](https://github.com/aallan/vera/issues/132))
  to the limitations table in `spec/11-compilation.md`.

### Removed
- **Unused `hypothesis` dependency** ([#138](https://github.com/aallan/vera/issues/138)):
  Removed `hypothesis>=6.0` from `pyproject.toml` dev dependencies — it was
  declared but never imported in the test suite.

## [0.0.58] - 2026-03-03

### Fixed
- **`list_ops.vera` runtime failure — built-in name shadowing** (C8e, [#154](https://github.com/aallan/vera/issues/154)):
  User-defined functions now take priority over built-in intrinsics in WASM
  codegen. Previously, a user-defined `length(@List<Int> -> @Nat)` was
  incorrectly intercepted by the array-length built-in handler, producing
  invalid WASM. The fix guards all 9 built-in handlers (`length`,
  `string_length`, `string_concat`, `string_slice`, `char_code`, `parse_nat`,
  `parse_float64`, `to_string`, `strip`) so they only activate when no
  user-defined function with the same name exists.
  - `examples/list_ops.vera` now compiles and runs correctly
  - 3 new tests, 1,347 tests total

## [0.0.57] - 2026-03-03

### Added
- **Name collision detection for flat module compilation** (C8e, [#110](https://github.com/aallan/vera/issues/110)):
  When two imported modules define a function, data type, or constructor with
  the same name, the compiler now reports a clear error (E608/E609/E610) listing
  both conflicting modules. Previously, the first module registered silently won
  and the second was ignored, producing silently wrong code.
  - Provenance tracking in `_register_modules` detects collisions across functions,
    ADT types, and constructors
  - New error codes: E608 (function collision), E609 (ADT type collision),
    E610 (constructor collision)
  - Local definitions continue to shadow imported names without error
  - Same-module duplicates (module imported twice) are not treated as collisions
  - 7 new tests, 1,344 tests total

## [0.0.56] - 2026-03-03

### Added
- **Nested constructor pattern codegen** (C8e, [#131](https://github.com/aallan/vera/issues/131)):
  Match expressions with nested constructor patterns (e.g. `Cons(Some(@Int), _)`)
  now compile to WASM correctly. Previously, any sub-pattern that was a
  `ConstructorPattern` or `NullaryPattern` caused the entire function to be
  silently skipped.
  - `_collect_nested_tag_checks` recursively emits tag comparisons for nested
    constructors, AND-chained into the arm condition
  - `_extract_constructor_fields` recursively loads nested field pointers and
    binds their sub-patterns
  - `_sub_pattern_wasm_type` helper resolves WASM types for offset computation
  - `examples/pattern_matching.vera` `first_some` now compiles and runs
  - 5 new tests (nested Some, nested None, multi-field, different arms, fallthrough)
  - 1,337 tests total

## [0.0.55] - 2026-03-03

### Added
- **Bidirectional type checking** (C8d, [#55](https://github.com/aallan/vera/issues/55)):
  Adds local type inference via an `expected` parameter threaded through
  expression synthesis. Nullary constructors of parameterised ADTs (`None`
  for `Option<T>`, `Nil` for `List<T>`) now resolve their TypeVars from
  context — return types, let bindings, if/match branches, and function
  arguments.
  - `_synth_expr` gains optional `expected: Type | None` parameter
  - Constructors resolve unresolved TypeVars from expected type in
    `_ctor_result_type` and `_check_constructor_call`
  - Nested constructors (`Some(None)` for `Option<Option<Int>>`) resolve
    via field-type propagation
  - Function call arguments with TypeVars are re-synthesised with the
    substituted parameter type as expected
  - If/match branches with TypeVars are re-synthesised using the concrete
    branch as expected, replacing the previous `contains_typevar` guards
  - `_check_fn` passes `expected=return_type` to body synthesis, removing
    the `contains_typevar` workaround guard from v0.0.53
  - No changes to function signatures, parser, AST, or spec
  - 12 new tests (TestBidirectionalInference)
  - 1,332 tests total

## [0.0.54] - 2026-03-02

### Added
- **Effect row subtyping and call-site effect checking** (C8d, [#21](https://github.com/aallan/vera/issues/21)):
  Implements the subeffecting rules from Spec Section 7.8: a function with fewer
  effects can be used where more effects are expected.
  - `is_effect_subtype()` function in `types.py` encodes subset semantics
    for effect rows (`effects(pure) <: effects(<IO>) <: effects(<IO, State<Int>>)`)
  - `FunctionType` subtyping now includes effect covariance: a pure function
    can be passed where `fn(A -> B) effects(<IO>)` is expected
  - Call-site check in `checker/calls.py`: calling a function whose effects
    exceed the caller's context is now an error (E125)
  - Handler bodies unaffected: handlers temporarily add their effect to the
    context before checking the body, then discharge it
  - Effect row variables (`forall<E>`) are permissive pending #55
  - `effects_equal()` function added for structural effect row comparison
  - `types_equal()` updated to compare effects in `FunctionType`
  - 20 new tests (13 unit tests, 7 integration tests)
  - 1,320 tests total

## [0.0.53] - 2026-03-02

### Changed
- **TypeVar subtyping is no longer permissive** (C8d, [#20](https://github.com/aallan/vera/issues/20)):
  Removes the blanket `TypeVar <: anything` rule from `is_subtype`.
  TypeVars now only match themselves via reflexive equality.
  - Generic function bodies are properly checked: returning a `T` where a
    concrete `Int` is expected is now an error (E121)
  - Call sites unaffected: existing inference + substitution resolves TypeVars
    before subtype checks; unresolved TypeVars are skipped
  - Nullary constructors of parameterised ADTs (e.g. `None` for `Option<T>`)
    produce types with unresolved TypeVars — these are tolerated at call sites
    and in non-generic function bodies
  - `contains_typevar` utility added to `types.py`
  - 13 new tests (5 subtyping unit tests, 3 rejection tests, 5 regression tests)
  - 1,300 tests total

## [0.0.52] - 2026-03-02

### Added
- **Mutual recursion termination verification** (C8c, [#45](https://github.com/aallan/vera/issues/45)):
  Verifies `decreases` clauses across mutually recursive `where`-block function groups,
  promoting the last E525 contract in `mutual_recursion.vera` from Tier 3 to Tier 1.
  - Where-block functions now have their contracts verified (requires, ensures, decreases)
  - Cross-function measure checking: callee measure evaluated in callee parameter env
  - Verification rate: 96 T1, 3 T3, 99 total (97.0% static)
  - 4 new verifier tests, 1,287 tests total

## [0.0.51] - 2026-03-02

### Added
- **Expand SMT decidable fragment** (C4/C6, [#13](https://github.com/aallan/vera/issues/13)):
  Promotes 4 Tier 3 (runtime) contracts to Tier 1 (statically verified), bringing
  the verification rate from 91.7% to 95.8% across all 15 examples (92 T1, 4 T3, 96 total).
  - **Match expression + ADT constructor Z3 translation**: `MatchExpr`, `NullaryConstructor`,
    and `ConstructorCall` are now translated to Z3 using `z3.Datatype` sorts, with pattern
    conditions mapped to recognizers and field bindings mapped to accessors.
  - **Termination verification for `decreases` clauses**: Simple `Nat` decreases (factorial)
    and structural ADT decreases (`List<T>` length/sum) are now verified via Z3. Uses a
    rank function with universal axioms for structural subterm ordering.
  - ADT sort creation with type parameter substitution and self-reference handling
  - Per-sort `length()` uninterpreted functions (supports both Int and ADT domains)
  - Recursive call collector with Z3 path conditions and slot env tracking
  - Verifier now populates constructor info for SMT translation
  - 16 new verifier tests across 3 test classes
  - 1,283 tests total

### Remaining Tier 3 contracts (4)
- 2 x E520: Generic type parameters in `generics.vera` (unfixable — fundamental SMT limitation)
- 1 x E522: `old`/`new` state modeling in `increment.vera` (deferred — requires symbolic effect execution)
- 1 x E525: Mutual recursion in `mutual_recursion.vera` (deferred — requires cross-function measure reasoning)

## [0.0.50] - 2026-03-02

### Added
- **Eight string/conversion built-in operations** (C8e, [#134](https://github.com/aallan/vera/issues/134), [#52](https://github.com/aallan/vera/issues/52)):
  First external contribution by [@rlseaman](https://github.com/rlseaman) in PR [#173](https://github.com/aallan/vera/pull/173).
  - `string_length(@String -> @Nat)` — byte length of a string
  - `string_concat(@String, @String -> @String)` — concatenation
  - `string_slice(@String, @Nat, @Nat -> @String)` — substring extraction
  - `char_code(@String, @Int -> @Nat)` — ASCII code at index
  - `parse_nat(@String -> @Nat)` — decimal string to natural number
  - `parse_float64(@String -> @Float64)` — decimal string to float
  - `to_string(@Int -> @String)` — integer to decimal string
  - `strip(@String -> @String)` — trim leading/trailing whitespace (zero-copy)
  - New example: `examples/string_ops.vera` (15 examples total)
  - 52 new tests: 10 type checker + 42 codegen/runtime
  - Uses bump allocator (`$alloc`); GC deferred to [#51](https://github.com/aallan/vera/issues/51)
  - `parse_nat` returns bare `Nat` pending [#174](https://github.com/aallan/vera/issues/174) (spec requires `Result<Nat, String>`)
  - 1,267 tests total

## [0.0.49] - 2026-03-01

### Added
- **Register `Diverge` as built-in effect** (C8c, [#136](https://github.com/aallan/vera/issues/136)):
  `effects(<Diverge>)` now resolves to the spec-defined marker effect
  (Chapter 7, Section 7.7.3). Diverge has no operations — it signals that a
  function may not terminate. Precursor to #45 (termination verification).

## [0.0.48] - 2026-03-01

### Added
- **Improve WASM translation test coverage** (C8.5, [#156](https://github.com/aallan/vera/issues/156)):
  - New `tests/test_wasm_coverage.py` with 109 tests targeting coverage gaps in `vera/wasm/`
  - Direct unit tests for `helpers.py` pure functions (`wasm_type`, `wasm_type_or_none`, `is_compilable_type`, element helpers)
  - Full pipeline tests for `inference.py` deep branches (block result type inference, Vera type inference, expression type propagation)
  - Closure free-variable walking coverage (`closures.py`): capture in binary, if, call, let, match contexts
  - Operator edge cases: Float64 comparisons, Byte unsigned comparisons, Boolean implies, AND/OR
  - Data/match coverage: nullary constructors, wildcard patterns, Bool/Int patterns, Option<T>
  - Effect handler coverage: State<Int> init/get/put/increment patterns
  - `wasm/` coverage improved from 79% to 86% (helpers.py 62%→96%, closures.py 72%→92%, inference.py 71%→74%)
  - Overall compiler coverage improved from 87% to 88% (6,861 stmts, 819 missed)
  - 1,209 tests (up from 1,100)

### Fixed
- Fixed approximate (`~`) coverage values for `tester.py` in TESTING.md (335/51/85%, not ~350/~60/~83%)

## [0.0.47] - 2026-03-01

### Added
- **`vera test` contract-driven testing** (C8b, [#79](https://github.com/aallan/vera/issues/79)):
  - New `vera test` command generates inputs from `requires()` clauses via Z3 and executes compiled WASM to validate `ensures()` at runtime
  - Z3-based input generation for Int, Nat, Bool parameters with boundary value seeding
  - Tier classification: Tier 1 functions reported as "verified", Tier 3 functions exercised with generated inputs, unsupported/generic functions skipped
  - `--json` flag for machine-readable test results
  - `--trials N` flag to configure trial count per function (default 100)
  - `--fn name` flag to test a single function
  - New `vera/tester.py` module (~530 lines) with public `test()` API
  - E7xx error code range for testing diagnostics (E700-E702)
  - 24 new tests: 13 unit tests in `test_tester.py`, 11 CLI tests in `test_cli.py`
  - 1,100 tests (up from 1,076)

## [0.0.46] - 2026-03-01

### Changed
- **Decompose `codegen.py` into `codegen/` mixin package** (C8a, [#155](https://github.com/aallan/vera/issues/155)):
  - Split the 2,140-line `codegen.py` monolith into 11 focused modules following the mixin pattern from `checker/` and `wasm/`
  - New modules: `api.py`, `core.py`, `modules.py`, `registration.py`, `monomorphize.py`, `functions.py`, `closures.py`, `contracts.py`, `assembly.py`, `compilability.py`
  - Added 5 coverage gap tests reaching defensive error paths (E600, E601, E605, E606, unknown module calls)
  - Split the 4,834-line `test_codegen.py` into 6 focused test files mirroring the module structure
  - 1,076 tests (up from 1,071)
  - Completes C8a refactoring: all three compiler monoliths (`checker.py`, `wasm.py`, `codegen.py`) are now mixin packages

## [0.0.45] - 2026-02-28

### Added
- **`vera fmt` canonical code formatter** ([#75](https://github.com/aallan/vera/issues/75)):
  - New `vera fmt` command formats Vera source to the canonical form defined in Spec §1.8
  - `--write` flag for in-place formatting, `--check` flag for CI (exit 1 if non-canonical)
  - AST-based formatter with pre-pass comment extraction and reattachment
  - Precedence-aware parenthesization for binary expressions
  - All 10 formatting rules enforced: indentation, braces, commas, operators, semicolons, parentheses, contracts, one-per-line, no trailing whitespace, final newline
  - New `vera/formatter.py` module (1,018 lines)
  - 75 new tests (1,071 total, up from 996)
  - All 14 examples reformatted to canonical form
  - SKILLS.md and spec examples updated to canonical form ([#150](https://github.com/aallan/vera/issues/150))

## [0.0.44] - 2026-02-28

### Changed
- **Module-qualified call syntax uses `::` delimiter** (C8b, [#95](https://github.com/aallan/vera/issues/95)):
  - Module-qualified calls now use `::` between module path and function name: `vera.math::abs(42)`
  - Resolves LALR(1) grammar ambiguity where `module_path` greedily consumed the function name
  - Old dot syntax (`vera.math.abs(42)`) is rejected with a targeted "did you mean `::` ?" error (E008)
  - Added `format_expr` support for `ModuleCall` AST nodes
  - Updated spec chapters 8 and 10, examples, and all documentation
  - 12 new tests (996 total, up from 984)

## [0.0.43] - 2026-02-27

### Added
- **Stable error code taxonomy for diagnostics** (C8b, [#80](https://github.com/aallan/vera/issues/80)):
  - Every diagnostic now carries a stable error code (`E001`–`E607`)
  - Codes are grouped by compiler phase: parse (E0xx), type check (E1xx–E3xx), verification (E5xx), codegen (E6xx)
  - 80 error codes across 8 files, covering all 77+ diagnostic emission sites
  - `Diagnostic` dataclass gains `error_code: str` field
  - `format()` output shows `[Exxx]` prefix when code is present
  - `to_dict()` includes `error_code` in JSON output
  - Central `ERROR_CODES` registry in `vera/errors.py` maps codes to short descriptions
  - 13 new tests (984 total, up from 971)

## [0.0.42] - 2026-02-27

### Changed
- **Informative runtime contract violation messages** (C8b, [#112](https://github.com/aallan/vera/issues/112)):
  - Contract violations now report which function, contract kind, and expression failed
  - Before: `Runtime contract violation: error while executing at wasm backtrace: ... wasm trap: wasm unreachable instruction executed`
  - After: `Precondition violation in clamp(@Int, @Int, @Int -> @Int)\n  requires(@Int.1 <= @Int.2) failed`
  - New `vera.contract_fail` host import passes pre-interned message strings from WASM to the runtime before trapping
  - Added `format_expr()`, `format_type_expr()`, `format_fn_signature()` to `vera/ast.py` for AST-to-source reconstruction
  - 20 new tests (971 total, up from 951)

## [0.0.41] - 2026-02-27

### Changed
- **Decompose wasm.py into wasm/ package** (C8a, [#100](https://github.com/aallan/vera/issues/100)):
  - Split 2,344-line monolith into 8 focused modules using mixin-based composition
  - `context.py` (369) — composed WasmContext class, expression dispatcher, block translation
  - `helpers.py` (211) — WasmSlotEnv, StringPool, type mapping, array element helpers
  - `inference.py` (527) — type inference, slot/type utilities, operator lookup tables
  - `operators.py` (430) — binary/unary operators, if, quantifiers, assert/assume, old/new
  - `calls.py` (223) — function calls, generic resolution, effect handlers
  - `closures.py` (248) — closures, anonymous functions, free variable analysis
  - `data.py` (460) — constructors, match expressions, arrays, indexing
  - Zero test changes — public API (`WasmContext`, `WasmSlotEnv`, `StringPool`, `wasm_type`) unchanged

## [0.0.40] - 2026-02-27

### Changed
- **Decompose checker.py into checker/ package** (C8a, [#99](https://github.com/aallan/vera/issues/99)):
  - Split 2,043-line monolith into 8 focused modules using mixin-based composition
  - `core.py` (349) — TypeChecker class, orchestration, diagnostics, contracts
  - `resolution.py` (190) — AST TypeExpr → semantic Type, type inference
  - `modules.py` (153) — cross-module registration (C7b/C7c)
  - `registration.py` (138) — Pass 1 forward declarations
  - `expressions.py` (530) — expression synthesis, operators, statements
  - `calls.py` (390) — function, constructor, and module-qualified calls
  - `control.py` (439) — if/match, patterns, exhaustiveness, effect handlers
  - Zero test changes — public API (`typecheck()`) unchanged

## [0.0.39] - 2026-02-27

### Added
- **Spec Chapter 8: Modules** (C7f):
  - New specification chapter covering module declarations, imports, visibility, name resolution, module resolution algorithm, cross-module type checking, verification, and compilation
  - Formal semantics for the flattening compilation strategy, transitive resolution, circular import detection, and shadowing rules
  - Clarification that type aliases and effect declarations are module-local (not importable)
  - Complete worked example with `vera/math.vera`, `vera/collections.vera`, and `modules.vera`
  - Limitations section tracking #95 (LALR grammar), #110 (name collisions), and future extensions

### Changed
- **Roadmap restructured**: C7 collapsed as complete (v0.0.31-v0.0.39), C8 defined as the polish phase with sub-phases C8a-C8e grouping all open issues by area
- Cross-references added from spec Chapters 5, 10, 11, and 12 pointing to Chapter 8
- `SKILLS.md` module section updated with type-alias/effect locality note and spec reference
- `vera/README.md` limitations table updated: module system marked complete
- `docs/index.html` feature grid updated with "Module system" entry
- README project status: Chapter 8 status changed from "Not started" to "Draft"

## [0.0.38] - 2026-02-27

### Added
- **Multi-module codegen** (C7e — [#50](https://github.com/aallan/vera/issues/50)):
  - Imported function bodies are now compiled into the WASM module via flattening
  - `vera compile` and `vera run` work with multi-module programs (previously blocked by C7e guard rail)
  - Private helper functions called by imported public functions are compiled automatically
  - `ModuleCall` nodes are desugared to flat `FnCall` in WASM translation (including pipe operator)
  - Guard rail updated: only truly undefined functions produce errors; imported functions pass through
  - `modules.vera` example now compiles and runs end-to-end
  - Spec Chapter 11 updated with cross-module compilation section (11.16)
- 8 new cross-module codegen tests (951 total, up from 943)

### Changed
- Error messages for undefined functions no longer reference C7e; instead they report "not found in any imported module"

## [0.0.37] - 2026-02-27

### Added
- **Cross-module contract verification** (C7d — [#14](https://github.com/aallan/vera/issues/14)):
  - Imported function preconditions are now checked at call sites by the SMT solver
  - Imported function postconditions are assumed, allowing callers to rely on them
  - Chained imported calls compose correctly (e.g. `abs(max(x, y)) >= 0`)
  - Only `public` functions from imported modules are available for verification
  - Selective imports are respected — only named imports are registered
  - Refactored SMT call translation into shared `_translate_call_with_info` for both local and cross-module calls
  - Added `ModuleCall` handling in SMT translator (including pipe operator desugaring)
  - `modules.vera` example now verifies `abs_max` postcondition (`ensures(@Int.result >= 0)`) at Tier 1
- 8 new cross-module verification tests (943 total, up from 935)

## [0.0.36] - 2026-02-27

### Fixed
- **WASM export visibility gate** (C7c — [#107](https://github.com/aallan/vera/pull/107)):
  - Only `public` functions are now exported as WASM entry points; `private` functions compile but are not accessible via `vera run`
  - Both the `exports` list and the WAT-level `(export ...)` annotation are gated on visibility
  - Monomorphized generic functions inherit visibility from the original generic declaration
- **Improved "no exports" error** ([#107](https://github.com/aallan/vera/pull/107)):
  - `vera run` on a file with no public functions now lists all declared functions with their visibility, any compilation warnings, and suggests making a function public
  - `vera run --fn <name>` targeting a private function gives a specific "declared private" error with fix suggestion
  - Both plain-text and `--json` output modes supported
- **Runnable examples** ([#107](https://github.com/aallan/vera/pull/107)):
  - All 13 non-module examples now have `public` test entry points (e.g. `vera run examples/factorial.vera --fn test_factorial`)
  - Entry-point functions in examples, README, SKILLS.md, spec chapters 5-7, and docs site updated from `private` to `public`
- 3 new tests (935 total, up from 932)

### Added
- **Roadmap**: [#106](https://github.com/aallan/vera/issues/106) (universal to-string conversion / Show for all types) added to codegen gaps

## [0.0.35] - 2026-02-27

### Fixed
- **Cross-module codegen guard rail** (C7c — partial [#14](https://github.com/aallan/vera/issues/14)):
  - `vera compile` and `vera run` on programs with imported functions now produce a proper Vera diagnostic instead of a raw wasmtime error (`unknown func: failed to find name $max`)
  - Pre-compilation AST scan detects `FnCall` to undefined names and `ModuleCall` nodes before WAT generation, emitting LLM-oriented diagnostics with rationale, fix suggestion, and spec reference
  - Belt-and-braces guard in `wasm.py` `_translate_call()` and explicit `ModuleCall` handler prevent any undefined call from reaching wasmtime
  - Diagnostic directs users to `vera check` / `vera verify` for multi-module programs until C7e (multi-module codegen) is implemented
- **Bare `fn`/`data` in error messages and docs** (merged in [#103](https://github.com/aallan/vera/pull/103)):
  - Fixed remaining bare `fn` declarations in compiler error message fix suggestions (`vera/errors.py`), spec chapters, README, AGENTS.md, `vera/README.md`, and `tests/test_resolver.py`
- **`vera run` parameter mismatch diagnostic**: when a function expects arguments but none are provided, the error now names the function, lists available exports, and shows the correct `--fn ... -- <args>` syntax (previously showed a raw "Runtime contract violation: too few parameters" wasmtime error)
- 5 new tests (932 total, up from 927)

## [0.0.34] - 2026-02-27

### Added
- **Visibility enforcement** (C7c — partial [#14](https://github.com/aallan/vera/issues/14)):
  - Every top-level `fn` and `data` declaration now requires an explicit `public` or `private` annotation — no implicit default, enforcing design principle 3 ("one canonical form")
  - Cross-module access control: only `public` declarations are importable; private names produce targeted "is private" errors with fix suggestions
  - Selective imports of private names caught at import site with clear diagnostics
  - Wildcard imports (`import m;`) automatically filter to public declarations only
  - Constructor visibility derived from parent ADT — private ADT means private constructors
  - `FunctionInfo` and `AdtInfo` now carry a `visibility` field threaded through the registration pipeline
  - Updated all 14 examples, all test inline sources, spec chapters, README, SKILLS.md, and docs site — no bare `fn`/`data` declarations remain anywhere in the repo
- 13 new tests (927 total, up from 914)

## [0.0.33] - 2026-02-27

### Removed
- **`Float` type alias** (closes [#76](https://github.com/aallan/vera/issues/76)): `Float` is no longer accepted as a type name — use `Float64` exclusively
  - Enforces design principle 3 ("one canonical form") from spec §1.8
  - Removed `"Float": FLOAT64` alias from `vera/types.py` PRIMITIVES dict
  - Simplified ~12 dual-name checks in `wasm.py` and `codegen.py`
  - Updated `examples/pattern_matching.vera` to use `Float64`
  - Updated spec chapters 4 and 11 to remove `Float` references
  - Decomposition issues tracked: [#99](https://github.com/aallan/vera/issues/99) (checker.py), [#100](https://github.com/aallan/vera/issues/100) (wasm.py)
- 1 new test (914 total, up from 913)

## [0.0.32] - 2026-02-27

### Added
- **Cross-module type checking** (C7b — partial [#14](https://github.com/aallan/vera/issues/14)):
  - Imported function signatures are now registered and type-checked: arity checking, argument type checking, generic inference, and effect propagation all work across module boundaries
  - **Bare calls**: `import vera.math(abs); abs(-5)` resolves `abs` from the imported module — immediately usable from source files
  - **Module-qualified calls**: `ModuleCall` AST nodes type-checked against imported module declarations (grammar limitation [#95](https://github.com/aallan/vera/issues/95) prevents parsing `path.fn(args)` from source)
  - Selective import enforcement: `import m(f)` restricts available names to `f` only; calls to unimported names produce errors with fix suggestions
  - Wildcard imports: `import m;` makes all module declarations available
  - Local declarations shadow imported names (standard rule)
  - Imported ADT constructors available via bare calls: `import col(List); Cons(1, Nil)` works
  - Module declarations registered in isolated `TypeChecker` instances to avoid namespace pollution
  - `examples/modules.vera` now exercises bare cross-module calls (`abs`, `max` from `vera.math`)
- LALR grammar limitation for module-qualified call syntax tracked as [#95](https://github.com/aallan/vera/issues/95)
- **Project website** ([veralang.dev](https://veralang.dev)): single-page site deployed via GitHub Pages ([#81](https://github.com/aallan/vera/pull/81))
- 13 new tests (913 total, up from 900)

## [0.0.31] - 2026-02-26

### Added
- **Module resolution** (C7a — partial [#14](https://github.com/aallan/vera/issues/14), [#50](https://github.com/aallan/vera/issues/50)): `import` paths now resolve to source files on disk
  - New `vera/resolver.py`: `ModuleResolver` maps import paths (e.g., `vera.math`) to `.vera` files relative to the importing file or project root
  - `ResolvedModule` dataclass: path tuple, file path, parsed Program AST, source text
  - Parse cache: each imported module parsed at most once per compilation session
  - Circular import detection via in-progress tracking set
  - Resolver wired into all CLI commands (`check`, `verify`, `compile`, `run`)
  - `typecheck()` accepts optional `resolved_modules` parameter; improved diagnostic messages distinguish "module resolved but type merging not yet implemented (C7b)" from "module not found"
  - `verify()` accepts `resolved_modules` for forward-compatibility with C7d
  - Stub modules `examples/vera/math.vera` and `examples/vera/collections.vera` for the `modules.vera` example
- README restructured: C6/C6.5 collapsed sections moved above "What's next"; new "Longer term" section with all 19 open issues linked by category
- 20 new tests (900 total, up from 880)

## [0.0.30] - 2026-02-26

### Added
- **old()/new() state expressions in postconditions** (C6.5f — closes [#70](https://github.com/aallan/vera/issues/70)): postconditions containing `old(State<T>)` and `new(State<T>)` now compile to WASM runtime checks
  - `old(State<T>)` snapshots the state value at function entry into a temp local
  - `new(State<T>)` reads the current state value at postcondition check time via `state_get`
  - `_snapshot_old_state()` in codegen.py walks ensures clauses to detect `OldExpr` nodes and emits snapshot instructions
  - `WasmContext._translate_old_expr()` and `_translate_new_expr()` handle the AST→WAT translation
  - Snapshot is only emitted when ensures clauses actually reference `old()` (trivial contracts skip it)
  - Completes the C6.5 codegen cleanup phase
- README restructured: C7 (Module System) is now the "What's next" section with sub-phase plan; C6.5 and C6 are collapsed
- 6 new codegen tests (880 total, up from 874)

## [0.0.29] - 2026-02-26

### Added
- **String and Array types in function signatures** (C6.5e — closes [#69](https://github.com/aallan/vera/issues/69)): functions with `String` or `Array<T>` parameters and return types now compile to WASM
  - Each String/Array parameter expands to two consecutive `i32` WASM parameters (pointer and length)
  - String/Array return types use WASM multi-value return `(result i32 i32)`
  - `_type_expr_to_wasm_type()` returns `"i32_pair"` sentinel instead of `"unsupported"` for String/Array
  - Generalised `_is_pair_type_name()` helper for String and Array<T> across slot refs, let bindings, and drop logic
  - `execute()` handles multi-value (list) returns from wasmtime
  - Postcondition checks skipped for pair return types (single-local save/restore pattern incompatible with two-value results)
  - `if` and `match` blocks emit `(result i32 i32)` for pair-typed branches
  - Functions previously skipped in `examples/pattern_matching.vera` and `examples/quantifiers.vera` now compile
- 8 new codegen tests (874 total, up from 866)

## [0.0.28] - 2026-02-26

### Added
- **Float64 modulo compilation** (C6.5d — closes [#46](https://github.com/aallan/vera/issues/46)): `%` on Float64 operands now compiles to WASM via the decomposition `a % b = a - trunc(a / b) * b`
  - Uses `f64.trunc` (truncation toward zero), matching C `fmod` semantics and consistent with `i64.rem_s` for integer modulo
  - Multi-instruction WAT sequence with temporary locals (same pattern as array indexing, closures)
  - WASM has no native `f64.rem` instruction; this was previously unsupported (function silently skipped)
- 4 new codegen tests: exact division, remainder, negative operand, parameterized (866 total, up from 862)

## [0.0.27] - 2026-02-26

### Added
- **Pipe operator compilation** (C6.5c — closes [#44](https://github.com/aallan/vera/issues/44)): `a |> f(x, y)` now compiles to WASM and verifies via Z3, desugaring to `f(a, x, y)` in both backends
  - WASM codegen: intercept `BinOp.PIPE` in `_translate_binary()`, construct synthetic `FnCall`, delegate to `_translate_call()`
  - SMT verifier: same desugaring pattern in `_translate_binary()`
  - No grammar, AST, transformer, or checker changes needed (pipe already parsed and type-checked)
- 4 new tests: 3 codegen, 1 verifier (862 total, up from 858)

## [0.0.26] - 2026-02-26

### Added
- **Handler `with` clause** (C6.5b — closes [#72](https://github.com/aallan/vera/issues/72)): handler operation clauses can now update handler state via `with @T = expr` after the clause body
  - Grammar: `with_clause` rule added to `handler_clause`
  - AST: `state_update` field on `HandlerClause`
  - Type checker: validates state update type matches handler state declaration
  - No codegen changes (handler clauses remain specifications per spec 11.11.2)
- 6 new tests: 2 parser, 4 checker (858 total, up from 852)

## [0.0.25] - 2026-02-26

### Fixed
- **`resume` recognized in handler scope** (C6.5a — closes [#74](https://github.com/aallan/vera/issues/74)): the type checker now binds `resume` as a function in handler clause bodies with the correct type (takes operation return type, returns Unit), eliminating spurious "Unresolved function 'resume'" warnings
- `effect_handler.vera` example now type-checks cleanly (moved from warn to clean examples)

### Added
- `_check_clean()` test helper asserts zero errors AND zero warnings
- 3 new tests: `test_resume_wrong_arg_type`, `test_resume_wrong_arity`, `test_resume_outside_handler` (852 total, up from 849)

## [0.0.24] - 2026-02-26

### Added
- **Spec Chapter 9: Standard Library** (C6n): documents all built-in types (`Option<T>`, `Result<T, E>`), collections (`Array<T>`), effects (`IO`, `State<T>`), and functions (`length`, future `similarity`); includes future features (Http, Async, Inference effects; Json, Decimal types; Set, Map collections; Abilities) with issue cross-references
- **Spec Chapter 12: Runtime and Execution** (C6n — closes [#63](https://github.com/aallan/vera/issues/63)): documents WASM module structure, wasmtime host runtime, host function bindings (IO.print, State\<T\>), linear memory model, bump allocator, execution flow, argument passing, error handling, and runtime limitations

### Changed
- **Spec Chapter 0**: condensed Section 0.8 design notes to a cross-reference table pointing to Chapter 9 sections (previously contained full feature designs inline)

## [0.0.23] - 2026-02-26

### Added
- **Refinement type alias compilation** (C6m): type aliases like `PosInt`, `Percentage`, `Nat` that resolve through refinement types now compile to their base WASM type
  - `_type_expr_to_wasm_type()` in codegen.py now recurses on any alias type (not just FnType)
  - `_resolve_base_type_name()` helper in wasm.py follows alias chains through refinement types to the underlying primitive (e.g. `PosInt` → `Int` → `i64`)
  - Applied uniformly to parameter types, return types, let bindings, and slot references
- **Spec Section 11.15**: new "Refinement Type Alias Compilation" section
- **Codegen tests**: 8 new tests — safe_divide, to_percentage (clamp low/pass/high), refined let bindings, refined return in expr, WAT exports (849 total, up from 841)

## [0.0.22] - 2026-02-26

### Added
- **Quantifier compilation** (C6l): compile `forall`/`exists` as runtime loops with short-circuit evaluation
  - Counted loop over `[0, domain)` with predicate inlined (no closure overhead)
  - `forall` returns true if all iterations satisfy predicate, short-circuits on first false
  - `exists` returns true if any iteration satisfies predicate, short-circuits on first true
  - Empty domain: `forall` → true (vacuously), `exists` → false
- **Assert compilation** (C6l): `assert(expr)` compiles to conditional `unreachable` trap
- **Assume compilation** (C6l): `assume(expr)` compiles to no-op at runtime (verifier-only construct)
- **Spec Sections 11.13-11.14**: new "Quantifier Compilation" and "Assert and Assume Compilation" sections
- **Codegen tests**: 20 new tests — assert/assume, forall, exists, WAT inspection (841 total, up from 821)

## [0.0.21] - 2026-02-26

### Added
- **Byte type compilation** (C6k): `Byte` maps to `i32` in WASM with unsigned comparison operators (`i32.lt_u`, `i32.gt_u`, `i32.le_u`, `i32.ge_u`); `i32.wrap_i64` coercion for Byte-returning functions with integer literal bodies
- **Array compilation** (C6k — closes [#30](https://github.com/aallan/vera/issues/30)): compile `Array<T>` literals, indexing, and `length()` to WASM via linear memory
  - Array representation: `(ptr: i32, len: i32)` pairs, allocated via bump allocator
  - Element types: `Byte` (1 byte, `i32.load8_u`/`i32.store8`), `Bool` (4 bytes), `Int`/`Nat` (8 bytes, `i64`), `Float64` (8 bytes, `f64`)
  - Bounds checking: `i32.ge_u` unsigned comparison + `unreachable` trap on out-of-bounds
  - `length()` built-in: extracts len from `(ptr, len)` pair, extends to `i64`
  - Array let bindings: two WASM locals (ptr at N, len at N+1)
  - Array slot refs: emit two `local.get` ops for `(ptr, len)` pair
  - Array function params/returns unsupported (skipped with warning, same as String)
- **Spec Section 11.12**: new "Array Compilation" section covering representation, allocation, indexing, bounds checking, length, let bindings, and scope
- **Codegen tests**: 26 new tests — Byte identity/zero/max/let/comparisons, array literals/indexing/bounds-check/length, WAT inspection (821 total, up from 795)

## [0.0.20] - 2026-02-25

### Fixed
- **Spec @T notation mismatch**: fixed 30 code blocks across 5 spec files where `@T` was used in data constructor fields and effect operation signatures (value-level `@` is for binding sites only); 16 blocks now parse, 14 recategorized as fragments for unrelated syntax reasons (empty effects, handler `with` clauses, inline function types)
- **Stale README limitation rows**: removed "No closure codegen" and "No effect handler codegen" rows (closed in v0.0.18 and v0.0.19 respectively)
- **Spec limitation issue tracking**: created GitHub issues [#50](https://github.com/aallan/vera/issues/50)–[#53](https://github.com/aallan/vera/issues/53) for all unlinked limitations in spec Chapter 11; updated spec and README tables

### Added
- **Test coverage**: 104 new tests across 4 modules (795 total, up from 691)
  - `tests/test_types.py` (new): 55 tests for `is_subtype`, `types_equal`, `substitute`, `pretty_type`, `canonical_type_name`, `base_type`
  - `tests/test_wasm.py` (new): 22 tests for `StringPool`, `WasmSlotEnv`, and translation edge cases via full compilation pipeline
  - `tests/test_errors.py`: 18 new tests for `SourceLocation`, `Diagnostic.to_dict`, `diagnose_lark_error`, `unclosed_block`, `unexpected_token`, `VeraError`
  - `tests/test_cli.py`: 10 new tests for compile/run/verify error paths in both text and JSON modes

### Changed
- **Spec allowlist**: removed all 30 MISMATCH entries from `check_spec_examples.py`; added 14 FRAGMENT entries for genuine syntax fragments; parsed blocks increased from 21 to 37

## [0.0.19] - 2026-02-25

### Added
- **Effect handler compilation** (C6j — closes [#28](https://github.com/aallan/vera/issues/28)): compile `handle[State<T>]` expressions to WASM via host imports
  - State handler translation: `handle[State<T>](@T = init) { get/put clauses } in { body }` compiles by initializing state via `state_put_T`, then compiling body with get/put mapped to host imports
  - Handler clauses serve as specifications (not compiled) — `resume()` calls describe the default State semantics, validated by type checker
  - Effect discharge: pure functions containing `handle[State<T>]` are compilable — state imports registered by scanning function body for handle expressions
  - Unsupported handlers (`Exn<E>`, custom effects) cause function to be skipped with warning
- **Reworked `examples/effect_handler.vera`**: removed `safe_parse` (uses String + undefined `parse_int`), added `test_state_init` and `test_put_get` (simple compilable tests)
- **Codegen tests**: 14 new tests — state initialization, put/get, increment pattern, run_counter, let bindings, Bool state, WAT inspection, unsupported handler skip, example file round-trips (691 total, up from 677)

## [0.0.18] - 2026-02-25

### Added
- **Closure compilation** (C6h — closes [#27](https://github.com/aallan/vera/issues/27)): compile anonymous functions and closures to WASM via function tables and `call_indirect`
  - Closure representation: heap-allocated struct `[func_table_idx: i32, capture_0, ...]` as `i32` pointer, using existing bump allocator
  - Function table infrastructure: `(type $closure_sig_N ...)`, `(table N funcref)`, `(elem ...)` for indirect calls
  - Closure lifting: anonymous functions compiled as module-level WASM functions with `$env` parameter for captured variables
  - Free variable capture: walk `AnonFn` body to detect `SlotRef` nodes referencing outer-scope bindings, store captured values in heap environment
  - `apply_fn` built-in: compiler-recognized function that emits `call_indirect` with closure's `func_table_idx`
  - Function type aliases (e.g. `type IntToInt = fn(Int -> Int) effects(pure)`) resolved to `i32` closure pointers
  - Functions with function-type parameters no longer skipped (recognized as compilable)
- **Reworked `examples/closures.vera`**: removed `Array<Int>`, undefined `map`, and `forall<T>` generic `map_option`; added `make_adder` (closure capture), `apply` (closure parameter), `map_option` (closure in match arm), `test_closure` and `test_map_option` (end-to-end round-trips)
- **Codegen tests**: 17 new tests — closure creation with/without capture, `apply_fn`, closures in let bindings and match arms, function-type parameters, WAT structure verification, example file round-trips (677 total, up from 660)

## [0.0.17] - 2026-02-24 ([#42](https://github.com/aallan/vera/pull/42))

### Added
- **Generics monomorphization** (C6i — closes [#29](https://github.com/aallan/vera/issues/29)): compile `forall<T>` functions to WASM via monomorphization
  - Collection pass: walk non-generic function bodies to find calls to generic functions, infer concrete type variable bindings
  - AST substitution: create monomorphized FnDecl copies with type variables replaced by concrete types (e.g. `@T.0` → `@Int.0`)
  - Name mangling: `identity` + `(Int,)` → `identity$Int`, `const` + `(Int, Bool)` → `const$Int_Bool`
  - Call rewriting: generic function calls resolve to mangled names at WASM translation time
  - FnCall type inference: infer WASM return types and Vera type names for function call expressions (improves if-branch and chained-call handling)
  - Supports: literal args, slot ref args, constructor args, chained generic calls, arithmetic expression args
- **Codegen tests**: 17 new tests — identity/const/is_some instantiation, two-instantiation exports, ADT match, chained calls, if-branches, let bindings, example files (660 total, up from 643)

## [0.0.16] - 2026-02-24 ([#41](https://github.com/aallan/vera/pull/41))

### Added
- **Match expression codegen** (C6g — closes [#26](https://github.com/aallan/vera/issues/26)): compile `MatchExpr` AST nodes to WASM chained if-else cascades
  - ADT tag dispatch: load tag from heap pointer, compare with constructor tag, branch
  - Field extraction: load constructor fields at computed offsets into locals, bind in environment
  - Monomorphized offsets: field offsets computed from concrete binding types (same approach as C6f constructor calls)
  - Pattern types: `ConstructorPattern`, `NullaryPattern`, `WildcardPattern`, `BindingPattern`, `BoolPattern`, `IntPattern`
  - Recursive if-else cascade: each arm generates a condition check and branches, last arm emits directly
  - Environment scoping: each arm gets fresh bindings from pattern extraction, no cross-arm leakage
- **Codegen tests**: 20 new tests — ADT tag dispatch, field extraction, wildcard catch-alls, Bool/Int literal patterns, binding patterns, composability (643 total, up from 623)

## [0.0.15] - 2026-02-24 ([#40](https://github.com/aallan/vera/pull/40))

### Added
- **ADT constructor codegen** (C6f): compile `ConstructorCall` and `NullaryConstructor` AST nodes to WASM heap-allocated tagged unions
  - Nullary constructors (e.g. `Red`, `None`): alloc → store tag → return pointer
  - Constructors with fields (e.g. `Some(42)`, `Wrap(@Int.0)`): alloc → store tag → store each field at computed offset → return pointer
  - Field offsets computed from concrete argument types at translation time — handles monomorphized generic constructors (e.g. `Some(T)` with `T=Int` stores i64)
  - ADT types compile to `i32` (heap pointer) in function signatures, slot references, and type inference
  - `WasmContext` accepts `ctor_layouts` and `adt_type_names` for constructor-aware translation
  - Functions using ADT constructors now compile (no longer skipped with warning)
- **Codegen tests**: 12 new tests — nullary/tagged constructors, Int/Bool fields, Option None/Some, WAT inspection, let bindings, if-then-else branches, ADT parameters (623 total, up from 611)

## [0.0.14] - 2026-02-24 ([#39](https://github.com/aallan/vera/pull/39))

### Added
- **Bump allocator infrastructure** (C6e): heap allocation support for upcoming ADT constructor codegen
  - `$heap_ptr` mutable global: initialized to first byte after string data, exported as `"heap_ptr"`
  - `$alloc` internal function: bump-allocates with 8-byte alignment, returns pointer to allocated block
  - ADT layout metadata: `ConstructorLayout` dataclass stores tag, field offsets, and total size per constructor
  - Layout computed eagerly during registration pass — available for C6f (constructor codegen) and C6g (match codegen)
  - Allocator and heap global emitted only when user-declared ADTs are present (no overhead for pure programs)
  - `StringPool.heap_offset` property exposes first free byte after string constants
- **Codegen tests**: 26 new tests — layout helpers, WAT output inspection, ADT metadata registration, conditional emission (611 total, up from 585)

## [0.0.13] - 2026-02-24 ([#38](https://github.com/aallan/vera/pull/38))

### Added
- **State\<T\> WASM host imports** (C6d): compile `get`/`put` operations for `State<T>` effects as WASM host imports
  - `State<Int>`, `State<Nat>`, `State<Bool>`, `State<Float64>` compile to typed host import pairs
  - `get(())` → `call $vera.state_get_{T}` (returns typed value); `put(x)` → `call $vera.state_put_{T}` (consumes typed value)
  - Host runtime maintains mutable state cells per type, initialized to zero
  - `execute()` accepts optional `initial_state` parameter and returns final `state` in `ExecuteResult`
  - Mixed effects supported: `effects(<State<Int>, IO>)` compiles correctly
  - `effect_ops` dict mechanism in `WasmContext` redirects bare `get`/`put` calls to host imports
  - `_is_void_expr` recognizes `put()` as void (no `drop` emitted in ExprStmt)
- **Codegen tests**: 15 new tests — get default, put-then-get, increment pattern, example file, Bool/Float64/Nat state, String rejection, mixed effects, WAT imports, multiple types, void semantics, initial state override, pure function purity (585 total, up from 570)
- `examples/increment.vera` now compiles and runs (7 of 14 examples compilable)

## [0.0.12] - 2026-02-24 ([#37](https://github.com/aallan/vera/pull/37))

### Added
- **Match exhaustiveness checking** (C6c — closes [#18](https://github.com/aallan/vera/issues/18)): compile-time verification that match expressions cover all possible values
  - ADT exhaustiveness: all constructors must be covered or a catch-all pattern must be present
  - Bool exhaustiveness: both `true` and `false` must be covered or a catch-all present
  - Infinite type exhaustiveness: `Int`, `String`, `Float64`, `Nat` matches require a wildcard `_` or binding pattern
  - Unreachable arm warnings: arms after a wildcard or binding catch-all produce warnings (Spec Section 4.9.3)
  - Refinement types properly stripped via `base_type()` before analysis
  - Error diagnostics include missing constructor/value names and fix suggestions
- **Type checker tests**: 17 new tests — ADT exhaustive/missing/wildcard/binding, Bool exhaustive/missing/wildcard, Int/String without wildcard, unreachable arms (single/multiple/after binding), wildcard only, refined type stripping (570 total, up from 553)

## [0.0.11] - 2026-02-24 ([#36](https://github.com/aallan/vera/pull/36))

### Added
- **Callee precondition verification** (C6b — closes [#19](https://github.com/aallan/vera/issues/19)): modular call-site contract checking
  - When function `f` calls function `g`, the verifier now checks that `g`'s `requires()` clauses hold at the call site given `f`'s assumptions
  - Callee postconditions (`ensures()`) are assumed at the call site, enabling symbolic reasoning about return values
  - Fresh Z3 variables created per call, with postconditions asserted — supports chained calls, let bindings, and recursive calls
  - Recursive functions (e.g., `factorial`) now verify `ensures()` at Tier 1 instead of falling to Tier 3
  - `CallViolation` dataclass in `smt.py` records call-site violations with callee name, precondition, and counterexample
  - `_report_call_violation()` in verifier produces LLM-oriented diagnostics with fix suggestions
  - `param_type_exprs` field added to `FunctionInfo` for callee parameter slot resolution
- **Verifier tests**: 13 new tests — satisfied/violated/forwarded preconditions, assumed postconditions, recursive calls, trivial preconditions, let bindings, where-block calls, generic call fallback, multiple preconditions, sequential calls, error message quality (553 total, up from 540)

### Changed
- Tier 3 warning rationale updated: "recursive calls" replaced with "generic calls" (recursive calls now handled via modular verification)
- `SmtContext` constructor accepts optional `fn_lookup` callback for callee contract resolution
- Caller precondition assumptions now asserted into the Z3 solver before body translation

## [0.0.10] - 2026-02-24 ([#35](https://github.com/aallan/vera/pull/35))

### Added
- **Float64 WASM codegen** (C6a — closes [#25](https://github.com/aallan/vera/issues/25)): compile Float64/Float values to WebAssembly `f64` instructions
  - Type mapping: Float64/Float → `f64` in `wasm_type()`, `_type_expr_to_wasm_type()`, `_slot_name_to_wasm_type()`, `_infer_expr_wasm_type()`, `_infer_block_result_type()`
  - `FloatLit` emission: `f64.const` literals
  - Float64 arithmetic: `f64.add`, `f64.sub`, `f64.mul`, `f64.div` (MOD unsupported — WASM has no `f64.rem`)
  - Float64 comparisons: `f64.eq`, `f64.ne`, `f64.lt`, `f64.gt`, `f64.le`, `f64.ge` (result is `i32`)
  - Float64 negation: `f64.neg`
  - Float64 slot references, let bindings, if/else branches, function parameters and returns all compile
  - `ExecuteResult.value` widened to `int | float | None`; `execute()` accepts `list[int | float]` args
- **Codegen tests**: 26 new tests — Float64 literals, slot references, arithmetic, comparisons, negation, if/else, let bindings, WAT output validation (540 total, up from 514)

### Changed
- `execute()` signature updated: `args` parameter accepts `list[int | float]` for Float64 arguments
- Warning messages updated to mention Float64 as a compilable type
- CLI `fn_args` type widened to `list[int | float]` for future float argument parsing

## [0.0.9] - 2026-02-23 ([#31](https://github.com/aallan/vera/pull/31))

### Added
- **WASM code generation** (`vera/codegen.py`, `vera/wasm.py`): compile verified Vera programs to WebAssembly and execute them via wasmtime — **first light** 🌅
  - Two-pass code generator: register functions (forward references, mutual recursion), then compile bodies
  - Expression compilation: integer/Boolean literals, arithmetic, comparisons, Boolean logic, if/else, let bindings, blocks, function calls, recursion, string literals, IO operations
  - `WasmSlotEnv` — maps De Bruijn slot references (`@T.n`) to WASM local indices (mirrors `SlotEnv` in `smt.py`)
  - `WasmContext` — manages local allocation, data section, imports, accumulates WAT instructions
  - `StringPool` — deduplicated string constants in the WASM data section
  - Type mapping: Int/Nat → i64, Bool → i32, Unit → void, String → (i32 ptr, i32 len) pair
  - IO effect as host imports: `IO.print` compiles to imported host function, host reads UTF-8 from linear memory
  - Where-block functions compiled as module-level WASM functions
  - Graceful degradation: functions with unsupported types/constructs are skipped with a warning
- **Runtime contract insertion**: Tier 3 (unverified) contracts compiled as runtime assertions
  - Preconditions checked at function entry, trap on violation via `unreachable`
  - Postconditions checked after body with result stored in temp local
  - Trivial contracts (`requires(true)`, `ensures(true)`) eliminated — no runtime overhead
  - Tier 1 (proven) contracts omitted — statically guaranteed
- **CLI commands**: `vera compile` and `vera run`
  - `vera compile <file>` — full pipeline, writes `.wasm` binary; `--wat` prints human-readable WAT; `--json` for diagnostics; `-o` for output path
  - `vera run <file>` — compile and execute; `--fn` to call specific function; `--` to pass arguments; `--json` for structured output
- **Spec Chapter 11** (`spec/11-compilation.md`): compilation model documentation — type mapping, expression compilation, string pool, IO host bindings, runtime contracts, CLI commands, limitations
- **Hello World example** (`examples/hello_world.vera`): IO effect with qualified `IO.print` call (14 examples total)
- **README code sample testing** (`scripts/check_readme_examples.py`, `tests/test_readme.py`): extracts Vera code blocks from README.md and verifies they parse; pre-commit hook added
- **Codegen tests**: 76 new tests — literals, arithmetic, comparisons, Boolean logic, control flow, let bindings, function calls, recursion, strings, IO, runtime contracts, CLI commands, subprocess integration (470 total, up from 372)

### Changed
- README: updated status table (WASM codegen: Working), advanced roadmap (C5 Done, What's next → C6), added `vera compile`/`vera run` docs, updated project structure with `wasm.py`, `codegen.py`, `spec/11-compilation.md`
- SKILLS.md: added `vera compile` and `vera run` to toolchain section, added Chapter 11 to spec reference table
- CLAUDE.md: added compile/run commands, updated pipeline, updated example/test counts
- AGENTS.md: added compile/run commands, updated pipeline, added `wasm.py` and `codegen.py` to module table, updated test counts
- vera/README.md: updated pipeline diagram (6 stages), added codegen/wasm to module map, updated line counts, added codegen section, updated test suite table, updated limitations

### Fixed
- Documentation consistency: all `print(...)` calls in README.md, spec/05-functions.md, spec/07-effects.md, and SKILLS.md corrected to use qualified `IO.print(...)` syntax (matching the language's "one canonical form" design principle)

## [0.0.8] - 2026-02-23 ([#10](https://github.com/aallan/vera/pull/10))

### Added
- **Contract verifier** (`vera/verifier.py`): Z3-backed verification of `requires`/`ensures` contracts on functions
  - Three-tier verification: Tier 1 (decidable, Z3 proves automatically), Tier 3 (runtime fallback with warning)
  - Forward symbolic execution — translates function body to Z3 expression, checks postconditions directly
  - Counterexample generation — when verification fails, shows concrete input values that break the contract
  - Trivial contract fast path — `requires(true)`/`ensures(true)` counted as verified without invoking Z3
  - Graceful Tier 3 fallback for unsupported constructs (match, effects, recursion, quantifiers)
  - LLM-oriented diagnostics with counterexample values, rationale, and spec references
- **SMT translation layer** (`vera/smt.py`): bridges Vera AST expressions to Z3 formulas
  - `SlotEnv` — De Bruijn slot stacks mapped to Z3 variables
  - Expression translation: integer/Boolean literals, arithmetic, comparisons, Boolean logic, if/else, let bindings, `length()` (uninterpreted function)
  - `SmtContext.check_valid()` — refutation-based validity checking with counterexample extraction
- **CLI command**: `vera verify <file>` — type-check and verify contracts, prints verification summary
- **Convenience API**: `verify_file(path)` in `vera/parser.py`
- **Verifier tests**: 51 new tests — round-trip verification of all 13 examples, trivial contracts, ensures verification, if/else bodies, let bindings, multiple contracts, counterexample extraction, tier classification, arithmetic, summary counts, edge cases (335 total, up from 284)

### Changed
- `FunctionInfo` in `vera/environment.py` now stores contract AST nodes (for modular verification)
- `_register_fn` in `vera/checker.py` passes contracts to `FunctionInfo`
- README: updated status table (Contract verifier: Working), added `vera verify` docs, updated project structure and test count, advanced roadmap (C4 Done, What's next → C5)
- SKILLS.md: added `vera verify` to toolchain section
- LICENSE converted to Markdown format

## [0.0.7] - 2026-02-23

### Added
- **Spec code block validator** (`scripts/check_spec_examples.py`) — extracts 154 code blocks from spec Markdown, classifies them as parseable/fragment/non-Vera, and verifies parseable blocks still parse with the current grammar. Categorised allowlist tracks 30 spec/parser mismatches (spec uses `@T` in data/effect declarations, parser expects bare `T`), 4 future-syntax design proposals, and 3 fragment overrides. Stale allowlist detection catches when spec edits shift line numbers.
- **Version sync check** (`scripts/check_version_sync.py`) — verifies `pyproject.toml` and `vera/__init__.py` agree on version number
- **Dependabot** (`.github/dependabot.yml`) — weekly automated PRs for pip and GitHub Actions dependency updates
- **CODEOWNERS** (`.github/CODEOWNERS`) — automatic review requests on PRs
- **CodeQL** (`.github/workflows/codeql.yml`) — security scanning on PRs and weekly schedule
- **macOS CI** — test matrix expanded from 3 jobs (ubuntu × 3 Python) to 6 jobs (ubuntu + macOS × 3 Python)
- **README narratives** — sub-headings and explanations for each code example in "What Vera Looks Like": Hello World (effects/contracts), absolute_value (postconditions/SMT verification), safe_divide (preconditions/compile-time guarantees), increment (algebraic effects/explicit state)

### Changed
- **CONTRIBUTING.md** — added pre-commit setup instructions, validation script documentation, branch protection rules
- **CI lint job** — now runs version sync check and spec code block validator alongside example validation

## [0.0.6] - 2026-02-23

### Added
- **Hello World example** in README — first example in "What Vera Looks Like" section, demonstrates IO effect and mandatory contracts
- **Spec design notes** in Chapter 0.8 (Section 0.8):
  - **Abilities**: Roc-style restricted type constraints — auto-derivable built-in set (`Eq`, `Ord`, `Hash`, `Encode`, `Decode`, `Show`), no higher-kinded types, `forall<T where Ability<T>>` syntax
  - **LLM Inference effect**: `<Inference>` as an algebraic effect for AI runtime calls — testable via mock handlers, explicit in type signatures, contracts still apply
  - **Standard library collections**: `Set<T>`, `Map<K, V>` (depend on abilities), `Decimal` (software implementation for WASM)

## [0.0.5] - 2026-02-23 ([#2](https://github.com/aallan/vera/pull/2))

### Added
- **Type checker**: Tier 1 decidable type checking — validates expression types, slot reference resolution, effect annotations, and contract well-formedness
  - Two-pass architecture: pass 1 registers all declarations (handles forward references and mutual recursion), pass 2 checks bodies
  - Expression type synthesis for all AST node types (literals, operators, calls, constructors, match/if, handlers, anonymous functions, quantifiers)
  - De Bruijn slot reference resolution with alias opacity
  - Function call type checking with generic type argument inference
  - ADT constructor validation and pattern type checking
  - Basic effect checking (pure functions can't call effectful operations)
  - Handler effect discharge (handlers eliminate their effect from the enclosing function's requirements)
  - Contract well-formedness (predicates must be Bool, `@T.result` only in ensures, `old`/`new` only in ensures)
  - Error accumulation — all type errors collected, never stops at first error
  - Unresolved name graceful handling (warning, not failure) with `UnknownType` propagation
  - LLM-oriented `TypeError` diagnostics with description, location, rationale, fix, and spec reference
- **Internal type representation** (`vera/types.py`): semantic `Type` objects separate from syntactic AST `TypeExpr` nodes — `PrimitiveType`, `AdtType`, `FunctionType`, `RefinedType`, `TypeVar`, `UnknownType`, effect row types
- **Type environment** (`vera/environment.py`): scope stack, slot resolution, built-in type/effect/function registrations (Option, Result, State with get/put, IO, length)
- **CLI command**: `vera typecheck <file>` as explicit alias for `vera check`
- **Convenience API**: `typecheck_file(path)` in `vera/parser.py`
- **Type checker tests**: 91 new tests — round-trip tests for all 13 examples, literal types, slot references, operators, function calls, generics, constructors, patterns, control flow, effects, contracts, higher-order functions, refinement types, error accumulation, where blocks, arrays, return types (284 total, up from 193)

### Changed
- `vera check` now runs the full pipeline: parse → AST → type check (previously parse only)
- README: updated status table (Type checker: Working), added type checker to project structure, documented `vera typecheck` alias
- SKILLS.md: added `vera typecheck` to toolchain section

## [0.0.4] - 2026-02-23 ([#1](https://github.com/aallan/vera/pull/1))

### Added
- **Typed AST layer**: frozen dataclass nodes with source spans, covering all grammar constructs (~50 node classes)
- **Lark→AST transformer**: bottom-up `Transformer` with ~86 methods converting parse trees to typed AST nodes
- **CLI command**: `vera ast <file>` prints indented text AST, `vera ast --json <file>` prints JSON
- **Convenience API**: `parse_to_ast(source, file)` in `vera/parser.py`
- **AST tests**: 83 new tests — round-trip tests for all 13 examples, node-specific tests for every construct, span tests, serialisation tests (193 total, up from 110)
- **TransformError**: new error class for AST transformation failures, subclass of `VeraError`

### Changed
- README: added AST to project status table, `vera ast` CLI docs, updated project structure
- SKILLS.md: added `vera ast` and `vera ast --json` to toolchain section

## [0.0.3] - 2026-02-23

### Added
- **Parser tests**: 40 new tests covering annotation comments, anonymous functions, generics, refinement types, tuple destructuring, quantifiers, assert/assume, qualified calls, function types, float literals, nested patterns, handler variations, and implies operator (110 total, up from 70)
- **Example programs**: 8 new examples — closures, generics, refinement types, effect handlers, modules, quantifiers, pattern matching, mutual recursion (13 total, up from 5)
- **Design notes**: network access as an effect (`<Http>`), JSON as a stdlib ADT, async promises/futures as an effect (`<Async>`) documented in spec Chapter 0

### Fixed
- Grammar: annotation comments (`/* ... */`) now correctly ignored by the parser
- Grammar: `vera/__init__.py` version was `0.1.0`, corrected to match pyproject.toml
- Spec Chapter 3: removed deliberation marker about `@Fn0` approach, kept settled type alias approach
- Spec Chapter 6: rewrote counterexample reporting section (removed incorrect example, added actionable fix suggestions)
- Spec Chapter 7: cleaned up effect-contract interaction section (removed problematic `get()` in contract example, kept settled `old()`/`new()` syntax)

## [0.0.2] - 2026-02-23

### Added
- **CI**: GitHub Actions workflow running pytest on Python 3.11/3.12/3.13 with coverage on 3.12
- **Social preview**: meerkat sentinel mascot using Negroni brand colour palette
- **Custom domain**: veralang.dev with GitHub Pages and HTTPS

### Changed
- CONTRIBUTING.md: point "Questions?" section at Issues instead of Discussions
- Issue template config: remove Discussions contact link (Discussions disabled)
- README: add social preview banner image linking to veralang.dev
- pyproject.toml: update Homepage/Documentation URLs to veralang.dev

## [0.0.1] - 2026-02-23

### Added
- **Parser**: Lark LALR(1) parser that validates `.vera` source files
  - `vera check <file>` — parse and report errors
  - `vera parse <file>` — print the parse tree
- **LLM-oriented diagnostics**: error messages are natural language instructions explaining what went wrong, why, how to fix it with a code example, and a spec reference
- **SKILLS.md**: complete language reference for LLM agents, following the agent skills format
- **Example programs**: `absolute_value.vera`, `safe_divide.vera`, `increment.vera`, `factorial.vera`, `list_ops.vera`
- **Test suite**: 70 tests (54 parser, 16 error diagnostics)
- **Language specification** chapters 0-7 and 10 (draft)
  - Chapter 0: Introduction, philosophy, and diagnostics-as-instructions
  - Chapter 1: Lexical structure
  - Chapter 2: Type system with refinement types
  - Chapter 3: Slot reference system (`@T.n` typed De Bruijn indices)
  - Chapter 4: Expressions and statements
  - Chapter 5: Function declarations
  - Chapter 6: Contract system (preconditions, postconditions, verification tiers)
  - Chapter 7: Algebraic effect system
  - Chapter 10: Formal EBNF grammar (LALR(1) compatible)
- Project structure with `spec/`, `vera/`, `runtime/`, `tests/`, `examples/`
- Python project configuration (`pyproject.toml`)
- Repository documentation (README, LICENSE, CONTRIBUTING, CODE_OF_CONDUCT, CHANGELOG)
- GitHub issue and pull request templates

### Fixed
- Grammar: operator precedence chain (pipe/implies ordering)
- Grammar: `old()`/`new()` accept parameterised types (`State<Int>`)
- Grammar: function signatures use `@Type` prefix to declare binding sites
- Grammar: handler body simplified to avoid LALR reduce/reduce conflict
- `pyproject.toml`: corrected build backend, package discovery, PEP 639 compliance

[Unreleased]: https://github.com/aallan/vera/compare/v0.0.172...HEAD
[0.0.172]: https://github.com/aallan/vera/compare/v0.0.171...v0.0.172
[0.0.171]: https://github.com/aallan/vera/compare/v0.0.170...v0.0.171
[0.0.170]: https://github.com/aallan/vera/compare/v0.0.169...v0.0.170
[0.0.169]: https://github.com/aallan/vera/compare/v0.0.168...v0.0.169
[0.0.168]: https://github.com/aallan/vera/compare/v0.0.167...v0.0.168
[0.0.167]: https://github.com/aallan/vera/compare/v0.0.166...v0.0.167
[0.0.166]: https://github.com/aallan/vera/compare/v0.0.165...v0.0.166
[0.0.165]: https://github.com/aallan/vera/compare/v0.0.164...v0.0.165
[0.0.164]: https://github.com/aallan/vera/compare/v0.0.163...v0.0.164
[0.0.163]: https://github.com/aallan/vera/compare/v0.0.162...v0.0.163
[0.0.162]: https://github.com/aallan/vera/compare/v0.0.161...v0.0.162
[0.0.161]: https://github.com/aallan/vera/compare/v0.0.160...v0.0.161
[0.0.160]: https://github.com/aallan/vera/compare/v0.0.159...v0.0.160
[0.0.159]: https://github.com/aallan/vera/compare/v0.0.158...v0.0.159
[0.0.158]: https://github.com/aallan/vera/compare/v0.0.157...v0.0.158
[0.0.157]: https://github.com/aallan/vera/compare/v0.0.156...v0.0.157
[0.0.156]: https://github.com/aallan/vera/compare/v0.0.155...v0.0.156
[0.0.155]: https://github.com/aallan/vera/compare/v0.0.154...v0.0.155
[0.0.154]: https://github.com/aallan/vera/compare/v0.0.153...v0.0.154
[0.0.153]: https://github.com/aallan/vera/compare/v0.0.152...v0.0.153
[0.0.152]: https://github.com/aallan/vera/compare/v0.0.151...v0.0.152
[0.0.151]: https://github.com/aallan/vera/compare/v0.0.150...v0.0.151
[0.0.150]: https://github.com/aallan/vera/compare/v0.0.149...v0.0.150
[0.0.149]: https://github.com/aallan/vera/compare/v0.0.148...v0.0.149
[0.0.148]: https://github.com/aallan/vera/compare/v0.0.147...v0.0.148
[0.0.147]: https://github.com/aallan/vera/compare/v0.0.146...v0.0.147
[0.0.146]: https://github.com/aallan/vera/compare/v0.0.145...v0.0.146
[0.0.145]: https://github.com/aallan/vera/compare/v0.0.144...v0.0.145
[0.0.144]: https://github.com/aallan/vera/compare/v0.0.143...v0.0.144
[0.0.143]: https://github.com/aallan/vera/compare/v0.0.142...v0.0.143
[0.0.142]: https://github.com/aallan/vera/compare/v0.0.141...v0.0.142
[0.0.141]: https://github.com/aallan/vera/compare/v0.0.140...v0.0.141
[0.0.140]: https://github.com/aallan/vera/compare/v0.0.139...v0.0.140
[0.0.139]: https://github.com/aallan/vera/compare/v0.0.138...v0.0.139
[0.0.138]: https://github.com/aallan/vera/compare/v0.0.137...v0.0.138
[0.0.137]: https://github.com/aallan/vera/compare/v0.0.136...v0.0.137
[0.0.136]: https://github.com/aallan/vera/compare/v0.0.135...v0.0.136
[0.0.135]: https://github.com/aallan/vera/compare/v0.0.134...v0.0.135
[0.0.134]: https://github.com/aallan/vera/compare/v0.0.133...v0.0.134
[0.0.133]: https://github.com/aallan/vera/compare/v0.0.132...v0.0.133
[0.0.132]: https://github.com/aallan/vera/compare/v0.0.131...v0.0.132
[0.0.131]: https://github.com/aallan/vera/compare/v0.0.130...v0.0.131
[0.0.130]: https://github.com/aallan/vera/compare/v0.0.129...v0.0.130
[0.0.129]: https://github.com/aallan/vera/compare/v0.0.128...v0.0.129
[0.0.128]: https://github.com/aallan/vera/compare/v0.0.127...v0.0.128
[0.0.127]: https://github.com/aallan/vera/compare/v0.0.126...v0.0.127
[0.0.126]: https://github.com/aallan/vera/compare/v0.0.125...v0.0.126
[0.0.125]: https://github.com/aallan/vera/compare/v0.0.124...v0.0.125
[0.0.124]: https://github.com/aallan/vera/compare/v0.0.123...v0.0.124
[0.0.123]: https://github.com/aallan/vera/compare/v0.0.122...v0.0.123
[0.0.122]: https://github.com/aallan/vera/compare/v0.0.121...v0.0.122
[0.0.121]: https://github.com/aallan/vera/compare/v0.0.120...v0.0.121
[0.0.120]: https://github.com/aallan/vera/compare/v0.0.119...v0.0.120
[0.0.119]: https://github.com/aallan/vera/compare/v0.0.118...v0.0.119
[0.0.118]: https://github.com/aallan/vera/compare/v0.0.117...v0.0.118
[0.0.117]: https://github.com/aallan/vera/compare/v0.0.116...v0.0.117
[0.0.116]: https://github.com/aallan/vera/compare/v0.0.115...v0.0.116
[0.0.115]: https://github.com/aallan/vera/compare/v0.0.114...v0.0.115
[0.0.114]: https://github.com/aallan/vera/compare/v0.0.113...v0.0.114
[0.0.113]: https://github.com/aallan/vera/compare/v0.0.112...v0.0.113
[0.0.112]: https://github.com/aallan/vera/compare/v0.0.111...v0.0.112
[0.0.111]: https://github.com/aallan/vera/compare/v0.0.110...v0.0.111
[0.0.110]: https://github.com/aallan/vera/compare/v0.0.109...v0.0.110
[0.0.109]: https://github.com/aallan/vera/compare/v0.0.108...v0.0.109
[0.0.108]: https://github.com/aallan/vera/compare/v0.0.107...v0.0.108
[0.0.107]: https://github.com/aallan/vera/compare/v0.0.106...v0.0.107
[0.0.106]: https://github.com/aallan/vera/compare/v0.0.105...v0.0.106
[0.0.105]: https://github.com/aallan/vera/compare/v0.0.104...v0.0.105
[0.0.104]: https://github.com/aallan/vera/compare/v0.0.103...v0.0.104
[0.0.103]: https://github.com/aallan/vera/compare/v0.0.102...v0.0.103
[0.0.102]: https://github.com/aallan/vera/compare/v0.0.101...v0.0.102
[0.0.101]: https://github.com/aallan/vera/compare/v0.0.100...v0.0.101
[0.0.100]: https://github.com/aallan/vera/compare/v0.0.99...v0.0.100
[0.0.99]: https://github.com/aallan/vera/compare/v0.0.98...v0.0.99
[0.0.98]: https://github.com/aallan/vera/compare/v0.0.97...v0.0.98
[0.0.97]: https://github.com/aallan/vera/compare/v0.0.96...v0.0.97
[0.0.96]: https://github.com/aallan/vera/compare/v0.0.95...v0.0.96
[0.0.95]: https://github.com/aallan/vera/compare/v0.0.94...v0.0.95
[0.0.94]: https://github.com/aallan/vera/compare/v0.0.93...v0.0.94
[0.0.93]: https://github.com/aallan/vera/compare/v0.0.92...v0.0.93
[0.0.92]: https://github.com/aallan/vera/compare/v0.0.91...v0.0.92
[0.0.91]: https://github.com/aallan/vera/compare/v0.0.90...v0.0.91
[0.0.90]: https://github.com/aallan/vera/compare/v0.0.89...v0.0.90
[0.0.89]: https://github.com/aallan/vera/compare/v0.0.88...v0.0.89
[0.0.88]: https://github.com/aallan/vera/compare/v0.0.87...v0.0.88
[0.0.87]: https://github.com/aallan/vera/compare/v0.0.86...v0.0.87
[0.0.86]: https://github.com/aallan/vera/compare/v0.0.85...v0.0.86
[0.0.85]: https://github.com/aallan/vera/compare/v0.0.84...v0.0.85
[0.0.84]: https://github.com/aallan/vera/compare/v0.0.83...v0.0.84
[0.0.83]: https://github.com/aallan/vera/compare/v0.0.82...v0.0.83
[0.0.82]: https://github.com/aallan/vera/compare/v0.0.81...v0.0.82
[0.0.81]: https://github.com/aallan/vera/compare/v0.0.80...v0.0.81
[0.0.80]: https://github.com/aallan/vera/compare/v0.0.79...v0.0.80
[0.0.79]: https://github.com/aallan/vera/compare/v0.0.78...v0.0.79
[0.0.78]: https://github.com/aallan/vera/compare/v0.0.77...v0.0.78
[0.0.77]: https://github.com/aallan/vera/compare/v0.0.76...v0.0.77
[0.0.76]: https://github.com/aallan/vera/compare/v0.0.75...v0.0.76
[0.0.75]: https://github.com/aallan/vera/compare/v0.0.74...v0.0.75
[0.0.74]: https://github.com/aallan/vera/compare/v0.0.73...v0.0.74
[0.0.73]: https://github.com/aallan/vera/compare/v0.0.72...v0.0.73
[0.0.72]: https://github.com/aallan/vera/compare/v0.0.71...v0.0.72
[0.0.71]: https://github.com/aallan/vera/compare/v0.0.70...v0.0.71
[0.0.70]: https://github.com/aallan/vera/compare/v0.0.69...v0.0.70
[0.0.69]: https://github.com/aallan/vera/compare/v0.0.68...v0.0.69
[0.0.68]: https://github.com/aallan/vera/compare/v0.0.67...v0.0.68
[0.0.67]: https://github.com/aallan/vera/compare/v0.0.66...v0.0.67
[0.0.66]: https://github.com/aallan/vera/compare/v0.0.65...v0.0.66
[0.0.65]: https://github.com/aallan/vera/compare/v0.0.64...v0.0.65
[0.0.64]: https://github.com/aallan/vera/compare/v0.0.63...v0.0.64
[0.0.63]: https://github.com/aallan/vera/compare/v0.0.62...v0.0.63
[0.0.62]: https://github.com/aallan/vera/compare/v0.0.61...v0.0.62
[0.0.61]: https://github.com/aallan/vera/compare/v0.0.60...v0.0.61
[0.0.60]: https://github.com/aallan/vera/compare/v0.0.59...v0.0.60
[0.0.59]: https://github.com/aallan/vera/compare/v0.0.58...v0.0.59
[0.0.58]: https://github.com/aallan/vera/compare/v0.0.57...v0.0.58
[0.0.57]: https://github.com/aallan/vera/compare/v0.0.56...v0.0.57
[0.0.56]: https://github.com/aallan/vera/compare/v0.0.55...v0.0.56
[0.0.55]: https://github.com/aallan/vera/compare/v0.0.54...v0.0.55
[0.0.54]: https://github.com/aallan/vera/compare/v0.0.53...v0.0.54
[0.0.53]: https://github.com/aallan/vera/compare/v0.0.52...v0.0.53
[0.0.52]: https://github.com/aallan/vera/compare/v0.0.51...v0.0.52
[0.0.51]: https://github.com/aallan/vera/compare/v0.0.50...v0.0.51
[0.0.50]: https://github.com/aallan/vera/compare/v0.0.49...v0.0.50
[0.0.49]: https://github.com/aallan/vera/compare/v0.0.48...v0.0.49
[0.0.48]: https://github.com/aallan/vera/compare/v0.0.47...v0.0.48
[0.0.47]: https://github.com/aallan/vera/compare/v0.0.46...v0.0.47
[0.0.46]: https://github.com/aallan/vera/compare/v0.0.45...v0.0.46
[0.0.45]: https://github.com/aallan/vera/compare/v0.0.44...v0.0.45
[0.0.44]: https://github.com/aallan/vera/compare/v0.0.43...v0.0.44
[0.0.43]: https://github.com/aallan/vera/compare/v0.0.42...v0.0.43
[0.0.42]: https://github.com/aallan/vera/compare/v0.0.41...v0.0.42
[0.0.41]: https://github.com/aallan/vera/compare/v0.0.40...v0.0.41
[0.0.40]: https://github.com/aallan/vera/compare/v0.0.39...v0.0.40
[0.0.39]: https://github.com/aallan/vera/compare/v0.0.38...v0.0.39
[0.0.38]: https://github.com/aallan/vera/compare/v0.0.37...v0.0.38
[0.0.37]: https://github.com/aallan/vera/compare/v0.0.36...v0.0.37
[0.0.36]: https://github.com/aallan/vera/compare/v0.0.35...v0.0.36
[0.0.35]: https://github.com/aallan/vera/compare/v0.0.34...v0.0.35
[0.0.34]: https://github.com/aallan/vera/compare/v0.0.33...v0.0.34
[0.0.33]: https://github.com/aallan/vera/compare/v0.0.32...v0.0.33
[0.0.32]: https://github.com/aallan/vera/compare/v0.0.31...v0.0.32
[0.0.31]: https://github.com/aallan/vera/compare/v0.0.30...v0.0.31
[0.0.30]: https://github.com/aallan/vera/compare/v0.0.29...v0.0.30
[0.0.29]: https://github.com/aallan/vera/compare/v0.0.28...v0.0.29
[0.0.28]: https://github.com/aallan/vera/compare/v0.0.27...v0.0.28
[0.0.27]: https://github.com/aallan/vera/compare/v0.0.26...v0.0.27
[0.0.26]: https://github.com/aallan/vera/compare/v0.0.25...v0.0.26
[0.0.25]: https://github.com/aallan/vera/compare/v0.0.24...v0.0.25
[0.0.24]: https://github.com/aallan/vera/compare/v0.0.23...v0.0.24
[0.0.23]: https://github.com/aallan/vera/compare/v0.0.22...v0.0.23
[0.0.22]: https://github.com/aallan/vera/compare/v0.0.21...v0.0.22
[0.0.21]: https://github.com/aallan/vera/compare/v0.0.20...v0.0.21
[0.0.20]: https://github.com/aallan/vera/compare/v0.0.19...v0.0.20
[0.0.19]: https://github.com/aallan/vera/compare/v0.0.18...v0.0.19
[0.0.18]: https://github.com/aallan/vera/compare/v0.0.17...v0.0.18
[0.0.17]: https://github.com/aallan/vera/compare/v0.0.16...v0.0.17
[0.0.16]: https://github.com/aallan/vera/compare/v0.0.15...v0.0.16
[0.0.15]: https://github.com/aallan/vera/compare/v0.0.14...v0.0.15
[0.0.14]: https://github.com/aallan/vera/compare/v0.0.13...v0.0.14
[0.0.13]: https://github.com/aallan/vera/compare/v0.0.12...v0.0.13
[0.0.12]: https://github.com/aallan/vera/compare/v0.0.11...v0.0.12
[0.0.11]: https://github.com/aallan/vera/compare/v0.0.10...v0.0.11
[0.0.10]: https://github.com/aallan/vera/compare/v0.0.9...v0.0.10
[0.0.9]: https://github.com/aallan/vera/compare/v0.0.8...v0.0.9
[0.0.8]: https://github.com/aallan/vera/compare/v0.0.7...v0.0.8
[0.0.7]: https://github.com/aallan/vera/compare/v0.0.6...v0.0.7
[0.0.6]: https://github.com/aallan/vera/compare/v0.0.5...v0.0.6
[0.0.5]: https://github.com/aallan/vera/compare/v0.0.4...v0.0.5
[0.0.4]: https://github.com/aallan/vera/compare/v0.0.3...v0.0.4
[0.0.3]: https://github.com/aallan/vera/compare/v0.0.2...v0.0.3
[0.0.2]: https://github.com/aallan/vera/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/aallan/vera/releases/tag/v0.0.1
