# Known issues

Bugs and limitations tracked against the [issue tracker](https://github.com/aallan/vera/issues). This file is a curated snapshot — the issue tracker is the source of truth, and priority/sequencing live in [ROADMAP.md](ROADMAP.md). Every row follows the same shape: one sentence on what the issue is, one sentence on impact and the path forward.

## Bugs

Defects in shipped compiler, runtime, or tooling behaviour — this table matches the issue tracker's open [`bug`-labelled issues](https://github.com/aallan/vera/issues?q=is%3Aissue%20state%3Aopen%20label%3Abug) one-to-one. Verification-soundness gaps carry the `limitation` label instead and are tracked under [Limitations](#limitations).

| Bug | Issue |
|-----|-------|
| `scripts/fix_allowlists.py --fix` uses a bulk-shift heuristic that misses entries when a doc file receives multiple edits at different positions in one session. A content-fingerprint anchor would be robust; the #538 fence-annotation migration would retire the script entirely. | [#606](https://github.com/aallan/vera/issues/606) |
| The Markdown ADT builders (`writeMdInline` / `writeMdBlock` and the CLI `vera/wasm/markdown.py` mirror) lack the `gcGuard` / shadow-stack rooting the JSON / HTML walkers got in #692, so under `VERA_EAGER_GC=1` or heap pressure an intermediate `MdNode` pointer can be swept mid-build and corrupt the tree. The #692 fix's missed sibling, surfaced by the PR #743 review; the fix mirrors the `writeJson` / `writeHtml` rooting on both runtimes with eager-GC regression tests. | [#744](https://github.com/aallan/vera/issues/744) |
| The type checker types `Int <op> Nat` as `Nat` — a non-negative literal is `Nat`, and the binary-arithmetic rule promotes to `Nat` when either operand is — so `@Int.0 - 2` / `@Int.0 * 2` type as `Nat` and drive spurious `@Nat` narrowing inferences (`async(@Int.0 * 2)` infers `Future<Nat>`, firing an E503 the author never asked for). Masked for verified code by #520's underflow check; the fix types `Int <op> Nat` as `Int` unless both operands carry `Nat` provenance. | [#755](https://github.com/aallan/vera/issues/755) |

## Limitations

Things Vera cannot do yet, as distinct from defects in what it claims to do.

| Limitation | Issue |
|-----------|-------|
| Tier 2 verification (Z3 guided by `assert`/lemma hints) is specified in §6.3.2 but not implemented, so contracts that need hints fall to Tier 3 runtime checks. Per-monomorphization verification (#732) is the nearer-term depth work; full Tier 2 stays on the Milestone 4 horizon. | [#427](https://github.com/aallan/vera/issues/427) |
| `data invariant(...)` clauses (spec §2.6, §6.2.3) are not implemented — every documented form fails with E130 because the slot environment for the invariant predicate isn't wired up. Refinement types (`{ @T \| predicate }`, §2.6) are the working alternative until this lands. | [#686](https://github.com/aallan/vera/issues/686) |
| **Statically**, every narrowing *binding site* is obligated: a provably-negative value is an E503 error, and an untranslatable narrowing at an unguarded site is an E504 warning — so a `vera verify`-clean program stores no negative `@Nat` at these sites. **At runtime** (an unverified `vera compile`/`run`), the guard covers every concrete binding site, generic function-formal calls, and the string/markup builtin `@Nat` parameters (`string_repeat`, `string_pad_start`/`_end`, `string_from_char_code`, `md_has_heading`), but three statically-obligated sites stay unguarded and store a negative silently: the effect-operation argument (codegen's `_effect_ops` carries only the dispatch target), the generic-instantiated constructor field (constructor layouts carry no per-field `@Nat` mono metadata), and the `nat_to_int`/`nat_to_string` conversion builtins (special-cased before the `_fn_nat_params` guard loop) — a tripped guard there surfaces a generic `unreachable` rather than the `requires(... >= 0)` fix. (The static obligation itself does not yet reach a function return position or a `@Nat` component built in value position — #758.) | [#754](https://github.com/aallan/vera/issues/754), [#757](https://github.com/aallan/vera/issues/757), [#758](https://github.com/aallan/vera/issues/758) |
| Generic (`forall<T>`) functions skip most static verification (the E502 underflow obligation, `ensures` clauses) at verify time, because the verifier's early return for generics can't represent type variables in Z3.  A concrete refined *return* IS now discharged statically (#746 — its obligation is type-parameter-independent), but the rest of a generic body's obligations still fall to Tier 3.  Per-monomorphization static verification (#732) closes the remaining static half. | [#555](https://github.com/aallan/vera/issues/555) |
| Calls in statement position (value discarded) are never precondition-checked — E501 fires only for calls in value position. Roadmap Tier 0; until then a discarded call's `requires(...)` is enforced only by the runtime contract check. | [#730](https://github.com/aallan/vera/issues/730) |
| `vera test` cannot generate inputs for functions with ADT parameters, so those functions are skipped with a warning. Constructor synthesis with recursive field generation is the planned fix (Milestone 1). | [#440](https://github.com/aallan/vera/issues/440) |
| Effect row variables cannot be unified, so higher-order functions polymorphic over their effect rows are not expressible. Full effect polymorphism is Milestone 4 work. | [#294](https://github.com/aallan/vera/issues/294) |
| Every `vera` invocation re-parses and re-checks the whole module graph from scratch. Incremental compilation is Milestone 4 work; the LSP server's warm `VerificationSession` already covers the editor loop. | [#56](https://github.com/aallan/vera/issues/56) |
| A module cannot re-export an imported symbol, so deep module trees force consumers to import from the defining file. Sequenced behind module-qualified call disambiguation (#187) in Milestone 4. | [#127](https://github.com/aallan/vera/issues/127) |
| There is no package system or registry — all code shares one module tree resolved from the filesystem. Milestone 4 work; the issue carries the design discussion. | [#130](https://github.com/aallan/vera/issues/130) |
| There is no interactive read-eval-print loop; the shortest feedback path is `vera run` on a file. Milestone 3 developer-experience work. | [#224](https://github.com/aallan/vera/issues/224) |
| The language server resolves module imports from disk rather than open editor buffers, so unsaved changes in imported files aren't seen. Buffer-aware resolution is roadmap Tier 3. | [#724](https://github.com/aallan/vera/issues/724) |
| `vera lsp` will not run on Python 3.16+: its `pygls` dependency calls `asyncio.iscoroutinefunction`, removed in 3.16. Out of Vera's hands until pygls migrates to `inspect.iscoroutinefunction`; tracked so the `[lsp]` extra's support window is explicit (the rest of the toolchain is unaffected). | [#753](https://github.com/aallan/vera/issues/753) |
| LSP slot go-to-definition covers parameters only — `let` and `match` bindings aren't navigable, and there is no mechanical slot-index rewriting on signature change. Roadmap Tier 3. | [#181](https://github.com/aallan/vera/issues/181) |
| `vera/addEffect` propagates the new effect to all transitive callers even when a caller discharges it with `handle[E]`. Handler-aware propagation bounding is roadmap Tier 3. | [#725](https://github.com/aallan/vera/issues/725) |
| There is no date or time handling beyond `IO.time` — no ISO 8601 parsing, formatting, or arithmetic. Milestone 2 server-adjacent work. | [#233](https://github.com/aallan/vera/issues/233) |
| There are no cryptographic primitives — no hashing, no HMAC. Milestone 2 work, needed for API-authentication patterns like webhook signatures. | [#235](https://github.com/aallan/vera/issues/235) |
| There is no CSV parsing or generation. Milestone 2 server-adjacent work; JSON is the workaround interchange format today. | [#236](https://github.com/aallan/vera/issues/236) |
| The wasmtime integration predates WASI 0.2 — filesystem, networking, and clock access don't follow the component interfaces. Compliance is the prerequisite for the Milestone 2 server-effect chain. | [#237](https://github.com/aallan/vera/issues/237) |
| WASM execution has no configurable fuel, memory, or timeout limits, so pathological computation runs unbounded. Milestone 2 work, essential for server workloads on untrusted input. | [#239](https://github.com/aallan/vera/issues/239) |
| `Http.get`/`Http.post` send fixed headers — callers cannot add custom ones such as `Authorization`. Milestone 2 Http-hardening work. | [#351](https://github.com/aallan/vera/issues/351) |
| Http responses surface only the body — status codes are not accessible, so callers cannot distinguish a 404 from a 500. Milestone 2 Http-hardening work. | [#352](https://github.com/aallan/vera/issues/352) |
| Http requests have no per-request timeout control. Milestone 2 Http-hardening work; today a hung server hangs the program. | [#353](https://github.com/aallan/vera/issues/353) |
| The browser runtime implements Http via deprecated synchronous XMLHttpRequest, which browsers throttle. Milestone 2 Http-hardening work, currently blocked (see the issue's relationships). | [#355](https://github.com/aallan/vera/issues/355) |
| Http supports GET and POST only — no PUT, PATCH, or DELETE. Milestone 2 Http-hardening work. | [#356](https://github.com/aallan/vera/issues/356) |
| `Inference.complete` hardcodes `max_tokens` and `temperature`. Configurability is Milestone 2's first Inference-hardening item — agent workloads need both for cost gates and deterministic replays. | [#370](https://github.com/aallan/vera/issues/370) |
| `Inference.embed` (vector embeddings) is not implemented. Blocked on the float-array host-alloc infrastructure (#373). | [#371](https://github.com/aallan/vera/issues/371) |
| The Inference effect cannot be handled in user code — `handle[Inference]` is rejected. Full handler support enables mocking, caching, and routing strategies (Milestone 2). | [#372](https://github.com/aallan/vera/issues/372) |
| Host imports cannot return `Array<Float64>` — the `alloc_result_ok_float_array` infrastructure doesn't exist. Required by `Inference.embed` (#371). | [#373](https://github.com/aallan/vera/issues/373) |
| `runtime.mjs` doesn't export its string-marshalling helpers, so JavaScript cannot pass `String` arguments into Vera functions in the browser. This forces browser programs into the compute-upfront/drain-stdout pattern; exporting the helpers is roadmap Tier 3. | [#603](https://github.com/aallan/vera/issues/603) |
| `IO.sleep` busy-waits the browser's main thread, freezing the tab for the sleep duration — animations and paced simulations don't run meaningfully under `--target browser`. The JSPI-based suspend/resume fix is roadmap Tier 3, demoted below correctness work. | [#609](https://github.com/aallan/vera/issues/609) |
| ANSI escape sequences render as literal control characters in the browser DOM, so terminal-style programs display garbage under `--target browser`. A minimal ANSI-subset interpreter in `runtime.mjs` is roadmap Tier 3. | [#610](https://github.com/aallan/vera/issues/610) |

## Refactoring needed

Files that have grown beyond a comfortable size and need decomposition. None of these affect correctness — they are purely internal structural debt.

| File | Lines | Refactoring | Issue |
|------|-------|-------------|-------|
| `tests/test_codegen.py` | 19,570 | Split into feature-focused test files (literals, arithmetic, control flow, strings, arrays, collections, effects, data types). The file has nearly doubled since the issue was filed; roadmap Tier 3. | [#419](https://github.com/aallan/vera/issues/419) |
| `tests/test_checker.py` | 5,939 | Split into phase-focused test files (types, functions, effects, contracts, modules, errors). Currently a not-doing-now item — a close-or-annotate decision is pending. | [#420](https://github.com/aallan/vera/issues/420) |
| `vera/codegen/api.py` | 4,253 | Extract the wasmtime execution layer into a `vera/runtime/` package, one host-binding family per PR. The characterization harness (#734) and the GC bucket-as-truth migration (#706) land first; the file has doubled since the issue was filed. | [#421](https://github.com/aallan/vera/issues/421) |

## Test coverage gaps

Internal test-quality items that don't affect correctness today but would make the suite more durable to refactoring.

| Gap | Issue |
|-----|-------|
| Five of the six UTF-8 decode sites are pinned only by structural source-greps — a refactor that centralises the decodes would break the greps even with preserved behaviour. End-to-end tests per site (parametrizing the existing `host_print` test over an import-name/signature/payload tuple) would survive it. | [#592](https://github.com/aallan/vera/issues/592) |
| Text-mode `open()`/`read_text()`/`write_text()` calls without explicit `encoding='utf-8'` remain at roughly 30 sites, relying on CI's `PYTHONUTF8=1` backstop. The durable fix is explicit encoding everywhere plus a pre-commit check, after which the CI variable can be dropped. | [#645](https://github.com/aallan/vera/issues/645) |

## CI workarounds

Defensive measures currently applied in CI (CVE ignores, forced upgrades, etc.) with explicit removal triggers — bridges, not permanent exceptions.

| Workaround | Where | Rationale | Remove when | Issue |
|------------|-------|-----------|-------------|-------|
| `--ignore-vuln CVE-2026-4539` ([CVE-2026-4539](https://nvd.nist.gov/vuln/detail/CVE-2026-4539)) | `dependency-audit` step in `.github/workflows/ci.yml` | pygments 2.19.2 (transitive via pytest/rich) is flagged for this CVE with no fixed release available yet. The ignore is scoped to this single CVE. | pygments ships a release with the fix. | — |
| `pip install --upgrade pip` before audit | Same step | `actions/setup-python@v6` bundles pip 26.0.1, flagged for [CVE-2026-3219](https://nvd.nist.gov/vuln/detail/CVE-2026-3219) (fixed in pip 26.1), and `pip-audit` scans the runner's bundled pip. Upgrading first keeps the audit green without ignoring the CVE. | `actions/setup-python@v6` ships a runner image with pip ≥ 26.1 natively. | [#537](https://github.com/aallan/vera/issues/537) |
| `codecov/codecov-action` SHA-pinned to a commit (`e79a696` = v6.0.1) instead of the floating `@v6` tag | Both Codecov upload steps in `.github/workflows/ci.yml` | Codecov was acquired by Harness (June 2026), elevating the risk that the floating tag is repointed and silently flows into CI; pinning to a reviewed commit closes that. Coverage enforcement is unaffected — the 80% gate is the on-runner `--cov-fail-under`, and uploads are `fail_ci_if_error: false`. | The Codecov → Harness migration stabilises — then re-evaluate, including whether to adopt a repo-wide SHA-pin policy. | [#712](https://github.com/aallan/vera/issues/712) |

## Runtime workarounds

Defensive measures applied in compiler / runtime code that exist to bridge an upstream-fixed-but-unreleased bug — same shape as the CI workarounds table, but the workaround sits in shipped code rather than CI config.

No runtime workarounds currently in place.
