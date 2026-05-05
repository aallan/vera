# Known issues

Bugs and limitations tracked against the [issue tracker](https://github.com/aallan/vera/issues). This file is a curated snapshot — the issue tracker is the source of truth.

## Bugs

| Bug | Issue |
|-----|-------|
| Opaque host-store handles (`Map` / `Set` / `Decimal`) accumulate monotonically in Python-side stores for the lifetime of an `execute()` call — every `map_insert`/`set_add`/`decimal_*` op allocates a new handle without releasing transient predecessors. Bounded by Python GC at `execute()` exit, so single-shot programs are unaffected; matters for long-running execution contexts. An earlier draft of v0.0.132 attempted a `host_gc_sweep` design but it was reverted during development — v0.0.132 as released only ships the codegen-time `#347 + #490` fixes (the `_is_host_handle_type` classifier excluding handles from GC-rooting decision sites), not active reclamation.  The reverted design grew six interlocking pieces (heap walk + shadow-stack scan + transitive closure + re-entrancy guard + let-binding shadow_push + JSON/HTML emission gates) which was too complex relative to practical impact.  The recommended path forward is heap-wrap-as-ADT — make handle-creating ops return a Vera-heap-allocated `MapHandle(i32)` ADT that the existing mark-sweep GC can reclaim with a destructor callback, rather than running a parallel reclamation system. (Originally [#346](https://github.com/aallan/vera/issues/346), now superseded.) | [#573](https://github.com/aallan/vera/issues/573) |
| Tail-call optimization disabled for allocating functions — v0.0.126 (#517) ships WASM `return_call` for tail-position calls in non-allocating functions; allocating functions revert `return_call` → `call` because `return_call` discards the GC epilogue and would leak shadow-stack slots. Workaround: restructure to allocate outside the recursion, or iterate via `array_fold` / `array_map` (which compile to WASM loops). Fix is emitting a GC-shadow-stack restore before each `return_call` in allocating functions | [#549](https://github.com/aallan/vera/issues/549) |
| `url_parse` / `url_join` drops leading colon — `url_parse(":foo")` returns Ok with empty scheme; `url_join` then emits just `foo` because its scheme-delimiter branch is gated on `s_len > 0` and the offset-44 packed-flag word doesn't carry a `has_colon` bit. Pre-existing pre-#475; surfaced by CodeRabbit on PR #567 (v0.0.129) but out of scope for #475 PR 2's seven Major findings. Two viable fixes: reject `colon_pos == 0` in url_parse (RFC 3986-compliant; behaviour change) or add a `has_colon` flag bit at offset 44 (round-trip-only fix; preserves current Ok/Err shape) | [#568](https://github.com/aallan/vera/issues/568) |
| `array_map` (and likely sibling iterative builders `array_filter` / `array_mapi` / `array_flatten`) over a heap-allocating closure body trap on GC shadow-stack overflow at around 4000 elements. Each iteration's `gc_shadow_push` of the per-element heap pointer accumulates on the 16 KiB / 4096-entry shadow stack and isn't unwound between iterations; a 5000-element `array_map(array_range(0, 5000), fn(@Int -> @Box) effects(pure) { MkBox(@Int.0) })` traps. Surfaced while working on [#348](https://github.com/aallan/vera/issues/348). Cleanest fix is per-iteration shadow-stack unwind in the array_map codegen (or eliminating the per-element root by writing directly into the rooted destination array). Workaround: chunk inputs to ≤4000 or avoid heap-allocated element types in large arrays | [#570](https://github.com/aallan/vera/issues/570) |

## Limitations

| Limitation | Issue |
|-----------|-------|
| Tier 2 verification (Z3-guided with `assert`/lemma hints) is specified in §6.3.2 but not yet implemented; contracts requiring hints fall to Tier 3 (runtime check) | [#427](https://github.com/aallan/vera/issues/427) |
| `@Nat` invariant check fires only at function return positions and at subtraction sites (the latter via #520's verifier obligation + codegen guard in `vera/wasm/operators.py`) — narrowing from `@Int` into a `@Nat`-typed let binding or function argument is not obligation-checked statically and not guarded at runtime, so a bad value can silently flow through subsequent expressions. Generalisation of #520 (which fixes the subtraction-specific subset) | [#552](https://github.com/aallan/vera/issues/552) |
| Generic (`forall<T>`) functions bypass the E502 underflow obligation at verify time — the verifier's early return for generic functions skips `_walk_for_subtraction_obligations` along with all other static contract checks. The codegen guard fires per-monomorphization at compile time so the runtime safety net is in place; only the static check is missing. Consistent with how E520 / E521 / E523 / E524 / E525 all skip generics today; tracked alongside the broader Tier 2 verification work [#427](https://github.com/aallan/vera/issues/427) | [#555](https://github.com/aallan/vera/issues/555) |
| `vera test` cannot generate ADT (algebraic data type) inputs | [#440](https://github.com/aallan/vera/issues/440) |
| Effect row variable unification (full effect polymorphism) | [#294](https://github.com/aallan/vera/issues/294) |
| Incremental compilation | [#56](https://github.com/aallan/vera/issues/56) |
| Module re-exports | [#127](https://github.com/aallan/vera/issues/127) |
| Package system and registry | [#130](https://github.com/aallan/vera/issues/130) |
| LSP server | [#222](https://github.com/aallan/vera/issues/222) |
| REPL | [#224](https://github.com/aallan/vera/issues/224) |
| Date and time handling | [#233](https://github.com/aallan/vera/issues/233) |
| Cryptographic hashing | [#235](https://github.com/aallan/vera/issues/235) |
| CSV parsing and generation | [#236](https://github.com/aallan/vera/issues/236) |
| WASI 0.2 compliance | [#237](https://github.com/aallan/vera/issues/237) |
| Resource limits (fuel, memory, timeout) | [#239](https://github.com/aallan/vera/issues/239) |
| Http: no custom headers | [#351](https://github.com/aallan/vera/issues/351) |
| Http: no HTTP status code access | [#352](https://github.com/aallan/vera/issues/352) |
| Http: no request timeout control | [#353](https://github.com/aallan/vera/issues/353) |
| Http: browser uses deprecated synchronous XHR | [#355](https://github.com/aallan/vera/issues/355) |
| Http: no PUT, PATCH, DELETE methods | [#356](https://github.com/aallan/vera/issues/356) |
| Inference: `embed` operation (vector embeddings) | [#371](https://github.com/aallan/vera/issues/371) |
| Inference: no token/temperature controls (`max_tokens` hardcoded) | [#370](https://github.com/aallan/vera/issues/370) |
| Inference: no user-defined handlers (`handle[Inference]`) | [#372](https://github.com/aallan/vera/issues/372) |
| No float array host-alloc (`_alloc_result_ok_float_array`) | [#373](https://github.com/aallan/vera/issues/373) |

## Refactoring needed

Files that have grown beyond a comfortable size and need decomposition. None of these affect correctness — they are purely internal structural debt.

| File | Lines | Refactoring | Issue |
|------|-------|-------------|-------|
| `tests/test_codegen.py` | 10,019 | Split into feature-focused test files (literals, arithmetic, control flow, strings, arrays, collections, effects, data types) | [#419](https://github.com/aallan/vera/issues/419) |
| `tests/test_checker.py` | 5,522 | Split into phase-focused test files (types, functions, effects, contracts, modules, errors) | [#420](https://github.com/aallan/vera/issues/420) |
| `vera/codegen/api.py` | 2,228 | Extract memory layout utilities → `memory.py`; extract host runtime → `runtime.py` | [#421](https://github.com/aallan/vera/issues/421) |

## CI workarounds

Defensive measures currently applied in CI (CVE ignores, forced upgrades, etc.) with explicit removal triggers — bridges, not permanent exceptions.

| Workaround | Where | Rationale | Remove when | Issue |
|------------|-------|-----------|-------------|-------|
| `--ignore-vuln CVE-2026-4539` ([CVE-2026-4539](https://nvd.nist.gov/vuln/detail/CVE-2026-4539)) | `dependency-audit` step in `.github/workflows/ci.yml` | pygments 2.19.2 (transitive via pytest/rich); no fix release exists yet. | pygments > 2.19.2 ships with the fix. | — |
| `pip install --upgrade pip` before audit | Same step | `actions/setup-python@v6` ships pip 26.0.1, which is flagged for [CVE-2026-3219](https://nvd.nist.gov/vuln/detail/CVE-2026-3219) (fixed in pip 26.1, [pypa/pip#13870](https://github.com/pypa/pip/pull/13870)). The runner doesn't track PyPI live, so `pip-audit` scans the runner's bundled pip and fails until we explicitly upgrade. | `actions/setup-python@v6` ships a runner image with pip ≥ 26.1 natively. Drop the `--upgrade pip` from the install step then. | [#537](https://github.com/aallan/vera/issues/537) |
