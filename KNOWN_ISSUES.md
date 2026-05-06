# Known issues

Bugs and limitations tracked against the [issue tracker](https://github.com/aallan/vera/issues). This file is a curated snapshot — the issue tracker is the source of truth.

## Bugs

| Bug | Issue |
|-----|-------|
| Tail-call optimization disabled for allocating functions — `return_call` would discard the GC epilogue and leak shadow-stack slots, so allocating functions fall back to plain `call`. Workaround: restructure to allocate outside the recursion, or iterate via `array_fold` / `array_map` (which compile to WASM loops). | [#549](https://github.com/aallan/vera/issues/549) |
| `url_parse` / `url_join` drops a leading colon — `url_parse(":foo")` returns `Ok` with empty scheme, then `url_join` emits just `foo` because its scheme-delimiter branch is gated on `s_len > 0`. Two viable fixes: reject `colon_pos == 0` in `url_parse` (RFC 3986-compliant, behaviour change) or add a `has_colon` flag bit to the round-trip word at offset 44 (preserves current `Ok`/`Err` shape). | [#568](https://github.com/aallan/vera/issues/568) |
| Conservative GC scan can spuriously retain heap objects via the host-handle field of a wrapper ADT (#573 latent). Phase 2b scans wrapper payloads word-by-word; the `handle` at offset 4 is a small i32 that stays below `gc_heap_start` (~147 KiB) for typical programs, so the heap-range check rejects it. Long-running programs (>100K host-store allocations in a single `execute()`) could see a handle exceed the threshold and (with the right alignment) be falsely classified as a heap pointer, retaining an unrelated heap object. Retention bug, not correctness — no use-after-free, no corruption. Issue body lists four candidate fix designs (self-describing wrappers, header skip-scan flag, wrap-table cross-reference, max-handle lower-bound check). | [#578](https://github.com/aallan/vera/issues/578) |

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
