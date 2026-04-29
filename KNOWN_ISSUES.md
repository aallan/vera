# Known issues

Bugs and limitations tracked against the [issue tracker](https://github.com/aallan/vera/issues). This file is a curated snapshot — the issue tracker is the source of truth.

## Bugs

| Bug | Issue |
|-----|-------|
| Opaque handle memory leak in host stores | [#346](https://github.com/aallan/vera/issues/346) |
| GC shadow stack pollution from opaque handle parameters | [#347](https://github.com/aallan/vera/issues/347) |
| GC worklist overflow for deeply nested object graphs | [#348](https://github.com/aallan/vera/issues/348) |
| WASM call translators: 10 pre-existing bugs (INT64_MIN to_string, string/array slice i64→i32 narrowing, char_code no bounds check, expression-bodied Exn handler result type, Map<K, Array<T>> lowering, url_parse/url_join round-trip, base64 `=` validation, parse_nat/int embedded spaces, float fractional carry) | [#475](https://github.com/aallan/vera/issues/475) |
| GC `$alloc` grows memory by only 1 page — single allocations more than ~64 KB larger than free heap space trap (out-of-bounds memory access) | [#487](https://github.com/aallan/vera/issues/487) |
| `array_fold` heuristic over-roots host-managed opaque handles (Map, Set, Regex, Decimal) as if they were Vera heap pointers — safe (conservative GC rejects out-of-range values) but wastes work and can cause spurious mark retention | [#490](https://github.com/aallan/vera/issues/490) |
| Closures capturing **pair-typed** outer bindings (`String`, `Array<T>`) silently drop the len field — the closure compiles and runs but reads the captured value as empty. ADT and primitive captures work correctly. The historical [#514](https://github.com/aallan/vera/issues/514) "all heap captures broken" framing was inaccurate; v0.0.121 fixed nested closures and clarified that the residual is specifically pair types. Workaround: lift the closure body to a top-level `private fn` that takes the pair-typed value as an explicit parameter — the parameter path through `_compile_lifted_closure` handles pair types correctly; only the capture path is broken. | [#535](https://github.com/aallan/vera/issues/535) |
| Tail-call optimization disabled for allocating functions — v0.0.126 (#517) ships WASM `return_call` for tail-position calls in non-allocating functions; allocating functions revert `return_call` → `call` because `return_call` discards the GC epilogue and would leak shadow-stack slots. Workaround: restructure to allocate outside the recursion, or iterate via `array_fold` / `array_map` (which compile to WASM loops). Fix is emitting a GC-shadow-stack restore before each `return_call` in allocating functions | [#549](https://github.com/aallan/vera/issues/549) |

## Limitations

| Limitation | Issue |
|-----------|-------|
| Tier 2 verification (Z3-guided with `assert`/lemma hints) is specified in §6.3.2 but not yet implemented; contracts requiring hints fall to Tier 3 (runtime check) | [#427](https://github.com/aallan/vera/issues/427) |
| `@Nat` invariant check fires only at function return positions — narrowing from `@Int` into a `@Nat`-typed let binding or function argument is not obligation-checked, so a bad value can silently flow through subsequent expressions. Tier-3 fallback compiles correctly but the verifier doesn't catch it statically. Generalisation of #520 (which fixes the subtraction-specific subset) | [#552](https://github.com/aallan/vera/issues/552) |
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
