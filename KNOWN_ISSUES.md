# Known issues

Bugs and limitations tracked against the [issue tracker](https://github.com/aallan/vera/issues). This file is a curated snapshot — the issue tracker is the source of truth.

## Bugs

| Bug | Issue |
|-----|-------|
| Opaque handle memory leak in host stores | [#346](https://github.com/aallan/vera/issues/346) |
| GC shadow stack pollution from opaque handle parameters | [#347](https://github.com/aallan/vera/issues/347) |
| GC worklist overflow for deeply nested object graphs | [#348](https://github.com/aallan/vera/issues/348) |
| WASM call translators: 10 pre-existing bugs (INT64_MIN to_string, string/array slice i64→i32 narrowing, char_code no bounds check, expression-bodied Exn handler result type, Map<K, Array<T>> lowering, url_parse/url_join round-trip, base64 `=` validation, parse_nat/int embedded spaces, float fractional carry) | [#475](https://github.com/aallan/vera/issues/475) |
| GC object header size field is 16-bit — allocations >65535 bytes corrupt memory (sweeper truncates size, links middle-of-payload as fake free blocks) | [#484](https://github.com/aallan/vera/issues/484) |

## Limitations

| Limitation | Issue |
|-----------|-------|
| Tier 2 verification (Z3-guided with `assert`/lemma hints) is specified in §6.3.2 but not yet implemented; contracts requiring hints fall to Tier 3 (runtime check) | [#427](https://github.com/aallan/vera/issues/427) |
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
