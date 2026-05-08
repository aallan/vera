# Known issues

Bugs and limitations tracked against the [issue tracker](https://github.com/aallan/vera/issues). This file is a curated snapshot — the issue tracker is the source of truth.

## Bugs

| Bug | Issue |
|-----|-------|
| Tail-call optimization disabled for allocating functions — `return_call` would discard the GC epilogue and leak shadow-stack slots, so allocating functions fall back to plain `call`. Workaround: restructure to allocate outside the recursion, or iterate via `array_fold` / `array_map` (which compile to WASM loops). | [#549](https://github.com/aallan/vera/issues/549) |
| Conservative GC scan can spuriously retain heap objects via the host-handle field of a wrapper ADT (#573 latent). Phase 2b scans wrapper payloads word-by-word; the `handle` at offset 4 is a small i32 that stays below `gc_heap_start` (~147 KiB) for typical programs, so the heap-range check rejects it. Long-running programs (>100K host-store allocations in a single `execute()`) could see a handle exceed the threshold and (with the right alignment) be falsely classified as a heap pointer, retaining an unrelated heap object. Retention bug, not correctness — no use-after-free, no corruption. Issue body lists four candidate fix designs (self-describing wrappers, header skip-scan flag, wrap-table cross-reference, max-handle lower-bound check). | [#578](https://github.com/aallan/vera/issues/578) |
| macOS malloc abort during wasmtime cleanup after Ctrl-C arrives in a host import (observed with `IO.sleep`).  The Python-side `KeyboardInterrupt` traceback half is fixed in v0.0.137 (host_sleep converts to `_VeraExit(130)` for clean exit), but a follow-on `pointer being freed was not allocated` / `Abort trap: 6` from the wasmtime/ctypes teardown path can still fire if the program was in certain heap states.  Filed upstream against wasmtime-py as [bytecodealliance/wasmtime-py#336](https://github.com/bytecodealliance/wasmtime-py/issues/336) — root cause is `wasmtime/_func.py` catching `Exception` rather than `BaseException` in the trampoline, letting `KeyboardInterrupt` escape into Rust with an undefined ABI return value.  Independent of #593 (which turned out to be a closure-return shadow-push asymmetry, not a Ctrl-C / cleanup issue).  No data-integrity impact; only the cleanup path. | [#595](https://github.com/aallan/vera/issues/595) |
| `Inference.complete` / `Http.get` / `Http.post` decode network response bodies with strict UTF-8 (`vera/codegen/api.py:756 / :2809 / :2841`). If a remote API returns a response containing non-UTF-8 bytes, the user sees a Python `UnicodeDecodeError` message leaked into the `Result::Err` string. Lower-severity sibling of #589 — the sites are wrapped in `try/except Exception` so no Python traceback escapes wasmtime's trampoline (the failure surfaces as a Vera-level `Err`, not a crash), but the error message contains Python-internals noise rather than a Vera-native diagnostic. Practical trigger probability is low (HTTP/JSON APIs almost universally use UTF-8), but the defensive-coding hygiene gap mirrors #589 and should be closed. Decision pending: `errors="replace"` (preserve data, lose signal) vs explicit invalid-UTF-8 detection with a Vera-native `Err` (preserve signal, lose data). | [#591](https://github.com/aallan/vera/issues/591) |
| Five prelude combinators (`option_unwrap_or`, `result_unwrap_or`, `option_map`, `option_and_then`, `result_map`) are silently skipped from every WASM compile due to two backend gaps: (1) the `_unwrap_or` variants take a bare type variable `@T` as a parameter which the WASM backend can't lower; (2) the `_map` / `_and_then` variants use `apply_fn` inside a `match` arm which the WASM codegen doesn't support yet (already noted as a known gap in `vera/wasm/README.md:643`).  Python target works in full; only `--target browser` (and any future native target sharing the WASM codegen) is affected.  The `apply_fn` path would unblock 3 of 5 functions in one stroke. | [#604](https://github.com/aallan/vera/issues/604) |
| `_fn_ret_type_exprs` registry (introduced in #614, re-used by #602) is not propagated to imported modules — `vera/codegen/modules.py` harvests `_fn_sigs` from the temp generator but doesn't carry over `_fn_ret_type_exprs`.  A `String`-returning fn defined in module A and used in module B's interpolation, OR an `Array<T>`-returning fn defined in module A and indexed via `f()[i]` in module B, still hits the original silent-skip path even after #614 / #602 / #627 closed the in-module shapes.  Surfaced during PR #627's review.  Fix sketch in the issue body: harvest `_fn_ret_type_exprs` alongside `_fn_sigs` in `modules.py`. | [#628](https://github.com/aallan/vera/issues/628) |
| `_canonical_wasm_type` defaults to `"i64"` when the canonicalisation walker can't reach a `NamedType`.  Reachable for unhandled `apply_fn` closure-arg shapes (e.g. `apply_fn(make_mapper(), 42)` where `make_mapper` is a `FnCall` returning a closure).  Result: `call_indirect` type mismatch at WASM validation rather than a source-located `vera check` diagnostic.  Apply_fn / call_indirect parallel of #630 Tier 2's interpolation-side `[E615]` work; would close the same surface for the call_indirect half.  Surfaced by silent-failure-hunter agent during PR #631's review. | [#632](https://github.com/aallan/vera/issues/632) |
| `_resolve_base_type_name` recurses without a cycle guard — inconsistent with the post-#630 `_canonical_named_type` walker (which has explicit `seen` protection).  Currently dead-code-safe because cyclic aliases crash an upstream resolver first, but the inconsistency is a code smell and a latent regression if the upstream crash is ever fixed.  Surfaced by test-analyzer / silent-failure-hunter / code-reviewer agents during PR #631's review. | [#633](https://github.com/aallan/vera/issues/633) |
| `SlotRef` nodes inside `InterpolatedString` carry unreliable spans — `[E615]` diagnostics emitted by the post-#630 harvest report a source location, but it can land on adjacent syntax (e.g. the closing brace of an earlier construct) rather than the offending interpolation segment.  Affects diagnostic quality but not correctness.  Reproducer test fixture exists in `TestE615LoudInterpolationFallthrough630::test_e615_fires_on_adt_in_interpolation`; tightening the soft "line > 0" assertion to "line points at the segment" is the natural acceptance test.  Surfaced during PR #631's review. | [#634](https://github.com/aallan/vera/issues/634) |

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
| Browser runtime: `runtime.mjs` doesn't export the internal string-marshalling helpers (`allocString`, `readString`, `allocArrayOfStrings`), so JavaScript can't pass `String` arguments into Vera functions.  Forces all browser programs into the "compute everything upfront, drain stdout once" pattern; rules out streaming or interactive simulations driven from JS. | [#603](https://github.com/aallan/vera/issues/603) |
| Terminal-vs-browser IO seam in the "write once, run anywhere" framing.  A program built for terminal ergonomics (`IO.sleep` for animation pacing, ANSI escapes for cursor control) compiles cleanly to `--target browser` but doesn't run meaningfully — `IO.sleep` busy-waits on the main thread ([#609](https://github.com/aallan/vera/issues/609) tracks the JSPI-driven yield fix), ANSI escapes render as literal text in the DOM ([#610](https://github.com/aallan/vera/issues/610) tracks an ANSI-subset interpreter for the browser runtime).  Closing both — neither requires a language change — would let typical terminal Vera programs render unchanged on either target.  Vera's design point ("pure core, effects at the boundary") is still right; the boundary just differs between targets. | [#608](https://github.com/aallan/vera/issues/608) (umbrella) |
| Documentation: bidirectional `Int <: Nat` subtyping (with verifier-enforced refinement) is implemented in the type checker but not surfaced in user-facing docs — agents discover it by surprise when `array_length` (formally `@Int`) flows freely into `@Nat` positions. | [#607](https://github.com/aallan/vera/issues/607) |
| Documentation: `decreases` rule for effectful recursive functions is correct in SKILL.md but buried inside a paragraph, requiring agents to triangulate between FizzBuzz (no `decreases`) and the State combinator example (with `decreases`) to find it. | [#605](https://github.com/aallan/vera/issues/605) |

## Refactoring needed

Files that have grown beyond a comfortable size and need decomposition. None of these affect correctness — they are purely internal structural debt.

| File | Lines | Refactoring | Issue |
|------|-------|-------------|-------|
| `tests/test_codegen.py` | 10,019 | Split into feature-focused test files (literals, arithmetic, control flow, strings, arrays, collections, effects, data types) | [#419](https://github.com/aallan/vera/issues/419) |
| `tests/test_checker.py` | 5,522 | Split into phase-focused test files (types, functions, effects, contracts, modules, errors) | [#420](https://github.com/aallan/vera/issues/420) |
| `vera/codegen/api.py` | 2,228 | Extract memory layout utilities → `memory.py`; extract host runtime → `runtime.py` | [#421](https://github.com/aallan/vera/issues/421) |

## Test coverage gaps

Internal test-quality items that don't affect correctness today but would make the suite more durable to refactoring.

| Gap | Issue |
|-----|-------|
| `TestHostPrintInvalidUtf8589` (`tests/test_runtime_traps.py`) has 6 structural source-greps and 1 end-to-end synthetic-WAT test for `host_print`. The other 5 decode sites (`host_stderr`, `host_contract_fail`, `_read_wasm_string`, `markdown.py::_read_string`, `_extract_string`) are pinned only by structural tests. A refactor that centralises the decodes into a `_safe_decode()` helper would break the structural greps even with preserved behaviour. End-to-end tests using synthetic WAT modules per site (~5 × 20 lines) would survive the refactor. Lowest-cost form: parametrize the existing test over an `(import_name, type_signature, payload_construction)` tuple. | [#592](https://github.com/aallan/vera/issues/592) |
| `scripts/fix_allowlists.py --fix` uses a line-offset bulk-shift heuristic that doesn't reliably re-anchor when a documentation file receives multiple edits at different positions in one session.  Hit twice during PR #601's workflow — required manual line-number patching plus one mis-anchored entry that was only caught by CodeRabbit on PR review.  A content-fingerprint anchor (hash the surrounding ~5 lines of each entry) would be robust to multi-edit sequences. | [#606](https://github.com/aallan/vera/issues/606) |

## CI workarounds

Defensive measures currently applied in CI (CVE ignores, forced upgrades, etc.) with explicit removal triggers — bridges, not permanent exceptions.

| Workaround | Where | Rationale | Remove when | Issue |
|------------|-------|-----------|-------------|-------|
| `--ignore-vuln CVE-2026-4539` ([CVE-2026-4539](https://nvd.nist.gov/vuln/detail/CVE-2026-4539)) | `dependency-audit` step in `.github/workflows/ci.yml` | pygments 2.19.2 (transitive via pytest/rich); no fix release exists yet. | pygments > 2.19.2 ships with the fix. | — |
| `pip install --upgrade pip` before audit | Same step | `actions/setup-python@v6` ships pip 26.0.1, which is flagged for [CVE-2026-3219](https://nvd.nist.gov/vuln/detail/CVE-2026-3219) (fixed in pip 26.1, [pypa/pip#13870](https://github.com/pypa/pip/pull/13870)). The runner doesn't track PyPI live, so `pip-audit` scans the runner's bundled pip and fails until we explicitly upgrade. | `actions/setup-python@v6` ships a runner image with pip ≥ 26.1 natively. Drop the `--upgrade pip` from the install step then. | [#537](https://github.com/aallan/vera/issues/537) |

## Runtime workarounds

Defensive measures applied in compiler / runtime code that exist to bridge an upstream-fixed-but-unreleased bug — same shape as the CI workarounds table, but the workaround sits in shipped code rather than CI config.

| Workaround | Where | Rationale | Remove when | Issue |
|------------|-------|-----------|-------------|-------|
| `host_sleep` catches `KeyboardInterrupt` and re-raises as `_VeraExit(130)` so the buggy `wasmtime-py` trampoline (`except Exception`) catches it cleanly instead of letting it escape into Rust as a `BaseException` and abort with a libmalloc SIGABRT | `vera/codegen/api.py::host_sleep` | The current pin (`wasmtime>=44.0.0` in `pyproject.toml`) catches `Exception` rather than `BaseException` in the trampoline; `KeyboardInterrupt` escapes into Rust with an undefined ABI return value. Filed upstream as [bytecodealliance/wasmtime-py#336](https://github.com/bytecodealliance/wasmtime-py/issues/336); fixed by [bytecodealliance/wasmtime-py#337](https://github.com/bytecodealliance/wasmtime-py/pull/337) (merged 2026-05-07 to `main`; the v44.0.0 tag is two commits behind that fix, so no released version yet contains it). | A wasmtime-py PyPI release above 44.0.0 ships containing the upstream fix; bump `pyproject.toml` to require it, then drop the guard in a follow-up PR (see [#599](https://github.com/aallan/vera/issues/599) for the removal-order rationale). | [#599](https://github.com/aallan/vera/issues/599) (bookmark) — closes [#595](https://github.com/aallan/vera/issues/595) |
