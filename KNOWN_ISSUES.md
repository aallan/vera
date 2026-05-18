# Known issues

Bugs and limitations tracked against the [issue tracker](https://github.com/aallan/vera/issues). This file is a curated snapshot — the issue tracker is the source of truth.

## Bugs

| Bug | Issue |
|-----|-------|
| `vera test` reports functions as `VERIFIED (Tier 1)` when the verifier has refuted them with an `E500` counterexample.  The classifier only harvests `severity == "warning"` Tier 3 codes (`E520`–`E525`); `severity == "error"` codes (`E500`, `E501`, `E502`) flow past untouched and the function falls through to the default `"verified"` branch.  Reproducer: a function with `requires(@Nat.0 < 1000) ensures(@Nat.result == @Nat.0 * 2)` and body `@Nat.0 + @Nat.0 + 1` is flagged by `vera verify` (E500 with counterexample `@Nat.0 = 0`) but reported as `VERIFIED (Tier 1)` with exit code 0 by `vera test`.  Workaround: run `vera verify` before trusting `vera test` results.  Severity: correctness, unsafe direction. | [#681](https://github.com/aallan/vera/issues/681) |

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
| Text-mode `open()` / `read_text()` / `write_text()` without explicit `encoding='utf-8'` in `vera/`, `scripts/`, `tests/`.  PR for #641 covered CI via `PYTHONUTF8=1` (PEP 540) and added explicit UTF-8 to the load-bearing `vera/parser.py` grammar load, but the broader audit (~30 sites) is the durable fix — locally users on Windows without `PYTHONUTF8=1` set still hit cp1252 fallbacks on individual files.  Acceptance: every text-mode call has explicit encoding + a pre-commit check enforces the convention + `PYTHONUTF8=1` line in CI can be removed. | [#645](https://github.com/aallan/vera/issues/645) |

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
| `host_sleep` catches `KeyboardInterrupt` and re-raises as `_VeraExit(130)` so the buggy `wasmtime-py` trampoline (`except Exception`) catches it cleanly instead of letting it escape into Rust as a `BaseException` and abort with a libmalloc SIGABRT | `vera/codegen/api.py::host_sleep` | The current pin (`wasmtime>=44.0.0` in `pyproject.toml`) catches `Exception` rather than `BaseException` in the trampoline; `KeyboardInterrupt` escapes into Rust with an undefined ABI return value. Filed upstream as [bytecodealliance/wasmtime-py#336](https://github.com/bytecodealliance/wasmtime-py/issues/336); fixed by [bytecodealliance/wasmtime-py#337](https://github.com/bytecodealliance/wasmtime-py/pull/337) (merged 2026-05-07 to `main`; the v44.0.0 tag is two commits behind that fix, so no released version yet contains it). | A wasmtime-py PyPI release above 44.0.0 ships containing the upstream fix; bump `pyproject.toml` to require it, then drop the guard in a follow-up PR (see [#599](https://github.com/aallan/vera/issues/599) for the removal-order rationale). | [#599](https://github.com/aallan/vera/issues/599) (bookmark) |
