# Environment Variables

Vera reads a small set of `VERA_*` environment variables.  This document is the canonical reference; other docs (README, AGENTS, TESTING, CONTRIBUTING, SKILL, CLAUDE) link here for the full table and only mention individual variables where they're relevant in context.

| Variable | Purpose | Phase | Required |
|---|---|---|---|
| [`VERA_ANTHROPIC_API_KEY`](#inference-provider-keys) | Anthropic provider key for the `Inference` effect | runtime | one of the six provider keys, when running an `Inference` program |
| [`VERA_OPENAI_API_KEY`](#inference-provider-keys) | OpenAI provider key for the `Inference` effect | runtime | as above |
| [`VERA_MOONSHOT_API_KEY`](#inference-provider-keys) | Moonshot (Kimi) provider key for the `Inference` effect | runtime | as above |
| [`VERA_MISTRAL_API_KEY`](#inference-provider-keys) | Mistral provider key for the `Inference` effect | runtime | as above |
| [`VERA_XAI_API_KEY`](#inference-provider-keys) | xAI (Grok) provider key for the `Inference` effect | runtime | as above |
| [`VERA_DEEPSEEK_API_KEY`](#inference-provider-keys) | DeepSeek provider key for the `Inference` effect | runtime | as above |
| [`VERA_INFERENCE_PROVIDER`](#explicit-provider--model-overrides) | Force a specific provider rather than auto-detecting from the non-empty keys | runtime | optional |
| [`VERA_INFERENCE_MODEL`](#explicit-provider--model-overrides) | Override the provider's default model | runtime | optional |
| [`VERA_DB_URL`](#vera_db_url) | Database connection for the `DB` effect | runtime | optional (defaults to `sqlite::memory:`) |
| [`VERA_JS_COVERAGE`](#vera_js_coverage) | Opt-in V8 coverage during browser-parity tests | dev / CI | optional |
| [`VERA_Z3_TIMEOUT_MS`](#vera_z3_timeout_ms) | Per-query Z3 budget in milliseconds — raises or lowers the Tier 1 / Tier 3 boundary | verify / test / language server | optional (defaults to `10000`) |
| [`VERA_EAGER_GC`](#vera_eager_gc) | Force `$gc_collect` on every allocation — debugging knob for GC-rooting bugs | compile-time (dev) | optional |
| [`VERA_GC_CHECK_MARKS`](#vera_gc_check_marks) | Trap if a GC mark store targets an address that is not an object body — debugging knob for conservative-scan false positives | compile-time (dev) | optional |
| [`VERA_DEBUG_HOST_ERRORS`](#vera_debug_host_errors) | Re-raise a host callback's original exception instead of converting it — debugging knob for host-binding bugs | runtime (dev) | optional |

## Inference provider keys

The `Inference` effect ([spec/07-effects.md](spec/07-effects.md)) reaches an LLM provider over HTTP.  The runtime auto-detects which provider to use by checking which of these six variables is set to a non-empty value:

- `VERA_ANTHROPIC_API_KEY`
- `VERA_OPENAI_API_KEY`
- `VERA_MOONSHOT_API_KEY` (Kimi)
- `VERA_MISTRAL_API_KEY`
- `VERA_XAI_API_KEY` (Grok)
- `VERA_DEEPSEEK_API_KEY`

The order above is the registry order, and detection walks it and takes the **first** provider whose key is set to a NON-EMPTY value — a variable exported as the empty string is skipped, as if unset — so setting more than one key is deterministic rather than ambiguous, but silently ignores every key after the first.  Set exactly one, or use [`VERA_INFERENCE_PROVIDER`](#explicit-provider--model-overrides) to name the one you mean.  The conformance tests `tests/conformance/ch09_inference.vera` and `tests/conformance/ch09_http.vera` are skipped in CI because no provider key is set there; to run them locally:

```bash
export VERA_ANTHROPIC_API_KEY=sk-ant-...   # or any other key above, e.g. VERA_XAI_API_KEY=xai-...
vera run tests/conformance/ch09_inference.vera
```

The same export works for `examples/inference.vera` from `README.md`.

## Explicit provider / model overrides

- **`VERA_INFERENCE_PROVIDER`** — set to `anthropic`, `openai`, `moonshot`, `mistral`, `xai`, or `deepseek` to force the runtime to use that provider, overriding the auto-detect-by-key logic.  Useful when more than one provider key is set in the environment (e.g. a development shell), where auto-detection would otherwise take the first key in the order listed above.
- **`VERA_INFERENCE_MODEL`** — set to a provider-specific model identifier to override the default model.  Each provider has its own default; consult the provider's docs for valid model strings.

Both are optional.  When unset, the runtime uses auto-detection and the provider's default model.

## `VERA_DB_URL`

Chooses the database the `DB` effect connects to at runtime (`DB.query` / `DB.execute`; spec [§9.5.7](spec/09-standard-library.md)).

- **Unset** — an in-memory SQLite database (`sqlite::memory:`), created empty per run. Hermetic: nothing touches disk, so `vera test` and examples run without configuration.
- **`sqlite:///path/to/file.db`** — an on-disk SQLite file, e.g.:

  ```bash
  VERA_DB_URL=sqlite:///examples/sqlitedb.sqlite vera run examples/sqlitedb.vera
  ```

Phase: runtime (the connection is opened once at startup, during DB host-function registration — only for programs that use a `DB` operation — and reused for the rest of the run). In v1 the effect is SQLite-only and single-connection; a value that isn't one of the in-memory spellings or a `sqlite://` URL is treated as a SQLite file path, and an unopenable URL surfaces as the operation's `Err` result rather than a crash. Further backends are [#1143](https://github.com/aallan/vera/issues/1143). The browser runtime returns `Err` for every `DB` operation regardless of this variable, and the `wasi-p2` target rejects `<DB>` programs at compile time.

## `VERA_JS_COVERAGE`

Set to any non-empty value to enable V8 coverage collection during the browser-parity test suite (`tests/test_browser.py`).  Without it, the JavaScript runtime tests still run — they just don't emit a coverage report:

```bash
VERA_JS_COVERAGE=1 pytest tests/test_browser.py -v
```

CI sets this for the browser-parity job; local runs typically don't need it.  See [TESTING.md](TESTING.md) for the broader test layout.

## `VERA_Z3_TIMEOUT_MS`

The per-query budget Z3 is given for a single proof obligation, in
milliseconds.  Defaults to `10000`.  `vera verify --timeout-ms N` takes
precedence over it, and an explicit `timeout_ms=` argument takes precedence
over both.

```bash
VERA_Z3_TIMEOUT_MS=60000 vera verify program.vera
vera verify --timeout-ms 60000 program.vera     # same, for one run
```

A non-integer or non-positive value is a loud error rather than a silent
fall back to the default, because a mistyped budget that quietly reverted
would be indistinguishable from the host-sensitivity this setting exists to
remove.

**When to use it.**  The budget decides more than how long a run takes.  An
obligation whose proof lands near it is Tier 1 on a fast machine and Tier 3
on a slow or busy one, which makes the tier a property of the host rather
than of the program.  Raising the budget is therefore the way to read a
Tier 3 correctly: if it becomes Tier 1, the claim only needed more time.

If it stays Tier 3, the run itself says which of two things happened, and
the distinction matters — no finite budget can establish that no budget
would.  A `timeout` status means the solver was still working when the
budget expired: undecided at this budget, and a larger one may yet prove it.
A `tier3` status means the obligation was never handed to the solver as a
decidable goal — a claim standing behind `sqrt` or `asin`, outside the
translated fragment — and no budget reaches that.  `vera verify --json`
reports the status per obligation, so the two are distinguishable without
guessing.  Float arithmetic in postconditions is where this bites, costing
roughly an order of magnitude more solver time than the integer equivalent.

Read by `vera/smt.py::resolve_timeout_ms`, at the seams that construct a
solver (`verify()`, `ContractVerifier`, and the LSP's `VerificationSession`),
so it reaches `vera verify`, `vera test` and the language server.  `vera
compile` and `vera run` never build a solver and are unaffected.

## `VERA_EAGER_GC`

A diagnostic knob for hunting GC-rooting bugs in the WASM codegen.  Set to `1`, `true`, `yes` or `on` (case-insensitive, surrounding whitespace ignored) at **compile time** to make the emitted `$alloc` function call `$gc_collect` on every allocation, regardless of memory pressure:

```bash
VERA_EAGER_GC=1 vera run program.vera
```

Read by `vera/codegen/assembly.py::AssemblyMixin._emit_alloc`; affects the WAT that `vera compile` emits, not the runtime behaviour of an already-compiled module.

**When to use it.**  The conservative mark-sweep collector marks only from the shadow stack (`$gc_sp`); WAT locals are not roots.  If a heap pointer is held only in a WAT local across an allocation, the allocation can trigger a GC that reclaims the still-needed object — the resulting use-after-free typically only manifests at scale, when heap pressure is high enough to fire `$gc_collect` at the wrong moment.  Eager-GC collapses this from "fires occasionally at scale" to "fires on the very next allocation," giving a sharp signal for diagnosis.

This was the diagnostic that cracked [#593](https://github.com/aallan/vera/issues/593): the rebuilt minimum reproducer crashed at generation 0 under `VERA_EAGER_GC=1` rather than around generation 20 without it, and the much smaller stack trace pinpointed the missing return-value root in `_compile_lifted_closure`.

**Cost.**  Programs run orders of magnitude slower with `$gc_collect` on every allocation — never enable it in production or in normal test runs.  It's a debugging knob, not a release-build option.  Tests that exercise this knob live in `tests/test_codegen_closures.py::TestClosureReturnShadowPushBalance`.

## `VERA_GC_CHECK_MARKS`

A diagnostic knob for the collector's own soundness, not for a program's.

```bash
VERA_GC_CHECK_MARKS=1 VERA_EAGER_GC=1 vera run program.vera
```

Set to `1`, `true`, `yes` or `on` — the same spellings [`VERA_EAGER_GC`](#vera_eager_gc) accepts, because both read the one predicate in `vera/envflags.py` — to make the mark phase assert, before every mark store, that the address it is about to write is a real object body.

The mark phase is conservative: it classifies a word as a heap pointer from two cheap tests (heap range, and `(val - $gc_heap_start) & 7 == 4`). Those are sound for the *reads* a conservative collector makes — a false positive costs retention and nothing more — but marking also **writes**, ORing the mark bit into the word four bytes below the candidate. A false positive that lands inside a live object therefore corrupts it ([#1382](https://github.com/aallan/vera/issues/1382)).

Candidates are now validated against an object-base bitmap that Phase 1 fills as it walks, so the store cannot escape its object. This knob is the independent check on that: it re-derives the answer by walking the heap from `$gc_heap_start` along the allocator's own `align_up(size + 4, 8)` chain and traps when the target is not a body address it reached. Deliberately independent of the bitmap — dropped into a pre-#1382 collector it fires, which is what makes it a check rather than a restatement of the fix.

O(heap) per mark store on top of whatever `VERA_EAGER_GC` already costs, so it is slower still than that knob. Pair the two when a wrong answer smells like heap corruption; use neither in production.

## `VERA_DEBUG_HOST_ERRORS`

A diagnostic knob for debugging the host bindings themselves.  Set to `1`, `true`, `yes` or `on` — the same spellings [`VERA_EAGER_GC`](#vera_eager_gc) accepts, because both read the one predicate in `vera/envflags.py` — to make `execute()` re-raise a host callback's original Python exception instead of converting it to a `WasmTrapError`:

```bash
VERA_DEBUG_HOST_ERRORS=1 vera run program.vera
```

Read by `vera/codegen/api.py::execute`; affects how a failure is *presented*, never whether one happens.

**When to use it.**  [#1302](https://github.com/aallan/vera/issues/1302) made every exception escaping the guest invocation arrive as a classified Vera error — a one-line `Error:` with the host's own sentence, the captured `stdout`, and a source backtrace — because a user-level program must never produce a Python traceback regardless of what it does.  That is right for someone running a Vera program and unhelpful for someone who suspects the *binding* is wrong: the sentence survives, the Python frames that say where in the binding it came from do not.  They remain on the exception's `__cause__`, which serves a library caller and not a person reading a terminal.  This knob puts the frames back.

**Cost.**  None at runtime — the variable is read only on the failure path, and only after a host callback has already raised.  It is still a debugging knob rather than a mode, and it disables more than a message.  With it set, a program that would have exited with a clean Vera diagnostic exits with an interpreter traceback instead, so nothing that parses `vera run` output should be run under it — and `vera serve` reverts to its pre-[#1302](https://github.com/aallan/vera/issues/1302) behaviour, where the raw exception bypasses the `WasmTrapError` handler that answers the request, leaving the connection unanswered rather than returning a 500.  The knob turns off the stronger invariant, not just the prettier output.  Tests that exercise this knob live in `tests/test_runtime_traps.py::TestHostErrorDebugKnob1302`.

## Adding a new environment variable

When adding a new `VERA_*` variable to the codebase:

1. Add a row to the table at the top of this document.
2. Add a section explaining purpose, phase (compile-time / runtime / dev), and an example.
3. If it's user-facing (runtime), mention it in [README.md](README.md) and the relevant agent-facing docs ([SKILL.md](SKILL.md), [AGENTS.md](AGENTS.md)).  If it's dev-only, mention it in [CONTRIBUTING.md](CONTRIBUTING.md) and [TESTING.md](TESTING.md).  Other docs link here for the full reference rather than duplicating the explanation.

Keeping the catalogue centralised stops `VERA_*` variables from drifting into one-line mentions scattered across half a dozen documents — the failure mode that motivated creating this file in the first place.
