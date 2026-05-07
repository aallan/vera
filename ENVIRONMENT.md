# Environment Variables

Vera reads a small set of `VERA_*` environment variables.  This document is the canonical reference; other docs (README, AGENTS, TESTING, CONTRIBUTING, SKILL, CLAUDE) link here for the full table and only mention individual variables where they're relevant in context.

| Variable | Purpose | Phase | Required |
|---|---|---|---|
| [`VERA_ANTHROPIC_API_KEY`](#inference-provider-keys) | Anthropic provider key for the `Inference` effect | runtime | one of the four provider keys, when running an `Inference` program |
| [`VERA_OPENAI_API_KEY`](#inference-provider-keys) | OpenAI provider key for the `Inference` effect | runtime | as above |
| [`VERA_MOONSHOT_API_KEY`](#inference-provider-keys) | Moonshot (Kimi) provider key for the `Inference` effect | runtime | as above |
| [`VERA_MISTRAL_API_KEY`](#inference-provider-keys) | Mistral provider key for the `Inference` effect | runtime | as above |
| [`VERA_INFERENCE_PROVIDER`](#explicit-provider--model-overrides) | Force a specific provider rather than auto-detecting from the keys present | runtime | optional |
| [`VERA_INFERENCE_MODEL`](#explicit-provider--model-overrides) | Override the provider's default model | runtime | optional |
| [`VERA_JS_COVERAGE`](#vera_js_coverage) | Opt-in V8 coverage during browser-parity tests | dev / CI | optional |
| [`VERA_EAGER_GC`](#vera_eager_gc) | Force `$gc_collect` on every allocation — debugging knob for GC-rooting bugs | compile-time (dev) | optional |

## Inference provider keys

The `Inference` effect ([spec/07-effects.md](spec/07-effects.md)) reaches an LLM provider over HTTP.  The runtime auto-detects which provider to use by checking which of these four variables is set:

- `VERA_ANTHROPIC_API_KEY`
- `VERA_OPENAI_API_KEY`
- `VERA_MOONSHOT_API_KEY` (Kimi)
- `VERA_MISTRAL_API_KEY`

Set exactly one (or use [`VERA_INFERENCE_PROVIDER`](#explicit-provider--model-overrides) to force a choice when more than one is set).  The conformance tests `tests/conformance/ch09_inference.vera` and `tests/conformance/ch09_http.vera` are skipped in CI because no provider key is set there; to run them locally:

```bash
export VERA_ANTHROPIC_API_KEY=sk-ant-...
vera run tests/conformance/ch09_inference.vera
```

The same export works for `examples/inference.vera` from `README.md`.

## Explicit provider / model overrides

- **`VERA_INFERENCE_PROVIDER`** — set to `anthropic`, `openai`, `moonshot`, or `mistral` to force the runtime to use that provider, overriding the auto-detect-by-key logic.  Useful when more than one provider key is set in the environment (e.g. a development shell).
- **`VERA_INFERENCE_MODEL`** — set to a provider-specific model identifier to override the default model.  Each provider has its own default; consult the provider's docs for valid model strings.

Both are optional.  When unset, the runtime uses auto-detection and the provider's default model.

## `VERA_JS_COVERAGE`

Set to any non-empty value to enable V8 coverage collection during the browser-parity test suite (`tests/test_browser.py`).  Without it, the JavaScript runtime tests still run — they just don't emit a coverage report:

```bash
VERA_JS_COVERAGE=1 pytest tests/test_browser.py -v
```

CI sets this for the browser-parity job; local runs typically don't need it.  See [TESTING.md](TESTING.md) for the broader test layout.

## `VERA_EAGER_GC`

A diagnostic knob for hunting GC-rooting bugs in the WASM codegen.  Set to `1`, `true`, or `yes` at **compile time** to make the emitted `$alloc` function call `$gc_collect` on every allocation, regardless of memory pressure:

```bash
VERA_EAGER_GC=1 vera run program.vera
```

Read by `vera/codegen/assembly.py::AssemblyMixin._emit_alloc`; affects the WAT that `vera compile` emits, not the runtime behaviour of an already-compiled module.

**When to use it.**  The conservative mark-sweep collector marks only from the shadow stack (`$gc_sp`); WAT locals are not roots.  If a heap pointer is held only in a WAT local across an allocation, the allocation can trigger a GC that reclaims the still-needed object — the resulting use-after-free typically only manifests at scale, when heap pressure is high enough to fire `$gc_collect` at the wrong moment.  Eager-GC collapses this from "fires occasionally at scale" to "fires on the very next allocation," giving a sharp signal for diagnosis.

This was the diagnostic that cracked [#593](https://github.com/aallan/vera/issues/593): the rebuilt minimum reproducer crashed at generation 0 under `VERA_EAGER_GC=1` rather than around generation 20 without it, and the much smaller stack trace pinpointed the missing return-value root in `_compile_lifted_closure`.

**Cost.**  Programs run orders of magnitude slower with `$gc_collect` on every allocation — never enable it in production or in normal test runs.  It's a debugging knob, not a release-build option.  Tests that exercise this knob live in `tests/test_codegen_closures.py::TestClosureReturnShadowPushBalance`.

## Adding a new environment variable

When adding a new `VERA_*` variable to the codebase:

1. Add a row to the table at the top of this document.
2. Add a section explaining purpose, phase (compile-time / runtime / dev), and an example.
3. If it's user-facing (runtime), mention it in [README.md](README.md) and the relevant agent-facing docs ([SKILL.md](SKILL.md), [AGENTS.md](AGENTS.md)).  If it's dev-only, mention it in [CONTRIBUTING.md](CONTRIBUTING.md) and [TESTING.md](TESTING.md).  Other docs link here for the full reference rather than duplicating the explanation.

Keeping the catalogue centralised stops `VERA_*` variables from drifting into one-line mentions scattered across half a dozen documents — the failure mode that motivated creating this file in the first place.
