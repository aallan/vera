# The Vera language server (`vera lsp`)

Vera ships a language server: a long-running process that an editor (or
an agent) talks to over the [Language Server
Protocol](https://microsoft.github.io/language-server-protocol/), the
standard JSON-RPC protocol editors use to get language intelligence —
diagnostics, hover, go-to-definition, completion — without each editor
reimplementing the compiler. One server, any LSP-capable client: VS
Code, Neovim, Emacs, Helix, Zed, or a coding agent speaking the
protocol directly.

What makes Vera's server different from a typical language server is
*what* it serves. Most language servers answer "does this parse, what
type is this?". Vera's also answers "**does this still prove?**" — it
keeps a warm, incremental Z3 verification session alive between
keystrokes, so contract proofs re-check at editor latency rather than
batch-compile latency, and it exposes that capability to agents through
four custom methods that no generic language server has.

This guide covers the editor/agent surface — the long-running server.
For the command-line surface (`vera check`/`verify`/`test`/`run` and
the introspection commands), see the CLI cookbook,
[TOOLCHAIN.md](TOOLCHAIN.md).

## Install and run

The server lives behind the optional `[lsp]` extra (pure-Python
dependencies: `pygls`, `lsprotocol`):

```bash
git clone https://github.com/aallan/vera.git
cd vera
python -m venv .venv && source .venv/bin/activate
pip install -e ".[lsp]"     # or ".[dev]", which includes it
```

Then:

```bash
vera lsp
```

speaks LSP over stdio. There is nothing to configure server-side: the
client launches the process and the handshake does the rest. Without
the extra installed, `vera lsp` prints an actionable install message
and exits; every other `vera` command works without it.

### Wiring up an editor

- **VS Code** — the [bundled extension](editors/vscode/) starts the
  server automatically for `.vera` files, finding the binary via the
  `vera.lsp.path` setting, then a workspace-local venv
  (`.venv/bin/vera`, or `.venv\Scripts\vera.exe` on Windows — so a
  from-source clone needs no configuration on either platform), then
  `PATH`. See its [README](editors/vscode/README.md) for setup.
- **Anything else** — point your editor's generic LSP client at the
  command `vera lsp` for language `vera` / file pattern `*.vera`,
  using stdio transport and full-document sync. That is the entire
  contract.

## Standard features

On `didOpen`/`didChange` the server runs the full pipeline — parse,
type-check, **verify** — on the in-memory buffer (unsaved changes
included) and publishes:

- **Diagnostics** with the same stable error codes, rationale, and
  spec references as `vera check --json` / `vera verify --json`, plus
  a `tier` annotation on verification diagnostics (Tier 3 fallbacks
  carry `tier: 3` in their data).
- **Per-function verification-tier hints** — a Hint-severity
  diagnostic per function summarising its proof state: "Tier 1 — all
  contracts proven by Z3" or "Tier 3 — N of M obligations fall back
  to runtime checks". The verifier itself stays silent about
  successes; the hint is how the editor shows you which functions are
  *proven* rather than merely checked.
- **Hover** — the inferred type of the smallest expression under the
  cursor.
- **Go-to-definition on slot references** — `@T.n` under the cursor
  jumps to the parameter it names under De Bruijn resolution
  (most-recent-first), which is exactly the lookup humans find
  hardest to do in their head.
- **Typed-hole completion** — with the cursor at a `?` hole,
  completion lists the in-scope bindings that fit, innermost first,
  each with its type.

## What no generic language server can do

### The warm verification core

Verification state persists between edits. Each function's discharged
proof obligations are cached against a structural hash, and the
invalidation rule follows the proof dependencies: editing a function's
*body* re-verifies only that function; editing its *contract* also
re-verifies every caller (callers assume postconditions and must
re-prove preconditions at call sites). Timeouts are never cached. The
result: after the first full pass, re-verification cost is
proportional to what your edit could actually have broken.

### Custom methods: the agent surface

Four methods extend LSP 3.17, designed for coding agents rather than
humans-with-cursors. All take plain JSON params; malformed requests
(missing/non-string fields, unknown functions) refuse with standard
JSON-RPC `InvalidParams` rather than opaque errors.

#### `vera/speculativeEdit` — "would this edit break my proofs?"

```json
{"uri": "file:///main.vera", "text": "<full proposed source>"}
```

Verifies the proposed text *in memory* — the canonical document, its
published diagnostics, and the editor's view are untouched — and
returns a **proof delta** against the document's current obligation
set:

```json
{
  "ok": true,
  "proof_delta": {
    "newly_discharged":   [],
    "newly_undischarged": [{"fn": "f", "kind": "nat_sub",
                            "expr": "@Nat.0 - 1", "line": 6, "column": 3,
                            "status_before": "verified",
                            "status_after": "violated"}],
    "timed_out": [], "removed": [], "unchanged": 11
  },
  "diagnostics": 1
}
```

An agent learns whether an edit **keeps** the program's proofs
(everything still discharges), **breaks** them (obligations become
violated or fall to runtime checks), or **strengthens** them
(previously-runtime obligations now prove) — before committing
anything.

#### `vera/proposeEdit` — the enforced edit workflow

```json
{"uri": "file:///main.vera", "text": "<full proposed source>", "force": false}
```

The whole edit → verify → apply sequence as one method, so the
verification gate cannot be skipped or reordered: the proposed text is
speculatively verified, and **applies only if** the proof delta has no
`newly_undischarged` obligations and the proposed state has no error
diagnostics. On apply the server issues `workspace/applyEdit` (the
client owns the buffer), updates its canonical state, and republishes
diagnostics; on refuse, nothing changes and the response says why:

```json
{"applied": false, "ok": true, "proof_delta": {...}, "diagnostics": 0}
```

`"force": true` (strictly boolean — anything else fails closed)
overrides the gate for the cases where breaking a proof is the point,
but it must be said out loud. This is the same philosophy as Vera's
mandatory contracts, applied to tooling: the right thing is the only
easy thing.

#### `vera/strengthenContract` — contract change with a call-site audit

```json
{"uri": "file:///main.vera", "fn": "callee",
 "kind": "requires", "expr": "@Nat.0 >= 1"}
```

Splices the new expression over the first `requires`/`ensures` clause
of the named top-level function and runs it through the proposeEdit
gate. The call-site audit *is* the proof delta: a tightened
precondition some caller no longer satisfies surfaces as
`newly_undischarged` items of kind `call_pre` located **at the call
sites**, and the gate refuses. There is no `force` here — an agent
that wants to push through a breaking contract change must construct
the full text and call `vera/proposeEdit` with `force` explicitly.

#### `vera/addEffect` — effect propagation through the call graph

```json
{"uri": "file:///main.vera", "fn": "target", "effect": "Async"}
```

The genuinely multi-site one. Adding an effect to a function
invalidates the effect row of every **transitive caller**, so the
server computes that closure over the call graph, rewrites each
affected `effects(...)` clause (`pure` → `<Async>`; `<IO>` →
`<IO, Async>`; functions already naming the effect are skipped —
identity is the base name before type arguments), and verifies the
whole rewrite as **one** candidate through the proposeEdit gate:
all-or-nothing, never a half-propagated document. The response adds
`"rewritten"`: the affected functions in declaration order. If every
row already carries the effect, nothing runs and the no-op shape comes
back (`"applied": false, "ok": true, "proof_delta": null,
"rewritten": []`).

Declared-but-unused effects are legal in Vera, so the agent ordering
"propagate rows first, then write the effectful code" type-checks at
every step.

### A typical agent loop

1. `didOpen` the file; read the published diagnostics and tier hints.
2. Draft an edit; `vera/speculativeEdit` it; inspect the proof delta.
3. If the delta looks right, `vera/proposeEdit` the same text — the
   server re-verifies (cheaply, from the warm cache) and applies.
4. For the two structured refactors — tightening a contract,
   threading an effect — call the dedicated method instead and let
   the server construct the candidate.

## Current limitations

| Limitation | Issue |
|-----------|-------|
| Single-file model: module imports resolve from disk, not from open editor buffers, so unsaved edits to an imported module are invisible until saved. | [#724](https://github.com/aallan/vera/issues/724) |
| Slot go-to-definition covers parameters only — references binding through `let`/`match` have no definition site to jump to yet. | [#181](https://github.com/aallan/vera/issues/181) |
| `vera/addEffect` is handler-unaware: a caller that handles the effect in a `handle[E]` block is still rewritten. Propagation also stops at the file boundary, by design. | [#725](https://github.com/aallan/vera/issues/725) |

## Under the hood

The server is ~1,400 lines over the reusable obligation core in
`vera/obligations/` (reified `ProofObligation` records, the warm
incremental `VerificationSession`). Architecture notes live in the
[compiler README](vera/README.md) module map; the design history —
including why the obligation core was built before any wire format —
is the comment trail on
[#222](https://github.com/aallan/vera/issues/222).
