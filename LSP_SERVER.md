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
python -m venv .venv && source .venv/bin/activate   # Windows: .venv\Scripts\activate
python -m pip install "veralang[lsp]"
```

To install the current GitHub source instead:

```bash
git clone https://github.com/aallan/vera.git
cd vera
python -m venv .venv && source .venv/bin/activate   # Windows: .venv\Scripts\activate
python -m pip install -e ".[lsp]"     # or ".[dev]", which includes it
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

- **VS Code** — install [Vera Language from the VS Code
  Marketplace](https://marketplace.visualstudio.com/items?itemName=veralang.vera-language)
  (or see the [extension source](https://github.com/aallan/vera/tree/main/editors/vscode)).
  It starts the server automatically for `.vera` files, finding the binary via the
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
  hardest to do in their head. Both sides of the lookup — the
  parameter's name and the reference's — are rendered by the same
  function the checker keys its binding table with, so a
  parameterised reference (`@Option<Int>.0`) resolves, an
  alias-spelled parameter (`@Option<Cnt>` under `type Cnt = Int`) is
  reachable from its canonical spelling, and a reference inside a
  `where` helper resolves against that helper's own scope, including
  any `forall` variables it inherits from its parent.
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
    "timed_out": [], "removed": [], "unchanged": 11,
    "proof_regressions": [{"fn": "f", "kind": "nat_sub",
                           "expr": "@Nat.0 - 1", "line": 6, "column": 3,
                           "line_before": 6, "column_before": 3,
                           "status_before": "verified",
                           "status_after": "violated"}]
  },
  "diagnostics": 1
}
```

An agent learns whether an edit **keeps** the program's proofs
(everything still discharges), **breaks** them (obligations become
violated or fall to runtime checks), or **strengthens** them
(previously-runtime obligations now prove) — before committing
anything.

The first four lists **sort by the obligation's status AFTER the edit**,
which makes them a presentation of the delta rather than an answer to
"did this edit take a proof away?".  That question has its own list:
`proof_regressions` holds every obligation that was `verified` before
and is anything else after — `timeout`, `tier3`, `tier3_unguarded` or
`violated` — so an obligation appears in it **as well as** in whichever
category its new status puts it in (`verified → timeout` is in both
`timed_out` and `proof_regressions`).  Read `proof_regressions` to ask
about lost proofs; read the categories to display what happened.

The two views also differ on **identity**, and deliberately.  An
obligation is keyed by its span, so one inserted line above it gives it
a new key: the categories report that as a removal plus a rediscovery,
which is what a display of positions should say.  The gate cannot
reason that way — an edit that shifts a line and costs a proof further
down the file would walk straight past it — so before judging anything
it pairs the leftovers on a span-insensitive key (file, owning
function, function, kind, predicate text; equal keys pair positionally
in source order).  A pair is one obligation that **moved**.  Pairing changes what an entry
is reported *against*, not which list it is in: the categories still
partition the speculative stream by the after-status, and a relocated
obligation is still a removal at its old span plus an entry at its new
one — it simply carries the `status_before` it paired with, where an
obligation the edit really did introduce carries `null`.  The gate
reads that: a `newly_undischarged` entry whose `status_before` equals
its `status_after` only moved, so it introduced nothing and took
nothing away.  Relocation is invisible to the gate; the presentation
keeps its span view.

Each `proof_regressions` entry carries both ends: `line` / `column` are
where the obligation is now, `line_before` / `column_before` where it
was.  They differ exactly when the obligation moved — in the same-span
example above they are equal — and the pair is what points an agent at
the proof it broke rather than at the line it happens to sit on now.

An old obligation with no counterpart on the new side is a **deletion**,
not a regression, and does not need `force`: the gate protects proofs,
not contracts — the removal is visible in the edit itself, and no
unproved code is left behind.  It is reported under `removed` with the
status it had.  Replacing a proved contract with a differently-worded
one is a deletion plus an addition, so the replacement is judged as an
addition: refused if it is `violated` or `tier3`, applied if it merely
times out, which is the same boundary any newly introduced timeout
already sits on.  What the pairing key does not cover, by construction:
renaming the function, changing the obligation's kind, rewriting the
predicate text, or moving the code to another file all make it a new
obligation to the gate.

#### `vera/proposeEdit` — the enforced edit workflow

```json
{"uri": "file:///main.vera", "text": "<full proposed source>", "force": false}
```

The whole edit → verify → apply sequence as one method, so the
verification gate cannot be skipped or reordered: the proposed text is
speculatively verified, and **applies only if** the proof delta has no
`proof_regressions` (no obligation lost a proof — whatever it lost it
to, and wherever in the file it now sits), no `newly_undischarged`
entry whose `status_before` differs from its `status_after`, and no
error diagnostics in the proposed state.  Neither list subsumes the
other: `newly_undischarged` is the only one that can see an obligation
the edit INTRODUCES, which has no `before` to regress from and so
arrives with `status_before: null`.  The `status_before` qualifier is
what lets a **relocated** obligation through: one that is undischarged
at both ends of its pair is listed here — the categories partition the
speculative stream, so it has to be — but it introduced nothing and
took nothing away, so the gate passes it.  A pair that worsened is
refused exactly as the identical unmoved edit is.  On apply the server issues `workspace/applyEdit` (the client
owns the buffer), updates its canonical state, and republishes
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

The closure is **bounded at handlers**: a call site inside a
`handle[E]` body contributes no edge, because the handler discharges
the effect there, so a caller that wraps every one of its call sites
is left unrewritten and nothing propagates past it. A caller that also
reaches the callee on an unhandled path is still rewritten — the
effect genuinely escapes along that path — and a call in a handler
*clause* propagates, since a clause body runs outside its own handler,
as does one in the handler's *state initialiser*, which is evaluated
in the enclosing scope before the handler is installed.
The bound compares the `handle[...]` head's **spelling** to the
requested effect, type arguments included and as written rather than
as resolved. So `handle[State<Nat>]` does not bound a `State<Int>`
propagation and a caller around it still gets the row — which it
needs, since the checker discharges against effect *instance*
equality. An alias spelling of the same instance
(`handle[State<MyAlias>]` with `type MyAlias = Int`) does not bound it
either, though the checker does discharge that one: there the
comparison under-prunes, leaving a row the program does not need,
which still type-checks. That is the documented behaviour until
[#1292](https://github.com/aallan/vera/issues/1292) keys the bound on
the resolved instance. Propagation stops at the file boundary, by
design: module-qualified calls are not followed.

Rows are rewritten for top-level functions only. A call inside a
`where` block attributes to the top-level function containing it —
that is what the closure reports, and the handler bound applies inside
a helper body the same way — but the helper's own `effects(...)` row is
never rewritten, so a helper that itself needs the new effect leaves
the candidate refused at the gate rather than half-applied.

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

![The agent proof-delta loop: didOpen returns diagnostics and tier hints; speculativeEdit verifies a draft in memory and returns a proof delta without touching the document; proposeEdit re-verifies from the warm cache and applies only if nothing newly fails to prove.](assets/diagrams/lsp-session.svg)

## Current limitations

A row without an issue link is deliberate behaviour rather than
tracked work.

| Limitation | Issue |
|-----------|-------|
| Single-file model: module imports resolve from disk, relative to the analysed document's own path, not from open editor buffers — so unsaved edits to an imported module are invisible until saved. A document that names no local path resolves no imports and is analysed alone: an `untitled:` buffer or other non-`file:` URI, and a `file://host/…` URI naming another machine (carried opaquely — it used to raise out of the didOpen handler on Python 3.14). | [#724](https://github.com/aallan/vera/issues/724) |
| Slot go-to-definition covers parameters only — references binding through `let`/`match` have no definition site to jump to yet. | [#181](https://github.com/aallan/vera/issues/181) |
| `vera/addEffect` propagation stops at the file boundary, by design: the closure runs over unqualified call names, so a module-qualified call is not followed and a caller in another file is never rewritten. | — |

## Under the hood

The server is a thin transport and feature layer over the reusable
obligation core in `vera/obligations/` (reified `ProofObligation`
records, the warm incremental `VerificationSession`). Architecture
notes — and the per-module line counts, gated against the source tree
so they cannot drift out of step with it — live in the
[compiler README](vera/README.md) module map; the design history —
including why the obligation core was built before any wire format —
is the comment trail on
[#222](https://github.com/aallan/vera/issues/222).
