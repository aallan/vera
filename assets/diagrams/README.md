# assets/diagrams — the documentation diagram set

Hand-authored SVG diagrams embedded across the documentation. Rendered by
GitHub-flavored markdown (and any markdown viewer); each is fully
self-contained — inline styles, system font stacks, no scripts, no external
resources — so it renders identically through GitHub's camo proxy.

## Conventions

- **Every embed keeps a text version.** Wherever a diagram replaced an ASCII
  original, the markdown keeps a collapsed `<details><summary>Text version…`
  block beside the image, tagged ```` ```text ````. Vera's documentation is
  consumed by LLMs (`docs/llms-full.txt`, agents reading files in a terminal)
  — images are invisible to them, so the information must survive in text.
  When a diagram and its text version disagree, that is a bug; fix both.
- **No live counts.** Test totals, module counts, and issue lists drift and
  are policed by `scripts/check_doc_counts.py`, which cannot see inside an
  SVG. The one deliberate exception is `history-growth.svg`, which charts the
  *historical* release columns recorded in `HISTORY.md` §By the numbers and
  says so on its face.
- **Truthfulness beats the source it replaced.** `architecture.svg` draws the
  check → {verify | compile} fork because `vera compile` does not consume
  verify results and contract guards are always emitted — the linear ASCII it
  replaced implied otherwise (the same drift tracked for the spec in
  [#958](https://github.com/aallan/vera/issues/958)). No diagram may claim
  Tier-1 contracts are omitted from compiled output.
- **Accessibility:** every SVG carries a `<title>` (read by screen readers
  and used as hover text) that states the diagram's full claim in a sentence.
- **All embeds use repo-relative paths**, including `README.md`'s — they
  render from whatever ref is being viewed (branch, PR, merged main).
  Latent constraint: `pyproject.toml` declares `readme = "README.md"`, so
  if the package is ever *published* to PyPI, `README.md`'s embeds must
  switch to absolute raw URLs at that point — PyPI's renderer does not
  resolve repo-relative image paths. Not applicable while installation is
  `git clone` + `pip install -e .`.

## Design system

Derived from the house app style (warm-neutral cards):

| Token | Value |
|---|---|
| Panel | `#faf9f7`, border `#e8e6e1` @ 1.5px, radius 14 — opaque, so it reads on GitHub light *and* dark |
| Card | `#ffffff`, border `#e8e6e1` @ 1px, radius 10, 4px colored left-accent |
| Text | `#2d2b28` primary · `#7a756d` secondary · `#a9a49b` tertiary/micro-labels |
| Fonts | system stack (`-apple-system, BlinkMacSystemFont, 'Segoe UI', system-ui, sans-serif`); `'SF Mono', Menlo, Monaco, Consolas` for code/file names |
| Micro-labels | 10.5px, 600 weight, 1.5px letter-spacing, uppercase, tertiary |
| Edges | `#a9a49b` @ 1.5px, shared arrowhead marker; dashed = optional/alternative |

Category palette (consistent across every diagram):

| Category | Color | Tint (over white) |
|---|---|---|
| Frontend — parse · transform · resolve | `#4a82a8` | `#e4ecf2` |
| Type checking | `#8b6cad` | `#ede8f2` |
| Verification — Z3, tiers, obligations | `#d4952a` | `#f8efdf` |
| Code generation — codegen/ · wasm/ | `#5a9e6f` | `#e6f0e9` |
| Runtimes & hosts | `#cc9966` | `#f7efe8` |
| Failure / violated | `#c45` | — |

Canvas is 920 wide (GitHub's content column scales it to ~830px); heights
vary. Editing: these are plain XML — keep the class-based `<style>` block,
reuse the arrow marker, and update the `<title>` and any paired
`<details>` text version in the same commit.

## Inventory

| File | Embedded in | Depicts |
|---|---|---|
| `architecture.svg` | `vera/README.md`, `README.md` | full pipeline + module map, verify/compile fork, warm-verification sidecar, three targets |
| `workflow.svg` | `README.md` | the agent loop: write → check/verify → diagnostics feed back → run |
| `pipeline.svg` | `spec/11` | five compile stages and their artifacts |
| `tiers.svg` | `spec/06` | three-tier verification decision flow |
| `effect-handlers.svg` | `spec/07` | handler suspend/resume sequence |
| `wasmtime-embedding.svg` | `spec/12` | Engine → Module → Linker → Store → call chain |
| `memory-layout.svg` | `spec/12` | linear-memory segments + allocation header |
| `gc-cycle.svg` | `spec/12` | `$alloc` decision flow + mark-sweep phases |
| `wasi-component.svg` | `spec/13` | component wrapping `$Main`/`$Adapter` + dispatch table |
| `checker-passes.svg` | `vera/README.md` | the three checker passes over the TypeEnv |
| `z3-refutation.svg` | `vera/README.md` | contract → assert ¬goal → unsat/sat/unknown |
| `slot-scopes.svg` | `vera/README.md`, `DE_BRUIJN.md` | scope stack + backwards index resolution |
| `slot-numbering.svg` | `DE_BRUIJN.md` | per-type right-to-left numbering |
| `diagnostic-card.svg` | `vera/README.md` | the eight Diagnostic fields |
| `toolchain.svg` | `TOOLCHAIN.md` | CLI commands mapped onto pipeline stages |
| `testing-layers.svg` | `TESTING.md` | three test layers + four conformance levels |
| `lsp-session.svg` | `LSP_SERVER.md` | the agent proof-delta session |
| `history-growth.svg` | `HISTORY.md` | growth across the nine landmark releases |
| `subtyping-lattice.svg` | `spec/02` | the complete subtyping relation + the checker/verifier Nat split |
| `effect-row-lattice.svg` | `spec/07` | effect subtyping by row inclusion |
| `module-resolution.svg` | `spec/08` | path mapping, cache, cycle rejection, transitive-≠-visible |
| `async-model.svg` | `spec/09` | eager vs concurrent futures, the commutative-row gate |
| `httpserver-lifecycle.svg` | `spec/09` | the vera serve request lifecycle, fresh instance per request |
| `closure-layout.svg` | `spec/11` | closure heap struct + call_indirect dispatch |
| `browser-bindings.svg` | `spec/12` | dynamic import introspection in the browser runtime |
| `wasi-arena.svg` | `spec/13` | the GC-exempt cabi_realloc arena |
| `server-world.svg` | `spec/13` | the wasi:http incoming-handler adapter sequence |
| `faq-layers.svg` | `FAQ.md` | the three verification layers (types / Z3 / intent) |
| `contract-testing.svg` | `FAQ.md` | the vera test generate–execute–check loop |
| `language-comparison.svg` | `FAQ.md` | Dafny / Lean 4 / Koka / F* / Vera feature matrix |
| `ci-gates.svg` | `CONTRIBUTING.md` | commit-stage, push-stage and CI gate rings |
| `slot-evolution.svg` | `DE_BRUIJN.md` | the binding stack statement by statement |
| `host-families.svg` | `vera/README.md` | family adapters into the Linker; IO inline by design |
