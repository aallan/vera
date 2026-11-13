# assets/diagrams: the documentation diagram set

Hand-authored SVG diagrams embedded across the documentation. GitHub-flavoured
markdown renders them, as does any markdown viewer. Each is self-contained
(inline styles, system font stacks, no scripts, no external resources), so it
renders the same through GitHub's camo proxy.

## Conventions

- **Text versions.** An embed whose information appears nowhere else in the
  text keeps a collapsed `<details><summary>Text version…` block beside the
  image, tagged ```` ```text ````. Vera's documentation is read by models
  (`docs/llms-full.txt`, agents reading files in a terminal), and images are
  invisible to them, so the information has to survive as text. When a
  diagram and its text version disagree, that is a bug; fix both.
- **No live counts.** Test totals, module counts and issue lists drift. The
  one place they live is TESTING.md's generated status, which
  `scripts/render_status.py` writes, and nothing can write inside an SVG. The
  one exception is `history-growth.svg`, which charts the historical release
  columns in `HISTORY.md` §By the numbers and says so on its face.
- **The compile path keeps its guards.** `architecture.svg` draws the
  check → {verify | compile} fork because `vera compile` does not consume
  verify results: a contract's guard is emitted whether or not the contract
  was proved (spec §11.8). A clause no check can express, such as an
  `ensures` on a function that returns a `String` or an `Array`, has no
  guard; where the verifier does not prove it either, `vera verify`
  discloses it (`E543`).
  No diagram may claim Tier 1
  contracts are omitted from compiled output.
- **Accessibility.** Every SVG has a `<title>` (read by screen readers and
  used as hover text) that states the diagram's full claim in a sentence.
- **All embeds use repo-relative paths**, `README.md`'s included, so they
  render from whatever ref is being viewed (branch, pull request, `main`).
  The PyPI page for `veralang` renders `PYPI_README.md` (`pyproject.toml`
  declares `readme = "PYPI_README.md"`), which embeds no diagrams; an image
  added there must use an absolute URL, because PyPI's renderer does not
  resolve repo-relative paths.

## Design system

Derived from the house app style (warm-neutral cards):

| Token | Value |
|---|---|
| Panel | `#faf9f7`, border `#e8e6e1` @ 1.5px, radius 14; opaque, so it reads on GitHub's light and dark themes |
| Card | `#ffffff`, border `#e8e6e1` @ 1px, radius 10, 4px coloured left accent |
| Text | `#2d2b28` primary · `#7a756d` secondary · `#a9a49b` tertiary/micro-labels |
| Fonts | system stack (`-apple-system, BlinkMacSystemFont, 'Segoe UI', system-ui, sans-serif`); `'SF Mono', Menlo, Monaco, Consolas` for code/file names |
| Micro-labels | 10.5px, 600 weight, 1.5px letter-spacing, uppercase, tertiary |
| Edges | `#a9a49b` @ 1.5px, shared arrowhead marker; dashed = optional/alternative |

Every diagram uses the same category palette:

| Category | Colour | Tint (over white) |
|---|---|---|
| Frontend: parse · transform · resolve | `#4a82a8` | `#e4ecf2` |
| Type checking | `#8b6cad` | `#ede8f2` |
| Verification: Z3, tiers, obligations | `#d4952a` | `#f8efdf` |
| Code generation: codegen/ · wasm/ | `#5a9e6f` | `#e6f0e9` |
| Runtimes & hosts | `#cc9966` | `#f7efe8` |
| Failure / violated | `#c45` | none |

The canvas is 920 wide (GitHub's content column scales it to about 830px),
and heights vary. The files are plain XML. When editing one, keep the
class-based `<style>` block, reuse the arrow marker, and update the `<title>`
and any paired `<details>` text version in the same commit.

## Inventory

| File | Embedded in | Depicts |
|---|---|---|
| `architecture.svg` | `vera/README.md`, `README.md` | full pipeline + module map: resolve binding every call, one typed program with its instances and obligation sites; the verify/compile fork, verify's reconciliation with the compiled module, the warm-verification sidecar, three targets, the one-renderer note for `naming.py` |
| `workflow.svg` | `README.md` | the agent loop: write → check/verify (prove, check at run time, or diagnose) → diagnostics feed back → run on the command line, in the browser, as a WASI component or behind HTTP |
| `pipeline.svg` | `spec/11` | parse, transform, resolve (calls bound), check and the typed program; then verify and compile, compile not reading the verifier's result |
| `tiers.svg` | `spec/06`, `DESIGN.md` | the tier decision flow: Tier 1, a counterexample error, a Tier 3 runtime check or a disclosed warning; Tier 2 shown as specified but not implemented |
| `effect-handlers.svg` | `spec/07` | handler suspend/resume sequence, traced through `get(())` under `handle[State<Int>]` |
| `wasmtime-embedding.svg` | `spec/12` | Engine → Module → Linker → Store → call chain, which `execute()` wraps for `vera run`, `vera test` and `vera serve` |
| `memory-layout.svg` | `spec/12` | linear-memory segments + allocation header |
| `gc-cycle.svg` | `spec/12` | `$alloc` decision flow + mark-sweep phases, with the object-base record and the rescan after a dropped push |
| `wasi-component.svg` | `spec/13` | component wrapping `$Main`/`$Adapter` + dispatch table |
| `checker-passes.svg` | `vera/README.md` | the three checker passes over the TypeEnv, with `binding.py` binding every call between passes 1 and 2 |
| `z3-refutation.svg` | `vera/README.md` | contract → assert ¬goal → unsat/sat/unknown |
| `slot-scopes.svg` | `vera/README.md` | scope stack + backwards index resolution |
| `slot-numbering.svg` | `DE_BRUIJN.md` | per-type right-to-left numbering |
| `diagnostic-card.svg` | `vera/README.md` | the eight Diagnostic fields, the optional `tier`, and the gate on an error's fields |
| `toolchain.svg` | `TOOLCHAIN.md` | CLI commands mapped onto pipeline stages; `verify` compiles to reconcile, `compile`, `run` and `serve` skip verification |
| `testing-layers.svg` | `TESTING.md` | three test layers + four conformance levels |
| `lsp-session.svg` | `LSP_SERVER.md` | the agent proof-delta session |
| `history-growth.svg` | `HISTORY.md` | growth across the ten landmark releases |
| `subtyping-lattice.svg` | `spec/02` | the complete subtyping relation, the variance of compound types, and the checker/verifier Nat split |
| `effect-row-lattice.svg` | `spec/07`, `DESIGN.md` | effect subtyping by row inclusion |
| `module-resolution.svg` | `spec/08` | path mapping, cache, cycle rejection, transitive-≠-visible |
| `async-model.svg` | `spec/09` | eager vs concurrent futures, the commutative-row gate, and the fused `Http` shape the reference implementation runs concurrently |
| `httpserver-lifecycle.svg` | `spec/09` | the `vera serve` request lifecycle: a fresh instance per request, the handler's contract checks run on each |
| `closure-layout.svg` | `spec/11` | closure heap struct + call_indirect dispatch |
| `browser-bindings.svg` | `spec/12` | dynamic import introspection in the browser runtime |
| `wasi-arena.svg` | `spec/13` | the GC-exempt cabi_realloc arena |
| `server-world.svg` | `spec/13` | the wasi:http incoming-handler adapter sequence |
| `faq-layers.svg` | `FAQ.md` | the three verification layers (types / Z3 / intent) |
| `contract-testing.svg` | `FAQ.md` | the `vera test` loop over the functions the verifier did not prove: generate, compile once, execute, check |
| `language-comparison.svg` | `FAQ.md` | Dafny / Lean 4 / Koka / F* / Vera feature matrix |
| `ci-gates.svg` | `CONTRIBUTING.md` | commit-stage, push-stage and CI gate rings, CI's shards and sampled matrices |
| `slot-evolution.svg` | `DE_BRUIJN.md` | the binding stack statement by statement |
| `host-families.svg` | `vera/README.md` | one adapter module per host-import family into the Linker; IO inline by design; `Map` and `Set` need none |
