# Roadmap

Development follows an **interleaved spiral** — each phase adds a complete compiler layer with tests, docs, and working examples before moving to the next. The core language and compiler are complete through v0.0.89. What remains is standard library, effects, and ecosystem — the gap between a working language and a viable agent target.

| Phase | Version | Layer | Status |
|-------|---------|-------|--------|
| C1 | [v0.0.1](https://github.com/aallan/vera/releases/tag/v0.0.1)–[v0.0.3](https://github.com/aallan/vera/releases/tag/v0.0.3) | **Parser** — Lark LALR(1) grammar, LLM diagnostics, 13 examples | Done |
| C2 | [v0.0.4](https://github.com/aallan/vera/releases/tag/v0.0.4) | **AST** — typed syntax tree, Lark→AST transformer | Done |
| C3 | [v0.0.5](https://github.com/aallan/vera/releases/tag/v0.0.5) | **Type checker** — decidable type checking, slot resolution, effect tracking | Done |
| C4 | [v0.0.8](https://github.com/aallan/vera/releases/tag/v0.0.8) | **Contract verifier** — Z3 integration, refinement types, counterexamples | Done |
| C5 | [v0.0.9](https://github.com/aallan/vera/releases/tag/v0.0.9) | **WASM codegen** — compile to WebAssembly, `vera compile` / `vera run` | Done |
| C6 | [v0.0.10](https://github.com/aallan/vera/releases/tag/v0.0.10)–[v0.0.24](https://github.com/aallan/vera/releases/tag/v0.0.24) | **Codegen completeness** — ADTs, match, closures, effects, generics in WASM | Done |
| C6.5 | [v0.0.25](https://github.com/aallan/vera/releases/tag/v0.0.25)–[v0.0.30](https://github.com/aallan/vera/releases/tag/v0.0.30) | **Codegen cleanup** — handler fixes, missing operators, String/Array support | Done |
| C7 | [v0.0.31](https://github.com/aallan/vera/releases/tag/v0.0.31)–[v0.0.39](https://github.com/aallan/vera/releases/tag/v0.0.39) | **Module system** — cross-file imports, visibility, multi-module compilation | Done |
| C8 | [v0.0.40](https://github.com/aallan/vera/releases/tag/v0.0.40)–[v0.0.65](https://github.com/aallan/vera/releases/tag/v0.0.65) | **Polish** — refactoring, tooling, diagnostics, verification depth, codegen gaps | Done |
| C8.5 | [v0.0.66](https://github.com/aallan/vera/releases/tag/v0.0.66)–[v0.0.88](https://github.com/aallan/vera/releases/tag/v0.0.88) | **Completeness** — builtins, IO runtime, types, effects, browser target | Done |

## Where we are

**v0.0.89** delivers a full compiler pipeline (parse → typecheck → verify → compile → run), 68 built-in functions plus 5 Option/Result combinators, a module system, algebraic effect handlers, a 54-program conformance suite, a canonical formatter, and contract-driven testing. An independent viability assessment rates Vera at **60–70% of the way to being a viable agent target**. The gap is standard library and data-format support, not the core language or verification system.

Most remaining features are gated by a single dependency chain:

**Abilities ([#60](https://github.com/aallan/vera/issues/60)) → Map ([#62](https://github.com/aallan/vera/issues/62)) → JSON ([#58](https://github.com/aallan/vera/issues/58)) → HTTP ([#57](https://github.com/aallan/vera/issues/57))**

Abilities introduce type constraints (`Eq`, `Hash`, `Show`). Map needs abilities for key constraints. JSON needs Map for `JObject`. HTTP needs JSON for request/response bodies. Unblocking abilities unblocks the entire chain.

## What's next

```
Tier 0 (unblocked)          Tier 1 (sequential)               Tier 2 (interleave)
─────────────────           ──────────────────                ──────────────────
✓ #211 Combinators          #60 Abilities ─┐                  #289 Prelude
#133 Array slice            #133 map/fold ←┘─┐                #226 Typed holes
#288 Naming audit                #62 Map ←───┘─┐              #233 DateTime
                                 #58 JSON ←────┘─┐            #235 Crypto
                                 #57 HTTP ←──────┘            #61 Inference
```

### Tier 0 — Ship now

No blocking dependencies. Highest value-per-effort.

- <del>[#211](https://github.com/aallan/vera/issues/211) **Option/Result combinators** — pure Vera functions, no compiler changes. Eliminates 5-line match blocks for every fallible operation. Fundamental enough for a standard prelude.</del> ([v0.0.89](https://github.com/aallan/vera/releases/tag/v0.0.89))
- [#133](https://github.com/aallan/vera/issues/133) **Array `slice`** — the `slice` operation has no abilities dependency and can ship independently of `map`/`fold`/`filter`. Unblocks basic array manipulation.
- [#288](https://github.com/aallan/vera/issues/288) **Built-in function naming audit** — four naming patterns where there should be one or two. Must happen before new functions ship to establish the convention they follow. Breaking change — do it early.

### Tier 1 — Critical path

The chain that unlocks agent-viable data processing. Each item depends on the previous.

1. [#60](https://github.com/aallan/vera/issues/60) **Abilities and type constraints** — highest-leverage foundation work. Every item below is transitively blocked by this. The viability assessment's "60–70%" verdict is largely gated here. ([PR #297](https://github.com/aallan/vera/pull/297), [PR #298](https://github.com/aallan/vera/pull/298))
2. [#133](https://github.com/aallan/vera/issues/133) **Array `map`/`fold`/`filter`** (remainder) — requires abilities for generic iteration. The iteration verbosity tax — 12-line recursive loop vs 1-line `map`, multiplied across every data transformation — is the single biggest usability gap for agent workloads.
3. [#62](https://github.com/aallan/vera/issues/62) **Map and Set collections** — requires abilities for key constraints (`Eq + Hash`). Unlocks structured data handling.
4. [#58](https://github.com/aallan/vera/issues/58) **JSON type** — requires Map for `JObject`. Without JSON parsing and serialisation, Vera cannot participate in any API integration workflow.
5. [#57](https://github.com/aallan/vera/issues/57) **HTTP effect** — requires JSON for request/response bodies. Completes the chain: a Vera program can make an HTTP call, parse the JSON response, and return typed, verified data.

### Tier 2 — Interleave as opportunities arise

Independent of the Tier 1 chain. Can be scheduled between Tier 1 items or in parallel.

- [#289](https://github.com/aallan/vera/issues/289) **Standard prelude** — eliminates 2–6 lines of identical boilerplate in every program that uses `Result` or `Option`
- [#226](https://github.com/aallan/vera/issues/226) **Typed holes** — partial program generation; type context at hole sites improves LLM completion quality
- [#233](https://github.com/aallan/vera/issues/233) **Date and time** (ISO 8601) — agent workloads frequently need timestamps
- [#235](https://github.com/aallan/vera/issues/235) **Cryptographic hashing** (SHA-256, HMAC) — needed for API authentication (webhook signatures, OAuth)
- [#61](https://github.com/aallan/vera/issues/61) **Inference effect** — `effects(<Inference>)` in a signature means "this function calls an LLM, and you can mock it for testing." The feature that most differentiates Vera from Dafny as a verification target, and the one that positions it as the natural language for verified LLM orchestration.

### Remaining completeness

Items from the original compiler phases not yet done:

- [#187](https://github.com/aallan/vera/issues/187) → [#127](https://github.com/aallan/vera/issues/127) Module-qualified call disambiguation → module re-exports (sequential dependency)
- [#263](https://github.com/aallan/vera/issues/263) CLI argument passing: strings, floats, typed dispatch
- [#169](https://github.com/aallan/vera/issues/169) → [#170](https://github.com/aallan/vera/issues/170) `vera test` Float64/compound input generation → hypothesis integration (sequential)

### Tooling and ecosystem

Lower priority than data-format support but important for adoption.

- [#222](https://github.com/aallan/vera/issues/222) **LSP server** — the standard integration protocol for production coding agents (Claude Code, Cursor, Copilot, Windsurf); the existing `--json` infrastructure is a solid foundation to build on
- [#224](https://github.com/aallan/vera/issues/224) REPL
- [#225](https://github.com/aallan/vera/issues/225) **Benchmark suite** — a HumanEval/MBPP-style benchmark adapted for Vera would quantify LLM code generation progress and attract research attention. DafnyBench demonstrated that verification success rates can improve from 68% to 96% over one year of tracking.
- [#56](https://github.com/aallan/vera/issues/56) Incremental compilation
- [#237](https://github.com/aallan/vera/issues/237) WASI 0.2 compliance
- [#238](https://github.com/aallan/vera/issues/238) Component Model (WIT) interop
- [#239](https://github.com/aallan/vera/issues/239) Resource limit configuration (fuel, memory, timeout)
- [#163](https://github.com/aallan/vera/issues/163) Standalone WASM runtime package
- [#130](https://github.com/aallan/vera/issues/130) Package system and registry
- [#143](https://github.com/aallan/vera/issues/143) Comprehensive example programs
- [#181](https://github.com/aallan/vera/issues/181) Signature refactoring (mechanical slot index rewriting)
- [#183](https://github.com/aallan/vera/issues/183) Human-readable slot annotations

### Additional effects

Future effect types for extended agent workloads:

- [#227](https://github.com/aallan/vera/issues/227) `<Timeout>` — timeout and cancellation
- [#228](https://github.com/aallan/vera/issues/228) `<WebSocket>` / `<SSE>` — streaming clients
- [#229](https://github.com/aallan/vera/issues/229) `<DB>` — database access
- [#236](https://github.com/aallan/vera/issues/236) CSV parsing and generation
- [#270](https://github.com/aallan/vera/issues/270) `handle[Async]` — custom scheduling strategies

---

## Completed phases

<details>
<summary>C6 — Codegen Completeness (<a href="https://github.com/aallan/vera/releases/tag/v0.0.10">v0.0.10</a>–<a href="https://github.com/aallan/vera/releases/tag/v0.0.24">v0.0.24</a>) ✓</summary>

C6 extended WASM compilation to all language constructs, working through the dependency graph from simplest to most complex. All 15 examples now compile.

| Sub-phase | Scope | Version |
|-----------|-------|---------|
| C6a | Float64 — `f64` literals, arithmetic, comparisons | [v0.0.10](https://github.com/aallan/vera/releases/tag/v0.0.10) |
| C6b | Callee preconditions — verify `requires()` at call sites | [v0.0.11](https://github.com/aallan/vera/releases/tag/v0.0.11) |
| C6c | Match exhaustiveness — verify all constructors covered | [v0.0.12](https://github.com/aallan/vera/releases/tag/v0.0.12) |
| C6d | State\<T\> operations — get/put as host imports | [v0.0.13](https://github.com/aallan/vera/releases/tag/v0.0.13) |
| C6e | Bump allocator — heap allocation for tagged values | [v0.0.14](https://github.com/aallan/vera/releases/tag/v0.0.14) |
| C6f | ADT constructors — heap-allocated tagged unions | [v0.0.15](https://github.com/aallan/vera/releases/tag/v0.0.15) |
| C6g | Match expressions — tag dispatch, field extraction | [v0.0.16](https://github.com/aallan/vera/releases/tag/v0.0.16) |
| C6h | Closures — closure conversion, `call_indirect` | [v0.0.18](https://github.com/aallan/vera/releases/tag/v0.0.18) |
| C6i | Generics — monomorphization of `forall<T>` functions | [v0.0.17](https://github.com/aallan/vera/releases/tag/v0.0.17) |
| C6j | Effect handlers — handle/resume compilation | [v0.0.19](https://github.com/aallan/vera/releases/tag/v0.0.19) |
| C6k | Byte + arrays — linear memory arrays with bounds | [v0.0.21](https://github.com/aallan/vera/releases/tag/v0.0.21) |
| C6l | Quantifiers — forall/exists as runtime loops | [v0.0.22](https://github.com/aallan/vera/releases/tag/v0.0.22) |
| C6m | Refinement type alias compilation | [v0.0.23](https://github.com/aallan/vera/releases/tag/v0.0.23) |
| C6n | Spec chapters 9 (Standard library) and 12 (Runtime) | [v0.0.24](https://github.com/aallan/vera/releases/tag/v0.0.24) |

</details>

<details>
<summary>C6.5 — Codegen & Checker Cleanup (<a href="https://github.com/aallan/vera/releases/tag/v0.0.25">v0.0.25</a>–<a href="https://github.com/aallan/vera/releases/tag/v0.0.30">v0.0.30</a>) ✓</summary>

Before starting the module system, C6.5 addressed residual gaps in single-file compilation — handler bugs, missing operators, and type support limits. Each sub-phase closed a tracked issue.

| Sub-phase | Scope | Version |
|-----------|-------|---------|
| C6.5a | `resume` not recognized as built-in in handler scope | [v0.0.25](https://github.com/aallan/vera/releases/tag/v0.0.25) |
| C6.5b | Handler `with` clause for state updates not in grammar | [v0.0.26](https://github.com/aallan/vera/releases/tag/v0.0.26) |
| C6.5c | Pipe operator (`\|>`) compilation | [v0.0.27](https://github.com/aallan/vera/releases/tag/v0.0.27) |
| C6.5d | Float64 modulo (`%`) — WASM has no `f64.rem` | [v0.0.28](https://github.com/aallan/vera/releases/tag/v0.0.28) |
| C6.5e | String and Array types in function signatures | [v0.0.29](https://github.com/aallan/vera/releases/tag/v0.0.29) |
| C6.5f | `old()`/`new()` state expressions in contracts | [v0.0.30](https://github.com/aallan/vera/releases/tag/v0.0.30) |

</details>

<details>
<summary>C7 — Module System (<a href="https://github.com/aallan/vera/releases/tag/v0.0.31">v0.0.31</a>–<a href="https://github.com/aallan/vera/releases/tag/v0.0.39">v0.0.39</a>) ✓</summary>

C7 implemented the full module system: file-based resolution, cross-module type checking with visibility enforcement, cross-module contract verification, and multi-module WASM compilation using a flattening strategy. Spec Chapter 8 (Modules) documents the formal semantics.

| Sub-phase | Scope | Version |
|-----------|-------|---------|
| C7a | Module resolution — map `import` paths to source files and parse them | [v0.0.31](https://github.com/aallan/vera/releases/tag/v0.0.31) |
| C7b | Cross-module type environment — merge public declarations across files | [v0.0.32](https://github.com/aallan/vera/releases/tag/v0.0.32) |
| C7c | Visibility enforcement — `public`/`private` access control in the checker | [v0.0.34](https://github.com/aallan/vera/releases/tag/v0.0.34)–[v0.0.35](https://github.com/aallan/vera/releases/tag/v0.0.35) |
| C7d | Cross-module verification — verify contracts that reference imported symbols | [v0.0.37](https://github.com/aallan/vera/releases/tag/v0.0.37) |
| C7e | Multi-module codegen — flatten imported functions into the WASM module | [v0.0.38](https://github.com/aallan/vera/releases/tag/v0.0.38) |
| C7f | Spec Chapter 8 — formal module semantics, resolution algorithm, examples | [v0.0.39](https://github.com/aallan/vera/releases/tag/v0.0.39) |

</details>

<details>
<summary>C8 — Polish (<a href="https://github.com/aallan/vera/releases/tag/v0.0.40">v0.0.40</a>–<a href="https://github.com/aallan/vera/releases/tag/v0.0.65">v0.0.65</a>) ✓</summary>

C8 addressed accumulated technical debt and UX gaps before v0.1.0. Issues were grouped into sub-phases ordered by impact and dependency.

**C8a — Refactoring** — reduce file sizes to improve maintainability

- <del>[#99](https://github.com/aallan/vera/issues/99) decompose `checker.py` (~1,900 lines) into `checker/` submodules</del> ([v0.0.40](https://github.com/aallan/vera/releases/tag/v0.0.40))
- <del>[#100](https://github.com/aallan/vera/issues/100) decompose `wasm.py` (~2,300 lines) into `wasm/` submodules</del> ([v0.0.41](https://github.com/aallan/vera/releases/tag/v0.0.41))
- <del>[#155](https://github.com/aallan/vera/issues/155) decompose `codegen.py` (~2,140 lines) into `codegen/` submodules</del> ([v0.0.46](https://github.com/aallan/vera/releases/tag/v0.0.46))

**C8b — Diagnostics and tooling** — improve the developer (human and LLM) experience

- <del>[#112](https://github.com/aallan/vera/issues/112) informative runtime contract violation error messages</del> ([v0.0.42](https://github.com/aallan/vera/releases/tag/v0.0.42))
- <del>[#80](https://github.com/aallan/vera/issues/80) stable error code taxonomy for diagnostics</del> ([v0.0.43](https://github.com/aallan/vera/releases/tag/v0.0.43))
- <del>[#95](https://github.com/aallan/vera/issues/95) LALR grammar fix for module-qualified call syntax</del> ([v0.0.44](https://github.com/aallan/vera/releases/tag/v0.0.44))
- <del>[#75](https://github.com/aallan/vera/issues/75) `vera fmt` canonical formatter</del> ([v0.0.45](https://github.com/aallan/vera/releases/tag/v0.0.45))
- <del>[#79](https://github.com/aallan/vera/issues/79) `vera test` contract-driven testing</del> ([v0.0.47](https://github.com/aallan/vera/releases/tag/v0.0.47))
- <del>[#156](https://github.com/aallan/vera/issues/156) improve test coverage for WASM translation modules</del> ([v0.0.48](https://github.com/aallan/vera/releases/tag/v0.0.48))

**C8c — Verification depth** — expand what the SMT solver can prove

- <del>[#136](https://github.com/aallan/vera/issues/136) register `Diverge` as built-in effect</del> ([v0.0.49](https://github.com/aallan/vera/releases/tag/v0.0.49))
- <del>[#13](https://github.com/aallan/vera/issues/13) expand SMT decidable fragment (Tier 2 verification)</del> ([v0.0.51](https://github.com/aallan/vera/releases/tag/v0.0.51))
- <del>[#45](https://github.com/aallan/vera/issues/45) `decreases` clause termination verification</del> ([v0.0.52](https://github.com/aallan/vera/releases/tag/v0.0.52))

**C8d — Type system** — close type-checking gaps

- <del>[#20](https://github.com/aallan/vera/issues/20) TypeVar subtyping</del> ([v0.0.53](https://github.com/aallan/vera/releases/tag/v0.0.53))
- <del>[#21](https://github.com/aallan/vera/issues/21) effect row unification and subeffecting</del> ([v0.0.54](https://github.com/aallan/vera/releases/tag/v0.0.54))
- <del>[#55](https://github.com/aallan/vera/issues/55) minimal type inference</del> ([v0.0.55](https://github.com/aallan/vera/releases/tag/v0.0.55))

**C8e — Codegen gaps** — extend WASM compilation

- <del>[#154](https://github.com/aallan/vera/issues/154) `list_ops.vera` runtime failure — recursive generic ADT codegen</del> ([v0.0.58](https://github.com/aallan/vera/releases/tag/v0.0.58))
- <del>[#110](https://github.com/aallan/vera/issues/110) name collision detection for flat module compilation</del> ([v0.0.57](https://github.com/aallan/vera/releases/tag/v0.0.57))
- <del>[#131](https://github.com/aallan/vera/issues/131) nested constructor pattern codegen</del> ([v0.0.56](https://github.com/aallan/vera/releases/tag/v0.0.56))
- <del>[#53](https://github.com/aallan/vera/issues/53) `Exn<E>` and custom effect handler compilation</del> ([v0.0.62](https://github.com/aallan/vera/releases/tag/v0.0.62))
- <del>[#51](https://github.com/aallan/vera/issues/51) garbage collection for WASM linear memory</del> ([v0.0.65](https://github.com/aallan/vera/releases/tag/v0.0.65))
- <del>[#132](https://github.com/aallan/vera/issues/132) arrays of compound types in codegen</del> ([v0.0.61](https://github.com/aallan/vera/releases/tag/v0.0.61))
- <del>[#52](https://github.com/aallan/vera/issues/52) dynamic string construction</del> ([v0.0.63](https://github.com/aallan/vera/releases/tag/v0.0.63))
- <del>[#134](https://github.com/aallan/vera/issues/134) string built-in operations (length, concat, slice)</del> ([v0.0.50](https://github.com/aallan/vera/releases/tag/v0.0.50))
- <del>[#174](https://github.com/aallan/vera/issues/174) `parse_nat` should return `Result<Nat, String>` per spec</del> ([v0.0.60](https://github.com/aallan/vera/releases/tag/v0.0.60))
- <del>[#106](https://github.com/aallan/vera/issues/106) universal to-string conversion (Show/Display)</del> ([v0.0.64](https://github.com/aallan/vera/releases/tag/v0.0.64))

</details>

<details>
<summary>C8.5 — Completeness (<a href="https://github.com/aallan/vera/releases/tag/v0.0.66">v0.0.66</a>–<a href="https://github.com/aallan/vera/releases/tag/v0.0.88">v0.0.88</a>) ✓</summary>

C8.5 built out the standard library, IO runtime, and remaining type/effect support — completing the existing language before new features.

**IO runtime** — host bindings for file and stdin access

- <del>[#135](https://github.com/aallan/vera/issues/135) IO operations (read_line, read_file, write_file, args, exit, get_env)</del> ([v0.0.66](https://github.com/aallan/vera/releases/tag/v0.0.66))
- <del>[#216](https://github.com/aallan/vera/issues/216) string escape sequences (\n, \t, etc.) not parsed in string literals</del> ([v0.0.67](https://github.com/aallan/vera/releases/tag/v0.0.67))

**Builtin extensions** — standard library functions

- <del>[#199](https://github.com/aallan/vera/issues/199) numeric math builtins</del> ([v0.0.70](https://github.com/aallan/vera/releases/tag/v0.0.70))
- <del>[#208](https://github.com/aallan/vera/issues/208) numeric type conversions</del> ([v0.0.71](https://github.com/aallan/vera/releases/tag/v0.0.71))
- <del>[#212](https://github.com/aallan/vera/issues/212) Float64 special value operations (is_nan, is_infinite)</del> ([v0.0.72](https://github.com/aallan/vera/releases/tag/v0.0.72))
- <del>[#198](https://github.com/aallan/vera/issues/198) string search and transformation builtins</del> ([v0.0.73](https://github.com/aallan/vera/releases/tag/v0.0.73))
- <del>[#210](https://github.com/aallan/vera/issues/210) from_char_code builtin</del> ([v0.0.74](https://github.com/aallan/vera/releases/tag/v0.0.74))
- <del>[#213](https://github.com/aallan/vera/issues/213) string_repeat builtin</del> ([v0.0.75](https://github.com/aallan/vera/releases/tag/v0.0.75))
- <del>[#230](https://github.com/aallan/vera/issues/230) string interpolation</del> ([v0.0.76](https://github.com/aallan/vera/releases/tag/v0.0.76))
- <del>[#200](https://github.com/aallan/vera/issues/200) parsing completeness (parse_int, parse_bool, safe parse_float64)</del> ([v0.0.77](https://github.com/aallan/vera/releases/tag/v0.0.77))
- <del>[#209](https://github.com/aallan/vera/issues/209) array construction builtins (range, append, concat)</del> ([v0.0.78](https://github.com/aallan/vera/releases/tag/v0.0.78))
- <del>[#234](https://github.com/aallan/vera/issues/234) base64 encoding and decoding</del> ([v0.0.79](https://github.com/aallan/vera/releases/tag/v0.0.79))
- <del>[#232](https://github.com/aallan/vera/issues/232) URL parsing and construction builtins</del> ([v0.0.81](https://github.com/aallan/vera/releases/tag/v0.0.81))
- <del>[#231](https://github.com/aallan/vera/issues/231) regex support</del> ([v0.0.86](https://github.com/aallan/vera/releases/tag/v0.0.86))

**Types and effects** — new type and effect support

- <del>[#59](https://github.com/aallan/vera/issues/59) `<Async>` futures and promises</del> ([v0.0.82](https://github.com/aallan/vera/releases/tag/v0.0.82))
- <del>[#267](https://github.com/aallan/vera/issues/267) Tuple type WASM codegen</del> ([v0.0.83](https://github.com/aallan/vera/releases/tag/v0.0.83))
- <del>[#147](https://github.com/aallan/vera/issues/147) Markdown standard library type</del> ([v0.0.84](https://github.com/aallan/vera/releases/tag/v0.0.84))

**Tooling and runtime**

- <del>[#223](https://github.com/aallan/vera/issues/223) conformance test suite</del> ([v0.0.68](https://github.com/aallan/vera/releases/tag/v0.0.68))
- <del>[#273](https://github.com/aallan/vera/issues/273) browser runtime for compiled WASM (JS host bindings)</del> ([v0.0.85](https://github.com/aallan/vera/releases/tag/v0.0.85))

</details>
