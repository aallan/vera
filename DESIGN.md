# Design

Technical decisions, rationale, and prior art. For the design philosophy and FAQ, see [FAQ.md](FAQ.md). For the formal specification, see [spec/](spec/). For the compiler architecture, see [vera/README.md](vera/README.md).

---

## Design principles

1. **Checkability over correctness.** The model does not need to produce correct code on the first attempt — it needs to produce code that can be mechanically checked. When the code is wrong, the compiler provides a natural language explanation of the error with a concrete fix. The diagnostic is an instruction, not a status report.

2. **Explicitness over convenience.** All state changes are declared. All effects are typed. All function contracts are mandatory. There is no implicit behaviour for the model to infer or hallucinate.

3. **One canonical form.** Every construct has exactly one textual representation. No style choices, no optional syntax, no equivalent alternatives. The canonical formatter enforces this; `vera fmt --check` is a CI gate.

4. **Structural references over names.** Bindings are referenced by type and positional index (`@T.n`), not by arbitrary names. This eliminates naming consistency errors — one of the most common failure modes when models generate code across large contexts. See [`DE_BRUIJN.md`](DE_BRUIJN.md) for the academic background and empirical evidence.

5. **Contracts as the source of truth.** Every function declares what it requires (`requires`) and what it guarantees (`ensures`). The compiler verifies these statically where possible, inserts runtime checks where it cannot, and uses them as input generators for property-based testing. The contract is the specification.

6. **Constrained expressiveness.** The space of valid programs is deliberately small. Refinement types, mandatory contracts, and the effect system combine to reject large classes of incorrect programs at compile time. Fewer valid programs means fewer opportunities for the model to be wrong.

---

## Technical decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| References | [`@T.n` typed De Bruijn indices](DE_BRUIJN.md) | Eliminates naming coherence errors; indices are locally determinable from types alone |
| Contracts | Mandatory `requires`/`ensures`/`effects` on all functions | Programs must be checkable; contracts are the machine-verifiable specification |
| Verification | Three-tier: Z3 static → Z3 guided → runtime fallback | Maximises static guarantees; degrades gracefully where SMT is undecidable |
| Effects | Algebraic, row-polymorphic (`IO`, `Http`, `State`, `Exn`, `Async`, `Inference`) | All state and side effects explicit; effects are typed, trackable, and handleable |
| Error handling | `Result<T,E>` ADTs for expected errors; `Exn<T>` algebraic effect for exceptions | Errors are values; `match` enforces handling every case; `Exn<T>` is handleable like any other effect |
| Inference | `Inference.complete` as an algebraic effect | LLM calls are typed, contract-verifiable, mockable via `handle[Inference]`, and explicit in signatures |
| Data types | Algebraic data types + exhaustive `match` | No classes, no inheritance; compiler enforces every case is handled |
| Polymorphism | Monomorphized generics (`forall<T where Eq<T>>`) | No runtime dispatch; four built-in abilities (`Eq`, `Ord`, `Hash`, `Show`); types fully specialised at compile time |
| Refinement types | `{ @T \| predicate }` checked by Z3 | Encode value-level constraints in the type system; rejected statically or at runtime |
| Collections | `Array<T>`, `Map<K,V>`, `Set<T>` | Functional, immutable; no mutation, no loops; `array_map`/`filter`/`fold`/`slice` as built-ins |
| Standard library | 122 built-in functions | Strings, arrays, maps, sets, decimals, JSON, HTML, Markdown, regex, base64, URL — no external deps |
| Modules | `module`/`import` with explicit re-exports | Programs split across files; `vera check` resolves the module graph |
| Recursion | Explicit termination measures (`decreases`) | Compiler verifies termination via Z3; no unbounded loops |
| Evaluation | Strict (call-by-value) | Simpler for models to reason about; no lazy evaluation to track |
| Memory | Conservative mark-sweep GC in WASM | Implemented entirely in generated WASM (`$alloc`, `$gc_collect`, shadow stack); no host GC; models focus on logic |
| Target | WebAssembly (native + browser) | Portable, sandboxed, no ambient capabilities; `vera run` uses wasmtime; `vera compile --target browser` emits a JS bundle |
| Compiler | Python reference implementation | Correctness over performance; clean separation of phases; see [vera/README.md](vera/README.md) |
| Grammar | Machine-readable Lark EBNF (`grammar.lark`) | Formal grammar is shared between spec and implementation; no ambiguity |
| Diagnostics | LLM-instruction format; `--json` for machine use; stable error codes E001–E702 | Every diagnostic names the problem, explains why, and gives a concrete fix; codes are stable for tooling |
| Testing | Contract-driven via Z3 + WASM (`vera test`) | Z3 generates inputs that satisfy `requires`; compiled WASM executes; `ensures` is checked against real outputs |
| Formatting | Canonical formatter (`vera fmt`) | One canonical form, enforced by pre-commit and CI; no style drift |
| Representation | Text with rigid syntax | One canonical form, no parsing ambiguity, no equivalent alternatives |

---

## The verification pipeline

Vera's contracts are checked in three tiers, applied at every call site:

**Tier 1 — Z3 static (decidable fragment).** The compiler generates a verification condition and sends it to Z3. If Z3 returns `unsat`, the contract is proved for all inputs. This covers arithmetic, boolean logic, and simple refinement predicates.

**Tier 2 — Z3 guided (extended fragment).** The compiler adds hints from `assert` statements and lemma functions. Z3 has a 10-second timeout. Covers function calls, quantifiers, and array properties.

**Tier 3 — Runtime fallback.** If Z3 returns `unknown` or times out, the contract is compiled as a runtime check in the WASM binary. A violation raises a trap at the call site with the contract text.

`vera verify --json` reports the tier breakdown:
```json
{"verification": {"tier1_verified": 12, "tier3_runtime": 1, "total": 13}}
```

A fully Tier 1–verified program has the strongest guarantee: if it compiles and verifies, the contracts hold for all inputs. See [spec/06-contracts.md](spec/06-contracts.md) for the formal treatment.

---

## The effect system

Effects are declared in function signatures and checked at every call site. A function that calls `IO.print` must declare `effects(<IO>)`; a function that calls `Inference.complete` must declare `effects(<Inference>)`. Undeclared effects are a compile error.

Built-in effects:

| Effect | Operations | Notes |
|--------|-----------|-------|
| `IO` | `print`, `read_line`, file ops | Console and file I/O |
| `Http` | `get`, `post` | Network requests; returns `Result<String, String>` |
| `State<T>` | `get`, `put` | Typed mutable state; scope controlled by `handle[State<T>]` |
| `Exn<T>` | `throw`, `catch` | Typed exceptions; handleable like any algebraic effect |
| `Async` | `async`, `await` | `Future<T>` is zero-overhead at compile time; true concurrency deferred to WASI 0.3 |
| `Inference` | `complete` | LLM calls; `String → Result<String, String>`; provider selected by env var |

User-defined effects follow the same pattern. Effects compose in rows: `effects(<IO, Http>)`, `effects(<Inference, IO>)`.

`handle[EffectName]` blocks intercept operations, enabling mocking, logging, and local state. See [spec/07-effects.md](spec/07-effects.md).

---

## Prior art

Vera draws on ideas from several existing languages and systems (see also [spec/00-introduction.md §0.4](spec/00-introduction.md#04-prior-art)):

- [Eiffel](https://www.eiffel.org/) — the originator of Design by Contract; `require`/`ensure` as first-class language constructs
- [Dafny](https://dafny.org/) — full functional verification with preconditions, postconditions, and termination measures; the closest single-language ancestor
- [F*](https://fstar-lang.org/) — refinement types, algebraic effects, and SMT-based verification in a dependently-typed language
- [Koka](https://koka-lang.github.io/koka/doc/book.html) — row-polymorphic algebraic effects; Vera's effect system follows this model
- [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/) — refinement types checked via SMT solver
- [Idris](https://www.idris-lang.org/) — totality checking and termination proofs; Vera's `decreases` clauses draw on this
- [SPARK/Ada](https://www.adacore.com/about-spark) — contract-based industrial verification; the "if it compiles, it's correct" philosophy
- [bruijn](https://bruijn.marvinborner.de/) — De Bruijn indices as surface syntax for a pure lambda calculus; Vera extends this to a typed, effectful language with type-namespaced indices (see [`DE_BRUIJN.md`](DE_BRUIJN.md))
- [TLA+](https://lamport.azurewebsites.net/tla/tla.html) / [Alloy](https://alloytools.org/) — executable specifications that constrain what implementations can do; Vera's contracts serve an analogous role
- [WebAssembly](https://webassembly.org/) — portable, sandboxed compilation target; the host-import model enables the effect system's runtime dispatch without ambient capabilities
