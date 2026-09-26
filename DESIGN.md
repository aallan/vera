# Design

Technical decisions, rationale, and prior art. For the design philosophy and FAQ, see [FAQ.md](FAQ.md). For the language specification, see [spec/](spec/). For the compiler architecture, see [vera/README.md](vera/README.md).

---

## Design principles

1. **Checkability over correctness.** Code that can be mechanically checked. When wrong, the compiler provides a natural language explanation of the error with a concrete fix — an instruction, not a status report.
2. **Explicitness over convenience.** All state changes declared. All effects typed. All function contracts mandatory. No implicit behaviour.
3. **One canonical form.** One preferred spelling per construct; for a given parse, formatting is deterministic and idempotent. No style choices.
4. **Structural references over names.** Bindings referenced by type and positional index (`@T.n`), not arbitrary names. See [`DE_BRUIJN.md`](DE_BRUIJN.md).
5. **Contracts as the source of truth.** Every function declares what it requires and guarantees. The compiler verifies statically where possible.
6. **Constrained expressiveness.** Fewer valid programs means fewer opportunities for the model to be wrong.

---

## Technical decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| References | [`@T.n` typed De Bruijn indices](DE_BRUIJN.md) | Eliminates naming coherence errors; indices are locally determinable from types alone |
| Contracts | Mandatory `requires`/`ensures`/`effects` on all functions | Programs must be checkable; contracts are the machine-verifiable specification |
| Verification | Z3 static (Tier 1) → Z3 guided (Tier 2) → runtime fallback (Tier 3) | Maximises static guarantees; degrades gracefully where SMT is undecidable |
| Effects | Algebraic, row-polymorphic (`IO`, `Http`, `HttpServer`, `State`, `Async`, `Inference`, `DB`, `Random`, `Diverge`, plus the parameterised exception effect `Exn<T>` — all reported by `vera effects --json`) | All state and side effects explicit; effects are typed, trackable, and handleable |
| Error handling | `Result<T,E>` ADTs for expected errors; `Exn<T>` algebraic effect for exceptions | Errors are values; `match` enforces handling every case; `Exn<T>` is handleable like any other effect |
| Inference | `Inference.complete` as an algebraic effect | LLM calls are typed, contract-verifiable, handleable, and explicit in signatures |
| Data types | Algebraic data types + exhaustive `match` | No classes, no inheritance; compiler enforces every case is handled |
| Polymorphism | Monomorphized generics (`forall<T where Eq<T>>`) | No runtime dispatch; four built-in abilities (`Eq`, `Ord`, `Hash`, `Show`); types fully specialised at compile time |
| Refinement types | `{ @T \| predicate }` checked by Z3 | Encode value-level constraints in the type system; rejected statically or at runtime |
| Type aliases | Opaque at a slot name's head; resolved inside type arguments, and in `State`/`Exn` cell identity wherever the resolved type has a mangle-safe family name ([`DE_BRUIJN.md`](DE_BRUIJN.md) §6.5) | An alias names a binding, so a library adding one must not split a caller's namespace; a type argument is a structural component, so one type must not become two namespaces |
| Collections | `Array<T>`, `Map<K,V>`, `Set<T>` | Functional, immutable; no mutation, no loops; `array_map`/`filter`/`fold`/`slice` as built-ins |
| Standard library | 164 built-in functions | Strings, arrays, maps, sets, decimals, math (log/trig/constants/utilities), JSON, HTML, Markdown, regex, base64, URL — no external deps |
| Modules | `module`/`import` with explicit `public`/`private` visibility | Programs split across files; `vera check` resolves the module graph |
| Recursion | Explicit termination measures (`decreases`), or the `Diverge` effect for a function that may not terminate; a recursive function with neither is refused (`E137`) | Termination is proved via Z3 where it can be and guarded at run time otherwise; non-termination is visible in the signature |
| Evaluation | Strict (call-by-value) | Simpler for models to reason about; no lazy evaluation to track |
| Memory | Conservative mark-sweep GC in WASM | Implemented entirely in generated WASM (`$alloc`, `$gc_collect`, shadow stack); no host GC; models focus on logic |
| Target | WebAssembly (native + browser + WASI P2 components) | Portable, sandboxed, no ambient capabilities; `vera run` uses wasmtime; `vera compile --target browser` emits a JS bundle; `--target wasi-p2` emits an experimental WASI Preview 2 component for stock wasip2 hosts (`--world server` for `wasmtime serve`) |
| Compiler | Python reference implementation | Correctness over performance; clean separation of phases; see [vera/README.md](vera/README.md) |
| Grammar | Machine-readable Lark EBNF (`grammar.lark`) | Formal grammar is shared between spec and implementation; no ambiguity |
| Diagnostics | LLM-instruction format; `--json` for machine use; stable error codes E001–E702 and warning codes W001–W003 | Every diagnostic names the problem, explains why, and gives a concrete fix; codes are stable for tooling |
| Testing | Contract-driven via Z3 + WASM (`vera test`) | Z3 generates inputs that satisfy `requires`; compiled WASM executes; `ensures` is checked against real outputs |
| Formatting | Canonical formatter (`vera fmt`) | One canonical form, enforced by pre-commit and CI; no style drift |
| Representation | Text with rigid syntax | One canonical form, no parsing ambiguity, no equivalent alternatives |

---

## The verification pipeline

Vera's contracts are checked in two implemented tiers, applied at every call site:

![Three-tier verification: each obligation goes to Z3 — unsat is verified (Tier 1), sat is a compile error with a counterexample, unknown or timeout defers to a Tier 3 runtime guard; Tier 2 (hints) is specified but not yet implemented and also falls to Tier 3.](assets/diagrams/tiers.svg)

**Tier 1 — Z3 static (decidable fragment).** The compiler generates a verification condition and sends it to Z3. If Z3 returns `unsat`, the contract is proved for all inputs. This covers linear integer and real arithmetic, boolean logic, strings, ADT constructor discrimination and fields, array lengths and literals, and refinement predicates (spec §6.8).

**Tier 3 — Runtime fallback.** If Z3 returns `unknown` or times out, the contract is compiled as a runtime check in the WASM binary. A violation traps on entry to the function (a `requires`) or on its return (an `ensures`), naming the contract. A site that can be neither proved nor guarded is disclosed as a warning (`E504`, `E506`, `E531`, `E537`) and counted in neither tier.

`vera verify --json` reports the tier breakdown:

```json
{"verification": {"tier1_verified": 12, "tier3_runtime": 1, "total": 13, "assumptions": 0, "timeout_ms": 10000}}
```

A fully Tier 1–verified program has the strongest guarantee: if it compiles and verifies, the contracts hold for all inputs. The compiled program checks its contracts at run time as well, so a wrong proof traps rather than returning a wrong answer. See [spec/06-contracts.md](spec/06-contracts.md) for the formal treatment.

**Tier 2 — Z3 guided (extended fragment).** Hints from `assert` statements and lemma functions extend the decidable fragment to function calls, quantifiers, and array properties. See [spec/06-contracts.md §6.3.2](spec/06-contracts.md).

---

## The effect system

Effects are declared in function signatures and checked at every call site. A function that calls `IO.print` must declare `effects(<IO>)`; a function that calls `Inference.complete` must declare `effects(<Inference>)`. Undeclared effects are a compile error.

Built-in effects:

| Effect | Operations | Notes |
|--------|-----------|-------|
| `IO` | `print`, `read_line`, file ops | Console and file I/O |
| `Http` | `get`, `post` | Network requests; returns `Result<String, String>` |
| `State<T>` | `get`, `put` | Typed mutable state; scope controlled by `handle[State<T>]` |
| `Exn<T>` | `throw` | Typed exceptions; `throw` never resumes (`Never` return type); handling is via `handle[Exn<T>]` syntax |
| `Async` | `async`, `await` | `Future<T>` is zero-overhead at compile time; `async(Http.get/post(...))` runs concurrently on a host worker thread, all other shapes evaluate eagerly |
| `HttpServer` | — (marker) | Verified HTTP handling: `vera serve` hosts a contract-checked `handle(Request -> Response)`; compiles to a wasi:http component with `--world server` |
| `Random` | `random_int`, `random_float`, `random_bool` | Host randomness; rejection-sampled for unbiased ranges |
| `Diverge` | — (marker) | Declares potential non-termination |
| `Inference` | `complete` | LLM calls; `String → Result<String, String>`; provider selected by env var |
| `DB` | `query`, `execute` | SQL against SQLite (chosen by `VERA_DB_URL`); the SQL argument must be literal-provenance (`E207`) with runtime values through `?` placeholders; rows are `Array<Array<Option<String>>>` (SQL `NULL` = `None`) |

User-defined effects follow the same pattern. Effects compose in rows: `effects(<IO, Http>)`, `effects(<Inference, IO>)`.

![Effect subtyping by row inclusion: pure fits where IO is allowed, and IO fits where IO plus State is allowed — fewer effects always fit where more are expected.](assets/diagrams/effect-row-lattice.svg)

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
