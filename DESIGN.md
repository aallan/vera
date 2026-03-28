# Design

Technical decisions, rationale, and prior art. For the design philosophy and FAQ, see [FAQ.md](FAQ.md). For the formal specification, see [spec/](spec/).

## Technical decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Representation | Text with rigid syntax | One canonical form, no parsing ambiguity |
| References | `@T.n` typed De Bruijn indices | Eliminates naming coherence errors |
| Contracts | Mandatory on all functions | Programs must be checkable |
| Effects | Algebraic, row-polymorphic | All state and side effects explicit |
| Verification | Z3 via SMT-LIB | Industry standard, decidable fragment |
| Memory | Managed (conservative mark-sweep GC) | Models focus on logic, not memory |
| Target | WebAssembly | Portable, sandboxed, no ambient capabilities |
| Compiler | Python reference impl | Correctness over performance — see [architecture docs](vera/README.md) |
| Evaluation | Strict (call-by-value) | Simpler for models to reason about |
| Grammar | Machine-readable Lark EBNF (`grammar.lark`) | Formal grammar shared between spec and implementation |
| Diagnostics | Structured JSON with `--json` flag | Machine-readable errors for LLM feedback loops |
| Testing | Contract-driven via Z3 + WASM (`vera test`) | Generate test inputs from contracts, no manual test cases |
| Formatting | Canonical formatter (`vera fmt`) | One canonical form, enforced by tooling |
| Data types | Algebraic data types + exhaustive `match` | No classes, no inheritance; compiler enforces every case is handled |
| Polymorphism | Monomorphized generics (`forall<T where Eq<T>>`) | No runtime dispatch; four built-in abilities (`Eq`, `Ord`, `Hash`, `Show`); types fully specialized at compile time |
| Collections | `Array<T>` with `map`, `filter`, `fold`, `slice`; `Map<K, V>` key-value maps | Functional collections — no mutation, no loop constructs |
| Error handling | `Result<T, E>` ADTs, no exceptions | Errors are values; models handle every case via `match` |
| Recursion | Explicit termination measures (`decreases`) | Compiler verifies termination via Z3; no unbounded loops |
| Naming | No user-chosen variable names | `@T.n` indices are the only binding mechanism |
| Run everywhere | Dual-target WASM (native + browser bundle) | Same program runs via `wasmtime` or in the browser with `--target browser` |

## Design principles

1. **Checkability over correctness.** Code that can be mechanically checked. When wrong, the compiler provides a natural language explanation of the error with a concrete fix — an instruction, not a status report.
2. **Explicitness over convenience.** All state changes declared. All effects typed. All function contracts mandatory. No implicit behaviour.
3. **One canonical form.** Every construct has exactly one textual representation. No style choices.
4. **Structural references over names.** Bindings referenced by type and positional index (`@T.n`), not arbitrary names.
5. **Contracts as the source of truth.** Every function declares what it requires and guarantees. The compiler verifies statically where possible.
6. **Constrained expressiveness.** Fewer valid programs means fewer opportunities for the model to be wrong.

## Prior art

Vera draws on ideas from (see also [Spec Ch 0, Section 0.4](spec/00-introduction.md#04-prior-art)):

- [Eiffel](https://www.eiffel.org/) — Design by Contract, the originator of `require`/`ensure`
- [Dafny](https://dafny.org/) — full functional verification with preconditions, postconditions, and termination measures
- [F*](https://fstar-lang.org/) — refinement types, algebraic effects, and SMT-based verification
- [Koka](https://koka-lang.github.io/koka/doc/book.html) — row-polymorphic algebraic effects
- [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/) — refinement types checked via SMT solver
- [Idris](https://www.idris-lang.org/) — totality checking and termination proofs
- [SPARK/Ada](https://www.adacore.com/about-spark) — contract-based industrial verification ("if it compiles, it's correct")
- [bruijn](https://bruijn.marvinborner.de/) — De Bruijn indices as surface syntax
- [TLA+](https://lamport.azurewebsites.net/tla/tla.html) / [Alloy](https://alloytools.org/) — executable specifications that constrain what implementations can do
