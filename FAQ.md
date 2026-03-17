# Frequently Asked Questions

## Why no variable names?

The short answer is that variable names are one of the things that confuses LLMs rather than helps them. Unlike with humans, names undermine a model's efforts to keep track of state over larger scales. Models confuse similarly named variables in different parts of the codebase easily. Names help us; they don't help them.

The longer answer is more interesting. Wang et al. ("How Does Naming Affect LLMs on Code Analysis Tasks?", [arXiv:2307.12488](https://arxiv.org/abs/2307.12488)) systematically replaced variable and function names with nonsense or shuffled strings and measured the impact on CodeBERT across code analysis tasks. Good names do help LLM performance — but shuffled names (where a variable named `count` gets swapped with one named `result`) perform *worse* than random gibberish. The model actively gets misled by plausible-but-wrong names. Python, being dynamically typed, is hit harder than Java, because models compensate for lost names using type declarations in statically typed languages.

That last point is the Vera thesis in miniature. In a language with strong types, explicit contracts, and no variable names, the model can't fall back on the naming crutch, but it also can't be misled by it. It has to use the structural information.

Le et al. ("When Names Disappear", [arXiv:2510.03178](https://arxiv.org/abs/2510.03178)) make this sharper still: LLMs exploit statistical correlations between identifiers and functionality even on execution prediction tasks that should depend only on program structure. They call this "identifier leakage." The model *appears* to understand code when it's actually pattern-matching on familiar tokens.

So the problem isn't that variable names are useless to LLMs. It's that they're a crutch that lets the model appear to understand code when it's actually not reasoning about the code. Vera's bet is that if you remove the crutch and give the model verified structural information instead — contracts, types, effect declarations — you force it onto firmer ground.


## Why not keep variable names and strip them with tooling?

You could absolutely build a bidirectional transform: names in, indices out for the model, indices back to names for humans. The tooling for that would be straightforward.

The reason Vera doesn't do this is that the canonical form *is* the language. If names exist in the source, they're part of the program, which means they can diverge from intent, be inconsistent, or be misleading — and now you have two representations to keep in sync. Vera sidesteps that by having one representation that's unambiguous by construction. The model writes exactly what the compiler sees. No translation layer, no sync problem.

That said, a visualiser that infers human-readable names from types and usage for display purposes is interesting tooling *on top* of Vera. The canonical form stays clean for the model, but humans get an annotated view when they need one.


## But don't variable names help the LLM relate implementation to requirements?

This is a fair point. The contracts can say what the output *cannot* be, but if the constraints fully determine the output then the function body is superfluous. So the implementation matters, and shouldn't the implementation be tied to the human's requirements?

Vera's answer is that the contracts *are* the link between implementation and requirements. The human writes (or reviews) the contracts — preconditions, postconditions, effect declarations — and those are small, declarative, and human-readable. The compiler then proves the implementation satisfies them. The human audits the specification, not the code.

The bet is that contracts are a better surface for capturing intent than variable names scattered through an implementation. A function signature with `requires(@Int.1 != 0)` and `ensures(@Int.result == @Int.0 / @Int.1)` communicates what the function does more precisely than any variable name could.


## What actually gets verified?

There are three layers, and they cover different things.

**Layer 1: Type system (mechanical, complete).** Every binding uses typed De Bruijn indices (`@Int.0`, `@String.1`, etc.), so the type checker can verify that every reference resolves to a binding of the correct type, every function call matches its signature, every pattern match is exhaustive, and generics monomorphise correctly. This is the "components slot together" layer. Nothing novel here beyond the index scheme, but it's total — if it type-checks, the pieces fit.

**Layer 2: Z3 contract verification (mechanical, bounded).** Every function has mandatory preconditions, postconditions, and effect declarations. The compiler translates these into a decidable SMT fragment and hands them to Z3. Currently that fragment covers linear arithmetic over integers and booleans, array lengths, ADT constructor discrimination and field access (via Z3 datatype sorts), and termination measures for structural recursion. Across the current example programs, the vast majority of contracts verify statically — the compiler can prove the implementation satisfies the spec without running the code. The remainder are contracts involving generic type parameters (a fundamental SMT limitation) or symbolic effect state modelling across handlers. These fall back to runtime contract checking: the assertions still execute, they just aren't proven at compile time.

This layer does cover actual correctness properties, not just interface compatibility. If you write `ensures(@Nat.result >= 0)` on an absolute value function, the compiler will either prove it holds for all inputs or give you a counterexample.

**Layer 3: Agent documentation and human intent (expressive, unverified).** The contracts themselves are unverified with respect to user intent. Nothing in the pipeline checks whether `ensures(@Int.result >= 0)` is actually what you wanted the function to do. The contract could be a perfectly verified implementation of the wrong specification. This is where SKILL.md lives — it steers the model toward writing contracts that capture reasonable intent, but "reasonable" has no formal backing.

So: provably correct relative to stated requirements, yes. Provably correct relative to unstated intent, no — but the auditable surface is deliberately as small as possible. The human reviews contracts, not implementations.


## How can we verify if the written code is safe and follows compliance?

Every function in Vera must declare what it requires, what it guarantees, and what side effects it performs. The compiler proves the implementation satisfies those contracts via Z3 — it either verifies statically or gives you a counterexample. So a compliance reviewer can audit the contracts (which are small and declarative) without reading the implementation, and the compiler proves the code matches them.

The effect system adds another dimension: a function that declares `effects(pure)` is proven to have no side effects. A function that declares `effects(<IO>)` can only perform IO operations. A caller that only permits `<Http>` cannot invoke a function that also performs `<IO>`. This makes it possible to enforce security boundaries at the type level — a sandboxed module literally cannot perform operations outside its declared effect set.


## What are abilities?

Abilities are Vera's mechanism for constrained generics — type constraints that restrict what types a generic function can accept. They're inspired by Roc's ability system and serve a similar role to Haskell's type classes or Rust's traits, but with a fixed set of built-in abilities rather than user-defined ones.

Vera has four built-in abilities:

- **`Eq<T>`** — equality comparison via `eq(a, b)`, satisfied by all primitive types and ADTs whose fields are themselves `Eq`
- **`Ord<T>`** — ordering via `compare(a, b)`, which returns the built-in `Ordering` ADT (`Less`, `Equal`, `Greater`), satisfied by `Int`, `Nat`, `Bool`, `Float64`, `String`, and `Byte`
- **`Hash<T>`** — hashing via `hash(x)`, which returns an `Int`, satisfied by `Int`, `Nat`, `Bool`, `Float64`, `String`, and `Byte`
- **`Show<T>`** — string conversion via `show(x)`, satisfied by `Int`, `Nat`, `Bool`, `Float64`, `String`, and `Byte`

You use them in generic signatures with `where` clauses:

```vera
public forall<T where Eq<T>> fn contains(@Array<T>, @T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  ...
}
```

The compiler checks at every call site that the concrete type satisfies the required ability. ADTs can auto-derive `Eq` if all their constructor fields are themselves `Eq`-satisfying types — simple enums satisfy `Eq` automatically.

The design choice to fix the ability set (rather than allowing user-defined abilities) is deliberate: it keeps the language simpler for models and avoids the coherence problems that plague open type class systems.


## Can I run Vera programs in the browser?

Yes. `vera compile --target browser` produces a self-contained directory with a `.wasm` binary, a JavaScript runtime (`runtime.mjs`), and an `index.html`:

```bash
vera compile --target browser examples/hello_world.vera
# produces examples/hello_world_browser/
#   module.wasm
#   runtime.mjs
#   index.html
```

Serve it with any HTTP server and open `index.html` — no build step, no bundler, no dependencies. The JavaScript runtime provides browser-appropriate implementations of all Vera host bindings: `IO.print` writes to the page, `IO.read_line` uses `prompt()`, and all other operations (State, contracts, Markdown) work identically to the wasmtime runtime.

The runtime also works in Node.js:

```bash
node --experimental-wasm-exnref vera/browser/harness.mjs module.wasm
```

Mandatory parity tests enforce that the browser runtime produces identical results to the wasmtime runtime on every PR.


## How does contract-driven testing work?

`vera test` is Vera's built-in testing command. It generates test inputs automatically from function contracts — you don't write test cases manually.

The process works in three steps:

1. **Input generation**: The compiler reads each function's `requires()` clause and uses Z3 to generate concrete values that satisfy the precondition. For example, if a function requires `@Int.1 != 0`, Z3 produces pairs of integers where the second is non-zero. It generates up to 100 trials per function by default (configurable with `--trials`).

2. **Execution**: Each generated input is compiled to WASM and executed via wasmtime. The function runs with real values, not symbolic ones.

3. **Contract checking**: The `ensures()` postcondition is checked against the actual output. If any trial produces a result that violates the postcondition, the test fails with the concrete input that triggered it.

```bash
vera test examples/safe_divide.vera          # test all functions
vera test --trials 50 examples/safe_divide.vera  # limit trials
vera test --json examples/safe_divide.vera   # JSON output for agents
```

This combines the best of property-based testing (generated inputs, no manual cases) with the best of formal verification (inputs derived from specifications, not random). The contracts serve double duty: they're both the specification the compiler proves and the test oracle that validates runtime behaviour.


## What are the intended applications? Who are the end users?

The reference compiler targets WebAssembly, so the initial applications are web-based. The `.wasm` binary runs at the command line via wasmtime or in any browser with the self-contained JavaScript runtime.

But the deeper answer is that the end users aren't humans directly — they're AI coding agents. The intended workflow is: a human (or an orchestrating agent) describes what they want; a model generates Vera code; the compiler verifies it; the WASM binary runs. The human's job is to review contracts, not implementations.

The roadmap includes native HTTP, JSON, and Markdown support, which points toward agent workloads: API integration, data processing, and structured document generation. A research function that searches the web, processes results via LLM inference, and returns typed, contract-checked Markdown output is the kind of program Vera is designed for.


## Is there evidence this actually works?

Vera-specific data doesn't exist yet. Nobody has run a controlled comparison measuring whether models produce more reliable code in Vera than in existing languages. That's the experiment that needs to happen.

However, the recent literature is encouraging. The type-constrained decoding paper (Mündler, He, Wang et al., "Type-Constrained Code Generation with Language Models", PLDI 2025, [ACM DL](https://dl.acm.org/doi/10.1145/3729274)) found that enforcing type constraints during LLM code generation cut compilation errors by more than half and improved functional correctness by 3.5–4.5%. Syntax constraints alone provided limited improvement — it was the *type* constraints that made the difference. The same paper found that 94% of LLM-generated compilation errors are type-check failures — exactly the class of error that a strong static type system catches at compile time.

The Vericoding benchmark (Sun et al., "A Benchmark for Vericoding", [arXiv:2509.22908](https://arxiv.org/abs/2509.22908)) shows LLMs achieving 82% verification success on Dafny versus 27% on Lean, which suggests SMT-automated verification (Vera's approach) is significantly more LLM-tractable than explicit proof construction.

Blinn et al. ("Statically Contextualizing Large Language Models with Typed Holes", OOPSLA 2024, [ACM DL](https://doi.org/10.1145/3689728)) demonstrated that providing type context at incomplete program locations significantly improves LLM completion quality — a result that directly motivates Vera's planned typed holes feature ([#226](https://github.com/aallan/vera/issues/226)).

None of this is Vera-specific, but it validates the design choices. The thesis is plausible, the tooling exists. What's missing is someone running the experiment.


## What about the training data problem? LLMs have never seen Vera code.

This is a real concern. LLMs are trained on trillions of tokens of Python, TypeScript, and JavaScript. A MojoBench study (NAACL 2025) found that even fine-tuned models achieved only 30–35% improvement over base models on Mojo code generation, illustrating the cold-start problem for new languages.

Vera's approach has three parts. First, the agent-facing documentation (SKILL.md) is designed to be dropped into a model's context window, so the model works from the language specification rather than training data recall. Second, Vera's syntax is deliberately simple and regular — fewer constructs, each with exactly one canonical form — which reduces the surface area a model needs to learn. Third, the conformance test suite (55 programs covering every language feature) gives models concrete examples to learn from and conform to. Simon Willison argued in December 2025 that a language-agnostic conformance suite is the single most important tool for LLM adoption of a new language — LLMs can learn new languages remarkably well when given tests to conform to.


## How does Vera compare to Dafny / Lean / Koka / F*?

**Dafny** shares Vera's Z3/SMT verification approach and is used in production at AWS (Cedar authorisation). But it's imperative, lacks algebraic effects, and has optional (not mandatory) annotations. The 2025 paper proposing Dafny as a verification intermediate language for LLM-generated code validates Vera's core thesis — but Dafny wasn't purpose-built for it.

**Lean 4** has the richest LLM integration ecosystem (LeanDojo, Lean Copilot) and significant investment. But it's primarily a theorem prover with monadic effects. LLMs achieve only 27% success rate on Lean versus 82% on Dafny, suggesting explicit proof construction is harder for models than SMT-automated verification.

**Koka** pioneered the row-polymorphic algebraic effect type system that Vera draws from. But it has no verification, no contracts, and isn't production-ready.

**F*** combines refinement types, algebraic effects, and SMT-based verification. It's the closest to Vera's feature set, but targets human programmers, not models. It also has a steep learning curve.

No production language today combines mandatory contracts, algebraic effects, refinement types, constrained generics with built-in abilities, De Bruijn indices, Z3 verification, and WebAssembly compilation into a single design optimised for LLM code generation.


## Why WebAssembly?

Three reasons. First, portability — the same `.wasm` binary runs at the command line or in any browser. Second, sandboxing — WebAssembly has no ambient capabilities, so a Vera program cannot do anything its effect declarations don't permit. Third, the WASM Component Model (W3C, production-ready in Wasmtime) will enable Vera components to interoperate with Rust, Go, and Python components via WIT interfaces, providing ecosystem access without requiring a massive native package system.


## Why Python for the compiler?

Correctness over performance. The reference compiler is a specification-faithful implementation, not a production compiler. Python makes the compiler readable, testable, and easy to modify during rapid language evolution. The seven-stage pipeline (parse → transform → resolve → typecheck → verify → compile → execute) is independently testable at each stage.

If Vera reaches the point where compiler performance matters, a production compiler in Rust or OCaml would be a separate project. The Python reference compiler would remain as the specification oracle.


## Why are contracts mandatory?

Because the whole point is that code should be checkable. If contracts are optional, models won't write them — and then you're back to unverifiable code. Making contracts mandatory means every function is a specification that the compiler can verify against its implementation. The model doesn't need to be right; it needs to be checkable.

This is a deliberate trade-off. Mandatory contracts add friction. But the friction is the feature — it forces the model (and any human) to state what the function requires, what it guarantees, and what effects it performs. That statement is the auditable surface.


## What does the project status look like?

The reference compiler is at v0.0.90. It includes:

- A seven-stage pipeline: parse, transform, resolve, typecheck, verify, compile, execute
- Around 28,500 lines of Python compiler code
- A 13-chapter formal specification
- 2,375 unit tests plus a 55-program conformance suite
- 25 working example programs
- 70 built-in functions plus 5 Option/Result combinators
- Four built-in abilities (Eq, Ord, Hash, Show) with constrained generics and ADT auto-derivation
- Full IO operations (print, read_line, read_file, write_file, args, exit, get_env)
- Algebraic data types, pattern matching, closures, generics with monomorphisation
- Algebraic effect handlers with resume and state
- Async/await with `Future<T>` and the `<Async>` effect
- Typed Markdown (`MdBlock`/`MdInline` ADTs) for structured document processing
- String interpolation with auto-conversion for primitive types
- Cross-module imports with contract verification at call sites
- Contract-driven testing via Z3 and WASM
- A canonical code formatter
- WebAssembly compilation and execution via wasmtime
- Browser runtime with mandatory parity tests

The language is under active development. See the [Roadmap](ROADMAP.md) and [Changelog](CHANGELOG.md) for current status and planned features.


## How do I try it?

```bash
git clone https://github.com/aallan/vera.git && cd vera
python -m venv .venv && source .venv/bin/activate
pip install -e .
vera run examples/hello_world.vera
```

For agents, point your model at [SKILL.md](https://raw.githubusercontent.com/aallan/vera/main/SKILL.md). It's the complete language reference, designed to be dropped into a context window.


## References

- Wang et al., "How Does Naming Affect LLMs on Code Analysis Tasks?", [arXiv:2307.12488](https://arxiv.org/abs/2307.12488)
- Le et al., "When Names Disappear: Revealing What LLMs Actually Understand About Code", [arXiv:2510.03178](https://arxiv.org/abs/2510.03178)
- Mündler, He, Wang et al., "Type-Constrained Code Generation with Language Models", PLDI 2025, [ACM DL](https://dl.acm.org/doi/10.1145/3729274)
- Blinn et al., "Statically Contextualizing Large Language Models with Typed Holes", OOPSLA 2024, [ACM DL](https://doi.org/10.1145/3689728)
- Sun et al., "A Benchmark for Vericoding: Formally Verified Program Synthesis", [arXiv:2509.22908](https://arxiv.org/abs/2509.22908)
