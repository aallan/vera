# Chapter 0: Introduction and Philosophy

## 0.1 What Is Vera?

Vera is a statically typed, purely functional programming language with algebraic effects, full contracts, and refinement types. It compiles to WebAssembly.

Vera is designed for large language models (LLMs) to write, not humans. Every design decision prioritises machine-verifiability over human ergonomics.

The name comes from the Latin *veritas* (truth). In Vera, verification is a first-class citizen, not an afterthought.

## 0.2 Design Goals

1. **Checkability over correctness.** The model does not need to produce correct code on the first attempt. It needs to produce code that can be mechanically checked. When the code is wrong, the compiler provides a precise, actionable signal (a type error, a contract violation with counterexample, an undeclared effect).

2. **Explicitness over convenience.** All state changes are declared. All effects are typed. All function contracts are mandatory. There is no implicit behaviour for the model to infer or hallucinate.

3. **One canonical form.** Every construct has exactly one textual representation. There are no style choices, no optional syntax, no equivalent alternatives. If two programs are semantically identical, they are textually identical.

4. **Structural references over names.** Bindings are referenced by type and positional index (`@T.n`), not by arbitrary names. This eliminates naming consistency errors — one of the most common failure modes when models generate code across large contexts.

5. **Contracts as the source of truth.** Every function declares what it requires and what it guarantees. The compiler verifies these contracts statically where possible (via SMT solver) and inserts runtime checks where it cannot. The contract is the specification; the implementation must satisfy it.

6. **Constrained expressiveness.** The space of valid programs is deliberately small. Refinement types, mandatory contracts, and the effect system combine to reject large classes of incorrect programs at compile time. Fewer valid programs means fewer opportunities for the model to be wrong.

## 0.3 Non-Goals

1. **Human ergonomics.** Vera's syntax will look alien to human programmers. This is intentional. The language is optimised for unambiguous machine emission, not for human readability or writability.

2. **Syntactic sugar.** There is no shorthand syntax. No operator overloading. No implicit conversions. No default arguments. Every feature that introduces ambiguity or alternative representations is excluded.

3. **Backward compatibility.** Vera is a new language with no existing ecosystem. The specification may change freely between versions.

4. **Maximum performance.** The reference compiler prioritises correctness and spec compliance over optimisation. Performance improvements are a future concern.

5. **General-purpose systems programming.** Vera is not designed for writing operating systems, device drivers, or real-time software. It targets application-level logic where correctness matters more than bare-metal performance.

## 0.4 Prior Art

Vera draws on ideas from several existing languages and systems:

- **Dafny** (Microsoft Research): Full functional verification with preconditions, postconditions, loop invariants, and termination measures. Vera's contract system is directly inspired by Dafny's approach, adapted for a language without loops.

- **Koka** (Microsoft Research): Row-polymorphic algebraic effects. Vera's effect system follows Koka's model of declared effects with handlers and row polymorphism.

- **Liquid Haskell**: Refinement types where type predicates are restricted to a decidable logic fragment and checked via SMT solver. Vera's refinement type system uses this approach.

- **SPARK/Ada**: Industrial-strength contract-based verification. SPARK's philosophy of "if it compiles, it's correct" is a guiding principle for Vera.

- **bruijn**: A pure lambda calculus language using De Bruijn indices as surface syntax. Vera extends this concept to a typed, effectful language with type-namespaced indices (`@T.n`).

- **TLA+ / Alloy**: Formal specification languages. Vera's contracts serve a similar role — they are executable specifications that constrain what the implementation can do.

## 0.5 Document Conventions

Throughout this specification:

- **MUST**, **MUST NOT**, **SHALL**, **SHALL NOT**: absolute requirements per RFC 2119.
- **SHOULD**, **SHOULD NOT**: recommended but not absolute.
- **MAY**: truly optional.
- Code examples are shown in `monospace`. All examples are normative — they represent the one canonical way to write the construct shown.
- Grammar rules use EBNF notation as defined in Chapter 10.
- The term "the compiler" refers to any conforming implementation of the Vera specification.

## 0.6 Specification Structure

| Chapter | Contents |
|---------|----------|
| 0 | Introduction and Philosophy (this chapter) |
| 1 | Lexical Structure |
| 2 | Types |
| 3 | Slot References |
| 4 | Expressions and Statements |
| 5 | Functions |
| 6 | Contracts |
| 7 | Effects |
| 8 | Modules |
| 9 | Standard Library |
| 10 | Formal Grammar |
| 11 | Evaluation Semantics |
| 12 | WASM Compilation Model |
| A | Complete Examples |
| B | Verification Condition Reference |
| C | WASM Mapping Reference |
