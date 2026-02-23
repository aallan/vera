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

## 0.5 Diagnostics as Instructions

Vera's compiler does not produce diagnostics for humans. It produces **instructions for the model that wrote the code**.

Every diagnostic — parse errors, type errors, contract violations, effect mismatches, verification failures — MUST be a natural language explanation that tells the model what went wrong, why, and how to fix it. The diagnostic is not a status report; it is a corrective action.

### 0.5.1 Diagnostic Structure

Every diagnostic MUST include:

1. **Location.** File path, line number, and column, with the offending source line quoted and the error position indicated.
2. **Description.** A plain English explanation of the problem. No error codes, no abbreviated jargon.
3. **Rationale.** Why this is an error — which language rule was violated.
4. **Fix.** A concrete code example showing the corrected form. This is not a hint; it is a template the model can apply directly.
5. **Spec reference.** The specification chapter and section that defines the violated rule.

### 0.5.2 Example

```
Error in examples/bad.vera at line 5, column 1:

    fn add(@Int, @Int -> @Int)
    ^

  Function "add" is missing its contract block. Every function in Vera
  must declare requires(), ensures(), and effects() clauses between
  the signature and the body.

  Add a contract block after the signature:

    fn add(@Int, @Int -> @Int)
      requires(true)
      ensures(@Int.result == @Int.0 + @Int.1)
      effects(pure)
    {
      ...
    }

  See: Chapter 5, Section 5.1 "Function Structure"
```

### 0.5.3 Diagnostic Categories

Diagnostics occur at every phase of compilation:

| Phase | Examples |
|-------|----------|
| Parsing | Missing contracts, malformed `@T.n` references, unclosed blocks, invalid syntax |
| Type checking | Type mismatches, invalid refinement predicates, subtyping violations |
| Effect checking | Undeclared effects, missing handlers, effect row mismatches |
| Verification (Tier 1) | Contract violations with SMT counterexamples, explained in plain language |
| Verification (Tier 2) | Suggestions for lemmas or hints that would help the solver |
| Verification (Tier 3) | Runtime check insertion points, with explanation of what could not be proven |
| Reachability | Unreachable branches (when preconditions or types make a case impossible) |
| Call-site analysis | Arguments that cannot be proven to satisfy a callee's preconditions |

### 0.5.4 Design Rationale

The LLM-compiler interaction is a feedback loop. The model writes code; the compiler checks it; the model reads the diagnostics and revises. The quality of the diagnostics determines the speed of convergence.

Traditional compilers optimise diagnostics for human developers who understand the language and can infer fixes from terse messages. LLMs do not have this background knowledge reliably. They perform best when given explicit, complete instructions — the same principle that makes MCP tool descriptions effective is applied here to compiler output.

A diagnostic that says `expected token '{'` is a puzzle. A diagnostic that says "Function X is missing its contract block. Add requires(), ensures(), and effects() between the signature and the body, like this: [example]" is an instruction. Vera always produces instructions.

## 0.6 Document Conventions

Throughout this specification:

- **MUST**, **MUST NOT**, **SHALL**, **SHALL NOT**: absolute requirements per RFC 2119.
- **SHOULD**, **SHOULD NOT**: recommended but not absolute.
- **MAY**: truly optional.
- Code examples are shown in `monospace`. All examples are normative — they represent the one canonical way to write the construct shown.
- Grammar rules use EBNF notation as defined in Chapter 10.
- The term "the compiler" refers to any conforming implementation of the Vera specification.

## 0.7 Specification Structure

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

## 0.8 Design Notes (Future Chapters)

The following design decisions are noted here for future specification work:

### Network Access as an Effect

Network I/O SHOULD be modelled as an algebraic effect (e.g., `<Http>` or `<Net>`) with operations like `get`, `post`, etc. Functions performing network access declare `effects(<Http>)`. Handlers provide the implementation — real HTTP in production, mocks in tests. This fits naturally with Vera's algebraic effect system and makes network I/O explicit and testable. Almost all practical programs need network access; this should be a first-class part of the standard library (Chapter 9).

### JSON as a Standard Library Type

JSON SHOULD be a standard library ADT, not a primitive type:

```vera
data Json {
  JNull,
  JBool(Bool),
  JNumber(Float),
  JString(String),
  JArray(Array<Json>),
  JObject(Map<String, Json>)
}
```

Parse and serialize operations belong in the standard library. Refinement types can express JSON schemas (e.g., `type ApiResponse = { @Json | has_field(@Json.0, "status") }`). This approach keeps the core language small while providing ergonomic JSON support.

### Asynchronous Promises/Futures

Async operations SHOULD be first-class citizens in Vera, modelled as an algebraic effect. An `<Async>` effect with an `await` operation fits naturally:

```vera
fn fetch_both(@String, @String -> @Tuple<Json, Json>)
  requires(true)
  ensures(true)
  effects(<Http, Async>)
{
  let @Future<Json> = async(http_get(@String.0));
  let @Future<Json> = async(http_get(@String.1));
  let @Json = await(@Future<Json>.1);
  let @Json = await(@Future<Json>.0);
  Tuple(@Json.1, @Json.0)
}
```

Key design points:
- `async(expr)` wraps an effectful computation in a `Future<T>`, starting it concurrently
- `await(@Future<T>.n)` suspends until the future resolves, yielding the result
- Futures can be passed around, stored in data structures, and composed
- The `<Async>` effect must be declared, making concurrency explicit and trackable
- Handlers can provide different scheduling strategies (thread pool, event loop, sequential)
- This integrates with the `<Http>` effect: network calls are naturally async

This avoids coloured-function problems (async vs sync) because algebraic effects already separate the description of an operation from its execution. A handler can run `<Http>` operations sequentially or concurrently — the function code is the same either way.
