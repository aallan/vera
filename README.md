# Vera

[![Vera — A language designed for machines to write](assets/vera-social-preview.jpg)](https://veralang.dev)

**Vera** (v-EER-a) is a programming language designed for large language models (LLMs) to write, not humans.

The name comes from the Latin *veritas* (truth). In Vera, verification is a first-class citizen, not an afterthought.

## Why?

Programming languages have always co-evolved with their users. Assembly emerged from hardware constraints. C emerged from operating system needs. Python emerged from productivity needs. If models become the primary authors of software, it is consistent for languages to adapt to that.

The evidence suggests the biggest problem models face isn't syntax — it's **coherence over scale**. Models struggle with maintaining invariants across a codebase, understanding the ripple effects of changes, and reasoning about state over time. They're pattern matchers optimising for local plausibility, not architects holding the entire system in mind.

Vera addresses this by making everything explicit and verifiable. The model doesn't need to be right — it needs to be **checkable**.

## Design Principles

1. **Checkability over correctness.** Code that can be mechanically checked. When wrong, the compiler provides a natural language explanation of the error with a concrete fix — an instruction, not a status report.
2. **Explicitness over convenience.** All state changes declared. All effects typed. All function contracts mandatory. No implicit behaviour.
3. **One canonical form.** Every construct has exactly one textual representation. No style choices.
4. **Structural references over names.** Bindings referenced by type and positional index (`@T.n`), not arbitrary names.
5. **Contracts as the source of truth.** Every function declares what it requires and guarantees. The compiler verifies statically where possible.
6. **Constrained expressiveness.** Fewer valid programs means fewer opportunities for the model to be wrong.

## Key Features

- **No variable names** — typed De Bruijn indices (`@T.n`) replace traditional variable names
- **Full contracts** — mandatory preconditions, postconditions, invariants, and effect declarations on all functions
- **Algebraic effects** — declared, typed, and handled explicitly; pure by default
- **Refinement types** — types that express constraints like "a list of positive integers of length n"
- **Three-tier verification** — static verification via Z3, guided verification with hints, runtime fallback
- **Diagnostics as instructions** — every error message is a natural language explanation with a concrete fix, designed for LLM consumption
- **Compiles to WebAssembly** — portable, sandboxed execution

## What Vera Looks Like

### Hello World — effects and contracts

Every function declares what it requires, what it guarantees, and what effects it performs. Even a one-liner has a full contract. Effects are declared before use, and effect operations use qualified calls (`IO.print`). `effects(<IO>)` tells the compiler (and the model) that this function interacts with the outside world.

```vera
effect IO {
  op print(String -> Unit);
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("Hello, World!")
}
```

> [`examples/hello_world.vera`](examples/hello_world.vera) — run with `vera run examples/hello_world.vera`

### Pure functions — postconditions the compiler can verify

There are no variable names. `@Int.0` refers to the most recent `Int` binding — a typed positional index, like De Bruijn indices but namespaced by type. The `ensures` clause is a machine-checkable promise: the result is non-negative and equals the absolute value of the input. The compiler verifies this via SMT solver.

```vera
public fn absolute_value(@Int -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  ensures(@Nat.result == @Int.0 || @Nat.result == -@Int.0)
  effects(pure)
{
  if @Int.0 >= 0 then {
    @Int.0
  } else {
    -@Int.0
  }
}
```

> [`examples/absolute_value.vera`](examples/absolute_value.vera) — run with `vera run examples/absolute_value.vera --fn absolute_value -- -42`

### Preconditions — rejecting bad inputs at compile time

`requires(@Int.1 != 0)` means this function cannot be called with a zero divisor. The compiler checks every call site to prove the precondition holds. If it cannot prove it, the code does not compile. Division by zero is not a runtime error — it is a type error.

```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

> [`examples/safe_divide.vera`](examples/safe_divide.vera) — run with `vera run examples/safe_divide.vera --fn safe_divide -- 3 10`

### File IO — results and pattern matching

IO operations return `Result` types for error handling. `IO.read_file` returns `Result<String, String>` — the program must handle both success and failure via pattern matching. The `effects(<IO>)` annotation makes the side effect explicit.

```vera
public fn main(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match IO.read_file("example.txt") {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  };
  ()
}
```

> [`examples/file_io.vera`](examples/file_io.vera) — run with `vera run examples/file_io.vera`

### Algebraic effects — explicit state, no hidden mutation

Vera is pure by default. State changes must be declared as effects. `effects(<State<Int>>)` says this function reads and writes an integer. The `ensures` clause specifies exactly how the state changes: the new value equals the old value plus one. Handlers (not shown) provide the actual state implementation — an in-memory cell in production, a mock in tests.

```vera
public fn increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
```

> [`examples/increment.vera`](examples/increment.vera) — this example uses `State<Int>` effects with handler compilation. Compile it with `vera compile examples/increment.vera` or run the function with `vera run examples/increment.vera --fn increment`

## What Errors Look Like

Traditional compilers produce diagnostics for humans: `expected token '{'`. Vera produces **instructions for the model that wrote the code**.

Every error includes what went wrong, why, how to fix it with a concrete code example, and a spec reference. The compiler's output is designed to be fed directly back to the model as corrective context.

```
Error in main.vera at line 12, column 1:

    private fn add(@Int, @Int -> @Int)
    ^

  Function "add" is missing its contract block. Every function in Vera
  must declare requires(), ensures(), and effects() clauses between the
  signature and the body.

  Add a contract block after the signature:

    private fn add(@Int, @Int -> @Int)
      requires(true)
      ensures(@Int.result == @Int.0 + @Int.1)
      effects(pure)
    {
      ...
    }

  See: Chapter 5, Section 5.1 "Function Structure"
```

This principle applies at every stage: parse errors, type errors, effect mismatches, verification failures, and contract violations all produce natural language explanations with actionable fixes.

## Project Status

Vera is in **active development**. The reference compiler — parser, AST, type checker, contract verifier (Z3), WASM code generator, module system, and runtime contract insertion — is working. Programs compile to WebAssembly and execute via wasmtime. See the [roadmap](#roadmap) for what's next.

The language specification is in draft across 13 chapters:

- **[Ch 0: Introduction and Philosophy](spec/00-introduction.md)** — Design goals, the LLM-first premise, and the principles behind mandatory contracts, slot references, and algebraic effects.
- **[Ch 1: Lexical Structure](spec/01-lexical-structure.md)** — Source encoding (UTF-8), whitespace handling, indentation-free formatting, and token conventions.
- **[Ch 2: Types](spec/02-types.md)** — Primitive types, algebraic data types, parametric polymorphism, refinement types with logical predicates, and function types with effect annotations.
- **[Ch 3: Slot References](spec/03-slot-references.md)** — The `@T.n` binding mechanism where bindings are referenced by type and positional index rather than variable names.
- **[Ch 4: Expressions and Statements](spec/04-expressions.md)** — Expression-oriented design where blocks and nearly all constructs produce values. `let` bindings are the only statement form.
- **[Ch 5: Functions](spec/05-functions.md)** — Mandatory parameter types, return types, contracts, effect declarations, and body expressions. Functions are the primary abstraction unit.
- **[Ch 6: Contracts](spec/06-contracts.md)** — Preconditions, postconditions, and `decreases` clauses as executable specifications that the implementation must satisfy.
- **[Ch 7: Effects](spec/07-effects.md)** — Pure-by-default semantics with algebraic effects for state, I/O, and exceptions, inspired by Koka.
- **[Ch 8: Modules](spec/08-modules.md)** — File-based module system with dotted paths, selective and wildcard imports, public/private visibility, and cross-module verification.
- **[Ch 9: Standard Library](spec/09-standard-library.md)** — Built-in types (Option, Result, Array), effects (IO, State), and functions that cannot be expressed purely in user code.
- **[Ch 10: Formal Grammar](spec/10-grammar.md)** — Complete EBNF grammar compatible with the Lark LALR(1) parser generator.
- **[Ch 11: Compilation Model](spec/11-compilation.md)** — The pipeline from source to WAT/WASM, including Tier 1 (static) and Tier 3 (runtime) contract classification.
- **[Ch 12: Runtime and Execution](spec/12-runtime.md)** — The wasmtime-based runtime providing effect implementations, linear memory management, and trap handling.

### Testing

Testing is organized in three layers: **unit tests** (1,943 tests across 20 files, testing compiler internals), a **conformance suite** (46 programs across 8 spec chapters, systematically validating every language feature against the spec), and **example programs** (18 end-to-end demos). The compiler has 90% code coverage, enforced by pre-commit hooks and [CI](.github/workflows/ci.yml) across 6 Python/OS combinations. Every commit validates all conformance programs, example programs, and 95 specification code blocks. See **[TESTING.md](TESTING.md)** for the full testing reference -- coverage tables, conformance suite details, CI pipeline, and infrastructure.

## Roadmap

Development follows an **interleaved spiral** — each phase adds a complete compiler layer with tests, docs, and working examples before moving to the next.

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
| C8.5 | — | **Completeness** — module refinements, lexical extensions, IO runtime | In progress |
| C9 | — | **Language design** — abilities, new effects, stdlib extensions | Planned |
| C10 | — | **Ecosystem** — package management and registry | Planned |

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

### Working on C8.5 — Completeness

Module refinements, lexical extensions, and IO runtime — completing the existing language before adding new features.

**Builtin extensions** — independent of each other, no module deps

- <del>[#199](https://github.com/aallan/vera/issues/199) numeric math builtins</del> ([v0.0.70](https://github.com/aallan/vera/releases/tag/v0.0.70))
- <del>[#200](https://github.com/aallan/vera/issues/200) parsing completeness (parse_int, parse_bool, safe parse_float64)</del> ([v0.0.77](https://github.com/aallan/vera/releases/tag/v0.0.77))
- <del>[#198](https://github.com/aallan/vera/issues/198) string search and transformation builtins</del> ([v0.0.73](https://github.com/aallan/vera/releases/tag/v0.0.73))
- <del>[#208](https://github.com/aallan/vera/issues/208) numeric type conversions</del> ([v0.0.71](https://github.com/aallan/vera/releases/tag/v0.0.71))
- <del>[#209](https://github.com/aallan/vera/issues/209) array construction builtins (range, append, concat)</del>
- <del>[#210](https://github.com/aallan/vera/issues/210) from_char_code builtin</del> ([v0.0.74](https://github.com/aallan/vera/releases/tag/v0.0.74))
- <del>[#212](https://github.com/aallan/vera/issues/212) Float64 special value operations (is_nan, is_infinite)</del> ([v0.0.72](https://github.com/aallan/vera/releases/tag/v0.0.72))
- <del>[#213](https://github.com/aallan/vera/issues/213) string_repeat builtin</del> ([v0.0.75](https://github.com/aallan/vera/releases/tag/v0.0.75))
- <del>[#230](https://github.com/aallan/vera/issues/230) string interpolation</del> ([v0.0.76](https://github.com/aallan/vera/releases/tag/v0.0.76))
- [#231](https://github.com/aallan/vera/issues/231) regex support
- [#232](https://github.com/aallan/vera/issues/232) URL parsing and construction builtins
- [#234](https://github.com/aallan/vera/issues/234) base64 encoding and decoding

**Module system** — sequential dependency (#187 before #127)

- [#187](https://github.com/aallan/vera/issues/187) module-qualified call disambiguation via name mangling
- [#127](https://github.com/aallan/vera/issues/127) module re-exports

**IO runtime** — host bindings for file and stdin access

- <del>[#135](https://github.com/aallan/vera/issues/135) IO operations (read_line, read_file, write_file, args, exit, get_env)</del> ([v0.0.66](https://github.com/aallan/vera/releases/tag/v0.0.66))
- <del>[#216](https://github.com/aallan/vera/issues/216) string escape sequences (\n, \t, etc.) not parsed in string literals</del> ([v0.0.67](https://github.com/aallan/vera/releases/tag/v0.0.67))

**Testing improvements** — sequential dependency (#169 before #170)

- [#169](https://github.com/aallan/vera/issues/169) `vera test` Float64 and compound type input generation
- [#170](https://github.com/aallan/vera/issues/170) `vera test` hypothesis integration and advanced testing

### C9 — Language design

New effects, types, abilities, and standard library extensions (spec §0.8).

**Language features** — new syntax and type system extensions

- [#60](https://github.com/aallan/vera/issues/60) abilities and type constraints
- [#226](https://github.com/aallan/vera/issues/226) typed holes for partial program generation

**Effects** — new effect types for agent workloads

- [#57](https://github.com/aallan/vera/issues/57) `<Http>` network access effect
- [#59](https://github.com/aallan/vera/issues/59) `<Async>` futures and promises
- [#61](https://github.com/aallan/vera/issues/61) `<Inference>` LLM inference effect
- [#227](https://github.com/aallan/vera/issues/227) `<Timeout>` timeout and cancellation effects
- [#228](https://github.com/aallan/vera/issues/228) `<WebSocket>` / `<SSE>` streaming client effects
- [#229](https://github.com/aallan/vera/issues/229) `<DB>` database access effect

**Standard library** — types, data formats, and host-provided functions

- [#62](https://github.com/aallan/vera/issues/62) standard library collections (Set, Map, Decimal)
- [#133](https://github.com/aallan/vera/issues/133) array operations (map, fold, slice)
- [#58](https://github.com/aallan/vera/issues/58) JSON standard library type
- [#147](https://github.com/aallan/vera/issues/147) Markdown standard library type
- [#211](https://github.com/aallan/vera/issues/211) Option and Result combinators
- [#233](https://github.com/aallan/vera/issues/233) date and time handling (ISO 8601)
- [#235](https://github.com/aallan/vera/issues/235) cryptographic hashing (SHA-256, HMAC)
- [#236](https://github.com/aallan/vera/issues/236) CSV parsing and generation

### C10 — Tooling and ecosystem

**Agent tooling** — feedback loops that determine whether agents can use Vera at all

- [#222](https://github.com/aallan/vera/issues/222) LSP server
- <del>[#223](https://github.com/aallan/vera/issues/223) conformance test suite</del> ([v0.0.68](https://github.com/aallan/vera/releases/tag/v0.0.68))
- [#224](https://github.com/aallan/vera/issues/224) REPL (interactive read-eval-print loop)
- [#225](https://github.com/aallan/vera/issues/225) benchmark suite for LLM code generation

**Compilation and runtime**

- [#56](https://github.com/aallan/vera/issues/56) incremental compilation
- [#237](https://github.com/aallan/vera/issues/237) WASI 0.2 compliance
- [#238](https://github.com/aallan/vera/issues/238) Component Model (WIT) interop
- [#239](https://github.com/aallan/vera/issues/239) resource limit configuration (fuel, memory, timeout)
- [#163](https://github.com/aallan/vera/issues/163) standalone WASM runtime package

**Ecosystem**

- [#130](https://github.com/aallan/vera/issues/130) package system and registry
- [#143](https://github.com/aallan/vera/issues/143) comprehensive example programs
- [#181](https://github.com/aallan/vera/issues/181) signature refactoring (mechanical slot index rewriting)
- [#183](https://github.com/aallan/vera/issues/183) human-readable slot annotations (display layer for `@T.n` references)

### Where this is going

The features on the C9 roadmap -- `<Http>` ([#57](https://github.com/aallan/vera/issues/57)), `<Inference>` ([#61](https://github.com/aallan/vera/issues/61)), and the `Markdown` type ([#147](https://github.com/aallan/vera/issues/147)) -- converge into a single design goal: an LLM should be able to write a short Vera function that searches the web, feeds the results into another model, and returns typed, contract-checked output. No scaffolding, no untyped string wrangling, no unchecked side effects.

A research function that searches YouTube, summarises the results via LLM inference, and returns structured Markdown might look like this:

```vera
public fn research_topic(@String -> @MdBlock)
  requires(length(@String.0) > 0)
  ensures(md_has_heading(@MdBlock.result, 1))
  effects(<Http, Inference>)
{
  let @Array<MdBlock> = youtube_search(@String.0, 5);
  let @String = md_render_all(@Array<MdBlock>.0);
  let @String = complete("Summarise this research:\n" ++ @String.0);
  md_parse(@String.0)
}
```

Five lines of logic. The signature carries all the ceremony -- parameter types, contracts, effect declarations -- so the body reads like a pipeline. The `<Http, Inference>` effect annotation means a caller that only permits `<Http>` cannot invoke this function, and an effect handler can mock both effects for deterministic testing. The postcondition `md_has_heading(@MdBlock.result, 1)` constrains the shape of the LLM response at the type level: if the model produces output that lacks a top-level heading, the contract fails.

This is what "designed for LLMs to write" means in practice: the language makes the intent machine-checkable, the side effects explicit, and the output structurally typed -- in fewer lines than most languages need for a HTTP request.

## Getting Started

### Prerequisites

- Python 3.11+
- Git

The install step pulls in several dependencies via pip — [Lark](https://github.com/lark-parser/lark) (parser generator), [Z3](https://github.com/Z3Prover/z3) (SMT solver for contract verification), and [wasmtime](https://wasmtime.dev/) (WASM runtime for compilation and execution). These all install into the virtual environment and don't require separate system packages.

### Installation

```bash
git clone https://github.com/aallan/vera.git
cd vera
python -m venv .venv
source .venv/bin/activate
pip install -e ".[dev]"
```

### Check a program

```
$ vera check examples/absolute_value.vera
OK: examples/absolute_value.vera
```

`vera check` parses the file, builds the AST, and runs the type checker. `vera typecheck` is an explicit alias for the same command.

### Verify contracts

```
$ vera verify examples/safe_divide.vera
OK: examples/safe_divide.vera
Verification: 4 verified (Tier 1)
```

`vera verify` runs the type checker and then verifies contracts using Z3. Tier 1 contracts (decidable arithmetic, comparisons, Boolean logic, match expressions, ADT constructors, and decreases clauses) are proved automatically. Contracts that Z3 cannot decide are reported as Tier 3 (runtime checks) with a warning. Across all 18 examples, 118 of 122 contracts (96.7%) are verified statically.

### Format a program

```bash
vera fmt examples/absolute_value.vera
```

`vera fmt` prints the canonical form of a Vera source file to stdout. Add `--write` to reformat in place, or `--check` to verify a file is already canonical (exits 1 if not):

```bash
vera fmt --write examples/absolute_value.vera   # reformat in place
vera fmt --check examples/absolute_value.vera   # check only (for CI)
```

### Compile a program

```
$ vera compile examples/hello_world.vera
Compiled: examples/hello_world.wasm (1 function exported)
```

`vera compile` runs the full pipeline (parse → typecheck → verify → compile) and writes a `.wasm` binary. Add `--wat` to print the human-readable WAT text instead:

```bash
vera compile --wat examples/hello_world.vera
```

### Run a program

```
$ vera run examples/hello_world.vera
Hello, World!
```

`vera run` compiles and executes the program. By default it calls `main`. Use `--fn` to call a different function, and pass arguments after `--`:

```
$ vera run examples/factorial.vera --fn factorial -- 5
120
```

### Parse a program

```bash
vera parse examples/safe_divide.vera
```

This prints the parse tree, useful for debugging syntax issues.

### Inspect the AST

```bash
vera ast examples/factorial.vera
```

This prints the typed abstract syntax tree. Add `--json` for JSON output:

```bash
vera ast --json examples/factorial.vera
```

### Test contracts

```
$ vera test examples/safe_divide.vera
Testing safe_divide: 100 trials, all passed (Tier 1)
Testing main: 1 trial, all passed (Tier 1)
```

`vera test` generates test inputs from contracts using Z3, compiles the function to WASM, and executes it against the generated inputs. This validates that contracts and implementations agree without writing any test cases manually. Add `--json` for machine-readable results, or `--trials N` to control the number of test inputs per function.

### Machine-readable diagnostics

All diagnostic commands support `--json` output for agent and tool consumption:

```bash
vera check --json file.vera     # type errors as structured JSON
vera verify --json file.vera    # verification results as structured JSON
vera test --json file.vera      # test results as structured JSON
```

The JSON output includes exact source locations, error codes, rationale, fix suggestions, and spec references — designed for LLM feedback loops where the agent reads the error, corrects the code, and re-checks.

### Run the tests

```bash
pytest tests/ -v
```

### Development setup

For contributors, install pre-commit hooks to catch issues before they reach CI:

```bash
pre-commit install
```

This runs mypy, pytest, trailing whitespace checks, and validates all examples on every commit.

### Write a program

Create a file `hello.vera`:

```vera
private fn double(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 * 2)
  effects(pure)
{
  @Int.0 * 2
}
```

Then check it:

```bash
vera check hello.vera
```

See `examples/` for more programs, and the [language specification](spec/) for the full language reference.

## For Agents

Vera ships with three files for LLM agents:

- [`SKILL.md`](SKILL.md) — Complete language reference for agents writing Vera code. Covers syntax, slot references, contracts, effects, common mistakes, and working examples.
- [`AGENTS.md`](AGENTS.md) — Instructions for any agent system (Copilot, Cursor, Windsurf, custom). Covers both writing Vera code and working on the compiler.
- [`CLAUDE.md`](CLAUDE.md) — Project orientation for Claude Code. Key commands, layout, workflows, and invariants.

### Giving Your Agent the Vera Skill

#### Claude Code

If you're working in this repo, Claude Code discovers `SKILL.md` and `CLAUDE.md` automatically. For other projects, install the skill manually:

```bash
mkdir -p ~/.claude/skills/vera-language
cp /path/to/vera/SKILL.md ~/.claude/skills/vera-language/SKILL.md
```

The skill is now available across all your Claude Code projects. Claude will read it automatically when you ask it to write Vera code.

#### Claude.ai

1. Create a folder called `vera-language` containing a single file named `Skill.md` (copy `SKILL.md` into this folder)
2. Compress the folder into a ZIP file — the structure should be `vera-language.zip → vera-language/ → Skill.md`
3. In Claude.ai, go to **Settings > Capabilities > Skills** and upload the ZIP file
4. The skill is now available in your conversations — Claude will use it automatically when you ask it to write Vera code

#### Claude API

```python
from anthropic.lib import files_from_dir

client = anthropic.Anthropic()

skill = client.beta.skills.create(
    display_title="Vera Language",
    files=[("SKILL.md", open("SKILL.md", "rb"))],
    betas=["skills-2025-10-02"],
)

# Use in a message
response = client.beta.messages.create(
    model="claude-sonnet-4-6",
    max_tokens=4096,
    betas=["code-execution-2025-08-25", "skills-2025-10-02"],
    container={"skills": [{"type": "custom", "skill_id": skill.id, "version": "latest"}]},
    tools=[{"type": "code_execution_20250825", "name": "code_execution"}],
    messages=[{"role": "user", "content": "Write a Vera function that..."}],
)
```

#### Other Models

Point the model at `SKILL.md` by including it in the system prompt, as a file attachment, or as a retrieval document. The file is self-contained and works with any model that can read markdown.

### Agent Quickstart

If you are an LLM agent, read [`SKILL.md`](SKILL.md) for the full language reference. Here is the minimal workflow:

Install (if not already available):

```bash
git clone https://github.com/aallan/vera.git && cd vera
python -m venv .venv && source .venv/bin/activate && pip install -e .
```

Write a `.vera` file, then check, verify, and run it:

```bash
vera check your_file.vera              # type-check
vera verify your_file.vera             # type-check + verify contracts
vera test your_file.vera               # contract-driven testing via Z3 + WASM
vera compile your_file.vera            # compile to .wasm binary
vera run your_file.vera                # compile + execute
vera run your_file.vera --fn f -- 42   # call function f with argument 42
vera fmt your_file.vera                # format to canonical form (stdout)
vera verify --json your_file.vera      # verify with JSON diagnostics
```

If the check or verification fails, the error message tells you exactly what went wrong and how to fix it. Feed the error back into your context and correct the code. Use `--json` for machine-readable output that includes structured diagnostics with location, rationale, and fix suggestions.

**Essential rules:**
1. Every function needs `requires()`, `ensures()`, and `effects()` between the signature and body
2. Use `@Type.index` to reference bindings — `@Int.0` is the most recent `Int`, `@Int.1` is the one before that
3. Declare all effects — `effects(pure)` for pure functions, `effects(<IO>)` for IO, etc.
4. Recursive functions need a `decreases()` clause
5. Match expressions must be exhaustive

## Project Structure

```
vera/
├── SKILL.md                       # Language reference for LLM agents
├── AGENTS.md                      # Instructions for any AI agent system
├── CLAUDE.md                      # Project orientation for Claude Code
├── TESTING.md                     # Testing reference (single source of truth)
├── CONTRIBUTING.md                # Contributor guidelines
├── CODE_OF_CONDUCT.md             # Contributor Covenant
├── SECURITY.md                    # Security policy
├── CHANGELOG.md                   # Version history
├── LICENSE                        # MIT licence
├── pyproject.toml                 # Package configuration
├── .pre-commit-config.yaml        # Pre-commit hook configuration
├── .github/workflows/             # CI pipeline
│   ├── ci.yml                     #   Tests, type checking, linting
│   └── codeql.yml                 #   GitHub CodeQL analysis
├── spec/                          # Language specification (13 chapters)
│   ├── 00-introduction.md         # Design goals and philosophy
│   ├── 01-lexical-structure.md    # Tokens, operators, formatting rules
│   ├── 02-types.md                # Type system with refinement types
│   ├── 03-slot-references.md      # The @T.n reference system
│   ├── 04-expressions.md          # Expressions and statements
│   ├── 05-functions.md            # Function declarations and contracts
│   ├── 06-contracts.md            # Verification system
│   ├── 07-effects.md              # Algebraic effect system
│   ├── 08-modules.md              # Module system
│   ├── 09-standard-library.md     # Built-in types, effects, functions
│   ├── 10-grammar.md              # Formal EBNF grammar
│   ├── 11-compilation.md          # Compilation model and WASM target
│   └── 12-runtime.md              # Runtime execution and host bindings
├── vera/                          # Reference compiler (Python)
│   ├── __init__.py                # Version constant
│   ├── README.md                  # Compiler architecture docs
│   ├── grammar.lark               # Lark LALR(1) grammar
│   ├── parser.py                  # Parser module
│   ├── ast.py                     # Typed AST node definitions
│   ├── transform.py               # Lark parse tree → AST transformer
│   ├── types.py                   # Internal type representation
│   ├── registration.py            # Function signature registration
│   ├── environment.py             # Type environment and slot resolution
│   ├── checker/                   # Type checker (mixin package)
│   │   ├── core.py                #   Orchestration, diagnostics, contracts
│   │   ├── resolution.py          #   AST TypeExpr → semantic Type
│   │   ├── modules.py             #   Cross-module registration
│   │   ├── registration.py        #   Pass 1 forward declarations
│   │   ├── expressions.py         #   Expression synthesis, operators
│   │   ├── calls.py               #   Function/constructor/module calls
│   │   └── control.py             #   If/match, patterns, handlers
│   ├── smt.py                     # Z3 SMT translation layer
│   ├── verifier.py                # Contract verifier
│   ├── wasm/                     # WASM translation layer (8 modules)
│   │   ├── context.py            #   Composed WasmContext, expression dispatcher
│   │   ├── helpers.py            #   WasmSlotEnv, StringPool, type mapping helpers
│   │   ├── inference.py          #   Type inference and utilities
│   │   ├── operators.py          #   Binary/unary operators, quantifiers
│   │   ├── calls.py              #   Function calls, effect handlers
│   │   ├── closures.py           #   Closures, free variable analysis
│   │   └── data.py               #   Constructors, match, arrays
│   ├── codegen/                    # Code generation orchestrator (11 modules)
│   │   ├── api.py               #   Public API, compile(), execute()
│   │   ├── core.py              #   Composed CodeGenerator class
│   │   ├── modules.py           #   Cross-module call detection
│   │   ├── registration.py      #   Function/ADT registration
│   │   ├── monomorphize.py      #   Generic instantiation
│   │   ├── functions.py         #   Function body compilation
│   │   ├── closures.py          #   Closure lifting
│   │   ├── contracts.py         #   Runtime contract insertion
│   │   ├── assembly.py          #   WAT module assembly
│   │   └── compilability.py     #   Compilability checks
│   ├── tester.py                  # Contract-driven testing engine
│   ├── resolver.py                # Module resolver
│   ├── formatter.py               # Canonical code formatter
│   ├── errors.py                  # LLM-oriented diagnostics
│   └── cli.py                     # Command-line interface
├── examples/                      # 18 example Vera programs
├── tests/                         # Test suite (see TESTING.md)
└── scripts/                       # CI and validation scripts
    ├── check_examples.py          # Verify all .vera examples
    ├── check_spec_examples.py     # Verify spec code blocks parse
    ├── check_readme_examples.py   # Verify README code blocks parse
    ├── check_skill_examples.py    # Verify SKILL.md code blocks parse
    ├── check_version_sync.py      # Verify version consistency
    └── fix_allowlists.py          # Auto-fix stale allowlist line numbers
```

For compiler architecture, pipeline internals, design patterns, and how to extend the compiler, see [`vera/README.md`](vera/README.md).

## Technical Decisions

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
| Diagnostics | Structured JSON with `--json` flag | Machine-readable errors with locations, fix suggestions, and spec references |
| Testing | Contract-driven via Z3 + WASM (`vera test`) | Generate test inputs from contracts, no manual test cases |
| Formatting | Canonical formatter (`vera fmt`) | One canonical form, enforced by tooling |
| Error handling | `Result<T, E>` ADTs, no exceptions | Errors are values; models handle every case via `match` |
| Type annotations | Mandatory on all parameters and returns | No type inference across boundaries — explicitness over convenience |
| Verification tiers | Proven (Tier 1) or runtime-checked (Tier 3) | Every contract is checked; unproven ones become runtime assertions, never silently dropped |
| Naming | No user-chosen variable names | `@T.n` indices are the only binding mechanism — no naming decisions to hallucinate |

## Prior Art

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

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines on how to contribute to Vera. For compiler internals — pipeline architecture, module map, design patterns, and how to extend the compiler — see [vera/README.md](vera/README.md).


## Changelog

See [CHANGELOG.md](CHANGELOG.md) for a history of changes.

## Licence

Vera is licensed under the [MIT License](LICENSE).

Copyright &copy; 2026 Alasdair Allan

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
