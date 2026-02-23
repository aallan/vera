# Vera

**Vera** is a programming language designed for large language models (LLMs) to write, not humans.

The name comes from the Latin *veritas* (truth). In Vera, verification is a first-class citizen, not an afterthought.

## Why?

Programming languages have always co-evolved with their users. Assembly emerged from hardware constraints. C emerged from operating system needs. Python emerged from productivity needs. If models become the primary authors of software, it is consistent for languages to adapt to that.

The evidence suggests the biggest problem models face isn't syntax — it's **coherence over scale**. Models struggle with maintaining invariants across a codebase, understanding the ripple effects of changes, and reasoning about state over time. They're pattern matchers optimising for local plausibility, not architects holding the entire system in mind.

Vera addresses this by making everything explicit and verifiable. The model doesn't need to be right — it needs to be **checkable**.

## Design Principles

1. **Checkability over correctness.** Code that can be mechanically checked. When wrong, the compiler provides a precise, actionable signal.
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
- **Compiles to WebAssembly** — portable, sandboxed execution

## What Vera Looks Like

```vera
fn absolute_value(@Int -> @Nat)
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

```vera
fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

```vera
fn increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
```

## Project Status

Vera is in the **specification phase**. The language specification is being written alongside a reference compiler.

| Component | Status |
|-----------|--------|
| Language specification (Chapters 0-7, 10) | Draft |
| Language specification (Chapters 8-9, 11-12) | Not started |
| Reference compiler (Python) | Not started |
| WASM code generation | Not started |

## Project Structure

```
vera/
├── spec/                          # Language specification
│   ├── 00-introduction.md         # Design goals and philosophy
│   ├── 01-lexical-structure.md    # Tokens, operators, formatting rules
│   ├── 02-types.md                # Type system with refinement types
│   ├── 03-slot-references.md      # The @T.n reference system
│   ├── 04-expressions.md          # Expressions and statements
│   ├── 05-functions.md            # Function declarations and contracts
│   ├── 06-contracts.md            # Verification system
│   ├── 07-effects.md              # Algebraic effect system
│   └── 10-grammar.md              # Formal EBNF grammar
├── vera/                          # Reference compiler (Python)
├── runtime/                       # WASM runtime support
├── tests/                         # Test suite
└── examples/                      # Example Vera programs
```

## Technical Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Representation | Text with rigid syntax | One canonical form, no parsing ambiguity |
| References | `@T.n` typed De Bruijn indices | Eliminates naming coherence errors |
| Contracts | Mandatory on all functions | Programs must be checkable |
| Effects | Algebraic, row-polymorphic | All state and side effects explicit |
| Verification | Z3 via SMT-LIB | Industry standard, decidable fragment |
| Memory | Garbage collected | Models focus on logic, not memory |
| Target | WebAssembly | Portable, sandboxed, no ambient capabilities |
| Compiler | Python reference impl | Correctness over performance |
| Evaluation | Strict (call-by-value) | Simpler for models to reason about |

## Prior Art

Vera draws on ideas from:

- [Dafny](https://dafny.org/) — full functional verification with contracts
- [Koka](https://koka-lang.github.io/koka/doc/book.html) — row-polymorphic algebraic effects
- [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/) — refinement types via SMT
- [SPARK/Ada](https://www.adacore.com/about-spark) — contract-based industrial verification
- [bruijn](https://bruijn.marvinborner.de/) — De Bruijn indices as surface syntax

## Getting Started

The reference compiler is not yet implemented. For now, you can read the [language specification](spec/) to understand Vera's design.

### Prerequisites (for when the compiler is ready)

- Python 3.11+
- Z3 SMT solver (`pip install z3-solver`)
- Wasmtime (`pip install wasmtime`)

### Installation (future)

```bash
pip install vera
```

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines on how to contribute to Vera.

## License

Vera is licensed under the [MIT License](LICENSE).

## Changelog

See [CHANGELOG.md](CHANGELOG.md) for a history of changes.
