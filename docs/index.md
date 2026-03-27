# Vera — A language designed for machines to write

> Vera is a statically typed, purely functional programming language designed for large language models to write. It uses typed slot references (`@T.n`) instead of variable names, requires contracts on every function, and compiles to WebAssembly.

**Current version:** [0.0.101](https://github.com/aallan/vera/releases/tag/v0.0.101)

## Why?

Programming languages have always co-evolved with their users. Assembly emerged from hardware constraints. C from operating systems. Python from productivity needs. If models become the primary authors of code, it follows that languages should adapt to that too.

The evidence suggests the biggest problem models face isn't syntax — it's coherence over scale. Models struggle with maintaining invariants across a codebase, understanding the ripple effects of changes, and reasoning about state over time.

## Design Principles

1. **Checkability over correctness** — Every program is machine-verifiable. The compiler proves properties via Z3, not just checks syntax.
2. **Explicitness over convenience** — No implicit state, no hidden control flow. Every effect is declared, every contract is visible.
3. **One canonical form** — The formatter produces a single representation. No style debates, no ambiguity.
4. **Structural references over names** — Typed De Bruijn indices (`@Int.0`) eliminate naming errors entirely.
5. **Contracts as the source of truth** — Preconditions, postconditions, and effect declarations are the specification. The compiler enforces them.
6. **Constrained expressiveness** — Fewer ways to write the same thing means fewer ways to get it wrong.

## Key Features

- **No variable names** — Typed slot references (`@Int.0`, `@String.1`) using De Bruijn indexing
- **Mandatory contracts** — `requires(...)`, `ensures(...)`, `effects(...)` on every function
- **Algebraic effects** — IO, Http, State, Exceptions, Async tracked in the type system
- **Z3 verification** — Contracts proved statically by the Z3 SMT solver
- **Contract-driven testing** — Z3 generates test inputs from contracts
- **WebAssembly** — Compiles to WASM, runs via wasmtime or in the browser
- **String interpolation** — `"value: \(@Int.0)"` with auto-conversion
- **Typed Markdown** — Parse and query Markdown documents with type safety
- **Pattern matching** — Exhaustive ADT matching with nested patterns
- **Generics** — Parametric polymorphism with monomorphization

## Quick Start

```bash
git clone https://github.com/aallan/vera.git && cd vera
python -m venv .venv && source .venv/bin/activate
pip install -e .
vera run examples/hello_world.vera
```

## Documentation

- [SKILL.md](https://raw.githubusercontent.com/aallan/vera/main/SKILL.md) — Complete language reference
- [AGENTS.md](https://raw.githubusercontent.com/aallan/vera/main/AGENTS.md) — Instructions for AI agents
- [FAQ](https://raw.githubusercontent.com/aallan/vera/main/FAQ.md) — Design rationale and comparisons
- [Specification](https://github.com/aallan/vera/tree/main/spec) — 13-chapter formal spec
- [Examples](https://github.com/aallan/vera/tree/main/examples) — 28 verified programs

## Links

- [GitHub](https://github.com/aallan/vera)
- [Releases](https://github.com/aallan/vera/releases)
- [Issues](https://github.com/aallan/vera/issues)
- [MIT License](https://github.com/aallan/vera/blob/main/LICENSE)
