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

> [`examples/increment.vera`](examples/increment.vera) — this example uses `State<Int>` effects, which require effect handler compilation ([#53](https://github.com/aallan/vera/issues/53)) before `vera run` can execute them

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
| C8 | v0.1.0 | **Polish** — refactoring, tooling, diagnostics, verification depth | In progress |
| C8.5 | — | **Completeness** — module refinements, lexical extensions, IO runtime | Planned |
| C9 | — | **Language design** — abilities, new effects, stdlib extensions | Planned |
| C10 | — | **Ecosystem** — package management and registry | Planned |

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
<summary>C6 — Codegen Completeness (<a href="https://github.com/aallan/vera/releases/tag/v0.0.10">v0.0.10</a>–<a href="https://github.com/aallan/vera/releases/tag/v0.0.24">v0.0.24</a>) ✓</summary>

C6 extended WASM compilation to all language constructs, working through the dependency graph from simplest to most complex. All 14 examples now compile.

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

### Working on C8 — Polish

C8 addresses the accumulated technical debt and UX gaps before v0.1.0. Open issues are grouped into sub-phases ordered by impact and dependency.

**C8a — Refactoring** — reduce file sizes to improve maintainability

- <del>[#99](https://github.com/aallan/vera/issues/99) decompose `checker.py` (~1,900 lines) into `checker/` submodules</del> ([v0.0.40](https://github.com/aallan/vera/releases/tag/v0.0.40))
- <del>[#100](https://github.com/aallan/vera/issues/100) decompose `wasm.py` (~2,300 lines) into `wasm/` submodules</del> ([v0.0.41](https://github.com/aallan/vera/releases/tag/v0.0.41))

**C8b — Diagnostics and tooling** — improve the developer (human and LLM) experience

- <del>[#112](https://github.com/aallan/vera/issues/112) informative runtime contract violation error messages</del> ([v0.0.42](https://github.com/aallan/vera/releases/tag/v0.0.42))
- <del>[#80](https://github.com/aallan/vera/issues/80) stable error code taxonomy for diagnostics</del> ([v0.0.43](https://github.com/aallan/vera/releases/tag/v0.0.43))
- <del>[#95](https://github.com/aallan/vera/issues/95) LALR grammar fix for module-qualified call syntax</del> ([v0.0.44](https://github.com/aallan/vera/releases/tag/v0.0.44))
- [#75](https://github.com/aallan/vera/issues/75) `vera fmt` canonical formatter
- [#79](https://github.com/aallan/vera/issues/79) `vera test` contract-driven testing

**C8c — Verification depth** — expand what the SMT solver can prove

- [#136](https://github.com/aallan/vera/issues/136) register `Diverge` as built-in effect
- [#137](https://github.com/aallan/vera/issues/137) register `Alloc` as built-in effect
- [#13](https://github.com/aallan/vera/issues/13) expand SMT decidable fragment (Tier 2 verification)
- [#45](https://github.com/aallan/vera/issues/45) `decreases` clause termination verification

**C8d — Type system** — close type-checking gaps

- [#20](https://github.com/aallan/vera/issues/20) TypeVar subtyping
- [#21](https://github.com/aallan/vera/issues/21) effect row unification and subeffecting
- [#55](https://github.com/aallan/vera/issues/55) minimal type inference

**C8e — Codegen gaps** — extend WASM compilation

- [#110](https://github.com/aallan/vera/issues/110) name collision detection for flat module compilation
- [#131](https://github.com/aallan/vera/issues/131) nested constructor pattern codegen
- [#53](https://github.com/aallan/vera/issues/53) `Exn<E>` and custom effect handler compilation
- [#51](https://github.com/aallan/vera/issues/51) garbage collection for WASM linear memory
- [#132](https://github.com/aallan/vera/issues/132) arrays of compound types in codegen
- [#52](https://github.com/aallan/vera/issues/52) dynamic string construction
- [#134](https://github.com/aallan/vera/issues/134) string built-in operations (length, concat, slice)
- [#106](https://github.com/aallan/vera/issues/106) universal to-string conversion (Show/Display)
- [#56](https://github.com/aallan/vera/issues/56) incremental compilation

### C8.5 — Completeness

Module refinements, lexical extensions, and IO runtime — completing the existing language before adding new features.

- [#127](https://github.com/aallan/vera/issues/127) module re-exports
- [#129](https://github.com/aallan/vera/issues/129) import aliasing
- [#128](https://github.com/aallan/vera/issues/128) wildcard exclusion in imports
- [#135](https://github.com/aallan/vera/issues/135) IO operations (read_line, read_file, write_file)
- [#139](https://github.com/aallan/vera/issues/139) scientific notation for float literals
- [#140](https://github.com/aallan/vera/issues/140) raw strings and multi-line string literals

### C9 — Language design

New effects, types, abilities, and standard library extensions (spec §0.8).

- [#60](https://github.com/aallan/vera/issues/60) abilities and type constraints
- [#62](https://github.com/aallan/vera/issues/62) standard library collections (Set, Map, Decimal)
- [#133](https://github.com/aallan/vera/issues/133) array operations (map, fold, slice)
- [#58](https://github.com/aallan/vera/issues/58) JSON standard library type
- [#57](https://github.com/aallan/vera/issues/57) `<Http>` network access effect
- [#59](https://github.com/aallan/vera/issues/59) `<Async>` futures and promises
- [#61](https://github.com/aallan/vera/issues/61) `<Inference>` LLM inference effect

### C10 — Ecosystem

- [#130](https://github.com/aallan/vera/issues/130) package system and registry

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
Verification: 2 verified (Tier 1)
```

`vera verify` runs the type checker and then verifies contracts using Z3. Tier 1 contracts (decidable arithmetic, comparisons, Boolean logic) are proved automatically. Contracts that Z3 cannot decide are reported as Tier 3 (runtime checks) with a warning.

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

- [`SKILLS.md`](SKILLS.md) — Complete language reference for agents writing Vera code. Covers syntax, slot references, contracts, effects, common mistakes, and working examples.
- [`AGENTS.md`](AGENTS.md) — Instructions for any agent system (Copilot, Cursor, Windsurf, custom). Covers both writing Vera code and working on the compiler.
- [`CLAUDE.md`](CLAUDE.md) — Project orientation for Claude Code. Key commands, layout, workflows, and invariants.

### Giving Your Agent the Vera Skill

#### Claude Code

If you're working in this repo, Claude Code discovers `SKILLS.md` and `CLAUDE.md` automatically. For other projects, install the skill manually:

```bash
mkdir -p ~/.claude/skills/vera-language
cp /path/to/vera/SKILLS.md ~/.claude/skills/vera-language/SKILL.md
```

The skill is now available across all your Claude Code projects. Claude will read it automatically when you ask it to write Vera code.

#### Claude.ai

1. Create a folder called `vera-language` containing a single file named `Skill.md` (copy `SKILLS.md` into this folder and rename it to `Skill.md`)
2. Compress the folder into a ZIP file — the structure should be `vera-language.zip → vera-language/ → Skill.md`
3. In Claude.ai, go to **Settings > Capabilities > Skills** and upload the ZIP file
4. The skill is now available in your conversations — Claude will use it automatically when you ask it to write Vera code

#### Claude API

```python
from anthropic.lib import files_from_dir

client = anthropic.Anthropic()

skill = client.beta.skills.create(
    display_title="Vera Language",
    files=[("SKILL.md", open("SKILLS.md", "rb"))],
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

Point the model at `SKILLS.md` by including it in the system prompt, as a file attachment, or as a retrieval document. The file is self-contained and works with any model that can read markdown.

### Agent Quickstart

If you are an LLM agent, read [`SKILLS.md`](SKILLS.md) for the full language reference. Here is the minimal workflow:

Install (if not already available):

```bash
git clone https://github.com/aallan/vera.git && cd vera
python -m venv .venv && source .venv/bin/activate && pip install -e .
```

Write a `.vera` file, then check, verify, and run it:

```bash
vera check your_file.vera              # type-check
vera verify your_file.vera             # type-check + verify contracts
vera compile your_file.vera            # compile to .wasm binary
vera run your_file.vera                # compile + execute
vera run your_file.vera --fn f -- 42   # call function f with argument 42
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
├── SKILLS.md                      # Language reference for LLM agents
├── AGENTS.md                      # Instructions for any AI agent system
├── CLAUDE.md                      # Project orientation for Claude Code
├── CONTRIBUTING.md                # Contributor guidelines
├── CHANGELOG.md                   # Version history
├── pyproject.toml                 # Package configuration
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
│   ├── codegen.py                 # Code generation orchestrator
│   ├── resolver.py                # Module resolver
│   ├── errors.py                  # LLM-oriented diagnostics
│   └── cli.py                     # Command-line interface
├── examples/                      # 14 example Vera programs
├── tests/                         # Test suite (951 tests)
├── scripts/                       # CI and validation scripts
│   ├── check_examples.py          # Verify all .vera examples
│   ├── check_spec_examples.py     # Verify spec code blocks parse
│   ├── check_readme_examples.py   # Verify README code blocks parse
│   └── check_version_sync.py      # Verify version consistency
└── runtime/                       # WASM runtime support (future)
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
| Memory | Managed (bump allocator; GC planned — [#51](https://github.com/aallan/vera/issues/51)) | Models focus on logic, not memory |
| Target | WebAssembly | Portable, sandboxed, no ambient capabilities |
| Compiler | Python reference impl | Correctness over performance — see [architecture docs](vera/README.md) |
| Evaluation | Strict (call-by-value) | Simpler for models to reason about |
| Diagnostics | Natural language with fix examples | Compiler output is the model's feedback loop |

## Prior Art

Vera draws on ideas from:

- [Eiffel](https://www.eiffel.org/) — Design by Contract (the originator of `require`/`ensure`)
- [Dafny](https://dafny.org/) — full functional verification with contracts
- [F*](https://fstar-lang.org/) — refinement types, algebraic effects, and SMT verification
- [Koka](https://koka-lang.github.io/koka/doc/book.html) — row-polymorphic algebraic effects
- [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/) — refinement types via SMT
- [Idris](https://www.idris-lang.org/) — totality checking and termination proofs
- [SPARK/Ada](https://www.adacore.com/about-spark) — contract-based industrial verification
- [bruijn](https://bruijn.marvinborner.de/) — De Bruijn indices as surface syntax

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
