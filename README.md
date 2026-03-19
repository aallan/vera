# Vera

[![Vera — A language designed for machines to write](assets/vera-social-preview.jpg)](https://veralang.dev)

[![CodeRabbit Pull Request Reviews](https://img.shields.io/coderabbit/prs/github/aallan/vera?utm_source=oss&utm_medium=github&utm_campaign=aallan%2Fvera&labelColor=171717&color=FF570A&link=https%3A%2F%2Fcoderabbit.ai&label=CodeRabbit+Reviews)](https://coderabbit.ai)
[![codecov](https://codecov.io/gh/aallan/vera/graph/badge.svg)](https://codecov.io/gh/aallan/vera)

**Vera** (v-EER-a) is a programming language designed for large language models to write. The name comes from the Latin *veritas* (truth). Programs compile to WebAssembly and run at the command line or in the browser.

```vera
public fn clamp(@Int, @Int, @Int -> @Int)
  requires(@Int.1 <= @Int.0)
  ensures(@Int.result >= @Int.1)
  ensures(@Int.result <= @Int.0)
  effects(pure)
{
  if @Int.2 < @Int.1 then {
    @Int.1
  } else {
    if @Int.2 > @Int.0 then {
      @Int.0
    } else {
      @Int.2
    }
  }
}
```

There are no variable names. `@Int.0` is the most recent `Int` binding; `@Int.2` is two bindings back. The `requires` clause is a precondition the compiler checks at every call site. The two `ensures` clauses are postconditions the SMT solver proves statically. The function is `pure` no side effects of any kind. If any of this is wrong, the code does not compile.

## Why?

Programming languages have always co-evolved with their users. Assembly emerged from hardware constraints. C from operating systems. Python from productivity needs. If models become the primary authors of code, it follows that languages should adapt to that too.

The evidence suggests the biggest problem models face isn't syntax, instead it's coherence over scale. Models struggle with maintaining invariants across a codebase, understanding the ripple effects of changes, and reasoning about state over time. They're pattern matchers optimising for local plausibility, not architects holding the entire system in mind. The [empirical literature](https://arxiv.org/abs/2307.12488) shows that models are particularly vulnerable to naming-related errors like choosing misleading names, reusing names incorrectly, and losing track of which name refers to which value.

Vera addresses this by making everything explicit and verifiable. The model doesn't need to be right, it needs to be checkable. Names are replaced by structural references. Contracts are mandatory. Effects are typed. Every function is a specification that the compiler can verify against its implementation.

### Design Principles

Vera adheres to six main design principles:

1. **Checkability over correctness.** Code that can be mechanically checked. When wrong, the compiler provides a natural language explanation of the error with a concrete fix — an instruction, not a status report.
2. **Explicitness over convenience.** All state changes declared. All effects typed. All function contracts mandatory. No implicit behaviour.
3. **One canonical form.** Every construct has exactly one textual representation. No style choices.
4. **Structural references over names.** Bindings referenced by type and positional index (`@T.n`), not arbitrary names.
5. **Contracts as the source of truth.** Every function declares what it requires and guarantees. The compiler verifies statically where possible.
6. **Constrained expressiveness.** Fewer valid programs means fewer opportunities for the model to be wrong.

See the **[FAQ](FAQ.md)** for deeper questions about the design — why no variable names, what gets verified, how Vera compares to Dafny/Lean/Koka/F*, and the empirical evidence behind the design choices.


## What Vera Looks Like

Vera has a number of key features:

- **No variable names** — typed De Bruijn indices (`@T.n`) replace traditional variable names
- **Full contracts** — mandatory preconditions, postconditions, invariants, and effect declarations on all functions
- **Algebraic effects** — declared, typed, and handled explicitly; pure by default
- **Refinement types** — types that express constraints like "a list of positive integers of length n"
- **Async/await** — `Future<T>` with declared `<Async>` effects
- **Typed Markdown** — built-in `MdBlock`/`MdInline` ADTs for structured document processing
- **String interpolation** — `"value: \(@Int.0)"` with auto-conversion for primitive types
- **Three-tier verification** — static verification via Z3, guided verification with hints, runtime fallback
- **Diagnostics as instructions** — every error message is a natural language explanation with a concrete fix
- **Contract-driven testing** — `vera test` generates inputs from contracts via Z3, no manual test cases
- **Compiles to WebAssembly** — portable, sandboxed execution at the command line and in the browser
- **Browser runtime** — `vera compile --target browser` produces a self-contained bundle that runs in any browser
- **Module system** — cross-file imports, visibility enforcement, cross-module contract verification
- **Canonical formatter** — `vera fmt` enforces one representation; no style debates

### Contracts the compiler proves

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

### Refinement types — constraints at the type level

Types can carry predicates. `PosInt` is not just `Int` — it's an integer the compiler has proved is positive. `NonEmptyArray` is an array the compiler has proved is non-empty. Indexing into it is safe by construction.

```vera
type PosInt = { @Int | @Int.0 > 0 };
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 };
type NonEmptyArray = { @Array<Int> | array_length(@Array<Int>.0) > 0 };

public fn safe_divide(@Int, @PosInt -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 / @PosInt.0
}

private fn head(@NonEmptyArray -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @NonEmptyArray.0[0]
}
```

> [`examples/refinement_types.vera`](examples/refinement_types.vera) — run with `vera run examples/refinement_types.vera --fn test_refine`

### Algebraic data types and pattern matching

User-defined types with recursive structure. `decreases(@List<Int>.0)` is a termination proof — the compiler verifies that the argument shrinks on every recursive call.

```vera
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

public fn sum(@List<Int> -> @Int)
  requires(true)
  ensures(true)
  decreases(@List<Int>.0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> @Int.0 + sum(@List<Int>.0)
  }
}
```

> [`examples/list_ops.vera`](examples/list_ops.vera) — run with `vera run examples/list_ops.vera --fn test_list`

### Effects — explicit state, no hidden mutation

Vera is pure by default. State changes must be declared as effects. `effects(<State<Int>>)` says this function reads and writes an integer. The `ensures` clause specifies exactly how the state changes. Handlers provide the actual state implementation — the function `run_counter` eliminates the effect entirely and is pure.

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

public fn run_counter(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    put(0);
    put(get(()) + 1);
    put(get(()) + 1);
    put(get(()) + 1);
    get(())
  }
}
```

> [`examples/effect_handler.vera`](examples/effect_handler.vera) — run with `vera run examples/effect_handler.vera --fn run_counter`

### Exceptions as effects

The `Exn<E>` effect models exceptions with a typed error value. Unlike most languages, exceptions are explicit in the type signature and must be handled by the caller. The handler catches the thrown value and returns a fallback — `safe_div` is pure because the effect has been discharged.

```vera
effect Exn<E> {
  op throw(E -> Never);
}

private fn checked_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Int>>)
{
  if @Int.1 == 0 then { throw(0 - 1) } else { @Int.0 / @Int.1 }
}

public fn safe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 }
  } in {
    checked_div(@Int.0, @Int.1)
  }
}
```

> [`examples/effect_handler.vera`](examples/effect_handler.vera) — run with `vera run examples/effect_handler.vera --fn safe_div -- 10 0`

### String interpolation and IO

`IO.print` is an effect operation. The `\(@Int.0)` syntax interpolates values into strings, auto-converting primitive types. `effects(<IO, Async>)` declares both IO and async effects — the compiler rejects any call to this function from a context that doesn't permit both.

```vera
effect IO {
  op print(String -> Unit);
}

private fn roundtrip(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(<Async>)
{
  let @Future<Int> = async(@Int.0);
  await(@Future<Int>.0)
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO, Async>)
{
  let @Int = roundtrip(42);
  IO.print("roundtrip(42) = \(@Int.0)");
  ()
}
```

> [`examples/async_futures.vera`](examples/async_futures.vera) — run with `vera run examples/async_futures.vera`

### Recursion as iteration

Vera has no `for` or `while` loops — iteration is always recursion. The `loop` function calls itself with `@Nat.0 + 1` until it reaches the bound. This is the standard Vera pattern for counted iteration.

Notice the separation of concerns: `fizzbuzz` is `effects(pure)` — the verifier can reason about it with SMT. `loop` has `effects(<IO>)` because it prints. `main` calls `loop` and also has `effects(<IO>)`. The effect annotations propagate up the call chain but never contaminate the pure classifier.

The contract `requires(@Nat.0 <= @Nat.1)` on `loop` ensures the function is only called with valid bounds — and since the recursive call passes `@Nat.0 + 1` where `@Nat.0 < @Nat.1`, the precondition is maintained at every step.

```vera
effect IO {
  op print(String -> Unit);
}

public fn fizzbuzz(@Nat -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Nat.0 % 15 == 0 then {
    "FizzBuzz"
  } else {
    if @Nat.0 % 3 == 0 then {
      "Fizz"
    } else {
      if @Nat.0 % 5 == 0 then {
        "Buzz"
      } else {
        "\(@Nat.0)"
      }
    }
  }
}

private fn loop(@Nat, @Nat -> @Unit)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  effects(<IO>)
{
  IO.print(string_concat(fizzbuzz(@Nat.0), "\n"));
  if @Nat.0 < @Nat.1 then {
    loop(@Nat.1, @Nat.0 + 1)
  } else {
    ()
  }
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  loop(100, 1)
}
```

> [`examples/fizzbuzz.vera`](examples/fizzbuzz.vera) — run with `vera run examples/fizzbuzz.vera`

### Typed Markdown

Vera has a built-in Markdown document type. `md_parse` produces a typed `MdBlock` tree; `md_has_heading` and `md_extract_code_blocks` query its structure. This is designed for agent workflows where an LLM produces structured output and the contract system validates its shape.

```vera
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Hello\n\n```vera\n42\n```");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      if md_has_heading(@MdBlock.0, 1) then {
        IO.print("Has title")
      } else {
        IO.print("No title")
      };
      let @Array<String> = md_extract_code_blocks(@MdBlock.0, "vera");
      IO.print("Code blocks: \(array_length(@Array<String>.0))");
      ()
    },
    Err(@String) -> { IO.print(@String.0); () }
  };
  ()
}
```

> [`examples/markdown.vera`](examples/markdown.vera) — run with `vera run examples/markdown.vera`

## Runs Everywhere

Vera compiles to WebAssembly. Programs run at the command line via wasmtime, or in the browser with a self-contained JavaScript runtime.

### Command line

```
$ vera run examples/hello_world.vera
Hello, World!

$ vera run examples/factorial.vera --fn factorial -- 10
3628800

$ vera run examples/effect_handler.vera --fn run_counter
3
```

### Browser

```
$ vera compile --target browser examples/hello_world.vera
Browser bundle: examples/hello_world_browser/
  module.wasm
  runtime.mjs
  index.html
```

This produces a ready-to-serve directory — no build step, no bundler, no dependencies. Serve it with any HTTP server (`python -m http.server`) and open `index.html`. The JavaScript runtime provides browser-appropriate implementations of all Vera host bindings: `IO.print` writes to the page, `IO.read_line` uses `prompt()`, and all other operations (State, contracts, Markdown) work identically to the Python runtime. Mandatory parity tests enforce this on every PR.

The runtime also works in Node.js:

```bash
node --experimental-wasm-exnref vera/browser/harness.mjs module.wasm
```

## What Errors Look Like

Traditional compilers produce diagnostics for humans: `expected token '{'`. Vera produces **instructions for the model that wrote the code**.

Every error includes what went wrong, why, how to fix it with a concrete code example, and a spec reference. The compiler's output is designed to be fed directly back to the model as corrective context.

```
[E001] Error at main.vera, line 14, column 1:

    {
    ^

  Function is missing its contract block. Every function in Vera must declare
  requires(), ensures(), and effects() clauses between the signature and the body.

  Vera requires all functions to have explicit contracts so that every function's
  behaviour is mechanically checkable.

  Fix:

    Add a contract block after the signature:

      private fn example(@Int -> @Int)
        requires(true)
        ensures(@Int.result >= 0)
        effects(pure)
      {
        ...
      }

  See: Chapter 5, Section 5.1 "Function Structure"
```

This principle applies at every stage: parse errors, type errors, effect mismatches, verification failures, and contract violations all produce natural language explanations with actionable fixes. Every diagnostic also has a stable error code (`E001`–`E702`) and is available as structured JSON via the `--json` flag.

## Getting Started

### Prerequisites

- Python 3.11+
- Git
- Node.js 22+ *(optional, for browser runtime and parity tests)*

### Installation

```bash
git clone https://github.com/aallan/vera.git
cd vera
python -m venv .venv
source .venv/bin/activate
pip install -e ".[dev]"
```

### The workflow

Write a `.vera` file, then check, verify, and run it:

```
$ vera check examples/absolute_value.vera
OK: examples/absolute_value.vera

$ vera verify examples/safe_divide.vera
OK: examples/safe_divide.vera
Verification: 4 verified (Tier 1)

$ vera compile examples/hello_world.vera
Compiled: examples/hello_world.wasm (1 function exported)

$ vera run examples/hello_world.vera
Hello, World!
```

`vera check` parses and type-checks. `vera verify` adds contract verification via Z3 — Tier 1 contracts (decidable arithmetic, comparisons, Boolean logic, ADTs, termination) are proved automatically; contracts Z3 cannot decide become Tier 3 runtime checks. `vera compile` writes a `.wasm` binary. `vera run` compiles and executes.

### More commands

```bash
vera run file.vera --fn f -- 42       # call function f with argument 42
vera compile --wat file.vera          # print human-readable WAT text
vera compile --target browser file.vera  # emit browser bundle
vera test file.vera                   # contract-driven testing via Z3 + WASM
vera fmt file.vera                    # format to canonical form (stdout)
vera fmt --write file.vera            # format in place
vera fmt --check file.vera            # check if canonical (for CI)
vera ast --json file.vera             # print typed AST as JSON
vera verify --json file.vera          # JSON diagnostics for agent feedback loops
```

`vera test` generates test inputs from contracts using Z3, compiles the function to WASM, and executes it against the generated inputs — validating that contracts and implementations agree without writing any test cases manually.

### Run the tests

```bash
pytest tests/ -v
```

For contributors, install pre-commit hooks:

```bash
pre-commit install
```

## For Agents

Vera ships with three files for LLM agents:

- [`SKILL.md`](SKILL.md) — Complete language reference. Covers syntax, slot references, contracts, effects, common mistakes, and working examples.
- [`AGENTS.md`](AGENTS.md) — Instructions for any agent system (Copilot, Cursor, Windsurf, custom). Covers both writing Vera code and working on the compiler.
- [`CLAUDE.md`](CLAUDE.md) — Project orientation for Claude Code. Key commands, layout, workflows, and invariants.

### Quickstart

Install, then write and run:

```bash
git clone https://github.com/aallan/vera.git && cd vera
python -m venv .venv && source .venv/bin/activate && pip install -e .
```

```bash
vera check your_file.vera              # type-check
vera verify your_file.vera             # type-check + verify contracts
vera test your_file.vera               # contract-driven testing
vera run your_file.vera                # compile + execute
vera verify --json your_file.vera      # JSON diagnostics for feedback loops
```

If the check or verification fails, the error message tells you exactly what went wrong and how to fix it. Feed the error back into your context and correct the code.

**Essential rules:**
1. Every function needs `requires()`, `ensures()`, and `effects()` between the signature and body
2. Use `@Type.index` to reference bindings — `@Int.0` is the most recent `Int`, `@Int.1` is the one before that
3. Declare all effects — `effects(pure)` for pure functions, `effects(<IO>)` for IO, etc.
4. Recursive functions need a `decreases()` clause
5. Match expressions must be exhaustive

### Giving Your Agent the Vera Skill

**Claude Code** — discovers `SKILL.md` and `CLAUDE.md` automatically in this repo. For other projects:

```bash
mkdir -p ~/.claude/skills/vera-language
cp /path/to/vera/SKILL.md ~/.claude/skills/vera-language/SKILL.md
```

**Claude.ai** — create a `vera-language` folder containing `Skill.md` (copy of `SKILL.md`), compress to ZIP, upload in **Settings > Capabilities > Skills**.

**Claude API** — see the [API skill documentation](https://docs.anthropic.com) for programmatic skill creation.

**Other models** — include `SKILL.md` in the system prompt, as a file attachment, or as a retrieval document.

## Project Status

Vera is in **active development** at v0.0.92. The reference compiler — parser, AST, type checker, contract verifier (Z3), WASM code generator, module system, browser runtime, and runtime contract insertion — is working. Programs compile to WebAssembly and execute via wasmtime or in the browser.

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

<details>
<summary><strong>Project Structure</strong></summary>

```
vera/
├── SKILL.md                       # Language reference for LLM agents
├── AGENTS.md                      # Instructions for any AI agent system
├── CLAUDE.md                      # Project orientation for Claude Code
├── FAQ.md                         # Frequently asked questions
├── TESTING.md                     # Testing reference (single source of truth)
├── CONTRIBUTING.md                # Contributor guidelines
├── CODE_OF_CONDUCT.md             # Contributor Covenant
├── SECURITY.md                    # Security policy
├── CHANGELOG.md                   # Version history
├── ROADMAP.md                     # Language roadmap
├── LICENSE                        # MIT licence
├── pyproject.toml                 # Package configuration
├── .pre-commit-config.yaml        # Pre-commit hook configuration
├── .github/workflows/             # CI pipeline
│   ├── ci.yml                     #   Tests, type checking, linting
│   └── codeql.yml                 #   GitHub CodeQL analysis
├── spec/                          # Language specification (13 chapters)
├── vera/                          # Reference compiler (Python)
│   ├── grammar.lark               # Lark LALR(1) grammar
│   ├── parser.py                  # Parser module
│   ├── ast.py                     # Typed AST node definitions
│   ├── transform.py               # Lark parse tree → AST transformer
│   ├── types.py                   # Internal type representation
│   ├── checker/                   # Type checker (mixin package)
│   ├── smt.py                     # Z3 SMT translation layer
│   ├── verifier.py                # Contract verifier
│   ├── wasm/                      # WASM translation layer (9 modules)
│   ├── codegen/                   # Code generation orchestrator (11 modules)
│   ├── markdown.py                # Python Markdown parser/renderer
│   ├── browser/                   # Browser runtime for compiled WASM
│   │   ├── runtime.mjs            #   Self-contained JS runtime
│   │   ├── harness.mjs            #   Node.js test harness
│   │   └── emit.py                #   Browser bundle emission
│   ├── tester.py                  # Contract-driven testing engine
│   ├── resolver.py                # Module resolver
│   ├── formatter.py               # Canonical code formatter
│   ├── errors.py                  # LLM-oriented diagnostics
│   └── cli.py                     # Command-line interface
├── examples/                      # 25 example Vera programs
├── tests/                         # Test suite (see TESTING.md)
└── scripts/                       # CI and validation scripts
```

</details>

### Compiler Architecture

For compiler architecture, pipeline internals, and how to extend the compiler, see [`vera/README.md`](vera/README.md).

### Testing

Testing is organized in three layers: **unit tests** (2,407 tests across 24 files, testing compiler internals and browser parity), a **conformance suite** (55 programs across 9 spec chapters, systematically validating every language feature against the spec), and **example programs** (25 end-to-end demos). The compiler has 91% code coverage, enforced by pre-commit hooks and [CI](.github/workflows/ci.yml) across 6 Python/OS combinations plus a dedicated browser parity job (Node.js 22). Every commit validates all conformance programs, example programs, and specification code blocks. See **[TESTING.md](TESTING.md)** for the full testing reference.

### Known Bugs and Limitations

#### Bugs

No open issues.

#### Limitations

| Limitation | Issue |
|-----------|-------|
| Incremental compilation | [#56](https://github.com/aallan/vera/issues/56) |
| Module re-exports | [#127](https://github.com/aallan/vera/issues/127) |
| Package system and registry | [#130](https://github.com/aallan/vera/issues/130) |
| LSP server | [#222](https://github.com/aallan/vera/issues/222) |
| REPL | [#224](https://github.com/aallan/vera/issues/224) |
| Typed holes for partial programs | [#226](https://github.com/aallan/vera/issues/226) |
| Date and time handling | [#233](https://github.com/aallan/vera/issues/233) |
| Cryptographic hashing | [#235](https://github.com/aallan/vera/issues/235) |
| CSV parsing and generation | [#236](https://github.com/aallan/vera/issues/236) |
| WASI 0.2 compliance | [#237](https://github.com/aallan/vera/issues/237) |
| Resource limits (fuel, memory, timeout) | [#239](https://github.com/aallan/vera/issues/239) |
| Combinator bare-constructor type inference | [#293](https://github.com/aallan/vera/issues/293) |
| Effect row variable unification | [#294](https://github.com/aallan/vera/issues/294) |

## Project Roadmap

Development follows an **interleaved spiral** — each phase adds a complete compiler layer with tests, docs, and working examples before moving to the next. See **[ROADMAP.md](ROADMAP.md)** for the full language roadmap.

The features on the roadmap — `<Http>` ([#57](https://github.com/aallan/vera/issues/57)), `<Inference>` ([#61](https://github.com/aallan/vera/issues/61)), and the already-implemented `Markdown` type ([#147](https://github.com/aallan/vera/issues/147)) — converge into a single design goal: an LLM should be able to write a short Vera function that searches the web, feeds the results into another model, and returns typed, contract-checked output. No scaffolding, no untyped string wrangling, no unchecked side effects.

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

Five lines of logic. The signature carries all the ceremony — parameter types, contracts, effect declarations — so the body reads like a pipeline. The `<Http, Inference>` effect annotation means a caller that only permits `<Http>` cannot invoke this function. The postcondition `md_has_heading(@MdBlock.result, 1)` constrains the shape of the LLM response at the type level: if the model produces output that lacks a top-level heading, the contract fails.

This is what "designed for LLMs to write" means in practice: the language makes the intent machine-checkable, the side effects explicit, and the output structurally typed — in fewer lines than most languages need for a HTTP request.

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
| Diagnostics | Structured JSON with `--json` flag | Machine-readable errors for LLM feedback loops |
| Testing | Contract-driven via Z3 + WASM (`vera test`) | Generate test inputs from contracts, no manual test cases |
| Formatting | Canonical formatter (`vera fmt`) | One canonical form, enforced by tooling |
| Data types | Algebraic data types + exhaustive `match` | No classes, no inheritance; compiler enforces every case is handled |
| Polymorphism | Monomorphized generics (`forall<T where Eq<T>>`) | No runtime dispatch; four built-in abilities (`Eq`, `Ord`, `Hash`, `Show`); types fully specialized at compile time |
| Collections | `Array<T>` with `map`, `filter`, `fold`, `slice` | Functional iteration — no mutation, no loop constructs |
| Error handling | `Result<T, E>` ADTs, no exceptions | Errors are values; models handle every case via `match` |
| Recursion | Explicit termination measures (`decreases`) | Compiler verifies termination via Z3; no unbounded loops |
| Naming | No user-chosen variable names | `@T.n` indices are the only binding mechanism |
| Run everywhere | Dual-target WASM (native + browser bundle) | Same program runs via `wasmtime` or in the browser with `--target browser` |

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

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines on how to contribute to Vera. For compiler internals, see [vera/README.md](vera/README.md).

## Changelog

See [CHANGELOG.md](CHANGELOG.md) for a history of changes.

## Licence

Vera is licensed under the [MIT License](LICENSE). All dependencies (direct and transitive) are MIT-compatible — licence compliance is enforced by CI and pre-commit hooks via `scripts/check_licenses.py`.

| Dependency | Licence | Role |
|-----------|---------|------|
| [Lark](https://github.com/lark-parser/lark) | MIT | LALR(1) parser generator |
| [z3-solver](https://github.com/Z3Prover/z3) | MIT | SMT solver for contract verification |
| [wasmtime](https://github.com/bytecodealliance/wasmtime) | Apache-2.0 | WebAssembly runtime |

Copyright &copy; 2026 Alasdair Allan

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
