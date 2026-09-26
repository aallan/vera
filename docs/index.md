# Vera: a language designed for machines to write

> Vera is a programming language designed for large language models to write, not humans. It uses typed slot references (`@T.n`) instead of variable names, requires contracts on every function, and compiles to WebAssembly. Programs run at the command line via wasmtime or in any browser with a self-contained JavaScript runtime.

From the Latin *veritas*, meaning truth. Verification is built into the language from the ground up.

**Current version:** [0.2.0](https://github.com/aallan/vera/releases/tag/v0.2.0)  ·  [GitHub](https://github.com/aallan/vera)  ·  [SKILL.md](https://veralang.dev/SKILL.md) (agent language reference)

## Why?

Programming languages have always co-evolved with their users. Assembly emerged from hardware constraints. C from operating systems. Python from productivity needs. If models are becoming the main authors of code, the languages they write should change for them too.

> Syntax is the easy part. The hard problem for a model is coherence at scale: models are pattern matchers optimising for local plausibility, not architects holding the whole system in mind.

[Research on model-written code](https://arxiv.org/abs/2307.12488) finds that names are a particular weakness. Models pick misleading names, reuse names wrongly, and lose track of which name refers to which value. Vera takes the variable names away.

The model doesn't need to be right. It needs to be *checkable*. Structural references replace names. Contracts are mandatory. Effects are typed. Every function is a specification the compiler checks against its implementation, proving what it can with Z3 and compiling runtime checks for most of the rest.

![The loop: the model writes Vera with mandatory contracts, and the compiler type-checks it, proves contracts with Z3 and guards most of the rest at run time. When the model is wrong the diagnostics go back to it with a description, rationale, fix and spec reference; when the proofs hold, the program ships as one .wasm for the command line and the browser, or as a WASI component.](https://veralang.dev/loop-web.svg)

The [FAQ](https://raw.githubusercontent.com/aallan/vera/main/FAQ.md) goes deeper into the design: why there are no variable names, what gets verified, and how Vera compares with Dafny, Lean and Koka.

## What Vera Looks Like

Nothing is implicit. The signature declares types, preconditions, postconditions and effects, and `vera verify` proves this contract with Z3 before the program ever runs. A zero divisor the verifier can find is refused at compile time (`E526`) rather than left to crash at run time.

<!-- vera:run fn="safe_divide" args="2 10" stdout="5" -->
```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

Read the slots. `@Int.1` is the first parameter and `@Int.0` the second: De Bruijn indexing, most recent first. With no variable names there is no naming bug to make, since every reference is typed and positional. The `requires` clause is what makes the division safe. With it, the division is proved at compile time; without it, the compiler refuses the program with `E526` and a counterexample. [examples/safe_divide.vera](https://github.com/aallan/vera/blob/main/examples/safe_divide.vera).

<!-- vera:run fn="fizzbuzz" args="15" stdout="FizzBuzz" -->
```vera
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
```

A program everyone knows. Interpolation takes the slot reference directly, `"\(@Nat.0)"`, and converts it to a string. There are no naming decisions to make, and none to hallucinate. [examples/fizzbuzz.vera](https://github.com/aallan/vera/blob/main/examples/fizzbuzz.vera).

<!-- vera:no-run category="api-key" reason="calls Inference, which needs a provider key" -->
```vera
public fn classify_sentiment(@String -> @Result<String, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Inference>)
{
  let @String = string_concat("Classify as Positive, Negative, or Neutral: ", @String.0);
  Inference.complete(@String.0)
}
```

LLM calls are effects. The two functions above are `effects(pure)`; this one declares `<Inference>`, and a caller that doesn't permit `<Inference>` can't call it. A model call shows up in the signature of every function that makes one, all the way up the call chain. [examples/inference.vera](https://github.com/aallan/vera/blob/main/examples/inference.vera).

<!-- vera:no-run category="network" reason="calls Http, so a run would reach the network" -->
```vera
public fn research_topic(@String -> @Result<String, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Http, Inference>)
{
  let @String = url_encode(@String.0);
  let @Result<String, String> = Http.get(string_concat("https://api.duckduckgo.com/?format=json&q=", @String.0));
  match @Result<String, String>.0 {
    Ok(@String) -> Inference.complete(string_concat("Summarise this in one paragraph:\n\n", @String.0)),
    Err(@String) -> Err(@String.0)
  }
}
```

Effects compose. The row `<Http, Inference>` says this function needs both. `Inference` picks its provider (Anthropic, OpenAI, Moonshot, Mistral, xAI or DeepSeek) from whichever API key is set. Postconditions can constrain what the model returns; Z3 can't know that at compile time, so they become runtime checks that trap on a violation.

<!-- vera:no-run category="fixture" reason="queries a users table the block does not create" -->
```vera
public fn find_user(@String -> @Result<Array<Array<Option<String>>>, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<DB>)
{
  DB.query("SELECT name, email FROM users WHERE name = ?", [Some(@String.0)])
}
```

SQL injection won't compile. Nearly every SQL injection starts the same way, with a query assembled from a value that came from outside the program. In Vera the query text has to be written into the source, so it is fixed at compile time, and outside data reaches the database only through the `?` placeholders and the parameter array. Build the query with `string_concat` instead and the compiler refuses it with `E207`. It's a type error, and there is no setting that turns it off. [examples/database.vera](https://github.com/aallan/vera/blob/main/examples/database.vera).

When the model gets it wrong, every error comes back as an instruction:

```
[E001] Error at main.vera, line 2, column 1:

    {
    ^

  Function is missing its contract block. Every function in Vera must declare requires(), ensures(), and effects() clauses between the signature and the body.

  Vera requires all functions to have explicit contracts so that every function's behaviour is mechanically checkable.

  Fix:

    Add a contract block after the signature:

      private fn example(@Int -> @Int)
        requires(true)
        ensures(@Int.result >= 0)
        effects(pure)
      {
        ...
      }

  See: Chapter 5, Section 5.2 "Function Declaration Syntax"
```

Parse errors, type errors, effect mismatches, failed proofs and contract violations all come back in the same shape: what went wrong, why, how to fix it, and where the spec covers it.

## VeraBench

**Six of nine frontier models write 100% correct Vera, a language none of them had seen before.**

A 60-problem benchmark across 5 difficulty tiers: pure arithmetic, strings and arrays, ADTs and exhaustive matching, recursion with termination proofs, and effects propagated across functions. Nine models, three providers, four modes each: Vera written against the full specification, Vera written from a plain English description with the model writing its own contracts, and the same problems in Python and TypeScript. The table below shows three of the four modes as **% solved**, meaning the code compiled, ran and produced the right output. A refusal, a compile failure, a crash and a wrong answer all count as a miss.

| Model | Tier | Vera | Python | TypeScript |
|---|---|---|---|---|
| Claude Fable 5 | ceiling | **100%** | _97%_ | _97%_ |
| GPT-5.6 Sol (pro) | ceiling | 100% | _95%_ | 100% |
| Claude Opus 5 | flagship | 100% | _95%_ | 100% |
| Claude Opus 4.8 | flagship | _93%_ | _98%_ | **100%** |
| GPT-5.6 Sol | flagship | _98%_ | _95%_ | **100%** |
| Kimi K3 | flagship | 100% | 100% | 100% |
| Claude Sonnet 5 | workhorse | _97%_ | _98%_ | **100%** |
| GPT-5.6 Terra | workhorse | 100% | _95%_ | 100% |
| Kimi K2.6 | workhorse | 100% | _97%_ | 100% |

Every score is marked against the other two in its row: **bold** where it is the sole highest, _italic_ where it is not the highest, unmarked where it ties for highest.

Frontier models write Vera **as well as they write the languages they were trained on**. Vera scores highest, or joint highest, for six of the nine models.

Mandatory contracts and typed slot references give a model enough structure to make up for having no training data at all. Every one of these programs was written by a model that had never seen Vera, working from a single skill file in its context.

The gap between Python and TypeScript tells the same story. Python is dynamically typed, so a type error surfaces when the code runs; TypeScript rejects the same error before anything runs. Vera goes further than TypeScript, making `requires`, `ensures` and `effects` mandatory on every function and replacing variable names with typed slot references. Sort the three languages by how much they constrain the model, rather than by how much of them it has read, and the two that constrain it finish ahead of the one that doesn't.

TypeScript earns its results from years of training data. Vera earns very nearly the same results with none. Whatever familiarity buys TypeScript, Vera's constraints supply by other means.

Each model made one attempt per problem, with no pass@k, and each of the sixty problems is worth just under two percentage points. Language design can outweigh sheer volume of training data, and if you generate code at any scale, that's worth knowing.

Results from [VeraBench v0.0.18](https://github.com/aallan/vera-bench#results) against [Vera v0.1.8](https://github.com/aallan/vera/releases/tag/v0.1.8). Inspired by [HumanEval](https://github.com/openai/human-eval), [MBPP](https://github.com/google-research/google-research/tree/master/mbpp), and [DafnyBench](https://github.com/sun-wendy/DafnyBench).

Full source and data: [https://github.com/aallan/vera-bench](https://github.com/aallan/vera-bench).

## Design Principles

1. **Checkability over correctness.** Code the compiler can mechanically check. Every diagnostic includes a concrete fix in natural language.
2. **Explicitness over convenience.** All state changes declared. All effects typed. All contracts mandatory. No implicit behaviour.
3. **One canonical form.** One preferred spelling per construct; formatting is deterministic and idempotent. `vera fmt` settles it.
4. **Structural references over names.** Bindings referenced by type and positional index (`@T.n`), not arbitrary names.
5. **Contracts as the source of truth.** Every function declares what it requires and guarantees, and the compiler proves it statically wherever it can.
6. **Constrained expressiveness.** Fewer valid programs means fewer opportunities for the model to be wrong.

## Key Features

- **No variable names.** Typed [De Bruijn indices](https://raw.githubusercontent.com/aallan/vera/main/DE_BRUIJN.md) (`@T.n`) replace variable names: `@Int.0` is the most-recent `Int` binding, `@Int.1` the one before. A whole class of naming hallucinations disappears from the language instead of being caught after the fact.
- **Full contracts.** Mandatory preconditions, postconditions and effect declarations on every function, plus a `decreases` measure (or the `Diverge` effect) on every recursive one. `vera test` uses Z3 to generate inputs from the contracts and runs them through WASM, so there are no test cases to write by hand.
- **SQL injection won't compile.** The `<DB>` effect accepts only a query written as literals in the source, never one spliced together from a runtime value. Interpolating user input into SQL is a compile-time error (`E207`), so every value goes through a `?` placeholder. Injection safety stops being a discipline you have to remember and becomes a rule the compiler enforces.
- **Algebraic effects.** IO, Http, HttpServer, State, Exceptions, Async, Inference, DB, Random, Diverge. Every effect is declared and typed, and code is pure by default. `State` and `Exn` are handled in Vera code; the host effects are backed by the runtime.
- **Refinement types.** Types that state constraints, such as a list of positive integers of length `n`.
- **Proof, then runtime checks.** Contracts are proved at compile time with [Z3](https://www.microsoft.com/en-us/research/project/z3-3/), and most of what Z3 can't prove is checked at run time instead. A `requires` that can never hold is refused, so a contradiction can't prove everything. `vera verify --timeout-ms` sets the solver budget.
- **Traps that name their cause.** A `@Nat` underflow, a failed contract or `assert`, an index out of bounds or an escaped exception reports what kind of trap it is and how to fix it, the same way on wasmtime, in the browser and under WASI 0.2.
- **Language server.** A warm Z3 session between keystrokes, so proofs re-check at editor speed. Custom methods give agents [proof deltas](https://raw.githubusercontent.com/aallan/vera/main/LSP_SERVER.md) before an edit lands.
- **Diagnostics as instructions.** Every error is a natural-language explanation with a concrete fix, designed for LLM consumption.
- **LLM inference as effect.** `Inference.complete` is an algebraic effect: typed, checked against its contract, and backed by the host. It works with Anthropic, OpenAI, Moonshot, Mistral, xAI and DeepSeek.
- **Typed stdlib.** JSON, HTML, Markdown, HTTP, regular expressions and decimals, as built-in data types you can parse, query and serialise.
- **Async / Future<T>.** Futures carry an `<Async>` effect and compose with the rest of the effect system.
- **Verified HTTP handlers.** An `<HttpServer>` effect marks a total `handle(Request -> Response)`. The accept loop lives in the host, so every handler contract is an ordinary proof obligation. `vera serve` runs it.
- **WASI 0.2 components.** `vera compile --target wasi-p2` emits a component that any stock wasip2 host runs (experimental, covering IO and Random). `--world server` packages a handler as a `wasi:http` component for `wasmtime serve`.

## Runs Everywhere

Vera compiles to WebAssembly. The same `.wasm` runs at the command line under [wasmtime](https://wasmtime.dev/) and in the browser inside a self-contained JavaScript runtime, and the same source builds a portable WASI 0.2 component.

### Command line

```bash
$ vera run examples/hello_world.vera
Hello, World!

$ vera run examples/factorial.vera --fn factorial -- 10
3628800
```

`vera run` compiles to WASM and executes via wasmtime. `--fn` picks any public function; arguments follow `--`.

### Browser

```bash
$ vera compile --target browser examples/hello_world.vera
Browser bundle: examples/hello_world_browser/
  module.wasm
  runtime.mjs
  index.html
```

Self-contained, with no bundler. Serve it from any HTTP server (`python -m http.server`). `IO.print` writes to the page, and everything else the browser target supports behaves exactly as it does at the command line; parity tests hold the two runtimes to the same output on every pull request. *`Inference.complete` and `DB` return an error in the browser by design, because the credentials they need would be readable from the page source. Reach them through a server-side proxy over `Http`.*

### WASI components

```bash
$ vera compile --target wasi-p2 --world server examples/http_server.vera
Compiled (WASI Preview 2 server component
(run with: wasmtime serve <file>)): examples/http_server.wasm

$ wasmtime serve examples/http_server.wasm
Serving HTTP on http://0.0.0.0:8080/
```

`--target wasi-p2` emits a WASI 0.2 component that any stock wasip2 host runs; `wasmtime run module.wasm` needs no flags and no Vera bindings. The target is experimental and covers IO and Random. `--world server` packages a `handle(Request -> Response)` program as a `wasi:http` component that `wasmtime serve` runs unmodified.

## Get Started

Python 3.11+. Everything else installs into a virtual environment.

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install veralang
vera version
# Optional: the language server for editors and agents
python -m pip install "veralang[lsp]"
```

**Upgrading from 0.1.x?** The checker and verifier are stricter in 0.2.0, so some programs that 0.1.13 accepted are now refused. The two you're most likely to meet are a recursive function with neither `decreases` nor `Diverge` (`E137`), and a `decreases` measure whose `@Nat` subtraction can underflow (`E502`). The [CHANGELOG](https://github.com/aallan/vera/blob/main/CHANGELOG.md) lists every new check.

The wheel installs the compiler and the `vera` command. Install from source for the full environment (the bundled examples, the conformance suite and the specification the agent docs teach from) or to work on the compiler itself:

```bash
git clone https://github.com/aallan/vera.git
cd vera
python -m venv .venv
source .venv/bin/activate
python -m pip install -e ".[dev]"
```

```bash
vera check examples/absolute_value.vera
vera verify examples/safe_divide.vera
vera run examples/hello_world.vera
vera compile --target browser examples/hello_world.vera
```

Editor support: [Vera Language for VS Code](https://marketplace.visualstudio.com/items?itemName=veralang.vera-language) (`code --install-extension veralang.vera-language`; [source](https://github.com/aallan/vera/tree/main/editors/vscode)), a [Vim package](https://github.com/aallan/vera/tree/main/editors/vim-veralang) for Vim 8+ and Neovim, and a [TextMate `.tmbundle`](https://github.com/aallan/vera/tree/main/editors/textmate) for Sublime Text and other TextMate-grammar editors.

Live proof-aware diagnostics, hover, slot go-to-definition and typed-hole completion come from the [language server](https://raw.githubusercontent.com/aallan/vera/main/LSP_SERVER.md). The source install above (`.[dev]`) includes it; from PyPI, add it with `python -m pip install "veralang[lsp]"`, or use `pip install -e ".[lsp]"` for a lighter source checkout. Any editor with a generic LSP client can point at `vera lsp` directly.

## For Agents

This page is also a machine-readable specification. Every document here has a markdown alternate on the same domain, discoverable through the standard `<link rel="alternate">`, `llms.txt`, and the Mintlify `llms-txt` and `llms-full-txt` conventions.

- [`SKILL.md`](https://veralang.dev/SKILL.md): Complete language reference for writing Vera code: syntax, slots, contracts, effects, common mistakes and working examples.
- [`LSP_SERVER.md`](https://raw.githubusercontent.com/aallan/vera/main/LSP_SERVER.md): The language server: live proof-aware diagnostics, and the custom proof-delta methods agents use to ask whether an edit still proves before committing it.
- [`AGENTS.md`](https://raw.githubusercontent.com/aallan/vera/main/AGENTS.md): Setup instructions for any agent system (Copilot, Cursor, Windsurf, custom). Writing Vera code and working on the compiler.
- [`CLAUDE.md`](https://raw.githubusercontent.com/aallan/vera/main/CLAUDE.md): Project orientation for Claude Code. Key commands, repo layout, workflows, invariants.
- [`TOOLCHAIN.md`](https://raw.githubusercontent.com/aallan/vera/main/TOOLCHAIN.md): The CLI cookbook for writing, verifying, testing, running and debugging Vera, plus the `builtins`, `effects` and `errors` introspection commands.

Claude Code discovers `SKILL.md` and `CLAUDE.md` automatically when working inside the repo. For other projects, install the skill manually:

```bash
mkdir -p ~/.claude/skills/vera-language
cp /path/to/vera/SKILL.md ~/.claude/skills/vera-language/SKILL.md
```

For other models, point them at [`SKILL.md`](https://veralang.dev/SKILL.md) through the system prompt, a file attachment or retrieval. It's self-contained and works with any model that reads markdown. Every Vera example in it, and on this page, is tested in CI.

The documents above are how machines *read* Vera. The [language server](https://raw.githubusercontent.com/aallan/vera/main/LSP_SERVER.md) is how they *interrogate* it. `vera lsp` holds a warm, incremental Z3 session between edits, and four custom methods (`vera/speculativeEdit`, `vera/proposeEdit`, `vera/strengthenContract` and `vera/addEffect`) tell an agent whether an edit *keeps*, *breaks* or *strengthens* a program's proofs before it commits, then apply the edit only through the verification gate.

```json
// vera/speculativeEdit: the proof delta for an in-memory edit
{
  "ok": true,
  "proof_delta": {
    "newly_discharged": ["..."],
    "newly_undischarged": [],
    "timed_out": [],
    "removed": [],
    "unchanged": 11,
    "proof_regressions": []
  },
  "diagnostics": 0
}
```

## Status

Vera is under [active development](https://raw.githubusercontent.com/aallan/vera/main/ROADMAP.md). A complete compiler with 164 built-in functions, ten algebraic effects (IO, Http, HttpServer, State, Exceptions, Async, Inference, DB, Random, Diverge), contract-driven testing with [Z3](https://www.microsoft.com/en-us/research/project/z3-3/), a language server with agent-facing proof deltas, and a 14-chapter specification. A 256-program conformance suite and 43 worked examples are validated against the spec on every pull request. It's all developed in the open on [GitHub](https://github.com/aallan/vera) under the MIT licence.

## Links

- [GitHub](https://github.com/aallan/vera)
- [README](https://raw.githubusercontent.com/aallan/vera/main/README.md)
- [SKILL.md](https://veralang.dev/SKILL.md)
- [AGENTS.md](https://raw.githubusercontent.com/aallan/vera/main/AGENTS.md)
- [Specification](https://github.com/aallan/vera/tree/main/spec)
- [Roadmap](https://raw.githubusercontent.com/aallan/vera/main/ROADMAP.md)
- [History](https://raw.githubusercontent.com/aallan/vera/main/HISTORY.md)
- [Changelog](https://raw.githubusercontent.com/aallan/vera/main/CHANGELOG.md)
- [Contributing](https://raw.githubusercontent.com/aallan/vera/main/CONTRIBUTING.md)
- [Issues](https://github.com/aallan/vera/issues)
- [VeraBench](https://github.com/aallan/vera-bench)
- [MIT Licence](https://github.com/aallan/vera/blob/main/LICENSE)
