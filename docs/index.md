# Vera — A language designed for machines to write

> Vera is a programming language designed for large language models to write, not humans. It uses typed slot references (`@T.n`) instead of variable names, requires contracts on every function, and compiles to WebAssembly. Programs run at the command line via wasmtime or in any browser with a self-contained JavaScript runtime.

From the Latin *veritas* — truth. In Vera, verification is a first-class citizen.

**Current version:** [0.1.13](https://github.com/aallan/vera/releases/tag/v0.1.13)  ·  [GitHub](https://github.com/aallan/vera)  ·  [SKILL.md](https://veralang.dev/SKILL.md) (agent language reference)

## Why?

Programming languages have always co-evolved with their users. Assembly emerged from hardware constraints. C from operating systems. Python from productivity needs. If models become the primary authors of code, it follows that languages should adapt to that too.

> The biggest problem models face isn't syntax — it's coherence over scale. Models are pattern matchers optimising for local plausibility, not architects holding the entire system in mind.

The [empirical literature](https://arxiv.org/abs/2307.12488) shows models are particularly vulnerable to naming-related errors: choosing misleading names, reusing names incorrectly, and losing track of which name refers to which value. Vera addresses this by making everything explicit and verifiable.

The model doesn't need to be right. It needs to be *checkable*. Names are replaced by structural references. Contracts are mandatory. Effects are typed. Every function is a specification the compiler verifies against its implementation.

![The loop: the model writes Vera with mandatory contracts; the compiler type-checks every program, proves supported contract obligations via Z3, guards most of the rest at runtime, and discloses what it can neither prove nor guard; when it's wrong the diagnostics return — description, rationale, fix, spec_ref — and when the proofs hold it ships as one .wasm for CLI and browser, or a WASI component.](https://veralang.dev/loop-web.svg)

For deeper questions about the design — why no variable names, what gets verified, how Vera compares to Dafny, Lean, and Koka — see the [FAQ](https://raw.githubusercontent.com/aallan/vera/main/FAQ.md).

## What Vera Looks Like

Nothing is implicit. The signature declares types, preconditions, postconditions, and effects. The compiler verifies the contract via SMT solver. A zero divisor the verifier can witness is a compile error (`E526`), not a runtime crash.

```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

Read the slots: `@Int.1` is the first parameter, `@Int.0` is the second — De Bruijn indexing, most-recent first. No local variable names means no local naming bug is possible — references are type-directed and positional. The `requires` clause is what discharges the divisor obligation: with it the division proves at compile time; without it the compiler refuses the program with `E526` and a counterexample, and only a divisor it can neither prove non-zero nor witness a zero for falls to a runtime guard. [examples/safe_divide.vera](https://github.com/aallan/vera/blob/main/examples/safe_divide.vera).

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

A program everyone knows. Interpolation uses `"\(@Nat.0)"` — the slot reference substitutes in directly with auto-conversion. There are no naming decisions to make, and none to hallucinate. [examples/fizzbuzz.vera](https://github.com/aallan/vera/blob/main/examples/fizzbuzz.vera).

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

LLM calls are effects. Where the two functions above are `effects(pure)`, this one declares `<Inference>`. A caller that does not permit `<Inference>` cannot invoke it. The effect system makes model calls visible in every signature that uses them, all the way up. [examples/inference.vera](https://github.com/aallan/vera/blob/main/examples/inference.vera).

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

Effects compose. `<Http, Inference>` is the row — both must be permitted. `Inference` auto-detects the provider (Anthropic, OpenAI, Moonshot, Mistral, xAI, DeepSeek) from whichever API key is set to a non-empty value. Postconditions can constrain model output; Z3 cannot know what a model will return at compile time, so these become runtime assertions that trap on violation.

```vera
public fn find_user(@String -> @Result<Array<Array<Option<String>>>, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<DB>)
{
  DB.query("SELECT name, email FROM users WHERE name = ?", [Some(@String.0)])
}
```

SQL injection won't compile. Nearly every SQL injection starts the same way — a query assembled from a value that came from outside the program. Vera makes that unwriteable. The SQL text has to be written into the source, so the query is fixed when the program compiles and outside data can only reach the database through the `?` placeholders and the params array. Build the query out of the parameter with `string_concat` instead and the answer is `[E207]`: not a warning, not a lint you can silence, but a type error you cannot configure away. [examples/database.vera](https://github.com/aallan/vera/blob/main/examples/database.vera).

When you get it wrong, every error is an instruction for the model that wrote the code:

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

Parse errors, type errors, effect mismatches, verification failures, and contract violations all produce the same shape: what went wrong, why, how to fix it, and a spec reference.

## VeraBench

**Six of nine frontier models write 100% correct Vera — a language none of them has ever seen before.**

A 60-problem benchmark across 5 difficulty tiers — pure arithmetic, strings and arrays, ADTs and exhaustive matching, recursion with termination proofs, multi-function effect propagation. Nine models, three providers, four modes each: Vera written against a full specification, Vera written from a plain English description with the model authoring its own contracts, and the same problems in Python and TypeScript. The table below shows three of the four, and reports **% solved**: the model wrote code, it compiled, it ran, and the output matched. A refusal, a compile failure, a crash and a wrong answer all count alike as not solved.

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

Frontier models now write Vera **as well as they write the languages they were trained on**. Vera has the highest score, or level with it, for six of the nine models.

Mandatory contracts and typed slot references appear to provide enough structure to compensate for zero training data. Every successful program came from a single skill file in context, written by a model that had never seen the language before.

The difference between the Python and TypeScript results is probably not random. Python is dynamically typed, so a type error surfaces when the code runs; TypeScript is statically typed and rejects the same error before anything runs. Vera sits with TypeScript but goes further, making `requires`, `ensures` and `effects` mandatory on every function and replacing variable names with typed slot references. Sort the three languages by how much they constrain the model rather than by how much of them it has read, and the ordering stops looking accidental: the two languages that constrain the model finish ahead of the one that doesn't.

TypeScript earns its results due to its inclusion in model training data. Vera earns very nearly the same results without that. Whatever familiarity is buying TypeScript, the additional constraints Vera provides appear to be supplying by other means.

It's still early days. The benchmark is just a single run per model, no pass@k; and with just sixty problems each problem is worth just under two percentage points, so most of the gaps above are only one or two problems wide. However, it looks like language design can, at least sometimes, outweigh sheer volume of training data. Which, if you're in the business of generating code at any scale, is a reasonably interesting thing to be true.

Results from [VeraBench v0.0.18](https://github.com/aallan/vera-bench#results) against [Vera v0.1.8](https://github.com/aallan/vera/releases/tag/v0.1.8). Inspired by [HumanEval](https://github.com/openai/human-eval), [MBPP](https://github.com/google-research/google-research/tree/master/mbpp), and [DafnyBench](https://github.com/sun-wendy/DafnyBench).

Full source and data: [https://github.com/aallan/vera-bench](https://github.com/aallan/vera-bench).

## Design Principles

1. **Checkability over correctness** — Code the compiler can mechanically check. Every diagnostic carries a concrete fix in natural language.
2. **Explicitness over convenience** — All state changes declared. All effects typed. All contracts mandatory. No implicit behaviour.
3. **One canonical form** — One preferred spelling per construct; formatting is deterministic and idempotent. `vera fmt` settles it.
4. **Structural references over names** — Bindings referenced by type and positional index (`@T.n`), not arbitrary names.
5. **Contracts as the source of truth** — Every function declares what it requires and guarantees. The compiler verifies statically where possible.
6. **Constrained expressiveness** — Fewer valid programs means fewer opportunities for the model to be wrong.

## Key Features

- **No variable names** — Typed [De Bruijn indices](https://raw.githubusercontent.com/aallan/vera/main/DE_BRUIJN.md) (`@T.n`) replace variable names: `@Int.0` is the most-recent `Int` binding, `@Int.1` the one before. The whole class of naming hallucinations is removed at the language level, not caught after the fact.
- **Full contracts** — Mandatory preconditions, postconditions, and effect declarations on every function. Z3 generates test inputs from the contracts and runs them through WASM — no manual test cases.
- **SQL injection won't compile** — The `<DB>` effect accepts only a literal query string — built from string literals, never spliced from a runtime value. Interpolating user input into SQL is a compile-time error (`E207`); every value flows through a `?` placeholder instead. Injection safety stops being a discipline you remember and becomes one the compiler enforces.
- **Algebraic effects** — IO, Http, HttpServer, State, Exceptions, Async, Inference, DB, Random, Diverge — declared, typed, and handled explicitly. Pure by default.
- **Refinement types** — Types that express constraints like "a list of positive integers of length `n`".
- **Three-tier verification** — Static via [Z3](https://www.microsoft.com/en-us/research/project/z3-3/) plus runtime fallback, shipped; the Z3-guided middle tier is specified, not yet implemented.
- **Diagnostics as instructions** — Every error is a natural-language explanation with a concrete fix, designed for LLM consumption.
- **LLM inference as effect** — `Inference.complete` is an algebraic effect — typed, contract-verifiable, host-backed. Anthropic, OpenAI, Moonshot, Mistral, xAI, DeepSeek.
- **Typed stdlib** — JSON, HTML, Markdown, HTTP, Regex, Decimal — built-in ADTs with parse/query/serialize.
- **Async / Future<T>** — Futures carry an `<Async>` effect and compose with the rest of the effect system.
- **Verified HTTP handlers** — An `<HttpServer>` effect marks a total `handle(Request -> Response)`. The accept loop lives in the host, so every handler contract is an ordinary proof obligation. `vera serve` runs it.
- **WASI 0.2 components** — `vera compile --target wasi-p2` emits a component any stock wasip2 host runs (experimental; IO and Random surface). `--world server` packages a handler as a `wasi:http` component for `wasmtime serve`.

## Runs Everywhere

Vera compiles to WebAssembly. The same `.wasm` runs at the command line (via [wasmtime](https://wasmtime.dev/)) and in the browser (wrapped in a self-contained JS runtime); WASI 0.2 is a separate portable component built from the same source.

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

Self-contained — no bundler. Serve with any HTTP server (`python -m http.server`). `IO.print` writes to the page; every other operation the browser target supports works identically to the CLI. `json_stringify` and `md_render` reach that identity by emitting a canonical form the specification states (§9.7.1, §9.7.3) rather than by the hosts happening to agree, and `json_parse` by accepting the domain §9.7.1 states — RFC 8259-valid text that decodes to finite numbers and strings of Unicode scalar values — rather than whatever its host parser admits, and `md_parse` by parsing the grammar §9.7.3 states, from one shared table of patterns both runtimes read; parity tests check all four against that stated form as well as against each other, on every PR — for `md_parse` by comparing the two hosts' ADTs byte for byte over a generated corpus. *Note: `Inference.complete` and every `DB` operation return an error in the browser — a deliberate platform boundary, since the credentials they need would be readable from page source; reach them through a server-side proxy via `Http`.*

### WASI components

```bash
$ vera compile --target wasi-p2 --world server examples/http_server.vera
Compiled (WASI Preview 2 server component
(run with: wasmtime serve <file>)): examples/http_server.wasm

$ wasmtime serve examples/http_server.wasm
Serving HTTP on http://0.0.0.0:8080/
```

`--target wasi-p2` emits a WASI 0.2 component any stock wasip2 host runs — `wasmtime run module.wasm` needs no flags and no Vera bindings (experimental; the IO and Random surface). `--world server` packages a `handle(Request -> Response)` program as a `wasi:http` component that `wasmtime serve` runs unmodified.

## Get Started

Python 3.11+. Everything else installs into a virtual environment.

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install veralang
```

Or install the current GitHub source for development:

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

## For Agents

This page is also a machine-readable specification. Every document here has an alternate in markdown, served on the same domain, discoverable through standard `<link rel="alternate">`, `llms.txt`, and the Mintlify `llms-txt` / `llms-full-txt` conventions.

- [`SKILL.md`](https://veralang.dev/SKILL.md) — Complete language reference for writing Vera code: syntax, slots, contracts, effects, common mistakes, working examples.
- [`LSP_SERVER.md`](https://raw.githubusercontent.com/aallan/vera/main/LSP_SERVER.md) — The language server: live proof-aware diagnostics and the custom proof-delta methods agents use to ask “does this edit still prove?” before committing it.
- [`AGENTS.md`](https://raw.githubusercontent.com/aallan/vera/main/AGENTS.md) — Setup instructions for any agent system (Copilot, Cursor, Windsurf, custom). Writing Vera code and working on the compiler.
- [`CLAUDE.md`](https://raw.githubusercontent.com/aallan/vera/main/CLAUDE.md) — Project orientation for Claude Code. Key commands, repo layout, workflows, invariants.

Claude Code discovers `SKILL.md` and `CLAUDE.md` automatically when working inside the repo. For other projects, install the skill manually:

```bash
mkdir -p ~/.claude/skills/vera-language
cp /path/to/vera/SKILL.md ~/.claude/skills/vera-language/SKILL.md
```

For other models: point them at [`SKILL.md`](https://veralang.dev/SKILL.md) via system prompt, file attachment, or retrieval. It's self-contained and works with any model that reads markdown.

## Status

Vera is under [active development](https://raw.githubusercontent.com/aallan/vera/main/ROADMAP.md). A complete compiler with 164 built-in functions, ten algebraic effects (IO, Http, HttpServer, State, Exceptions, Async, Inference, DB, Random, Diverge), contract-driven testing via [Z3](https://www.microsoft.com/en-us/research/project/z3-3/), and a 14-chapter specification. A 247-program conformance suite and 43 worked examples are validated against the spec on every pull request. All of it is developed openly on [GitHub](https://github.com/aallan/vera) and released under the MIT licence.

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
