# Vera — A language designed for machines to write

> Vera is a programming language designed for large language models to write, not humans. It uses typed slot references (`@T.n`) instead of variable names, requires contracts on every function, and compiles to WebAssembly. Programs run at the command line via wasmtime or in any browser with a self-contained JavaScript runtime.

From the Latin *veritas* — truth. In Vera, verification is a first-class citizen.

**Current version:** [0.0.126](https://github.com/aallan/vera/releases/tag/v0.0.126)  ·  [GitHub](https://github.com/aallan/vera)  ·  [SKILL.md](https://veralang.dev/SKILL.md) (agent language reference)

## Why?

Programming languages have always co-evolved with their users. Assembly emerged from hardware constraints. C from operating systems. Python from productivity needs. If models become the primary authors of code, it follows that languages should adapt to that too.

> The biggest problem models face isn't syntax — it's coherence over scale. Models are pattern matchers optimising for local plausibility, not architects holding the entire system in mind.

The [empirical literature](https://arxiv.org/abs/2307.12488) shows models are particularly vulnerable to naming-related errors: choosing misleading names, reusing names incorrectly, and losing track of which name refers to which value. Vera addresses this by making everything explicit and verifiable.

The model doesn't need to be right. It needs to be *checkable*. Names are replaced by structural references. Contracts are mandatory. Effects are typed. Every function is a specification the compiler verifies against its implementation.

For deeper questions about the design — why no variable names, what gets verified, how Vera compares to Dafny, Lean, and Koka — see the [FAQ](https://raw.githubusercontent.com/aallan/vera/main/FAQ.md).

## What Vera Looks Like

Nothing is implicit. The signature declares types, preconditions, postconditions, and effects. The compiler verifies the contract via SMT solver. Division by zero is not a runtime error — it is a type error.

```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

Read the slots: `@Int.1` is the first parameter, `@Int.0` is the second — De Bruijn indexing, most-recent first. No variable names means no naming bug is possible. The `requires` clause is what lifts divide-by-zero from a runtime crash to a compile-time error.

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

A program everyone knows. Interpolation uses `"\(@Nat.0)"` — the slot reference substitutes in directly with auto-conversion. There are no naming decisions to make, and none to hallucinate.

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

LLM calls are effects. Where the two functions above are `effects(pure)`, this one declares `<Inference>`. A caller that does not permit `<Inference>` cannot invoke it. The effect system makes model calls visible in every signature that uses them, all the way up.

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

Effects compose. `<Http, Inference>` is the row — both must be permitted. `Inference` auto-detects the provider (Anthropic, OpenAI, Moonshot) from whichever API key is set. Postconditions can constrain model output; Z3 cannot know what a model will return at compile time, so these become runtime assertions that trap on violation.

When you get it wrong, every error is an instruction for the model that wrote the code:

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

Parse errors, type errors, effect mismatches, verification failures, and contract violations all produce the same shape: what went wrong, why, how to fix it, and a spec reference.

## VeraBench

**Kimi K2.5 writes 100% correct Vera — beating its own 86% on Python and 91% on TypeScript.**

A 50-problem benchmark across 5 difficulty tiers — pure arithmetic, ADTs, recursion, closures, multi-function effect propagation. Six models, three providers, four modes each. The numbers below are run-correct rates.

| Model | Mode | Vera | Python | TypeScript |
|---|---|---|---|---|
| Kimi K2.5 | flagship | **100%** | 86% | 91% |
| GPT-4.1 | flagship | 91% | 96% | 96% |
| Claude Opus 4 | flagship | 88% | 96% | 96% |
| Kimi K2 Turbo | sonnet | **83%** | 88% | 79% |
| Claude Sonnet 4 | sonnet | 79% | 96% | 88% |
| GPT-4o | sonnet | 78% | 93% | 83% |

In our latest results **Kimi K2.5 writes perfect Vera code** — 100% run_correct, beating both Python (86%) and TypeScript (91%); Kimi K2 Turbo also writes better Vera than TypeScript. In the previous [v0.0.4](https://github.com/aallan/vera-bench/releases/tag/v0.0.4) benchmark Claude Sonnet 4 wrote Vera better than TypeScript (83% vs 79%); the latest v0.0.7 re-run flipped that result, illustrating the variance inherent in single-run evaluation and model non-determinism.

Mandatory contracts and typed slot references appear to provide enough structure to compensate for zero training data. Still early days — 50 problems, single run per model. Stable rates will require pass@k evaluation with multiple trials. Results from [VeraBench v0.0.7](https://github.com/aallan/vera-bench/releases/tag/v0.0.7) against [Vera v0.0.108](https://github.com/aallan/vera/releases/tag/v0.0.108). Inspired by [HumanEval](https://github.com/openai/human-eval), [MBPP](https://github.com/google-research/google-research/tree/master/mbpp), and [DafnyBench](https://github.com/sun-wendy/DafnyBench).

Full source and data: [https://github.com/aallan/vera-bench](https://github.com/aallan/vera-bench).

## Design Principles

1. **Checkability over correctness** — Code the compiler can mechanically check. Every diagnostic carries a concrete fix in natural language.
2. **Explicitness over convenience** — All state changes declared. All effects typed. All contracts mandatory. No implicit behaviour.
3. **One canonical form** — Every construct has exactly one textual representation. `vera fmt` settles it.
4. **Structural references over names** — Bindings referenced by type and positional index (`@T.n`), not arbitrary names.
5. **Contracts as the source of truth** — Every function declares what it requires and guarantees. The compiler verifies statically where possible.
6. **Constrained expressiveness** — Fewer valid programs means fewer opportunities for the model to be wrong.

## Key Features

- **No variable names** — Typed [De Bruijn indices](https://raw.githubusercontent.com/aallan/vera/main/DE_BRUIJN.md) (`@T.n`) replace variable names: `@Int.0` is the most-recent `Int` binding, `@Int.1` the one before. The whole class of naming hallucinations is removed at the language level, not caught after the fact.
- **Full contracts** — Mandatory preconditions, postconditions, invariants, and effect declarations on every function. Z3 generates test inputs from the contracts and runs them through WASM — no manual test cases.
- **Algebraic effects** — IO, Http, State, Exceptions, Async, Inference, Random — declared, typed, and handled explicitly. Pure by default.
- **Refinement types** — Types that express constraints like "a list of positive integers of length `n`".
- **Three-tier verification** — Static via [Z3](https://www.microsoft.com/en-us/research/project/z3-3/), guided with hints, runtime fallback for the rest.
- **Diagnostics as instructions** — Every error is a natural-language explanation with a concrete fix, designed for LLM consumption.
- **LLM inference as effect** — `Inference.complete` is an algebraic effect — typed, contract-verifiable, mockable. Anthropic, OpenAI, Moonshot.
- **Typed stdlib** — JSON, HTML, Markdown, HTTP, Regex, Decimal — built-in ADTs with parse/query/serialize.
- **Async / Future<T>** — Futures carry an `<Async>` effect and compose with the rest of the effect system.

## Runs Everywhere

Vera compiles to WebAssembly. The same `.wasm` runs at the command line via [wasmtime](https://wasmtime.dev/) or in any browser with a self-contained JS runtime.

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

Self-contained — no bundler. Serve with any HTTP server (`python -m http.server`). `IO.print` writes to the page; all other operations work identically to the CLI. Parity tests enforce this on every PR. *Note: `Inference.complete` errors in the browser — use a server-side proxy via `Http`.*

## Get Started

Python 3.11+ and Git. Everything else installs into a virtual environment.

```bash
# Clone and install
git clone https://github.com/aallan/vera.git
cd vera
python -m venv .venv
source .venv/bin/activate
pip install -e ".[dev]"

# Check, verify, run, compile
vera check examples/absolute_value.vera
vera verify examples/safe_divide.vera
vera run examples/hello_world.vera
vera compile --target browser examples/hello_world.vera
```

Editor support: [TextMate `.tmbundle`](https://github.com/aallan/vera/tree/main/editors/textmate), [VS Code extension](https://github.com/aallan/vera/tree/main/editors/vscode).

## For Agents

This page is also a machine-readable specification. Every document here has an alternate in markdown, served on the same domain, discoverable through standard `<link rel="alternate">`, `llms.txt`, and the Mintlify `llms-txt` / `llms-full-txt` conventions.

- [`SKILL.md`](https://veralang.dev/SKILL.md) — Complete language reference for writing Vera code: syntax, slots, contracts, effects, common mistakes, working examples.
- [`AGENTS.md`](https://raw.githubusercontent.com/aallan/vera/main/AGENTS.md) — Setup instructions for any agent system (Copilot, Cursor, Windsurf, custom). Writing Vera code and working on the compiler.
- [`CLAUDE.md`](https://raw.githubusercontent.com/aallan/vera/main/CLAUDE.md) — Project orientation for Claude Code. Key commands, repo layout, workflows, invariants.

Claude Code discovers `SKILL.md` and `CLAUDE.md` automatically when working inside the repo. For other projects, install the skill manually:

```bash
mkdir -p ~/.claude/skills/vera-language
cp /path/to/vera/SKILL.md ~/.claude/skills/vera-language/SKILL.md
```

For other models: point them at [`SKILL.md`](https://veralang.dev/SKILL.md) via system prompt, file attachment, or retrieval. It's self-contained and works with any model that reads markdown.

## Status

Vera is under [active development](https://raw.githubusercontent.com/aallan/vera/main/ROADMAP.md). A complete compiler with 164 built-in functions, seven algebraic effects (IO, Http, State, Exceptions, Async, Inference, Random), contract-driven testing via [Z3](https://www.microsoft.com/en-us/research/project/z3-3/), and a 13-chapter specification. An 81-program conformance suite and 33 worked examples are validated against the spec on every pull request. All of it is developed openly on [GitHub](https://github.com/aallan/vera) and released under the MIT licence.

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
