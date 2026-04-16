# Vera

[![Vera — A language designed for machines to write](assets/vera-social-preview.jpg)](https://veralang.dev)

[![CI](https://github.com/aallan/vera/actions/workflows/ci.yml/badge.svg)](https://github.com/aallan/vera/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/aallan/vera/graph/badge.svg)](https://codecov.io/gh/aallan/vera)

**Vera** (v-ERR-a) is a programming language designed for large language models to write. The name comes from the Latin *veritas* (truth). Programs compile to WebAssembly and run at the command line or in the browser.

```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

There are no variable names. `@Int.0` is the most recent `Int` binding; `@Int.1` is the one before. The `requires` clause is a precondition the compiler checks at every call site. The `ensures` clause is a postcondition the SMT solver proves statically. The function is `pure` — no side effects of any kind. If any of this is wrong, the code does not compile.

## Why?

Programming languages have always co-evolved with their users. Assembly emerged from hardware constraints. C from operating systems. Python from productivity needs. If models become the primary authors of code, it follows that languages should adapt to that too.

The evidence suggests the biggest problem models face isn't syntax, instead it's coherence over scale. Models struggle with maintaining invariants across a codebase, understanding the ripple effects of changes, and reasoning about state over time. They're pattern matchers optimising for local plausibility, not architects holding the entire system in mind. The [empirical literature](https://arxiv.org/abs/2307.12488) shows that models are particularly vulnerable to naming-related errors like choosing misleading names, reusing names incorrectly, and losing track of which name refers to which value.

Vera addresses this by making everything explicit and verifiable. The model doesn't need to be right, it needs to be checkable. Names are replaced by structural references. Contracts are mandatory. Effects are typed. Every function is a specification that the compiler can verify against its implementation.

See the **[FAQ](FAQ.md)** for deeper questions about the design — why no variable names, what gets verified, how Vera compares to Dafny/Lean/Koka/F*, and the empirical evidence behind the design choices.

## What Vera looks like

Three examples that show what makes Vera different. For the full tour — contracts, refinement types, ADTs, effects, exception handling, recursion, Markdown, JSON, HTML, HTTP, LLM inference — see **[EXAMPLES.md](EXAMPLES.md)**.

### Contracts the compiler proves

Division by zero is not a runtime error — it is a type error. The compiler checks every call site to prove the divisor is non-zero.

```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

### Effects are explicit

Vera is pure by default. A function that calls an LLM says so in its signature. A caller that doesn't permit `<Inference>` cannot invoke it. A caller that doesn't permit `<Http>` cannot invoke it either. Both callers must declare the full effect row.

```vera
public fn research_topic(@String -> @Result<String, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Http, Inference>)
{
  let @Result<String, String> = Http.get(
    string_concat("https://search.example.com/?q=", @String.0));
  match @Result<String, String>.0 {
    Ok(@String) -> Inference.complete(
      string_concat("Summarise this research:\n\n", @String.0)),
    Err(@String) -> Err(@String.0)
  }
}
```

Six lines of logic. The signature carries all the ceremony — parameter types, contracts, effect declarations — so the body reads like a pipeline. Run a real example with `VERA_ANTHROPIC_API_KEY=sk-ant-... vera run` [`examples/inference.vera`](examples/inference.vera).

### Errors are instructions

Traditional compilers produce diagnostics for humans: `expected token '{'`. Vera produces instructions for the model that wrote the code. Every error includes what went wrong, why, how to fix it with a concrete code example, and a spec reference.

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

Every diagnostic has a stable error code (`E001`–`E702`) and is available as structured JSON via the `--json` flag.

## Getting started

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

```
$ vera check examples/absolute_value.vera
OK: examples/absolute_value.vera

$ vera verify examples/safe_divide.vera
OK: examples/safe_divide.vera
Verification: 4 verified (Tier 1)

$ vera run examples/hello_world.vera
Hello, World!
```

`vera check` parses and type-checks. `vera verify` adds contract verification via Z3 — Tier 1 contracts (decidable arithmetic, comparisons, Boolean logic, ADTs, termination) are proved automatically; contracts Z3 cannot decide become Tier 3 runtime checks. `vera run` compiles to WebAssembly and executes.

```bash
vera run file.vera --fn f -- 42           # call function f with argument 42
vera compile --target browser file.vera   # emit browser bundle
vera test file.vera                       # contract-driven testing via Z3 + WASM
vera fmt file.vera                        # format to canonical form
vera verify --json file.vera              # JSON diagnostics for agent feedback loops
vera check --explain-slots file.vera     # show slot resolution table (which @T.n maps to which param)
vera version                             # print the installed version
```

`vera compile --target browser` produces a self-contained bundle (wasm + JS runtime + HTML) that runs in any browser — no build step, no bundler. Mandatory parity tests ensure identical behaviour between the command-line and browser runtimes.

### Editor support

- **[VS Code extension](editors/vscode/)** — syntax highlighting and language configuration
- **[TextMate bundle](editors/textmate/)** — also compatible with Sublime Text and other TextMate-grammar editors

## For agents

Vera ships with these files for LLM agents:

- [`SKILL.md`](SKILL.md) — Complete language reference. Covers syntax, slot references, contracts, effects, common mistakes, and working examples.
- [`AGENTS.md`](AGENTS.md) — Instructions for any agent system (Copilot, Cursor, Windsurf, custom). Covers both writing Vera code and working on the compiler.
- [`CLAUDE.md`](CLAUDE.md) — Project orientation for Claude Code. Key commands, layout, workflows, and invariants.
- [`DE_BRUIJN.md`](DE_BRUIJN.md) — Deep dive into Vera's typed slot references: the academic background, worked examples, the commutative-operations trap, and connections to proof assistants and LLM code-generation research.

**Claude Code** discovers `SKILL.md` and `CLAUDE.md` automatically in this repo. For other projects, install the skill manually:

```bash
mkdir -p ~/.claude/skills/vera-language
cp /path/to/vera/SKILL.md ~/.claude/skills/vera-language/SKILL.md
```

**Other models** — include `SKILL.md` in the system prompt, as a file attachment, or as a retrieval document. The file is self-contained and works with any model that can read markdown.

**Essential rules** for writing Vera code:

1. Every function needs `requires()`, `ensures()`, and `effects()` between the signature and body
2. Use `@Type.index` to reference bindings — `@Int.0` is the most recent `Int`, `@Int.1` is the one before
3. Declare all effects — `effects(pure)` for pure functions, `effects(<IO>)` for IO, etc.
4. Recursive functions need a `decreases()` clause
5. Match expressions must be exhaustive

## Project status

Vera is in **active development** at v0.0.113 — 810+ commits, 113 releases, 3,318 tests, 96% code coverage, 73 conformance programs, 30 examples, and a 13-chapter specification. See **[HISTORY.md](HISTORY.md)** for how the compiler was built.

The reference compiler — parser, AST, type checker, contract verifier (Z3), WASM code generator, module system, browser runtime, and runtime contract insertion — is working. The language specification is in draft across [13 chapters](spec/).

**Key features delivered:** [typed De Bruijn indices](DE_BRUIJN.md) (`@T.n`), mandatory contracts, algebraic effects (IO, Http, State, Exceptions, Async, Inference), refinement types, constrained generics (Eq, Ord, Hash, Show), algebraic data types, pattern matching, modules, 122 built-in functions (strings, arrays, maps, sets, decimals, JSON, HTML, Markdown, regex, base64, URL), contract-driven testing, canonical formatter, browser runtime, and three-tier verification (Z3 static, guided, runtime fallback).

**What's next:** the path from "working language" to "the language agents actually use" — see **[ROADMAP.md](ROADMAP.md)** for the four strategic milestones. The flagship goal is a verified MCP tool server where contracts guarantee tool schemas at compile time. **[VeraBench](https://github.com/aallan/vera-bench)** — a 50-problem benchmark across 5 difficulty tiers — now covers 6 models across 3 providers (v0.0.7). The headline result: Kimi K2.5 achieves 100% run_correct on Vera, beating both Python (86%) and TypeScript (91%). Three models beat TypeScript on Vera; the flagship tier averages 93% Vera vs 93% Python — essentially parity. These are single-run results with high variance — see the [full report](https://github.com/aallan/vera-bench) for details.

Known bugs and open issues are tracked on the **[issue tracker](https://github.com/aallan/vera/issues)**. See **[KNOWN_ISSUES.md](KNOWN_ISSUES.md)** for a consolidated list.

<details>
<summary><strong>Project structure</strong></summary>

```
vera/
├── SKILL.md                       # Language reference for LLM agents
├── AGENTS.md                      # Instructions for any AI agent system
├── CLAUDE.md                      # Project orientation for Claude Code
├── FAQ.md                         # Design rationale and comparisons
├── EXAMPLES.md                    # Language tour with code examples
├── HISTORY.md                     # How the compiler was built
├── ROADMAP.md                     # Forward-looking language roadmap
├── KNOWN_ISSUES.md                # Known bugs and limitations
├── DESIGN.md                      # Technical decisions and prior art
├── TESTING.md                     # Testing reference (single source of truth)
├── CONTRIBUTING.md                # Contributor guidelines
├── CHANGELOG.md                   # Version history
├── LICENSE                        # MIT licence
├── spec/                          # Language specification (13 chapters)
├── vera/                          # Reference compiler (Python)
│   ├── grammar.lark               #   Lark LALR(1) grammar
│   ├── parser.py                  #   Parser module
│   ├── ast.py                     #   Typed AST node definitions
│   ├── transform.py               #   Lark parse tree → AST transformer
│   ├── checker/                   #   Type checker (mixin package)
│   ├── verifier.py                #   Contract verifier (Z3)
│   ├── codegen/                   #   Code generation (11 modules)
│   ├── wasm/                      #   WASM translation (9 modules)
│   ├── browser/                   #   Browser runtime
│   ├── formatter.py               #   Canonical code formatter
│   ├── errors.py                  #   LLM-oriented diagnostics
│   └── cli.py                     #   Command-line interface
├── docs/                          # GitHub Pages site (veralang.dev)
├── editors/                       # VS Code extension + TextMate bundle
├── examples/                      # 30 example Vera programs
├── tests/                         # Test suite (see TESTING.md)
└── scripts/                       # CI and validation scripts
```

</details>

For compiler architecture and internals, see [`vera/README.md`](vera/README.md). For testing details, see **[TESTING.md](TESTING.md)**.

## Design

See **[DESIGN.md](DESIGN.md)** for the full technical decisions table (representation, references, contracts, effects, verification, memory, target, grammar, diagnostics, data types, polymorphism, collections, error handling, recursion, naming) and **[prior art](DESIGN.md#prior-art)** (Eiffel, Dafny, F*, Koka, Liquid Haskell, Idris, SPARK/Ada, bruijn, TLA+/Alloy).

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines on how to contribute to Vera. For compiler internals, see [vera/README.md](vera/README.md).

## Citation

If you use Vera in your research, please cite:

```bibtex
@software{vera2026,
  author = {Allan, Alasdair},
  title = {Vera: a programming language designed for LLMs to write},
  year = {2026},
  url = {https://github.com/aallan/vera}
}
```

## Licence

Vera is licensed under the [MIT License](LICENSE).

All direct dependencies are MIT or Apache-2.0. One transitive dependency (`chardet`, via `cyclonedx-bom`) is LGPL v2+, which is compatible with MIT redistribution. Licence compliance is enforced by CI.

| Dependency | Licence | Role |
|-----------|---------|------|
| [Lark](https://github.com/lark-parser/lark) | MIT | LALR(1) parser generator |
| [z3-solver](https://github.com/Z3Prover/z3) | MIT | SMT solver for contract verification |
| [wasmtime](https://github.com/bytecodealliance/wasmtime) | Apache-2.0 | WebAssembly runtime |

Copyright &copy; 2026 Alasdair Allan

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
