#!/usr/bin/env python3
"""Build AI-readable site assets for veralang.dev.

Auto-generates from source documentation:
  - docs/llms.txt        Curated index (llms.txt spec)
  - docs/llms-full.txt   Complete docs in one file
  - docs/robots.txt      AI-crawler-friendly robots.txt
  - docs/sitemap.xml     XML sitemap
  - docs/index.md        Markdown companion of index.html
  - docs/SKILL.md        Language reference served on-domain (copy of SKILL.md)

Run manually or from CI:
    python scripts/build_site.py

All output goes to docs/. Existing generated files are overwritten.
"""

from __future__ import annotations

import re
import sys
from datetime import date
from functools import cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs"
SITE = "https://veralang.dev"
REPO = "https://github.com/aallan/vera"
RAW = "https://raw.githubusercontent.com/aallan/vera/main"


def _version() -> str:
    """Read the current version from vera/__init__.py."""
    init = (ROOT / "vera" / "__init__.py").read_text(encoding="utf-8")
    m = re.search(r'__version__\s*=\s*"([^"]+)"', init)
    if not m:
        raise RuntimeError("Cannot find __version__ in vera/__init__.py")
    return m.group(1)


@cache
def _count_examples() -> int:
    """Count .vera files in examples/."""
    return len(list((ROOT / "examples").glob("*.vera")))


@cache
def _count_conformance() -> int:
    """Count conformance programs from manifest.json."""
    import json as _json
    manifest = _json.loads(
        (ROOT / "tests" / "conformance" / "manifest.json").read_text(encoding="utf-8")
    )
    return len(manifest)


# ── llms.txt ────────────────────────────────────────────────────────


def build_llms_txt(version: str) -> str:
    """Build the curated llms.txt index."""
    n_examples = _count_examples()
    n_conformance = _count_conformance()
    return f"""\
# Vera

> Vera is a statically typed, purely functional programming language \
designed for large language models to write. It uses typed slot references \
(`@T.n`) instead of variable names, requires contracts (preconditions, \
postconditions, effect declarations) on every function, and compiles to \
WebAssembly. Programs run at the command line via wasmtime or in the browser.

Vera uses De Bruijn indexing for bindings: `@Int.0` is the most recent \
`Int` binding, `@Int.1` the one before. There are no variable names. \
Contracts are mandatory — every function must declare `requires(...)`, \
`ensures(...)`, and `effects(...)`. The Z3 SMT solver verifies contracts \
statically where possible; remaining contracts become runtime assertions. \
All side effects (IO, Http, State, Exceptions, Async, Inference) are \
tracked in the type system via algebraic effects.

Current version: {version}. The reference compiler is written in Python. \
Install with `pip install -e .` from the repository.

## Homepage

- [Vera]({SITE}/index.md): Markdown companion to veralang.dev — project \
overview, thesis, design principles, key features, quick install, and links \
to the full documentation set.

## Language Reference

- [SKILL.md]({SITE}/SKILL.md): Complete language reference — syntax, types, \
slot references, contracts, effects, built-in functions, common mistakes, \
and working examples. This is the primary document for writing Vera code.

## Quick Start

- [AGENTS.md]({RAW}/AGENTS.md): Instructions for AI agents — workflow, \
commands, error handling, and essential rules for writing correct Vera.
- [FAQ]({RAW}/FAQ.md): Design rationale — why no variable names, what gets \
verified, comparison to Dafny/Lean/Koka, research citations.

## Specification

- [Chapter 0: Introduction]({RAW}/spec/00-introduction.md): Language \
philosophy and design goals.
- [Chapter 1: Lexical Structure]({RAW}/spec/01-lexical-structure.md): \
Tokens, literals, keywords, and comments.
- [Chapter 2: Types]({RAW}/spec/02-types.md): Primitive types, composite \
types, type aliases, and generics.
- [Chapter 3: Slot References]({RAW}/spec/03-slot-references.md): De Bruijn \
indexing, binding rules, and resolution.
- [Chapter 4: Expressions]({RAW}/spec/04-expressions.md): Arithmetic, \
comparison, logical, and let expressions.
- [Chapter 5: Functions]({RAW}/spec/05-functions.md): Function declarations, \
closures, generics, and mutual recursion.
- [Chapter 6: Contracts]({RAW}/spec/06-contracts.md): Preconditions, \
postconditions, termination measures, and quantifiers.
- [Chapter 7: Effects]({RAW}/spec/07-effects.md): Algebraic effects, \
handlers, IO, Http, State, Exceptions, Async, and Inference.
- [Chapter 8: Modules]({RAW}/spec/08-modules.md): Module system, imports, \
and visibility.
- [Chapter 9: Standard Library]({RAW}/spec/09-standard-library.md): All \
built-in functions — arrays, strings, maps, sets, decimals, JSON, HTML, \
markdown, regex, numeric, type conversions.
- [Chapter 10: Grammar]({RAW}/spec/10-grammar.md): Complete LALR(1) grammar \
in Lark notation.
- [Chapter 11: Compilation]({RAW}/spec/11-compilation.md): Compilation \
model and WebAssembly code generation.
- [Chapter 12: Runtime]({RAW}/spec/12-runtime.md): Runtime execution, \
memory management, and GC.

## Examples

- [examples/]({REPO}/tree/main/examples): {n_examples} verified example \
programs covering closures, generics, effects, pattern matching, string \
operations, async, markdown, JSON, HTML, HTTP, inference, regex, modules, \
and more.

## Compiler and Tooling

- [README]({RAW}/README.md): Project overview, installation, and getting started.
- [EXAMPLES]({RAW}/EXAMPLES.md): Language tour with code examples.
- [DESIGN]({RAW}/DESIGN.md): Technical decisions and prior art.
- [CHANGELOG]({RAW}/CHANGELOG.md): Version history and release notes.
- [ROADMAP]({RAW}/ROADMAP.md): Forward-looking language roadmap.
- [HISTORY]({RAW}/HISTORY.md): How the compiler was built.
- [Compiler Architecture]({RAW}/vera/README.md): Compiler internals — \
pipeline stages, module map, design patterns.

## Optional

- [TESTING.md]({RAW}/TESTING.md): Test suite architecture, coverage data, \
and test conventions.
- [KNOWN_ISSUES.md]({RAW}/KNOWN_ISSUES.md): Known bugs and limitations.
- [CONTRIBUTING.md]({RAW}/CONTRIBUTING.md): Contribution guidelines.
- [Conformance Suite]({REPO}/tree/main/tests/conformance): {n_conformance} \
programs validating every language feature against the spec.
"""


# ── llms-full.txt ───────────────────────────────────────────────────


def _abs_links(text: str) -> str:
    """Rewrite relative markdown links to absolute GitHub blob URLs.

    Only rewrites links whose URL looks like a repo-relative file path
    (alphanumeric characters, dots, slashes, hyphens, underscores).
    Links that already start with http/https/# and anything inside
    fenced code blocks are left unchanged.
    """
    # Walk line-by-line so fenced blocks may safely contain backticks.
    # The regex-split approach (```[^`]*```) breaks when code inside a
    # fence contains inline backticks, because [^`]* stops at the first one.
    link_re = re.compile(
        r"\[([^\]]+)\]\((?!https?://|#)([A-Za-z0-9_./#-][A-Za-z0-9_./#-]*)\)"
    )
    parts_inner: list[str] = []
    in_fence = False
    fence_marker: str | None = None
    for line in text.splitlines(keepends=True):
        m = re.match(r"^\s*(```|~~~)", line)
        if m:
            marker = m.group(1)
            if not in_fence:
                in_fence = True
                fence_marker = marker
            elif marker == fence_marker:
                in_fence = False
                fence_marker = None
            parts_inner.append(line)
            continue
        if in_fence:
            parts_inner.append(line)
        else:
            parts_inner.append(link_re.sub(
                lambda m: f"[{m.group(1)}]({REPO}/blob/main/{m.group(2)})", line
            ))
    return "".join(parts_inner)


def build_llms_full_txt(version: str) -> str:
    """Compile core language documentation into a single markdown file.

    Includes: language reference (SKILL.md), agent instructions (AGENTS.md),
    FAQ, error code reference, and formal grammar. For full documentation
    including the spec chapters and supplementary docs, see the individual
    files listed in llms.txt.
    """
    parts: list[str] = []

    def section(title: str, content: str) -> None:
        parts.append(f"\n{'=' * 72}")
        parts.append(f"# {title}")
        parts.append(f"{'=' * 72}\n")
        parts.append(_abs_links(content.strip()))
        parts.append("")

    # Header
    parts.append("# Vera — Language Reference Documentation")
    parts.append("")
    parts.append(
        "> Vera is a statically typed, purely functional programming "
        "language designed for large language models to write. It uses "
        "typed slot references (@T.n) instead of variable names, requires "
        "contracts on every function, and compiles to WebAssembly."
    )
    parts.append("")
    parts.append(
        "This file contains the core Vera language documentation — "
        "language reference, agent instructions, FAQ, error codes, and "
        f"formal grammar — compiled into a single document. Version {version}. "
        "For the full documentation index including the 13-chapter "
        "specification and supplementary docs, see llms.txt."
    )
    parts.append("")

    # SKILL.md (strip YAML frontmatter)
    skill = (ROOT / "SKILL.md").read_text(encoding="utf-8")
    skill = re.sub(r"^---\n.*?\n---\n", "", skill, flags=re.DOTALL)
    section("Language Reference (SKILL.md)", skill)

    # AGENTS.md
    section("Agent Instructions (AGENTS.md)", (ROOT / "AGENTS.md").read_text(encoding="utf-8"))

    # FAQ.md
    section(
        "Frequently Asked Questions (FAQ.md)", (ROOT / "FAQ.md").read_text(encoding="utf-8")
    )

    # Error codes
    error_lines = [
        "## Error Code Reference\n",
        "Every diagnostic has a stable error code. "
        "Codes are grouped by compiler phase:\n",
        "| Range | Phase |",
        "|-------|-------|",
        "| E001-E009 | Parse errors |",
        "| E010 | Transform errors |",
        "| E1xx | Type check: core + expressions |",
        "| E2xx | Type check: calls |",
        "| E3xx | Type check: control flow |",
        "| E5xx | Verification |",
        "| E6xx | Code generation |",
        "| E7xx | Testing |",
        "",
    ]
    for line in (ROOT / "vera" / "errors.py").read_text(encoding="utf-8").splitlines():
        m = re.match(r'\s+"(E\d+)":\s+"(.+)"', line)
        if m:
            error_lines.append(f"- **{m.group(1)}**: {m.group(2)}")
    section("Error Codes (vera/errors.py)", "\n".join(error_lines))

    # Grammar
    grammar = (ROOT / "vera" / "grammar.lark").read_text(encoding="utf-8")
    section(
        "Grammar (vera/grammar.lark)",
        f"## Formal Grammar (Lark LALR(1))\n\n```lark\n{grammar}\n```",
    )

    return "\n".join(parts)


# ── robots.txt ──────────────────────────────────────────────────────


def build_robots_txt() -> str:
    """Build an AI-crawler-friendly robots.txt."""
    return f"""\
# veralang.dev — AI agents welcome
User-agent: *
Allow: /

# AI-readable documentation
# See https://llmstxt.org for the llms.txt specification
Sitemap: {SITE}/sitemap.xml
"""


# ── sitemap.xml ─────────────────────────────────────────────────────


def build_sitemap_xml() -> str:
    """Build an XML sitemap for the site."""
    today = date.today().isoformat()
    urls = [
        (f"{SITE}/", "1.0", "weekly"),
        (f"{SITE}/SKILL.md", "0.9", "weekly"),
        (f"{SITE}/llms.txt", "0.8", "weekly"),
        (f"{SITE}/llms-full.txt", "0.8", "weekly"),
        (f"{SITE}/index.md", "0.5", "weekly"),
    ]
    url_entries = []
    for loc, priority, freq in urls:
        url_entries.append(
            f"  <url>\n"
            f"    <loc>{loc}</loc>\n"
            f"    <lastmod>{today}</lastmod>\n"
            f"    <changefreq>{freq}</changefreq>\n"
            f"    <priority>{priority}</priority>\n"
            f"  </url>"
        )
    return (
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
        + "\n".join(url_entries)
        + "\n</urlset>\n"
    )


# ── index.md ────────────────────────────────────────────────────────


def build_index_md(version: str) -> str:
    """Build a Markdown companion of the landing page.

    Mirrors the structure and substance of docs/index.html so agents that
    fetch the .md alternate see the same content that human readers see —
    thesis, code samples, VeraBench data, runtime story, install steps, and
    the agent-facing documents. Kept in sync with the HTML hand-edited by a
    human designer; if the HTML's substance changes, update this too.
    """
    n_examples = _count_examples()
    return f"""\
# Vera — A language designed for machines to write

> Vera is a programming language designed for large language models to write, not humans. It uses typed slot references (`@T.n`) instead of variable names, requires contracts on every function, and compiles to WebAssembly. Programs run at the command line via wasmtime or in any browser with a self-contained JavaScript runtime.

From the Latin *veritas* — truth. In Vera, verification is a first-class citizen.

**Current version:** [{version}]({REPO}/releases/tag/v{version})  ·  [GitHub]({REPO})  ·  [SKILL.md]({SITE}/SKILL.md) (agent language reference)

## Why?

Programming languages have always co-evolved with their users. Assembly emerged from hardware constraints. C from operating systems. Python from productivity needs. If models become the primary authors of code, it follows that languages should adapt to that too.

> The biggest problem models face isn't syntax — it's coherence over scale. Models are pattern matchers optimising for local plausibility, not architects holding the entire system in mind.

The [empirical literature](https://arxiv.org/abs/2307.12488) shows models are particularly vulnerable to naming-related errors: choosing misleading names, reusing names incorrectly, and losing track of which name refers to which value. Vera addresses this by making everything explicit and verifiable.

The model doesn't need to be right. It needs to be *checkable*. Names are replaced by structural references. Contracts are mandatory. Effects are typed. Every function is a specification the compiler verifies against its implementation.

For deeper questions about the design — why no variable names, what gets verified, how Vera compares to Dafny, Lean, and Koka — see the [FAQ]({RAW}/FAQ.md).

## What Vera Looks Like

Nothing is implicit. The signature declares types, preconditions, postconditions, and effects. The compiler verifies the contract via SMT solver. Division by zero is not a runtime error — it is a type error.

```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{{
  @Int.0 / @Int.1
}}
```

Read the slots: `@Int.1` is the first parameter, `@Int.0` is the second — De Bruijn indexing, most-recent first. No variable names means no naming bug is possible. The `requires` clause is what lifts divide-by-zero from a runtime crash to a compile-time error.

```vera
public fn fizzbuzz(@Nat -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{{
  if @Nat.0 % 15 == 0 then {{
    "FizzBuzz"
  }} else {{
    if @Nat.0 % 3 == 0 then {{
      "Fizz"
    }} else {{
      if @Nat.0 % 5 == 0 then {{
        "Buzz"
      }} else {{
        "\\(@Nat.0)"
      }}
    }}
  }}
}}
```

A program everyone knows. Interpolation uses `"\\(@Nat.0)"` — the slot reference substitutes in directly with auto-conversion. There are no naming decisions to make, and none to hallucinate.

```vera
public fn classify_sentiment(@String -> @Result<String, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Inference>)
{{
  let @String = string_concat("Classify as Positive, Negative, or Neutral: ", @String.0);
  Inference.complete(@String.0)
}}
```

LLM calls are effects. Where the two functions above are `effects(pure)`, this one declares `<Inference>`. A caller that does not permit `<Inference>` cannot invoke it. The effect system makes model calls visible in every signature that uses them, all the way up.

```vera
public fn research_topic(@String -> @Result<String, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Http, Inference>)
{{
  let @Result<String, String> = Http.get(string_concat("https://api.duckduckgo.com/?format=json&q=", @String.0));
  match @Result<String, String>.0 {{
    Ok(@String) -> Inference.complete(string_concat("Summarise this in one paragraph:\\n\\n", @String.0)),
    Err(@String) -> Err(@String.0)
  }}
}}
```

Effects compose. `<Http, Inference>` is the row — both must be permitted. `Inference` auto-detects the provider (Anthropic, OpenAI, Moonshot) from whichever API key is set. Postconditions can constrain model output; Z3 cannot know what a model will return at compile time, so these become runtime assertions that trap on violation.

When you get it wrong, every error is an instruction for the model that wrote the code:

```
[E001] Error at main.vera, line 14, column 1:

    {{
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
      {{
        ...
      }}

  See: Chapter 5, Section 5.1 "Function Structure"
```

Parse errors, type errors, effect mismatches, verification failures, and contract violations all produce the same shape: what went wrong, why, how to fix it, and a spec reference.

## VeraBench

**Kimi K2.5 writes 100% correct Vera — beating its own 86% on Python and 91% on TypeScript.**

A 60-problem benchmark across 5 difficulty tiers — pure arithmetic, ADTs, recursion, closures, multi-function effect propagation. Six models, three providers, four modes each. The numbers below are run-correct rates.

| Model | Mode | Vera | Python | TypeScript |
|---|---|---|---|---|
| Kimi K2.5 | flagship | **100%** | 86% | 91% |
| GPT-4.1 | flagship | 91% | 96% | 96% |
| Claude Opus 4 | flagship | 88% | 96% | 96% |
| Kimi K2 Turbo | sonnet | **83%** | 88% | 79% |
| Claude Sonnet 4 | sonnet | 79% | 96% | 88% |
| GPT-4o | sonnet | 78% | 93% | 83% |

In our latest results **Kimi K2.5 writes perfect Vera code** — 100% run_correct, beating both Python (86%) and TypeScript (91%); Kimi K2 Turbo also writes better Vera than TypeScript. In the previous [v0.0.4]({REPO}-bench/releases/tag/v0.0.4) benchmark Claude Sonnet 4 wrote Vera better than TypeScript (83% vs 79%); the latest v0.0.7 re-run flipped that result, illustrating the variance inherent in single-run evaluation and model non-determinism.

Mandatory contracts and typed slot references appear to provide enough structure to compensate for zero training data. Still early days — 60 problems, single run per model. Stable rates will require pass@k evaluation with multiple trials. Results from [VeraBench v0.0.7]({REPO}-bench/releases/tag/v0.0.7) against [Vera v0.0.108]({REPO}/releases/tag/v0.0.108). Inspired by [HumanEval](https://github.com/openai/human-eval), [MBPP](https://github.com/google-research/google-research/tree/master/mbpp), and [DafnyBench](https://github.com/sun-wendy/DafnyBench).

Full source and data: [{REPO}-bench]({REPO}-bench).

## Design Principles

1. **Checkability over correctness** — Code the compiler can mechanically check. Every diagnostic carries a concrete fix in natural language.
2. **Explicitness over convenience** — All state changes declared. All effects typed. All contracts mandatory. No implicit behaviour.
3. **One canonical form** — Every construct has exactly one textual representation. `vera fmt` settles it.
4. **Structural references over names** — Bindings referenced by type and positional index (`@T.n`), not arbitrary names.
5. **Contracts as the source of truth** — Every function declares what it requires and guarantees. The compiler verifies statically where possible.
6. **Constrained expressiveness** — Fewer valid programs means fewer opportunities for the model to be wrong.

## Key Features

- **No variable names** — Typed [De Bruijn indices]({RAW}/DE_BRUIJN.md) (`@T.n`) replace variable names: `@Int.0` is the most-recent `Int` binding, `@Int.1` the one before. The whole class of naming hallucinations is removed at the language level, not caught after the fact.
- **Full contracts** — Mandatory preconditions, postconditions, invariants, and effect declarations on every function. Z3 generates test inputs from the contracts and runs them through WASM — no manual test cases.
- **Algebraic effects** — IO, Http, State, Exceptions, Async, Inference — declared, typed, and handled explicitly. Pure by default.
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
git clone {REPO}.git
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

Editor support: [TextMate `.tmbundle`]({REPO}/tree/main/editors/textmate), [VS Code extension]({REPO}/tree/main/editors/vscode).

## For Agents

This page is also a machine-readable specification. Every document here has an alternate in markdown, served on the same domain, discoverable through standard `<link rel="alternate">`, `llms.txt`, and the Mintlify `llms-txt` / `llms-full-txt` conventions.

- [`SKILL.md`]({SITE}/SKILL.md) — Complete language reference for writing Vera code: syntax, slots, contracts, effects, common mistakes, working examples.
- [`AGENTS.md`]({RAW}/AGENTS.md) — Setup instructions for any agent system (Copilot, Cursor, Windsurf, custom). Writing Vera code and working on the compiler.
- [`CLAUDE.md`]({RAW}/CLAUDE.md) — Project orientation for Claude Code. Key commands, repo layout, workflows, invariants.

Claude Code discovers `SKILL.md` and `CLAUDE.md` automatically when working inside the repo. For other projects, install the skill manually:

```bash
mkdir -p ~/.claude/skills/vera-language
cp /path/to/vera/SKILL.md ~/.claude/skills/vera-language/SKILL.md
```

For other models: point them at [`SKILL.md`]({SITE}/SKILL.md) via system prompt, file attachment, or retrieval. It's self-contained and works with any model that reads markdown.

## Status

Vera is under [active development]({RAW}/ROADMAP.md). A complete compiler with 164 built-in functions, six algebraic effects (IO, Http, State, Exceptions, Async, Inference), contract-driven testing via [Z3](https://www.microsoft.com/en-us/research/project/z3-3/), and a 13-chapter specification. A 77-program conformance suite and {n_examples} worked examples are validated against the spec on every pull request. All of it is developed openly on [GitHub]({REPO}) and released under the MIT licence.

## Links

- [GitHub]({REPO})
- [README]({RAW}/README.md)
- [SKILL.md]({SITE}/SKILL.md)
- [AGENTS.md]({RAW}/AGENTS.md)
- [Specification]({REPO}/tree/main/spec)
- [Roadmap]({RAW}/ROADMAP.md)
- [History]({RAW}/HISTORY.md)
- [Changelog]({RAW}/CHANGELOG.md)
- [Contributing]({RAW}/CONTRIBUTING.md)
- [Issues]({REPO}/issues)
- [VeraBench]({REPO}-bench)
- [MIT Licence]({REPO}/blob/main/LICENSE)
"""


# ── SKILL.md ────────────────────────────────────────────────────────


def build_skill_md() -> str:
    """Return SKILL.md with relative links rewritten to absolute GitHub URLs.

    The source of truth is the top-level SKILL.md.  This copy in docs/ is a
    generated artefact that makes the language reference available at
    veralang.dev/SKILL.md — same domain as the website, cacheable, stable.
    Relative links are rewritten to absolute GitHub blob URLs because this
    file is consumed outside the repository context.
    """
    return _abs_links((ROOT / "SKILL.md").read_text(encoding="utf-8"))


# ── main ────────────────────────────────────────────────────────────


def main() -> int:
    version = _version()
    files = {
        "llms.txt": build_llms_txt(version),
        "llms-full.txt": build_llms_full_txt(version),
        "robots.txt": build_robots_txt(),
        "sitemap.xml": build_sitemap_xml(),
        "index.md": build_index_md(version),
        "SKILL.md": build_skill_md(),
    }
    DOCS.mkdir(parents=True, exist_ok=True)
    for name, content in files.items():
        path = DOCS / name
        path.write_text(content, encoding="utf-8")
        chars = len(content)
        print(f"  {name:20s}  {chars:>8,} chars  (~{chars // 4:,} tokens)")
    print(f"\nGenerated {len(files)} files in docs/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
