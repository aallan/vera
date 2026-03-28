#!/usr/bin/env python3
"""Build AI-readable site assets for veralang.dev.

Auto-generates from source documentation:
  - docs/llms.txt        Curated index (llms.txt spec)
  - docs/llms-full.txt   Complete docs in one file
  - docs/robots.txt      AI-crawler-friendly robots.txt
  - docs/sitemap.xml     XML sitemap
  - docs/index.md        Markdown companion of index.html

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

## Language Reference

- [SKILL.md]({RAW}/SKILL.md): Complete language reference — syntax, types, \
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


def build_llms_full_txt(version: str) -> str:
    """Compile complete documentation into a single markdown file."""
    parts: list[str] = []

    def section(title: str, content: str) -> None:
        parts.append(f"\n{'=' * 72}")
        parts.append(f"# {title}")
        parts.append(f"{'=' * 72}\n")
        parts.append(content.strip())
        parts.append("")

    # Header
    parts.append("# Vera — Complete Language Documentation")
    parts.append("")
    parts.append(
        "> Vera is a statically typed, purely functional programming "
        "language designed for large language models to write. It uses "
        "typed slot references (@T.n) instead of variable names, requires "
        "contracts on every function, and compiles to WebAssembly."
    )
    parts.append("")
    parts.append(
        "This file contains the complete Vera documentation compiled "
        f"into a single document. Version {version}."
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
    """Build a Markdown companion of the landing page."""
    n_examples = _count_examples()
    return f"""\
# Vera — A language designed for machines to write

> Vera is a statically typed, purely functional programming language \
designed for large language models to write. It uses typed slot references \
(`@T.n`) instead of variable names, requires contracts on every function, \
and compiles to WebAssembly.

**Current version:** [{version}]({REPO}/releases/tag/v{version})

## Why?

Programming languages have always co-evolved with their users. Assembly \
emerged from hardware constraints. C from operating systems. Python from \
productivity needs. If models become the primary authors of code, it \
follows that languages should adapt to that too.

The evidence suggests the biggest problem models face isn't syntax — it's \
coherence over scale. Models struggle with maintaining invariants across a \
codebase, understanding the ripple effects of changes, and reasoning about \
state over time.

## Design Principles

1. **Checkability over correctness** — Every program is machine-verifiable. \
The compiler proves properties via Z3, not just checks syntax.
2. **Explicitness over convenience** — No implicit state, no hidden control \
flow. Every effect is declared, every contract is visible.
3. **One canonical form** — The formatter produces a single representation. \
No style debates, no ambiguity.
4. **Structural references over names** — Typed De Bruijn indices (`@Int.0`) \
eliminate naming errors entirely.
5. **Contracts as the source of truth** — Preconditions, postconditions, \
and effect declarations are the specification. The compiler enforces them.
6. **Constrained expressiveness** — Fewer ways to write the same thing means \
fewer ways to get it wrong.

## Key Features

- **No variable names** — Typed slot references (`@Int.0`, `@String.1`) \
using De Bruijn indexing
- **Mandatory contracts** — `requires(...)`, `ensures(...)`, `effects(...)` \
on every function
- **Algebraic effects** — IO, Http, State, Exceptions, Async, Inference \
tracked in the type system
- **LLM inference** — `Inference.complete` as a first-class algebraic \
effect; model calls are typed, contract-verifiable, and mockable
- **Z3 verification** — Contracts proved statically by the Z3 SMT solver
- **Contract-driven testing** — Z3 generates test inputs from contracts
- **WebAssembly** — Compiles to WASM, runs via wasmtime or in the browser
- **Built-in data types** — JSON, HTML, Markdown, Map, Set, Decimal with \
typed parse/query/serialize operations
- **HTTP** — `Http.get` and `Http.post` as algebraic effects, composing \
with JSON for verified API access
- **String interpolation** — `"value: \\(@Int.0)"` with auto-conversion
- **Pattern matching** — Exhaustive ADT matching with nested patterns
- **Constrained generics** — Four built-in abilities (Eq, Ord, Hash, Show) \
with monomorphization

## Quick Start

```bash
git clone {REPO}.git && cd vera
python -m venv .venv && source .venv/bin/activate
pip install -e .
vera run examples/hello_world.vera
```

## Documentation

- [SKILL.md]({RAW}/SKILL.md) — Complete language reference
- [AGENTS.md]({RAW}/AGENTS.md) — Instructions for AI agents
- [EXAMPLES.md]({RAW}/EXAMPLES.md) — Language tour with code examples
- [FAQ]({RAW}/FAQ.md) — Design rationale and comparisons
- [Specification]({REPO}/tree/main/spec) — 13-chapter formal spec
- [Examples]({REPO}/tree/main/examples) — {n_examples} verified programs

## Links

- [GitHub]({REPO})
- [Roadmap]({RAW}/ROADMAP.md)
- [Changelog]({RAW}/CHANGELOG.md)
- [History]({RAW}/HISTORY.md)
- [Releases]({REPO}/releases)
- [Issues]({REPO}/issues)
- [MIT License]({REPO}/blob/main/LICENSE)
"""


# ── main ────────────────────────────────────────────────────────────


def main() -> int:
    version = _version()
    files = {
        "llms.txt": build_llms_txt(version),
        "llms-full.txt": build_llms_full_txt(version),
        "robots.txt": build_robots_txt(),
        "sitemap.xml": build_sitemap_xml(),
        "index.md": build_index_md(version),
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
