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

# The repo root (not `scripts/`, which the next line adds for the
# doc_annotations sibling import below) must precede site-packages on
# sys.path BEFORE the `from vera...` import: `import vera` otherwise falls
# through to whichever venv's editable-install finder answers first —
# pinned to whatever checkout `pip install -e` last ran in, which can be a
# different worktree entirely (plan-file S13; see TESTING.md's "Running
# against ANOTHER checkout" section for the sibling pytest-rootdir trap
# this is NOT — a different mechanism with a different remedy).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parent))

# The doc gates' inline <!-- vera:skip-... --> fence annotations (#538) are
# repo-tooling metadata: strip them from every generated site asset.
from doc_annotations import strip_annotations

# Single-sourced E001 doc example (#954): render_e001_doc_example() is the
# same call README.md, spec/00-introduction.md, and tests/test_errors.py's
# TestErrorDisplaySync all use, so docs/index.md's copy cannot drift from
# vera.errors on its own.
from vera.errors import render_e001_doc_example

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
All side effects (IO, Http, HttpServer, State, Exceptions, Async, Inference, \
DB, Random, Diverge) are tracked in the type system via algebraic effects.

Current version: {version}. The reference compiler is written in Python. \
Install the `veralang` distribution from PyPI or use `pip install -e ".[dev]"` from \
the repository.

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
- [LSP_SERVER.md]({RAW}/LSP_SERVER.md): The language server — live \
proof-aware diagnostics, hover, slot go-to-definition, hole completion, \
and the custom proof-delta methods for coding agents \
(vera/speculativeEdit, vera/proposeEdit, vera/strengthenContract, \
vera/addEffect).

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
handlers, IO, Http, HttpServer, State, Exceptions, Async, Inference, DB, Random, and Diverge.
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
- [Chapter 13: WASI Preview 2 Target]({RAW}/spec/13-wasi.md): The \
`wasi-p2` compilation target — experimental WASI 0.2 components, the \
`--world server` wasi:http backend, and the divergences from the core runtime.
- [Implementation Status]({SITE}/implementation-status.md): Every \
`Status:` callout in the specification, collected — the boundary between \
what the reference compiler ships and what the chapters describe.

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
    # The optional leading ``!`` captures image embeds: an image must point
    # at the RAW host (actual bytes) — a ``blob/`` URL is an HTML page and
    # renders as a broken image wherever llms-full.txt is displayed.  Plain
    # links keep the human-facing ``blob/`` pages.
    link_re = re.compile(
        r"(!?)\[([^\]]+)\]\((?!https?://|#)([A-Za-z0-9_./#-][A-Za-z0-9_./#-]*)\)"
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
                lambda m: (
                    f"![{m.group(2)}]({RAW}/{m.group(3)})"
                    if m.group(1)
                    else f"[{m.group(2)}]({REPO}/blob/main/{m.group(3)})"
                ),
                line,
            ))
    return "".join(parts_inner)


def build_llms_full_txt(version: str) -> str:
    """Compile core language documentation into a single markdown file.

    Includes: language reference (SKILL.md), agent instructions (AGENTS.md), the language-server manual (LSP_SERVER.md),
    FAQ, error code reference, and formal grammar. For full documentation
    including the spec chapters and supplementary docs, see the individual
    files listed in llms.txt.
    """
    parts: list[str] = []

    def section(title: str, content: str) -> None:
        parts.append(f"\n{'=' * 72}")
        parts.append(f"# {title}")
        parts.append(f"{'=' * 72}\n")
        parts.append(_abs_links(strip_annotations(content).strip()))
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
        "For the full documentation index including the 14-chapter "
        "specification and supplementary docs, see llms.txt."
    )
    parts.append("")

    # SKILL.md (strip YAML frontmatter)
    skill = (ROOT / "SKILL.md").read_text(encoding="utf-8")
    skill = re.sub(r"^---\n.*?\n---\n", "", skill, flags=re.DOTALL)
    section("Language Reference (SKILL.md)", skill)

    # AGENTS.md
    section("Agent Instructions (AGENTS.md)", (ROOT / "AGENTS.md").read_text(encoding="utf-8"))

    # LSP_SERVER.md
    section(
        "Language Server (LSP_SERVER.md)",
        (ROOT / "LSP_SERVER.md").read_text(encoding="utf-8"),
    )

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


#: A `Status:` callout in the specification — the marker a chapter uses to
#: say that what it describes is not (or is only partly) implemented.  Two
#: spellings are in use and both are discovered: a blockquote callout, and
#: the bare paragraph form used in Chapter 13.  Matching only the blockquote
#: form would silently drop the WASI chapter's, which is exactly the kind of
#: omission this appendix exists to make impossible.
_STATUS_CALLOUT_RE = re.compile(r"^(?:>\s*)?\*\*Status:", re.IGNORECASE)
_HEADING_RE = re.compile(r"^(#{1,6})\s+(.+?)\s*$")


def _status_callouts(path: Path) -> list[tuple[str, int, str]]:
    """Every `Status:` callout in *path* as (heading, line number, text).

    The heading is the nearest preceding ATX heading, so a reader can find
    the callout in its chapter without a line number.  The text keeps its
    inline links intact — the issue each one cites is the actionable half.
    """
    out: list[tuple[str, int, str]] = []
    lines = path.read_text(encoding="utf-8").splitlines()
    heading = ""
    i = 0
    while i < len(lines):
        line = lines[i]
        m = _HEADING_RE.match(line)
        if m is not None:
            heading = m.group(2)
            i += 1
            continue
        if _STATUS_CALLOUT_RE.match(line):
            start = i
            quoted = line.lstrip().startswith(">")
            body: list[str] = []
            while i < len(lines):
                cur = lines[i]
                if quoted:
                    if not cur.lstrip().startswith(">"):
                        break
                    body.append(cur.lstrip()[1:].lstrip())
                else:
                    # Bare paragraph: runs to the first blank line.
                    if not cur.strip():
                        break
                    body.append(cur.strip())
                i += 1
            out.append((heading, start + 1, " ".join(body).strip()))
            continue
        i += 1
    return out


def build_impl_status() -> str:
    """The shipped-versus-specified boundary, collected from the spec itself.

    The specification marks every gap between what it describes and what the
    reference compiler does with a `Status:` callout.  Those callouts are
    accurate but scattered across fourteen chapters, so the boundary they
    describe has never been readable in one place.  This page is that place,
    and it is generated: a callout added to a chapter appears here without
    anyone remembering to copy it, and one removed disappears.
    """
    chapters = sorted(
        (ROOT / "spec").glob("*.md"), key=lambda p: p.name,
    )
    sections: list[str] = []
    total = 0
    for chapter in chapters:
        callouts = _status_callouts(chapter)
        if not callouts:
            continue
        total += len(callouts)
        rel = chapter.relative_to(ROOT).as_posix()
        sections.append(f"## [{rel}]({RAW}/{rel})\n")
        for heading, line, text in callouts:
            where = heading or "(chapter preamble)"
            sections.append(f"### {where}\n")
            sections.append(f"{text}\n")
    body = "\n".join(sections)
    n_chapters = sum(1 for c in chapters if _status_callouts(c))
    return f"""<!-- GENERATED FILE — do not edit.
     Source: scripts/build_site.py (build_impl_status).
     Regenerate: python scripts/build_site.py -->

# Implementation Status

Vera's specification describes the language; the reference compiler implements most of it. Where the two stand apart, the chapter says so in a `Status:` callout — usually naming a gap, sometimes recording that a feature has landed. This page collects every one of those callouts — {total} across {n_chapters} chapters — so the boundary between what is shipped and what is specified is readable in one place.

Each entry keeps its chapter's wording, including the issue it cites. The specification remains the normative source; this page is an index into it.

{body}"""


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


def _without_lastmod(sitemap: str) -> str:
    """Blank out ``<lastmod>`` values so two sitemaps compare equal when only
    their build dates differ (the date is noise, not content)."""
    return re.sub(r"<lastmod>[^<]*</lastmod>", "<lastmod></lastmod>", sitemap)


def build_sitemap_xml() -> str:
    """Build an XML sitemap for the site.

    ``<lastmod>`` dates are preserved from the committed sitemap whenever the
    URL set is otherwise unchanged.  Most rebuilds are triggered by an
    unrelated source edit (the ``site-assets`` pre-commit hook fires on
    ``vera/errors.py``, ``SKILL.md``, etc.); rewriting the dates to
    ``date.today()`` on each one churns a field that carries no real signal —
    and trips the hook into a "files were modified by this hook" failure on the
    first commit.  The dates refresh only when the URL set actually changes.
    """
    today = date.today().isoformat()
    urls = [
        (f"{SITE}/", "1.0", "weekly"),
        (f"{SITE}/SKILL.md", "0.9", "weekly"),
        (f"{SITE}/llms.txt", "0.8", "weekly"),
        (f"{SITE}/llms-full.txt", "0.8", "weekly"),
        (f"{SITE}/index.md", "0.5", "weekly"),
        (f"{SITE}/implementation-status.md", "0.5", "weekly"),
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
    new = (
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
        + "\n".join(url_entries)
        + "\n</urlset>\n"
    )
    existing_path = DOCS / "sitemap.xml"
    if existing_path.exists():
        existing = existing_path.read_text(encoding="utf-8")
        if _without_lastmod(existing) == _without_lastmod(new):
            return existing
    return new


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
    n_conformance = _count_conformance()
    e001_example = render_e001_doc_example()
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

![The loop: the model writes Vera with mandatory contracts; the compiler type-checks every program, proves supported contract obligations via Z3, guards most of the rest at runtime, and discloses what it can neither prove nor guard; when it's wrong the diagnostics return — description, rationale, fix, spec_ref — and when the proofs hold it ships as one .wasm for CLI and browser, or a WASI component.]({SITE}/loop-web.svg)

For deeper questions about the design — why no variable names, what gets verified, how Vera compares to Dafny, Lean, and Koka — see the [FAQ]({RAW}/FAQ.md).

## What Vera Looks Like

Nothing is implicit. The signature declares types, preconditions, postconditions, and effects. The compiler verifies the contract via SMT solver. A zero divisor the verifier can witness is a compile error (`E526`), not a runtime crash.

```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{{
  @Int.0 / @Int.1
}}
```

Read the slots: `@Int.1` is the first parameter, `@Int.0` is the second — De Bruijn indexing, most-recent first. No local variable names means no local naming bug is possible — references are type-directed and positional. The `requires` clause is what discharges the divisor obligation: with it the division proves at compile time; without it the compiler refuses the program with `E526` and a counterexample, and only a divisor it can neither prove non-zero nor witness a zero for falls to a runtime guard. [examples/safe_divide.vera]({REPO}/blob/main/examples/safe_divide.vera).

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

A program everyone knows. Interpolation uses `"\\(@Nat.0)"` — the slot reference substitutes in directly with auto-conversion. There are no naming decisions to make, and none to hallucinate. [examples/fizzbuzz.vera]({REPO}/blob/main/examples/fizzbuzz.vera).

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

LLM calls are effects. Where the two functions above are `effects(pure)`, this one declares `<Inference>`. A caller that does not permit `<Inference>` cannot invoke it. The effect system makes model calls visible in every signature that uses them, all the way up. [examples/inference.vera]({REPO}/blob/main/examples/inference.vera).

```vera
public fn research_topic(@String -> @Result<String, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Http, Inference>)
{{
  let @String = url_encode(@String.0);
  let @Result<String, String> = Http.get(string_concat("https://api.duckduckgo.com/?format=json&q=", @String.0));
  match @Result<String, String>.0 {{
    Ok(@String) -> Inference.complete(string_concat("Summarise this in one paragraph:\\n\\n", @String.0)),
    Err(@String) -> Err(@String.0)
  }}
}}
```

Effects compose. `<Http, Inference>` is the row — both must be permitted. `Inference` auto-detects the provider (Anthropic, OpenAI, Moonshot, Mistral, xAI, DeepSeek) from whichever API key is set to a non-empty value. Postconditions can constrain model output; Z3 cannot know what a model will return at compile time, so these become runtime assertions that trap on violation.

```vera
public fn find_user(@String -> @Result<Array<Array<Option<String>>>, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<DB>)
{{
  DB.query("SELECT name, email FROM users WHERE name = ?", [Some(@String.0)])
}}
```

SQL injection won't compile. Nearly every SQL injection starts the same way — a query assembled from a value that came from outside the program. Vera makes that unwriteable. The SQL text has to be written into the source, so the query is fixed when the program compiles and outside data can only reach the database through the `?` placeholders and the params array. Build the query out of the parameter with `string_concat` instead and the answer is `[E207]`: not a warning, not a lint you can silence, but a type error you cannot configure away. [examples/database.vera]({REPO}/blob/main/examples/database.vera).

When you get it wrong, every error is an instruction for the model that wrote the code:

```
{e001_example}
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

Results from [VeraBench v0.0.18]({REPO}-bench#results) against [Vera v0.1.8]({REPO}/releases/tag/v0.1.8). Inspired by [HumanEval](https://github.com/openai/human-eval), [MBPP](https://github.com/google-research/google-research/tree/master/mbpp), and [DafnyBench](https://github.com/sun-wendy/DafnyBench).

Full source and data: [{REPO}-bench]({REPO}-bench).

## Design Principles

1. **Checkability over correctness** — Code the compiler can mechanically check. Every diagnostic carries a concrete fix in natural language.
2. **Explicitness over convenience** — All state changes declared. All effects typed. All contracts mandatory. No implicit behaviour.
3. **One canonical form** — One preferred spelling per construct; formatting is deterministic and idempotent. `vera fmt` settles it.
4. **Structural references over names** — Bindings referenced by type and positional index (`@T.n`), not arbitrary names.
5. **Contracts as the source of truth** — Every function declares what it requires and guarantees. The compiler verifies statically where possible.
6. **Constrained expressiveness** — Fewer valid programs means fewer opportunities for the model to be wrong.

## Key Features

- **No variable names** — Typed [De Bruijn indices]({RAW}/DE_BRUIJN.md) (`@T.n`) replace variable names: `@Int.0` is the most-recent `Int` binding, `@Int.1` the one before. The whole class of naming hallucinations is removed at the language level, not caught after the fact.
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

Self-contained — no bundler. Serve with any HTTP server (`python -m http.server`). `IO.print` writes to the page; every other operation the browser target supports works identically to the CLI, apart from `md_parse`, whose two hand-written implementations still disagree on a few shapes the §9.7.3 subset does not pin ([#1301](https://github.com/aallan/vera/issues/1301)). `json_stringify` and `md_render` reach that identity by emitting a canonical form the specification states (§9.7.1, §9.7.3) rather than by the hosts happening to agree, and `json_parse` by accepting the domain §9.7.1 states — RFC 8259-valid text that decodes to finite numbers and strings of Unicode scalar values — rather than whatever its host parser admits; parity tests check all three against that stated form as well as against each other, on every PR. *Note: `Inference.complete` and every `DB` operation return an error in the browser — a deliberate platform boundary, since the credentials they need would be readable from page source; reach them through a server-side proxy via `Http`.*

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
git clone {REPO}.git
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

Editor support: [Vera Language for VS Code](https://marketplace.visualstudio.com/items?itemName=veralang.vera-language) (`code --install-extension veralang.vera-language`; [source]({REPO}/tree/main/editors/vscode)), a [Vim package]({REPO}/tree/main/editors/vim-veralang) for Vim 8+ and Neovim, and a [TextMate `.tmbundle`]({REPO}/tree/main/editors/textmate) for Sublime Text and other TextMate-grammar editors.

## For Agents

This page is also a machine-readable specification. Every document here has an alternate in markdown, served on the same domain, discoverable through standard `<link rel="alternate">`, `llms.txt`, and the Mintlify `llms-txt` / `llms-full-txt` conventions.

- [`SKILL.md`]({SITE}/SKILL.md) — Complete language reference for writing Vera code: syntax, slots, contracts, effects, common mistakes, working examples.
- [`LSP_SERVER.md`]({RAW}/LSP_SERVER.md) — The language server: live proof-aware diagnostics and the custom proof-delta methods agents use to ask “does this edit still prove?” before committing it.
- [`AGENTS.md`]({RAW}/AGENTS.md) — Setup instructions for any agent system (Copilot, Cursor, Windsurf, custom). Writing Vera code and working on the compiler.
- [`CLAUDE.md`]({RAW}/CLAUDE.md) — Project orientation for Claude Code. Key commands, repo layout, workflows, invariants.

Claude Code discovers `SKILL.md` and `CLAUDE.md` automatically when working inside the repo. For other projects, install the skill manually:

```bash
mkdir -p ~/.claude/skills/vera-language
cp /path/to/vera/SKILL.md ~/.claude/skills/vera-language/SKILL.md
```

For other models: point them at [`SKILL.md`]({SITE}/SKILL.md) via system prompt, file attachment, or retrieval. It's self-contained and works with any model that reads markdown.

## Status

Vera is under [active development]({RAW}/ROADMAP.md). A complete compiler with 164 built-in functions, ten algebraic effects (IO, Http, HttpServer, State, Exceptions, Async, Inference, DB, Random, Diverge), contract-driven testing via [Z3](https://www.microsoft.com/en-us/research/project/z3-3/), and a 14-chapter specification. A {n_conformance}-program conformance suite and {n_examples} worked examples are validated against the spec on every pull request. All of it is developed openly on [GitHub]({REPO}) and released under the MIT licence.

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
    file is consumed outside the repository context, and the doc gates'
    vera:skip fence annotations (#538) are stripped for the same reason.
    """
    return _abs_links(
        strip_annotations((ROOT / "SKILL.md").read_text(encoding="utf-8"))
    )


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
        "implementation-status.md": build_impl_status(),
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
