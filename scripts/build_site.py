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

# The doc gate's inline <!-- vera:skip-... --> and <!-- vera:run ... --> fence
# markers (#538, #1481) are repo-tooling metadata: strip them from every
# generated site asset.
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
`ensures(...)`, and `effects(...)`, and every recursive function a \
`decreases(...)` measure or the `Diverge` effect. The Z3 SMT solver verifies \
contracts statically where possible; every contract is also compiled as a \
runtime check where code generation can express it, and most of what can be \
neither proved nor guarded is disclosed (#1607 is a contract that is not). \
All side effects (IO, Http, HttpServer, State, Exceptions, Async, Inference, \
DB, Random, Diverge) are tracked in the type system via algebraic effects.

Current version: {version}. The reference compiler is written in Python. \
Install the `veralang` distribution from PyPI, or use `pip install -e ".[dev]"` \
from the repository — the recommended route for agents, since it includes the \
examples, conformance programs and specification the language reference \
teaches from.

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
- [TOOLCHAIN.md]({RAW}/TOOLCHAIN.md): The CLI cookbook — driving the \
toolchain to write, verify, test, run, and debug Vera, and the \
`builtins`/`effects`/`errors` introspection commands.
- [DE_BRUIJN.md]({RAW}/DE_BRUIJN.md): Typed slot references in depth — \
worked examples and the commutative-operations trap.
- [ENVIRONMENT.md]({RAW}/ENVIRONMENT.md): Every `VERA_*` environment \
variable — provider keys, runtime knobs, and debug flags.
- [KNOWN_ISSUES.md]({RAW}/KNOWN_ISSUES.md): Known bugs and limitations, \
each with its tracking issue.
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
        "Diagnostics carry stable codes: errors E001-E702 and warnings "
        "W001-W003. Codes are grouped by compiler phase:\n",
        "| Range | Phase |",
        "|-------|-------|",
        "| E001-E009 | Parse errors |",
        "| E010 | Transform errors |",
        "| E011-E013 | Import resolution |",
        "| E020-E023 | Parse: malformed comments (lexical) |",
        "| E030-E032 | Parse: contract clauses |",
        "| E1xx | Type check: core + expressions |",
        "| E2xx | Type check: calls |",
        "| E3xx | Type check: control flow |",
        "| E5xx | Verification |",
        "| E6xx | Code generation |",
        "| E7xx | Testing |",
        "| W001-W003 | Warnings |",
        "",
    ]
    for line in (ROOT / "vera" / "errors.py").read_text(encoding="utf-8").splitlines():
        m = re.match(r'\s+"([EW]\d+)":\s+"(.+)"', line)
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
# Vera: a language designed for machines to write

> Vera is a programming language designed for large language models to write, not humans. It uses typed slot references (`@T.n`) instead of variable names, requires contracts on every function, and compiles to WebAssembly. Programs run at the command line via wasmtime or in any browser with a self-contained JavaScript runtime.

From the Latin *veritas*, meaning truth. Verification is built into the language from the ground up.

**Current version:** [{version}]({REPO}/releases/tag/v{version})  ·  [GitHub]({REPO})  ·  [SKILL.md]({SITE}/SKILL.md) (agent language reference)

## Why?

Programming languages have always co-evolved with their users. Assembly emerged from hardware constraints. C from operating systems. Python from productivity needs. If models are becoming the main authors of code, the languages they write should change for them too.

> Syntax is the easy part. The hard problem for a model is coherence at scale: models are pattern matchers optimising for local plausibility, not architects holding the whole system in mind.

[Research on model-written code](https://arxiv.org/abs/2307.12488) finds that names are a particular weakness. Models pick misleading names, reuse names wrongly, and lose track of which name refers to which value. Vera takes the variable names away.

The model doesn't need to be right. It needs to be *checkable*. Structural references replace names. Contracts are mandatory. Effects are typed. Every function is a specification the compiler checks against its implementation, proving what it can with Z3 and compiling runtime checks for most of the rest.

![The loop: the model writes Vera with mandatory contracts, and the compiler type-checks it, proves contracts with Z3 and guards most of the rest at run time. When the model is wrong the diagnostics go back to it with a description, rationale, fix and spec reference; when the proofs hold, the program ships as one .wasm for the command line and the browser, or as a WASI component.]({SITE}/loop-web.svg)

The [FAQ]({RAW}/FAQ.md) goes deeper into the design: why there are no variable names, what gets verified, and how Vera compares with Dafny, Lean and Koka.

## What Vera Looks Like

Nothing is implicit. The signature declares types, preconditions, postconditions and effects, and `vera verify` proves this contract with Z3 before the program ever runs. A zero divisor the verifier can find is refused at compile time (`E526`) rather than left to crash at run time.

<!-- vera:run fn="safe_divide" args="2 10" stdout="5" -->
```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{{
  @Int.0 / @Int.1
}}
```

Read the slots. `@Int.1` is the first parameter and `@Int.0` the second: De Bruijn indexing, most recent first. With no variable names there is no naming bug to make, since every reference is typed and positional. The `requires` clause is what makes the division safe. With it, the division is proved at compile time; without it, the compiler refuses the program with `E526` and a counterexample. [examples/safe_divide.vera]({REPO}/blob/main/examples/safe_divide.vera).

<!-- vera:run fn="fizzbuzz" args="15" stdout="FizzBuzz" -->
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

A program everyone knows. Interpolation takes the slot reference directly, `"\\(@Nat.0)"`, and converts it to a string. There are no naming decisions to make, and none to hallucinate. [examples/fizzbuzz.vera]({REPO}/blob/main/examples/fizzbuzz.vera).

<!-- vera:no-run category="api-key" reason="calls Inference, which needs a provider key" -->
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

LLM calls are effects. The two functions above are `effects(pure)`; this one declares `<Inference>`, and a caller that doesn't permit `<Inference>` can't call it. A model call shows up in the signature of every function that makes one, all the way up the call chain. [examples/inference.vera]({REPO}/blob/main/examples/inference.vera).

<!-- vera:no-run category="network" reason="calls Http, so a run would reach the network" -->
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

Effects compose. The row `<Http, Inference>` says this function needs both. `Inference` picks its provider (Anthropic, OpenAI, Moonshot, Mistral, xAI or DeepSeek) from whichever API key is set. Postconditions can constrain what the model returns; Z3 can't know that at compile time, so they become runtime checks that trap on a violation.

<!-- vera:no-run category="fixture" reason="queries a users table the block does not create" -->
```vera
public fn find_user(@String -> @Result<Array<Array<Option<String>>>, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<DB>)
{{
  DB.query("SELECT name, email FROM users WHERE name = ?", [Some(@String.0)])
}}
```

SQL injection won't compile. Nearly every SQL injection starts the same way, with a query assembled from a value that came from outside the program. In Vera the query text has to be written into the source, so it is fixed at compile time, and outside data reaches the database only through the `?` placeholders and the parameter array. Build the query with `string_concat` instead and the compiler refuses it with `E207`. It's a type error, and there is no setting that turns it off. [examples/database.vera]({REPO}/blob/main/examples/database.vera).

When the model gets it wrong, every error comes back as an instruction:

```
{e001_example}
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

Results from [VeraBench v0.0.18]({REPO}-bench#results) against [Vera v0.1.8]({REPO}/releases/tag/v0.1.8). Inspired by [HumanEval](https://github.com/openai/human-eval), [MBPP](https://github.com/google-research/google-research/tree/master/mbpp), and [DafnyBench](https://github.com/sun-wendy/DafnyBench).

Full source and data: [{REPO}-bench]({REPO}-bench).

## Design Principles

1. **Checkability over correctness.** Code the compiler can mechanically check. Every diagnostic includes a concrete fix in natural language.
2. **Explicitness over convenience.** All state changes declared. All effects typed. All contracts mandatory. No implicit behaviour.
3. **One canonical form.** One preferred spelling per construct; formatting is deterministic and idempotent. `vera fmt` settles it.
4. **Structural references over names.** Bindings referenced by type and positional index (`@T.n`), not arbitrary names.
5. **Contracts as the source of truth.** Every function declares what it requires and guarantees, and the compiler proves it statically wherever it can.
6. **Constrained expressiveness.** Fewer valid programs means fewer opportunities for the model to be wrong.

## Key Features

- **No variable names.** Typed [De Bruijn indices]({RAW}/DE_BRUIJN.md) (`@T.n`) replace variable names: `@Int.0` is the most-recent `Int` binding, `@Int.1` the one before. A whole class of naming hallucinations disappears from the language instead of being caught after the fact.
- **Full contracts.** Mandatory preconditions, postconditions and effect declarations on every function, plus a `decreases` measure (or the `Diverge` effect) on every recursive one. `vera test` uses Z3 to generate inputs from the contracts and runs them through WASM, so there are no test cases to write by hand.
- **SQL injection won't compile.** The `<DB>` effect accepts only a query written as literals in the source, never one spliced together from a runtime value. Interpolating user input into SQL is a compile-time error (`E207`), so every value goes through a `?` placeholder. Injection safety stops being a discipline you have to remember and becomes a rule the compiler enforces.
- **Algebraic effects.** IO, Http, HttpServer, State, Exceptions, Async, Inference, DB, Random, Diverge. Every effect is declared and typed, and code is pure by default. `State` and `Exn` are handled in Vera code; the host effects are backed by the runtime.
- **Refinement types.** Types that state constraints, such as a list of positive integers of length `n`.
- **Proof, then runtime checks.** Contracts are proved at compile time with [Z3](https://www.microsoft.com/en-us/research/project/z3-3/), and most of what Z3 can't prove is checked at run time instead. A `requires` that can never hold is refused, so a contradiction can't prove everything. `vera verify --timeout-ms` sets the solver budget.
- **Traps that name their cause.** A `@Nat` underflow, a failed contract or `assert`, an index out of bounds or an escaped exception reports what kind of trap it is and how to fix it, the same way on wasmtime, in the browser and under WASI 0.2.
- **Language server.** A warm Z3 session between keystrokes, so proofs re-check at editor speed. Custom methods give agents [proof deltas]({RAW}/LSP_SERVER.md) before an edit lands.
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

**Upgrading from 0.1.x?** The checker and verifier are stricter in 0.2.0, so some programs that 0.1.13 accepted are now refused. The two you're most likely to meet are a recursive function with neither `decreases` nor `Diverge` (`E137`), and a `decreases` measure whose `@Nat` subtraction can underflow (`E502`). The [CHANGELOG]({REPO}/blob/main/CHANGELOG.md) lists every new check.

The wheel installs the compiler and the `vera` command. Install from source for the full environment (the bundled examples, the conformance suite and the specification the agent docs teach from) or to work on the compiler itself:

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

Live proof-aware diagnostics, hover, slot go-to-definition and typed-hole completion come from the [language server]({RAW}/LSP_SERVER.md). The source install above (`.[dev]`) includes it; from PyPI, add it with `python -m pip install "veralang[lsp]"`, or use `pip install -e ".[lsp]"` for a lighter source checkout. Any editor with a generic LSP client can point at `vera lsp` directly.

## For Agents

This page is also a machine-readable specification. Every document here has a markdown alternate on the same domain, discoverable through the standard `<link rel="alternate">`, `llms.txt`, and the Mintlify `llms-txt` and `llms-full-txt` conventions.

- [`SKILL.md`]({SITE}/SKILL.md): Complete language reference for writing Vera code: syntax, slots, contracts, effects, common mistakes and working examples.
- [`LSP_SERVER.md`]({RAW}/LSP_SERVER.md): The language server: live proof-aware diagnostics, and the custom proof-delta methods agents use to ask whether an edit still proves before committing it.
- [`AGENTS.md`]({RAW}/AGENTS.md): Setup instructions for any agent system (Copilot, Cursor, Windsurf, custom). Writing Vera code and working on the compiler.
- [`CLAUDE.md`]({RAW}/CLAUDE.md): Project orientation for Claude Code. Key commands, repo layout, workflows, invariants.
- [`TOOLCHAIN.md`]({RAW}/TOOLCHAIN.md): The CLI cookbook for writing, verifying, testing, running and debugging Vera, plus the `builtins`, `effects` and `errors` introspection commands.

Claude Code discovers `SKILL.md` and `CLAUDE.md` automatically when working inside the repo. For other projects, install the skill manually:

```bash
mkdir -p ~/.claude/skills/vera-language
cp /path/to/vera/SKILL.md ~/.claude/skills/vera-language/SKILL.md
```

For other models, point them at [`SKILL.md`]({SITE}/SKILL.md) through the system prompt, a file attachment or retrieval. It's self-contained and works with any model that reads markdown. Every Vera example in it, and on this page, is tested in CI.

The documents above are how machines *read* Vera. The [language server]({RAW}/LSP_SERVER.md) is how they *interrogate* it. `vera lsp` holds a warm, incremental Z3 session between edits, and four custom methods (`vera/speculativeEdit`, `vera/proposeEdit`, `vera/strengthenContract` and `vera/addEffect`) tell an agent whether an edit *keeps*, *breaks* or *strengthens* a program's proofs before it commits, then apply the edit only through the verification gate.

```jsonc
// vera/speculativeEdit: the proof delta for an in-memory edit
{{
  "ok": true,
  "proof_delta": {{
    "newly_discharged": ["..."],
    "newly_undischarged": [],
    "timed_out": [],
    "removed": [],
    "unchanged": 11,
    "proof_regressions": []
  }},
  "diagnostics": 0
}}
```

## Status

Vera is under [active development]({RAW}/ROADMAP.md). A complete compiler with 164 built-in functions, ten algebraic effects (IO, Http, HttpServer, State, Exceptions, Async, Inference, DB, Random, Diverge), contract-driven testing with [Z3](https://www.microsoft.com/en-us/research/project/z3-3/), a language server with agent-facing proof deltas, and a 14-chapter specification. A {n_conformance}-program conformance suite and {n_examples} worked examples are validated against the spec on every pull request. It's all developed in the open on [GitHub]({REPO}) under the MIT licence.

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
    file is consumed outside the repository context, and the doc gate's
    vera:skip and vera:run fence markers (#538, #1481) are stripped for the
    same reason.
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
