# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

## [0.0.3] - 2026-02-23

### Added
- **Parser tests**: 40 new tests covering annotation comments, anonymous functions, generics, refinement types, tuple destructuring, quantifiers, assert/assume, qualified calls, function types, float literals, nested patterns, handler variations, and implies operator (110 total, up from 70)
- **Example programs**: 8 new examples — closures, generics, refinement types, effect handlers, modules, quantifiers, pattern matching, mutual recursion (13 total, up from 5)
- **Design notes**: network access as an effect (`<Http>`), JSON as a stdlib ADT, async promises/futures as an effect (`<Async>`) documented in spec Chapter 0

### Fixed
- Grammar: annotation comments (`/* ... */`) now correctly ignored by the parser
- Grammar: `vera/__init__.py` version was `0.1.0`, corrected to match pyproject.toml
- Spec Chapter 3: removed deliberation marker about `@Fn0` approach, kept settled type alias approach
- Spec Chapter 6: rewrote counterexample reporting section (removed incorrect example, added actionable fix suggestions)
- Spec Chapter 7: cleaned up effect-contract interaction section (removed problematic `get()` in contract example, kept settled `old()`/`new()` syntax)

## [0.0.2] - 2026-02-23

### Added
- **CI**: GitHub Actions workflow running pytest on Python 3.11/3.12/3.13 with coverage on 3.12
- **Social preview**: meerkat sentinel mascot using Negroni brand colour palette
- **Custom domain**: veralang.dev with GitHub Pages and HTTPS

### Changed
- CONTRIBUTING.md: point "Questions?" section at Issues instead of Discussions
- Issue template config: remove Discussions contact link (Discussions disabled)
- README: add social preview banner image linking to veralang.dev
- pyproject.toml: update Homepage/Documentation URLs to veralang.dev

## [0.0.1] - 2026-02-23

### Added
- **Parser**: Lark LALR(1) parser that validates `.vera` source files
  - `vera check <file>` — parse and report errors
  - `vera parse <file>` — print the parse tree
- **LLM-oriented diagnostics**: error messages are natural language instructions explaining what went wrong, why, how to fix it with a code example, and a spec reference
- **SKILLS.md**: complete language reference for LLM agents, following the agent skills format
- **Example programs**: `absolute_value.vera`, `safe_divide.vera`, `increment.vera`, `factorial.vera`, `list_ops.vera`
- **Test suite**: 70 tests (54 parser, 16 error diagnostics)
- **Language specification** chapters 0-7 and 10 (draft)
  - Chapter 0: Introduction, philosophy, and diagnostics-as-instructions
  - Chapter 1: Lexical structure
  - Chapter 2: Type system with refinement types
  - Chapter 3: Slot reference system (`@T.n` typed De Bruijn indices)
  - Chapter 4: Expressions and statements
  - Chapter 5: Function declarations
  - Chapter 6: Contract system (preconditions, postconditions, verification tiers)
  - Chapter 7: Algebraic effect system
  - Chapter 10: Formal EBNF grammar (LALR(1) compatible)
- Project structure with `spec/`, `vera/`, `runtime/`, `tests/`, `examples/`
- Python project configuration (`pyproject.toml`)
- Repository documentation (README, LICENSE, CONTRIBUTING, CODE_OF_CONDUCT, CHANGELOG)
- GitHub issue and pull request templates

### Fixed
- Grammar: operator precedence chain (pipe/implies ordering)
- Grammar: `old()`/`new()` accept parameterised types (`State<Int>`)
- Grammar: function signatures use `@Type` prefix to declare binding sites
- Grammar: handler body simplified to avoid LALR reduce/reduce conflict
- `pyproject.toml`: corrected build backend, package discovery, PEP 639 compliance
