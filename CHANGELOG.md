# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

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
