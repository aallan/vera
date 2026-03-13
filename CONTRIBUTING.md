# Contributing to Vera

Thank you for your interest in contributing to Vera. This document provides guidelines and information for contributors.

## How to Contribute

### Reporting Issues

If you find a bug, inconsistency in the specification, or have a feature suggestion:

1. Check the [existing issues](https://github.com/aallan/vera/issues) to see if it has already been reported.
2. If not, [open a new issue](https://github.com/aallan/vera/issues/new/choose) using the appropriate template.
3. Provide as much context as possible, including example Vera code where relevant.

### Specification Contributions

The language specification is in `spec/`. If you want to propose changes:

1. Open an issue first to discuss the change. Language design decisions should be discussed before implementation.
2. Reference the specific spec chapter and section.
3. Explain the rationale for the change, including how it affects the language's goals (checkability, explicitness, one canonical form).
4. Consider the impact on the reference compiler.

### Code Contributions

For contributions to the reference compiler:

1. Fork the repository.
2. Create a feature branch from `main`:
   ```bash
   git checkout -b feature/your-feature-name
   ```
3. Make your changes, following the coding standards below.
4. Add or update tests as appropriate.
5. Ensure all tests pass:
   ```bash
   pytest
   ```
6. Commit your changes with a clear commit message.
7. Push to your fork and open a pull request.

### Built-in functions and types

When adding or modifying built-in functions (registered in `vera/environment.py`):

- **Match the spec.** Type signatures should use the types specified in the language specification (e.g. `NAT` where the spec says `Nat`, not `INT`). Reference the relevant spec chapter and section in your PR description.
- **Add type checker tests** in `tests/test_checker.py` — at minimum, one test with correct types and one with a wrong argument type.
- **Add codegen/runtime tests** in `tests/test_codegen.py` — cover normal cases, edge cases (empty inputs, zero values), and composition with other built-ins.
- **Update the example** if an existing example demonstrates the feature, or add a new one in `examples/`.

## Development Setup

### Prerequisites

- Python 3.11 or later
- Git
- Node.js 22+ *(optional, for browser runtime parity tests)*

### Installation

```bash
git clone https://github.com/aallan/vera.git
cd vera
python -m venv .venv
source .venv/bin/activate
pip install -e ".[dev]"
pre-commit install
```

### Pre-commit Hooks

After running `pre-commit install`, every commit is automatically checked by 18 hooks including:

- Trailing whitespace and file endings
- YAML/TOML validity
- Merge conflict markers
- Python debug statements
- mypy type checking
- pytest test suite
- All 55 conformance programs pass their declared level
- All 25 `.vera` examples type-check and verify cleanly
- README, SKILL.md, HTML, and spec code blocks parse correctly
- Documentation counts match live codebase
- Browser parity (JS runtime matches Python runtime)

### Running Tests

```bash
pytest                    # run all tests
pytest tests/test_parser.py  # run specific test file
pytest -v                 # verbose output
pytest --cov=vera         # with coverage
```

See [TESTING.md](TESTING.md) for the full testing reference -- coverage data, test helpers, and guidelines for adding tests.

### Type Checking

```bash
mypy vera/
```

### Validation Scripts

```bash
python scripts/check_conformance.py      # verify all 55 conformance programs
python scripts/check_examples.py         # verify all 25 .vera examples
python scripts/check_spec_examples.py    # verify spec code blocks parse
python scripts/check_readme_examples.py  # verify README code blocks parse
python scripts/check_skill_examples.py   # verify SKILL.md code blocks parse
python scripts/check_html_examples.py   # verify HTML code blocks parse, check, verify
python scripts/check_version_sync.py     # verify version consistency
python scripts/check_doc_counts.py       # verify documentation counts match codebase
```

## Coding Standards

### Python Code (Reference Compiler)

- Follow [PEP 8](https://peps.python.org/pep-0008/).
- Use type hints on all function signatures.
- Use `dataclasses` for AST nodes and other structured data.
- Keep functions small and focused.
- Write docstrings for public functions and classes.
- Format code with `black`.

### Specification Documents

- Use Markdown.
- Use RFC 2119 keywords (MUST, SHOULD, MAY) precisely.
- Include code examples for every construct.
- Code examples must be valid Vera (they will be tested against the parser).
- Use the canonical formatting rules defined in Chapter 1 for all examples.

### Commit Messages

- Use the imperative mood ("Add feature" not "Added feature").
- Keep the first line under 72 characters.
- Reference related issues with `#issue-number`.

### Pull Requests

- Keep pull requests focused on a single change.
- Update relevant documentation and tests.
- Fill in the pull request template.
- Ensure CI passes before requesting review.

## Design Principles to Keep in Mind

When proposing changes, consider whether they align with Vera's design goals:

1. **Does this make code more checkable?** If it introduces ambiguity or makes verification harder, it's probably not right for Vera.
2. **Is there still one canonical form?** If a change introduces multiple ways to express the same thing, it violates a core principle.
3. **Does this help models or humans?** Vera is designed for LLMs. Changes that improve human ergonomics at the cost of machine writability should be carefully evaluated.
4. **Is it explicit?** Implicit behaviour is a non-goal. If something can be made explicit, it should be.

## Project Structure

```
vera/
├── spec/          # Language specification (Markdown)
├── vera/          # Reference compiler (Python)
├── tests/         # Test suite
├── examples/      # Example Vera programs
├── scripts/       # CI and validation scripts
```

## Branch Protection

The `main` branch has the following protections enabled:

- **Pull request required.** All changes to `main` must go through a pull request. No direct pushes.
- **CI must pass.** The test, typecheck, and lint jobs must all pass before merging.
- **Review required.** At least one approving review is needed.
- **No force pushes.** History on `main` is immutable.

If you are a maintainer setting up branch protection on a fork, configure these rules in **Settings > Branches > Branch protection rules** for the `main` branch.

## Code of Conduct

This project follows the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md). By participating, you are expected to uphold this code.

## License

By contributing to Vera, you agree that your contributions will be licensed under the [MIT License](LICENSE).

## Questions?

If you have questions about contributing, [open an issue](https://github.com/aallan/vera/issues).
