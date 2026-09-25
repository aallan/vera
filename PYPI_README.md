# Vera

Vera is a programming language designed for large language models to write. It
has mandatory contracts, algebraic effects, typed slot references instead of
variable names, and a compiler that emits WebAssembly. Contracts are verified
statically with Z3 where possible; a contract the solver can't decide is checked
at run time, and the compiled program checks its contracts at run time as well.
Recursion must be shown to terminate (`decreases`) or declare that it may not
(`Diverge`), every runtime trap names its cause, and SQL injection is a
compile-time error.

Full documentation, examples, and the language specification are available at
[veralang.dev](https://veralang.dev) and in the
[GitHub repository](https://github.com/aallan/vera).

## Install a released version

Vera requires Python 3.11 or later. Create a virtual environment and install
the `veralang` distribution:

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install veralang
```

On Windows, activate the environment with `.venv\Scripts\activate` instead.
For editor and agent integration through the language server, install the LSP
extra:

```bash
python -m pip install "veralang[lsp]"
```

VS Code users can pair that server with
[Vera Language from the VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=veralang.vera-language);
the extension supplies syntax highlighting and starts `vera lsp`
automatically.

The distribution is named `veralang`, but the installed command remains
`vera`, and Python code still imports it as `import vera`. **Do not run `pip install vera`**: that name belongs to an unrelated
ERAV citizen-science project on PyPI. The wheel ships the compiler and the
`vera` command only — the bundled examples, the conformance suite, and the
specification live in the GitHub repository.

**Upgrading to 0.2.0:** the checker and verifier are stricter than in 0.1.x, so
a program 0.1.13 accepted may be refused — most often a recursive function with
neither `decreases` nor `Diverge` (`E137`), a `decreases` measure that is not
proved to decrease (`E502`), or a name, type or effect the checker cannot
resolve. The
[CHANGELOG](https://github.com/aallan/vera/blob/main/CHANGELOG.md) lists each
new check.

## Install from GitHub source

The source route provides the full environment — the examples, conformance
programs, and specification alongside the toolchain (the recommended setup for
agents learning the language) — and remains the route for compiler
development, unreleased changes, and testing the current `main` branch:

```bash
git clone https://github.com/aallan/vera.git
cd vera
python -m venv .venv
source .venv/bin/activate
python -m pip install -e .
```

Use `python -m pip install -e ".[lsp]"` for the language server or
`python -m pip install -e ".[dev]"` when working on the compiler.

## Try it

<!-- vera:run fn="main" stdout="5" -->
```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}

public fn main(-> @Int)
  requires(true)
  ensures(@Int.result == 5)
  effects(pure)
{
  safe_divide(2, 10)
}
```

```bash
vera check program.vera
vera verify program.vera    # proves main returns 5 from safe_divide's contract
vera run program.vera       # prints 5
vera verify --timeout-ms 60000 program.vera  # raise the per-query Z3 budget
```

See the [CLI cookbook](https://github.com/aallan/vera/blob/main/TOOLCHAIN.md),
[language reference](https://veralang.dev/SKILL.md),
[supported-platform policy](https://github.com/aallan/vera#supported-platforms),
and [issue tracker](https://github.com/aallan/vera/issues) for more.
