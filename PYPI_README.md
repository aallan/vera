# Vera

Vera is a programming language designed for large language models to write. It
has mandatory contracts, algebraic effects, typed slot references instead of
variable names, and a compiler that emits WebAssembly.

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

The distribution is named `veralang`, but the installed command remains
`vera`, and Python code still imports it as `import vera`. **Do not run `pip install vera`**: that name belongs to an unrelated
ERAV citizen-science project on PyPI.

## Install from GitHub source

The source route remains supported for compiler development, unreleased
changes, and testing the current `main` branch:

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

```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

```bash
vera check program.vera
vera verify program.vera
vera run program.vera
```

See the [CLI cookbook](https://github.com/aallan/vera/blob/main/TOOLCHAIN.md),
[language reference](https://veralang.dev/SKILL.md),
[supported-platform policy](https://github.com/aallan/vera#supported-platforms),
and [issue tracker](https://github.com/aallan/vera/issues) for more.
