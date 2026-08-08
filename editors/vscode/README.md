# Vera Language for Visual Studio Code

Language server integration and syntax highlighting for the [Vera programming language](https://veralang.dev/) — a statically typed, purely functional language with algebraic effects, mandatory contracts, and typed slot references (`@T.n`), designed for LLM-generated code.

## Features

**Language server integration** — the extension starts Vera's own
language server ([`vera lsp`](https://github.com/aallan/vera/blob/main/LSP_SERVER.md)) for `.vera` files,
which runs the full pipeline — parse, type-check, **verify** — on every
edit and provides:

- **Proof-aware diagnostics** as you type, with the same stable error
  codes and spec references as `vera verify --json`, plus per-function
  verification-tier hints ("Tier 1 — all contracts proven by Z3").
- **Hover** showing the inferred type of the expression under the cursor.
- **Go-to-definition on slot references** — jump from `@T.n` to the
  parameter it names under De Bruijn resolution.
- **Typed-hole completion** — at a `?` hole, completion lists the
  in-scope bindings that fit, with their types.

Requires the `vera` binary with the `[lsp]` extra from PyPI (see
[Requirements](#requirements)); without it the extension stays in
syntax-highlighting-only mode. See [LSP_SERVER.md](https://github.com/aallan/vera/blob/main/LSP_SERVER.md)
for everything the server can do, including the custom methods for
coding agents.

**Syntax highlighting** for the full Vera language, including constructs that have no equivalent in other languages:

- **Slot references** — `@Int.0`, `@Array<String>.1`, `@Nat.result`, and bare `@Type` bindings in match arms are all highlighted distinctly, since they are the primary way Vera code refers to values.
- **Contract blocks** — `requires`, `ensures`, `effects`, `decreases`, and `invariant` are scoped separately from control flow keywords, so colour themes can distinguish verification annotations from program logic.
- **Effects** — built-in effects (`IO`, `State`, `Exn`, `Http`, `HttpServer`, `Async`, `Diverge`, `Inference`, `Random`, `DB`) and qualified operation calls (`IO.print`, `Exn.throw`) are highlighted with their components broken out.
- **String interpolation** — `\(...)` expressions inside strings get full Vera highlighting.
- **Nestable block comments** — `{- ... {- ... -} ... -}` handled correctly.
- **Typed holes** — the `?` placeholder expression is scoped as a language constant, so it stands out as the thing left to fill in.

**Language configuration** so VS Code understands Vera's structure:

- Toggle line comments with `Cmd+/` (uses `--`)
- Toggle block comments with `Shift+Alt+A` (uses `{- ... -}`)
- Bracket matching and auto-closing for `{}`, `[]`, `()`, `<>`, `""`, and `{- -}`
- Code folding on brace blocks
- Auto-indentation on `{` / `}`
- Word selection that understands slot references as single tokens

## Requirements

For language-server features the extension needs Python 3.11+ and a
`vera` binary with the optional LSP dependencies:

```bash
python -m pip install "veralang[lsp]"
```

The base `veralang` installation does not include the optional language
server dependencies, so keep the `[lsp]` extra in the command. The
extension finds the binary in this order: the `vera.lsp.path` setting
(if changed from its default), a workspace-local virtual environment
(`.venv/bin/vera` or `.venv\\Scripts\\vera.exe`), then `vera` from
`PATH`. If a GUI-launched VS Code cannot see the Python installation,
set `vera.lsp.path` to the absolute path of the `vera` executable.
Syntax highlighting works without the binary.

## Settings

| Setting | Default | Meaning |
|---|---|---|
| `vera.lsp.enabled` | `true` | Start the language server for `.vera` files |
| `vera.lsp.path` | `"vera"` | Command used to launch it (absolute path or `PATH`-resolved) |

The **Vera: Restart Language Server** command restarts the server
(e.g. after switching venvs or upgrading `vera`).

## Installation

### VS Code Marketplace

Install **Vera Language** from the
[VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=veralang.vera-language),
from the Extensions view in VS Code, or from the command line:

```bash
code --install-extension veralang.vera-language
```

Syntax highlighting works immediately. For diagnostics, hover,
go-to-definition, and typed-hole completion, install the language server as
described in [Requirements](#requirements).

### From source

**Fresh clone:**

```bash
git clone https://github.com/aallan/vera.git
cd vera/editors/vscode && npm install && npm run build && cd -
ln -s "$(pwd)/vera/editors/vscode" ~/.vscode/extensions/vera-language
```

**Existing clone** (run from the repo root):

```bash
(cd editors/vscode && npm install && npm run build)
ln -s "$(pwd)/editors/vscode" ~/.vscode/extensions/vera-language
```

Then reload VS Code. Any `.vera` file will be recognised automatically.
The build bundles the LSP client library into `dist/extension.js`.
Skipping it leaves the declarative syntax highlighting available, but
the language server integration cannot start.

## Scope reference

The grammar uses standard TextMate scope conventions, so it works with any colour theme. Key assignments:

| Vera construct | Scope |
|---|---|
| `@Int.0`, `@Array<String>.result` | `variable.other.slot.vera` |
| `@Int` (in match binding) | `variable.other.slot-binding.vera` |
| `requires`, `ensures`, `effects` | `keyword.contract.vera` |
| `if`, `match`, `let`, `handle` | `keyword.control.vera` |
| `fn`, `data`, `effect`, `import` | `keyword.declaration.vera` |
| `public`, `private` | `storage.modifier.vera` |
| `IO`, `State`, `Exn` | `entity.name.type.effect.vera` |
| `IO.print`, `Exn.throw` | effect + `entity.name.function.effect-op.vera` |
| `Some`, `None`, `Ok`, `Err` | `entity.name.tag.constructor.vera` |
| `Int`, `Bool`, `String` | `storage.type.primitive.vera` |
| `Array`, `Option`, `Result` | `storage.type.composite.vera` |
| `true`, `false`, `pure` | `constant.language.vera` |
| `?` (typed hole) | `constant.language.hole.vera` |
| `->` | `keyword.operator.arrow.vera` |
| `|>` | `keyword.operator.pipe.vera` |

## Links

- [Vera language](https://veralang.dev/)
- [Vera on GitHub](https://github.com/aallan/vera)
- [TextMate bundle](https://github.com/aallan/vera/tree/main/editors/textmate) (same grammar, TextMate 2 packaging)

## Licence

MIT
