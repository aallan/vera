# Vera Language for Visual Studio Code

Language server integration and syntax highlighting for the [Vera programming language](https://veralang.dev/) — a statically typed, purely functional language with algebraic effects, mandatory contracts, and typed slot references (`@T.n`), designed for LLM-generated code.

## Features

**Language server integration** — the extension starts Vera's own
language server ([`vera lsp`](../../LSP_SERVER.md)) for `.vera` files,
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

Requires the `vera` binary with the `[lsp]` extra (see
[Requirements](#requirements)); without it the extension quietly stays
in syntax-highlighting-only mode. See [LSP_SERVER.md](../../LSP_SERVER.md)
for everything the server can do, including the custom methods for
coding agents.

**Syntax highlighting** for the full Vera language, including constructs that have no equivalent in other languages:

- **Slot references** — `@Int.0`, `@Array<String>.1`, `@Nat.result`, and bare `@Type` bindings in match arms are all highlighted distinctly, since they are the primary way Vera code refers to values.
- **Contract blocks** — `requires`, `ensures`, `effects`, `decreases`, and `invariant` are scoped separately from control flow keywords, so colour themes can distinguish verification annotations from program logic.
- **Effects** — built-in effects (`IO`, `State`, `Exn`, `Http`, `Async`, `Diverge`) and qualified operation calls (`IO.print`, `Exn.throw`) are highlighted with their components broken out.
- **String interpolation** — `\(...)` expressions inside strings get full Vera highlighting.
- **Nestable block comments** — `{- ... {- ... -} ... -}` handled correctly.

**Language configuration** so VS Code understands Vera's structure:

- Toggle line comments with `Cmd+/` (uses `--`)
- Toggle block comments with `Shift+Alt+A` (uses `{- ... -}`)
- Bracket matching and auto-closing for `{}`, `[]`, `()`, `<>`, `""`, and `{- -}`
- Code folding on brace blocks
- Auto-indentation on `{` / `}`
- Word selection that understands slot references as single tokens

## Requirements

For language-server features the extension needs a `vera` binary that
can serve LSP — from a clone of the repo:

```bash
pip install -e ".[lsp]"     # or ".[dev]", which includes it
```

The binary is resolved from `PATH` by default; point the
`vera.lsp.path` setting at an absolute path (e.g. a venv's
`.venv/bin/vera`) if yours lives elsewhere. Syntax highlighting works
with no binary at all.

## Settings

| Setting | Default | Meaning |
|---|---|---|
| `vera.lsp.enabled` | `true` | Start the language server for `.vera` files |
| `vera.lsp.path` | `"vera"` | Command used to launch it (absolute path or `PATH`-resolved) |

The **Vera: Restart Language Server** command restarts the server
(e.g. after switching venvs or upgrading `vera`).

## Installation

### From source (recommended for now)

**Fresh clone:**

```bash
git clone https://github.com/aallan/vera.git
cd vera/editors/vscode && npm install && cd -
ln -s "$(pwd)/vera/editors/vscode" ~/.vscode/extensions/vera-language
```

**Existing clone** (run from the repo root):

```bash
(cd editors/vscode && npm install)
ln -s "$(pwd)/editors/vscode" ~/.vscode/extensions/vera-language
```

Then reload VS Code. Any `.vera` file will be recognised automatically.
The `npm install` fetches the LSP client library
(`vscode-languageclient`); skipping it is fine — you just get syntax
highlighting without the language server.

### From VSIX

If a packaged `.vsix` is available:

```bash
code --install-extension vera-language-0.2.0.vsix
```

### VS Code Marketplace

Not yet published. This is planned once the language reaches a stable release.

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
| `->` | `keyword.operator.arrow.vera` |
| `|>` | `keyword.operator.pipe.vera` |

## Links

- [Vera language](https://veralang.dev/)
- [Vera on GitHub](https://github.com/aallan/vera)
- [TextMate bundle](https://github.com/aallan/vera/tree/main/editors/textmate) (same grammar, TextMate 2 packaging)

## Licence

MIT
