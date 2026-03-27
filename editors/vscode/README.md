# Vera Language for Visual Studio Code

Syntax highlighting and language support for the [Vera programming language](https://veralang.dev/) — a statically typed, purely functional language with algebraic effects, mandatory contracts, and typed slot references (`@T.n`), designed for LLM-generated code.

## Features

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

## Installation

### From source (recommended for now)

Clone the Vera repository (or navigate to an existing clone), then symlink the extension directory into VS Code's extensions folder:

```bash
git clone https://github.com/aallan/vera.git
ln -s "$(pwd)/vera/editors/vscode" ~/.vscode/extensions/vera-language
```

Then reload VS Code. Any `.vera` file will be recognised automatically.

### From VSIX

If a packaged `.vsix` is available:

```bash
code --install-extension vera-language-0.1.0.vsix
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
| `\|>` | `keyword.operator.pipe.vera` |

## Links

- [Vera language](https://veralang.dev/)
- [Vera on GitHub](https://github.com/aallan/vera)
- [TextMate bundle](https://github.com/aallan/vera/tree/main/editors/textmate) (same grammar, TextMate 2 packaging)

## Licence

MIT
