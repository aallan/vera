# Vera.tmbundle

TextMate 2 syntax highlighting for the [Vera programming language](https://veralang.dev/) — a statically typed, purely functional language with algebraic effects, mandatory contracts, and typed slot references (`@T.n`), designed for LLM-generated code.

## Installation

### From the Vera repository

Clone the Vera repository (or navigate to an existing clone), then copy the bundle into TextMate's bundle directory:

```bash
cp -r editors/textmate/Vera.tmbundle ~/Library/Application\ Support/TextMate/Bundles/
```

Alternatively, open Finder, navigate to `editors/textmate/`, and double-click `Vera.tmbundle`. TextMate will install it automatically.

Then restart TextMate or select **Bundles → Bundle Editor → Reload Bundles**.

## What gets highlighted

The grammar covers the full Vera language as of v0.0.100.

**Slot references** are the most distinctive feature of Vera syntax, and the bundle treats them as first-class citizens. Full references like `@Int.0`, `@Array<String>.1`, and `@Nat.result` are scoped as `variable.other.slot`, while bare bindings in match arms (e.g. `Some(@Int)`) are scoped as `variable.other.slot-binding`. Both are visually distinct from all other tokens.

**Contract blocks** — `requires`, `ensures`, `effects`, `decreases`, and `invariant` — are scoped separately from control flow keywords (`keyword.contract` vs `keyword.control`), so they can be themed independently.

**Effects** — built-in effects (`IO`, `State`, `Exn`, `Http`, `Async`, `Diverge`) are recognised as `entity.name.type.effect`. Qualified operation calls like `IO.print` and `Exn.throw` are decomposed into effect name, accessor, and operation name.

**Other language features:**

- `public`/`private` visibility modifiers
- `fn`, `data`, `effect`, `ability`, `type`, `module`, `import` declarations
- `forall` with generic type parameters and ability constraints
- ADT constructors (built-in and user-defined)
- Pattern matching with `match`, including wildcard `_`
- `if`/`then`/`else`, `let`, `where`, `handle`/`resume`/`with`/`in`
- `old()`/`new()` in state contract postconditions
- `forall()`/`exists()` quantifiers in contracts
- Module-qualified calls with `::` syntax
- String literals with `\(...)` interpolation (interpolated expressions get full highlighting)
- `--` line comments and nestable `{- ... -}` block comments
- All operators: `|>`, `==>`, `||`, `&&`, `==`, `!=`, `<=`, `>=`, `<`, `>`, `+`, `-`, `*`, `/`, `%`, `!`, `[]`
- Float and integer numeric literals
- `true`, `false`, `pure`, and `()` unit literal

## Scope naming

The grammar uses standard TextMate scope conventions so it works with any colour scheme out of the box. Key scope assignments:

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

## Compatibility

Built for [TextMate 2](https://macromates.com/). The `.tmLanguage` plist format is also compatible with editors and tools that consume TextMate grammars, including Sublime Text and any LSP or tree-sitter bridge that accepts TextMate scopes as a fallback.

## Links

- [Vera language](https://veralang.dev/)
- [Vera on GitHub](https://github.com/aallan/vera)
- [TextMate 2](https://macromates.com/)

## Licence

MIT
