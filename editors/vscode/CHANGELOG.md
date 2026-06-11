# Changelog

## 0.2.0

Language server integration.

- The extension now starts Vera's language server (`vera lsp`) for
  `.vera` files: proof-aware diagnostics with verification-tier hints,
  expression-type hover, De Bruijn slot go-to-definition, and
  typed-hole completion
- New settings: `vera.lsp.enabled`, `vera.lsp.path`
- New command: **Vera: Restart Language Server**
- Degrades gracefully to syntax-highlighting-only when the `vera`
  binary (or the extension's `npm install`) is absent
- Requires VS Code 1.82+ (was 1.75+)
- Grammar: typed holes (`?`) are now scoped (`constant.language.hole.vera`) — the one syntax addition since the grammar was written (v0.0.100)

## 0.1.0

Initial release.

- Syntax highlighting for the full Vera language
- Slot references (`@T.n`, `@T.result`, bare `@T` in match bindings)
- Contract blocks (`requires`, `ensures`, `effects`, `decreases`, `invariant`)
- Built-in effects (`IO`, `State`, `Exn`, `Http`, `Async`, `Diverge`)
- Qualified effect operations (`IO.print`, `Exn.throw`)
- Module-qualified calls (`vera.math::abs`)
- String interpolation with `\(...)`
- Nestable block comments `{- ... -}`
- Language configuration: bracket matching, auto-closing, comment toggling, folding, indentation
