# Changelog

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
