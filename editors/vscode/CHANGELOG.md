# Changelog

## Unreleased

Grammar fix and a language-client bump.

- Grammar: the effect rule now carries all ten built-in effects —
  `HttpServer`, `Inference`, `Random` and `DB` were missing, so
  `DB.query(...)` highlighted as an ordinary type reference rather than
  as an effect. The README's copy of the same list was stale in the same
  way and is corrected with it. A gate in the main repository
  (`scripts/check_editor_grammars.py`) now holds both against
  `vera effects --json`, so the next effect cannot land without them.
- `vscode-languageclient` 10.1.0 → 10.1.1 (LSP protocol 3.18.3).

## 0.2.1

Security fix.

- `brace-expansion` 5.0.7 → 5.0.8, closing
  [GHSA-mh99-v99m-4gvg](https://github.com/advisories/GHSA-mh99-v99m-4gvg)
  — a high-severity denial of service where an unbounded expansion
  length crashes the process out of memory. It is a runtime dependency,
  not build tooling: `vscode-languageclient` → `minimatch` →
  `brace-expansion`, and the esbuild bundle externalises only `vscode`,
  so it ships inside `dist/extension.js`. 0.2.0 carries the vulnerable
  version; upgrade to 0.2.1.

## 0.2.0

Language server integration.

- First release on the VS Code Marketplace
- Bundles the extension runtime instead of shipping raw `node_modules`
- The extension now starts Vera's language server (`vera lsp`) for
  `.vera` files: proof-aware diagnostics with verification-tier hints,
  expression-type hover, De Bruijn slot go-to-definition, and
  typed-hole completion
- New settings: `vera.lsp.enabled`, `vera.lsp.path` — binary resolution prefers a workspace-local venv (`.venv/bin/vera`) over `PATH`, so a from-source clone needs no configuration; spawn failure shows one actionable warning
- New command: **Vera: Restart Language Server**
- Degrades gracefully to syntax-highlighting-only when the `vera`
  binary (or the extension's `npm install`) is absent
- Requires VS Code 1.91+ (was 1.75+) — the floor of `vscode-languageclient` 10
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
