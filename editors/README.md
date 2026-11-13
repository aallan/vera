# Editor Support

Editor packages for Vera: a VS Code extension with the language server, and syntax highlighting for TextMate, Sublime Text and Vim.

## VS Code

A full VS Code language extension for `.vera` files: starts the [Vera language server](../LSP_SERVER.md) (proof-aware diagnostics, hover, slot go-to-definition, typed-hole completion) and provides syntax highlighting and language configuration.

See [`vscode/`](vscode/) for installation instructions.

## TextMate 2

A `.tmbundle` providing syntax highlighting for `.vera` files in TextMate 2.

See [`textmate/`](textmate/) for installation instructions.

The `.tmLanguage` grammar is also compatible with Sublime Text and other editors that consume TextMate grammars.

## Vim

A Vim package (`ftdetect`/`ftplugin`/`syntax`) ported from the VS Code TextMate grammar, for Vim 8+ and Neovim.

See [`vim-veralang/`](vim-veralang/) for installation instructions.
