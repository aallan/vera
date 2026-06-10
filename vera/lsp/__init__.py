"""Vera Language Server (#222) — transport layer.

``vera lsp`` serves LSP 3.17 over stdio.  Phase C: handshake +
document sync + the coordinate-conversion layer (``convert``).
Language features arrive in Phase D on top of the obligation core
(``vera.obligations``); the heavy imports (pygls) live in ``server``
and are deliberately NOT imported here, so ``import vera.lsp.convert``
works on a base install without the [lsp] extra.
"""
