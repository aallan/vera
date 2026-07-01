#!/usr/bin/env python3
"""Explicit-encoding enforcement for text-mode file I/O (#645).

Python's text-mode ``open()`` / ``Path.read_text()`` / ``Path.write_text()``
fall back to ``locale.getpreferredencoding()`` when no ``encoding=`` is given.
On Windows that is typically cp1252, which cannot represent most of Unicode — so
a Vera source / doc / fixture containing ``→``, ``—``, or any non-ASCII byte
fails to read or write on a locale-default Windows shell.  #641 papered over CI
with ``PYTHONUTF8=1``; the durable fix (#645) is an explicit
``encoding="utf-8"`` at every text-mode call site, enforced here so the
convention cannot rot (and so the CI backstop can be removed).

Scope (per #645): builtin ``open(...)``, ``X.read_text(...)`` and
``X.write_text(...)`` under ``vera/``, ``scripts/``, ``tests/``.  The
``encoding=`` must be a UTF-8 *string literal* (``"utf-8"`` / ``"UTF-8"`` /
``"utf8"``); a non-literal (``encoding=enc``) or a different codec
(``encoding="latin-1"``) is rejected — the repo rule is UTF-8, and a deliberate
non-UTF-8 site uses ``# encoding-exempt: <reason>``.

Deliberately NOT flagged:

- Binary-mode ``open(..., "rb" | "wb" | ...)`` — encoding is irrelevant.
- ``read_bytes`` / ``write_bytes`` — binary by definition.
- ``.open(...)`` method calls — out of scope for #645, and blanket-checking
  them would false-positive unrelated ``.open()`` methods (e.g. the LSP document
  store's ``store.open(uri, text, version)``); the handful of real
  ``Path.open()`` text sites already pass ``encoding=``.
- A site carrying ``# encoding-exempt: <reason>`` (reason mandatory) — for a
  deliberate non-UTF-8 / binary-ish edge case.  A marker with no reason is
  itself a violation (mirrors the ``# diag-fields-exempt`` convention in
  ``scripts/check_diagnostic_fields.py``).

Usage:
    python scripts/check_explicit_encoding.py            # walk the scope dirs
    python scripts/check_explicit_encoding.py FILE ...   # check given files

Wired into pre-commit and the CI lint job so a new bare text-mode call is
rejected at the door.
"""

from __future__ import annotations

import ast
import io
import sys
import tokenize
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parent.parent
SCOPE_DIRS = ("vera", "scripts", "tests")
OPT_OUT = "# encoding-exempt"
# Path methods that decode/encode text and default to a locale codec.
TEXT_METHODS = ("read_text", "write_text")


@dataclass
class Violation:
    file: str
    line: int
    call: str          # "open" | "read_text" | "write_text"
    reason: str
    snippet: str | None


def _optout_lines(source: str) -> dict[int, str]:
    """Map line number -> opt-out reason, but ONLY where ``# encoding-exempt``
    appears in a real ``COMMENT`` token — never inside a string literal (a raw
    line scan would let a call whose *string argument* contains the marker text
    silently exempt itself).  Reason ``""`` means the marker carried none, which
    is itself a violation."""
    out: dict[int, str] = {}
    try:
        for tok in tokenize.generate_tokens(io.StringIO(source).readline):
            if tok.type != tokenize.COMMENT:
                continue
            text = tok.string.strip()
            if text == OPT_OUT:
                out[tok.start[0]] = ""
            elif text.startswith(OPT_OUT) and (
                    text[len(OPT_OUT)] == ":" or text[len(OPT_OUT)].isspace()):
                out[tok.start[0]] = text[len(OPT_OUT):].lstrip(" :").strip()
    except (tokenize.TokenError, IndentationError):
        pass
    return out


def _encoding_kw(call: ast.Call) -> ast.keyword | None:
    for kw in call.keywords:
        if kw.arg == "encoding":
            return kw
    return None


def _is_utf8_literal(node: ast.expr) -> bool:
    """True iff ``node`` is a string literal naming UTF-8.

    Accepts the common spellings (``"utf-8"``, ``"UTF-8"``, ``"utf8"``,
    ``"utf_8"``) case-insensitively.  A non-literal (``encoding=enc``) or a
    different codec (``encoding="latin-1"``) is NOT accepted — the repo-wide rule
    is UTF-8, and a deliberate exception uses ``# encoding-exempt: <reason>``."""
    return (isinstance(node, ast.Constant) and isinstance(node.value, str)
            and node.value.lower().replace("-", "").replace("_", "") == "utf8")


def _open_mode_is_binary(call: ast.Call) -> bool | None:
    """For an ``open(...)`` call return True if binary-mode, False if text-mode,
    None if the mode is a non-literal expression we cannot resolve statically.

    The mode is the 2nd positional argument or the ``mode=`` keyword; absent, it
    defaults to ``"r"`` (text)."""
    mode_node: ast.expr | None = None
    if len(call.args) >= 2:
        mode_node = call.args[1]
    else:
        for kw in call.keywords:
            if kw.arg == "mode":
                mode_node = kw.value
                break
    if mode_node is None:
        return False  # default "r" -> text
    if isinstance(mode_node, ast.Constant) and isinstance(mode_node.value, str):
        return "b" in mode_node.value
    return None  # non-literal mode -> can't tell


def check_source(source: str, filename: str) -> list[Violation]:
    """Return every bare text-mode open/read_text/write_text in one source."""
    tree = ast.parse(source, filename=filename)
    src_lines = source.splitlines()
    optout = _optout_lines(source)
    violations: list[Violation] = []

    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        f = node.func

        non_literal_mode = False
        if isinstance(f, ast.Name) and f.id == "open":
            binary = _open_mode_is_binary(node)
            if binary is True:
                continue  # binary open -> encoding is irrelevant
            non_literal_mode = binary is None
            call_name = "open"
        elif isinstance(f, ast.Attribute) and f.attr in TEXT_METHODS:
            call_name = f.attr
        else:
            continue

        enc_kw = _encoding_kw(node)
        if enc_kw is not None and _is_utf8_literal(enc_kw.value):
            continue  # explicit UTF-8 — good

        snippet = (src_lines[node.lineno - 1]
                   if 0 <= node.lineno - 1 < len(src_lines) else None)

        # A `# encoding-exempt[: reason]` COMMENT on any of the call's source
        # lines suppresses it; a missing reason is itself a violation.
        reason = next(
            (optout[ln] for ln in range(node.lineno,
                                        (node.end_lineno or node.lineno) + 1)
             if ln in optout),
            None)
        if reason is not None:
            if reason == "":
                violations.append(Violation(
                    filename, node.lineno, call_name,
                    "`# encoding-exempt` marker without a reason", snippet))
            continue

        if enc_kw is not None:
            why = (f'{call_name}(...) passes a non-UTF-8 or non-literal '
                   'encoding=; the repo rule is encoding="utf-8" (use it, or '
                   '`# encoding-exempt: <reason>` for a deliberate codec)')
        elif non_literal_mode:
            why = ('open(...) has a non-literal mode and no encoding=; pass '
                   'encoding="utf-8" for text mode, or open in binary')
        else:
            why = (f'text-mode {call_name}(...) without explicit '
                   f'encoding="utf-8"')
        violations.append(Violation(filename, node.lineno, call_name, why,
                                    snippet))
    return violations


def iter_scope_files() -> list[Path]:
    out: list[Path] = []
    for d in SCOPE_DIRS:
        out.extend(sorted((ROOT / d).rglob("*.py")))
    return out


def check_paths(paths: Iterable[Path]) -> list[Violation]:
    out: list[Violation] = []
    for p in paths:
        rel = p.relative_to(ROOT).as_posix() if p.is_absolute() else p.as_posix()
        out.extend(check_source(p.read_text(encoding="utf-8"), rel))
    return out


def _in_scope(p: Path) -> bool:
    try:
        rel = p.resolve().relative_to(ROOT)
    except ValueError:
        return False
    return bool(rel.parts) and rel.parts[0] in SCOPE_DIRS and rel.suffix == ".py"


def main(argv: list[str]) -> int:
    paths = ([p for a in argv if _in_scope(p := Path(a))]
             if argv else iter_scope_files())
    violations = check_paths(paths)
    if not violations:
        print("check_explicit_encoding: OK — every text-mode open() / "
              "read_text() / write_text() passes an explicit encoding.")
        return 0
    by_file: dict[str, list[Violation]] = {}
    for v in violations:
        by_file.setdefault(v.file, []).append(v)
    print(f"check_explicit_encoding: {len(violations)} bare text-mode file "
          f"call(s) in {len(by_file)} file(s) (#645).\n", file=sys.stderr)
    print('Text-mode file I/O must pass encoding="utf-8" explicitly — the '
          "locale\ndefault is cp1252 on Windows and mangles non-ASCII "
          "(→ / — / any Unicode).\nAdd encoding=\"utf-8\", or mark a deliberate "
          "exception with\n`# encoding-exempt: <reason>`.\n", file=sys.stderr)
    for fname in sorted(by_file):
        print(f"  {fname}", file=sys.stderr)
        for v in sorted(by_file[fname], key=lambda x: x.line):
            print(f"    line {v.line:<5} {v.reason}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
