#!/usr/bin/env python
"""Validate examples/README.md's example-index tables against the examples.

For each row in the example index tables:
  1. Extract the `vera run` command from the Run column.
  2. Verify the referenced .vera file exists.
  3. If --fn <name> is specified, verify <name> is a public function in
     that file (i.e. `public fn <name>` appears in the source).
  4. Extract every backtick-quoted BARE IDENTIFIER from the Demonstrates
     column (`array_slice`, `decreases`, `PosInt`, ...) and verify it
     appears in the referenced file's source.

This catches stale README entries when examples are renamed, functions
are removed, or the table falls out of sync with the source — including
the Demonstrates column crediting an example with a builtin it never
calls (#1351).  Only backtick-quoted SINGLE IDENTIFIERS are checked in
the Demonstrates column: a backtick span containing anything else (a
call expression like `` `async(Http.get)` ``, a declaration snippet like
`` `type Board = Map<String, Int>` ``, a module path like `` `wasi:http` ``)
is a code illustration rather than a name claim, and the column's plain
prose stays unchecked entirely — the same scope the issue's own "Suggested
fix" draws.
"""

import re
import sys
from pathlib import Path


def extract_run_commands(readme: Path) -> list[tuple[int, str]]:
    """Return (line_number, command) for every vera run command in tables."""
    commands: list[tuple[int, str]] = []
    for lineno, line in enumerate(readme.read_text(encoding="utf-8").splitlines(), 1):
        # Table rows: | ... | `vera run ...` | ... |
        if not line.startswith("|") or "vera run" not in line:
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        for cell in cells:
            # Unwrap backtick-quoted cell content
            inner = re.fullmatch(r"`([^`]+)`", cell)
            content = inner.group(1) if inner else cell
            if content.startswith("vera run "):
                commands.append((lineno, content))
    return commands


def parse_run_command(cmd: str) -> tuple[str, str | None]:
    """Parse `vera run <path> [--fn <name>] [-- args...]`.

    Returns (file_path, fn_name_or_None).
    """
    # Strip leading 'vera run '
    rest = cmd[len("vera run "):].strip()
    # Split off '--' args
    rest = rest.split(" -- ")[0].strip()
    # Extract --fn <name> if present
    fn_match = re.search(r"--fn\s+(\S+)", rest)
    fn_name = fn_match.group(1) if fn_match else None
    # File path is first token
    tokens = rest.split()
    if not tokens:
        raise ValueError(f"no file path in command: {cmd!r}")
    file_path = tokens[0]
    return file_path, fn_name


def is_public_function(vera_file: Path, fn_name: str) -> bool:
    """Return True if `public fn <fn_name>` appears in the source."""
    source = vera_file.read_text(encoding="utf-8")
    return bool(re.search(rf"\bpublic\s+fn\s+{re.escape(fn_name)}\b", source))


_EXAMPLE_FILENAME = re.compile(r"`([\w.-]+\.vera)`")
_BACKTICK_IDENTIFIER = re.compile(r"`([A-Za-z_][A-Za-z0-9_]*)`")


def extract_example_rows(readme: Path) -> list[tuple[int, str, str]]:
    """Return (line_number, vera_filename, demonstrates_cell) for every
    example-index table data row.

    A data row is identified by a backtick-quoted `*.vera` filename in
    its first cell — this sidesteps depending on the header row's exact
    wording or the separator row's dashes, and skips any 3-cell row
    that isn't naming an example (there are none today, but a table
    row identified structurally rather than by position survives the
    table growing a column).
    """
    rows: list[tuple[int, str, str]] = []
    for lineno, line in enumerate(readme.read_text(encoding="utf-8").splitlines(), 1):
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) != 3:
            continue
        name_match = _EXAMPLE_FILENAME.fullmatch(cells[0])
        if not name_match:
            continue
        rows.append((lineno, name_match.group(1), cells[2]))
    return rows


def extract_backticked_names(demonstrates_cell: str) -> list[str]:
    """Bare-identifier backtick spans in a Demonstrates cell.

    A span is a "name claim" only if its ENTIRE backtick-quoted content
    is a single identifier (letters/digits/underscore, not starting
    with a digit) — `array_slice`, `decreases`, `PosInt`.  A span with
    anything else inside (a dot, parens, angle brackets, spaces, a
    colon) is a syntax illustration rather than a name the row claims
    the example demonstrates, and is left unchecked, matching how most
    of the column's prose is never backtick-quoted at all.
    """
    return _BACKTICK_IDENTIFIER.findall(demonstrates_cell)


# Mirrors vera/grammar.lark's own token precedence: `STRING_LIT` is a
# distinct token from the `--`-to-end-of-line comment `%ignore` rule, so a
# `--` INSIDE a string is part of the string, never a comment start —
# `examples/regex.vera` relies on exactly this (`IO.print("-- Matching --")`).
# Matching a full string literal first and passing it through unchanged
# (rather than also stripping ITS contents) preserves that precedence;
# only a `--...` span found OUTSIDE of one is a comment and gets removed.
_STRING_OR_COMMENT = re.compile(r'"(?:[^"\\]|\\.)*"|--[^\n]*')


def _strip_comments(source: str) -> str:
    """Remove Vera line comments so a name mentioned only in PROSE — a
    comment, never executed — cannot satisfy a Demonstrates-column claim
    about the CODE (a real gap: `-- mentions phantom_builtin in prose
    only` plus a matching Demonstrates entry passed before this)."""
    def replace(match: re.Match[str]) -> str:
        text = match.group(0)
        return text if text.startswith('"') else ""
    return _STRING_OR_COMMENT.sub(replace, source)


def name_appears_in_source(vera_file: Path, name: str) -> bool:
    """Return True if `name` appears as a whole word in the source,
    outside of comments."""
    source = _strip_comments(vera_file.read_text(encoding="utf-8"))
    return bool(re.search(rf"\b{re.escape(name)}\b", source))


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    readme = root / "examples" / "README.md"

    if not readme.is_file():
        print("ERROR: examples/README.md not found.", file=sys.stderr)
        return 1

    commands = extract_run_commands(readme)
    if not commands:
        print("ERROR: no vera run commands found in examples/README.md.",
              file=sys.stderr)
        return 1

    failures: list[str] = []

    for lineno, cmd in commands:
        try:
            file_path_str, fn_name = parse_run_command(cmd)
        except ValueError as exc:
            failures.append(f"  line {lineno}: {exc}\n    Command: {cmd}")
            continue
        vera_file = root / file_path_str

        if not vera_file.is_file():
            failures.append(
                f"  line {lineno}: file not found: {file_path_str}\n"
                f"    Command: {cmd}"
            )
            continue

        if fn_name and not is_public_function(vera_file, fn_name):
            failures.append(
                f"  line {lineno}: no public fn '{fn_name}' in {file_path_str}\n"
                f"    Command: {cmd}"
            )

    example_rows = extract_example_rows(readme)
    names_checked = 0
    for lineno, vera_filename, demonstrates in example_rows:
        vera_file = root / "examples" / vera_filename
        if not vera_file.is_file():
            # The Run-column loop above parses its OWN file path out of
            # the `vera run` command, independently of this row's first
            # cell — a row whose Run command happens to name a
            # different (valid) path, or carries no `vera run` command
            # matching that loop's pattern at all, would otherwise let
            # this row's missing file go completely unreported.
            failures.append(
                f"  line {lineno}: example file not found: "
                f"examples/{vera_filename}"
            )
            continue
        for name in extract_backticked_names(demonstrates):
            names_checked += 1
            if not name_appears_in_source(vera_file, name):
                failures.append(
                    f"  line {lineno}: Demonstrates column names `{name}`,"
                    f" which does not appear in examples/{vera_filename}\n"
                    f"    Demonstrates: {demonstrates.strip()}"
                )

    if failures:
        print(f"FAILED: {len(failures)} invalid entr{'y' if len(failures) == 1 else 'ies'} in examples/README.md:\n",
              file=sys.stderr)
        for msg in failures:
            print(msg, file=sys.stderr)
        return 1

    print(
        f"All {len(commands)} vera run commands and {names_checked} "
        "Demonstrates-column names in examples/README.md are valid."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
