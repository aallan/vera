#!/usr/bin/env python
"""Validate vera run commands documented in examples/README.md.

For each row in the example index tables:
  1. Extract the `vera run` command from the Run column.
  2. Verify the referenced .vera file exists.
  3. If --fn <name> is specified, verify <name> is a public function in
     that file (i.e. `public fn <name>` appears in the source).

This catches stale README entries when examples are renamed, functions
are removed, or the table falls out of sync with the source.
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
        file_path_str, fn_name = parse_run_command(cmd)
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

    if failures:
        print(f"FAILED: {len(failures)} invalid run command(s) in examples/README.md:\n",
              file=sys.stderr)
        for msg in failures:
            print(msg, file=sys.stderr)
        return 1

    print(f"All {len(commands)} vera run commands in examples/README.md are valid.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
