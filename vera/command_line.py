"""What each `vera` command takes, and the command line read against it (#1872).

`COMMANDS` is the one description of the command line: each command's
summary, whether it reads a source file, the options it takes (with each
valued option's domain), the pairs of its options that contradict each
other, and whether it passes the arguments after ``--`` to the program it
runs.  `parse` reads a command line against it, the usage text (`usage`)
and each command's ``--help`` (`command_help`) are rendered from it, and
every refusal names what it lists, so an option is taken by exactly the
commands that list it.

The rules `parse` applies, in the order it applies them:

1. Only the tokens before the first ``--`` are the command line's own;
   the rest are the program's arguments, whatever they look like, and only
   a command that runs a program (`vera run`) takes any.
2. ``--help`` or ``-h`` among them prints the command's usage, whatever
   else the command line holds.
3. A token that starts with ``-`` (other than ``-`` alone, which names
   stdin) is an option.  One the command does not list is E901 (written
   with ``=``, or naming a file whose name begins with a dash, its fix
   says how to write it).  A valued option's value is the next token
   unless that is an option itself (a negative number is a value): with
   none, or a value outside the option's domain or the command's set, it
   is E903.  An option given twice is E902, whatever the two values are,
   and so are two options the command lists as exclusive.
4. Every other token is an operand.  A command that reads a file takes
   exactly one, and a command that reads none takes none: anything else is
   E904.  An empty operand, or one that names a directory, is E900.

A refusal is printed as the ``--json`` envelope when ``--json`` stands
among the command line's own tokens, and as the diagnostic on stderr
otherwise (`Refusal`).
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass, field

from vera import command_errors
from vera.errors import Diagnostic


@dataclass(frozen=True)
class Option:
    """One option: its name, the line its help gives it, its value's
    placeholder (``None`` for a flag that takes none), and its value's
    domain: ``"positive"`` (an integer of at least 1), ``"port"`` (an
    integer from 0 to 65535), ``"name"`` (a function's name), or ``None``
    (any token that is not empty).  A command's fixed set of values for
    an option is the command's (`Command.values`)."""

    name: str
    help: str
    metavar: str | None = None
    domain: str | None = None


@dataclass(frozen=True)
class Command:
    """One command: what it does, whether it reads a source file, the
    options it takes (with, for a valued option, the values it takes when
    they are a fixed set), the options it refuses together (``(a, b,
    value)``: *a* with *b*, or with *b* at *value*), and whether it passes
    the arguments after ``--`` to the program it runs."""

    name: str
    summary: str
    reads_file: bool
    options: tuple[Option, ...] = ()
    values: dict[str, tuple[str, ...]] = field(default_factory=dict)
    program_args: bool = False
    exclusive: tuple[tuple[str, str, str | None], ...] = ()

    def option(self, name: str) -> Option | None:
        return next((o for o in self.options if o.name == name), None)


JSON = Option("--json", "Print machine-readable JSON (the --json envelope)")
QUIET = Option("--quiet", "Suppress success output (errors still printed)")
EXPLAIN_SLOTS = Option(
    "--explain-slots", "Print slot-resolution tables after a successful check")
TIMEOUT_MS = Option(
    "--timeout-ms",
    "Per-query Z3 budget in ms (default 10000; also VERA_Z3_TIMEOUT_MS)",
    "n")
RECONCILE = Option(
    "--reconcile", "Reconcile the runtime-check claims (the default)")
NO_RECONCILE = Option(
    "--no-reconcile",
    "Verify without compiling: no reconciliation of the runtime-check claims")
TRIALS = Option("--trials", "Number of trials per function (default 100)", "n",
                "positive")
FN = Option("--fn", "The function to run or test (run: default main)", "name",
            "name")
DISTRUST = Option(
    "--distrust",
    "Also run the functions the verifier proved; a refuted proof is E703")
WAT = Option("--wat", "Print WAT text instead of writing the .wasm binary")
OUTPUT = Option(
    "-o", "Output path (a directory for --target browser)", "path")
TARGET = Option("--target", "Compilation target", "t")
WORLD = Option(
    "--world", "wasi-p2 world: cli (default) or server (wasi:http)", "w")
PORT = Option("--port", "Port to serve on (default 8000; 0 picks one)", "n",
              "port")
HOST = Option("--host", "Host or interface to bind (default 127.0.0.1)", "h")
WRITE = Option("--write", "Format the file in place")
CHECK = Option("--check", "Exit 1 unless the file is already canonical")
STDIO = Option("--stdio", "Speak LSP over stdio (the only transport)")

_WASM_TARGETS = ("wasm", "browser", "wasi-p2")
_WORLDS = ("cli", "server")

COMMANDS: dict[str, Command] = {c.name: c for c in (
    Command("version", "Print the installed Vera version (also --version, -V)",
            False),
    Command("parse", "Parse a .vera file and print the parse tree", True),
    Command("check", "Parse and type-check a .vera file", True,
            (JSON, QUIET, EXPLAIN_SLOTS)),
    Command("typecheck", "Same as check (an alias)", True,
            (JSON, QUIET, EXPLAIN_SLOTS)),
    Command("verify",
            "Type-check, verify contracts via Z3, reconcile runtime checks",
            True,
            (JSON, QUIET, TIMEOUT_MS, RECONCILE, NO_RECONCILE),
            exclusive=(("--reconcile", "--no-reconcile", None),)),
    Command("test", "Test contracts with Z3-generated inputs", True,
            (JSON, TRIALS, FN, DISTRUST)),
    Command("compile", "Compile a .vera file to WebAssembly", True,
            (JSON, WAT, OUTPUT, TARGET, WORLD),
            {"--target": _WASM_TARGETS, "--world": _WORLDS},
            exclusive=(("--wat", "-o", None),
                       ("--wat", "--target", "browser"))),
    Command("run", "Compile and execute a .vera file", True,
            (JSON, FN, TARGET, WORLD),
            {"--target": ("wasm", "wasi-p2"), "--world": _WORLDS},
            program_args=True),
    Command("serve", "Serve handle(Request -> Response) over HTTP", True,
            (PORT, HOST)),
    Command("ast", "Parse a .vera file and print the AST", True, (JSON,)),
    Command("fmt", "Format a .vera file to canonical form (stdout)", True,
            (WRITE, CHECK), exclusive=(("--check", "--write", None),)),
    Command("lsp", "Serve the Language Server Protocol over stdio "
            "(needs the [lsp] extra)", False, (STDIO,)),
    Command("builtins", "List the built-in function registry", False, (JSON,)),
    Command("effects", "List the effect and ability registry", False, (JSON,)),
    Command("errors", "List the diagnostic code registry", False, (JSON,)),
)}

#: The other spellings of a command.
ALIASES = {"--version": "version", "-V": "version"}

HELP_FLAGS = ("--help", "-h")

#: What a refusal of an option adds for the option, after its owners.
_REFUSAL_NOTES = {
    "--timeout-ms": "Set VERA_Z3_TIMEOUT_MS in the environment to reach "
                    "`vera test` and the language server.",
}


def owners(option: str) -> list[str]:
    """The commands that take *option*, the alias apart, in table order."""
    return [c.name for c in COMMANDS.values()
            if c.option(option) is not None and c.name != "typecheck"]


def _quoted(values: tuple[str, ...]) -> str:
    q = [f"'{v}'" for v in values]
    return q[0] if len(q) == 1 else (
        f"{q[0]} or {q[1]}" if len(q) == 2 else ", ".join(q[:-1]) + f", or {q[-1]}")


def _commands(names: list[str]) -> str:
    q = [f"`vera {n}`" for n in names]
    return q[0] if len(q) == 1 else ", ".join(q[:-1]) + f" and {q[-1]}"


def _takes(command: Command) -> str:
    names = [o.name for o in command.options]
    return (f"`vera {command.name}` takes " + ", ".join(names) + "."
            if names else f"`vera {command.name}` takes no option.")


# ---------------------------------------------------------------------
# The help texts
# ---------------------------------------------------------------------


def _synopsis(command: Command) -> str:
    opts = " ".join(
        f"[{o.name} {o.metavar}]" if o.metavar else f"[{o.name}]"
        for o in command.options)
    operand = " <file.vera>" if command.reads_file else ""
    rest = " [-- <args>...]" if command.program_args else ""
    return f"{command.name} {opts}".rstrip() + operand + rest


def _option_line(command: Command | None, option: Option) -> str:
    head = f"{option.name} <{option.metavar}>" if option.metavar else option.name
    text = option.help
    values = command.values.get(option.name) if command else None
    if command is None and option.name == "--target":
        values = _WASM_TARGETS
    if values and option.name == "--target":
        text = f"{text}: {', '.join(values)} (default {values[0]})"
    return f"    {head:<20} {text}"


def usage() -> str:
    """The usage text `vera` prints: every command, then every option."""
    lines = ["Usage: vera <command> [options] <file.vera>", "",
             "Commands:"]
    for command in COMMANDS.values():
        lines.append(f"    {command.name:<10} {command.summary}")
        if command.options or command.program_args:
            lines.append(f"    {'':<10}   vera {_synopsis(command)}")
    lines += ["", "Options:"]
    seen: set[str] = set()
    for command in COMMANDS.values():
        for option in command.options:
            if option.name in seen:
                continue
            seen.add(option.name)
            line = _option_line(None, option)
            lines.append(f"{line} ({', '.join(owners(option.name))})")
    lines.append(f"    {'-h, --help':<20} Print the usage (of one command after it)")
    lines.append(f"    {'-- <args>...':<20} Arguments for the function vera run calls")
    return "\n".join(lines)


def command_help(name: str) -> str:
    """One command's usage, as ``vera <command> --help`` prints it."""
    command = COMMANDS[name]
    lines = [f"Usage: vera {_synopsis(command)}", "", command.summary]
    if command.options:
        lines += ["", "Options:"]
        lines += [_option_line(command, o) for o in command.options]
    lines += ["", "    -h, --help           Print this help"]
    if command.program_args:
        lines.append("    -- <args>...         Arguments for the function "
                     "it calls, each one whatever it looks like")
    return "\n".join(lines)


def markdown_table() -> str:
    """The table as TOOLCHAIN.md shows it, between its `render_lists`
    markers: each command, what it reads, and the options it takes."""
    rows = ["| Command | Reads | Options |", "|---|---|---|"]
    for command in COMMANDS.values():
        opts = [f"`{o.name} <{o.metavar}>`" if o.metavar else f"`{o.name}`"
                for o in command.options]
        for option, values in command.values.items():
            i = [o.name for o in command.options].index(option)
            opts[i] += " (" + ", ".join(values) + ")"
        if command.program_args:
            opts.append("`-- <args>...`")
        reads = "one `.vera` file" if command.reads_file else "no file"
        rows.append(f"| `vera {command.name}` | {reads} | "
                    f"{', '.join(opts) or 'none'} |")
    return "\n".join(rows) + "\n"


# ---------------------------------------------------------------------
# Reading a command line
# ---------------------------------------------------------------------


@dataclass(frozen=True)
class Refusal:
    """A command line refused: the diagnostic, whether it is printed as the
    ``--json`` envelope, and whether the usage text follows it."""

    diagnostic: Diagnostic
    as_json: bool
    usage: bool = False


@dataclass(frozen=True)
class Invocation:
    """A command line read: the command as named and as the table has it,
    the options given (a flag as ``True``, a valued option as its value),
    the operands, and the program's arguments (``None`` with no ``--``)."""

    name: str
    command: Command
    options: dict[str, str | bool]
    files: list[str]
    program_args: list[str] | None
    help: bool = False

    def flag(self, name: str) -> bool:
        return self.options.get(name) is True

    def value(self, name: str) -> str | None:
        v = self.options.get(name)
        return v if isinstance(v, str) else None


def _is_option(arg: str) -> bool:
    """An option is a token led by a dash, bar ``-`` alone (stdin)."""
    return arg.startswith("-") and arg != "-"


def _is_number(arg: str) -> bool:
    """A token that is an integer, negative ones included: an option's
    value, never an option (`--trials -5` is a value out of its domain)."""
    try:
        int(arg)
    except ValueError:
        return False
    return True


_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _domain_refusal(option: Option, value: str) -> Diagnostic | None:
    """E903 when *value* is outside *option*'s domain, else ``None``.  The
    budget (`--timeout-ms`) is held by `vera.smt.resolve_timeout_ms`, which
    the environment variable shares."""
    name = option.name
    if value == "":
        return command_errors.invalid_option_value(f"{name}: empty value")
    if option.domain == "positive":
        if not _is_number(value):
            return command_errors.invalid_option_value(
                f"Invalid {name} value: {value}")
        if int(value) < 1:
            return command_errors.invalid_option_value(
                f"Invalid {name} value: {value} (expected a positive integer)")
    elif option.domain == "port":
        if not _is_number(value):
            return command_errors.invalid_option_value(
                f"{name} requires an integer, not {value!r}.")
        if not 0 <= int(value) <= 65535:
            return command_errors.invalid_option_value(
                f"{name} requires an integer from 0 to 65535, not {value!r}.")
    elif option.domain == "name" and not _NAME.fullmatch(value):
        return command_errors.invalid_option_value(
            f"Invalid {name} value: {value!r} (expected a function's name)")
    return None


def parse(argv: list[str]) -> Invocation | Refusal:
    """Read *argv* (the arguments after ``vera``, which names a command)
    against `COMMANDS`, by the rules the module docstring states."""
    word = argv[0]
    own = argv[1:argv.index("--")] if "--" in argv else argv[1:]
    rest = argv[argv.index("--") + 1:] if "--" in argv else None
    as_json = "--json" in own
    name = ALIASES.get(word, word)
    command = COMMANDS.get(name)
    if command is None:
        return Refusal(command_errors.command_not_understood(
            f"Unknown command: {word}"), as_json, usage=True)

    options: dict[str, str | bool] = {}
    files: list[str] = []
    refusal: Diagnostic | None = None
    help_asked = False
    i = 0
    while i < len(own):
        token = own[i]
        i += 1
        if token in HELP_FLAGS:
            help_asked = True
            continue
        if not _is_option(token):
            files.append(token)
            continue
        option = command.option(token)
        if option is None:
            if refusal is None:
                refusal = _not_accepted(token, command)
            continue
        value: str | bool = True
        if option.metavar is not None:
            # A value is the next token, unless there is none or it is an
            # option itself (`--fn --json`): a negative number is a value.
            if i >= len(own) or (_is_option(own[i]) and not _is_number(own[i])):
                refusal = refusal or command_errors.invalid_option_value(
                    f"{token}: missing value")
                continue
            value = own[i]
            i += 1
            allowed = command.values.get(token)
            if refusal is None:
                if allowed is not None and value not in allowed:
                    refusal = command_errors.invalid_option_value(
                        f"Invalid {token} value: {value} "
                        f"(expected {_quoted(allowed)})")
                else:
                    refusal = _domain_refusal(option, value)
        if token in options:
            refusal = refusal or command_errors.contradictory_options(
                f"{token} is given twice; `vera {name}` takes it once.")
            continue
        options[token] = value

    if help_asked:
        return Invocation(name, command, options, files, rest, help=True)
    if refusal is None:
        refusal = _contradiction(command, options)
    if refusal is None and rest is not None and not command.program_args:
        dashed = next((a for a in rest if _is_option(a) and os.path.isfile(a)), None)
        refusal = command_errors.option_not_accepted(
            f"`--` passes arguments to the function `vera run` calls; "
            f"`vera {name}` calls none.",
            fix=_dash_file_fix(name, dashed) if dashed else None)
    if refusal is not None:
        return Refusal(refusal, as_json)
    if command.reads_file and not files:
        return Refusal(command_errors.command_not_understood(
            f"`vera {name}` names no file: it reads a .vera source file."),
            as_json, usage=True)
    if command.reads_file and len(files) > 1:
        return Refusal(command_errors.second_file_refused(name, len(files)),
                       as_json)
    if not command.reads_file and files:
        return Refusal(command_errors.command_not_understood(
            f"`vera {name}` reads no file, and the command line names "
            f"{files[0]!r}."), as_json, usage=True)
    if command.reads_file:
        path = files[0]
        if path == "":
            return Refusal(command_errors.file_not_found(
                path, description="an empty argument names no file"), as_json)
        if os.path.isdir(path):
            return Refusal(command_errors.file_not_found(
                path, description=f"not a file: {path} is a directory"),
                as_json)
    return Invocation(name, command, options, files, rest)


def _contradiction(command: Command, options: dict[str, str | bool]) -> Diagnostic | None:
    """E902 for the first of the command's exclusive pairs the options hold
    both sides of."""
    for first, second, value in command.exclusive:
        held = options.get(second)
        if first in options and held is not None and (value is None or held == value):
            other = second if value is None else f"{second} {value}"
            return command_errors.contradictory_options(
                f"`vera {command.name}` takes {first} or {other}, not both.")
    return None


def _dash_file_fix(name: str, path: str) -> str:
    return (
        f"{path} is a file, and a token that begins with a dash is read as "
        f"an option. Name the file by a path that begins otherwise:\n\n"
        f"  vera {name} ./{path}"
    )


def _not_accepted(token: str, command: Command) -> Diagnostic:
    """E901 for *token* on *command*: an option written with `=`, a file
    whose name begins with a dash, the commands that take the option, or
    that none does and what this one takes."""
    name = command.name
    head, eq, value = token.partition("=")
    if eq:
        option = command.option(head)
        if option is not None:
            if option.metavar is None:
                return command_errors.option_not_accepted(
                    f"{token}: {head} takes no value.",
                    fix=f"Write the option alone:\n\n  vera {name} {head} program.vera")
            return command_errors.option_not_accepted(
                f"{token}: write the value after a space, `{head} {value}`.",
                fix=(f"Write the option and its value as two arguments:\n\n"
                     f"  vera {name} {head} {value} program.vera"))
        token = head
    if os.path.isfile(token) and not owners(token):
        return command_errors.option_not_accepted(
            f"{token} is not an option of any `vera` command, and it names a "
            f"file: write `./{token}` to name the file.",
            fix=_dash_file_fix(name, token))
    takers = owners(token)
    if takers:
        text = (f"{token} is only accepted by {_commands(takers)}, "
                f"not `vera {name}`.")
        note = _REFUSAL_NOTES.get(token)
        if note:
            text += f" {note}"
    else:
        text = (f"{token} is not an option of any `vera` command. "
                + _takes(command))
    return command_errors.option_not_accepted(text)
