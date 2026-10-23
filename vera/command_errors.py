"""The diagnostics a command reports about its own run (#1490).

Spec §0.5.1 names two ranges that belong to no compiler phase: an ``E8xx``
code reports a program's own failure while it runs, and an ``E9xx`` code a
refusal of the command line itself, not of the program it names.  Every
command builds them here, one function per code, so each code has one
construction site and ``scripts/check_diagnostic_fields.py`` holds every one
to the fields every diagnostic carries.  A command prints the diagnostic's
``Diagnostic.format()`` as its text, and under ``--json`` the envelope
carries its ``Diagnostic.to_dict()``.

Each function takes the *description* the command words for the case in
hand (the flag, the path, the function it could not call), so the text a
command has always printed stays its description, and writes the rationale
and the fix the concept has wherever it arises.  *path* is the source file
the command was asked about, which the location names; a refusal of the
command line made before any file is read has none.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import TYPE_CHECKING

from vera.errors import Diagnostic, SourceLocation

if TYPE_CHECKING:
    from vera.runtime.traps import TrapFrame


def _at(path: str | None) -> SourceLocation:
    """The location of a refusal about *path* as a whole: no position in it."""
    return SourceLocation(file=path, line=0, column=0)


def runtime_trap(
    path: str | None,
    description: str,
    *,
    fix: str = "",
    frames: Sequence[TrapFrame] = (),
) -> Diagnostic:
    """E800: the program trapped while it ran.

    *description* is the trap's message and *fix* its kind's paragraph,
    empty for the kinds whose message already says what to change.  The
    location is the first function of the program's own the backtrace
    *frames* name, at the line its declaration starts on, or *path* when
    the trap unwound through none (a trap in a runtime helper alone).
    """
    location = _at(path)
    for frame in frames:
        if not frame.is_builtin and frame.line_start is not None:
            location = SourceLocation(
                file=frame.file, line=frame.line_start, column=1)
            break
    return Diagnostic(
        description=description,
        location=location,
        rationale=(
            "The program stopped while it ran: a check the compiler emitted "
            "failed, or WebAssembly refused an operation, and nothing after "
            "that point ran. The trap's kind is `trap_kind` in the `--json` "
            "envelope, and the source backtrace names the functions it "
            "unwound through."
        ),
        fix=fix,
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E800",
    )


def file_not_found(path: str) -> Diagnostic:
    """E900: the command names a source file that does not exist."""
    return Diagnostic(
        description=f"file not found: {path}",
        location=_at(path),
        rationale=(
            "A command reads the Vera source file its command line names, "
            "and no file exists at that path. A relative path is read from "
            "the directory the command runs in."
        ),
        fix=(
            "Name a .vera file that exists: a path relative to the directory "
            "the command runs in, or an absolute one.\n\n"
            "  vera check path/to/program.vera"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E900",
    )


def option_not_accepted(description: str) -> Diagnostic:
    """E901: an option given to a command that does not read it."""
    return Diagnostic(
        description=description,
        location=_at(None),
        rationale=(
            "An option belongs to the commands that read it. A command that "
            "cannot honour an option refuses it rather than ignore it, so an "
            "option never seems to take effect where it does not."
        ),
        fix=(
            "Drop the option, or give it to the command that takes it:\n\n"
            "  vera verify --timeout-ms 60000 program.vera\n"
            "  vera test --distrust program.vera\n"
            "  vera verify --no-reconcile program.vera"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E901",
    )


def contradictory_options(
    description: str, path: str | None = None,
) -> Diagnostic:
    """E902: options that cannot hold together."""
    return Diagnostic(
        description=description,
        location=_at(path),
        rationale=(
            "The options on this command line cannot all hold: one needs "
            "another that is absent, or two ask for opposite things, so the "
            "command cannot tell which was meant."
        ),
        fix=(
            "Keep one consistent set of options, as the description says. "
            "`--world server` needs `--target wasi-p2` and is served, not "
            "run; `--fn` runs under the default target; `vera verify` takes "
            "`--reconcile` or `--no-reconcile`:\n\n"
            "  vera compile --target wasi-p2 --world server program.vera\n"
            "  vera run --fn f program.vera"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E902",
    )


def invalid_option_value(description: str) -> Diagnostic:
    """E903: an option, or the variable standing for one, with a value it
    does not take."""
    return Diagnostic(
        description=description,
        location=_at(None),
        rationale=(
            "An option's value must be one the option takes. The description "
            "names the option and, where it takes a fixed set, the values."
        ),
        fix=(
            "Give the option a value it takes: `--target` wasm, browser or "
            "wasi-p2; `--world` cli or server; `--trials` and `--port` an "
            "integer; `--timeout-ms` and VERA_Z3_TIMEOUT_MS a positive "
            "integer number of milliseconds.\n\n"
            "  vera verify --timeout-ms 60000 program.vera"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E903",
    )


def command_not_understood(description: str) -> Diagnostic:
    """E904: an unknown command, or a command that reads a file and names
    none."""
    return Diagnostic(
        description=description,
        location=_at(None),
        rationale=(
            "`vera` takes a command, its options and, for a command that "
            "reads a program, the path of the program's source file. The "
            "usage text lists the commands."
        ),
        fix=(
            "Name one of the commands the usage lists, and the file it "
            "reads:\n\n"
            "  vera check program.vera"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E904",
    )


def no_exports(path: str | None, description: str) -> Diagnostic:
    """E905: the compiled module exports no function to call."""
    return Diagnostic(
        description=description,
        location=_at(path),
        rationale=(
            "A module's entry points are the public functions code "
            "generation compiled. With none, the compiled module has nothing "
            "a host can call."
        ),
        fix=(
            "Declare the function to call public, and where code generation "
            "dropped a public function, fix the construct its [E602] "
            "warning names:\n\n"
            "  public fn main(-> @Int)\n"
            "    requires(true)\n"
            "    ensures(true)\n"
            "    effects(pure)\n"
            "  {\n"
            "    0\n"
            "  }"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E905",
    )


def fn_not_exported(path: str | None, description: str) -> Diagnostic:
    """E906: ``--fn`` names a function the module does not export."""
    return Diagnostic(
        description=description,
        location=_at(path),
        rationale=(
            "`--fn` names the function to call, and only an exported one, a "
            "public function code generation compiled, can be called from "
            "outside the module."
        ),
        fix=(
            "Name a function the description lists as exported, or declare "
            "the one you meant public:\n\n"
            "  vera run program.vera --fn main"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E906",
    )


def entry_dropped(path: str | None, description: str) -> Diagnostic:
    """E907: the function to run was dropped by code generation."""
    return Diagnostic(
        description=description,
        location=_at(path),
        rationale=(
            "Code generation dropped the function to run, because its body, "
            "or the body of a function it calls, holds a construct code "
            "generation cannot compile. Running another function in its "
            "place would answer a question nobody asked."
        ),
        fix=(
            "Fix the construct the [E602] warning names (the [E620] chain "
            "says which call reaches it), or run another exported function "
            "with --fn."
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E907",
    )


def target_requirement(path: str | None, description: str) -> Diagnostic:
    """E908: the program lacks what its target, or ``vera serve``, needs."""
    return Diagnostic(
        description=description,
        location=_at(path),
        rationale=(
            "A target needs something of the program: `--target browser` "
            "calls `main` when the page loads, `--target wasi-p2` hosts only "
            "the host families it implements, and `vera serve` calls "
            "`handle(@Request -> @Response)` for each request."
        ),
        fix=(
            "Give the program what the target needs, as the description "
            "says, or build it for the default target:\n\n"
            "  vera run program.vera"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E908",
    )


def arguments_do_not_fit(path: str | None, description: str) -> Diagnostic:
    """E909: the arguments ``vera run`` was given do not fit the function."""
    return Diagnostic(
        description=description,
        location=_at(path),
        rationale=(
            "`vera run` passes the arguments after `--` to the function it "
            "calls, one per parameter, each read as its parameter's type and "
            "held to that type's range."
        ),
        fix=(
            "Pass one argument per parameter, each a value of its type:\n\n"
            "  vera run program.vera --fn f -- 1 2"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E909",
    )


def cannot_bind(description: str, path: str | None = None) -> Diagnostic:
    """E910: ``vera serve`` cannot bind the address it was given."""
    return Diagnostic(
        description=description,
        location=_at(path),
        rationale=(
            "`vera serve` listens on a host and port, and the operating "
            "system refused to bind them: another process holds the port, or "
            "the host names no interface of this machine."
        ),
        fix=(
            "Serve on a free port, or stop the process that holds this "
            "one:\n\n"
            "  vera serve --port 8080 program.vera"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E910",
    )


def output_not_writable(
    path: str | None, output: str, error: OSError,
) -> Diagnostic:
    """E912: the command cannot write the output it was asked to, *output*:
    its directory does not exist, or the command may not write there."""
    return Diagnostic(
        description=(
            f"cannot write the output {output}: {error.strerror or error}"),
        location=_at(path),
        rationale=(
            "The command writes its output to the path its command line "
            "names, or beside the source, and the operating system refused "
            "the write: the path's directory does not exist, the path is a "
            "directory, or the command may not write there."
        ),
        fix=(
            "Name an output path in a directory that exists and the command "
            "may write, or create the directory first:\n\n"
            "  vera compile -o build/program.wasm program.vera"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E912",
    )


def optional_dependency(description: str) -> Diagnostic:
    """E911: a command needs an optional extra that is not installed."""
    return Diagnostic(
        description=description,
        location=_at(None),
        rationale=(
            "The language server's transport is an optional extra, so the "
            "base install stays minimal, and `vera lsp` needs it."
        ),
        fix=(
            "Install the extra in the source checkout:\n\n"
            '  pip install -e ".[lsp]"'
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E911",
    )
