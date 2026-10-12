"""The test suite's one driver for the compiler pipeline.

A test that parses, checks, verifies, compiles, runs or contract-tests a
program drives it through this module rather than through a driver of its
own.  Each stage has one function, and each function runs the stages before
it in process, wired exactly as the CLI wires them, from the compiler's own
stage functions:

- ``parse``: parse and transform (``vera.parser.parse``, ``transform``).
- ``check``: ``parse``, then resolve the imports and type-check
  (``ModuleResolver``, ``typecheck_with_artifacts``), as ``vera check`` does.
- ``verify``: ``check``, then verify the contracts with the checker's tables
  (``vera.verifier.verify``), as ``vera verify`` does.
- ``compile``: ``check``, then generate code with the checker's tables
  (``CodeGenerator.compile_program``), as ``vera compile`` does.
- ``run``: ``compile``, then execute one export (``vera.codegen.execute``).
- ``contract_test``: ``check``, then contract-driven testing with the
  checker's tables (``vera.tester.test``), as ``vera test`` does.
- ``cli``: ``vera.cli.main`` itself, in process, with its argv, stdin and
  output captured.

A stage takes source text (a ``str``) or the path of a file (any
``os.PathLike``).  Source text is labelled with *file*, or with nothing, as
the compiler's own functions label it; a path is read as UTF-8, labelled with
itself, and its imports are resolved from its directory (or *root*), as the
CLI resolves them.  Source text resolves nothing: modules built in memory go
in through *modules*, and a program whose imports should be resolved from
disk is written there first (:func:`write_tree`) and handed over by path.

A stage returns its result rather than raising: ``ok``, the diagnostics in
the order the CLI reports them, the artefact the stage made (the typed
program, the verification result with its obligations, the compiled module
with its WAT and bytes, the execution's value and output or its trap), and
``envelope()``, the JSON object ``vera <stage> --json`` prints for the same
input.  An artefact the stage did not make is not there to read: reading it
raises what stopped the stage, the parse or transform error itself, the
trap itself, or :class:`StageFailed` naming the errors of a stage that
refused the program.  A compiler crash is never a result: it propagates.

``compile`` also asserts the one invariant every compiled module must hold
whatever it is for (#1185): a module that holds a ``call_indirect`` declares
a function table.

Three options name the configurations the CLI never runs, which some suites
measure on purpose:

- ``compile(..., checked=False)`` (and ``run``) generates code from the
  parsed program alone, with no resolution, no type check and none of the
  checker's tables, which is how the code-generation suites drive code
  generation: their programs need not type-check.
- ``verify(..., past_check=True)`` and ``compile(..., past_check=True)``
  verify, or generate code for, a program the check refused, with the
  tables that check collected: a test of what the verifier or code
  generation does with a program the checker refuses (that the verifier
  does not crash on one, or a code-generation refusal that sits behind a
  check refusal).
- ``check``'s *collect_module_artifacts* collects each imported module's own
  tables, as ``vera verify``, ``compile`` and ``run`` do and ``vera check``
  does not.

``tests/checker_helpers.py``, ``tests/verifier_helpers.py``,
``tests/codegen_helpers.py`` and ``tests/module_fixture_helpers.py`` keep
their names for the files that import them, as thin layers over this module.
``scripts/check_test_drivers.py`` fails a test helper that drives a stage
itself.
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import re
import sys
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from vera import ast
from vera.checker import CheckArtifacts, typecheck_with_artifacts
from vera.codegen import CodeGenerator, CompileResult, ExecuteResult, execute
from vera.codegen.api import HttpRequestData
from vera.errors import Diagnostic, VeraError
from vera.parser import parse as _parse_tree
from vera.resolver import ModuleResolver, ResolvedModule
from vera.runtime.traps import WasmTrapError
from vera.smt import resolve_timeout_ms
from vera.tester import TestResult
from vera.tester import test as _test_program
from vera.transform import transform
from vera.verifier import VerifyResult
from vera.verifier import verify as _verify_program

#: What a stage takes: source text, or the path of a file.
Source = str | os.PathLike[str]

__all__ = [
    "CALL_INDIRECT_RE",
    "TABLE_DECL_RE",
    "Checked",
    "CliResult",
    "Compiled",
    "Parsed",
    "Ran",
    "Source",
    "StageFailed",
    "Tested",
    "Verified",
    "assert_no_orphan_call_indirect",
    "check",
    "cli",
    "compile",
    "contract_test",
    "parse",
    "run",
    "verify",
    "write_tree",
]


class StageFailed(AssertionError):
    """An artefact was read from a stage that refused the program.

    An ``AssertionError``, so a test that reads one fails the way an
    assertion fails, with the refusing stage's errors as its message.
    """


def _describe(diagnostics: Sequence[Diagnostic]) -> str:
    return "; ".join(
        f"[{d.error_code}] {d.description}" if d.error_code else d.description
        for d in diagnostics
    )


def _errors(diagnostics: Sequence[Diagnostic]) -> tuple[Diagnostic, ...]:
    return tuple(d for d in diagnostics if d.severity == "error")


def _raise_front_end_error(parsed: Parsed) -> None:
    """Raise the parse or transform error that stopped *parsed*, if one did."""
    if parsed.error is not None:
        raise parsed.error


def _warnings(diagnostics: Sequence[Diagnostic]) -> tuple[Diagnostic, ...]:
    return tuple(d for d in diagnostics if d.severity == "warning")


# =====================================================================
# parse
# =====================================================================


@dataclass(frozen=True)
class Parsed:
    """The front end's result: the program, or the error that stopped it."""

    #: The text that was parsed.
    source: str
    #: The label every stage reports the program under (``None`` for source
    #: text given no *file*).
    file: str | None
    #: The file it was read from, for a path; ``None`` for source text.
    path: Path | None
    #: The parse or transform error, when there was one.
    error: VeraError | None
    _program: ast.Program | None

    @property
    def ok(self) -> bool:
        return self.error is None

    @property
    def diagnostics(self) -> tuple[Diagnostic, ...]:
        return (self.error.diagnostic,) if self.error is not None else ()

    @property
    def program(self) -> ast.Program:
        """The program; the parse or transform error, raised, if it failed."""
        _raise_front_end_error(self)
        assert self._program is not None
        return self._program


def _read(source: Source, file: str | None) -> tuple[str, str | None, Path | None]:
    if isinstance(source, str):
        return source, file, None
    path = Path(source)
    return path.read_text(encoding="utf-8"), file if file is not None else str(path), path


def parse(source: Source, *, file: str | None = None) -> Parsed:
    """Parse and transform *source*, as every command does first."""
    text, label, path = _read(source, file)
    try:
        program = transform(_parse_tree(text, file=label))
    except VeraError as exc:
        return Parsed(text, label, path, exc, None)
    return Parsed(text, label, path, None, program)


# =====================================================================
# check
# =====================================================================


@dataclass(frozen=True)
class Checked:
    """``parse``, import resolution and the type check."""

    parsed: Parsed
    #: The modules the program was checked against, or ``None`` when none
    #: were resolved or given (source text with no *modules*).
    modules: tuple[ResolvedModule, ...] | None
    #: The resolver's diagnostics (an import it could not resolve, E011, or
    #: a cycle, E012).
    resolution_diagnostics: tuple[Diagnostic, ...]
    #: The checker's diagnostics.
    checker_diagnostics: tuple[Diagnostic, ...]
    _artifacts: CheckArtifacts | None

    @property
    def diagnostics(self) -> tuple[Diagnostic, ...]:
        """The parse error, or the resolver's diagnostics then the checker's."""
        return (self.parsed.diagnostics + self.resolution_diagnostics
                + self.checker_diagnostics)

    @property
    def ok(self) -> bool:
        return not self.errors

    @property
    def errors(self) -> tuple[Diagnostic, ...]:
        return _errors(self.diagnostics)

    @property
    def warnings(self) -> tuple[Diagnostic, ...]:
        return _warnings(self.diagnostics)

    @property
    def source(self) -> str:
        return self.parsed.source

    @property
    def file(self) -> str | None:
        return self.parsed.file

    @property
    def program(self) -> ast.Program:
        return self.parsed.program

    @property
    def artifacts(self) -> CheckArtifacts:
        """The checker's tables; the parse error, raised, if it failed."""
        _raise_front_end_error(self.parsed)
        assert self._artifacts is not None
        return self._artifacts

    @property
    def resolved(self) -> list[ResolvedModule] | None:
        """:attr:`modules` as the stage functions take them."""
        return list(self.modules) if self.modules is not None else None

    def envelope(self) -> dict[str, Any]:
        """What ``vera check --json`` prints for this program."""
        return {
            "ok": self.ok,
            "file": self.file,
            "diagnostics": [d.to_dict() for d in self.errors],
            "warnings": [d.to_dict() for d in self.warnings],
        }


def _resolve(
    program: ast.Program, parsed: Parsed, root: Path | None,
    modules: Sequence[ResolvedModule] | None,
) -> tuple[tuple[ResolvedModule, ...] | None, list[Diagnostic]]:
    if modules is not None:
        return tuple(modules), []
    if parsed.path is None:
        return None, []
    resolver = ModuleResolver(_root=root if root is not None else parsed.path.parent)
    resolved = resolver.resolve_imports(program, parsed.path)
    return tuple(resolved), list(resolver.errors)


def check(
    source: Source,
    *,
    file: str | None = None,
    root: Path | None = None,
    modules: Sequence[ResolvedModule] | None = None,
    collect_module_artifacts: bool = False,
) -> Checked:
    """Parse, resolve and type-check *source*, as ``vera check`` does.

    *root* is the directory imports resolve from, for a path (its own
    directory by default); *modules* replaces resolution with the modules
    given.
    """
    parsed = parse(source, file=file)
    if not parsed.ok:
        return Checked(parsed, None, (), (), None)
    program = parsed.program
    resolved, resolver_diagnostics = _resolve(program, parsed, root, modules)
    diagnostics, artifacts = typecheck_with_artifacts(
        program, parsed.source, file=parsed.file,
        resolved_modules=list(resolved) if resolved is not None else None,
        collect_module_artifacts=collect_module_artifacts,
    )
    return Checked(
        parsed, resolved, tuple(resolver_diagnostics), tuple(diagnostics),
        artifacts,
    )


# =====================================================================
# verify
# =====================================================================


@dataclass(frozen=True)
class Verified:
    """``check``, then contract verification when the check passed (or
    past it, with ``past_check``)."""

    checked: Checked
    #: The budget each solver query had, as the caller gave it.
    timeout_ms: int | None
    _result: VerifyResult | None

    @property
    def ran(self) -> bool:
        """Whether verification ran: it does not when the check refused,
        unless asked to run past it."""
        return self._result is not None

    @property
    def result(self) -> VerifyResult:
        """The verifier's result; raises what stopped the check, if it did."""
        if self._result is None:
            _raise_front_end_error(self.checked.parsed)
            raise StageFailed(
                "verification did not run: the check reported "
                + _describe(self.checked.errors))
        return self._result

    @property
    def diagnostics(self) -> tuple[Diagnostic, ...]:
        """The check's diagnostics, then the verifier's."""
        own = tuple(self._result.diagnostics) if self._result is not None else ()
        return self.checked.diagnostics + own

    @property
    def errors(self) -> tuple[Diagnostic, ...]:
        return _errors(self.diagnostics)

    @property
    def warnings(self) -> tuple[Diagnostic, ...]:
        return _warnings(self.diagnostics)

    @property
    def ok(self) -> bool:
        return self.ran and not self.errors

    @property
    def obligations(self) -> list[Any]:
        return list(self.result.obligations)

    def envelope(self) -> dict[str, Any]:
        """What ``vera verify --json`` prints for this program."""
        if self._result is None:
            if not self.checked.parsed.ok:
                return self.checked.envelope()
            return {
                "ok": False,
                "file": self.checked.file,
                "diagnostics": [d.to_dict() for d in self.checked.errors],
                "warnings": [d.to_dict() for d in self.checked.warnings],
            }
        result = self._result
        label = self.checked.file
        summary = result.summary
        return {
            "ok": not self.errors,
            "file": label,
            "diagnostics": [d.to_dict() for d in self.errors],
            "warnings": [d.to_dict() for d in self.warnings],
            "verification": {
                "tier1_verified": summary.tier1_verified,
                "tier3_runtime": summary.tier3_runtime,
                "total": summary.total,
                "assumptions": summary.assumptions,
                "timeout_ms": resolve_timeout_ms(self.timeout_ms),
            },
            "obligations": [
                {
                    "kind": o.kind,
                    "status": o.status,
                    "description": o.expr_text,
                    "location": {
                        "line": o.line,
                        "column": o.column,
                        **({"file": o.file or label} if label else {}),
                    },
                    **({"error_code": o.error_code} if o.error_code else {}),
                }
                for o in result.obligations
            ],
        }


def verify(
    source: Source,
    *,
    file: str | None = None,
    root: Path | None = None,
    modules: Sequence[ResolvedModule] | None = None,
    timeout_ms: int | None = None,
    past_check: bool = False,
) -> Verified:
    """Check *source*, then verify its contracts, as ``vera verify`` does.

    Verification runs only on a program the check accepts, with the
    checker's tables for the program and for each module it imports.  With
    ``past_check=True`` it runs on a program the check refuses too, with the
    tables that check collected.
    """
    checked = check(
        source, file=file, root=root, modules=modules,
        collect_module_artifacts=True,
    )
    if not checked.parsed.ok or (not checked.ok and not past_check):
        return Verified(checked, timeout_ms, None)
    artifacts = checked.artifacts
    result = _verify_program(
        checked.program, checked.source, file=checked.file,
        timeout_ms=timeout_ms,
        resolved_modules=checked.resolved,
        expr_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
    )
    return Verified(checked, timeout_ms, result)


# =====================================================================
# compile
# =====================================================================


#: A ``call_indirect`` instruction, and a ``(table ...)`` declaration, in WAT.
CALL_INDIRECT_RE = re.compile(r"(?m)^\s*call_indirect\b")
TABLE_DECL_RE = re.compile(r"(?m)^\s*\(table\b")


def assert_no_orphan_call_indirect(wat: str) -> None:
    """#1185: every emitted ``call_indirect`` has a table to dispatch on.

    A ``call_indirect`` names no symbol, so the #1100 caller-drop pass
    (which scans the WAT for ``call $f``) cannot see it.  When an [E602]
    skip swallowed a module's only closure the lift rolled back, module
    assembly suppressed the ``(table)``/``(elem)`` sections, and any
    surviving ``apply_fn`` / ``array_map`` carrier kept an indirect call
    into a table that no longer existed: an uninstantiable module emitted
    with no diagnostics, which raised a raw ``WasmtimeError: unknown table
    0`` the moment any export ran.

    A differential over the two sides that must agree (the instruction
    stream and the table section), asserted on every module :func:`compile`
    builds.  Only this direction is universal: a table with no indirect call
    is inert, and happens whenever a lift succeeds and its sole carrier is
    dropped for an unrelated reason (the [E616] fixture in
    ``tests/test_codegen_interpolation.py``).
    """
    if CALL_INDIRECT_RE.search(wat) and not TABLE_DECL_RE.search(wat):
        raise AssertionError(
            "#1185: emitted WAT contains `call_indirect` but declares no "
            "function table — the module cannot be instantiated, and the "
            "user gets a raw `unknown table 0` from wasmtime instead of a "
            "located diagnostic.  The carrier must be dropped instead."
        )


@dataclass(frozen=True)
class Compiled:
    """``check`` (or ``parse`` alone, unchecked), then code generation."""

    parsed: Parsed
    #: The check, or ``None`` for an unchecked compile.
    checked: Checked | None
    _result: CompileResult | None
    #: The generator that built the module, for a test that reads what it
    #: registered; ``None`` when code generation did not run.
    generator: CodeGenerator | None

    @property
    def result(self) -> CompileResult:
        """The compiled module; raises what stopped the check, if it did."""
        if self._result is None:
            _raise_front_end_error(self.parsed)
            assert self.checked is not None
            raise StageFailed(
                "code generation did not run: the check reported "
                + _describe(self.checked.errors))
        return self._result

    @property
    def diagnostics(self) -> tuple[Diagnostic, ...]:
        """The check's diagnostics, then code generation's."""
        front = (self.checked.diagnostics if self.checked is not None
                 else self.parsed.diagnostics)
        own = tuple(self._result.diagnostics) if self._result is not None else ()
        return front + own

    @property
    def errors(self) -> tuple[Diagnostic, ...]:
        return _errors(self.diagnostics)

    @property
    def warnings(self) -> tuple[Diagnostic, ...]:
        return _warnings(self.diagnostics)

    @property
    def ok(self) -> bool:
        """The check accepted the program (when it ran), and code generation
        ran and reported no error."""
        return self._result is not None and not self.errors

    @property
    def wat(self) -> str:
        return self.result.wat

    @property
    def wasm_bytes(self) -> bytes:
        return self.result.wasm_bytes

    @property
    def exports(self) -> list[str]:
        return self.result.exports

    def envelope(self) -> dict[str, Any]:
        """What ``vera compile --json`` prints for this program."""
        label = self.parsed.file
        if self._result is None:
            if self.checked is None or not self.parsed.ok:
                return {
                    "ok": False, "file": label,
                    "diagnostics": [d.to_dict() for d in self.parsed.diagnostics],
                    "warnings": [],
                }
            return {
                "ok": False, "file": label,
                "diagnostics": [d.to_dict() for d in self.checked.errors],
                "warnings": [d.to_dict() for d in self.checked.warnings],
            }
        result = self._result
        warnings = [d.to_dict() for d in self.warnings]
        if self.errors:
            return {
                "ok": False, "file": label,
                "diagnostics": [d.to_dict() for d in _errors(result.diagnostics)],
                "warnings": warnings,
            }
        entries = [
            tld.decl.name for tld in self.parsed.program.declarations
            if isinstance(tld.decl, ast.FnDecl)
            and tld.visibility == "public" and not tld.decl.forall_vars
        ]
        if entries and not result.exports:
            declared = "".join(f"  - {n}\n" for n in entries)
            return {
                "ok": False, "file": label, "exports": [],
                "diagnostics": [{
                    "severity": "error",
                    "description": (
                        "No exported functions — the compiled module has no "
                        "entry points.\n"
                        f"\nDeclared public functions:\n{declared}"
                        "\nA public function whose body (or a callee's body) "
                        "could not be compiled is dropped from the module "
                        "with a diagnostic above; fix the reported construct "
                        "to restore the export."
                    ),
                    "location": {"line": 0, "column": 0},
                }],
                "warnings": warnings,
            }
        return {
            "ok": True, "file": label, "exports": result.exports,
            "diagnostics": [], "warnings": warnings,
        }


def compile(
    source: Source,
    *,
    file: str | None = None,
    root: Path | None = None,
    modules: Sequence[ResolvedModule] | None = None,
    checked: bool = True,
    past_check: bool = False,
) -> Compiled:
    """Check *source*, then compile it, as ``vera compile`` does.

    Code generation runs only on a program the check accepts, with the
    checker's tables for the program and each module it imports.  With
    ``past_check=True`` it runs on a program the check refuses too, with the
    tables that check collected, so a code-generation refusal behind a
    check refusal is still driven.  With ``checked=False`` it runs on the
    parsed program alone (and *modules*, if given): no resolution, no check
    and no tables.
    """
    front: Checked | None
    if checked:
        front = check(
            source, file=file, root=root, modules=modules,
            collect_module_artifacts=True,
        )
        parsed = front.parsed
        if not parsed.ok or (not front.ok and not past_check):
            return Compiled(parsed, front, None, None)
        artifacts = front.artifacts
        generator = CodeGenerator(
            source=parsed.source, file=parsed.file,
            resolved_modules=front.resolved,
            expr_semantic_types=artifacts.expr_semantic_types,
            expr_target_types=artifacts.expr_target_types,
            module_artifacts=artifacts.module_artifacts,
        )
    else:
        front = None
        parsed = parse(source, file=file)
        if not parsed.ok:
            return Compiled(parsed, None, None, None)
        generator = CodeGenerator(
            source=parsed.source, file=parsed.file,
            resolved_modules=list(modules) if modules is not None else None,
        )
    result = generator.compile_program(parsed.program)
    assert_no_orphan_call_indirect(result.wat)
    return Compiled(parsed, front, result, generator)


# =====================================================================
# run
# =====================================================================


@dataclass(frozen=True)
class Ran:
    """``compile``, then the execution of one export."""

    #: The compile, or ``None`` when ``run`` was handed a compiled module.
    compiled: Compiled | None
    #: The module that ran, or ``None`` when the compile refused.
    module: CompileResult | None
    #: The function asked for (``None``: the module's default entry).
    fn: str | None
    _execution: ExecuteResult | None
    #: The trap that ended the execution, if one did.
    trap: WasmTrapError | None

    @property
    def ok(self) -> bool:
        """The module compiled and the call returned without a trap."""
        return self._execution is not None

    def _refusal(self) -> tuple[Diagnostic, ...]:
        """The errors of the stage that refused the program."""
        assert self.compiled is not None
        if self.compiled._result is None:
            if self.compiled.checked is None:
                return self.compiled.parsed.diagnostics
            return self.compiled.checked.errors
        return _errors(self.compiled._result.diagnostics)

    @property
    def execution(self) -> ExecuteResult:
        """The execution's result; raises the trap, if there was one."""
        if self.trap is not None:
            raise self.trap
        if self._execution is None:
            assert self.compiled is not None
            _ = self.compiled.result  # raises what refused it, if the check did
            raise StageFailed(
                "the module did not run: code generation reported "
                + _describe(self._refusal()))
        return self._execution

    @property
    def value(self) -> int | float | str | None:
        return self.execution.value

    @property
    def stdout(self) -> str:
        """What the program printed, up to its trap if it trapped."""
        if self.trap is not None:
            return self.trap.stdout
        return self.execution.stdout

    @property
    def stderr(self) -> str:
        if self.trap is not None:
            return self.trap.stderr
        return self.execution.stderr

    @property
    def exit_code(self) -> int | None:
        """The code the program passed to ``IO.exit``, if it called it."""
        return self.execution.exit_code if self.trap is None else None

    @property
    def returncode(self) -> int:
        """The status ``vera run`` exits with after this execution."""
        if self._execution is None:
            return 1
        return self._execution.exit_code or 0

    @property
    def diagnostics(self) -> tuple[Diagnostic, ...]:
        """The compile's diagnostics (the trap is :attr:`trap`)."""
        if self.compiled is not None:
            return self.compiled.diagnostics
        return tuple(self.module.diagnostics) if self.module is not None else ()

    def envelope(self) -> dict[str, Any]:
        """What ``vera run --json`` prints for a program it runs.

        The compile's refusal, the completed call, or the trap.  ``vera
        run``'s refusals of an entry it will not call are the CLI's own, and
        :func:`cli` reports them.
        """
        label = self.compiled.parsed.file if self.compiled is not None else None
        if self.module is None:
            return {"ok": False, "file": label,
                    "diagnostics": [d.to_dict() for d in self._refusal()]}
        module = self.module
        notes = [d.to_dict() for d in module.diagnostics
                 if d.severity == "warning"]
        if self.trap is not None:
            trap = self.trap
            envelope: dict[str, Any] = {
                "ok": False, "file": label,
                "diagnostics": [{
                    "severity": "error",
                    "description": str(trap),
                    "trap_kind": trap.kind,
                    "location": {"line": 0, "column": 0},
                    "frames": [f.to_dict() for f in trap.frames],
                    "fix": trap.fix,
                }],
            }
            if trap.stdout:
                envelope["stdout"] = trap.stdout
            if trap.stderr:
                envelope["stderr"] = trap.stderr
            return envelope
        execution = self.execution
        envelope = {
            "ok": True, "file": label,
            "function": self.fn or (
                "main" if "main" in module.exports
                else module.exports[0] if module.exports else None),
            "value": execution.value,
            "stdout": execution.stdout,
        }
        if execution.stderr:
            envelope["stderr"] = execution.stderr
        if execution.exit_code is not None:
            envelope["exit_code"] = execution.exit_code
        if notes:
            envelope["warnings"] = notes
        return envelope


def run(
    target: Source | Compiled | CompileResult,
    fn: str | None = None,
    args: Sequence[int | float] | None = None,
    *,
    file: str | None = None,
    root: Path | None = None,
    modules: Sequence[ResolvedModule] | None = None,
    checked: bool = True,
    raw_args: list[str] | None = None,
    initial_state: dict[str, int | float] | None = None,
    stdin: str | None = None,
    cli_args: list[str] | None = None,
    env_vars: dict[str, str] | None = None,
    capture_stderr: bool = True,
    tee_stdout: bool = False,
    http_request: HttpRequestData | None = None,
) -> Ran:
    """Compile *target* (unless it is compiled already) and call *fn*.

    *target* is source text, a path, or a module :func:`compile` (or
    ``vera.codegen.compile``) built.  The keyword arguments after *checked*
    are :func:`vera.codegen.execute`'s own.  ``capture_stderr`` is on, as
    ``vera run`` has it, so a program's ``IO.stderr`` is the result's
    :attr:`Ran.stderr`; off, it reaches ``sys.stderr`` as it is written.
    """
    compiled: Compiled | None
    if isinstance(target, Compiled):
        compiled, module = target, target._result
    elif isinstance(target, CompileResult):
        compiled, module = None, target
    else:
        compiled = compile(target, file=file, root=root, modules=modules,
                           checked=checked)
        module = compiled._result
    if compiled is not None and not compiled.ok:
        return Ran(compiled, None, fn, None, None)
    assert module is not None
    try:
        execution = execute(
            module, fn_name=fn, args=list(args) if args is not None else None,
            raw_args=raw_args, initial_state=initial_state, stdin=stdin,
            cli_args=cli_args, env_vars=env_vars,
            capture_stderr=capture_stderr, tee_stdout=tee_stdout,
            http_request=http_request,
        )
    except WasmTrapError as trap:
        return Ran(compiled, module, fn, None, trap)
    return Ran(compiled, module, fn, execution, None)


# =====================================================================
# contract_test
# =====================================================================


@dataclass(frozen=True)
class Tested:
    """``check``, then contract-driven testing when the check passed."""

    checked: Checked
    _result: TestResult | None

    @property
    def result(self) -> TestResult:
        """The tester's result; raises what stopped the check, if it did."""
        if self._result is None:
            _raise_front_end_error(self.checked.parsed)
            raise StageFailed(
                "testing did not run: the check reported "
                + _describe(self.checked.errors))
        return self._result

    @property
    def diagnostics(self) -> tuple[Diagnostic, ...]:
        """The check's diagnostics, then the tester's."""
        own = tuple(self._result.diagnostics) if self._result is not None else ()
        return self.checked.diagnostics + own

    @property
    def errors(self) -> tuple[Diagnostic, ...]:
        return _errors(self.diagnostics)

    @property
    def ok(self) -> bool:
        """The ``ok`` of ``vera test --json``: nothing failed or was refuted,
        and no error was reported."""
        if self._result is None:
            return False
        summary = self._result.summary
        return not (summary.failed or summary.refuted or self.errors)


def contract_test(
    source: Source,
    *,
    file: str | None = None,
    root: Path | None = None,
    modules: Sequence[ResolvedModule] | None = None,
    trials: int = 100,
    fn: str | None = None,
    distrust: bool = False,
) -> Tested:
    """Check *source*, then test its contracts, as ``vera test`` does.

    Testing runs only on a program the check accepts, with the checker's
    tables for the program and each module it imports.  *distrust* also runs
    the functions the verifier proved (``vera test --distrust``).
    """
    checked = check(
        source, file=file, root=root, modules=modules,
        collect_module_artifacts=True,
    )
    if not checked.ok:
        return Tested(checked, None)
    artifacts = checked.artifacts
    result = _test_program(
        checked.program, source=checked.source, file=checked.file,
        trials=trials, fn_name=fn, resolved_modules=checked.resolved,
        expr_semantic_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
        alias_env=artifacts.alias_env, distrust=distrust,
    )
    return Tested(checked, result)


# =====================================================================
# The CLI, in process
# =====================================================================


@dataclass(frozen=True)
class CliResult:
    """One ``vera`` command's exit status and output.

    The attribute names are ``subprocess.CompletedProcess``'s, so a test
    that ran the CLI as a process reads this the same way.
    """

    args: tuple[str, ...]
    returncode: int
    stdout: str
    stderr: str

    def json(self) -> Any:
        """The command's ``--json`` output, parsed."""
        return json.loads(self.stdout)


@contextlib.contextmanager
def _environment(changes: Mapping[str, str | None]) -> Iterator[None]:
    saved = {name: os.environ.get(name) for name in changes}
    try:
        for name, value in changes.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value
        yield
    finally:
        for name, value in saved.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value


def _exit_status(code: object) -> int:
    if code is None:
        return 0
    if isinstance(code, int):
        return code
    print(code, file=sys.stderr)
    return 1


def cli(
    *args: str | os.PathLike[str],
    stdin: str = "",
    env: Mapping[str, str | None] | None = None,
) -> CliResult:
    """Run ``vera <args>`` through ``vera.cli.main``, in process.

    ``sys.argv``, ``sys.stdin``, ``sys.stdout`` and ``sys.stderr`` are the
    command's for the call and restored after it, and so is each variable
    *env* names (a value of ``None`` unsets it).  The command reads *stdin*,
    which is empty unless given.  Its exit status is the code it exits with.
    """
    from vera.cli import main

    argv = ["vera", *(os.fspath(a) for a in args)]
    out, err = io.StringIO(), io.StringIO()
    saved_argv, saved_stdin = sys.argv, sys.stdin
    status = 0
    with contextlib.ExitStack() as stack:
        stack.enter_context(_environment(env or {}))
        stack.enter_context(contextlib.redirect_stdout(out))
        stack.enter_context(contextlib.redirect_stderr(err))
        sys.argv, sys.stdin = argv, io.StringIO(stdin)
        try:
            main()
        except SystemExit as exc:
            status = _exit_status(exc.code)
        finally:
            sys.argv, sys.stdin = saved_argv, saved_stdin
    return CliResult(tuple(argv[1:]), status, out.getvalue(), err.getvalue())


# =====================================================================
# Programs on disk
# =====================================================================


def write_tree(
    root: Path, files: Mapping[str, str], entry: str = "main.vera",
) -> Path:
    """Write *files* (name to source) under *root* and return the entry's path.

    The program a stage resolves imports for is handed over by path, so its
    modules have to exist; this writes them, as UTF-8.
    """
    for name, text in files.items():
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")
    return root / entry
