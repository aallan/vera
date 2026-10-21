"""Shared builders for multi-module test fixtures (#1228).

Six test files carried independent copies of the same two patterns for
turning a source string into a :class:`~vera.resolver.ResolvedModule`.
They are two patterns, not one, and what separates them is PARSE
PROVENANCE — not whether a file survives the call, because neither
leaves one:

``resolved_module`` — writes the source to a real temporary file, parses
THAT (:func:`~vera.parser.parse_file`), and deletes the file before
returning.  The module carries real-file provenance: its program came
through the on-disk parse path, and ``file_path`` is a well-formed
absolute path of the shape the pipeline sees in production.

``fake_resolved_module`` — parses the source in memory
(:func:`~vera.parser.parse_to_ast`) and labels the module
``/fake/<path>.vera``.  Cheaper, and correct wherever the parse path
does not matter; the label is conspicuously synthetic, so a path that
turns up in a failure message is recognisable as a fixture's rather than
a real module's.

**Neither builder leaves a file on disk, and neither ``file_path`` can
be opened after the call returns.**  That is safe because nothing
downstream re-reads it: ``compile()`` and the checker work off the
parsed program and the in-memory ``source`` string and keep the path
only as a diagnostic label (PR #664 review — the one ``read_text`` under
``vera/codegen/`` is the ``IO.read_file`` HOST binding, which reads
whatever path the compiled program asks for at run time, not the
module's).  A test that needs a module file to EXIST while it runs must
therefore write one itself; these builders will not provide it.
:func:`test_neither_builder_leaves_a_file_behind` pins the contract.

Both are Windows-portable, per the rules in TESTING.md's "Test Fixture
Conventions": ``delete=False`` plus a manual unlink (Windows cannot
reopen a held ``NamedTemporaryFile``), explicit ``encoding="utf-8"``,
and — for callers embedding a fixture path into Vera source —
POSIX-form paths via ``Path.as_posix()``.

One of the consolidated copies did not unlink at all, and leaked one
temp file per fixture it built.

Beside the two ``ResolvedModule`` builders sits the WHOLE-PIPELINE pair
:func:`build_multi_module` and :func:`module_value` (#1299): write a set
of ``.vera`` files into a directory, resolve / check / verify / compile
the entry exactly as ``vera run`` does, and then execute an export.  They
exist because a cross-module namespace bug is only visible as a
DIFFERENTIAL — the verify verdict beside the runtime value, asserted in
one place — and a test that stops at ``compile`` cannot see the half of
the defect that lands at run.  Both #1274's and #1299's matrices drive
them, so the two issues' cells can never be built against subtly
different pipelines.

:func:`build_multi_module_past_check` (#1304) is the same pipeline for a
program the CHECKER refuses: it compiles anyway, with the tables that check
collected (``tests/pipeline.py``'s ``compile(..., past_check=True)``), so a
codegen rail that now sits behind an earlier refusal is still driven and
still asserted.

:func:`check_multi_module` and :func:`verify_multi_module` stop earlier
and return more: every check diagnostic, warnings and locations included,
and the verify result with its obligations — what a test comparing two
programs phase by phase needs, through the same resolution and the same
verify wiring as the builders.

Every builder here drives ``tests/pipeline.py``: the entry is written with
its modules and handed to the pipeline's stages by path, so its imports
resolve from *tmp_path* exactly as ``vera run`` resolves them.
"""
from __future__ import annotations

import tempfile
from pathlib import Path

import wasmtime

from tests import pipeline
from vera import ast
from vera.checker.core import CheckArtifacts
from vera.codegen.api import CompileResult
from vera.errors import Diagnostic
from vera.resolver import ResolvedModule
from vera.verifier import VerifyResult


def resolved_module(path: tuple[str, ...], source: str) -> ResolvedModule:
    """A ``ResolvedModule`` parsed from a real (temporary) file.

    The file exists for the parse and is deleted before this returns, so
    ``file_path`` names a path that is no longer there.  What the module
    keeps is the PROVENANCE — a program that came through the on-disk
    parse path, under a realistic absolute path — which is all any
    consumer needs, since none of them reopens it (see the module
    docstring).
    """
    # Creation, then ONE cleanup site covering every path.  Two rules
    # meet here and the obvious arrangement satisfies only one of them:
    # the file must be removed even if the WRITE fails (`delete=False`
    # means it outlives the context manager), and on Windows it cannot
    # be removed while the handle is open at all — an unlink in an
    # `except` inside the `with` is WinError 32 there, which is
    # TESTING.md's first fixture rule (PR #1282 review, and its own CI).
    # So the name is captured and the `try` entered before anything that
    # can fail, the `with` closes the handle on its way out however it
    # leaves, and the `finally` unlinks after it — never during.
    tmp = tempfile.NamedTemporaryFile(  # noqa: SIM115 — closed by the `with`
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    )
    fp = tmp.name
    try:
        with tmp as f:
            f.write(source)
            f.flush()
        return ResolvedModule(
            path=path,
            file_path=Path(fp),
            program=pipeline.parse(Path(fp)).program,
            source=source,
        )
    finally:
        Path(fp).unlink(missing_ok=True)


def fake_resolved_module(
    path: tuple[str, ...], source: str,
) -> ResolvedModule:
    """A ``ResolvedModule`` parsed in memory, labelled with a fake path.

    For tests where the parse path does not matter.  The label is
    ``/fake/<dotted/path>.vera`` — conspicuously synthetic, so a path
    appearing in a failure message is recognisable as a fixture's.  Like
    :func:`resolved_module` it leaves nothing on disk; the difference
    between them is where the program was parsed from, not whether the
    file survives.
    """
    return ResolvedModule(
        path=path,
        file_path=Path(f"/fake/{'/'.join(path)}.vera"),
        program=pipeline.parse(source).program,
        source=source,
    )


def build_multi_module(
    tmp_path: Path, files: dict[str, str],
    main_name: str = "main.vera",
) -> tuple[
    list[tuple[str, str]], CompileResult, list[tuple[str, str]],
]:
    """Resolve + check + verify + compile *main_name* as ``vera run`` does.

    Returns ``(verify_errors, compile_result, codegen_errors)`` — the two
    diagnostic streams a cross-module namespace defect can land in, kept
    separate so a caller can assert them independently and, more
    importantly, assert them TOGETHER with the runtime value from
    :func:`module_value`.  A clean verify beside a wrong (or absent)
    answer is exactly the false Tier-1 shape these matrices hunt, and it
    is invisible to any test that inspects one side alone.

    Each error is an ``(error_code, description)`` pair rather than a bare
    description, so a caller pinning a specific diagnostic matches on the
    CODE, which the description never contains.

    Resolution and type-check errors RAISE instead of being returned: every
    caller's fixture is well-formed and check-green by construction, so
    either means the FIXTURE is broken, not the compiler — and returning
    them would let a matrix cell pass vacuously with nothing assembled.

    Resolution goes through the real :class:`~vera.resolver.ModuleResolver`
    rooted at *tmp_path*, so each module's ``direct`` flag is the
    production one (a transitive-only module is marked as such) rather
    than a hand-built fixture's default.

    Shares its resolve-and-check front half with
    :func:`build_multi_module_past_check`, which keeps going where this one
    raises; the two differ only in what they do about a rejected program, so
    a codegen rail measured through one is measured against the same
    resolution and the same artifacts as through the other.
    """
    entry = pipeline.write_tree(tmp_path, files, main_name)
    verified = pipeline.verify(entry, root=tmp_path)
    check_errors = _check_errors(verified.checked)
    assert not check_errors, (
        f"typecheck errors: {[d for _, d in check_errors]}"
    )
    verify_errors = [
        (d.error_code, d.description)
        for d in verified.result.diagnostics if d.severity == "error"
    ]
    result, cg_errors = _compiled(pipeline.compile(entry, root=tmp_path))
    return verify_errors, result, cg_errors


def compile_multi_module(
    tmp_path: Path, files: dict[str, str],
    main_name: str = "main.vera",
) -> CompileResult:
    """Resolve + check + compile *main_name* as ``vera compile`` does, and
    return the module, its own diagnostics unasserted.  Resolution and
    type-check errors raise, as for :func:`build_multi_module`."""
    compiled = pipeline.compile(
        pipeline.write_tree(tmp_path, files, main_name), root=tmp_path)
    assert compiled.checked is not None
    check_errors = _check_errors(compiled.checked)
    assert not check_errors, (
        f"typecheck errors: {[d for _, d in check_errors]}"
    )
    return compiled.result


def compile_multi_module_ok(
    tmp_path: Path, files: dict[str, str],
    main_name: str = "main.vera",
) -> CompileResult:
    """:func:`compile_multi_module`, asserting code generation reports no
    error."""
    result = compile_multi_module(tmp_path, files, main_name)
    errs = [d for d in result.diagnostics if d.severity == "error"]
    assert not errs, f"codegen errors: {[d.description for d in errs]}"
    return result


def check_multi_module(
    tmp_path: Path, files: dict[str, str],
    main_name: str = "main.vera",
) -> list[Diagnostic]:
    """Every diagnostic the checker gives *main_name*, its imports resolved
    as ``vera check`` resolves them: warnings included, and errors returned
    rather than raised, for a test about what the checker reports."""
    checked = pipeline.check(
        pipeline.write_tree(tmp_path, files, main_name), root=tmp_path,
        collect_module_artifacts=True,
    )
    _assert_resolved(checked)
    return list(checked.checker_diagnostics)


def verify_multi_module(
    tmp_path: Path, files: dict[str, str],
    main_name: str = "main.vera",
) -> tuple[list[Diagnostic], VerifyResult]:
    """Check and verify *main_name* as ``vera verify`` does: every check
    diagnostic, and the verify result with its obligations, which
    :func:`build_multi_module` reduces to the verifier's errors.  The
    obligations include the imported modules' own, as ``vera verify``
    reports them.

    Check-clean is the premise, as for a single file: verification of an
    ill-typed program describes nothing (``tests/verifier_helpers.py``)."""
    verified = pipeline.verify(
        pipeline.write_tree(tmp_path, files, main_name), root=tmp_path)
    checked = verified.checked
    _assert_resolved(checked)
    check_errors = checked.errors
    assert not check_errors, (
        f"typecheck errors: {[d.description for d in check_errors]}"
    )
    return list(checked.checker_diagnostics), verified.result


def build_multi_module_past_check(
    tmp_path: Path, files: dict[str, str],
    main_name: str = "main.vera",
) -> tuple[
    list[tuple[str, str]], CompileResult, list[tuple[str, str]],
]:
    """Resolve + check + compile, CONTINUING past a rejected check (#1304).

    Returns ``(check_errors, compile_result, codegen_errors)``.

    :func:`build_multi_module` raises on a check error because every one of
    its callers builds a check-green fixture, so an error there means the
    fixture is broken.  This one exists for the opposite case: a shape the
    CHECKER refuses, whose compile is still measured — what code generation
    does with a program the check refused (it refuses a call bound to
    nothing, spec §8.9.3) — so the shape is driven through both doors and
    asserted at both, rather than at whichever one happens to answer first.

    Verification is skipped: the program is already rejected, so a verify
    verdict over it would describe a program the toolchain will not build.
    """
    compiled = pipeline.compile(
        pipeline.write_tree(tmp_path, files, main_name), root=tmp_path,
        past_check=True,
    )
    assert compiled.checked is not None
    check_errors = _check_errors(compiled.checked)
    assert check_errors, (
        "expected the checker to refuse this program; it was accepted"
    )
    result, cg_errors = _compiled(compiled)
    return check_errors, result, cg_errors


def _resolve_and_check(
    tmp_path: Path, files: dict[str, str], main_name: str,
) -> tuple[
    ast.Program, str, Path, list[ResolvedModule], CheckArtifacts,
    list[tuple[str, str]],
]:
    """Write *files*, resolve *main_name*'s imports, and type-check it.

    Returns the pieces codegen needs plus the check errors as
    ``(error_code, description)`` pairs, and decides nothing about them.
    """
    entry = pipeline.write_tree(tmp_path, files, main_name)
    checked = pipeline.check(entry, root=tmp_path, collect_module_artifacts=True)
    check_errors = _check_errors(checked)
    return (
        checked.program, checked.source, entry, checked.resolved or [],
        checked.artifacts, check_errors,
    )


def _assert_resolved(checked: pipeline.Checked) -> None:
    """Raise the parse error, or fail on a resolution error, for a fixture.

    Resolution failures are RECORDED, not raised: `resolve_imports` appends
    E011/E012 to `resolver.errors` and returns whatever it did resolve.  An
    unresolved module therefore drops out silently, and a cell whose
    expected answer is the effect operation — most of the matrix — still
    gets that answer and passes while measuring nothing.  Measured: with
    `lib.vera` written as `liib.vera`, the private-wildcard cell returns
    42007 and every stage reports zero errors.

    Asserted here for every builder, unlike the type-check errors: no caller
    of any expects a resolution error, so one means the FIXTURE is
    broken, not the compiler — and returning it would let a cell pass with
    nothing assembled.
    """
    _ = checked.program  # raises the parse or transform error, if any
    resolve_errors = [d.description for d in checked.resolution_diagnostics]
    assert not resolve_errors, f"module resolution errors: {resolve_errors}"


def _check_errors(checked: pipeline.Checked) -> list[tuple[str, str]]:
    """The check's errors as ``(error_code, description)`` pairs, once the
    fixture is known to have resolved."""
    _assert_resolved(checked)
    return [(d.error_code, d.description) for d in checked.errors]


def _compiled(
    compiled: pipeline.Compiled,
) -> tuple[CompileResult, list[tuple[str, str]]]:
    """A compile's module beside its codegen errors."""
    result = compiled.result
    cg_errors = [
        (d.error_code, d.description)
        for d in result.diagnostics if d.severity == "error"
    ]
    return result, cg_errors


def module_value(
    result: CompileResult, fn: str = "main",
) -> tuple[str, object]:
    """``("ok", value)`` or ``("trap", message)`` for one export.

    A namespace defect surfaces in BOTH shapes — a wrong-but-loadable
    value where the colliding cells happen to share a WAT type, and a
    load failure where they do not — so the two are returned as one
    tagged pair rather than one being raised past the assertion.  A cell
    that only ever asserts "no trap" would go green on the silent-wrong
    answer, which is the more dangerous half.
    """
    try:
        ran = pipeline.run(result, fn, capture_stderr=False)
    except (wasmtime.WasmtimeError, wasmtime.Trap) as exc:
        return "trap", str(exc)
    if ran.trap is not None:
        return "trap", str(ran.trap)
    return "ok", ran.value
