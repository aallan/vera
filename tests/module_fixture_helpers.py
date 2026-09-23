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
program the CHECKER refuses: it shares the resolve-and-check front half
(``_resolve_and_check``) and then compiles anyway, so a codegen rail that
now sits behind an earlier refusal is still driven and still asserted.
"""
from __future__ import annotations

import tempfile
from pathlib import Path

import wasmtime

from vera import ast
from vera.checker import typecheck_with_artifacts
from vera.checker.core import CheckArtifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import CompileResult
from vera.parser import parse_file, parse_to_ast
from vera.resolver import ModuleResolver, ResolvedModule
from vera.runtime.traps import WasmTrapError
from vera.transform import transform
from vera.verifier import verify


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
            program=transform(parse_file(fp)),
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
        program=parse_to_ast(source),
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
    CODE.  ``_emit_collision_error`` renders E608, E609 and E610 from one
    format string, so a description-substring match cannot tell a function
    collision from an ADT one.

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
    program, source, main_path, resolved, arts, check_errors = (
        _resolve_and_check(tmp_path, files, main_name)
    )
    assert not check_errors, (
        f"typecheck errors: {[d for _, d in check_errors]}"
    )
    # With the checker's tables, each module's own included, as `vera verify`
    # hands them over (#1509).
    vres = verify(program, source, file=str(main_path),
                  resolved_modules=resolved,
                  expr_types=arts.expr_semantic_types,
                  expr_target_types=arts.expr_target_types,
                  module_artifacts=arts.module_artifacts)
    verify_errors = [
        (d.error_code, d.description)
        for d in vres.diagnostics if d.severity == "error"
    ]
    result, cg_errors = _compile_resolved(
        program, source, main_path, resolved, arts,
    )
    return verify_errors, result, cg_errors


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
    CHECKER now refuses, whose codegen rail must still be shown refusing it
    too.  Once #1304 moved the two-supplier refusal to the checker, no
    check-green program reaches E608's ambiguity condition any more, and a
    rail nothing exercises is a rail that can rot into a relaxation nobody
    measures — so the shape is driven through both doors and asserted at
    both, rather than at whichever one happens to answer first.

    Verification is skipped: the program is already rejected, so a verify
    verdict over it would describe a program the toolchain will not build.
    """
    program, source, main_path, resolved, arts, check_errors = (
        _resolve_and_check(tmp_path, files, main_name)
    )
    assert check_errors, (
        "expected the checker to refuse this program; it was accepted"
    )
    result, cg_errors = _compile_resolved(
        program, source, main_path, resolved, arts,
    )
    return check_errors, result, cg_errors


def _resolve_and_check(
    tmp_path: Path, files: dict[str, str], main_name: str,
) -> tuple[
    ast.Program, str, Path, list[ResolvedModule], CheckArtifacts,
    list[tuple[str, str]],
]:
    """Write *files*, resolve *main_name*'s imports, and type-check it.

    The front half both public builders share (see their docstrings for the
    difference).  Returns the pieces codegen needs plus the check errors as
    ``(error_code, description)`` pairs, and decides nothing about them.
    """
    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, src in files.items():
        (tmp_path / name).write_text(src, encoding="utf-8")
    main_path = tmp_path / main_name
    source = files[main_name]
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(program, main_path)
    # Resolution failures are RECORDED, not raised: `resolve_imports` appends
    # E011/E012 to `resolver.errors` and returns whatever it did resolve.  An
    # unresolved module therefore drops out silently, and a cell whose
    # expected answer is the effect operation — most of the matrix — still
    # gets that answer and passes while measuring nothing.  Measured: with
    # `lib.vera` written as `liib.vera`, the private-wildcard cell returns
    # 42007 and every stage reports zero errors.
    #
    # Raised here for BOTH builders, unlike the type-check errors: no caller
    # of either expects a resolution error, so one means the FIXTURE is
    # broken, not the compiler — and returning it would let a cell pass with
    # nothing assembled.
    resolve_errors = [d.description for d in resolver.errors]
    assert not resolve_errors, f"module resolution errors: {resolve_errors}"
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(main_path), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    check_errors = [
        (d.error_code, d.description)
        for d in diags if d.severity == "error"
    ]
    return program, source, main_path, resolved, arts, check_errors


def _compile_resolved(
    program: ast.Program, source: str, main_path: Path,
    resolved: list[ResolvedModule], arts: CheckArtifacts,
) -> tuple[CompileResult, list[tuple[str, str]]]:
    """Compile a resolved program, returning it beside its codegen errors."""
    result = codegen_compile(
        program, source=source, file=str(main_path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
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
        return "ok", execute(result, fn_name=fn).value
    except (WasmTrapError, wasmtime.WasmtimeError, wasmtime.Trap) as exc:
        return "trap", str(exc)
