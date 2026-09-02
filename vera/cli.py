"""Vera command-line interface.

Usage:
    vera parse     <file.vera>              Parse a file and print the tree
    vera check     <file.vera>              Parse and type-check a file
    vera check     --json <file.vera>       Type-check and output JSON diagnostics
    vera check     --explain-slots <file>   Show slot resolution table (@T.n → parameter)
    vera typecheck <file.vera>              Same as check (explicit alias)
    vera verify    <file.vera>              Type-check and verify contracts
    vera verify    --json <file.vera>       Verify and output JSON diagnostics
    vera compile   <file.vera>              Compile to .wasm binary
    vera compile   --wat <file.vera>        Print WAT text to stdout
    vera compile   -o out.wasm <file.vera>  Specify output path
    vera compile   --target browser <file>  Emit browser bundle (wasm + JS + HTML)
    vera compile   --target wasi-p2 <file>  Emit WASI Preview 2 component (experimental)
    vera compile   --target wasi-p2 --world server <file>  Emit wasi:http server component (wasmtime serve)
    vera run       <file.vera>              Compile and execute
    vera run       --fn name <file.vera>    Execute a specific function
    vera run       <file.vera> -- 5 10      Pass arguments to the function
    vera run       --target wasi-p2 <file>  Execute under the built-in WASI 0.2 host
    vera ast       <file.vera>              Parse and print the AST
    vera ast       --json <file.vera>       Parse and print the AST as JSON
    vera test      <file.vera>              Test contracts via Z3-guided inputs
    vera test      --json <file.vera>       Test with JSON output
    vera test      --trials 50 <file.vera>  Set trial count (default 100)
    vera verify    --timeout-ms N <file.vera>  Per-query Z3 budget in ms
                                            (default 10000; also
                                            VERA_Z3_TIMEOUT_MS)
    vera test      --fn name <file.vera>    Test a specific function
    vera serve     <file.vera>              Serve handle(Request -> Response) over HTTP
    vera serve     --port 8080 <file.vera>  Serve on a specific port (default 8000)
    vera fmt       <file.vera>              Format to canonical form (stdout)
    vera fmt       --write <file.vera>      Format in place
    vera fmt       --check <file.vera>      Check if already canonical
    vera builtins  [--json]                 List the built-in function registry
    vera effects   [--json]                 List the effect and ability registry
    vera errors    [--json]                 List the diagnostic error-code registry
    vera lsp                                Serve the LSP over stdio (needs [lsp] extra)
    vera version                            Print the installed version
    vera --version                          Same as vera version
    vera -V                                 Same as vera version
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import cast

from lark import Tree
from vera.codegen.api import WasmTrapError
from vera.errors import Diagnostic, SourceLocation, VeraError
from vera.introspect import builtins_payload, effects_payload, errors_payload
from vera.parser import parse
from vera.transform import transform


def _is_int_str(s: str) -> bool:
    """Return True if *s* can be parsed as a Python int literal."""
    try:
        int(s)
        return True
    except ValueError:
        return False


_STDIN_PATHS: frozenset[str] = frozenset({"-", "/dev/stdin"})


def _load_and_parse(path: str) -> tuple[Path, str, Tree[object]]:
    """Read *path* once and return (logical_path, source, parse_tree).

    Using this helper avoids the double-read bug (#335): each caller used
    to call p.read_text() for the source string and then parse_file(path)
    which re-opened the same path.  For non-seekable inputs such as
    /dev/stdin the second open returns empty content.

    For stdin paths ("-" or "/dev/stdin") the source is read directly
    from ``sys.stdin`` and the returned logical path is
    ``Path.cwd() / "stdin.vera"`` rather than the raw special-file path.
    Reading ``sys.stdin`` directly (rather than ``Path("/dev/stdin")
    .read_text()``) is portable across Unix and Windows — Windows
    doesn't have a ``/dev/stdin`` filesystem entry, so the path-based
    read raised ``FileNotFoundError`` there pre-#640.  The CWD-relative
    logical path ensures callers use CWD for module resolution
    (ModuleResolver _root) and produce sensible default output names
    (stdin.wasm) rather than erroneously resolving imports under
    ``/dev/`` or writing output to ``/dev/stdin.wasm``.  Diagnostics
    still reference the original *path* string for readable error
    locations.
    """
    if path in _STDIN_PATHS:
        source = sys.stdin.read()
        p = Path.cwd() / "stdin.vera"
    else:
        raw_p = Path(path)
        source = raw_p.read_text(encoding="utf-8")
        p = raw_p
    tree = parse(source, file=path)
    return p, source, tree


def cmd_parse(path: str) -> int:
    """Parse a .vera file and print the parse tree."""
    try:
        _p, _source, tree = _load_and_parse(path)
        print(tree.pretty())
        return 0
    except FileNotFoundError:
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1


def cmd_check(
    path: str,
    as_json: bool = False,
    quiet: bool = False,
    explain_slots: bool = False,
) -> int:
    """Parse, transform, and type-check a .vera file."""
    try:
        # INSIDE the try, as in `cmd_verify`: a function-scope import that fails
        # (a broken `z3` wheel reached through `vera.checker`) must become an
        # envelope, not a raw traceback past the backstop (#1361 review).
        from vera.ast import FnDecl, format_type_expr
        from vera.checker import typecheck
        from vera.checker.core import typecheck_with_artifacts
        from vera.resolver import ModuleResolver
        from vera.slots import (
            fn_scopes,
            format_slot_table,
            slot_table,
            slot_table_dict,
        )

        p, source, tree = _load_and_parse(path)
        program = transform(tree)


        # Resolve imports (C7a)
        resolver = ModuleResolver(_root=p.parent)
        resolved = resolver.resolve_imports(program, p)
        resolve_diags = resolver.errors

        if explain_slots:
            # #1208: the slot table is a NAMING question, so it is answered
            # against the checker's own alias table
            # (``CheckArtifacts.alias_env``) rather than a syntactic rebuild.
            # Only this flag pays for the artifact-collecting check; a plain
            # ``vera check`` keeps the cheaper entry point, and the
            # diagnostics are the same list either way.
            check_diags, artifacts = typecheck_with_artifacts(
                program, source, file=str(p), resolved_modules=resolved,
            )
        else:
            check_diags = typecheck(
                program, source, file=str(p), resolved_modules=resolved,
            )
        diagnostics = resolve_diags + check_diags

        errors = [d for d in diagnostics if d.severity == "error"]
        warnings = [d for d in diagnostics if d.severity == "warning"]

        # Build slot environment tables (only on success)
        slot_sections: list[str] = []
        slot_json: list[dict[str, object]] = []
        if explain_slots and not errors:
            for top in program.declarations:
                if not isinstance(top.decl, FnDecl):
                    continue
                # Every function, `where`-block helpers included (#1217): a
                # helper resets the slot namespace, so its De Bruijn ordering
                # is its own question and the parent's table answers none of
                # it.  `fn_scopes` pairs each with the type parameters in
                # scope OVER it — the parent's `forall` variables reach the
                # helper, and they shadow same-named module aliases there too.
                blocks: list[str] = []
                for decl, in_scope, name_path in fn_scopes(top.decl):
                    # The ENTRY module's env (these are its own top-level
                    # declarations), plus the type parameters in scope —
                    # which shadow same-named module aliases, exactly as they
                    # do for the checker that bound these slots.
                    table = slot_table(
                        decl.params, artifacts.alias_env, in_scope,
                    )
                    params_str = (
                        ", ".join(format_type_expr(te) for te in decl.params)
                        + " -> "
                        + format_type_expr(decl.return_type)
                    )
                    if as_json:
                        slot_json.append(
                            slot_table_dict(".".join(name_path), table))
                    else:
                        blocks.append(format_slot_table(
                            decl.name, params_str, table,
                            len(name_path) - 1,
                        ))
                # One section per TOP-LEVEL function: its helpers belong to
                # it, so they print inside its block rather than as peers
                # separated by a blank line.
                if blocks:
                    slot_sections.append("\n".join(blocks))

        if as_json:
            result: dict[str, object] = {
                "ok": len(errors) == 0,
                "file": path,
                "diagnostics": [e.to_dict() for e in errors],
                "warnings": [w.to_dict() for w in warnings],
            }
            if explain_slots:
                result["slot_environments"] = slot_json  # [] on error
            print(json.dumps(result, indent=2))
            return 1 if errors else 0

        for w in warnings:
            print(f"warning: {w.format()}", file=sys.stderr)

        if errors:
            for e in errors:
                print(e.format(), file=sys.stderr)
            return 1

        if not quiet:
            print(f"OK: {path}")

        if slot_sections:
            print()
            print("Slot environments (index 0 = last occurrence in signature):")
            print()
            for section in slot_sections:
                print(section)
                print()

        return 0
    except FileNotFoundError:
        # The sibling handlers are inside the backstop's reach too (#1361
        # review): their own `print` / `json.dumps` / `to_dict` can raise, and an
        # unenveloped handler failing mid-report is the same empty stdout as no
        # handler at all.
        try:
            if as_json:
                err_result: dict[str, object] = {
                    "ok": False, "file": path,
                    "diagnostics": [{"severity": "error",
                                     "description": f"file not found: {path}",
                                     "location": {"line": 0, "column": 0}}],
                    "warnings": [],
                }
                if explain_slots:
                    err_result["slot_environments"] = []
                print(json.dumps(err_result, indent=2))
                return 1
            print(f"Error: file not found: {path}", file=sys.stderr)
            return 1
        except Exception as inner:  # noqa: BLE001 — envelope backstop
            return _internal_error_envelope(
                path, inner, doing='checking', as_json=as_json)
    except VeraError as exc:
        # The sibling handlers are inside the backstop's reach too (#1361
        # review): their own `print` / `json.dumps` / `to_dict` can raise, and an
        # unenveloped handler failing mid-report is the same empty stdout as no
        # handler at all.
        try:
            if as_json:
                err_result = {
                    "ok": False, "file": path,
                    "diagnostics": [exc.diagnostic.to_dict()],
                    "warnings": [],
                }
                if explain_slots:
                    err_result["slot_environments"] = []
                print(json.dumps(err_result, indent=2))
                return 1
            print(exc.diagnostic.format(), file=sys.stderr)
            return 1
        except Exception as inner:  # noqa: BLE001 — envelope backstop
            return _internal_error_envelope(
                path, inner, doing='checking', as_json=as_json)
    except Exception as exc:  # noqa: BLE001 — envelope backstop (#1360)
        return _internal_error_envelope(
            path, exc, doing="checking", as_json=as_json,
            extra={"slot_environments": []} if explain_slots else None)


def cmd_verify(path: str, as_json: bool = False, quiet: bool = False,
               timeout_ms: int | None = None) -> int:
    """Parse, transform, type-check, and verify a .vera file."""
    try:
        # INSIDE the try (#1361 review): these are function-scope imports, and
        # an import that fails — a broken or missing `z3` wheel is the live
        # case — raises here.  Outside, that raise bypasses the backstop below
        # and produces exactly the empty stdout plus raw traceback the
        # envelope exists to eliminate.
        from vera.checker import typecheck_with_artifacts
        from vera.resolver import ModuleResolver
        from vera.smt import resolve_timeout_ms
        from vera.verifier import verify

        p, source, tree = _load_and_parse(path)
        ast = transform(tree)


        # Resolve imports (C7a)
        resolver = ModuleResolver(_root=p.parent)
        resolved = resolver.resolve_imports(ast, p)

        # First type-check, collecting the #747 semantic-type side-tables
        # so the verifier can obligate projection / generic-instantiation
        # @Nat narrowings.
        check_diags, artifacts = typecheck_with_artifacts(
            ast, source, file=str(p), resolved_modules=resolved,
        )
        type_diags = resolver.errors + check_diags
        type_errors = [d for d in type_diags if d.severity == "error"]
        type_warnings = [d for d in type_diags if d.severity == "warning"]

        if type_errors:
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in type_errors],
                    "warnings": [w.to_dict() for w in type_warnings],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            for e in type_errors:
                print(e.format(), file=sys.stderr)
            return 1

        # Then verify contracts
        result = verify(ast, source, file=str(p),
                        timeout_ms=timeout_ms,
                        resolved_modules=resolved,
                        expr_types=artifacts.expr_semantic_types,
                        expr_target_types=artifacts.expr_target_types)

        errors = [d for d in result.diagnostics if d.severity == "error"]
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        all_warnings = type_warnings + warnings

        if as_json:
            s = result.summary
            result_dict = {
                "ok": len(errors) == 0,
                "file": path,
                "diagnostics": [e.to_dict() for e in errors],
                "warnings": [w.to_dict() for w in all_warnings],
                "verification": {
                    "tier1_verified": s.tier1_verified,
                    "tier3_runtime": s.tier3_runtime,
                    "total": s.total,
                    # #1345: assumptions counted BESIDE the tiers.  Absent
                    # from this object, an `assume` was counted nowhere at
                    # all, so a consumer could not tell a proof from a
                    # promise.
                    "assumptions": s.assumptions,
                    # #1350: the budget these tiers were measured under.  A
                    # tier near the budget is host-sensitive, so a summary
                    # that does not say which budget produced it cannot be
                    # compared against another machine's.
                    "timeout_ms": resolve_timeout_ms(timeout_ms),
                },
                # #967: expose the reified obligation stream the summary is
                # derived from, so a machine consumer can reproduce or refine
                # the tier counts (location mirrors a diagnostic's shape).
                "obligations": [
                    {
                        "kind": o.kind,
                        "status": o.status,
                        "description": o.expr_text,
                        "location": {
                            "line": o.line,
                            "column": o.column,
                            # The obligation's OWN file, so a consumer can
                            # join it to its diagnostic on (file, line,
                            # column) (PR #974 review).  That join assumed
                            # every obligation belonged to the entry program
                            # and stamped `str(p)` on all of them, which was
                            # true only while the verifier reported
                            # everything against the entry buffer; once an
                            # imported generic's clone reports against its
                            # own module (#1220), a stamped entry path both
                            # broke the join and named a line the entry file
                            # does not have.  The verifier normalizes the
                            # path it is handed (`verify(..., file=str(p))`),
                            # so a main-file obligation still carries exactly
                            # the `str(p)` diagnostics carry; the fallback
                            # covers only an obligation reified with no file
                            # at all, which a run given `path` does not
                            # produce.
                            **(
                                {"file": o.file or str(p)}
                                if path else {}
                            ),
                        },
                        **({"error_code": o.error_code} if o.error_code else {}),
                    }
                    for o in result.obligations
                ],
            }
            print(json.dumps(result_dict, indent=2))
            return 1 if errors else 0

        for w in all_warnings:
            print(f"warning: {w.format()}", file=sys.stderr)

        if errors:
            for e in errors:
                print(e.format(), file=sys.stderr)
            return 1

        # Print success with summary
        s = result.summary
        parts = []
        if s.tier1_verified:
            parts.append(f"{s.tier1_verified} verified (Tier 1)")
        if s.tier3_runtime:
            parts.append(f"{s.tier3_runtime} runtime checks (Tier 3)")
        summary_str = ", ".join(parts) if parts else "no contracts"

        if not quiet:
            print(f"OK: {path}")
            print(f"Verification: {summary_str}")
        return 0
    except FileNotFoundError:
        # The sibling handlers are inside the backstop's reach too (#1361
        # review): their own `print`/`json.dumps` can raise — a closed stdout,
        # a diagnostic that will not serialise — and an unenveloped handler
        # failing is the same empty stdout as no handler at all.
        try:
            if as_json:
                print(json.dumps({"ok": False, "file": path,
                                  "diagnostics": [{"severity": "error",
                                                   "description": f"file not found: {path}",
                                                   "location": {"line": 0, "column": 0}}],
                                  "warnings": []}, indent=2))
                return 1
            print(f"Error: file not found: {path}", file=sys.stderr)
            return 1
        except Exception as inner:  # noqa: BLE001 — envelope backstop
            return _internal_error_envelope(
                path, inner, doing="verifying", as_json=as_json)
    except VeraError as exc:
        try:
            if as_json:
                print(json.dumps({"ok": False, "file": path,
                                  "diagnostics": [exc.diagnostic.to_dict()],
                                  "warnings": []}, indent=2))
                return 1
            print(exc.diagnostic.format(), file=sys.stderr)
            return 1
        except Exception as inner:  # noqa: BLE001 — envelope backstop
            return _internal_error_envelope(
                path, inner, doing="verifying", as_json=as_json)
    except Exception as exc:  # noqa: BLE001 — envelope backstop (#1360)
        # Every exit path of `verify --json` emits a parseable envelope.
        # Anything reaching here is a compiler bug rather than a property of
        # the program, but a consumer that gets EMPTY stdout cannot tell a
        # crash from a clean run — it sees no diagnostics either way.  #1360
        # arrived here as a raw `z3.z3types.Z3Exception: Sort mismatch` from
        # the SMT translator; that defect is fixed, and this keeps the NEXT
        # one a diagnostic rather than a traceback.
        return _internal_error_envelope(
            path, exc, doing="verifying", as_json=as_json)

def _internal_error_envelope(
    path: str, exc: BaseException, *, doing: str, as_json: bool,
    extra: dict[str, object] | None = None,
) -> int:
    """Report an exception that escaped a command as an ``E699`` diagnostic.

    The machine-readable contract is that ``--json`` stdout is ALWAYS a
    parseable envelope, so a consumer can tell a crash from a clean run: empty
    stdout looks exactly like "no diagnostics" (#1360).  Anything reaching here
    is a compiler bug rather than a property of the program, which is the E699
    posture `vera/skip.py` documents for codegen invariants, applied at the
    command boundary.

    A real :class:`Diagnostic` rather than a hand-built dict, so the envelope
    carries ``spec_ref`` and the file on its location, and so the text path
    formats identically to every other error the user sees (PR #1361 review).
    ``source_line`` is deliberately absent: an internal error has no source
    POSITION to quote, and `to_dict` omits the key rather than emit an empty
    one — an earlier docstring claimed it, which is the kind of promise a test
    written from the implementation cannot catch.

    *extra* carries a command's own always-present JSON keys.  Only the keys a
    caller would parse unconditionally are wired; the crash envelope
    deliberately omits the per-command RESULT shapes (`verification` /
    `obligations` for verify, the run summary for test) rather than inventing
    zeroed ones, because there is no result to report and a fabricated empty
    summary reads as a successful run of nothing.
    """
    diag = Diagnostic(
        description=(
            f"Internal compiler error while {doing} '{path}': "
            f"{type(exc).__name__}: {exc}"
        ),
        location=SourceLocation(file=path, line=0, column=0),
        source_line="",
        rationale=(
            "The compiler raised an unexpected exception. This is a bug in "
            "the compiler, not a property of the program being processed — "
            "the input may well be valid."
        ),
        fix=(
            "Please file a bug report with the offending program at "
            "https://github.com/aallan/vera/issues"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E699",
    )
    try:
        if as_json:
            payload: dict[str, object] = {
                "ok": False, "file": path,
                "diagnostics": [diag.to_dict()], "warnings": [],
            }
            payload.update(extra or {})
            print(json.dumps(payload, indent=2))
            return 1
        print(diag.format(), file=sys.stderr)
        return 1
    except Exception:  # noqa: BLE001 — last resort (#1361 review)
        # The reporting path is itself the last thing that can fail, and the
        # envelope is worth nothing if the code emitting it can raise.  So this
        # leg builds the JSON by hand from strings that cannot fail to
        # serialise, rather than through `Diagnostic.to_dict` / `.format` — the
        # one place in this module where a dict literal is the RIGHT shape,
        # precisely because it depends on nothing that could be broken.
        if as_json:
            print(
                '{"ok": false, "file": %s, "diagnostics": [{"severity": '
                '"error", "error_code": "E699", "description": %s, '
                '"location": {"line": 0, "column": 0}}], "warnings": []}'
                % (json.dumps(str(path)), json.dumps(
                    f"Internal compiler error while {doing} '{path}': "
                    f"{type(exc).__name__}"))
            )
        else:
            print(
                f"Error: [E699] Internal compiler error while {doing} "
                f"'{path}': {type(exc).__name__}", file=sys.stderr)
        return 1


def _report_compile_failure(
    path: str,
    msg: str,
    all_warnings: list[Diagnostic],
    *,
    as_json: bool,
    extra: dict[str, object] | None = None,
) -> int:
    """Print one synthetic-diagnostic compile failure and return exit 1.

    Shared by the refusal paths that reject AFTER a successful core
    compile (zero exports, browser without ``main``, the wasi-p2 family
    gate), so the JSON/text envelope exists in exactly one place.
    Accumulated warnings are printed on both modes — these paths reject
    after compilation succeeded, so the warnings must not be dropped
    (#1004 review).  ``extra`` merges additional top-level keys into the
    JSON payload between ``file`` and ``diagnostics`` (the zero-export
    caller adds ``"exports": []``).
    """
    if as_json:
        payload: dict[str, object] = {"ok": False, "file": path}
        if extra:
            payload.update(extra)
        payload["diagnostics"] = [{
            "severity": "error",
            "description": msg,
            "location": {"line": 0, "column": 0},
        }]
        payload["warnings"] = [w.to_dict() for w in all_warnings]
        print(json.dumps(payload, indent=2))
        return 1
    for w in all_warnings:
        print(f"warning: {w.format()}", file=sys.stderr)
    print(f"Error: {msg}", file=sys.stderr)
    return 1


def cmd_compile(
    path: str,
    *,
    as_json: bool = False,
    wat: bool = False,
    output: str | None = None,
    target: str = "wasm",
    world: str = "cli",
) -> int:
    """Parse, type-check, and compile a .vera file to WebAssembly."""
    from vera.ast import FnDecl
    from vera.checker import typecheck_with_artifacts
    from vera.codegen import (
        compile as codegen_compile,
        dropped_entry_message,
    )
    from vera.resolver import ModuleResolver

    # Pure flag validation — needs nothing from the program, so it
    # fires before any parse/compile work (CR review, PR #850).
    if world != "cli" and target != "wasi-p2":
        msg = (
            f"--world {world} requires --target wasi-p2 "
            f"(the core and browser targets have no world concept)"
        )
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [{"severity": "error",
                                               "description": msg,
                                               "location": {"line": 0, "column": 0}}],
                              "warnings": []}, indent=2))
            return 1
        print(f"Error: {msg}", file=sys.stderr)
        return 1

    try:
        p, source, tree = _load_and_parse(path)
        ast = transform(tree)


        # Resolve imports (C7a)
        resolver = ModuleResolver(_root=p.parent)
        resolved = resolver.resolve_imports(ast, p)

        # Type-check first, retaining the resolved-type artifacts so the
        # codegen integer-overflow guard (#798) classifies operands in
        # lockstep with the verifier.
        check_diags, artifacts = typecheck_with_artifacts(
            ast, source, file=str(p), resolved_modules=resolved,
            collect_module_artifacts=True,
        )
        type_diags = resolver.errors + check_diags
        type_errors = [d for d in type_diags if d.severity == "error"]
        type_warnings = [d for d in type_diags if d.severity == "warning"]

        if type_errors:
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in type_errors],
                    "warnings": [w.to_dict() for w in type_warnings],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            # Print warnings on the error path too (#1004 review): the text
            # branch must not silently drop type_warnings when a type error is
            # also present, mirroring the codegen-error branch below.  (The JSON
            # branch already includes them.)
            for w in type_warnings:
                print(f"warning: {w.format()}", file=sys.stderr)
            for e in type_errors:
                print(e.format(), file=sys.stderr)
            return 1

        # Compile (C7e: pass resolved modules for cross-module codegen)
        result = codegen_compile(
            ast, source=source, file=str(p), resolved_modules=resolved,
            expr_semantic_types=artifacts.expr_semantic_types,
            expr_target_types=artifacts.expr_target_types,
            module_artifacts=artifacts.module_artifacts,
        )

        errors = [d for d in result.diagnostics if d.severity == "error"]
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        all_warnings = type_warnings + warnings

        if errors:
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in errors],
                    "warnings": [w.to_dict() for w in all_warnings],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            # Print accumulated warnings on the error path too (#1004): a
            # CodegenSkip drops a called function with an explanatory E602
            # "function skipped" warning, then the caller's dangling `call $f`
            # fails WAT assembly with an opaque `unknown func`.  Emitting only
            # the error would leave the user without the reason the function was
            # dropped.  (The JSON branch above already includes `warnings`.)
            for w in all_warnings:
                print(f"warning: {w.format()}", file=sys.stderr)
            for e in errors:
                print(e.format(), file=sys.stderr)
            return 1

        # #1183: a module that declares a public entry point and then
        # exports nothing is a failed compile — the artifact cannot be
        # called at all, and reporting "Compiled: out.wasm (0 functions
        # exported)" over it is a green light on an unusable output.
        #
        # Gated on a public NON-GENERIC declaration existing, because two
        # shapes export nothing by design and must stay successful: a file
        # of private helpers, and a cross-module generic library (a
        # `forall` template has no monomorphic body to export — its
        # importers instantiate it).  The accumulated warnings — the
        # [E602]/[E620] drops, when that is why the exports went away —
        # travel with the failure.
        entry_candidates = [
            tld.decl.name
            for tld in ast.declarations
            if isinstance(tld.decl, FnDecl)
            and tld.visibility == "public"
            and not tld.decl.forall_vars
        ]
        if entry_candidates and not result.exports:
            declared = "".join(f"  - {n}\n" for n in entry_candidates)
            msg = (
                "No exported functions — the compiled module has no entry "
                "points.\n"
                f"\nDeclared public functions:\n{declared}"
                "\nA public function whose body (or a callee's body) could "
                "not be compiled is dropped from the module with a "
                "diagnostic above; fix the reported construct to restore "
                "the export."
            )
            return _report_compile_failure(
                path, msg, all_warnings, as_json=as_json,
                extra={"exports": []},
            )

        # #1183: the browser shell calls `main` unconditionally, so any
        # bundle without a `main` export is a page that fails at load —
        # whether `main` was declared-and-dropped (quote the E620 chain)
        # or never declared at all (PR #1190 review; say what IS exported).
        # Refuse to write it, exactly as `vera run` refuses to run it.
        if target == "browser" and "main" not in result.exports:
            if "main" in result.dropped_fns:
                core = dropped_entry_message("main", result, suggest_fn=False)
            else:
                exports = ", ".join(result.exports) if result.exports else "(none)"
                core = (
                    "no 'main' function is exported, so there is nothing "
                    f"for the page to call.  Exports: {exports}."
                )
            msg = (
                "--target browser: " + core
                + "\n\nThe generated index.html calls main() on load, so "
                "the bundle would fail in the browser."
            )
            return _report_compile_failure(
                path, msg, all_warnings, as_json=as_json,
            )

        # --target wasi-p2 (#237): emit the component BEFORE any success
        # envelope — the emitter's family gate raises ValueError for host
        # families the target does not support, and that must surface as
        # a clean diagnostic (never a silent fallback to the core target).
        component_wat: str | None = None
        if target == "wasi-p2":
            from vera.codegen.wasi import emit_wasi_component

            try:
                component_wat = emit_wasi_component(result, world=world)
            except ValueError as exc:
                msg = f"--target wasi-p2: {exc}"
                return _report_compile_failure(
                    path, msg, all_warnings, as_json=as_json,
                )

        if as_json:
            result_dict = {
                "ok": True,
                "file": path,
                "exports": result.exports,
                "diagnostics": [],
                "warnings": [w.to_dict() for w in all_warnings],
            }
            print(json.dumps(result_dict, indent=2))
            return 0

        # Print warnings
        for w in all_warnings:
            print(f"warning: {w.format()}", file=sys.stderr)

        # Output mode: --wat prints WAT text, otherwise write .wasm binary
        if wat:
            print(component_wat if component_wat is not None else result.wat)
            return 0

        # Write the wasi-p2 component binary.  wasmtime's wat2wasm
        # accepts component text (probed live against wasmtime-py 45),
        # so the artifact is a genuine binary component that stock
        # `wasmtime run` executes with no Vera host bindings.
        if component_wat is not None:
            import wasmtime

            out_path = Path(output) if output else p.with_suffix(".wasm")
            out_path.write_bytes(wasmtime.wat2wasm(component_wat))
            kind = (
                "WASI Preview 2 server component (run with: "
                "wasmtime serve <file>)"
                if world == "server"
                else "WASI Preview 2 component"
            )
            print(f"Compiled ({kind}): {out_path}")
            return 0

        # --target browser: emit a self-contained browser bundle
        if target == "browser":
            from vera.browser.emit import emit_browser_bundle

            out_dir = Path(output) if output else p.parent / (p.stem + "_browser")
            title = p.stem.replace("_", " ").title()
            files = emit_browser_bundle(result.wasm_bytes, out_dir, title=title)
            print(f"Browser bundle: {out_dir}/")
            for f in files:
                print(f"  {f.name}")
            return 0

        # Write .wasm binary
        out_path = Path(output) if output else p.with_suffix(".wasm")
        out_path.write_bytes(result.wasm_bytes)
        n = len(result.exports)
        plural = "s" if n != 1 else ""
        print(f"Compiled: {out_path} ({n} function{plural} exported)")
        return 0

    except FileNotFoundError:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [{"severity": "error",
                                               "description": f"file not found: {path}",
                                               "location": {"line": 0, "column": 0}}],
                              "warnings": []}, indent=2))
            return 1
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [exc.diagnostic.to_dict()],
                              "warnings": []}, indent=2))
            return 1
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1


def cmd_serve(
    path: str,
    *,
    port: int = 8000,
    host: str = "127.0.0.1",
) -> int:
    """Compile a .vera file and serve its handle(Request -> Response).

    #305: the accept loop lives here in the host — one fresh
    instantiation per request (isolation), sequential handling (v1).
    A handler trap (including a runtime contract violation) answers
    500 with the trap diagnostic.  Ctrl-C stops the server (exit 130,
    the conventional SIGINT code, consistent with `vera run`).
    """
    from vera.checker import typecheck_with_artifacts
    from vera.codegen import compile as codegen_compile
    from vera.resolver import ModuleResolver
    from vera.runtime.server import make_server

    try:
        p, source, tree = _load_and_parse(path)
        ast = transform(tree)

        resolver = ModuleResolver(_root=p.parent)
        resolved = resolver.resolve_imports(ast, p)

        check_diags, artifacts = typecheck_with_artifacts(
            ast, source, file=str(p), resolved_modules=resolved,
            collect_module_artifacts=True,
        )
        type_diags = resolver.errors + check_diags
        type_errors = [d for d in type_diags if d.severity == "error"]
        if type_errors:
            for e in type_errors:
                print(e.format(), file=sys.stderr)
            return 1

        result = codegen_compile(
            ast, source=source, file=str(p), resolved_modules=resolved,
            expr_semantic_types=artifacts.expr_semantic_types,
            expr_target_types=artifacts.expr_target_types,
            module_artifacts=artifacts.module_artifacts,
        )
        errors = [d for d in result.diagnostics if d.severity == "error"]
        if errors:  # pragma: no cover — codegen errors after typecheck pass
            for e in errors:
                print(e.format(), file=sys.stderr)
            return 1

        try:
            httpd = make_server(result, host=host, port=port)
        except ValueError as err:
            print(f"Error: {err}", file=sys.stderr)
            return 1
        except OSError as err:
            print(
                f"Error: could not bind {host}:{port} — {err}",
                file=sys.stderr,
            )
            return 1

        bound_port = httpd.server_address[1]
        print(f"Serving {p.name} on http://{host}:{bound_port} "
              f"(Ctrl-C to stop)")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\nStopped.", file=sys.stderr)
            return 130
        finally:
            httpd.server_close()
        return 0  # pragma: no cover — serve_forever exits only via signal
    except FileNotFoundError:
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as e:
        print(e.diagnostic.format(), file=sys.stderr)
        return 1


def cmd_run(
    path: str,
    *,
    as_json: bool = False,
    fn_name: str | None = None,
    fn_args: list[int | float] | None = None,
    raw_fn_args: list[str] | None = None,
    target: str = "wasm",
    world: str = "cli",
) -> int:
    """Parse, type-check, compile, and execute a .vera file."""
    from vera.ast import FnDecl

    # Pure flag validation — same early exit cmd_compile gives
    # (CR review, PR #850).
    if world != "cli" and target != "wasi-p2":
        msg = (
            f"--world {world} requires --target wasi-p2 "
            f"(the core and browser targets have no world concept)"
        )
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [{"severity": "error",
                                               "description": msg,
                                               "location": {"line": 0, "column": 0}}]},
                             indent=2))
            return 1
        print(f"Error: {msg}", file=sys.stderr)
        return 1
    # A server-world component cannot be executed by vera run at all
    # — refuse before any parse/compile work (CR review, PR #850).
    if world == "server":
        # Stage D: wasmtime-py's add_wasip2 host has no wasi:http
        # and no resource-definition API, so a server-world
        # component cannot be executed here at all.
        msg = (
            "a server-world component exports "
            "wasi:http/incoming-handler, which `vera run` cannot "
            "host.  Compile it and serve with the wasmtime CLI:\n"
            f"  vera compile --target wasi-p2 --world server {path}\n"
            "  wasmtime serve <output>.wasm\n"
            "(or use `vera serve` for the native Python driver)"
        )
        if as_json:
            print(json.dumps({
                "ok": False,
                "file": path,
                "diagnostics": [{
                    "severity": "error",
                    "description": msg,
                    "location": {"line": 0, "column": 0},
                }],
            }, indent=2))
            return 1
        print(f"Error: {msg}", file=sys.stderr)
        return 1
    from vera.checker import typecheck_with_artifacts
    from vera.codegen import (
        compile as codegen_compile,
        dropped_entry_message,
        execute,
    )
    from vera.resolver import ModuleResolver

    try:
        p, source, tree = _load_and_parse(path)
        ast = transform(tree)


        # Resolve imports (C7a)
        resolver = ModuleResolver(_root=p.parent)
        resolved = resolver.resolve_imports(ast, p)

        # Type-check, retaining the resolved-type artifacts so the codegen
        # integer-overflow guard (#798) classifies operands in lockstep with
        # the verifier.
        check_diags, artifacts = typecheck_with_artifacts(
            ast, source, file=str(p), resolved_modules=resolved,
            collect_module_artifacts=True,
        )
        type_diags = resolver.errors + check_diags
        type_errors = [d for d in type_diags if d.severity == "error"]

        if type_errors:
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in type_errors],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            for e in type_errors:
                print(e.format(), file=sys.stderr)
            return 1

        # Compile (C7e: pass resolved modules for cross-module codegen)
        result = codegen_compile(
            ast, source=source, file=str(p), resolved_modules=resolved,
            expr_semantic_types=artifacts.expr_semantic_types,
            expr_target_types=artifacts.expr_target_types,
            module_artifacts=artifacts.module_artifacts,
        )

        if not result.ok:  # pragma: no cover — codegen errors after typecheck pass
            errors = [d for d in result.diagnostics if d.severity == "error"]
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in errors],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            for e in errors:
                print(e.format(), file=sys.stderr)
            return 1

        codegen_warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]

        # #1183: surface the skip/drop diagnostics on EVERY run that has
        # them, not only when the drop happened to empty the export list.
        # A program that still exports a sibling is exactly the case where
        # the user is least likely to notice that something went missing,
        # and a refused entry (below) needs the ROOT [E602]'s own wording,
        # not just the location its [E620] quotes.  Printed to stderr, so
        # the JSON envelope on stdout is unaffected; JSON consumers get
        # the same content under the envelope's `warnings` key.
        if codegen_warnings:
            print("Compilation notes:", file=sys.stderr)
            for w in codegen_warnings:
                print(f"  - {w.description}", file=sys.stderr)

        # #1183: refuse a DECLARED-but-dropped entry before anything else.
        # This runs ahead of the no-exports branch below because "you wrote
        # `main` and this construct is why it isn't there" is a strictly
        # better answer than "no exported functions; try declaring one
        # public" — which is actively misleading when `main` IS public.
        requested_entry = fn_name
        auto_selected_entry: str | None = None
        if requested_entry is None and "main" not in result.exports:
            if "main" in result.dropped_fns:
                requested_entry = "main"
            elif result.exports:
                auto_selected_entry = result.exports[0]
        if (
            requested_entry is not None
            and requested_entry not in result.exports
            and requested_entry in result.dropped_fns
        ):
            msg = dropped_entry_message(requested_entry, result)
            if as_json:
                dropped_envelope: dict[str, object] = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [{
                        "severity": "error",
                        "description": msg,
                        "location": {"line": 0, "column": 0},
                    }],
                }
                if codegen_warnings:
                    dropped_envelope["warnings"] = [
                        w.to_dict() for w in codegen_warnings
                    ]
                print(json.dumps(dropped_envelope, indent=2))
                return 1
            print(f"Error: {msg}", file=sys.stderr)
            return 1

        # Check for no-exports or private-fn-targeted cases
        if result.ok and not result.exports:
            # Build a summary of declared functions and their visibility
            fn_lines: list[str] = []
            for tld in ast.declarations:
                if isinstance(tld.decl, FnDecl):
                    vis = tld.visibility or "private"
                    fn_lines.append(f"  {vis} fn {tld.decl.name}")
            msg = "No exported functions to call.\n"
            if fn_lines:
                msg += "\nDeclared functions:\n"
                msg += "\n".join(fn_lines)
                msg += "\n"
            msg += (
                "\nOnly public functions are exported as WASM entry points."
                "\nTo make a function callable, declare it as public:\n"
                "\n  public fn main(-> @Int)"
                "\n    requires(true)"
                "\n    ensures(true)"
                "\n    effects(pure)"
                "\n  {\n    0\n  }"
                "\n\nAlternatively, use 'vera check' or 'vera verify' "
                "to validate without running."
            )
            if as_json:
                no_exports_envelope: dict[str, object] = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [{
                        "severity": "error",
                        "description": msg,
                        "location": {"line": 0, "column": 0},
                    }],
                }
                if codegen_warnings:
                    no_exports_envelope["warnings"] = [
                        w.to_dict() for w in codegen_warnings
                    ]
                print(json.dumps(no_exports_envelope, indent=2))
                return 1
            print(f"Error: {msg}", file=sys.stderr)
            return 1

        if result.ok and fn_name and fn_name not in result.exports:
            # Check if function exists but is private
            is_private = any(
                isinstance(tld.decl, FnDecl)
                and tld.decl.name == fn_name
                and tld.visibility == "private"
                for tld in ast.declarations
            )
            if is_private:
                msg = (
                    f"Function '{fn_name}' is declared private "
                    f"and cannot be called directly.\n"
                    f"\nTo make it callable, change its declaration to:\n"
                    f"\n  public fn {fn_name}"
                )
            else:
                exports_str = (
                    ", ".join(result.exports)
                    if result.exports else "(none)"
                )
                msg = (
                    f"Function '{fn_name}' not found in exports. "
                    f"Available: {exports_str}"
                )
            if as_json:
                print(json.dumps({
                    "ok": False,
                    "file": path,
                    "diagnostics": [{
                        "severity": "error",
                        "description": msg,
                        "location": {"line": 0, "column": 0},
                    }],
                }, indent=2))
                return 1
            print(f"Error: {msg}", file=sys.stderr)
            return 1

        # #1183: auto-selection survives only for the never-declared case
        # (the single-function convenience), and announces itself so the
        # choice is never invisible.
        if auto_selected_entry is not None:
            print(
                f"Note: no 'main' declared — running public function "
                f"'{auto_selected_entry}'.",
                file=sys.stderr,
            )

        # --target wasi-p2 (#237): execute as a component under the
        # built-in wasip2 host instead of the vera.* bindings.  The
        # component lifts a single entry (main), so --fn is a clean
        # diagnostic here rather than a missing-export crash; the
        # emitter's family gate likewise surfaces as a diagnostic.
        if target == "wasi-p2":
            if fn_name is not None and fn_name != "main":
                msg = (
                    f"--target wasi-p2 runs 'main' only (the component "
                    f"lifts a single entry); --fn {fn_name} is not "
                    f"available.  Use the default target for --fn."
                )
                if as_json:
                    print(json.dumps({
                        "ok": False,
                        "file": path,
                        "diagnostics": [{
                            "severity": "error",
                            "description": msg,
                            "location": {"line": 0, "column": 0},
                        }],
                    }, indent=2))
                    return 1
                print(f"Error: {msg}", file=sys.stderr)
                return 1
            from vera.runtime.wasi_host import execute_wasi_p2

            try:
                exec_result = execute_wasi_p2(
                    result,
                    cli_args=raw_fn_args or [],
                    argv0=p.name,
                    tee_stdout=not as_json,
                )
            except ValueError as exc:
                msg = f"--target wasi-p2: {exc}"
                if as_json:
                    print(json.dumps({
                        "ok": False,
                        "file": path,
                        "diagnostics": [{
                            "severity": "error",
                            "description": msg,
                            "location": {"line": 0, "column": 0},
                        }],
                    }, indent=2))
                    return 1
                print(f"Error: {msg}", file=sys.stderr)
                return 1
            # Falls through to the shared reporting tail below — the
            # ExecuteResult contract (value/stdout/stderr/exit_code)
            # is target-independent by design.
        else:
            # Execute — pass CLI args as strings for IO.args
            str_args = (
                raw_fn_args if raw_fn_args
                else ([str(a) for a in fn_args] if fn_args else [])
            )
            # capture_stderr=True so IO.stderr writes are buffered into
            # exec_result.stderr (and into WasmTrapError.stderr on the trap
            # path). Without it, host_stderr falls through to live writes on
            # sys.stderr — which works for the success path but leaves the
            # WasmTrapError handler's exc.stderr / JSON envelope's "stderr"
            # field permanently empty.  Mirrors the always-capture treatment
            # of stdout (host_print is unconditional).
            #
            # tee_stdout (#543): in text mode, mirror IO.print writes live
            # to sys.stdout so animations, progress bars, and any program
            # using ANSI escape sequences (cursor home, clear screen, etc.)
            # render as they happen instead of buffering until exit and
            # then flushing in a single burst at terminal-redraw speed.
            # JSON mode keeps the live mirror off — the transcript is
            # packed into the JSON envelope and a live write would corrupt
            # the output for downstream consumers parsing our stdout.
            exec_result = execute(
                result, fn_name=fn_name, args=fn_args, raw_args=raw_fn_args,
                cli_args=str_args, capture_stderr=True,
                tee_stdout=not as_json,
            )

        if as_json:
            result_dict = {
                "ok": True,
                "file": path,
                "function": fn_name or (
                    "main" if "main" in result.exports
                    else result.exports[0] if result.exports else None
                ),
                "value": exec_result.value,
                "stdout": exec_result.stdout,
            }
            if exec_result.stderr:
                result_dict["stderr"] = exec_result.stderr
            if exec_result.exit_code is not None:
                result_dict["exit_code"] = exec_result.exit_code
            # #1183: the machine-readable half of the "Compilation notes"
            # block — a JSON consumer must be able to see that functions
            # were dropped from the module it just ran.  Present only when
            # non-empty, so an ordinary run's envelope is unchanged.
            if codegen_warnings:
                result_dict["warnings"] = [
                    w.to_dict() for w in codegen_warnings
                ]
            print(json.dumps(result_dict, indent=2))
            return exec_result.exit_code if exec_result.exit_code else 0

        # Text mode (JSON returned above): IO.print writes have
        # already streamed live to sys.stdout via tee_stdout (#543),
        # so we do not re-write exec_result.stdout — that would
        # double-print the whole transcript.  We still emit a
        # trailing newline if the last live write didn't end with
        # one, so the shell prompt doesn't smush against the
        # program's final character.  The value-fallback branch is
        # unaffected: when no IO.print was called, output_buf is
        # empty and we print the return value as before.
        if exec_result.stdout:
            if not exec_result.stdout.endswith("\n"):
                sys.stdout.write("\n")
                sys.stdout.flush()
        elif exec_result.value is not None:
            print(exec_result.value)

        # Replay captured stderr to the actual stderr stream. Mirrors
        # the stdout replay above. Independent of value printing — a
        # function that returns 42 and also wrote to stderr should show
        # both, in their natural streams.
        if exec_result.stderr:
            sys.stderr.write(exec_result.stderr)
            if not exec_result.stderr.endswith("\n"):
                sys.stderr.write("\n")

        # Use IO.exit code as process exit code
        if exec_result.exit_code is not None:
            return exec_result.exit_code

        return 0

    except FileNotFoundError:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [{"severity": "error",
                                               "description": f"file not found: {path}",
                                               "location": {"line": 0, "column": 0}}]}
                              , indent=2))
            return 1
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [exc.diagnostic.to_dict()]}
                              , indent=2))
            return 1
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1
    except WasmTrapError as exc:
        # Classified WASM trap (#516 Stage 1) carrying any output the
        # program produced before the trap fired (#522). Note: this
        # handler must come before ``except RuntimeError`` because
        # WasmTrapError is a RuntimeError subclass.
        if as_json:
            # JSON mode: pack stdout/stderr into the envelope. Writing
            # them to sys.stdout/sys.stderr would corrupt the JSON for
            # downstream consumers parsing our output.
            diag: dict[str, object] = {
                "severity": "error",
                "description": str(exc),
                "trap_kind": exc.kind,
                "location": {"line": 0, "column": 0},
                # #516 Stage 2 — structured backtrace.  Always present
                # (possibly an empty list) so JSON consumers can
                # iterate `diag["frames"]` without `.get(..., [])`
                # ceremony.  Same shape stability principle as the
                # always-present `trap_kind` above; `frames` is
                # structural, not optional content like `stdout`.
                # Each frame is a `TrapFrame` dataclass (#516 Stage
                # 2) — convert to dict at the JSON serialisation
                # boundary so the wire format stays the same as
                # before the dataclass refactor (CodeRabbit round 5).
                "frames": [f.to_dict() for f in exc.frames],
                # #516 Stage 3 (#547) — per-kind Fix paragraph.
                # Always present for shape stability (same reasoning
                # as `trap_kind` and `frames`); empty string for the
                # kinds that don't admit a generic suggestion
                # (`contract_violation` and `host_error`, whose
                # descriptions already carry the remediation;
                # `unknown`).  Mirrors the
                # `fix` field on compile-time `Diagnostic` objects.
                "fix": exc.fix,
            }
            envelope: dict[str, object] = {
                "ok": False,
                "file": path,
                "diagnostics": [diag],
            }
            if exc.stdout:
                envelope["stdout"] = exc.stdout
            if exc.stderr:
                envelope["stderr"] = exc.stderr
            print(json.dumps(envelope, indent=2))
            return 1

        # Text mode: surface the captured streams to the corresponding
        # actual streams BEFORE the error message, so the error text
        # ends up after whatever the program had been printing.
        # Explicit flush on stdout: under `2>&1` redirects, stdout and
        # stderr are buffered independently and a stderr write can
        # appear before an earlier stdout write in the merged view.
        # Flushing stdout before any stderr write guarantees the
        # captured program output is committed first.
        #
        # tee_stdout (#543): in text mode IO.print writes have already
        # streamed live to sys.stdout, so exc.stdout has been printed
        # once already. Skip re-writing it (would double-print every
        # byte the program produced before the trap fired). Just
        # close the line if the last write didn't end with \n so the
        # error message lands cleanly on the next line. stderr
        # remains buffered (no tee), so we still own its replay.
        if exc.stdout and not exc.stdout.endswith("\n"):
            sys.stdout.write("\n")
        sys.stdout.flush()
        if exc.stderr:
            sys.stderr.write(exc.stderr)
            if not exc.stderr.endswith("\n"):
                sys.stderr.write("\n")
        print(f"Error: {exc}", file=sys.stderr)
        # #516 Stage 2 — print the source backtrace after the error
        # line.  Outermost (most recent) frame first.  Built-in /
        # runtime helpers ($alloc, $gc_collect, $contract_fail) show
        # as "<builtin>" rather than a misleading file:line.  Filter
        # the leading run of built-in frames so the user sees their
        # own code at the top — those frames are usually noise (the
        # trap fired inside the allocator on behalf of user code, and
        # what the user wants to know is which user function called
        # the allocator).  Only collapse if at least one user frame
        # would remain; otherwise keep the full list.
        if exc.frames:
            user_idx = next(
                (i for i, f in enumerate(exc.frames)
                 if not f.is_builtin),
                None,
            )
            display_frames = (
                exc.frames[user_idx:] if user_idx is not None
                else exc.frames
            )
            # Header first, then the optional suppression line, then
            # the frames themselves.  The suppression message is
            # metadata about the backtrace below it — reading it
            # under the heading is more natural than reading it as
            # a preface to the heading (CodeRabbit round 6).
            print("Source backtrace:", file=sys.stderr)
            if user_idx and user_idx > 0:
                hidden = user_idx
                print(
                    f"  (suppressed {hidden} runtime-helper frame"
                    f"{'s' if hidden != 1 else ''} above first user code)",
                    file=sys.stderr,
                )
            for frame in display_frames:
                if frame.is_builtin:
                    print(
                        f"  in {frame.func}  <builtin>", file=sys.stderr,
                    )
                elif frame.file == "<unknown>" or frame.line_start is None:
                    print(
                        f"  in {frame.func}  ({frame.file})",
                        file=sys.stderr,
                    )
                elif frame.line_start == frame.line_end:
                    print(
                        f"  in {frame.func}  "
                        f"({frame.file}:{frame.line_start})",
                        file=sys.stderr,
                    )
                else:
                    print(
                        f"  in {frame.func}  "
                        f"({frame.file}:{frame.line_start}"
                        f"-{frame.line_end})",
                        file=sys.stderr,
                    )
        # #516 Stage 3 (#547) — append the per-kind Fix paragraph
        # after the backtrace.  Empty string for kinds that don't
        # admit a generic suggestion (`contract_violation` and
        # `host_error`, where the description already explains what
        # failed; `unknown`, where by definition we don't know what
        # to suggest — the three empty entries in
        # `_TRAP_FIX_PARAGRAPHS`), so
        # we suppress the block entirely in those cases — printing
        # an empty "Fix:" header would just be noise.
        #
        # Wrap to ~76 columns to match the compile-time `Diagnostic`
        # rendering style, with a leading "  " indent so the block
        # visually nests under "Fix:".  textwrap.fill handles the
        # paragraph as a single string (we don't preserve internal
        # newlines because the canonical Fix paragraphs in
        # `_TRAP_FIX_PARAGRAPHS` are already single paragraphs).
        if exc.fix:
            import textwrap
            print("Fix:", file=sys.stderr)
            wrapped = textwrap.fill(
                exc.fix,
                width=76,
                initial_indent="  ",
                subsequent_indent="  ",
            )
            print(wrapped, file=sys.stderr)
        return 1
    except RuntimeError as exc:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [{"severity": "error",
                                               "description": str(exc),
                                               "location": {"line": 0, "column": 0}}]}
                              , indent=2))
            return 1
        print(f"Error: {exc}", file=sys.stderr)
        return 1
    except Exception as exc:  # pragma: no cover — defensive backstop
        # WasmTrapError above handles the expected wasmtime path. This
        # remains as a defensive backstop for the case where some other
        # Trap-named exception slips past the api.py classifier — for
        # example a future wasmtime version with a new Trap subclass.
        exc_name = type(exc).__name__
        if exc_name in ("Trap", "WasmtimeError"):
            msg = f"Unhandled WASM trap: {exc}"
            if as_json:
                print(json.dumps({"ok": False, "file": path,
                                  "diagnostics": [{"severity": "error",
                                                   "description": msg,
                                                   "location": {"line": 0, "column": 0}}]}
                                  , indent=2))
                return 1
            print(f"Error: {msg}", file=sys.stderr)
            return 1
        raise  # re-raise unexpected exceptions


def cmd_ast(path: str, as_json: bool = False) -> int:
    """Parse a .vera file and print the AST."""
    try:
        _p, _source, tree = _load_and_parse(path)
        ast = transform(tree)
        if as_json:
            print(json.dumps(ast.to_dict(), indent=2))
        else:
            print(ast.pretty())
        return 0
    except FileNotFoundError:
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1


def cmd_test(
    path: str,
    *,
    as_json: bool = False,
    trials: int = 100,
    fn_name: str | None = None,
) -> int:
    """Parse, type-check, and test a .vera file via contract-driven testing."""
    try:
        # INSIDE the try, as in `cmd_verify` (#1361 review).
        from vera.checker import typecheck_with_artifacts
        from vera.resolver import ModuleResolver
        from vera.tester import test as run_test

        p, source, tree = _load_and_parse(path)
        ast = transform(tree)


        # Resolve imports (C7a)
        resolver = ModuleResolver(_root=p.parent)
        resolved = resolver.resolve_imports(ast, p)

        # Type-check first.  #986: use the artifact-returning check and thread the
        # resolved- / target-type side-tables into the tester (below) so the WASM
        # the tester compiles carries the SAME @Nat->@Int widen guards
        # (tuple/array components, recovered only from the target table) the
        # verifier obligates — without them the tester executed guard-free WASM
        # the verifier had classified tier3-guarded (a `vera test` desync).
        check_diags, artifacts = typecheck_with_artifacts(
            ast, source, file=str(p), resolved_modules=resolved,
            collect_module_artifacts=True,
        )
        type_diags = resolver.errors + check_diags
        type_errors = [d for d in type_diags if d.severity == "error"]

        if type_errors:
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in type_errors],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            for e in type_errors:
                print(e.format(), file=sys.stderr)
            return 1

        # Run tests
        result = run_test(
            ast,
            source=source,
            file=str(p),
            trials=trials,
            fn_name=fn_name,
            resolved_modules=resolved,
            expr_semantic_types=artifacts.expr_semantic_types,
            expr_target_types=artifacts.expr_target_types,
            module_artifacts=artifacts.module_artifacts,
            alias_env=artifacts.alias_env,
        )

        has_errors = any(d.severity == "error" for d in result.diagnostics)

        if as_json:
            s = result.summary
            result_dict = {
                "ok": s.failed == 0 and not has_errors,
                "file": path,
                "functions": [
                    {
                        "name": f.fn_name,
                        "category": f.category,
                        "reason": f.reason,
                        "trials_run": f.trials_run,
                        "trials_passed": f.trials_passed,
                        "trials_failed": f.trials_failed,
                        "failures": [
                            {
                                "args": t.args,
                                "status": t.status,
                                "message": t.message,
                            }
                            for t in f.failures[:5]
                        ],
                    }
                    for f in result.functions
                ],
                "summary": {
                    "verified": s.verified,
                    "tested": s.tested,
                    "passed": s.passed,
                    "failed": s.failed,
                    "skipped": s.skipped,
                    "total_trials": s.total_trials,
                    "total_passes": s.total_passes,
                    "total_failures": s.total_failures,
                    "unlisted_errors": s.unlisted_errors,
                },
                "diagnostics": [d.to_dict() for d in result.diagnostics],
            }
            print(json.dumps(result_dict, indent=2))
            return 1 if s.failed > 0 or has_errors else 0

        # Human-readable output
        print(f"\nTesting: {path}\n")
        for f in result.functions:
            if f.category == "tested":
                if f.trials_failed > 0:
                    line = (
                        f"  {f.fn_name} {'.' * max(1, 40 - len(f.fn_name))} "
                        f"FAILED  "
                        f"({f.trials_passed}/{f.trials_run} passed, "
                        f"{f.trials_failed} failed)"
                    )
                else:
                    line = (
                        f"  {f.fn_name} {'.' * max(1, 40 - len(f.fn_name))} "
                        f"TESTED  ({f.trials_run}/{f.trials_run} passed)"
                    )
            elif f.category == "verified":
                line = (
                    f"  {f.fn_name} {'.' * max(1, 40 - len(f.fn_name))} "
                    f"VERIFIED (Tier 1)"
                )
            elif f.category == "failed":
                line = (
                    f"  {f.fn_name} {'.' * max(1, 40 - len(f.fn_name))} "
                    f"FAILED  ({f.reason})"
                )
            else:
                line = (
                    f"  {f.fn_name} {'.' * max(1, 40 - len(f.fn_name))} "
                    f"SKIPPED ({f.reason})"
                )
            print(line)

            # Show first few failures
            if f.failures:
                for trial in f.failures[:3]:
                    args_str = ", ".join(
                        f"{k} = {v}" for k, v in trial.args.items()
                    )
                    print(f"    {args_str} -> {trial.message}")

        if result.diagnostics:
            print("\nDiagnostics:")
            for d in result.diagnostics:
                code = f"{d.error_code}: " if d.error_code else ""
                first_line = d.description.splitlines()[0]
                print(f"  {code}{first_line}")

        # Summary
        s = result.summary
        static_failed = sum(1 for f in result.functions if f.category == "failed")
        tested_failed = sum(
            1 for f in result.functions
            if f.category == "tested" and f.trials_failed > 0
        )
        unlisted_errors = s.unlisted_errors
        parts = []
        if s.tested > 0:
            parts.append(
                f"{s.tested} tested ({s.passed} passed"
                + (f", {tested_failed} failed)" if tested_failed else ")")
            )
        if static_failed > 0:
            parts.append(f"{static_failed} failed")
        if unlisted_errors > 0:
            parts.append(
                f"{unlisted_errors} verifier "
                f"error{'s' if unlisted_errors != 1 else ''}"
            )
        if s.verified > 0:
            parts.append(f"{s.verified} verified")
        if s.skipped > 0:
            parts.append(f"{s.skipped} skipped")
        summary_str = ", ".join(parts) if parts else "no testable functions"
        print(f"\nResults: {summary_str}")

        if s.total_trials > 0:
            print(
                f"Trials:  {s.total_trials} run, "
                f"{s.total_passes} passed, "
                f"{s.total_failures} failed"
            )

        return 1 if s.failed > 0 or has_errors else 0

    except FileNotFoundError:
        # The sibling handlers are inside the backstop's reach too (#1361
        # review): their own `print` / `json.dumps` / `to_dict` can raise, and an
        # unenveloped handler failing mid-report is the same empty stdout as no
        # handler at all.
        try:
            if as_json:
                print(json.dumps({"ok": False, "file": path,
                                  "diagnostics": [{"severity": "error",
                                                   "description": f"file not found: {path}",
                                                   "location": {"line": 0, "column": 0}}]},
                                  indent=2))
                return 1
            print(f"Error: file not found: {path}", file=sys.stderr)
            return 1
        except Exception as inner:  # noqa: BLE001 — envelope backstop
            return _internal_error_envelope(
                path, inner, doing='testing', as_json=as_json)
    except VeraError as exc:
        # The sibling handlers are inside the backstop's reach too (#1361
        # review): their own `print` / `json.dumps` / `to_dict` can raise, and an
        # unenveloped handler failing mid-report is the same empty stdout as no
        # handler at all.
        try:
            if as_json:
                print(json.dumps({"ok": False, "file": path,
                                  "diagnostics": [exc.diagnostic.to_dict()]},
                                  indent=2))
                return 1
            print(exc.diagnostic.format(), file=sys.stderr)
            return 1
        except Exception as inner:  # noqa: BLE001 — envelope backstop
            return _internal_error_envelope(
                path, inner, doing='testing', as_json=as_json)
    except Exception as exc:  # noqa: BLE001 — envelope backstop (#1360)
        return _internal_error_envelope(
            path, exc, doing="testing", as_json=as_json)


def cmd_fmt(
    path: str,
    *,
    write: bool = False,
    check: bool = False,
) -> int:
    """Format a .vera file to canonical form."""
    from vera.formatter import format_source

    try:
        p = Path(path)
        # Read bytes, not text: read_text's universal-newline translation
        # erases carriage returns before we can see them, so a CRLF file
        # would compare equal to its LF formatting and --check would call
        # it canonical — disagreeing with the corpus gate, which reads
        # bytes and rejects any CR. Canonical Vera is LF-only (spec 1.8
        # rule 10). Normalise for formatting, but a file that HELD a CR
        # was not already canonical.
        raw = p.read_bytes()
        had_cr = b"\r" in raw
        source = raw.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
        formatted = format_source(source, file=str(p))

        if check:
            if source == formatted and not had_cr:
                print(f"OK: {path}")
                return 0
            print(f"Would reformat: {path}", file=sys.stderr)
            return 1

        if write:
            # Write bytes, not text: Path.write_text opens in text mode,
            # which on Windows translates every "\n" to "\r\n" — so the
            # *canonical* formatter would emit non-canonical CRLF output
            # (spec 1.8 rule 10 is LF-only), and --check would then flag
            # what --write just produced. Bytes bypass the translation.
            p.write_bytes(formatted.encode("utf-8"))
            print(f"Formatted: {path}")
            return 0

        # Default: print to stdout
        sys.stdout.write(formatted)
        return 0
    except FileNotFoundError:
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1


USAGE = """\
Usage: vera <command> [options] <file>

Commands:
    version              Print the installed Vera version (also --version, -V)
    parse                Parse a .vera file and print the parse tree
    check [--json|--quiet|--explain-slots]       Parse and type-check a .vera file
    typecheck [--json|--quiet|--explain-slots]   Same as check (explicit alias)
    verify [--json|--quiet|--timeout-ms n]   Parse, type-check, and verify contracts
    test [--json]        Test contracts via Z3-guided input generation
    compile [--wat]      Compile a .vera file to WebAssembly
    compile --target browser  Emit browser bundle (wasm + JS + HTML)
    compile --target wasi-p2  Emit a WASI Preview 2 component (experimental)
    compile --target wasi-p2 --world server  Emit a wasi:http server component (run with wasmtime serve)
    run [--fn name]      Compile and execute a .vera file
    run --target wasi-p2  Execute under the built-in WASI 0.2 host
    serve [--port n]     Serve handle(Request -> Response) over HTTP (default :8000)
    ast [--json]         Parse a .vera file and print the AST
    fmt [--write|--check] Format a .vera file to canonical form
    lsp                  Serve the Language Server Protocol over stdio
                         (needs the [lsp] extra: pip install -e ".[lsp]")
    builtins [--json]    List the built-in function registry
    effects [--json]     List the effect and ability registry
    errors [--json]      List the diagnostic error-code registry (E001–E702)

Options:
    --json               Output machine-readable JSON diagnostics
    --quiet              Suppress success output (errors still printed)
    --wat                Print WAT text instead of writing .wasm binary
    --fn <name>          Function to execute or test
    --trials <n>         Number of test trials (default: 100, for vera test)
    --timeout-ms <n>     Per-query Z3 budget in ms, accepted by vera verify.
                         Precedence: this flag, then VERA_Z3_TIMEOUT_MS, then
                         the 10000 default -- so the variable is also verify's
                         fallback when the flag is absent, and it is the only
                         route for vera test and the language server, which
                         take no such flag
    --port <n>           Port to serve on (default: 8000, for vera serve)
    --host <h>           Host/interface to bind (default: 127.0.0.1, for vera serve)
    -o <path>            Output path for .wasm binary (or directory for --target browser)
    --target <t>         Compilation target: wasm (default), browser, or wasi-p2
    --world <w>          wasi-p2 world: cli (default) or server (wasi:http/incoming-handler)
    --write              Format in place (vera fmt)
    --check              Check if already canonical (vera fmt)
    --explain-slots      Print slot-resolution tables after a successful check
    -- <args...>         Arguments to pass to the executed function
"""


def cmd_version() -> int:
    """Print the installed Vera version."""
    import vera
    print(f"vera {vera.__version__}")
    return 0


def cmd_lsp() -> int:
    """Serve the Language Server Protocol over stdio (#222).

    The transport dependencies live in the optional ``[lsp]`` extra so
    the base install stays pure-wheel-minimal; the guard below turns a
    missing extra into an actionable message instead of a traceback.
    """
    try:
        from vera.lsp.server import main as lsp_main
    except ModuleNotFoundError as exc:
        # Only a missing transport dependency means "extra not
        # installed" — any other import failure inside vera.lsp is a
        # real bug and must surface as its traceback, not be
        # misreported as a packaging problem.
        missing = (exc.name or "").split(".")[0]
        if missing not in {"pygls", "lsprotocol"}:
            raise
        print(
            "Error: the LSP server needs the optional [lsp] extra.\n"
            '  Install it with: pip install -e ".[lsp]"',
            file=sys.stderr,
        )
        return 1
    lsp_main()
    return 0


def _render_cell(value: object) -> str:
    """Render one introspection field for the text table.

    List-valued fields (``ops``, ``type_params``) become comma-joined;
    everything else is ``str()``.
    """
    if isinstance(value, list):
        return ", ".join(str(x) for x in value)
    return str(value)


def _emit_introspection(
    payload: dict[str, object], as_json: bool, columns: tuple[str, ...]
) -> int:
    """Print a registry introspection payload (#539).

    With ``--json`` the full ``{schema, items}`` envelope is emitted as pretty
    JSON — the machine surface, parallel to ``check``/``verify --json``.
    Otherwise the items are rendered as an aligned text table over *columns*,
    the human default.
    """
    if as_json:
        print(json.dumps(payload, indent=2))
        return 0
    items = cast("list[dict[str, object]]", payload["items"])
    widths = [max((len(_render_cell(it.get(c, ""))) for it in items), default=0) for c in columns]
    for it in items:
        row = "  ".join(
            f"{_render_cell(it.get(c, '')):<{widths[idx]}}" for idx, c in enumerate(columns)
        )
        print(row.rstrip())
    return 0


def cmd_builtins(as_json: bool = False) -> int:
    """List the built-in function registry — ``vera builtins`` (#539)."""
    return _emit_introspection(builtins_payload(), as_json, ("name", "module", "kind"))


def cmd_effects(as_json: bool = False) -> int:
    """List the effect and ability registry — ``vera effects`` (#539)."""
    return _emit_introspection(effects_payload(), as_json, ("name", "kind", "ops"))


def cmd_errors(as_json: bool = False) -> int:
    """List the diagnostic error-code registry — ``vera errors`` (#539)."""
    return _emit_introspection(errors_payload(), as_json, ("code", "phase", "title"))


def main() -> None:
    # Read stdin and emit program output / diagnostics as UTF-8 regardless of
    # the host locale: a Vera program printing OR reading `→` / `—` (or any
    # non-ASCII — e.g. `IO.read_char` on piped UTF-8 input) must not hit cp1252
    # on a locale-default Windows shell (#645).  Guarded via getattr — a wrapped
    # or replaced stream (e.g. pytest's capture) may not expose reconfigure();
    # encoding to UTF-8 never raises (it covers all of Unicode).
    for _stream in (sys.stdin, sys.stdout, sys.stderr):
        _reconfigure = getattr(_stream, "reconfigure", None)
        if _reconfigure is not None:
            _reconfigure(encoding="utf-8")

    args = sys.argv[1:]

    # #1350: `--timeout-ms` is verify-only, and the refusal must come BEFORE
    # the no-file dispatches below.  Placed after them, `vera lsp
    # --timeout-ms 5000` starts the language server and ignores the flag —
    # precisely the silent no-op the refusal exists to prevent — and the same
    # for `version`, `builtins`, `effects` and `errors`, none of which reads
    # it either.  The flag reaching a command that cannot honour it should
    # always be an error, whatever the command needs on its command line.
    if "--timeout-ms" in args and args[0] != "verify":
        _tm_msg = (
            f"--timeout-ms is only accepted by `vera verify`, not "
            f"`vera {args[0]}`. Set VERA_Z3_TIMEOUT_MS in the environment "
            f"to reach `vera test` and the language server."
        )
        if "--json" in args:
            print(json.dumps({"ok": False, "file": "",
                              "diagnostics": [{"severity": "error",
                                               "description": _tm_msg}]},
                             indent=2))
        else:
            print(f"Error: {_tm_msg}", file=sys.stderr)
        sys.exit(1)

    # Handle version before the length check — these need no file argument.
    if not args or args[0] in ("version", "--version", "-V"):
        if not args:
            print(USAGE, file=sys.stderr)
            sys.exit(1)
        sys.exit(cmd_version())

    # `lsp` also takes no file argument — it serves LSP over stdio
    # until the client disconnects (#222 Phase C).
    if args[0] == "lsp":
        sys.exit(cmd_lsp())

    # `builtins`/`effects`/`errors` take no file argument — they enumerate the
    # compiler's own registries as JSON or a text table (#539).
    if args[0] in ("builtins", "effects", "errors"):
        as_json = "--json" in args
        if args[0] == "builtins":
            sys.exit(cmd_builtins(as_json=as_json))
        if args[0] == "effects":
            sys.exit(cmd_effects(as_json=as_json))
        sys.exit(cmd_errors(as_json=as_json))

    if len(args) < 2:
        print(USAGE, file=sys.stderr)
        sys.exit(1)

    command = args[0]
    use_json = "--json" in args
    use_quiet = "--quiet" in args
    use_wat = "--wat" in args
    use_write = "--write" in args
    use_check_fmt = "--check" in args and command == "fmt"
    use_explain_slots = "--explain-slots" in args

    # Parse --fn <name> option
    fn_name: str | None = None
    if "--fn" in args:
        fn_idx = args.index("--fn")
        if fn_idx + 1 < len(args):
            fn_name = args[fn_idx + 1]

    # Parse --trials <n> option
    trials: int = 100
    serve_port = 8000
    serve_host = "127.0.0.1"
    if "--port" in args:
        port_idx = args.index("--port")
        if port_idx + 1 < len(args):
            try:
                serve_port = int(args[port_idx + 1])
            except ValueError:
                print("Error: --port requires an integer", file=sys.stderr)
                sys.exit(1)
    if "--host" in args:
        host_idx = args.index("--host")
        if host_idx + 1 < len(args):
            serve_host = args[host_idx + 1]
    from vera.smt import Z3BudgetError, resolve_timeout_ms

    timeout_ms: int | None = None
    # #1350: resolve once, here, so a malformed budget is a clean CLI error
    # rather than a traceback out of the solver's construction seam.  Only
    # the commands that verify consult it — `compile`/`run` never build a
    # solver, so a stray env var must not fail them.
    if command in ("verify", "test"):
        try:
            resolve_timeout_ms()
        except Z3BudgetError as exc:
            if use_json:
                print(json.dumps({"ok": False, "file": "",
                                  "diagnostics": [{"severity": "error",
                                                   "description": str(exc)}]},
                                 indent=2))
            else:
                print(f"Error: {exc}", file=sys.stderr)
            sys.exit(1)

    if "--timeout-ms" in args:
        tm_idx = args.index("--timeout-ms")
        raw_tm = args[tm_idx + 1] if tm_idx + 1 < len(args) else None
        try:
            if raw_tm is None:
                raise Z3BudgetError("--timeout-ms: missing value")
            timeout_ms = resolve_timeout_ms(raw_tm)
        except Z3BudgetError as exc:
            msg = str(exc).replace("timeout_ms:", "--timeout-ms:", 1)
            if use_json:
                print(json.dumps({"ok": False, "file": "",
                                  "diagnostics": [{"severity": "error",
                                                   "description": msg}]},
                                 indent=2))
            else:
                print(f"Error: {msg}", file=sys.stderr)
            sys.exit(1)

    if "--trials" in args:
        trials_idx = args.index("--trials")
        if trials_idx + 1 < len(args):
            try:
                trials = int(args[trials_idx + 1])
            except ValueError:
                msg = f"Invalid --trials value: {args[trials_idx + 1]}"
                if use_json:
                    print(json.dumps({"ok": False, "file": "",
                                      "diagnostics": [{"severity": "error",
                                                       "description": msg}]},
                                     indent=2))
                else:
                    print(f"Error: {msg}", file=sys.stderr)
                sys.exit(1)

    # Parse --target <target> option
    target: str = "wasm"
    if "--target" in args:
        target_idx = args.index("--target")
        if target_idx + 1 < len(args):
            target = args[target_idx + 1]
            if target not in ("wasm", "browser", "wasi-p2"):
                msg = (
                    f"Invalid --target value: {target} "
                    f"(expected 'wasm', 'browser', or 'wasi-p2')"
                )
                if use_json:
                    print(json.dumps({"ok": False, "file": "",
                                      "diagnostics": [{"severity": "error",
                                                       "description": msg,
                                                       "location": {"line": 0, "column": 0}}]},
                                     indent=2))
                else:
                    print(f"Error: {msg}", file=sys.stderr)
                sys.exit(1)

    # Parse --world <world> option (wasi-p2 target only; validated in
    # cmd_compile/cmd_run so JSON mode gets a proper envelope)
    world: str = "cli"
    if "--world" in args:
        world_idx = args.index("--world")
        if world_idx + 1 < len(args):
            world = args[world_idx + 1]
            if world not in ("cli", "server"):
                msg = (
                    f"Invalid --world value: {world} "
                    f"(expected 'cli' or 'server')"
                )
                if use_json:
                    print(json.dumps({"ok": False, "file": "",
                                      "diagnostics": [{"severity": "error",
                                                       "description": msg,
                                                       "location": {"line": 0, "column": 0}}]},
                                     indent=2))
                else:
                    print(f"Error: {msg}", file=sys.stderr)
                sys.exit(1)

    # Parse -o <path> option
    output_path: str | None = None
    if "-o" in args:
        o_idx = args.index("-o")
        if o_idx + 1 < len(args):
            output_path = args[o_idx + 1]

    # Parse -- <args> for run command (kept as raw strings for type-aware parsing)
    fn_args: list[int | float] | None = None
    raw_fn_args: list[str] | None = None
    if "--" in args:
        dash_idx = args.index("--")
        raw_fn_args = list(args[dash_idx + 1:])

    # Remove flags from remaining args to find the filepath
    skip_flags = {"--json", "--quiet", "--wat", "--write", "--check", "--explain-slots"}
    skip_next = {"--fn", "-o", "--trials", "--target", "--port", "--host",
                 "--world", "--timeout-ms"}
    remaining: list[str] = []
    i = 1  # skip command
    while i < len(args):
        if args[i] == "--":
            break  # everything after -- is function args
        if args[i] in skip_flags:
            i += 1
            continue
        if args[i] in skip_next:
            i += 2  # skip flag + value
            continue
        remaining.append(args[i])
        i += 1

    if not remaining:
        print(USAGE, file=sys.stderr)
        sys.exit(1)

    filepath = remaining[0]

    if command == "parse":
        sys.exit(cmd_parse(filepath))
    elif command in ("check", "typecheck"):
        sys.exit(cmd_check(
            filepath, as_json=use_json, quiet=use_quiet,
            explain_slots=use_explain_slots,
        ))
    elif command == "verify":
        sys.exit(cmd_verify(filepath, as_json=use_json, quiet=use_quiet,
                            timeout_ms=timeout_ms))
    elif command == "test":
        sys.exit(cmd_test(
            filepath, as_json=use_json, trials=trials, fn_name=fn_name
        ))
    elif command == "compile":
        sys.exit(cmd_compile(
            filepath, as_json=use_json, wat=use_wat, output=output_path,
            target=target, world=world,
        ))
    elif command == "serve":
        sys.exit(cmd_serve(filepath, port=serve_port, host=serve_host))
    elif command == "run":
        sys.exit(cmd_run(
            filepath, as_json=use_json, fn_name=fn_name, fn_args=fn_args,
            raw_fn_args=raw_fn_args, target=target, world=world,
        ))
    elif command == "ast":
        sys.exit(cmd_ast(filepath, as_json=use_json))
    elif command == "fmt":
        sys.exit(cmd_fmt(filepath, write=use_write, check=use_check_fmt))
    else:
        print(f"Unknown command: {command}", file=sys.stderr)
        print(USAGE, file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":  # pragma: no cover
    main()
