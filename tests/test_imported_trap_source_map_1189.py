"""#1189 — an imported function's trap frame must name ITS module's file.

``fn_source_map`` entries are created by ``_register_fn`` (registration.py),
which stamps every entry with ``self.file`` — the MAIN file — and that pass
runs before the per-module source scope (``_module_source_scope``, #1190) is
entered.  Two surfaces followed:

* An imported NON-GENERIC function never reached ``self._register_fn`` at
  all (Pass 0.5 registers module declarations into a throwaway
  ``CodeGenerator``), so its trap frame resolved to ``<unknown>`` — the
  ``fn_source_map`` miss branch in ``_resolve_trap_frames``.
* A monomorphized clone of an imported GENERIC *is* registered on the main
  generator (Pass 1.5), so it landed in the map with the IMPORTER's path and
  the MODULE's line/column.  In the fixtures below those coordinates point at
  a real-but-unrelated function in the importer — a backtrace that reads as
  correct and is not.

Same bug class as #1186 (imported ``[E602]``/``[E620]`` diagnostics carrying
the importer's path), which PR #1190 closed for the diagnostic surface only.
This file pins the source-map surface.

Fixtures deliberately split the two file names: the module is
``chinchilla.vera`` and the importer ``stargazer.vera``, so neither basename
can appear in the other's path and a frame's file attribution is decidable
from the string alone.  Every trap is a precondition violation, so the
``WasmTrapError.kind`` is pinned too and no unrelated failure mode can
satisfy these assertions.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from vera.checker import typecheck_with_artifacts
from vera.cli import cmd_run
from vera.codegen import CompileResult
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import WasmTrapError
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver

# ---------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------

_MODULE_NAME = "chinchilla.vera"
_IMPORTER_NAME = "stargazer.vera"

# `scaled` sits on module lines 1-5, `labelled` on lines 7-11.  The importer
# below is laid out so BOTH ranges also name a real function in ITS file —
# an entry stamped with the importer's path therefore reads as a plausible
# location instead of an obvious nonsense one.
_MODULE = """\
public fn scaled(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  @Int.0 * 2
}

public forall<T> fn labelled(@T, @Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  @Int.0 * 3
}
"""

# `let` (rather than a tail call) keeps the imported frame on the stack —
# a tail-position call is TCO'd away and the frame never reaches wasmtime's
# backtrace.  Mirrors `_DIVIDE_BY_ZERO_USER_FN` in test_runtime_traps.py.
_IMPORTER = """\
import chinchilla(scaled, labelled);

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Int = scaled(0 - 7);
  @Int.0
}

public fn generic_entry(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Int = labelled(true, 0 - 7);
  @Int.0
}
"""

# A local `scaled` shadows the import (spec §8.5.2), so the module's body is
# emitted under `mod$chinchilla$scaled` and reached by a qualified call.  The
# mangled name is its own `fn_source_map` key: the resolver's rightmost-`$`
# strip yields `mod$chinchilla`, which is nobody's entry.
_SHADOWING_IMPORTER = """\
import chinchilla(scaled);

private fn scaled(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  @Int.0
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Int = chinchilla::scaled(0 - 7);
  @Int.0
}
"""

# The over-correction control: a trap wholly inside the main file.  Green
# before AND after the #1189 fix — it exists to catch a fix that reattributes
# main-file entries to a module.
_MAIN_ONLY = """\
private fn scaled(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  @Int.0 * 2
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Int = scaled(0 - 7);
  @Int.0
}
"""


def _write(tmp_path: Path, files: dict[str, str]) -> Path:
    """Write *files* into *tmp_path*; return the importer's path."""
    for name, src in files.items():
        (tmp_path / name).write_text(src, encoding="utf-8")
    return tmp_path / _IMPORTER_NAME


def _frame_line(stderr: str, func: str) -> str:
    """The `  in <func>  (file:lines)` backtrace line for *func*.

    Asserting on the whole stderr blob would pass on the importer's path
    appearing in a DIFFERENT frame (`main` legitimately names it), so every
    file assertion below is made against one frame's own line.
    """
    needle = f"in {func}  "
    for line in stderr.splitlines():
        if line.strip().startswith(needle.strip()):
            return line
    raise AssertionError(
        f"no backtrace frame for {func!r} in:\n{stderr}"
    )


def _compile_files(
    tmp_path: Path, files: dict[str, str], main_name: str,
) -> CompileResult:
    """Compile *main_name* with its siblings resolvable as modules."""
    for name, src in files.items():
        (tmp_path / name).write_text(src, encoding="utf-8")
    main_path = tmp_path / main_name
    source = files[main_name]
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(program, main_path)
    assert not resolver.errors, (
        f"module resolution errors: "
        f"{[e.description for e in resolver.errors]}"
    )
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(main_path), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"typecheck errors: {[d.description for d in errors]}"
    return codegen_compile(
        program, source=source, file=str(main_path),
        resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )


# =====================================================================
# #1189 — the trap surface
# =====================================================================


class TestImportedTrapNamesTheModuleFile:
    """A trap inside an imported body reports the module's file."""

    def test_imported_fn_frame_names_the_module(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Pre-fix the `scaled` frame resolved to `<unknown>`."""
        path = _write(
            tmp_path,
            {_MODULE_NAME: _MODULE, _IMPORTER_NAME: _IMPORTER},
        )
        rc = cmd_run(str(path))
        err = capsys.readouterr().err

        assert rc != 0
        assert "Precondition violation" in err
        frame = _frame_line(err, "scaled")
        assert _MODULE_NAME in frame, (
            f"imported frame must name its module's file; got {frame!r}"
        )
        assert _IMPORTER_NAME not in frame, (
            f"imported frame must not name the importer; got {frame!r}"
        )
        # The caller's own frame is unaffected — it really is main-file code.
        assert _IMPORTER_NAME in _frame_line(err, "main")

    def test_imported_generic_clone_frame_names_the_module(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The literal #1189 repro: the clone carried the importer's path."""
        path = _write(
            tmp_path,
            {_MODULE_NAME: _MODULE, _IMPORTER_NAME: _IMPORTER},
        )
        rc = cmd_run(str(path), fn_name="generic_entry")
        err = capsys.readouterr().err

        assert rc != 0
        frame = _frame_line(err, "labelled$Bool")
        assert _MODULE_NAME in frame, (
            f"clone of an imported generic must name its defining module's "
            f"file; got {frame!r}"
        )
        assert _IMPORTER_NAME not in frame, (
            f"clone must not name the importer; got {frame!r}"
        )

    def test_shadowed_import_frame_names_the_module(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The `mod$…` emission of a locally-shadowed import (#814)."""
        path = _write(
            tmp_path,
            {_MODULE_NAME: _MODULE, _IMPORTER_NAME: _SHADOWING_IMPORTER},
        )
        rc = cmd_run(str(path))
        err = capsys.readouterr().err

        assert rc != 0
        frame = _frame_line(err, "mod$chinchilla$scaled")
        assert _MODULE_NAME in frame, (
            f"qualified module emission must name its module's file; "
            f"got {frame!r}"
        )
        assert _IMPORTER_NAME not in frame, (
            f"qualified module emission must not name the importer; "
            f"got {frame!r}"
        )

    def test_json_frames_carry_the_module_path_and_trap_kind(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Machine consumers see the same attribution, kind pinned."""
        path = _write(
            tmp_path,
            {_MODULE_NAME: _MODULE, _IMPORTER_NAME: _IMPORTER},
        )
        rc = cmd_run(str(path), as_json=True)
        out = capsys.readouterr().out

        assert rc != 0
        diag = json.loads(out)["diagnostics"][0]
        # Kind pinned: only a contract violation can satisfy this test.
        assert diag["trap_kind"] == "contract_violation"
        by_func = {f["func"]: f for f in diag["frames"]}
        assert by_func["scaled"]["file"].endswith(_MODULE_NAME), (
            f"expected the module file, got {by_func['scaled']['file']!r}"
        )
        assert by_func["scaled"]["is_builtin"] is False
        assert by_func["main"]["file"].endswith(_IMPORTER_NAME)

    def test_source_map_entry_is_the_module_file(
        self, tmp_path: Path,
    ) -> None:
        """Pin the map itself, not only its rendering."""
        result = _compile_files(
            tmp_path,
            {_MODULE_NAME: _MODULE, _IMPORTER_NAME: _IMPORTER},
            _IMPORTER_NAME,
        )
        assert "scaled" in result.fn_source_map, (
            "an imported function must have a source-map entry at all; "
            f"got keys {sorted(result.fn_source_map)}"
        )
        file_path, line_start, line_end = result.fn_source_map["scaled"]
        assert file_path.endswith(_MODULE_NAME), file_path
        # The coordinates were already module-local; only the file moves.
        assert (line_start, line_end) == (1, 5), (line_start, line_end)
        # `main` keeps the importer's file, byte-for-byte as before.
        main_file, _, _ = result.fn_source_map["main"]
        assert main_file.endswith(_IMPORTER_NAME), main_file

    def test_execute_trap_frames_name_the_module(
        self, tmp_path: Path,
    ) -> None:
        """The library surface (`execute`) carries the same attribution."""
        result = _compile_files(
            tmp_path,
            {_MODULE_NAME: _MODULE, _IMPORTER_NAME: _IMPORTER},
            _IMPORTER_NAME,
        )
        with pytest.raises(WasmTrapError) as excinfo:
            execute(result)
        exc = excinfo.value
        assert exc.kind == "contract_violation", exc.kind
        frames = {f.func: f for f in exc.frames}
        assert frames["scaled"].file.endswith(_MODULE_NAME), (
            frames["scaled"].file
        )


class TestMainFileTrapUnchanged:
    """Over-correction control — green BEFORE and AFTER the #1189 fix."""

    def test_main_file_trap_still_names_the_main_file(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A same-file trap keeps the main file's attribution."""
        path = tmp_path / _IMPORTER_NAME
        path.write_text(_MAIN_ONLY, encoding="utf-8")

        rc = cmd_run(str(path))
        err = capsys.readouterr().err

        assert rc != 0
        assert _MODULE_NAME not in err, (
            f"no module is involved here; got {err!r}"
        )
        for func in ("scaled", "main"):
            assert _IMPORTER_NAME in _frame_line(err, func)

    def test_main_file_source_map_is_the_main_file(
        self, tmp_path: Path,
    ) -> None:
        """The map's main-file entries are unchanged by the fix."""
        result = _compile_files(
            tmp_path, {_IMPORTER_NAME: _MAIN_ONLY}, _IMPORTER_NAME,
        )
        assert set(result.fn_source_map) == {"scaled", "main"}
        for name in ("scaled", "main"):
            assert result.fn_source_map[name][0] == str(
                tmp_path / _IMPORTER_NAME,
            )
