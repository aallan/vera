"""#1183 + #1186 — a dropped entry function must never be silently replaced.

#1183: the #1100 skip propagation drops a check-/verify-clean function whose
callee could not be compiled ([E602] root, [E620] caller drop).  When the
DECLARED entry (``main``, or an explicit ``--fn``) was one of the dropped
functions and any public sibling survived, ``execute()`` fell through to
``result.exports[0]`` and ``vera run`` printed the SIBLING'S result with exit
0 and empty stderr — a silent wrong answer, the one outcome the loud-skip
design exists to prevent.  Post-fix the entry drop is a refusal; auto-selection
survives only where no ``main`` was ever declared, and announces itself.

#1186: the root ``[E602]`` for an IMPORTED function body carried the MAIN
file's path with the MODULE's line/column, so the rendered source line quoted
whatever happened to sit at that line in the importer.  It also kept the
cross-file branch in ``_drop_dangling_callers`` permanently dark: the [E620]
caller message compared ``root_diag.location.file`` against the main file and
always matched, so the module context never reached the user.

Fixtures use a ``Map<String, Array<Int>>`` value (an unsupported host-import
shape) as the root [E602] trigger.  Every surviving sibling returns 4243 — a
value no fallback, default, or error path produces — so "the sibling did not
run" is decidable from the output alone.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from vera.cli import cmd_compile, cmd_run, cmd_test
from vera.codegen import execute
from tests.module_fixture_helpers import compile_multi_module as _compile_files

# ---------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------

# `main` calls a helper codegen cannot compile, so `main` is dropped;
# `survivor` is outside the doomed subgraph and keeps its export.
_MAIN_DROPPED_SIBLING_SURVIVES = """\
private fn tally(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Array<Int>> = map_insert(map_new(), "a", [1, 2]);
  map_size(@Map<String, Array<Int>>.0)
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  tally()
}

public fn survivor(-> @Int) requires(true) ensures(true) effects(pure) {
  4243
}
"""

# No `main` anywhere: the single-public-export convenience path.
_NO_MAIN_SINGLE_EXPORT = """\
public fn only_one(-> @Int) requires(true) ensures(true) effects(pure) {
  4243
}
"""

# Every public function is dropped -> the module exports nothing.
_ALL_EXPORTS_DROPPED = """\
private fn tally(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Array<Int>> = map_insert(map_new(), "a", [1, 2]);
  map_size(@Map<String, Array<Int>>.0)
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  tally()
}
"""

# A PUBLIC function with a Tier 3 contract whose body is dropped: reaches
# the tester's export check (the trivial-contract filter would otherwise
# short-circuit it).
_TIER3_PUBLIC_DROPPED = """\
public fn tally(@Int -> @Int) requires(@Int.0 > 0) ensures(@Int.0 >= 0) effects(pure) {
  let @Map<String, Array<Int>> = map_insert(map_new(), "a", [1, 2]);
  map_size(@Map<String, Array<Int>>.0) + @Int.0
}
"""

# #1186: the unsupported construct lives in the imported module, the entry
# in the importer.  The `Map<String, Array<Int>>` host-import shape (the
# same trigger the sibling fixtures use) is not compilable, so `helper` is
# [E602]-skipped in om.vera and `main` is [E620]-dropped in appmain.vera.
# (The original trigger — `option_map` under a colliding `OptionMapFn`
# alias — stopped BEING a trigger when #1184 fixed that collision, which
# is the improvement it exists to deliver; the location tests only need
# any imported [E602], so they use the stable trigger.)
_MODULE_WITH_DROPPED_BODY = """\
public fn helper(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Array<Int>> = map_insert(map_new(), "a", [1, 2]);
  map_size(@Map<String, Array<Int>>.0) + @Int.0
}
"""

_MAIN_IMPORTING_DROPPED_BODY = """\
import om(helper);

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  helper(21)
}
"""


def _write(tmp_path: Path, name: str, source: str) -> str:
    path = tmp_path / name
    path.write_text(source, encoding="utf-8")
    return str(path)


# =====================================================================
# #1183 — `vera run` refuses a dropped entry
# =====================================================================


class TestRunRefusesDroppedEntry:
    """A DECLARED-but-dropped entry is an error, never a substitution."""

    def test_dropped_main_never_runs_the_sibling(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The #1183 repro: exit nonzero, name `main`, never print 4243."""
        path = _write(
            tmp_path, "survivor.vera", _MAIN_DROPPED_SIBLING_SURVIVES,
        )
        rc = cmd_run(path)
        captured = capsys.readouterr()
        assert rc != 0, "a dropped entry must not exit 0"
        assert "4243" not in captured.out, (
            "the surviving sibling's body must never execute in place of "
            f"the declared entry (stdout was {captured.out!r})"
        )
        assert "main" in captured.err
        # The refusal must carry the ROOT reason, not just "not found".
        assert "E620" in captured.err or "E602" in captured.err
        # ...and the notes precede it, so the root [E602]'s own wording is
        # visible, not only the location its [E620] quotes.
        assert "Compilation notes" in captured.err
        assert "tally" in captured.err

    def test_explicit_fn_dropped_is_refused_with_root_reason(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """`--fn main` on a dropped `main` names why it is gone."""
        path = _write(
            tmp_path, "survivor.vera", _MAIN_DROPPED_SIBLING_SURVIVES,
        )
        rc = cmd_run(path, fn_name="main")
        captured = capsys.readouterr()
        assert rc != 0
        assert "4243" not in captured.out
        assert "main" in captured.err
        assert "E620" in captured.err or "E602" in captured.err
        assert "dropped" in captured.err.lower()

    def test_dropped_entry_json_is_not_ok(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """JSON mode reports ok: false with the drop reason."""
        path = _write(
            tmp_path, "survivor.vera", _MAIN_DROPPED_SIBLING_SURVIVES,
        )
        rc = cmd_run(path, as_json=True)
        out = capsys.readouterr().out
        assert rc != 0
        data = json.loads(out)
        assert data["ok"] is False
        assert "4243" not in json.dumps(data.get("value"))
        assert any(
            "main" in d["description"] for d in data["diagnostics"]
        )
        # The notes reach machine consumers under `warnings`, mirroring
        # the stderr block text mode prints.
        codes = {w.get("error_code") for w in data["warnings"]}
        assert {"E602", "E620"} <= codes

    def test_compilation_notes_shown_when_a_sibling_survives(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The notes block is no longer gated on an empty export list."""
        path = _write(
            tmp_path, "survivor.vera", _MAIN_DROPPED_SIBLING_SURVIVES,
        )
        cmd_run(path, fn_name="survivor")
        captured = capsys.readouterr()
        assert "Compilation notes" in captured.err, (
            "E602/E620 diagnostics must surface even when exports survive"
        )
        # The sibling was explicitly requested, so it DOES run here.
        assert "4243" in captured.out

    def test_library_execute_refuses_silent_substitution(
        self, tmp_path: Path,
    ) -> None:
        """``execute()`` itself must not fall through to exports[0]."""
        result = _compile_files(
            tmp_path,
            {"survivor.vera": _MAIN_DROPPED_SIBLING_SURVIVES},
            "survivor.vera",
        )
        assert "main" not in result.exports
        assert "survivor" in result.exports
        with pytest.raises(RuntimeError, match="main") as excinfo:
            execute(result)
        # Exact type, not a subclass: WasmTrapError extends RuntimeError,
        # so a runtime trap whose message mentions 'main' must not be able
        # to satisfy this test in place of the refusal (PR #1190 review).
        assert type(excinfo.value) is RuntimeError, type(excinfo.value)

    def test_compile_result_records_dropped_entry(
        self, tmp_path: Path,
    ) -> None:
        """The drop is reified on CompileResult, not re-derived by callers."""
        result = _compile_files(
            tmp_path,
            {"survivor.vera": _MAIN_DROPPED_SIBLING_SURVIVES},
            "survivor.vera",
        )
        assert "main" in result.dropped_fns
        assert "survivor" not in result.dropped_fns
        reason = result.dropped_fns["main"]
        assert reason is not None
        assert reason.error_code in {"E602", "E620"}


# =====================================================================
# #1183 — auto-selection survives only for the never-declared case
# =====================================================================


class TestAutoSelectionAnnouncesItself:
    """No `main` declared: the convenience path stays, but says so."""

    def test_single_public_export_auto_selected_with_note(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, "single.vera", _NO_MAIN_SINGLE_EXPORT)
        rc = cmd_run(path)
        captured = capsys.readouterr()
        assert rc == 0
        assert "4243" in captured.out, "the single export must still run"
        assert "only_one" in captured.err, (
            "an auto-selected entry must be named on stderr"
        )

    def test_note_is_one_line(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, "single.vera", _NO_MAIN_SINGLE_EXPORT)
        cmd_run(path)
        err = capsys.readouterr().err.strip()
        assert "only_one" in err, "the note itself must be present"
        assert err.count("\n") == 0, f"note must be one line, got {err!r}"

    def test_json_mode_reports_the_selected_function(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, "single.vera", _NO_MAIN_SINGLE_EXPORT)
        rc = cmd_run(path, as_json=True)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert data["function"] == "only_one"


# =====================================================================
# #1183 — sibling surfaces: compile / browser bundle
# =====================================================================


class TestCompileZeroExports:
    """A module with no callable entry point is a failed compile."""

    def test_zero_exports_exits_nonzero_with_notes(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, "allgone.vera", _ALL_EXPORTS_DROPPED)
        rc = cmd_compile(path, output=str(tmp_path / "out.wasm"))
        captured = capsys.readouterr()
        assert rc != 0, "0 exported functions is not a successful compile"
        assert "E602" in captured.err or "E620" in captured.err, (
            "the drop diagnostics must be shown alongside the failure"
        )

    def test_zero_exports_json_is_not_ok(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, "allgone.vera", _ALL_EXPORTS_DROPPED)
        rc = cmd_compile(
            path, as_json=True, output=str(tmp_path / "out.wasm"),
        )
        assert rc != 0
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert data["diagnostics"], "the failure must carry a diagnostic"

    def test_browser_bundle_refuses_dropped_main(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """index.html hardcodes call('main') — never emit it for a drop.

        Deliberately uses the SURVIVING-sibling fixture: with a non-empty
        export list the zero-exports check above cannot fire, so a pass
        here can only come from the browser path's own refusal.
        """
        path = _write(
            tmp_path, "survivor.vera", _MAIN_DROPPED_SIBLING_SURVIVES,
        )
        out_dir = tmp_path / "bundle"
        rc = cmd_compile(path, target="browser", output=str(out_dir))
        assert rc != 0
        assert not (out_dir / "index.html").exists(), (
            "a bundle whose entry does not exist must not be written"
        )

    def test_browser_bundle_refuses_never_declared_main(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """No `main` declared at all: the bundle is equally unusable.

        PR #1190 review finding: the dropped-main guard keyed on
        ``dropped_fns``, so a file that never declared ``main`` (with
        another public export) still emitted an index.html whose
        ``call('main')`` fails at page load.  The guard keys on
        ``"main" not in result.exports`` now — the never-declared and
        dropped cases refuse alike, with case-accurate messages.
        """
        src = (
            "public fn solo(-> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  99\n"
            "}\n"
        )
        path = _write(tmp_path, "nomain.vera", src)
        out_dir = tmp_path / "bundle_nomain"
        rc = cmd_compile(path, target="browser", output=str(out_dir))
        captured = capsys.readouterr()
        assert rc != 0, "a bundle that cannot call main() is not a success"
        assert "no 'main' function is exported" in captured.err
        assert "solo" in captured.err, "the exports must be named"
        assert not (out_dir / "index.html").exists()

    def test_browser_refusal_json_reports_not_ok(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """`--json` agents get `ok: false` + the export name (PR #1190).

        Pins the JSON envelope of the browser refusal through the shared
        `_report_compile_failure` helper, so a future change to that
        envelope is caught on this documented agent-facing path.
        """
        src = (
            "public fn solo(-> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  99\n"
            "}\n"
        )
        path = _write(tmp_path, "nomain_json.vera", src)
        out_dir = tmp_path / "bundle_nomain_json"
        rc = cmd_compile(
            path, target="browser", output=str(out_dir), as_json=True,
        )
        captured = capsys.readouterr()
        assert rc != 0
        data = json.loads(captured.out)
        assert data["ok"] is False
        assert "solo" in data["diagnostics"][0]["description"], (
            "the JSON diagnostic must name what IS exported"
        )
        assert not (out_dir / "index.html").exists()

    def test_browser_refusal_json_dropped_main(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """JSON mode for the DROPPED-main browser refusal (PR #1190 review).

        Complements the never-declared JSON pin above by exercising the
        `result.dropped_fns` arm: the diagnostic quotes the dropped entry,
        and the warnings array preserves the [E602] root and the [E620]
        drop, so a JSON consumer can reconstruct the chain.
        """
        path = _write(
            tmp_path, "survivor_json.vera", _MAIN_DROPPED_SIBLING_SURVIVES,
        )
        out_dir = tmp_path / "bundle_dropped_json"
        rc = cmd_compile(
            path, target="browser", output=str(out_dir), as_json=True,
        )
        captured = capsys.readouterr()
        assert rc != 0
        data = json.loads(captured.out)
        assert data["ok"] is False
        assert "main" in data["diagnostics"][0]["description"]
        codes = {w.get("error_code") for w in data["warnings"]}
        assert "E602" in codes, codes
        assert "E620" in codes, codes
        assert not (out_dir / "index.html").exists()


# =====================================================================
# #1186 — imported bodies locate in their own module
# =====================================================================


class TestImportedDiagnosticLocation:
    """The [E602] root of an imported body belongs to the module file."""

    def test_root_e602_carries_the_module_path(self, tmp_path: Path) -> None:
        result = _compile_files(
            tmp_path,
            {
                "om.vera": _MODULE_WITH_DROPPED_BODY,
                "appmain.vera": _MAIN_IMPORTING_DROPPED_BODY,
            },
            "appmain.vera",
        )
        roots = [d for d in result.diagnostics if d.error_code == "E602"]
        assert roots, "expected the imported body to be skipped"
        root = roots[0]
        assert Path(root.location.file).name == "om.vera", (
            f"imported [E602] must locate in its own module, got "
            f"{root.location.file!r}"
        )
        # Module-local coordinates are retained, not remapped.
        assert root.location.line == 2
        assert root.location.column == 34

    def test_root_e602_quotes_the_module_source_line(
        self, tmp_path: Path,
    ) -> None:
        result = _compile_files(
            tmp_path,
            {
                "om.vera": _MODULE_WITH_DROPPED_BODY,
                "appmain.vera": _MAIN_IMPORTING_DROPPED_BODY,
            },
            "appmain.vera",
        )
        root = next(
            d for d in result.diagnostics if d.error_code == "E602"
        )
        assert "map_insert" in root.source_line, (
            f"rendered source line came from the wrong file: "
            f"{root.source_line!r}"
        )

    def test_e620_message_carries_the_cross_file_prefix(
        self, tmp_path: Path,
    ) -> None:
        """The dark branch in ``_drop_dangling_callers`` must now fire."""
        result = _compile_files(
            tmp_path,
            {
                "om.vera": _MODULE_WITH_DROPPED_BODY,
                "appmain.vera": _MAIN_IMPORTING_DROPPED_BODY,
            },
            "appmain.vera",
        )
        e620s = [d for d in result.diagnostics if d.error_code == "E620"]
        assert e620s, "expected `main` to be dropped as a dangling caller"
        msg = e620s[0].description
        root = next(d for d in result.diagnostics if d.error_code == "E602")
        # Derived from the root rather than rebuilt from tmp_path: macOS
        # resolves /var -> /private/var, and the point being pinned is
        # that the E620 quotes the ROOT's file, whatever spelling it has.
        assert Path(root.location.file).name == "om.vera"
        assert f"at {root.location.file}, line 2, column 34" in msg, (
            f"E620 must name the module the root came from, got {msg!r}"
        )

    def test_same_file_drop_keeps_the_bare_location(
        self, tmp_path: Path,
    ) -> None:
        """No regression: a main-file root has no file prefix."""
        result = _compile_files(
            tmp_path,
            {"survivor.vera": _MAIN_DROPPED_SIBLING_SURVIVES},
            "survivor.vera",
        )
        e620s = [d for d in result.diagnostics if d.error_code == "E620"]
        assert e620s
        assert "at line 2, column 3" in e620s[0].description


# =====================================================================
# #1186 — `vera test` names the real skip reason
# =====================================================================


class TestTesterSkipReason:
    """A dropped PUBLIC function is not "private"."""

    def test_dropped_public_fn_is_not_labelled_private(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, "t3.vera", _TIER3_PUBLIC_DROPPED)
        cmd_test(path)
        out = capsys.readouterr().out
        assert "tally" in out
        assert "(private)" not in out, (
            f"a public-but-dropped fn must not be called private: {out!r}"
        )
        assert "E602" in out
        assert "dropped by codegen" in out

    def test_dropped_public_fn_json_reason_names_the_root(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _write(tmp_path, "t3.vera", _TIER3_PUBLIC_DROPPED)
        cmd_test(path, as_json=True)
        data = json.loads(capsys.readouterr().out)
        entry = next(f for f in data["functions"] if f["name"] == "tally")
        assert entry["category"] == "skipped"
        assert "(private)" not in entry["reason"]
        assert "[E602]" in entry["reason"]
        # Same-file root: no redundant path prefix, matching [E620].
        assert str(tmp_path) not in entry["reason"]
