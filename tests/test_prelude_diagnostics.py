"""Tests for #851 — prelude combinator skip-warnings (E602/E604).

Two defects pinned here:

1. **Noise** — every compile of a program that pulls in the prelude
   used to emit five `[E602]`/`[E604]` warnings about the generic
   Option/Result combinators (``option_unwrap_or``, ``option_map``,
   ``option_and_then``, ``result_unwrap_or``, ``result_map``) being
   skipped, even when the program never referenced them.  Post-fix,
   skip-warnings for prelude-injected functions are suppressed unless
   the program actually references them (a transitive name-reference
   scan over user + imported declarations, rooted outside the prelude).

2. **Misattribution** — prelude-injected declarations carry spans from
   the synthetic prelude source buffer, and the diagnostic renderer
   used to resolve those line numbers against the *user's* file
   (quoting unrelated user source under a caret, or nothing when out
   of range).  Post-fix, prelude-origin diagnostics carry the
   synthetic file ``<prelude>`` and quote the prelude buffer's own
   source line, so no diagnostic can ever render user source for
   prelude code.

User-origin unsupported functions keep warning exactly as before,
with correct user-file locations (negative control below).
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from vera import ast
from vera.cli import cmd_compile
from vera.codegen import CodeGenerator
from vera.parser import parse
from vera.prelude import PRELUDE_FILE, inject_prelude
from vera.transform import transform

from tests.codegen_helpers import _compile, _compile_example, _compile_ok


# A minimal program that touches nothing from the prelude.
_MINIMAL_SRC = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  42
}
"""

# All five prelude Option/Result combinators that codegen skips at the
# template level (forall params / nested binding patterns).
_SKIPPED_PRELUDE_FNS = (
    "option_unwrap_or",
    "option_map",
    "option_and_then",
    "result_unwrap_or",
    "result_map",
)


def _warnings_for(result, fn_name: str):
    """Skip-warnings (E602/E604/E605) naming ``fn_name``."""
    return [
        d for d in result.diagnostics
        if d.severity == "warning"
        and d.error_code in {"E602", "E604", "E605"}
        and d.description.startswith(f"Function '{fn_name}' ")
    ]


class TestUnreferencedPreludeWarningsSuppressed:
    """#851 defect 1 — no skip-warning noise for prelude functions the
    program never references."""

    def test_minimal_program_compiles_with_zero_warnings(self) -> None:
        """The headline regression: a minimal program that never touches
        Option/Result compiles with ZERO warnings.

        Pre-#851 this emitted five E602/E604 warnings about the unused
        prelude combinators on every single compile.
        """
        result = _compile_ok(_MINIMAL_SRC)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert not warnings, (
            f"Expected zero warnings compiling a minimal program; got: "
            f"{[(d.error_code, d.description) for d in warnings]}"
        )

    def test_cli_compile_json_zero_warnings(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """`vera compile --json` on a minimal program reports an empty
        warnings array (the machine-readable half of the headline)."""
        src_path = tmp_path / "minimal.vera"
        src_path.write_text(_MINIMAL_SRC, encoding="utf-8")
        rc = cmd_compile(str(src_path), as_json=True)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is True
        assert data["warnings"] == [], (
            f"Expected empty warnings in --json output; got: "
            f"{data['warnings']}"
        )

    def test_program_calling_option_map_compiles_clean(self) -> None:
        """A program that successfully calls ``option_map`` (mono clone
        compiles) sees no warnings at all: the called combinator's
        template warning is suppressed by the #604 mono-compiled pass,
        and the four uncalled combinators by the #851 reachability
        pass."""
        result = _compile_example("closures.vera")
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert not warnings, (
            f"Expected zero warnings for closures.vera; got: "
            f"{[(d.error_code, d.description) for d in warnings]}"
        )


# A user forall-generic fn that references option_map but is never
# called: the mono collector only scans non-generic bodies, so
# option_map is referenced but never instantiated, and its template
# E602 skip-warning legitimately survives.  ``helper`` itself has a
# bare @T param, so it draws its own (user-origin) E604 warning.
_REFERENCED_NOT_INSTANTIATED_SRC = """\
private forall<T> fn helper(@T, @Option<Int> -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_map(@Option<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 + 1 })
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  42
}
"""


class TestReferencedPreludeWarningAttribution:
    """#851 defect 2 — when a prelude skip-warning IS emitted (the
    program references the skipped combinator), it is attributed to the
    synthetic ``<prelude>`` origin, never to the user's file."""

    def test_referenced_prelude_fn_still_warns(self) -> None:
        """Referencing a skipped prelude combinator keeps its warning —
        the honest signal that the function cannot compile — while the
        four unreferenced combinators stay silent."""
        result = _compile(_REFERENCED_NOT_INSTANTIATED_SRC)
        assert _warnings_for(result, "option_map"), (
            f"Expected the E602 skip-warning for the referenced "
            f"'option_map' to survive suppression; warnings: "
            f"{[d.description for d in result.diagnostics if d.severity == 'warning']}"
        )
        for name in _SKIPPED_PRELUDE_FNS:
            if name == "option_map":
                continue
            assert not _warnings_for(result, name), (
                f"Expected no warning for unreferenced prelude fn "
                f"'{name}'"
            )

    def test_prelude_warning_carries_prelude_origin(self) -> None:
        """The surviving option_map warning cites ``<prelude>``, not the
        user's file, and never quotes a user source line."""
        result = _compile(_REFERENCED_NOT_INSTANTIATED_SRC)
        [diag] = _warnings_for(result, "option_map")
        assert diag.location.file == PRELUDE_FILE, (
            f"Expected prelude-origin file {PRELUDE_FILE!r}; got "
            f"{diag.location.file!r}"
        )
        # No user source line may ever be quoted for prelude code.
        user_lines = {
            ln for ln in _REFERENCED_NOT_INSTANTIATED_SRC.splitlines() if ln
        }
        assert diag.source_line not in user_lines, (
            f"Prelude-origin warning quotes a user source line: "
            f"{diag.source_line!r}"
        )
        # The quoted line (when present) is real prelude source — it
        # comes from the option_map body in the injected buffer.
        if diag.source_line:
            assert "@A" in diag.source_line or "option_map" in diag.source_line, (
                f"Expected the quoted line to be prelude source from "
                f"option_map; got {diag.source_line!r}"
            )

    def test_prelude_origin_in_json_dict(self) -> None:
        """The JSON path (`to_dict`) carries the synthetic file too."""
        result = _compile(_REFERENCED_NOT_INSTANTIATED_SRC)
        [diag] = _warnings_for(result, "option_map")
        d = diag.to_dict()
        location = d["location"]
        assert isinstance(location, dict)
        assert location.get("file") == PRELUDE_FILE

    def test_reachability_scan_is_transitive(self) -> None:
        """The reference scan follows prelude-to-prelude calls: a user
        call to ``json_get_string`` marks its callees ``json_get`` and
        ``json_as_string`` referenced too, while the uncalled
        Option/Result combinators stay unreferenced."""
        src = """\
private fn get_name(@Json -> @Option<String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  json_get_string(@Json.0, "name")
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  42
}
"""
        user_fn_names = {"get_name", "main"}
        program = transform(parse(src))
        inject_prelude(program)
        gen = CodeGenerator(source=src, file="test.vera")
        gen._prelude_fn_names = {
            tld.decl.name
            for tld in program.declarations
            if isinstance(tld.decl, ast.FnDecl)
            and tld.decl.name not in user_fn_names
        }
        referenced = gen._referenced_prelude_fns(program)
        assert "json_get_string" in referenced
        assert "json_get" in referenced, (
            "Transitive reference (json_get_string -> json_get) missed"
        )
        assert "json_as_string" in referenced
        for name in _SKIPPED_PRELUDE_FNS:
            assert name not in referenced, (
                f"'{name}' wrongly marked referenced"
            )

    def test_user_unsupported_fn_warns_with_user_location(self) -> None:
        """Negative control: a USER function skipped by codegen keeps
        warning exactly as before, attributed to the user's file with
        the user's own source line quoted."""
        result = _compile(_REFERENCED_NOT_INSTANTIATED_SRC)
        [diag] = _warnings_for(result, "helper")
        assert diag.location.file != PRELUDE_FILE
        assert diag.location.file and diag.location.file.endswith(".vera")
        assert diag.location.line == 1, (
            f"Expected the helper E604 to cite line 1 of the user "
            f"file; got line {diag.location.line}"
        )
        assert "fn helper" in diag.source_line, (
            f"Expected the user's own declaration line to be quoted; "
            f"got {diag.source_line!r}"
        )
