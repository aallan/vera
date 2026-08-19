"""#1312: an entry-file `data` declaration must not silently evict a module's.

Sibling of `test_prelude_adt_namespace_1277.py`'s contention rail (E621),
for the pair that rail cannot see. `_contends_with_prelude` compares an
IMPORTED module's declaration against the prelude's; an entry-file
declaration suppresses the prelude's own injection outright (spec §8.4.1),
so a contention between the entry file and an imported module never
reaches Pass 1.2, where E621 is decided.

Pass 0.5 (`_register_modules`) harvests an imported module's ADT layouts
into `_adt_layouts` via `setdefault`, recording the owner in
`_adt_layout_owners`. Pass 1 (`_register_all` -> `_register_data`) then
registers the entry file's own `data` declarations UNCONDITIONALLY, no
shape check, so an entry declaration sharing a module's ADT name but
describing a different layout silently takes the one registered slot: the
module's own constructors become `unknown constructor` inside its own
bodies (E602), the functions that use them are dropped (E620), all of it
reported only as warnings, and the artifact compiles with exit 0 missing
its entry point.
"""

from __future__ import annotations

from pathlib import Path

from vera.codegen.core import CodeGenerator
from vera.errors import ERROR_CODES
from vera.parser import parse_file
from vera.resolver import ModuleResolver
from vera.transform import transform

# The module's own `data Json`, used by its own function.
_JLIB_OWN_JSON = """
private data Json {
  JBlob(Int)
}

public fn blob_size(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match JBlob(@Int.0) {
    JBlob(@Int) -> @Int.0
  }
}
"""

# The entry declares its OWN, differently-shaped `data Json`.
_MAIN_DIFFERING_JSON = """
import jlib(blob_size);

private data Json {
  JMine(Int)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  blob_size(7)
}
"""

# The entry declares the module's OWN shape back: one layout serves both.
_MAIN_RESTATING_JSON = """
import jlib(blob_size);

private data Json {
  JBlob(Int)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  blob_size(7)
}
"""

# The entry never declares `Json` at all: no contention, nothing to check.
_MAIN_NO_JSON = """
import jlib(blob_size);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  blob_size(7)
}
"""


def _compile(tmp_path: Path, files: dict[str, str]) -> CodeGenerator:
    """Write *files*, compile ``main.vera``, hand back the generator."""
    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    program = transform(parse_file(str(main_path)))
    mods = ModuleResolver(tmp_path).resolve_imports(program, main_path)
    gen = CodeGenerator(
        source=main_path.read_text(encoding="utf-8"), file=str(main_path),
    )
    gen._resolved_modules = mods
    gen._result = gen.compile_program(program)  # type: ignore[attr-defined]
    return gen


def test_a_differing_entry_declaration_is_loud(tmp_path: Path) -> None:
    """The measured shape: E602/E620 warnings and a silently missing `main`.

    At the branch point this program is `vera check`-green and compiles
    with exit 0, only warnings (`unknown constructor 'JBlob'` inside
    `blob_size`, then `main` dropped behind it), and `exports == []`. The
    assertions below are the three things that were wrong: the severity,
    the file the diagnostic points at, and whether the artifact is
    produced at all.
    """
    gen = _compile(
        tmp_path,
        {"jlib.vera": _JLIB_OWN_JSON, "main.vera": _MAIN_DIFFERING_JSON},
    )
    result = gen._result  # type: ignore[attr-defined]
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert len(errors) == 1, [
        (d.severity, d.error_code, d.description) for d in result.diagnostics
    ]
    err = errors[0]
    assert err.error_code == "E622", err.error_code
    # Located at the ENTRY's declaration, in the entry file: `main.vera`
    # line 4, where `private data Json` is written.
    assert Path(err.location.file).name == "main.vera", err.location.file
    assert err.location.line == 4, (err.location.line, err.source_line)
    assert "data Json" in err.source_line, err.source_line
    assert "Json" in err.description and "jlib" in err.description, (
        err.description)
    assert err.fix and err.rationale and err.spec_ref
    assert result.exports == [], result.exports


def test_the_cli_refuses_rather_than_compiling_silently(tmp_path: Path) -> None:
    """`vera compile` exits non-zero on the contention shape.

    The whole point of the rail is the exit code: at the branch point
    every diagnostic here is a warning, so `cmd_compile` returned 0 over a
    module missing its entry point.
    """
    from vera.cli import cmd_check, cmd_compile

    tmp_path.mkdir(parents=True, exist_ok=True)
    (tmp_path / "jlib.vera").write_text(_JLIB_OWN_JSON, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    main_path.write_text(_MAIN_DIFFERING_JSON, encoding="utf-8")
    # This is a codegen-namespace collision, not a type error: the
    # checker gives both namespaces their own view and stays green.
    assert cmd_check(str(main_path), quiet=True) == 0
    assert cmd_compile(str(main_path), wat=True) == 1


def test_restating_the_module_shape_is_not_a_contention(tmp_path: Path) -> None:
    """One registered layout is correct for both declarations: legal.

    Green before and after: this is what separates "refuse a contention"
    from "reserve the module's names", the shape §8.4.1 sanctions.
    """
    gen = _compile(
        tmp_path,
        {"jlib.vera": _JLIB_OWN_JSON, "main.vera": _MAIN_RESTATING_JSON},
    )
    result = gen._result  # type: ignore[attr-defined]
    assert [d for d in result.diagnostics if d.severity == "error"] == []
    assert result.exports == ["main"], result.exports
    assert sorted(gen._adt_layouts["Json"]) == ["JBlob"]


def test_an_entry_that_never_declares_the_name_is_unaffected(
    tmp_path: Path,
) -> None:
    """No entry-file declaration of the name: nothing to compare, no rail."""
    gen = _compile(
        tmp_path,
        {"jlib.vera": _JLIB_OWN_JSON, "main.vera": _MAIN_NO_JSON},
    )
    result = gen._result  # type: ignore[attr-defined]
    assert [d for d in result.diagnostics if d.severity == "error"] == []
    assert result.exports == ["main"], result.exports
    assert sorted(gen._adt_layouts["Json"]) == ["JBlob"]


def test_e622_is_registered() -> None:
    """The code the rail emits exists in the registry `vera errors` reads."""
    assert "E622" in ERROR_CODES
    assert ERROR_CODES["E622"]
