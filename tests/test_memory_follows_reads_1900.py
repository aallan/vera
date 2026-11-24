"""A module declares memory when it holds a memory instruction, and every
artifact the compiler builds is validated where it is built (#1900).

The memory declaration was decided by a flag that the sites deciding
allocation, host rows and memory effects set.  The instructions that read
memory set nothing, so a module whose only heap contact was a read of a
parameter (a `match` on an `Option`, a tuple destructured, an ADT `==`)
held `i32.load` and no `(memory ...)`.  Assembly could not catch it: a
load names memory 0 implicitly, and `wat2wasm` resolves names without
validating.  The module was written with exit 0 and no loader accepted it.

The declaration is now derived from the assembled text
(`holds_memory_instruction`), and the module is validated right after
assembly (`vera/codegen/validation.py`): a module that does not validate is
an E699 and no bytes, so nothing is written.  The wasi-p2 component, the
other artifact the compiler builds, is checked by constructing it where it
is built.

The matrix is every reader shape (each a function whose only heap contact
is a read of its parameter) by every context it is compiled in: exported
alone, beside a `main` that allocates nothing, and called from a `main`
that builds its argument.  Each cell asserts the module validates and
declares memory, and runs where it can be called.
"""

from __future__ import annotations

import json
from collections.abc import Callable
from pathlib import Path

import pytest
import wasmtime

from tests import pipeline
from vera.codegen import CompileResult
from vera.codegen.assembly import holds_memory_instruction

pytestmark = pytest.mark.matrix(decides=[
    "vera/codegen/assembly.py", "vera/codegen/validation.py",
    "vera/codegen/core.py", "vera/cli.py",
])

_C = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

#: Each reader: its declarations (a function `f` whose only heap contact is
#: a read of its parameter), a call of `f` from a `main` that builds the
#: argument, and the value that call returns.  No expected value is 0 or 1,
#: the values a wrong arm or a Bool default would give.
READERS: dict[str, tuple[str, str, int]] = {
    "option_match": (
        "public fn f(@Option<Int>, @Int -> @Int)\n" + _C
        + "{\n  match @Option<Int>.0 {\n    None -> @Int.0,\n"
        "    Some(@Int) -> @Int.0\n  }\n}\n",
        "f(Some(3), 7)", 3),
    "result_match": (
        "public fn f(@Result<Int, Bool> -> @Int)\n" + _C
        + "{\n  match @Result<Int, Bool>.0 {\n    Ok(@Int) -> @Int.0,\n"
        "    Err(@Bool) -> 9\n  }\n}\n",
        "f(Ok(5))", 5),
    "tuple": (
        "public fn f(@Tuple<Int, Int> -> @Int)\n" + _C
        + "{\n  match @Tuple<Int, Int>.0 {\n"
        "    Tuple(@Int, @Int) -> @Int.1\n  }\n}\n",
        "f(Tuple(4, 9))", 4),
    "adt_equality": (
        "public fn f(@Option<Int>, @Option<Int> -> @Bool)\n" + _C
        + "{\n  @Option<Int>.0 == @Option<Int>.1\n}\n",
        "if f(Some(2), Some(3)) then { 5 } else { 6 }", 6),
    "nested_match": (
        "public fn f(@Option<Option<Int>> -> @Int)\n" + _C
        + "{\n  match @Option<Option<Int>>.0 {\n    None -> 2,\n"
        "    Some(@Option<Int>) -> match @Option<Int>.0 {\n"
        "      None -> 3,\n      Some(@Int) -> @Int.0\n    }\n  }\n}\n",
        "f(Some(Some(8)))", 8),
    "private_reader": (
        "private fn g(@Option<Int> -> @Int)\n" + _C
        + "{\n  match @Option<Int>.0 {\n    None -> 2,\n"
        "    Some(@Int) -> @Int.0\n  }\n}\n\n"
        "public fn f(@Option<Int> -> @Int)\n" + _C
        + "{\n  g(@Option<Int>.0) + 1\n}\n",
        "f(Some(3))", 4),
    "user_data": (
        "private data Shape {\n  Circle(Int),\n  Square(Int)\n}\n\n"
        "public fn f(@Shape -> @Int)\n" + _C
        + "{\n  match @Shape.0 {\n    Circle(@Int) -> @Int.0,\n"
        "    Square(@Int) -> @Int.0\n  }\n}\n",
        "f(Square(6))", 6),
}

CONTEXTS = ("export_only", "main_allocates_nothing", "main_builds")


def _source(reader: str, context: str) -> str:
    decls, call, _ = READERS[reader]
    if context == "export_only":
        return decls
    body = "42" if context == "main_allocates_nothing" else call
    return decls + "\npublic fn main(-> @Int)\n" + _C + "{\n  " + body + "\n}\n"


def _engine() -> wasmtime.Engine:
    config = wasmtime.Config()
    config.wasm_exceptions = True
    return wasmtime.Engine(config)


def _compiled(source: str) -> CompileResult:
    result = pipeline.compile(source, file="fixture.vera").result
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, [d.description for d in errors]
    return result


@pytest.mark.parametrize("context", CONTEXTS)
@pytest.mark.parametrize("reader", sorted(READERS))
def test_a_module_that_reads_the_heap_declares_memory_and_loads(
    reader: str, context: str,
) -> None:
    result = _compiled(_source(reader, context))
    assert holds_memory_instruction(result.wat)
    assert '(memory (export "vera.memory")' in result.wat
    wasmtime.Module.validate(_engine(), result.wasm_bytes)
    if context != "export_only":
        expected = 42 if context == "main_allocates_nothing" else READERS[reader][2]
        assert pipeline.run(result, "main").execution.value == expected


# =====================================================================
# The reported instance
# =====================================================================

_UNWRAP_OR = (
    "public fn unwrap_or(@Option<Int>, @Int -> @Int)\n" + _C
    + "{\n  match @Option<Int>.0 {\n    None -> @Int.0,\n"
    "    Some(@Int) -> @Int.0\n  }\n}\n"
)


def test_repro_1900_unwrap_or_declares_memory_and_validates() -> None:
    """The issue's program: two loads, and at base no `(memory ...)`."""
    result = _compiled(_UNWRAP_OR)
    assert '(memory (export "vera.memory") 1)' in result.wat
    wasmtime.Module.validate(_engine(), result.wasm_bytes)
    # It loads, and an embedder can call it: a `None` is a tag-0 word.
    store = wasmtime.Store(_engine())
    instance = wasmtime.Instance(
        store, wasmtime.Module(store.engine, result.wasm_bytes), [])
    unwrap_or = instance.exports(store)["unwrap_or"]
    assert isinstance(unwrap_or, wasmtime.Func)
    assert unwrap_or(store, 1024, 7) == 7


# =====================================================================
# The host reaches memory only through what the module holds
# =====================================================================

def test_a_memory_effect_declares_memory_with_no_instruction() -> None:
    """The host contract: an `IO` row declares the module's memory whatever
    its code holds, as it did before #1900 (`tests/conformance/
    ch07_io_sleep.vera` is such a module).  The module holds no memory
    instruction and no string, so only the row's flag declares it."""
    result = _compiled(
        "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
        "  effects(<IO>)\n{\n  IO.exit(3)\n}\n")
    assert not holds_memory_instruction(result.wat)
    assert "(data" not in result.wat
    assert '(memory (export "vera.memory") 1)' in result.wat
    assert pipeline.run(result, "main", []).execution.exit_code == 3


def test_a_string_the_host_writes_is_held_in_declared_memory() -> None:
    """`IO.read_line`'s host writes the line into the module's memory
    through `$alloc`, whose text declares it; the module reads only the
    pair's length."""
    result = _compiled(
        "public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(<IO>)\n{\n  let @String = IO.read_line(());\n"
        "  string_length(@String.0)\n}\n")
    assert '(memory (export "vera.memory") 1)' in result.wat
    assert pipeline.run(
        result, "main", [], stdin="hello\n").execution.value == 5


# =====================================================================
# The scan reads instructions, not text that looks like them
# =====================================================================

@pytest.mark.parametrize("text", [
    "i32.load", "i64.load offset=8", "f64.load align=4", "i32.load8_u",
    "i64.load32_s", "i32.store", "i64.store offset=8", "f32.store",
    "i32.store8", "i64.store16", "memory.size", "memory.grow",
    "memory.copy", "memory.fill",
])
def test_the_scan_finds_every_memory_instruction(text: str) -> None:
    assert holds_memory_instruction(f"(func $f\n    local.get 0\n    {text}\n  )")


@pytest.mark.parametrize("text", [
    ";; i32.load from a comment",
    "(; i64.store in a block comment ;)",
    "(;\n  memory.grow over two lines\n;)",
    "call $f.i32.load",
    "call $i32.load",
    "global.get $memory.size",
    '(data (i32.const 0) "i32.load")',
    '(export "memory.size" (func $g))',
    "i32.const 0\n    drop",
])
def test_the_scan_ignores_text_that_only_looks_like_one(text: str) -> None:
    assert not holds_memory_instruction(f"(func $f\n    {text}\n  )")


def test_repro_the_scan_reads_each_token_whole() -> None:
    """The scan's boundaries, unparametrised so every run holds them: a
    string is read past an escaped quote, a `$name` past its first
    character (a user function's name starts `$:`), a block comment to its
    own `;)` and no further, and an instruction is a whole token, neither
    the tail nor the head of a longer word.  The instruction families no
    corpus module holds yet are found too."""
    def wat(text: str) -> str:
        return f"(func $f\n    {text}\n  )"

    for text in ('(data (i32.const 0) "a\\" i32.load \\"b")',
                 "call $:i32.load",
                 "nopi32.load", "x.i32.load",
                 "memory.sizes", "memory.size.x"):
        assert not holds_memory_instruction(wat(text)), text
    for text in ("(; a ;) i32.load (; b ;)",
                 "v128.load", "v128.store", "memory.init 0", "data.drop 0"):
        assert holds_memory_instruction(wat(text)), text


def test_repro_a_host_row_that_reads_no_memory_declares_none() -> None:
    """`Random.random_int` passes and returns scalars: its row asks for no
    memory, and a module whose only host contact it is declares none."""
    result = _compiled(
        "public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(<Random>)\n{\n  Random.random_int(1, 6)\n}\n")
    assert '"random_int"' in result.wat
    assert "(memory" not in result.wat
    wasmtime.Module.validate(_engine(), result.wasm_bytes)


def test_repro_every_host_row_that_asks_for_memory_allocates() -> None:
    """A host row's `needs_memory` is implied by its `needs_alloc`: the
    allocator a row brings in holds loads and stores, so its memory is
    declared from the text whatever the row says.  This pins why the
    row's own memory flag changes no module (the hunt's census, #1900); a
    row that asks for memory without allocating breaks it."""
    from vera.builtins import HOST_FAMILIES, family_rows

    rows = [row for family in HOST_FAMILIES for row in family_rows(family.name)]
    asking = [row.name for row in rows if row.needs_memory]
    assert asking
    assert [r for r in rows if r.needs_memory and not r.needs_alloc] == []


def test_repro_a_data_segment_alone_declares_memory() -> None:
    """A module whose only contact with memory is a string the pool holds:
    no memory instruction and no host row, so only the data segment asks
    for the memory it is written into."""
    result = _compiled(
        "public fn f(-> @String)\n" + _C + '{\n  "hello"\n}\n')
    assert not holds_memory_instruction(result.wat)
    assert "(data" in result.wat
    assert '(memory (export "vera.memory") 1)' in result.wat
    wasmtime.Module.validate(_engine(), result.wasm_bytes)


def test_a_name_and_a_comment_that_look_like_loads_declare_no_memory() -> None:
    """Assembly-level: a module whose only `load` text is in a name and a
    comment declares no memory, and validates without one."""
    gen = pipeline.compile(
        "public fn f(-> @Int)\n" + _C + "{\n  1\n}\n", file="fixture.vera",
    ).generator
    assert gen is not None
    wat = gen._assemble_module([
        '  (func $i32.load (export "g") (result i32)\n'
        "    ;; i32.load\n    (; i64.store ;)\n    i32.const 7\n  )"])
    assert "(memory" not in wat
    wasmtime.Module.validate(_engine(), wasmtime.wat2wasm(wat))


# =====================================================================
# Validation is the backstop: a module that does not validate is E699
# =====================================================================

@pytest.fixture
def scan_disabled(monkeypatch: pytest.MonkeyPatch) -> None:
    """Assembly derives no memory from the module's instructions."""
    monkeypatch.setattr(
        "vera.codegen.assembly.holds_memory_instruction", lambda wat: False)


@pytest.mark.usefixtures("scan_disabled")
def test_a_module_that_does_not_validate_is_e699_with_no_bytes() -> None:
    result = pipeline.compile(_UNWRAP_OR, file="fixture.vera").result
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert [d.error_code for d in errors] == ["E699"]
    text = errors[0].description
    assert text.startswith(
        "Internal compiler error while assembling the module: "
        "the module does not validate: ")
    assert "unknown memory 0" in text
    assert "`unwrap_or`" in text
    assert result.wasm_bytes == b""


@pytest.mark.usefixtures("scan_disabled")
def test_vera_compile_writes_no_file_for_a_module_that_does_not_validate(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    from vera.cli import cmd_compile

    src = tmp_path / "unwrap.vera"
    src.write_text(_UNWRAP_OR, encoding="utf-8")
    out = tmp_path / "unwrap.wasm"
    assert cmd_compile(str(src), output=str(out)) == 1
    assert not out.exists()
    assert "E699" in capsys.readouterr().err


def test_validation_accepts_the_exception_proposal() -> None:
    """The validator's engine enables exceptions, as `execute()`'s does: a
    module with an exception boundary validates and compiles."""
    result = _compiled(
        "public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(<Exn<Int>>)\n{\n  if @Int.0 > 3 then { throw(@Int.0) }"
        " else { @Int.0 }\n}\n")
    assert "try_table" in result.wat
    wasmtime.Module.validate(_engine(), result.wasm_bytes)


# =====================================================================
# The wasi-p2 component is checked where it is built
# =====================================================================

_BAD_COMPONENT = (
    "(component\n  (core module $m\n    (func (result i32)\n"
    "      i32.const 0\n      i32.load)))\n"
)

_MAIN = "public fn main(-> @Int)\n" + _C + "{\n  42\n}\n"


@pytest.fixture
def bad_component(monkeypatch: pytest.MonkeyPatch) -> None:
    """The wasi-p2 emitter builds a component that assembles and does not
    validate (its core module loads from a memory it does not declare)."""
    # The host binds the emitter by name at its own import, so it is
    # imported before either is patched: imported while the emitter is
    # patched, it would bind the stand-in and keep it after the test.
    import vera.runtime.wasi_host  # noqa: F401

    for site in ("vera.codegen.wasi", "vera.runtime.wasi_host"):
        monkeypatch.setattr(
            f"{site}.emit_wasi_component",
            lambda result, world="cli": _BAD_COMPONENT)


@pytest.mark.parametrize("world", ["cli", "server"])
@pytest.mark.usefixtures("bad_component")
def test_vera_compile_wasi_p2_writes_no_invalid_component(
    world: str, tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    from vera.cli import cmd_compile

    src = tmp_path / "main.vera"
    src.write_text(_MAIN, encoding="utf-8")
    out = tmp_path / "main.wasm"
    rc = cmd_compile(str(src), output=str(out), target="wasi-p2", world=world)
    assert rc == 1
    assert not out.exists()
    err = capsys.readouterr().err
    assert "E699" in err
    assert "does not validate" in err


@pytest.mark.usefixtures("bad_component")
def test_vera_run_wasi_p2_refuses_an_invalid_component(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    from vera.cli import cmd_run

    src = tmp_path / "main.vera"
    src.write_text(_MAIN, encoding="utf-8")
    assert cmd_run(str(src), target="wasi-p2") == 1
    err = capsys.readouterr().err
    assert "E699" in err
    assert "the wasi-p2 component does not validate" in err


def test_memory_is_declared_before_the_data_segments() -> None:
    """The declaration keeps the place in the module's text it has always
    had, ahead of the data segments it holds, so a module's text does not
    move with where the decision is made."""
    wat = _compiled(
        "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
        '  effects(<IO>)\n{\n  IO.print("hi")\n}\n').wat
    assert 0 < wat.index("(memory") < wat.index("(data")


def test_a_valid_wasi_p2_component_is_written(tmp_path: Path) -> None:
    from vera.cli import cmd_compile

    src = tmp_path / "main.vera"
    src.write_text(_MAIN, encoding="utf-8")
    out = tmp_path / "main.wasm"
    assert cmd_compile(str(src), output=str(out), target="wasi-p2") == 0
    assert out.read_bytes()[:4] == b"\0asm"


def test_repro_build_component_returns_the_engine_it_built_with(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The engine `build_component` returns is the one it constructed the
    component with, read once: a caller makes its store from it."""
    from vera.codegen import validation

    engines = [validation.engine(), _engine()]
    calls = iter(engines)
    monkeypatch.setattr(validation, "engine", lambda: next(calls))
    wat = (
        "(component\n  (core module $m\n    (func (export \"f\") (result i32)\n"
        "      i32.const 7)))\n")
    _binary, returned, _component = validation.build_component(wat)
    assert returned is engines[0]
    # Read once: the construction took the same engine, not a second one.
    assert next(calls) is engines[1]


def test_repro_racing_callers_share_one_engine(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """`engine()` builds the process's engine once whoever races it: two
    threads that both find none built get the same object.  The engine's
    construction is slowed so both are inside it at once."""
    import threading
    import time

    from vera.codegen import validation

    real = wasmtime.Engine

    def slow(config: wasmtime.Config | None = None) -> wasmtime.Engine:
        time.sleep(0.05)
        return real(config)

    monkeypatch.setattr(validation, "_ENGINE", None)
    monkeypatch.setattr(validation.wasmtime, "Engine", slow)
    got: list[wasmtime.Engine] = []
    start = threading.Barrier(2)

    def call() -> None:
        start.wait()
        got.append(validation.engine())

    threads = [threading.Thread(target=call) for _ in range(2)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert len(got) == 2
    assert got[0] is got[1]


def test_repro_the_host_runs_the_component_it_checked(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """`vera run --target wasi-p2` runs the component `build_component`
    constructed, on the engine it was constructed with."""
    from vera.cli import cmd_run

    src = tmp_path / "hello.vera"
    src.write_text(
        "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
        '  effects(<IO>)\n{\n  IO.print("checked\\n")\n}\n', encoding="utf-8")
    assert cmd_run(str(src), target="wasi-p2") == 0
    assert "checked" in capsys.readouterr().out


# =====================================================================
# What `vera compile` reports and writes, each asserted whole
# =====================================================================

#: A `main` whose second arm is unreachable: an E310 warning at line 8,
#: column 5, which every refusal and every success must carry with it.
_MAIN_WARNS = (
    "public fn main(-> @Int)\n" + _C
    + "{\n  match 0 {\n    _ -> 1,\n    0 -> 2\n  };\n  42\n}\n"
)

#: The same warning ahead of a call of a host family wasi-p2 lacks.
_HTTP_WARNS = (
    "public fn main(-> @Unit)\n  requires(true)\n  ensures(true)\n"
    "  effects(<IO, Http>)\n{\n  match 0 {\n    _ -> 1,\n    0 -> 2\n  };\n"
    '  match Http.get("http://localhost/x") {\n'
    "    Ok(@String) -> IO.print(@String.0),\n"
    "    Err(@String) -> IO.print(@String.0)\n  }\n}\n"
)

_E699_RATIONALE = (
    "Code generation produced a module WebAssembly cannot load. That is a "
    "bug in the compiler, not something to change in the program: a "
    "program the checker should have refused was not, or a valid one was "
    "compiled under a clashing name or into a module that does not "
    "validate."
)
_E699_FIX = (
    "Please file a bug report with the offending program at "
    "https://github.com/aallan/vera/issues"
)
_SPEC_0_5_1 = 'Chapter 0, Section 0.5.1 "Diagnostic Structure"'


def _refusal(build: Callable[[], object]) -> str:
    """wasmtime's refusal of what *build* constructs, on one line, as the
    diagnostic quotes it.  Read from wasmtime, not written here, so the
    tests hold whatever version reports it."""
    with pytest.raises(wasmtime.WasmtimeError) as refused:
        build()
    return " ".join(str(refused.value).split())


def _e310(src: Path) -> dict[str, object]:
    return {
        "severity": "warning",
        "description": (
            "Unreachable match arm: pattern after catch-all will never "
            "match."),
        "location": {"line": 8, "column": 5, "file": str(src)},
        "source_line": "    0 -> 2",
        "rationale": (
            "A wildcard or binding pattern already matches all remaining "
            "values."),
        "fix": "Remove this arm or move it before the catch-all.",
        "spec_ref": 'Chapter 4, Section 4.9.3 "Redundancy"',
        "error_code": "E310",
    }


def _e310_text(src: Path) -> str:
    return (
        f"warning: [E310] Warning at {src}, line 8, column 5:\n\n"
        "        0 -> 2\n        ^\n\n"
        "  Unreachable match arm: pattern after catch-all will never match."
        "\n\n  A wildcard or binding pattern already matches all remaining "
        "values.\n\n  Fix:\n\n    Remove this arm or move it before the "
        'catch-all.\n\n  See: Chapter 4, Section 4.9.3 "Redundancy"\n'
    )


def _e699(src: Path, message: str) -> dict[str, object]:
    return {
        "severity": "error",
        "description": (
            "Internal compiler error while assembling the module: " + message),
        "location": {"line": 0, "column": 0, "file": str(src)},
        "rationale": _E699_RATIONALE,
        "fix": _E699_FIX,
        "spec_ref": _SPEC_0_5_1,
        "error_code": "E699",
    }


def _e699_text(src: Path, message: str) -> str:
    return (
        f"[E699] Error at {src}:\n\n"
        f"  Internal compiler error while assembling the module: {message}"
        f"\n\n  {_E699_RATIONALE}\n\n  Fix:\n\n    {_E699_FIX}\n\n"
        f"  See: {_SPEC_0_5_1}\n"
    )


def _listing(directory: Path) -> list[str]:
    return sorted(p.name for p in directory.iterdir())


@pytest.mark.usefixtures("scan_disabled", "bad_component")
def test_repro_e699_is_one_whole_diagnostic_for_a_module_and_a_component(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """`assembly_error` is the one E699 for an artifact that does not
    validate: the core module (through `compile_program`) and the wasi-p2
    component (through `vera compile`), each refused through the real
    command, in `--json` and in text, every field whole.  The location
    names the file and no position; nothing is written."""
    from wasmtime.component import Component

    from vera.cli import cmd_compile

    core = tmp_path / "unwrap.vera"
    core.write_text(_UNWRAP_OR, encoding="utf-8")
    wat = pipeline.compile(_UNWRAP_OR, file="fixture.vera").result.wat
    core_message = (
        "the module does not validate: "
        + _refusal(lambda: wasmtime.Module.validate(
            _engine(), wasmtime.wat2wasm(wat)))
        + ", in the function `unwrap_or`. No loader accepts it, so it is "
        "not written.")
    component = tmp_path / "main.vera"
    component.write_text(_MAIN_WARNS, encoding="utf-8")
    component_message = (
        "the wasi-p2 component does not validate: "
        + _refusal(lambda: Component(
            _engine(), wasmtime.wat2wasm(_BAD_COMPONENT)))
        + ". No loader accepts it, so it is not written.")
    cases: list[tuple[Path, str, dict[str, str], list[dict[str, object]], str]] = [
        (core, core_message, {}, [], ""),
        (component, component_message, {"target": "wasi-p2"},
         [_e310(component)], _e310_text(component)),
    ]
    for src, message, target, warnings, warning_text in cases:
        assert cmd_compile(str(src), as_json=True, **target) == 1
        assert json.loads(capsys.readouterr().out) == {
            "ok": False, "file": str(src),
            "diagnostics": [_e699(src, message)], "warnings": warnings,
        }
        assert cmd_compile(str(src), **target) == 1
        assert capsys.readouterr() == ("", warning_text + _e699_text(src, message))
    assert _listing(tmp_path) == ["main.vera", "unwrap.vera"]


def test_repro_a_family_wasi_p2_lacks_is_refused_whole(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """The emitter's family gate, the refusal just ahead of the
    component's check: E908 with the warnings, in `--json` and in text,
    and no file."""
    from vera.cli import cmd_compile

    src = tmp_path / "prog.vera"
    src.write_text(_HTTP_WARNS, encoding="utf-8")
    description = (
        "--target wasi-p2: --target wasi-p2 does not support the following "
        "host family: http (http_get). Supported families: IO, Random.")
    rationale = (
        "A target needs something of the program: `--target browser` calls "
        "`main` when the page loads, `--target wasi-p2` hosts only the host "
        "families it implements, and `vera serve` calls "
        "`handle(@Request -> @Response)` for each request.")
    fix = (
        "Give the program what the target needs, as the description says, "
        "or build it for the default target:")
    assert cmd_compile(str(src), target="wasi-p2", as_json=True) == 1
    assert json.loads(capsys.readouterr().out) == {
        "ok": False, "file": str(src),
        "diagnostics": [{
            "severity": "error", "description": description,
            "location": {"line": 0, "column": 0, "file": str(src)},
            "rationale": rationale,
            "fix": fix + "\n\n  vera run program.vera",
            "spec_ref": _SPEC_0_5_1, "error_code": "E908",
        }],
        "warnings": [_e310(src)],
    }
    assert cmd_compile(str(src), target="wasi-p2") == 1
    assert capsys.readouterr() == ("", _e310_text(src) + (
        f"[E908] Error at {src}:\n\n  {description}\n\n  {rationale}\n\n"
        f"  Fix:\n\n    {fix}\n    \n      vera run program.vera\n\n"
        f"  See: {_SPEC_0_5_1}\n"))
    assert _listing(tmp_path) == ["prog.vera"]


def test_repro_vera_compile_writes_each_artifact_where_it_says(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """A component that validates is written, to `--output` when one is
    given and beside the source as `.wasm` when not, and is the component;
    the core target's `--wat` prints the module's text and its default
    writes the module's bytes.  Each report is whole, warnings included."""
    from wasmtime.component import Component

    from vera.cli import cmd_compile

    home = tmp_path / "src"
    home.mkdir()
    src = home / "prog.vera"
    src.write_text(_MAIN_WARNS, encoding="utf-8")
    elsewhere = tmp_path / "out"
    elsewhere.mkdir()
    named = elsewhere / "artifact.component"

    assert cmd_compile(str(src), target="wasi-p2", output=str(named)) == 0
    assert capsys.readouterr() == (
        f"Compiled (WASI Preview 2 component): {named}\n", _e310_text(src))
    assert _listing(home) == ["prog.vera"]
    assert _listing(elsewhere) == ["artifact.component"]

    assert cmd_compile(str(src), target="wasi-p2") == 0
    default = home / "prog.wasm"
    assert capsys.readouterr() == (
        f"Compiled (WASI Preview 2 component): {default}\n", _e310_text(src))
    assert _listing(home) == ["prog.vera", "prog.wasm"]
    binary = default.read_bytes()
    assert binary == named.read_bytes()
    # The component layer's preamble, not a core module's.
    assert binary[:8] == b"\0asm\x0d\x00\x01\x00"
    Component(_engine(), binary)

    module = pipeline.compile(src.read_text(encoding="utf-8"), file=str(src)).result
    assert cmd_compile(str(src), wat=True) == 0
    assert capsys.readouterr() == (module.wat + "\n", _e310_text(src))
    assert cmd_compile(str(src)) == 0
    assert capsys.readouterr() == (
        f"Compiled: {default} (1 function exported)\n", _e310_text(src))
    assert default.read_bytes() == module.wasm_bytes


def test_repro_text_the_assembler_refuses_is_its_own_e699(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The other branch beside `assembly_error`: text `wat2wasm` refuses
    (a call of a function the module does not hold) is an E699 quoting the
    assembler, located at the file with no position, and no bytes."""
    bad = "(module\n  (func $f\n    call $missing\n  )\n)\n"
    monkeypatch.setattr("vera.codegen.core.strip_check_markers", lambda wat: bad)
    result = pipeline.compile(_MAIN, file="fixture.vera").result
    quoted = str(pytest.raises(
        wasmtime.WasmtimeError, wasmtime.wat2wasm, bad).value)
    assert [d.to_dict() for d in result.diagnostics] == [{
        "severity": "error",
        "description": f"WAT compilation failed: {quoted}",
        "location": {"line": 0, "column": 0, "file": "fixture.vera"},
        "rationale": (
            "Code generation produced WebAssembly text the assembler "
            "refuses. That is a bug in the compiler, not something to "
            "change in the program."),
        "fix": _E699_FIX,
        "spec_ref": _SPEC_0_5_1,
        "error_code": "E699",
    }]
    assert result.wasm_bytes == b""


def test_repro_a_closure_kept_from_a_dropped_function_has_its_allocator(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """`f`'s closure is lifted and committed, then `f` is dropped before its
    own merge (its postcondition's `hash` of a `Decimal` skips, E602).  The
    closure stays in the module and its body allocates, so the closure
    lift's own `_needs_alloc` is what declares `$alloc` and `$gc_sp`:
    without it the module does not assemble (E699)."""
    from vera.cli import cmd_compile

    source = (
        "type Mk = fn(Int -> Option<Int>) effects(pure);\n\n"
        "public fn f(@Decimal, @Int -> @Int)\n  requires(true)\n"
        "  ensures(hash(@Decimal.0) == 0)\n  effects(pure)\n{\n"
        "  let @Mk = fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0) };\n"
        "  match apply_fn(@Mk.0, @Int.0) {\n    None -> 0,\n"
        "    Some(@Int) -> @Int.0\n  }\n}\n\n"
        "public fn main(-> @Int)\n" + _C + "{\n  7\n}\n")
    result = pipeline.compile(source, file="fixture.vera").result
    assert [(d.severity, d.error_code) for d in result.diagnostics] == [
        ("warning", "E602")]
    assert result.exports == ["main"]
    assert "call $alloc" in result.wat
    assert "(func $alloc" in result.wat
    wasmtime.Module.validate(_engine(), result.wasm_bytes)
    assert pipeline.run(result, "main").execution.value == 7
    src = tmp_path / "kept.vera"
    src.write_text(source, encoding="utf-8")
    out = tmp_path / "kept.wasm"
    assert cmd_compile(str(src), output=str(out)) == 0
    assert out.read_bytes() == result.wasm_bytes
    capsys.readouterr()


def test_repro_the_server_world_writes_its_own_component(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """`--world server` reaches the emitter: the file written is the server
    world's component, byte for byte, and the report says how to run it."""
    from vera.cli import cmd_compile
    from vera.codegen.wasi import emit_wasi_component

    source = (
        "public fn handle(@Request -> @Response)\n  requires(true)\n"
        "  ensures(true)\n  effects(<HttpServer>)\n{\n"
        '  Response(200, map_new(), "served")\n}\n')
    src = tmp_path / "server.vera"
    src.write_text(source, encoding="utf-8")
    out = tmp_path / "server.component"
    assert cmd_compile(
        str(src), target="wasi-p2", world="server", output=str(out)) == 0
    assert capsys.readouterr() == (
        "Compiled (WASI Preview 2 server component (run with: wasmtime "
        f"serve <file>)): {out}\n", "")
    result = pipeline.compile(source, file=str(src)).result
    assert out.read_bytes() == bytes(wasmtime.wat2wasm(
        emit_wasi_component(result, world="server")))


def test_repro_an_imported_data_type_brings_the_allocator_as_a_declared_one_does(
    tmp_path: Path,
) -> None:
    """A module whose data type is only read, never built: declared in the
    entry file (`_register_data`) or imported (`_register_modules`), the
    module holds the allocator and exports it, so an embedder can build
    the argument the exported reader takes."""
    from vera.runtime import runtime_export

    lib = (
        "module lib;\n\npublic data Box {\n  MkBox(Int)\n}\n\n"
        "public fn unbox(@Box -> @Int)\n" + _C
        + "{\n  match @Box.0 {\n    MkBox(@Int) -> @Int.0\n  }\n}\n")
    imported = (
        "import lib(Box, unbox);\n\npublic fn f(@Box -> @Int)\n" + _C
        + "{\n  unbox(@Box.0)\n}\n")
    declared = (
        "private data Box {\n  MkBox(Int)\n}\n\npublic fn f(@Box -> @Int)\n"
        + _C + "{\n  match @Box.0 {\n    MkBox(@Int) -> @Int.0\n  }\n}\n")
    for name, files in (
        ("imported", {"lib.vera": lib, "main.vera": imported}),
        ("declared", {"main.vera": declared}),
    ):
        root = tmp_path / name
        main = pipeline.write_tree(root, files)
        result = pipeline.compile(main, root=root).result
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        module = wasmtime.Module(_engine(), result.wasm_bytes)
        exports = sorted(e.name for e in module.exports)
        assert runtime_export("alloc") in exports, (name, exports)
        assert "f" in exports, (name, exports)


def test_repro_the_function_a_refusal_names() -> None:
    """`_function_named` reads the name after the last `:` of the function
    wasmtime's compile names (a user function's starts `:`, a runtime
    function's has none), keeps a name that ends in `:` whole, and names
    none when the function has no name; `validate_module` quotes the
    validator, adds the name only when there is one, and refuses."""
    from vera.codegen.validation import _function_named, validate_module
    from vera.skip import CodegenInvariantError

    def failing(name: str) -> bytes:
        return bytes(wasmtime.wat2wasm(
            f"(module (func {name} (result i32) i32.const 0 i32.load))"))

    named = {
        "$:unwrap_or": "unwrap_or", "$alloc": "alloc",
        "$a:b:c": "c", "$f:": "f:", "": None,
    }
    for name, expected in named.items():
        assert _function_named(failing(name)) == expected, name
        quoted = _refusal(lambda: wasmtime.Module.validate(
            _engine(), failing(name)))
        with pytest.raises(CodegenInvariantError) as refused:
            validate_module(failing(name))
        assert refused.value.msg == (
            "the module does not validate: " + quoted
            + (f", in the function `{expected}`" if expected else "")
            + ". No loader accepts it, so it is not written."), name
    assert _function_named(wasmtime.wat2wasm("(module (func $:f))")) is None
