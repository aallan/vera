"""Tests for the WASI Preview 2 component emitter (#237).

``vera/codegen/wasi.py`` turns a compiled Vera module into a wasip2
component whose ``vera.*`` IO + Random imports are implemented by an
in-component adapter over WASI 0.2.  These tests validate the three
load-bearing claims end to end against the real wasmtime host:

1. the emitted text PARSES as a component
   (``wasmtime.component.Component`` runs full component validation,
   compiling both core modules);
2. it INSTANTIATES under ``Linker.add_wasip2()`` with a ``WasiConfig``
   (structural type-match of every WASI import against the real host —
   the design study caught a mis-spelled enum case only at this stage,
   so a parse-only check is not enough);
3. it EXECUTES with correct op semantics (stdout/stderr capture, env,
   argv, preopened files, stdin, clocks, random bounds, traps).

Plus the family gate (a clean diagnostic — never a silent fallback —
for host families the target does not support) and a pin that the
default ``--target wasm`` emission is untouched by the wasi machinery.
"""
from __future__ import annotations

import os
import shutil
import tempfile
import time
from pathlib import Path

import pytest
import wasmtime
from wasmtime.component import Component, Linker

from tests.codegen_helpers import _compile_ok
from vera.codegen import CompileResult
from vera.codegen.wasi import emit_wasi_component

# Engine + wasip2 linker are stateless across instantiations; build
# once at module scope to keep the suite fast.
_ENGINE = wasmtime.Engine()
_LINKER = Linker(_ENGINE)
_LINKER.add_wasip2()


HELLO = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("Hello, WASI!")
}
"""

# One program exercising every supported op — the widest interface
# import surface the emitter can produce (all 13 WASI interfaces).
KITCHEN_SINK = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO, Random>)
{
  IO.print("out");
  IO.stderr("err");
  let @String = IO.read_line(());
  let @Option<String> = IO.get_env("HOME");
  let @Array<String> = IO.args(());
  let @Nat = IO.time(());
  IO.sleep(1);
  let @Int = Random.random_int(1, 6);
  let @Float64 = Random.random_float(());
  let @Bool = Random.random_bool(());
  let @Result<String, String> = IO.read_file("x.txt");
  let @Result<Unit, String> = IO.write_file("y.txt", "data");
  let @Result<String, String> = IO.read_char(());
  42
}
"""


def _emit(source: str) -> str:
    return emit_wasi_component(_compile_ok(source))


def _run_component(
    result: CompileResult,
    *,
    argv: list[str] | None = None,
    env: list[tuple[str, str]] | None = None,
    stdin_path: str | None = None,
    preopen: str | None = None,
    entry: str = "main",
) -> tuple[object, str, str]:
    """Instantiate under wasip2 and call the lifted entry.

    Returns (value, stdout, stderr).  A WasiConfig is always set —
    calling a wasip2 import on a config-less store aborts the whole
    process (SIGABRT), per the WASI.md spike invariants.
    """
    component = Component(_ENGINE, emit_wasi_component(result))
    store = wasmtime.Store(_ENGINE)
    config = wasmtime.WasiConfig()
    out = bytearray()
    err = bytearray()
    config.stdout_custom = out.extend
    config.stderr_custom = err.extend
    config.argv = argv if argv is not None else ["prog"]
    if env is not None:
        config.env = env
    if stdin_path is not None:
        config.stdin_file = stdin_path
    if preopen is not None:
        config.preopen_dir(preopen, "/")
    store.set_wasi(config)
    instance = _LINKER.instantiate(store, component)
    func = instance.get_func(store, entry)
    assert func is not None, f"missing lifted export {entry!r}"
    value = func(store)
    func.post_return(store)
    return value, out.decode(), err.decode()


# =====================================================================
# Emission: parse + instantiate
# =====================================================================

class TestComponentValidates:
    """The emitted text survives full component validation and the
    structural type-match against wasmtime's real wasip2 host."""

    def test_print_program_parses_as_component(self) -> None:
        Component(_ENGINE, _emit(HELLO))

    def test_print_program_instantiates_under_wasip2(self) -> None:
        store = wasmtime.Store(_ENGINE)
        store.set_wasi(wasmtime.WasiConfig())
        _LINKER.instantiate(store, Component(_ENGINE, _emit(HELLO)))

    def test_kitchen_sink_parses_and_instantiates(self) -> None:
        """All 14 IO/Random ops + every WASI interface import at once."""
        component = Component(_ENGINE, _emit(KITCHEN_SINK))
        store = wasmtime.Store(_ENGINE)
        store.set_wasi(wasmtime.WasiConfig())
        _LINKER.instantiate(store, component)

    def test_no_memory_program_parses_and_instantiates(self) -> None:
        """A program with no strings and no GC still gets a memory +
        arena (the lowers need a canonical-ABI memory)."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{
  Random.random_int(1, 6)
}
"""
        component = Component(_ENGINE, _emit(source))
        store = wasmtime.Store(_ENGINE)
        store.set_wasi(wasmtime.WasiConfig())
        _LINKER.instantiate(store, component)

    def test_interface_imports_are_gated_by_ops(self) -> None:
        """A print-only program must not import filesystem/random/etc.
        interfaces — the import surface is the op-dependency closure."""
        wat = _emit(HELLO)
        assert '"wasi:cli/stdout@0.2.0"' in wat
        assert '"wasi:io/streams@0.2.0"' in wat
        assert '"wasi:io/error@0.2.0"' in wat
        for absent in (
            "wasi:filesystem/types", "wasi:filesystem/preopens",
            "wasi:random/random", "wasi:cli/stdin", "wasi:cli/exit",
            "wasi:clocks/wall-clock", "wasi:clocks/monotonic-clock",
            "wasi:cli/environment", "wasi:io/poll",
        ):
            assert absent not in wat, f"unexpected interface {absent}"

    def test_both_entry_exports_present(self) -> None:
        """wasi:cli/run (stock `wasmtime run`) + plain lifted main."""
        wat = _emit(HELLO)
        assert '(export "wasi:cli/run@0.2.0" (instance $run_inst))' in wat
        assert '(export "main" (func $main_l))' in wat

    def test_string_main_exports_cli_run_only(self) -> None:
        """A String-returning main has no scalar lift (the (ptr, len)
        pair is not liftable in v1); wasi:cli/run remains the entry."""
        wat = _emit("""\
public fn main(-> @String)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("side");
  "returned"
}
""")
        assert '(export "main" (func $main_l))' not in wat
        assert '(export "wasi:cli/run@0.2.0"' in wat


# =====================================================================
# Family gate
# =====================================================================

class TestFamilyGate:
    """Unsupported host families get a clean diagnostic naming the
    family — never a silent fallback or a broken component."""

    def test_http_program_is_rejected_naming_http(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<Http, IO>)
{
  match Http.get("http://example.invalid/") {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }
}
""")
        with pytest.raises(ValueError, match="http"):
            emit_wasi_component(result)

    def test_math_program_is_rejected_naming_math(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Float64)
  requires(true) ensures(true) effects(pure)
{
  sin(1.0)
}
""")
        with pytest.raises(ValueError, match="math"):
            emit_wasi_component(result)

    def test_state_program_is_rejected_naming_state(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{
  State.put(7);
  State.get(())
}
""")
        with pytest.raises(ValueError, match="state"):
            emit_wasi_component(result)

    def test_entry_point_is_required(self) -> None:
        result = _compile_ok("""\
public fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0
}
""")
        with pytest.raises(ValueError, match="main"):
            emit_wasi_component(result)


# =====================================================================
# Default-target pin
# =====================================================================

class TestCoreEmissionPin:
    """The wasi-p2 emitter post-processes a COPY of the WAT text; the
    default ``--target wasm`` emission must be byte-identical with and
    without the wasi machinery in play."""

    def test_emit_does_not_mutate_compile_result(self) -> None:
        result = _compile_ok(KITCHEN_SINK)
        before_wat = result.wat
        before_bytes = result.wasm_bytes
        emit_wasi_component(result)
        assert result.wat == before_wat
        assert result.wasm_bytes == before_bytes

    def test_default_target_wat_unchanged_by_wasi_import(self) -> None:
        """Two independent compiles bracket an emitter run: the default
        emission is a pure function of the program, unaffected by
        importing or invoking the wasi emitter."""
        first = _compile_ok(KITCHEN_SINK)
        emit_wasi_component(first)
        second = _compile_ok(KITCHEN_SINK)
        assert first.wat == second.wat


# =====================================================================
# Execution (the true end-to-end: lifted main under the real host)
# =====================================================================

class TestExecution:
    def test_print_captured_via_stdout_custom(self) -> None:
        value, out, err = _run_component(_compile_ok(HELLO))
        assert value is None  # Unit main lifts with no result
        assert out == "Hello, WASI!"
        assert err == ""

    def test_stdout_stderr_separation(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("to-out");
  IO.stderr("to-err")
}
""")
        _, out, err = _run_component(result)
        assert out == "to-out"
        assert err == "to-err"

    def test_int_main_round_trips_through_s64_lift(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("x");
  42
}
""")
        value, out, _ = _run_component(result)
        assert value == 42
        assert out == "x"

    def test_pure_program_with_no_host_imports_runs(self) -> None:
        """No vera.* imports at all: the component degenerates to an
        adapter-less shell but both entry lifts still work."""
        result = _compile_ok("""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  42
}
""")
        value, out, _ = _run_component(result)
        assert value == 42
        assert out == ""

    def test_overflow_guard_traps_through_the_dispatch_table(self) -> None:
        """overflow_trap is a non-WASI op planted in the same table;
        the #798 guard must still stop a wrapping add."""
        result = _compile_ok("""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = 9223372036854775807;
  @Int.0 + 1
}
""")
        component = Component(_ENGINE, emit_wasi_component(result))
        store = wasmtime.Store(_ENGINE)
        config = wasmtime.WasiConfig()
        config.argv = ["prog"]
        store.set_wasi(config)
        instance = _LINKER.instantiate(store, component)
        func = instance.get_func(store, "main")
        assert func is not None
        with pytest.raises(wasmtime.WasmtimeError, match="unreachable"):
            func(store)

    def test_wasi_cli_run_export_is_callable(self) -> None:
        """The nested wasi:cli/run@0.2.0#run export drives main and
        reports ok — this is what stock `wasmtime run` invokes."""
        component = Component(_ENGINE, _emit(HELLO))
        store = wasmtime.Store(_ENGINE)
        config = wasmtime.WasiConfig()
        out = bytearray()
        config.stdout_custom = out.extend
        config.argv = ["prog"]
        store.set_wasi(config)
        instance = _LINKER.instantiate(store, component)
        iface = instance.get_export_index(store, "wasi:cli/run@0.2.0")
        assert iface is not None
        run_idx = instance.get_export_index(store, "run", instance=iface)
        assert run_idx is not None
        func = instance.get_func(store, run_idx)
        assert func is not None
        run_result = func(store)
        func.post_return(store)
        assert getattr(run_result, "tag", None) == "ok"
        assert out.decode() == "Hello, WASI!"

    def test_get_env_hit_and_miss(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.get_env("FOO") {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("<none>")
  };
  match IO.get_env("MISSING") {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("<none>")
  }
}
""")
        _, out, _ = _run_component(
            result, env=[("FOO", "bar-value"), ("OTHER", "x")],
        )
        assert out == "bar-value<none>"

    def test_get_env_scans_a_large_environment(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.get_env("TARGET_KEY") {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("<none>")
  }
}
""")
        env = [(f"K{i:03d}", "v" * 50) for i in range(200)]
        env.append(("TARGET_KEY", "the-needle-value"))
        _, out, _ = _run_component(result, env=env)
        assert out == "the-needle-value"

    def test_args_skips_argv0(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  IO.print(nat_to_string(array_length(@Array<String>.0)));
  IO.print(":");
  IO.print(string_join(@Array<String>.0, ","))
}
""")
        _, out, _ = _run_component(
            result, argv=["prog", "alpha", "beta"],
        )
        assert out == "2:alpha,beta"

    def test_args_survive_gc_pressure_inside_the_adapter(self) -> None:
        """500 args x ~100 B force collections during op_args' element
        loop; a missing backing root would alias or corrupt elements.
        The element prints are alloc-free (indexing + print), so the
        oracle cannot be disturbed by later Vera-side allocations."""
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  IO.print(@Array<String>.0[0]);
  IO.print("|");
  IO.print(@Array<String>.0[499]);
  IO.print("|");
  IO.print(nat_to_string(array_length(@Array<String>.0)))
}
""")
        argv = ["prog"] + [
            f"arg{i:04d}-" + "x" * 90 for i in range(500)
        ]
        _, out, _ = _run_component(result, argv=argv)
        first, last, count = out.split("|")
        assert first == argv[1]
        assert last == argv[500]
        assert count == "500"

    def test_oversized_argv_traps_cleanly(self) -> None:
        """get-arguments is a one-shot realloc into the 64 KiB arena;
        beyond it the adapter traps `unreachable` (documented limit)
        rather than corrupting memory."""
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  IO.print(nat_to_string(array_length(@Array<String>.0)))
}
""")
        argv = ["prog"] + ["y" * 100 for _ in range(2000)]
        with pytest.raises(wasmtime.WasmtimeError, match="unreachable"):
            _run_component(result, argv=argv)

    def test_time_is_bracketed_by_host_clock_and_sleep_returns(
        self,
    ) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.sleep(10);
  let @Nat = IO.time(());
  IO.print(nat_to_string(@Nat.0))
}
""")
        before_ms = int(time.time() * 1000)
        _, out, _ = _run_component(result)
        after_ms = int(time.time() * 1000)
        assert before_ms <= int(out) <= after_ms

    def test_random_int_respects_inclusive_bounds(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{
  Random.random_int(1, 6)
}
""")
        seen = {
            _run_component(result)[0] for _ in range(20)
        }
        assert seen <= set(range(1, 7)), seen

    def test_random_float_and_bool_shapes(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO, Random>)
{
  let @Float64 = Random.random_float(());
  let @Bool = Random.random_bool(());
  IO.print(float_to_string(@Float64.0));
  IO.print("|");
  IO.print(bool_to_string(@Bool.0))
}
""")
        _, out, _ = _run_component(result)
        float_text, bool_text = out.split("|")
        assert 0.0 <= float(float_text) < 1.0
        assert bool_text in ("true", "false")

    def test_write_then_read_file_roundtrip_and_errno(
        self, tmp_path: Path,
    ) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.write_file("out.txt", "written-by-vera\\n") {
    Ok(_) -> {
      match IO.read_file("out.txt") {
        Ok(@String) -> IO.print(@String.0),
        Err(@String) -> IO.print(string_concat("RERR:", @String.0))
      }
    },
    Err(@String) -> IO.print(string_concat("WERR:", @String.0))
  };
  match IO.read_file("missing.txt") {
    Ok(@String) -> IO.print("unexpected"),
    Err(@String) -> IO.print(string_concat("ERR:", @String.0))
  }
}
""")
        _, out, _ = _run_component(result, preopen=str(tmp_path))
        assert out == "written-by-vera\nERR:no-entry"
        on_disk = (tmp_path / "out.txt").read_text(encoding="utf-8")
        assert on_disk == "written-by-vera\n"

    def test_read_file_chunks_large_files(self, tmp_path: Path) -> None:
        """> 16 KiB exercises the chunked blocking-read loop, the
        per-chunk arena reset, and the rooted grow-by-doubling buffer."""
        content = ("0123456789abcdef" * 4096) + "tail!"  # 64 KiB + 5
        (tmp_path / "big.txt").write_text(content, encoding="utf-8")
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_file("big.txt") {
    Ok(@String) -> IO.print(nat_to_string(string_length(@String.0))),
    Err(@String) -> IO.print(string_concat("ERR:", @String.0))
  }
}
""")
        _, out, _ = _run_component(result, preopen=str(tmp_path))
        assert out == str(len(content))

    def test_read_file_without_preopen_is_a_clean_err(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_file("x.txt") {
    Ok(@String) -> IO.print("unexpected"),
    Err(@String) -> IO.print(@String.0)
  }
}
""")
        _, out, _ = _run_component(result)
        assert out == "no preopened directories"

    def test_read_line_and_read_char_from_stdin(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(@String.0);
  IO.print("|");
  match IO.read_char(()) {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(string_concat("CERR:", @String.0))
  }
}
""")
        # Windows-safe stdin fixture: delete=False + manual unlink.
        handle = tempfile.NamedTemporaryFile(
            mode="w", suffix=".txt", delete=False, encoding="utf-8",
        )
        try:
            with handle:
                handle.write("first line\nsecond\n")
            _, out, _ = _run_component(result, stdin_path=handle.name)
        finally:
            os.unlink(handle.name)
        assert out == "first line|s"

    def test_read_char_multibyte_then_eof_then_empty_line(self) -> None:
        """UTF-8 lead-byte decoding, Err("EOF") parity with the host,
        and read_line returning "" at EOF."""
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_char(()) {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(string_concat("CERR:", @String.0))
  };
  match IO.read_char(()) {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(string_concat("|CERR:", @String.0))
  };
  let @String = IO.read_line(());
  IO.print(string_concat("|line:", @String.0))
}
""")
        handle = tempfile.NamedTemporaryFile(
            mode="w", suffix=".txt", delete=False, encoding="utf-8",
        )
        try:
            with handle:
                handle.write("é")
            _, out, _ = _run_component(result, stdin_path=handle.name)
        finally:
            os.unlink(handle.name)
        assert out == "é|CERR:EOF|line:"

    def test_exit_stops_execution(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("pre");
  IO.exit(3);
  IO.print("post")
}
""")
        component = Component(_ENGINE, emit_wasi_component(result))
        store = wasmtime.Store(_ENGINE)
        config = wasmtime.WasiConfig()
        out = bytearray()
        config.stdout_custom = out.extend
        config.argv = ["prog"]
        store.set_wasi(config)
        instance = _LINKER.instantiate(store, component)
        func = instance.get_func(store, "main")
        assert func is not None
        with pytest.raises(wasmtime.WasmtimeError):
            func(store)
        assert out.decode() == "pre"

    def test_contract_violation_message_reaches_stderr(self) -> None:
        """contract_fail routes the violation text through the WASI
        stderr stream before trapping — the component path loses
        structured trap frames, so the message is the diagnostic."""
        result = _compile_ok("""\
fn checked(@Int -> @Int)
  requires(@Int.0 > 10) ensures(true) effects(pure)
{
  @Int.0
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("go");
  checked(1)
}
""")
        component = Component(_ENGINE, emit_wasi_component(result))
        store = wasmtime.Store(_ENGINE)
        config = wasmtime.WasiConfig()
        err = bytearray()
        config.stderr_custom = err.extend
        config.argv = ["prog"]
        store.set_wasi(config)
        instance = _LINKER.instantiate(store, component)
        func = instance.get_func(store, "main")
        assert func is not None
        with pytest.raises(wasmtime.WasmtimeError):
            func(store)
        assert "requires" in err.decode()


# =====================================================================
# CLI integration: `vera compile/run --target wasi-p2` (C4)
# =====================================================================

INT_MAIN = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  42
}
"""

HTTP_MAIN = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO, Http>)
{
  match Http.get("http://localhost/x") {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }
}
"""


def _write_vera(tmp_path: Path, source: str) -> str:
    f = tmp_path / "prog.vera"
    f.write_text(source, encoding="utf-8")
    return str(f)


class TestCliCompileWasiP2:
    """`vera compile --target wasi-p2` writes a BINARY component
    (wat2wasm accepts component text — probed live) that stock
    `wasmtime run` / wasmtime-py accept with no Vera host bindings."""

    def test_writes_binary_component(self, tmp_path: Path) -> None:
        from vera.cli import cmd_compile

        src = _write_vera(tmp_path, HELLO)
        out = tmp_path / "prog.wasm"
        rc = cmd_compile(src, target="wasi-p2", output=str(out))
        assert rc == 0
        # A core module here would fail Component validation — this is
        # what distinguishes the wasi-p2 artifact from --target wasm.
        Component(_ENGINE, out.read_bytes())

    def test_wat_flag_prints_component_text(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        from vera.cli import cmd_compile

        src = _write_vera(tmp_path, HELLO)
        rc = cmd_compile(src, target="wasi-p2", wat=True)
        assert rc == 0
        printed = capsys.readouterr().out
        assert printed.lstrip().startswith("(component")

    def test_unsupported_family_is_a_clean_diagnostic(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        from vera.cli import cmd_compile

        src = _write_vera(tmp_path, HTTP_MAIN)
        rc = cmd_compile(src, target="wasi-p2")
        assert rc == 1
        err = capsys.readouterr().err
        assert "http" in err
        assert "wasi-p2" in err
        # Never a silent fallback: no artifact may be written.
        assert not (tmp_path / "prog.wasm").exists()

    def test_unsupported_family_json_envelope(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        import json as _json

        from vera.cli import cmd_compile

        src = _write_vera(tmp_path, HTTP_MAIN)
        rc = cmd_compile(src, target="wasi-p2", as_json=True)
        assert rc == 1
        envelope = _json.loads(capsys.readouterr().out)
        assert envelope["ok"] is False
        assert "http" in envelope["diagnostics"][0]["description"]


class TestCliRunWasiP2:
    """`vera run --target wasi-p2` executes the component under the
    built-in wasip2 host (add_wasip2), never the vera.* bindings."""

    def test_hello_prints(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        from vera.cli import cmd_run

        src = _write_vera(tmp_path, HELLO)
        rc = cmd_run(src, target="wasi-p2")
        assert rc == 0
        assert "Hello, WASI!" in capsys.readouterr().out

    def test_int_main_value_printed(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        from vera.cli import cmd_run

        src = _write_vera(tmp_path, INT_MAIN)
        rc = cmd_run(src, target="wasi-p2")
        assert rc == 0
        assert capsys.readouterr().out.strip() == "42"

    def test_json_envelope(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        import json as _json

        from vera.cli import cmd_run

        src = _write_vera(tmp_path, INT_MAIN)
        rc = cmd_run(src, as_json=True, target="wasi-p2")
        assert rc == 0
        envelope = _json.loads(capsys.readouterr().out)
        assert envelope["ok"] is True
        assert envelope["value"] == 42

    def test_exit_degrades_to_zero_or_one(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """wasi:cli/exit@0.2.0 only carries ok/err — IO.exit(3) is
        status 1 under ANY stock wasip2 host.  `vera run` reports the
        same degraded code rather than inventing fidelity the target
        cannot deliver (documented divergence, spec 13)."""
        from vera.cli import cmd_run

        src = _write_vera(tmp_path, """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("pre");
  IO.exit(3);
  IO.print("post")
}
""")
        rc = cmd_run(src, target="wasi-p2")
        out = capsys.readouterr().out
        assert rc == 1
        assert "pre" in out
        assert "post" not in out

    def test_exit_zero_is_success(self, tmp_path: Path) -> None:
        from vera.cli import cmd_run

        src = _write_vera(tmp_path, """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.exit(0)
}
""")
        assert cmd_run(src, target="wasi-p2") == 0

    def test_fn_flag_rejected(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The component lifts main only; --fn <other> must be a clean
        diagnostic, not a missing-export crash."""
        from vera.cli import cmd_run

        src = _write_vera(tmp_path, HELLO + """
public fn helper(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  7
}
""")
        rc = cmd_run(src, fn_name="helper", target="wasi-p2")
        assert rc == 1
        err = capsys.readouterr().err
        assert "main" in err
        assert "wasi-p2" in err

    def test_contract_violation_classified(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The component path loses structured trap frames (WASI.md
        check 5) but must still classify the kind from the trap text +
        WASI stderr channel."""
        import json as _json

        from vera.cli import cmd_run

        src = _write_vera(tmp_path, """\
private fn checked(@Int -> @Int)
  requires(@Int.0 > 10) ensures(true) effects(pure)
{
  @Int.0
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("go");
  checked(1)
}
""")
        rc = cmd_run(src, as_json=True, target="wasi-p2")
        assert rc == 1
        envelope = _json.loads(capsys.readouterr().out)
        diag = envelope["diagnostics"][0]
        assert diag["trap_kind"] == "contract_violation"
        assert "requires" in diag["description"]

    def test_unsupported_family_diagnostic(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        from vera.cli import cmd_run

        src = _write_vera(tmp_path, HTTP_MAIN)
        rc = cmd_run(src, target="wasi-p2")
        assert rc == 1
        assert "http" in capsys.readouterr().err


class TestWasiHostRunner:
    """execute_wasi_p2 (vera/runtime/wasi_host.py) — the host half."""

    def test_env_passthrough(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Parity with the core path: IO.get_env sees the process
        environment (snapshotted into WasiConfig at launch)."""
        from vera.runtime.wasi_host import execute_wasi_p2

        monkeypatch.setenv("VERA_WASI_PROBE_237", "probe-value")
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.get_env("VERA_WASI_PROBE_237") {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("<none>")
  }
}
""")
        er = execute_wasi_p2(result)
        assert er.stdout == "probe-value"

    def test_cli_args_reach_io_args(self) -> None:
        from vera.runtime.wasi_host import execute_wasi_p2

        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  IO.print(string_join(@Array<String>.0, ","))
}
""")
        er = execute_wasi_p2(result, cli_args=["first-arg", "second"])
        assert er.stdout == "first-arg,second"

    def test_stderr_captured(self) -> None:
        from vera.runtime.wasi_host import execute_wasi_p2

        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.stderr("to-stderr")
}
""")
        er = execute_wasi_p2(result)
        assert er.stderr == "to-stderr"
        assert er.stdout == ""

    def test_string_main_runs_via_cli_run(self) -> None:
        """A String-returning main has no scalar lift; the runner falls
        back to the wasi:cli/run entry (value is None — documented)."""
        from vera.runtime.wasi_host import execute_wasi_p2

        result = _compile_ok("""\
public fn main(-> @String)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("side");
  "returned"
}
""")
        er = execute_wasi_p2(result)
        assert er.stdout == "side"
        assert er.value is None


# =====================================================================
# Dual-target conformance differential (the #237 honesty test)
# =====================================================================

_CONF_DIR = Path(__file__).parent / "conformance"

# IO ops whose results differ across hosts by nature (randomness,
# clocks) or need external input (stdin, filesystem state) — a
# byte-equivalence differential over them would be flaky, not wrong.
_NONDETERMINISTIC_OPS = frozenset({
    "read_line", "read_char", "read_file", "write_file",
    "random_int", "random_float", "random_bool", "time",
})


def _conformance_run_ids() -> list[str]:
    import json as _json

    manifest = _json.loads(
        (_CONF_DIR / "manifest.json").read_text(encoding="utf-8"),
    )
    return [e["file"] for e in manifest if e["level"] == "run"]


def _compile_path(path: Path) -> CompileResult:
    """Compile a conformance file through the full CLI pipeline
    (resolver included — some ch08 programs import modules)."""
    from vera.checker import typecheck_with_artifacts
    from vera.cli import _load_and_parse
    from vera.codegen import compile as codegen_compile
    from vera.resolver import ModuleResolver
    from vera.transform import transform

    p, source, tree = _load_and_parse(str(path))
    ast = transform(tree)
    resolver = ModuleResolver(_root=p.parent)
    resolved = resolver.resolve_imports(ast, p)
    diags, artifacts = typecheck_with_artifacts(
        ast, source, file=str(p), resolved_modules=resolved,
    )
    errors = [d for d in resolver.errors + diags if d.severity == "error"]
    assert not errors, f"{path.name} failed typecheck: {errors[0].description}"
    result = codegen_compile(
        ast, source=source, file=str(p), resolved_modules=resolved,
        expr_semantic_types=artifacts.expr_semantic_types,
    )
    assert result.ok, f"{path.name} failed codegen"
    return result


class TestDualTargetConformance:
    """Every deterministic run-level conformance program must behave
    byte-identically under the core target (vera.* host bindings) and
    the wasi-p2 target (stock wasip2 host).  This is the plan's
    honesty test: the component is only 'a WASI Preview 2 target' if
    the same programs produce the same output with no Vera bindings."""

    @pytest.mark.parametrize("fname", _conformance_run_ids())
    def test_core_and_wasi_p2_agree(self, fname: str) -> None:
        import re as _re

        from vera.codegen import execute
        from vera.runtime.wasi_host import execute_wasi_p2

        result = _compile_path(_CONF_DIR / fname)

        used = set(_re.findall(r'\(import "vera" "(\w+)"', result.wat))
        nondet = used & _NONDETERMINISTIC_OPS
        if nondet:
            pytest.skip(f"nondeterministic ops {sorted(nondet)}")

        core = execute(result, capture_stderr=True)
        try:
            comp = execute_wasi_p2(result)
        except ValueError as exc:
            pytest.skip(f"family gate: {exc}")

        assert comp.stdout == core.stdout
        assert comp.stderr == core.stderr
        # wasi:cli/exit carries ok/err only — the documented degradation.
        expected_exit = (
            None if core.exit_code is None
            else (0 if core.exit_code == 0 else 1)
        )
        assert comp.exit_code == expected_exit
        # Scalar mains (s64/float64/Unit) have a plain lift; pointer-
        # returning mains fall back to wasi:cli/run and yield None —
        # comparing raw heap pointers across two heaps means nothing.
        if comp.value is not None:
            assert comp.value == core.value


# =====================================================================
# Stock-host smoke test (dev-only: needs the wasmtime CLI on PATH)
# =====================================================================

@pytest.mark.skipif(
    shutil.which("wasmtime") is None,
    reason="stock wasmtime CLI not installed (dev-only smoke test)",
)
class TestStockWasmtimeCli:
    """The plan's honesty bar: the artifact `vera compile --target
    wasi-p2` writes must run under a STOCK wasip2 host with no Vera
    bindings at all — a different implementation surface than
    wasmtime-py's add_wasip2 linker used everywhere above."""

    def test_component_runs_under_stock_wasmtime(
        self, tmp_path: Path,
    ) -> None:
        import subprocess

        from vera.cli import cmd_compile

        src = _write_vera(tmp_path, HELLO)
        out = tmp_path / "prog.wasm"
        assert cmd_compile(src, target="wasi-p2", output=str(out)) == 0
        proc = subprocess.run(
            ["wasmtime", "run", str(out)],
            capture_output=True, text=True, encoding="utf-8",
            timeout=60, check=False,
        )
        assert proc.returncode == 0, proc.stderr
        assert proc.stdout == "Hello, WASI!"
