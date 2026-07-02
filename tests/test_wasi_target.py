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
import re
import shutil
import subprocess
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
        # The guest samples wasi:clocks/wall-clock, the bracket samples
        # time.time() — two different clock APIs whose quantization can
        # disagree by a few ms (a 1 ms overshoot was observed on
        # windows-latest in PR #849's CI).  The slack still catches the
        # real failure modes — a wrong unit (s / us / ns are orders of
        # magnitude off) or a garbage read.
        clock_skew_ms = 100
        assert before_ms - clock_skew_ms <= int(out) <= after_ms + clock_skew_ms

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

    def test_random_int_equal_bounds_is_deterministic(self) -> None:
        """low == high pins inclusivity of BOTH bounds without chance:
        an exclusive upper bound could only return low-1 or reject
        forever (CR review, PR #849)."""
        result = _compile_ok("""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{
  Random.random_int(4, 4)
}
""")
        value, _, _ = _run_component(result)
        assert value == 4

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
        # Binary mode so the bytes on disk are LF exactly on every
        # platform (text mode writes \r\n on Windows, which turned
        # this into an accidental CRLF test — see the dedicated CRLF
        # test below for that case).
        handle = tempfile.NamedTemporaryFile(
            mode="wb", suffix=".txt", delete=False,
        )
        try:
            with handle:
                handle.write(b"first line\nsecond\n")
            _, out, _ = _run_component(result, stdin_path=handle.name)
        finally:
            os.unlink(handle.name)
        assert out == "first line|s"

    def test_read_line_strips_crlf_like_the_core_host(self) -> None:
        """Core-path read_line goes through Python's universal-newlines
        text layer and never returns a trailing \\r, on any platform —
        the adapter must match for CRLF input (what Windows pipes and
        text-mode-written files actually contain).  Surfaced by the
        windows-latest CI matrix on PR #849."""
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(@String.0);
  IO.print("|");
  IO.print(nat_to_string(string_length(@String.0)))
}
""")
        handle = tempfile.NamedTemporaryFile(
            mode="wb", suffix=".txt", delete=False,
        )
        try:
            with handle:
                handle.write(b"crlf line\r\nnext\r\n")
            _, out, _ = _run_component(result, stdin_path=handle.name)
        finally:
            os.unlink(handle.name)
        assert out == "crlf line|9"

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


# =====================================================================
# CodeRabbit round-1 regressions (PR #849)
# =====================================================================

class TestReservedMarkerScan:
    """The reserved-identifier check must inspect WAT identifiers, not
    data-segment payloads — a program PRINTING "$wasi_tbl" is fine; a
    program DEFINING a fn named wasi_tbl is a real collision."""

    def test_literal_containing_marker_is_accepted(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("$wasi_tbl is a nice name")
}
""")
        _, out, _ = _run_component(result)
        assert out == "$wasi_tbl is a nice name"

    def test_identifier_collision_is_still_rejected(self) -> None:
        result = _compile_ok("""\
private fn wasi_tbl(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  1
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  wasi_tbl()
}
""")
        with pytest.raises(ValueError, match="reserved identifier"):
            emit_wasi_component(result)

    def test_longer_identifier_sharing_the_prefix_is_accepted(
        self,
    ) -> None:
        """`$wasi_tblish` contains `$wasi_tbl` but is a DIFFERENT
        identifier — the check requires an identifier boundary after
        each exact marker (CR review round 2, PR #849)."""
        result = _compile_ok("""\
private fn wasi_tblish(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  7
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  wasi_tblish()
}
""")
        value, _, _ = _run_component(result)
        assert value == 7


class TestPreopenDescriptorCache:
    """get-directories returns a fresh OWNED descriptor list per call;
    the adapter must fetch once and cache, or every IO.read_file /
    write_file leaks a handle into the instance's resource table."""

    def test_emitted_wat_caches_the_preopen_descriptor(self) -> None:
        wat = _emit("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_file("x.txt") {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }
}
""")
        assert "(global $preopen_fd (mut i32) (i32.const -2))" in wat
        # Exactly one fetch site, guarded by the unfetched sentinel.
        assert wat.count("call $l_get_dirs") == 1
        assert "global.get $preopen_fd" in wat

    def test_repeated_file_ops_still_work_through_the_cache(
        self, tmp_path: Path,
    ) -> None:
        """60 read_file calls through one instance — every read goes
        through the cached descriptor and returns the same content."""
        result = _compile_ok("""\
private fn read_n(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(<IO>)
{
  if @Nat.0 == 0 then {
    0
  } else {
    match IO.read_file("cached.txt") {
      Ok(@String) -> string_length(@String.0),
      Err(@String) -> 0
    };
    read_n(@Nat.0 - 1)
  }
}

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  read_n(60);
  match IO.read_file("cached.txt") {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(string_concat("ERR:", @String.0))
  }
}
""")
        (tmp_path / "cached.txt").write_text("payload", encoding="utf-8")
        _, out, _ = _run_component(result, preopen=str(tmp_path))
        assert out == "payload"


class TestStdinTailSemantics:
    """Pins for the read_line tail rules (CR review round 2, PR #849),
    each verified against the core host's universal-newlines behavior:

    - \\r at EOF: Python's text layer treats it as a line break, so the
      core path returns the line WITHOUT it — the adapter's
      unconditional trailing-\\r strip is parity, and gating the strip
      on a \\n terminator would diverge.
    - lone \\r as a SEPARATOR: the core path splits there; the adapter
      keeps it as content — the documented spec §13.6 divergence
      (matching would need cross-call byte pushback in WAT)."""

    def test_cr_at_eof_is_stripped_like_the_core_host(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(@String.0);
  IO.print("|");
  IO.print(nat_to_string(string_length(@String.0)))
}
""")
        handle = tempfile.NamedTemporaryFile(
            mode="wb", suffix=".txt", delete=False,
        )
        try:
            with handle:
                handle.write(b"abc\r")
            _, out, _ = _run_component(result, stdin_path=handle.name)
        finally:
            os.unlink(handle.name)
        assert out == "abc|3"

    def test_lone_cr_separator_stays_content_as_documented(self) -> None:
        result = _compile_ok("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(nat_to_string(string_length(@String.0)))
}
""")
        handle = tempfile.NamedTemporaryFile(
            mode="wb", suffix=".txt", delete=False,
        )
        try:
            with handle:
                handle.write(b"a\rb\nrest\n")
            _, out, _ = _run_component(result, stdin_path=handle.name)
        finally:
            os.unlink(handle.name)
        # "a\rb" is 3 bytes of content — the lone \r separator is NOT
        # a terminator on this target (spec §13.6).
        assert out == "3"


# =====================================================================
# Server world (Stage D): wasi:http/incoming-handler@0.2.0
# =====================================================================

HTTP_SERVER_EXAMPLE = (
    Path(__file__).parent.parent / "examples" / "http_server.vera"
).read_text(encoding="utf-8")

# Differential handler: echoes method|path|<x-probe header lookup>|body
# — every field the serve wrapper marshals feeds the response, so the
# host-vs-served differential can see any marshalling drift.
DIFF_HANDLER = """\
private fn probe_of(@Map<String, String> -> @String)
  requires(true) ensures(true) effects(pure)
{
  match map_get(@Map<String, String>.0, "x-probe") {
    Some(@String) -> @String.0,
    None -> "absent"
  }
}

public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  match @Request.0 {
    Request(@String, @String, @Map<String, String>, @String) ->
      Response(200,
        map_insert(map_new(), "content-type", "text/plain"),
        string_concat(@String.2, string_concat("|",
          string_concat(@String.1, string_concat("|",
            string_concat(probe_of(@Map<String, String>.0),
              string_concat("|", @String.0)))))))
  }
}
"""

# Map-order/battery handler: insert a,b,g; update b in place; remove a;
# emits keys|values|size|contains — pins position-preserving update,
# survivor order, and the whole §3.2 op family in one body.  The
# response headers map is EMPTY (exercises 0-entry from-list).
MAP_ORDER_HANDLER = """\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  let @Map<String, String> = map_insert(map_insert(map_insert(map_new(), "alpha", "1"), "beta", "2"), "gamma", "3");
  let @Map<String, String> = map_remove(map_insert(@Map<String, String>.0, "beta", "9"), "alpha");
  Response(200, map_new(),
    string_concat(string_join(map_keys(@Map<String, String>.0), ","),
      string_concat("|", string_concat(string_join(map_values(@Map<String, String>.0), ","),
        string_concat("|", string_concat(nat_to_string(map_size(@Map<String, String>.0)),
          string_concat("|", bool_to_string(map_contains(@Map<String, String>.0, "gamma")))))))))
}
"""

TRAP_HANDLER = """\
private fn checked(@Int -> @Int)
  requires(@Int.0 > 10) ensures(true) effects(pure)
{
  @Int.0
}

public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  Response(checked(1), map_new(), "unreachable-body")
}
"""

FORBIDDEN_HEADER_HANDLER = """\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  Response(200, map_insert(map_new(), "connection", "close"), "nope")
}
"""

BAD_STATUS_HANDLER = """\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  Response(70000, map_new(), "nope")
}
"""

PRINT_HANDLER = """\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer, IO>)
{
  IO.print("served one request\\n");
  Response(200, map_new(), "printed")
}
"""


def _emit_server(source: str) -> str:
    return emit_wasi_component(_compile_ok(source), world="server")


class TestServerWorldEmission:
    """Hermetic pins: the server-world text parses as a component
    (wasmtime-py runs full component validation, compiling both core
    modules) and carries exactly the incoming-handler entry surface."""

    def test_http_server_example_parses_as_component(self) -> None:
        Component(_ENGINE, _emit_server(HTTP_SERVER_EXAMPLE))

    def test_map_get_handler_parses_as_component(self) -> None:
        Component(_ENGINE, _emit_server(DIFF_HANDLER))

    def test_full_map_op_battery_parses_as_component(self) -> None:
        """keys/values/size/contains/remove all at once (slots 16-25)."""
        Component(_ENGINE, _emit_server(MAP_ORDER_HANDLER))

    def test_io_print_handler_parses_as_component(self) -> None:
        Component(_ENGINE, _emit_server(PRINT_HANDLER))

    def test_time_sleep_random_handler_parses_as_component(self) -> None:
        """The rest of the allowed IO/Random family in one handler —
        pins the clocks/poll/random interface closure in the server
        assembly (all proxy-world-linkable, design §1.3)."""
        Component(_ENGINE, _emit_server("""\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer, IO, Random>)
{
  IO.sleep(1);
  let @Nat = IO.time(());
  let @Int = Random.random_int(1, 6);
  IO.stderr("diag\\n");
  Response(200, map_new(), nat_to_string(@Nat.0))
}
"""))

    def test_incoming_handler_is_the_only_entry_export(self) -> None:
        wat = _emit_server(HTTP_SERVER_EXAMPLE)
        assert '(export "wasi:http/incoming-handler@0.2.0"' in wat
        assert "wasi:cli/run" not in wat
        assert '(export "main"' not in wat
        assert "__wasi_run" not in wat

    def test_lift_is_from_the_adapter(self) -> None:
        """The serve wrapper lives in the ADAPTER (design §1.2) — the
        incoming-handler lift must take the adapter's export, so the
        wasi:http lowers stay direct imports (never dispatch-table)."""
        wat = _emit_server(HTTP_SERVER_EXAMPLE)
        assert '(canon lift (core func $adapter "handle"))' in wat

    def test_dispatch_table_is_32_slots(self) -> None:
        """Map family lands at slots 16+; the table must grow from the
        cli world's 16 (design §1.3)."""
        wat = _emit_server(HTTP_SERVER_EXAMPLE)
        assert '(table $wasi_tbl (export "wasi_tbl") 32 32 funcref)' in wat

    def test_every_wasi_version_is_0_2_0(self) -> None:
        wat = _emit_server(MAP_ORDER_HANDLER)
        versions = set(re.findall(r"wasi:[a-z/-]+@(\d+\.\d+\.\d+)", wat))
        assert versions == {"0.2.0"}

    def test_map_wrapper_tag_matches_the_heap_constant(self) -> None:
        """The emitter pins the #706 wrapper tag word without importing
        the (wasmtime-loading) heap module — this is the drift check."""
        from vera.codegen.wasi import _MAP_WRAPPER_TAG
        from vera.runtime.heap import _MAP_HANDLE_TAG

        assert _MAP_WRAPPER_TAG == _MAP_HANDLE_TAG

    def test_emit_does_not_mutate_compile_result(self) -> None:
        result = _compile_ok(HTTP_SERVER_EXAMPLE)
        before_wat = result.wat
        before_bytes = result.wasm_bytes
        emit_wasi_component(result, world="server")
        assert result.wat == before_wat
        assert result.wasm_bytes == before_bytes


class TestServerWorldGate:
    """#305 handler validation + the server family gate: every
    rejection is a clean diagnostic naming the offender — never a
    silent fallback or a broken component."""

    def test_unknown_world_is_rejected(self) -> None:
        result = _compile_ok(HELLO)
        with pytest.raises(ValueError, match="unknown wasi-p2 world"):
            emit_wasi_component(result, world="bogus")

    def test_missing_handle_is_rejected(self) -> None:
        result = _compile_ok(HELLO)
        with pytest.raises(
            ValueError,
            match=r"--target wasi-p2 --world server.*'handle'",
        ):
            emit_wasi_component(result, world="server")

    def test_wrong_signature_handle_is_rejected(self) -> None:
        result = _compile_ok("""\
public fn handle(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0
}
""")
        with pytest.raises(ValueError, match="Request"):
            emit_wasi_component(result, world="server")

    def test_file_io_handler_is_rejected_naming_read_file(self) -> None:
        result = _compile_ok("""\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer, IO>)
{
  match IO.read_file("x.txt") {
    Ok(@String) -> Response(200, map_new(), @String.0),
    Err(@String) -> Response(500, map_new(), @String.0)
  }
}
""")
        with pytest.raises(ValueError, match=r"IO\.read_file"):
            emit_wasi_component(result, world="server")

    def test_get_env_handler_is_rejected_naming_get_env(self) -> None:
        result = _compile_ok("""\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer, IO>)
{
  match IO.get_env("HOME") {
    Some(@String) -> Response(200, map_new(), @String.0),
    None -> Response(404, map_new(), "none")
  }
}
""")
        with pytest.raises(ValueError, match=r"IO\.get_env"):
            emit_wasi_component(result, world="server")

    def test_non_string_map_is_rejected_naming_the_instantiation(
        self,
    ) -> None:
        result = _compile_ok("""\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  let @Map<Int, Int> = map_insert(map_new(), 1, 2);
  Response(200, map_new(), nat_to_string(map_size(@Map<Int, Int>.0)))
}
""")
        with pytest.raises(
            ValueError, match=r"map_insert\$ki_vi.*|Map<String, String>",
        ) as exc:
            emit_wasi_component(result, world="server")
        assert "map_insert$ki_vi" in str(exc.value)
        assert "Map<String, String>" in str(exc.value)

    def test_math_handler_is_rejected_naming_math(self) -> None:
        result = _compile_ok("""\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  Response(200, map_new(), float_to_string(sin(1.0)))
}
""")
        with pytest.raises(ValueError, match="math"):
            emit_wasi_component(result, world="server")

    def test_http_client_handler_is_rejected_naming_http(self) -> None:
        result = _compile_ok("""\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer, Http>)
{
  match Http.get("http://example.invalid/") {
    Ok(@String) -> Response(200, map_new(), @String.0),
    Err(@String) -> Response(502, map_new(), @String.0)
  }
}
""")
        with pytest.raises(ValueError, match="http"):
            emit_wasi_component(result, world="server")


class TestCliWorldPin:
    """The server world must not leak into cli emission: the default
    world is cli, its text is world-argument-invariant, and it carries
    none of the server machinery.  (The full Stage-C suite above runs
    through the same default path — this class pins the seams.)"""

    def test_default_world_equals_explicit_cli(self) -> None:
        result = _compile_ok(KITCHEN_SINK)
        assert emit_wasi_component(result) == emit_wasi_component(
            result, world="cli",
        )

    def test_cli_emission_carries_no_server_machinery(self) -> None:
        wat = emit_wasi_component(_compile_ok(KITCHEN_SINK))
        assert '(table $wasi_tbl (export "wasi_tbl") 16 16 funcref)' in wat
        assert "wasi:http" not in wat
        assert "serve_handle" not in wat
        assert "$op_map_" not in wat
        assert '(export "wasi:cli/run@0.2.0"' in wat

    def test_cli_world_still_rejects_map_programs(self) -> None:
        result = _compile_ok(HTTP_SERVER_EXAMPLE)
        with pytest.raises(ValueError, match="map"):
            emit_wasi_component(result)


class TestServerLayoutTripwire:
    """The serve wrapper takes Request/Response offsets from
    ``adt_layouts`` at emit time with the same shape guard as
    ``build_request_adt`` — a moved prelude shape must fail loudly,
    never emit a desynced wrapper."""

    def test_doctored_request_layout_is_rejected(self) -> None:
        import dataclasses

        result = _compile_ok(HTTP_SERVER_EXAMPLE)
        real = result.adt_layouts["Request"]["Request"]
        doctored = dataclasses.replace(
            real,
            field_offsets=(
                (4, "i32_pair"), (12, "i32_pair"), (20, "i64"),
                (28, "i32_pair"),
            ),
        )
        layouts = dict(result.adt_layouts)
        layouts["Request"] = {"Request": doctored}
        bad = dataclasses.replace(result, adt_layouts=layouts)
        with pytest.raises(ValueError, match="Request layout"):
            emit_wasi_component(bad, world="server")

    def test_doctored_response_layout_is_rejected(self) -> None:
        import dataclasses

        result = _compile_ok(HTTP_SERVER_EXAMPLE)
        real = result.adt_layouts["Response"]["Response"]
        doctored = dataclasses.replace(
            real,
            field_offsets=((8, "i32"), (12, "i32"), (16, "i32_pair")),
        )
        layouts = dict(result.adt_layouts)
        layouts["Response"] = {"Response": doctored}
        bad = dataclasses.replace(result, adt_layouts=layouts)
        with pytest.raises(ValueError, match="Response layout"):
            emit_wasi_component(bad, world="server")


# =====================================================================
# Server world live smoke (dev-only: needs the wasmtime CLI on PATH)
# =====================================================================

_SERVE_ADDR_RE = re.compile(r"http://127\.0\.0\.1:(\d+)/")


class _WasmtimeServe:
    """Context manager: `wasmtime serve` a component text on an
    ephemeral port (``--addr 127.0.0.1:0``; the bound port is parsed
    from the "Serving HTTP on ..." banner — no bare sleeps, a
    deadline-polled reader thread collects the merged log for
    assertions)."""

    def __init__(self, component_text: str, tmp_path: Path,
                 name: str = "component.wat") -> None:
        import subprocess
        import threading

        wat_file = tmp_path / name
        wat_file.write_text(component_text, encoding="utf-8")
        self._proc = subprocess.Popen(
            ["wasmtime", "serve", "--addr", "127.0.0.1:0", str(wat_file)],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding="utf-8",
        )
        self._lines: list[str] = []
        self._reader = threading.Thread(target=self._drain, daemon=True)
        self._reader.start()
        try:
            self.port = self._wait_port()
        except Exception:
            self._proc.terminate()
            raise

    def _drain(self) -> None:
        assert self._proc.stdout is not None
        for line in self._proc.stdout:
            self._lines.append(line)

    def _wait_port(self) -> int:
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline:
            for line in list(self._lines):
                m = _SERVE_ADDR_RE.search(line)
                if m:
                    return int(m.group(1))
            if self._proc.poll() is not None:
                raise RuntimeError(f"wasmtime serve exited:\n{self.log()}")
            time.sleep(0.05)
        raise RuntimeError(f"wasmtime serve never bound:\n{self.log()}")

    def log(self) -> str:
        return "".join(self._lines)

    def settled_log(self) -> str:
        """Log after a short deadline-poll for the async writer."""
        deadline = time.monotonic() + 2
        seen = len(self._lines)
        while time.monotonic() < deadline:
            time.sleep(0.05)
            if len(self._lines) == seen:
                break
            seen = len(self._lines)
        return self.log()

    def __enter__(self) -> "_WasmtimeServe":
        return self

    def __exit__(self, *exc: object) -> None:
        self._proc.terminate()
        try:
            self._proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            # SIGTERM ignored — force-kill rather than leaking the
            # serve process and masking the test's real assertion.
            self._proc.kill()
            self._proc.wait(timeout=10)


def _serve_request(
    port: int, method: str, path: str,
    headers: list[tuple[str, str]], body: str,
) -> tuple[int, dict[str, str], str]:
    """One HTTP request via http.client (duplicate headers supported —
    urllib's add_header dedups, which would mask the later-wins test)."""
    import http.client

    deadline = time.monotonic() + 10
    while True:
        conn = http.client.HTTPConnection("127.0.0.1", port, timeout=120)
        try:
            conn.putrequest(
                method, path, skip_host=True, skip_accept_encoding=True,
            )
            conn.putheader("Host", f"127.0.0.1:{port}")
            for key, value in headers:
                conn.putheader(key, value)
            data = body.encode("utf-8")
            conn.putheader("Content-Length", str(len(data)))
            conn.endheaders()
            if data:
                conn.send(data)
            resp = conn.getresponse()
            return (
                resp.status,
                {k.lower(): v for k, v in resp.getheaders()},
                resp.read().decode("utf-8"),
            )
        except ConnectionRefusedError:
            if time.monotonic() > deadline:
                raise
            time.sleep(0.05)
        finally:
            conn.close()


def _host_response(
    result: CompileResult, method: str, path: str,
    headers: list[tuple[str, str]], body: str,
) -> dict[str, object]:
    """The #305 host path for the differential.  Header list -> dict
    with the driver's semantics (lower-cased keys, later value wins —
    exactly what ``dict(self.headers.items())`` does in server.py)."""
    from vera.codegen.api import HttpRequestData, execute

    merged: dict[str, str] = {}
    for key, value in headers:
        merged[key.lower()] = value
    er = execute(
        result, fn_name="handle",
        http_request=HttpRequestData(
            method=method, path=path, headers=merged, body=body,
        ),
    )
    resp = er.http_response
    assert resp is not None
    return resp


@pytest.mark.skipif(
    shutil.which("wasmtime") is None,
    reason="stock wasmtime CLI not installed (dev-only smoke test)",
)
class TestWasmtimeServeSmoke:
    """The Stage-D honesty bar: the emitted artifact serves HTTP under
    STOCK `wasmtime serve` with no flags and no Vera bindings, and the
    served behavior matches the #305 host driver (the differential
    that catches host-map vs in-guest-map semantic drift, which green
    unit suites cannot)."""

    def test_http_server_example_round_trips(
        self, tmp_path: Path,
    ) -> None:
        wat = _emit_server(HTTP_SERVER_EXAMPLE)
        with _WasmtimeServe(wat, tmp_path) as srv:
            status, headers, body = _serve_request(
                srv.port, "GET", "/", [], "",
            )
            assert (status, body) == (200, "hello from vera")
            assert headers.get("content-type") == "text/plain"
            status, _, body = _serve_request(
                srv.port, "POST", "/echo", [], "ping-pong",
            )
            assert (status, body) == (200, "ping-pong")
            status, headers, body = _serve_request(
                srv.port, "GET", "/nope", [], "",
            )
            assert (status, body) == (404, "not found")
            assert headers.get("content-type") == "text/plain"

    def test_header_matrix_differential(self, tmp_path: Path) -> None:
        """Same handler, host-backed core execution vs the served
        component, over methods x paths x header shapes (mixed-case,
        absent, DUPLICATE later-wins, multi) x body sizes — status,
        handler-set headers, and body must agree."""
        result = _compile_ok(DIFF_HANDLER)
        matrix: list[tuple[str, str, list[tuple[str, str]], str]] = [
            ("GET", "/", [], ""),
            ("GET", "/x?q=1", [("X-Probe", "MixedCase")], ""),
            ("POST", "/echo",
             [("x-probe", "first"), ("X-PROBE", "second")], "hello"),
            ("PUT", "/p", [("x-probe", "v"), ("x-other", "y")],
             "b" * 4096),
            ("DELETE", "/d", [], "tiny"),
            ("PATCH", "/many",
             [(f"x-h{i:02d}", f"v{i}") for i in range(40)]
             + [("X-Probe", "needle")], "x"),
        ]
        wat = emit_wasi_component(result, world="server")
        with _WasmtimeServe(wat, tmp_path) as srv:
            for method, path, headers, body in matrix:
                s_status, s_headers, s_body = _serve_request(
                    srv.port, method, path, headers, body,
                )
                host = _host_response(result, method, path, headers, body)
                assert s_status == host["status"], (method, path)
                assert s_body == host["body"], (method, path)
                for key, value in host["headers"].items():  # type: ignore[union-attr]
                    assert s_headers.get(key.lower()) == value, (
                        method, path, key,
                    )

    def test_map_order_differential(self, tmp_path: Path) -> None:
        """Position-preserving update + survivor order + size +
        contains: the served in-guest map ops must agree with the
        host-backed ops byte-for-byte (keys/values join order is the
        observable)."""
        result = _compile_ok(MAP_ORDER_HANDLER)
        wat = emit_wasi_component(result, world="server")
        with _WasmtimeServe(wat, tmp_path) as srv:
            s_status, _, s_body = _serve_request(
                srv.port, "GET", "/", [], "",
            )
        host = _host_response(result, "GET", "/", [], "")
        assert (s_status, s_body) == (host["status"], host["body"])
        # And pin the actual semantics, not just agreement: update in
        # place (beta first, value 9), alpha removed, gamma appended.
        assert s_body == "beta,gamma|9,3|2|true"

    def test_io_print_reaches_the_serve_console(
        self, tmp_path: Path,
    ) -> None:
        wat = _emit_server(PRINT_HANDLER)
        with _WasmtimeServe(wat, tmp_path) as srv:
            status, _, body = _serve_request(srv.port, "GET", "/", [], "")
            assert (status, body) == (200, "printed")
            log = srv.settled_log()
        assert "stdout [0] :: served one request" in log

    def test_contract_violation_maps_to_500_with_diagnostics(
        self, tmp_path: Path,
    ) -> None:
        wat = _emit_server(TRAP_HANDLER)
        with _WasmtimeServe(wat, tmp_path) as srv:
            status, _, _ = _serve_request(srv.port, "GET", "/", [], "")
            assert status == 500
            log = srv.settled_log()
        # wasmtime's own 500 + symbolized backtrace naming the guest
        # frames, and the violation text via the stderr channel.
        assert "worker failed" in log
        assert "Main!handle" in log
        assert "requires" in log

    def test_forbidden_response_header_is_a_graceful_500(
        self, tmp_path: Path,
    ) -> None:
        """from-list errs on `connection` -> the wrapper answers via
        outparam.set(err(internal-error)) — a 500 WITHOUT a guest trap
        (no `worker failed` backtrace in the serve log)."""
        wat = _emit_server(FORBIDDEN_HEADER_HANDLER)
        with _WasmtimeServe(wat, tmp_path) as srv:
            status, _, _ = _serve_request(srv.port, "GET", "/", [], "")
            assert status == 500
            log = srv.settled_log()
        assert "worker failed" not in log

    def test_out_of_range_status_is_a_graceful_500(
        self, tmp_path: Path,
    ) -> None:
        """Status 70000 exceeds u16 — the wrapper pre-checks (the
        set-status lift would trap) and takes the same graceful path."""
        wat = _emit_server(BAD_STATUS_HANDLER)
        with _WasmtimeServe(wat, tmp_path) as srv:
            status, _, _ = _serve_request(srv.port, "GET", "/", [], "")
            assert status == 500
            log = srv.settled_log()
        assert "worker failed" not in log

    def test_big_body_gc_stress_round_trip(self, tmp_path: Path) -> None:
        """1 MiB POST /echo (+50 headers): the ~2 MiB of transient
        guest allocations force collections through the serve
        wrapper's copy-out — a missing root corrupts or traps."""
        wat = _emit_server(HTTP_SERVER_EXAMPLE)
        big = ("0123456789abcdef" * 65536)[:1048576]
        headers = [(f"x-h{i:02d}", "v" * 40) for i in range(50)]
        with _WasmtimeServe(wat, tmp_path) as srv:
            status, _, body = _serve_request(
                srv.port, "POST", "/echo", headers, big,
            )
        assert status == 200
        assert body == big

    def test_request_build_rooting_is_load_bearing(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Mutation-validation of the delicate WAT (TESTING.md rule):
        with an eager-GC build (collect on every alloc), stripping the
        method-string shadow_push from the emitted wrapper must break
        the round-trip — proving the fixture actually exercises the
        rooting discipline rather than passing by luck."""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        result = _compile_ok(DIFF_HANDLER)
        monkeypatch.delenv("VERA_EAGER_GC")
        wat = emit_wasi_component(result, world="server")
        marker = "    local.get $mp\n    call $shadow_push ;; root: method\n"
        assert marker in wat
        expected = (200, "GET|/probe|marker|payload")
        with _WasmtimeServe(wat, tmp_path, "rooted.wat") as srv:
            status, _, body = _serve_request(
                srv.port, "GET", "/probe", [("X-Probe", "marker")],
                "payload",
            )
            assert (status, body) == expected, "eager-GC baseline broke"
        mutated = wat.replace(marker, "", 1)
        assert mutated != wat
        with _WasmtimeServe(mutated, tmp_path, "unrooted.wat") as srv:
            status, _, body = _serve_request(
                srv.port, "GET", "/probe", [("X-Probe", "marker")],
                "payload",
            )
        assert (status, body) != expected, (
            "dropping the method root did not break the round-trip — "
            "the GC-stress fixture no longer exercises rooting"
        )


# =====================================================================
# CLI integration: `--world server` (Stage D)
# =====================================================================

class TestCliServerWorld:
    """`vera compile --target wasi-p2 --world server` writes a binary
    component exporting wasi:http/incoming-handler; `vera run` rejects
    server-world artifacts (wasmtime-py cannot host wasi:http) with a
    pointer to `wasmtime serve`."""

    HANDLER_SRC = (Path(__file__).parent.parent
                   / "examples" / "http_server.vera")

    def test_compile_writes_server_component(self, tmp_path: Path) -> None:
        from vera.cli import cmd_compile

        out = tmp_path / "server.wasm"
        rc = cmd_compile(
            str(self.HANDLER_SRC), target="wasi-p2", world="server",
            output=str(out),
        )
        assert rc == 0
        Component(_ENGINE, out.read_bytes())

    def test_wat_prints_incoming_handler_export(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        from vera.cli import cmd_compile

        rc = cmd_compile(
            str(self.HANDLER_SRC), target="wasi-p2", world="server",
            wat=True,
        )
        assert rc == 0
        printed = capsys.readouterr().out
        assert printed.lstrip().startswith("(component")
        assert "wasi:http/incoming-handler@0.2.0" in printed

    def test_run_rejects_server_world(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        from vera.cli import cmd_run

        rc = cmd_run(
            str(self.HANDLER_SRC), target="wasi-p2", world="server",
        )
        assert rc == 1
        err = capsys.readouterr().err
        assert "wasmtime serve" in err

    def test_world_requires_wasi_p2_target(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        from vera.cli import cmd_compile

        rc = cmd_compile(
            str(self.HANDLER_SRC), target="wasm", world="server",
        )
        assert rc == 1
        assert "wasi-p2" in capsys.readouterr().err

    def test_missing_handler_is_a_clean_diagnostic(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        from vera.cli import cmd_compile

        src = tmp_path / "nohandle.vera"
        src.write_text(HELLO, encoding="utf-8")
        rc = cmd_compile(str(src), target="wasi-p2", world="server")
        assert rc == 1
        assert "handle" in capsys.readouterr().err

    def test_run_world_without_wasi_p2_is_a_usage_error(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """`vera run --world server` with the DEFAULT target must give
        the same usage error cmd_compile gives — not a message implying
        the user asked for wasi-p2 (review round 1, PR #850)."""
        from vera.cli import cmd_run

        rc = cmd_run(str(self.HANDLER_SRC), world="server")
        assert rc == 1
        err = capsys.readouterr().err
        assert "requires --target wasi-p2" in err

    def test_time_sleep_random_execute_under_serve(
        self, tmp_path: Path,
    ) -> None:
        """The clock/random adapters EXECUTE under stock wasmtime serve
        — not just parse (CR review round 1, PR #850).  Pins that the
        proxy world actually provides wall-clock, monotonic-clock/poll,
        and random at request time."""
        wat = _emit_server("""\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer, IO, Random>)
{
  match @Request.0 {
    Request(@String, @String, @Map<String, String>, @String) -> {
      IO.sleep(1);
      Response(
        200,
        map_new(),
        string_concat(
          nat_to_string(IO.time(())),
          string_concat("|", int_to_string(Random.random_int(1, 6)))
        )
      )
    }
  }
}
""")
        before_ms = int(time.time() * 1000)
        with _WasmtimeServe(wat, tmp_path) as srv:
            status, _, body = _serve_request(srv.port, "GET", "/", [], "")
        after_ms = int(time.time() * 1000)
        assert status == 200
        time_part, rand_part = body.split("|")
        # Cross-clock slack as in the cli-world time test.
        assert before_ms - 100 <= int(time_part) <= after_ms + 100
        assert 1 <= int(rand_part) <= 6
