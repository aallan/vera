"""Parity tests: Python/wasmtime vs Node.js/JS-runtime.

Every compilable Vera example must produce identical output in both runtimes.
This test file is run by pre-commit (on changes to browser/codegen files) and
by CI (on every PR).  It enforces that the JavaScript browser runtime stays
in sync with the Python reference runtime.

Requirements:
    - Node.js >= 18 must be available on PATH
    - The project must be installed in editable mode (pip install -e ".[dev]")
"""

from __future__ import annotations

import contextlib
import io
import json
import math
import random
import shutil
import struct
import subprocess
from pathlib import Path
from typing import Any

import pytest

from vera.codegen import compile as codegen_compile, execute
from vera.codegen.api import WasmTrapError
from vera.checker import typecheck
from vera.parser import parse_file
from vera.resolver import ModuleResolver
from vera.transform import transform
from vera.markdown import parse_markdown
from vera.markdown_grammar import js_grammar_block
from tests.md_parse_corpus import CLASS_REPROS, encode_json, md_corpus
from tests.json_domain_helpers import (
    ERR_PREFIX,
    INT_ROUNDS_TO_INFINITY,
    MAX_FINITE_AS_INT,
    accept_domain_src,
    err,
    ok,
)
from vera.wasm.json_serde import (
    lone_surrogate_message,
    _non_finite_message,
    non_finite_number_message,
    non_finite_parse_message,
    format_json_number,
)

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

ROOT = Path(__file__).parent.parent
EXAMPLES_DIR = ROOT / "examples"
HARNESS = ROOT / "vera" / "browser" / "harness.mjs"

# Skip the entire module if Node.js is not available or lacks exnref support
NODE = shutil.which("node")

def _node_supports_exnref() -> bool:
    """Check if the system Node.js supports --experimental-wasm-exnref."""
    if NODE is None:
        return False
    try:
        proc = subprocess.run(
            [NODE, "--experimental-wasm-exnref", "-e", "0"],
            capture_output=True, timeout=5,
            check=False,
        )
        return proc.returncode == 0
    except Exception:  # noqa: BLE001 — any failure means the node feature is unavailable
        return False

_HAS_EXNREF = _node_supports_exnref()
pytestmark = pytest.mark.skipif(
    not _HAS_EXNREF,
    reason="Node.js not available or lacks --experimental-wasm-exnref support",
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _compile_vera(source: str, tmp_path: Path) -> tuple[Path, list[str]]:
    """Compile inline Vera source to .wasm, returning (wasm_path, exports)."""
    vera_file = tmp_path / "test.vera"
    vera_file.write_text(source, encoding="utf-8")

    tree = parse_file(str(vera_file))
    ast = transform(tree)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(ast, vera_file)
    diags = resolver.errors + typecheck(
        ast, source, file=str(vera_file), resolved_modules=resolved,
    )
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"Type errors: {[e.description for e in errors]}"

    result = codegen_compile(
        ast, source=source, file=str(vera_file), resolved_modules=resolved,
    )
    assert result.ok, f"Compile errors: {result.diagnostics}"

    wasm_path = tmp_path / "test.wasm"
    wasm_path.write_bytes(result.wasm_bytes)
    return wasm_path, result.exports


def _compile_state_default(source: str, tmp_path: Path) -> tuple[Path, Any]:
    """Compile inline Vera source, returning (wasm_path, codegen result).

    Unlike :func:`_compile_vera` (which returns the export list), this keeps the
    full codegen ``result`` so :func:`_run_python` can execute it — used by the
    #920 State-default parity tests.
    """
    vera_file = tmp_path / "state_default.vera"
    vera_file.write_text(source, encoding="utf-8")
    tree = parse_file(str(vera_file))
    ast = transform(tree)
    result = codegen_compile(ast, source=source, file=str(vera_file))
    assert result.ok, f"Compile errors: {result.diagnostics}"
    wasm_path = tmp_path / "state_default.wasm"
    wasm_path.write_bytes(result.wasm_bytes)
    return wasm_path, result


def _compile_file(path: Path, tmp_path: Path) -> tuple[Path, Any]:
    """Compile a .vera file, returning (wasm_path, codegen result)."""
    source = path.read_text(encoding="utf-8")
    tree = parse_file(str(path))
    ast = transform(tree)
    resolver = ModuleResolver(_root=path.parent)
    resolved = resolver.resolve_imports(ast, path)
    diags = resolver.errors + typecheck(
        ast, source, file=str(path), resolved_modules=resolved,
    )
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"Type errors in {path.name}: {[e.description for e in errors]}"

    result = codegen_compile(
        ast, source=source, file=str(path), resolved_modules=resolved,
    )
    assert result.ok, f"Compile errors in {path.name}: {result.diagnostics}"

    wasm_path = tmp_path / "test.wasm"
    wasm_path.write_bytes(result.wasm_bytes)
    return wasm_path, result


def _run_python(result: Any, fn_name: str | None = None,
                args: list[int | float] | None = None,
                cli_args: list[str] | None = None) -> Any:
    """Execute a compiled module in Python/wasmtime."""
    return execute(
        result,
        fn_name=fn_name,
        args=args,
        cli_args=cli_args or [],
    )


def _run_node(
    wasm_path: Path,
    *,
    fn: str | None = None,
    fn_args: list[str] | None = None,
    stdin: str | None = None,
    args: str | None = None,
    env: str | None = None,
) -> dict[str, Any]:
    """Execute a .wasm module via the Node.js harness, returning parsed JSON."""
    cmd: list[str] = [
        NODE or "node",
        # Enable WASM exception handling (exnref) for Vera's Exn<T> effect
        "--experimental-wasm-exnref",
        str(HARNESS),
        str(wasm_path),
    ]
    if fn:
        cmd.extend(["--fn", fn])
    if stdin is not None:
        cmd.extend(["--stdin", stdin])
    if args is not None:
        cmd.extend(["--args", args])
    if env is not None:
        cmd.extend(["--env", env])
    if fn_args:
        cmd.append("--")
        cmd.extend(fn_args)

    proc = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        encoding="utf-8",
        timeout=60,  # Windows runner Node startup variance + cold V8 exnref codegen — see #694
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"Node harness failed (rc={proc.returncode}):\n"
            f"stderr: {proc.stderr}\nstdout: {proc.stdout}"
        )
    return json.loads(proc.stdout)


def _both_stdouts(src: str, tmp_path: Path, name: str = "parity") -> tuple[str, str]:
    """Compile ``src`` ONCE, run the same ``.wasm`` under wasmtime and Node,
    and return ``(native_stdout, browser_stdout)`` without comparing them.

    Because both runtimes execute identical module bytes, any divergence
    isolates a host import in ``vera/browser/runtime.mjs`` — the module
    itself cannot be at fault.  Used directly only by the cases that pin a
    *known* divergence as two explicit strings; everything else goes
    through :func:`_parity_stdout`.
    """
    src_path = tmp_path / f"{name}.vera"
    src_path.write_text(src, encoding="utf-8")
    wasm_path, result = _compile_file(src_path, tmp_path)
    py_out = _run_python(result).stdout
    node = _run_node(wasm_path)
    assert not node.get("error"), (
        f"Node harness reported error: {node.get('error')!r}"
    )
    return str(py_out), str(node["stdout"])


def _both_failures(src: str, tmp_path: Path, name: str) -> tuple[str, str]:
    """Compile ``src`` ONCE, run the same ``.wasm`` under both runtimes
    expecting each to FAIL, and return ``(native_message, browser_message)``.

    The failure-side counterpart to :func:`_both_stdouts`, for operations
    whose contract is "refuse loudly" rather than "return a value".  Each
    side asserts that the call did not succeed, so a host that quietly
    produced output — which is exactly what the browser did with a NaN
    ``JNumber`` before #1293 — fails here rather than reading as a pass.
    """
    src_path = tmp_path / f"{name}.vera"
    src_path.write_text(src, encoding="utf-8")
    wasm_path, result = _compile_file(src_path, tmp_path)

    # ``tee_stdout`` mirrors every ``IO.print`` to ``sys.stdout`` as it
    # happens, so redirecting it gives the native side the same
    # observation the Node harness gives for free: what reached the
    # terminal, in real time, before the call failed.  Since #1302
    # ``execute`` also carries the buffer on ``WasmTrapError.stdout`` for
    # a host-callback failure — it used to discard it — but the tee is
    # what this helper wants, because it answers "did anything actually
    # get written?" for BOTH failure shapes without the helper having to
    # know which one it caught.
    native_tee = io.StringIO()
    try:
        with contextlib.redirect_stdout(native_tee):
            native_out = execute(result, tee_stdout=True)
    except Exception as exc:  # noqa: BLE001 — any failure is the signal
        native_msg = str(exc)
    else:
        raise AssertionError(
            "native runtime did not fail; "
            f"stdout={native_out.stdout!r}"
        )
    assert native_tee.getvalue() == "", (
        "native runtime produced output on a failing call: "
        f"{native_tee.getvalue()!r}"
    )

    node = _run_node(wasm_path)
    browser_msg = str(node.get("error") or "")
    assert browser_msg, (
        "browser runtime did not fail; "
        f"stdout={node['stdout']!r}"
    )
    assert node["stdout"] == "", (
        "browser runtime produced output on a failing call: "
        f"{node['stdout']!r}"
    )
    return native_msg, browser_msg


def _parity_stdout(src: str, tmp_path: Path, name: str = "parity") -> str:
    """Compile ``src`` ONCE, run it under both runtimes, assert byte-identical
    stdout, and return the (shared) value.

    The single parity helper for the whole module: ``TestBrowserDecimalExact856``
    and the #349 coverage classes below both call it, passing ``name`` to keep
    their fixtures' ``.vera`` filenames distinct.
    """
    py_out, node_out = _both_stdouts(src, tmp_path, name)
    assert node_out == py_out, (
        "Browser↔native divergence:\n"
        f"  Python (wasmtime): {py_out!r}\n"
        f"  Node   (browser):  {node_out!r}"
    )
    return py_out


# ---------------------------------------------------------------------------
# Examples with main — parametric stdout parity
# ---------------------------------------------------------------------------

# Examples that export main and can be run in both runtimes.
# Excludes:
#   - io_operations: uses IO.read_line interactively
#   - file_io: uses IO.read_file/write_file (browser returns Result.Err)
#   - database: uses DB.query/DB.execute (browser returns Result.Err)
#   - sqlitedb: uses DB.query on an on-disk file (browser returns Result.Err)
#   - modules: depends on imports (doesn't compile standalone)
EXAMPLES_WITH_MAIN = [
    "hello_world",
    "base64",
    "string_ops",
    "url_encoding",
    "url_parsing",
    "markdown",
    "regex",
    "effect_handler",
    "gc_pressure",
    "async_futures",
]


@pytest.mark.parametrize("example", EXAMPLES_WITH_MAIN)
def test_stdout_parity(example: str, tmp_path: Path) -> None:
    """Every example with main() must produce identical stdout in both runtimes."""
    path = EXAMPLES_DIR / f"{example}.vera"
    assert path.exists(), f"Example not found: {path}"

    wasm_path, result = _compile_file(path, tmp_path)

    # Python runtime
    py_result = _run_python(result)

    # Node.js runtime
    node_result = _run_node(wasm_path)

    assert node_result["stdout"] == py_result.stdout, (
        f"Stdout mismatch for {example}:\n"
        f"  Python: {py_result.stdout!r}\n"
        f"  Node:   {node_result['stdout']!r}"
    )


# ---------------------------------------------------------------------------
# Examples without main — return value parity
# ---------------------------------------------------------------------------

# (example_name, fn_name, args_as_strings, args_as_ints)
FUNCTION_CALL_EXAMPLES = [
    ("factorial", "factorial", ["5"], [5]),
    ("factorial", "test_factorial", [], []),
    ("absolute_value", "absolute_value", ["-7"], [-7]),
    ("absolute_value", "test_abs", [], []),
    ("safe_divide", "safe_divide", ["10", "3"], [10, 3]),
    ("safe_divide", "safe_divide", ["10", "0"], [10, 0]),
    ("safe_divide", "test_divide", [], []),
    ("increment", "increment", [], []),
    ("closures", "test_closure", [], []),
    ("closures", "test_option_map", [], []),
    ("generics", "test_generics", [], []),
    ("list_ops", "test_list", [], []),
    ("mutual_recursion", "is_even", ["4"], [4]),
    ("mutual_recursion", "is_even", ["7"], [7]),
    ("mutual_recursion", "test_even", [], []),
    ("pattern_matching", "test_match", [], []),
    ("quantifiers", "test_process", [], []),
    ("refinement_types", "test_refine", [], []),
]


@pytest.mark.parametrize(
    "example,fn_name,str_args,int_args",
    FUNCTION_CALL_EXAMPLES,
    ids=[f"{e[0]}.{e[1]}({','.join(e[2])})" for e in FUNCTION_CALL_EXAMPLES],
)
def test_return_value_parity(
    example: str,
    fn_name: str,
    str_args: list[str],
    int_args: list[int],
    tmp_path: Path,
) -> None:
    """Exported functions must return the same value in both runtimes."""
    path = EXAMPLES_DIR / f"{example}.vera"
    wasm_path, result = _compile_file(path, tmp_path)

    py_result = _run_python(result, fn_name=fn_name, args=int_args or None)
    node_result = _run_node(wasm_path, fn=fn_name, fn_args=str_args or None)

    # Python returns int for i64, Node.js may return BigInt serialized as Number
    py_value = py_result.value
    node_value = node_result["value"]

    assert node_value == py_value, (
        f"Value mismatch for {example}.{fn_name}({str_args}):\n"
        f"  Python: {py_value!r}\n"
        f"  Node:   {node_value!r}"
    )


# =====================================================================
# TestBrowserIO — IO host bindings
# =====================================================================


class TestBrowserIO:
    """Test IO host bindings produce identical output in both runtimes."""

    def test_print_multiple(self, tmp_path: Path) -> None:
        """Multiple IO.print calls produce concatenated output."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("Hello, ");
  IO.print("World!");
  IO.print("\\n");
  ()
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "Hello, World!\n"

    def test_exit_code(self, tmp_path: Path) -> None:
        """IO.exit sets the exit code."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.exit(42)
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["exitCode"] == 42

    def test_read_line_with_stdin(self, tmp_path: Path) -> None:
        """IO.read_line reads from pre-queued stdin."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(@String.0);
  IO.print("\\n");
  ()
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path, stdin="hello from stdin")
        assert node["stdout"] == "hello from stdin\n"

    def test_args(self, tmp_path: Path) -> None:
        """IO.args returns the configured argument list."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  IO.print(int_to_string(array_length(@Array<String>.0)));
  IO.print("\\n");
  ()
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path, args="a,b,c")
        assert node["stdout"] == "3\n"

    def test_get_env_missing(self, tmp_path: Path) -> None:
        """IO.get_env returns None for missing keys."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.get_env("NONEXISTENT") {
    Some(@String) -> IO.print("some"),
    None -> IO.print("none")
  };
  IO.print("\\n");
  ()
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "none\n"

    def test_get_env_present(self, tmp_path: Path) -> None:
        """IO.get_env returns Some for configured keys."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.get_env("MY_VAR") {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("none")
  };
  IO.print("\\n");
  ()
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path, env="MY_VAR=hello_env")
        assert node["stdout"] == "hello_env\n"

    def test_stderr_captured(self, tmp_path: Path) -> None:
        """IO.stderr writes are captured in node['stderr'], separate from stdout.

        Added in #463.  Confirms the Node harness exposes a
        `stderr` field that mirrors the Python runtime's
        `ExecuteResult.stderr` behaviour when `capture_stderr=True`.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("to stdout");
  IO.stderr("to stderr");
  IO.print(" more stdout")
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "to stdout more stdout"
        assert node["stderr"] == "to stderr"

    def test_time_returns_positive(self, tmp_path: Path) -> None:
        """IO.time() returns the current Unix time in ms via Date.now().

        Doesn't check an exact value — just that the printed number
        is past a sane epoch threshold, confirming the import is
        wired up and the BigInt-to-decimal conversion works.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Nat = IO.time(());
  IO.print(nat_to_string(@Nat.0))
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert int(node["stdout"]) > 1_700_000_000_000

    def test_sleep_completes(self, tmp_path: Path) -> None:
        """IO.sleep(1) returns and subsequent statements execute.

        Browser runtime busy-waits on ``performance.now()`` (no
        ``Atomics.wait`` on the main thread).  Keep the sleep tiny
        so the test stays fast.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("before ");
  IO.sleep(1);
  IO.print("after")
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "before after"

    def test_file_io_returns_error(self, tmp_path: Path) -> None:
        """IO.read_file and IO.write_file return Err in the browser runtime."""
        # The file_io example tests both read and write, both should fail
        # gracefully in the browser runtime
        path = EXAMPLES_DIR / "file_io.vera"
        wasm_path, result = _compile_file(path, tmp_path)
        node = _run_node(wasm_path)
        # The browser runtime returns Result.Err for file operations.
        # The Python runtime may succeed or fail depending on filesystem.
        # Just verify the Node runtime doesn't crash.
        assert node["error"] is None

    def test_fused_async_await_err_path(self, tmp_path: Path) -> None:
        """#841: the fused async/await imports (`async_http_get` /
        `async_await`) are defined by the browser runtime and the eager
        buffered-outcome path works end-to-end.  Node has no
        XMLHttpRequest, so the fetch buffers the "Unsupported runtime"
        Err and await surfaces it — value-level: the program takes the
        Err arm (the native runtime's Err *text* differs by design;
        browser Http is documented-divergent)."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO, Http, Async>)
{
  let @Future<Result<String, String>> = async(Http.get("http://example.invalid/x"));
  let @Result<String, String> = await(@Future<Result<String, String>>.0);
  match @Result<String, String>.0 {
    Ok(@String) -> IO.print("OK"),
    Err(@String) -> IO.print("ERR")
  };
  ()
}
"""
        wasm_path, exports = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["error"] is None
        assert node["stdout"] == "ERR"

    def test_random_int_in_range(self, tmp_path: Path) -> None:
        """Random.random_int(low, high) is in inclusive range under Math.random.

        Browser runtime backs all three Random ops onto Math.random.
        Doesn't depend on a seed (no hook for one in the JS impl);
        covers the i64 ↔ BigInt boundary by returning the value
        and asserting on parsed stdout.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO, Random>)
{
  let @Int = Random.random_int(20, 25);
  IO.print(int_to_string(@Int.0))
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        # 30 runs to catch any range violations
        for _ in range(30):
            node = _run_node(wasm_path)
            v = int(node["stdout"])
            assert 20 <= v <= 25, f"out of range: {v}"

    def test_random_float_in_unit_interval(self, tmp_path: Path) -> None:
        """Random.random_float() returns f64 in [0.0, 1.0) via Math.random."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO, Random>)
{
  let @Float64 = Random.random_float(());
  IO.print(float_to_string(@Float64.0))
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        for _ in range(20):
            node = _run_node(wasm_path)
            v = float(node["stdout"])
            assert 0.0 <= v < 1.0, f"out of [0, 1): {v}"

    def test_random_bool_produces_both(self, tmp_path: Path) -> None:
        """Random.random_bool() produces both true and false in 50 draws."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO, Random>)
{
  if Random.random_bool(()) then { IO.print("1") } else { IO.print("0") }
}
'''
        wasm_path, exports = _compile_vera(source, tmp_path)
        total = 0
        for _ in range(50):
            node = _run_node(wasm_path)
            total += int(node["stdout"])
        # Bernoulli(0.5) over 50 trials: 99.9% inside [10, 40]. Generous bounds.
        assert 10 <= total <= 40, f"degenerate: {total}/50 trues"


class TestBrowserMathBuiltins:
    """Browser parity for math built-ins (#467).

    All log/trig ops are host-imported in the browser runtime as
    thin wrappers over `Math.log`, `Math.sin`, etc.  These tests
    exercise the same identities as the Python-side unit tests,
    confirming both runtimes produce equivalent Float64 values.
    """

    def test_log_identity(self, tmp_path: Path) -> None:
        """log(e()) ≈ 1.0 in the browser runtime."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(log(e())))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        # Parse and compare — Math.log of Math.E should be very close to 1.
        v = float(node["stdout"])
        assert abs(v - 1.0) < 1e-10, f"log(e()) = {v}"

    def test_sin_cos_at_zero(self, tmp_path: Path) -> None:
        """sin(0) + cos(0) == 1 via the browser Math API."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(sin(0.0) + cos(0.0)))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert float(node["stdout"]) == 1.0

    def test_atan2_quadrant(self, tmp_path: Path) -> None:
        """atan2(1, 1) ≈ π/4 across the browser boundary.

        Argument ordering matters: atan2(y, x) must match POSIX.
        If the runtime accidentally inverted to atan2(x, y) the
        value would still be π/4 for (1, 1), so use (1, -1) which
        disambiguates (3π/4 vs -π/4).
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(atan2(1.0, -1.0)))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        # atan2(1, -1) = 3π/4 ≈ 2.356194...
        v = float(node["stdout"])
        assert abs(v - 3 * math.pi / 4) < 1e-6, f"atan2(1, -1) = {v}"

    def test_pi_constant(self, tmp_path: Path) -> None:
        """pi() returns π — inlined, no host import.

        Browser runtime shouldn't emit a `vera.pi` binding; the
        value comes from the WAT `f64.const`.  ``float_to_string``
        truncates to 6 decimal digits, so the cross-runtime parity
        check is "agrees to 6 digits" rather than bit-for-bit —
        more precision is exercised by the Python-side unit test
        which reads the raw `ExecuteResult.value`.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(pi()))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert abs(float(node["stdout"]) - math.pi) < 1e-5

    def test_clamp_int(self, tmp_path: Path) -> None:
        """Integer clamp is inlined WAT; browser should match Python."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(int_to_string(clamp(15, 0, 10)));
  IO.print(",");
  IO.print(int_to_string(clamp(-10, -5, 5)))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "10,-5"

    def test_float_clamp(self, tmp_path: Path) -> None:
        """``float_clamp`` round-trips through the browser's `f64.max`/`f64.min`.

        Uses native WASM instructions (no host import), but the
        browser still has to agree with Python on the `min(max(v, lo),
        hi)` semantics.  Cases cover: inside-range, below-min,
        above-max, and an exact bound where the result should equal
        the bound bit-for-bit (no FP drift).  ``float_to_string``
        truncates to 6 digits, so the inside-range case uses a value
        that round-trips exactly at that precision.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(float_clamp(0.5, 0.0, 1.0)));   -- inside range
  IO.print(",");
  IO.print(float_to_string(float_clamp(-3.5, 0.0, 1.0)));  -- below min
  IO.print(",");
  IO.print(float_to_string(float_clamp(3.5, 0.0, 1.0)));   -- above max
  IO.print(",");
  IO.print(float_to_string(float_clamp(1.0, 0.0, 1.0)))    -- exact bound
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        parts = node["stdout"].split(",")
        assert len(parts) == 4, f"unexpected stdout shape: {node['stdout']!r}"
        expected = [0.5, 0.0, 1.0, 1.0]
        for got_str, want in zip(parts, expected):
            got = float(got_str)
            assert abs(got - want) < 1e-6, (
                f"float_clamp parity: got {got}, want {want}"
            )

    def test_sign(self, tmp_path: Path) -> None:
        """``sign`` is inlined WAT; browser should match Python.

        ``sign`` takes ``Int`` and returns ``Int`` (-1 / 0 / 1), so
        the three distinguishing cases are positive, negative, and
        zero.  There is no NaN case — NaN is a Float64 concept and
        ``sign`` doesn't accept floats.  (``float_is_nan`` is
        exercised in ``test_domain_edges_nan`` on the log/trig ops
        that do return Float64.)
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(int_to_string(sign(42)));
  IO.print(",");
  IO.print(int_to_string(sign(-7)));
  IO.print(",");
  IO.print(int_to_string(sign(0)))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "1,-1,0"

    @pytest.mark.parametrize(
        "vera_expr, py_expected",
        [
            ("log2(8.0)",     3.0),           # Math.log2 parity
            ("log10(1000.0)", 3.0),           # Math.log10 parity
            ("tan(1.0)",      math.tan(1.0)),
            ("atan(2.0)",     math.atan(2.0)),
        ],
    )
    def test_unary_host_parity(
        self, tmp_path: Path, vera_expr: str, py_expected: float,
    ) -> None:
        """Each log/trig host wrapper round-trips through the browser runtime.

        The original browser suite only exercised `log`, `sin`, `cos`,
        and `atan2`; `log2`, `log10`, `tan`, and `atan` went unverified
        end-to-end even though each has its own `imports.vera.*`
        binding in `runtime.mjs`.  A typo in any of those bindings
        would have silently shipped.  This test compiles one call per
        op, runs it under Node.js, and compares to the matching
        `math.*` value with a tolerance that accommodates
        `float_to_string`'s 6-digit truncation.
        """
        source = f'''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  IO.print(float_to_string({vera_expr}))
}}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        v = float(node["stdout"])
        assert abs(v - py_expected) < 1e-5, (
            f"{vera_expr}: expected {py_expected}, got {v}"
        )

    def test_domain_edges_nan(self, tmp_path: Path) -> None:
        """Out-of-domain inputs return NaN, matching IEEE 754 semantics.

        `log(-1.0)`, `asin(2.0)`, `acos(2.0)` are all mathematically
        undefined.  `Math.log`, `Math.asin`, `Math.acos` in JavaScript
        all return `NaN` for these inputs, and the browser host wrapper
        passes that through unchanged.  We verify the result via
        ``float_is_nan`` (true/false instead of string-comparing "NaN"
        which varies across runtimes) and cross the boundary once per
        function to confirm the wrapper doesn't throw or coerce.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(bool_to_string(float_is_nan(log(-1.0))));
  IO.print(",");
  IO.print(bool_to_string(float_is_nan(asin(2.0))));
  IO.print(",");
  IO.print(bool_to_string(float_is_nan(acos(2.0))))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "true,true,true"

    def test_log_pole_parity(self, tmp_path: Path) -> None:
        """log/log2/log10 at the zero pole are -Infinity in BOTH runtimes (#790).

        IEEE 754 and JS ``Math.log(0)`` give -Infinity at the pole,
        while genuine domain errors (``log(-1)``) give NaN.  Python's
        ``math.log(0.0)`` raises ``ValueError`` for both, and the
        wasmtime host wrapper used to fold every ``ValueError`` into
        NaN — so ``log(0.0)`` was NaN natively but -Infinity in the
        browser, a silent cross-runtime divergence (#790).

        This is a true differential: the same wasm runs under both
        runtimes and the stdout must be identical AND equal to the
        IEEE-correct answer (equality alone would pass if both
        runtimes were wrong the same way).  The pole is detected via
        ``float_is_infinite(x) && x < 0.0`` rather than
        ``float_to_string`` so the check cannot depend on how each
        runtime renders infinities.  ``-0.0`` is also the pole (JS
        ``Math.log(-0)`` is -Infinity), so all three ops are pinned
        at ``-0.0`` too — spec 9.6.10 claims it for both runtimes.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(bool_to_string(float_is_infinite(log(0.0)) && log(0.0) < 0.0));
  IO.print(",");
  IO.print(bool_to_string(float_is_infinite(log2(0.0)) && log2(0.0) < 0.0));
  IO.print(",");
  IO.print(bool_to_string(float_is_infinite(log10(0.0)) && log10(0.0) < 0.0));
  IO.print(",");
  IO.print(bool_to_string(float_is_infinite(log(-0.0)) && log(-0.0) < 0.0));
  IO.print(",");
  IO.print(bool_to_string(float_is_infinite(log2(-0.0)) && log2(-0.0) < 0.0));
  IO.print(",");
  IO.print(bool_to_string(float_is_infinite(log10(-0.0)) && log10(-0.0) < 0.0));
  IO.print(",");
  IO.print(bool_to_string(float_is_nan(log(-1.0))));
  IO.print(",");
  IO.print(bool_to_string(float_is_nan(log2(-1.0))));
  IO.print(",");
  IO.print(bool_to_string(float_is_nan(log10(-1.0))))
}
'''
        vera_file = tmp_path / "log_pole.vera"
        vera_file.write_text(source, encoding="utf-8")
        wasm_path, result = _compile_file(vera_file, tmp_path)

        py_result = _run_python(result)
        node = _run_node(wasm_path)

        assert node["stdout"] == py_result.stdout, (
            f"log pole parity mismatch:\n"
            f"  Python: {py_result.stdout!r}\n"
            f"  Node:   {node['stdout']!r}"
        )
        # Poles at 0.0 and -0.0 -> -Infinity (six trues), negatives
        # -> NaN (three trues).
        assert node["stdout"] == (
            "true,true,true,true,true,true,true,true,true"
        )

    def test_non_finite_render_parity(self, tmp_path: Path) -> None:
        """float_to_string renders NaN/±inf identically in both runtimes (#857).

        ``float_to_string`` is compiled to inline WASM (no host import),
        so the Python (wasmtime) and browser (Node.js) runtimes execute
        the *same* module — the non-finite spellings ("nan", "inf",
        "-inf") are emitted as literal bytes and cannot diverge.  This
        is a true differential: compile once, run under both runtimes,
        assert stdout is byte-identical AND equal to the canonical
        spellings.  It also guards against regressing to the pre-fix
        behavior, where NaN trapped ("invalid conversion to integer")
        and ±inf overflowed — either would surface as a Node harness
        error rather than a value here.  ``log(0.0)`` is the issue's
        exact -inf source (#790); ``0.0 - infinity()`` and the raw
        ``nan()``/``infinity()`` constants cover the other classes.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(nan()));
  IO.print(",");
  IO.print(float_to_string(infinity()));
  IO.print(",");
  IO.print(float_to_string(0.0 - infinity()));
  IO.print(",");
  IO.print(float_to_string(log(0.0)))
}
'''
        vera_file = tmp_path / "non_finite.vera"
        vera_file.write_text(source, encoding="utf-8")
        wasm_path, result = _compile_file(vera_file, tmp_path)

        py_result = _run_python(result)
        node = _run_node(wasm_path)

        assert node["stdout"] == py_result.stdout, (
            f"non-finite render parity mismatch:\n"
            f"  Python: {py_result.stdout!r}\n"
            f"  Node:   {node['stdout']!r}"
        )
        assert node["stdout"] == "nan,inf,-inf,-inf"


# =====================================================================
# TestBrowserState — State<T> host bindings
# =====================================================================


class TestBrowserArrayUtilities:
    """Browser parity for array utility built-ins (#466 phase 1).

    All seven ops are pure-WASM iterative loops with no host imports,
    so the Python (wasmtime) and browser (Node.js) runtimes should
    produce bit-identical output.  These tests fold array results
    back to a single Int/Bool/String to keep cross-runtime comparisons
    exact rather than relying on float_to_string truncation.
    """

    def test_array_mapi(self, tmp_path: Path) -> None:
        """mapi(range(10,15), |x,i| x + i*100) → [10, 111, 212, 313, 414], sum 1060.

        Uses a non-identity input range so element values and indices
        differ; a host implementation that swapped the (elem, idx)
        callback arguments would produce sum 6010 instead, failing
        loudly.  Mirrors the swap-detection fix made on the codegen
        side in test_array_mapi_passes_index.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Int> = array_mapi(
    array_range(10, 15),
    fn(@Int, @Nat -> @Int) effects(pure) {
      @Int.0 + nat_to_int(@Nat.0) * 100
    }
  );
  let @Int = array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  );
  IO.print(int_to_string(@Int.0))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        # 10 + 111 + 212 + 313 + 414 = 1060.
        # Swapped (idx, elem): 0 + 1*1000 + 2*1100 ... = 6010.
        assert node["stdout"] == "1060"

    def test_array_reverse(self, tmp_path: Path) -> None:
        """reverse + digit-pack fold: [1..5] reversed → 54321."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Int> = array_reverse(array_range(1, 6));
  let @Int = array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  );
  IO.print(int_to_string(@Int.0))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "54321"

    def test_array_find_some(self, tmp_path: Path) -> None:
        """find returns first match; matches on Some(@Int)."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = array_find(
    array_range(1, 10),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 5 }
  );
  match @Option<Int>.0 {
    Some(@Int) -> IO.print(int_to_string(@Int.0)),
    None -> IO.print("none")
  }
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "6"

    def test_array_find_none(self, tmp_path: Path) -> None:
        """find returns None when no element matches; matches on the None arm.

        Mirror-image of ``test_array_find_some`` but with a predicate
        that's always false.  Exercises the Option<T>=None tag path
        (tag 0 at offset 0 of the 16-byte heap box) end-to-end in the
        browser runtime.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = array_find(
    array_range(1, 10),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 1000 }
  );
  match @Option<Int>.0 {
    Some(@Int) -> IO.print(int_to_string(@Int.0)),
    None -> IO.print("none")
  }
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "none"

    def test_array_any_and_all(self, tmp_path: Path) -> None:
        """any/all — non-empty short-circuit + empty-array vacuous-truth.

        Four outputs in a single wasm program so we exercise all
        four branches against the browser runtime:

          any([-3..3], >0)  = true   (short-circuits on first match)
          all([-3..3], >0)  = false  (short-circuits on first failure)
          any([],      >0)  = false  (empty = no element satisfies)
          all([],      >0)  = true   (empty = vacuously satisfied)

        The empty-array cases are a conventional gotcha (some
        languages get the vacuous-truth of ``all([])`` wrong) and
        Vera's contract is to follow the mathematical reading.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(bool_to_string(array_any(
    array_range(-3, 3),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  )));
  IO.print(",");
  IO.print(bool_to_string(array_all(
    array_range(-3, 3),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  )));
  IO.print(",");
  let @Array<Int> = [];
  IO.print(bool_to_string(array_any(
    @Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  )));
  IO.print(",");
  IO.print(bool_to_string(array_all(
    @Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  )))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "true,false,false,true"

    def test_array_flatten(self, tmp_path: Path) -> None:
        """flatten [[1,2],[3,4],[5,6]] → 123456."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Array<Int>> = array_map(
    array_range(0, 3),
    fn(@Int -> @Array<Int>) effects(pure) {
      array_range(@Int.0 * 2 + 1, @Int.0 * 2 + 3)
    }
  );
  let @Array<Int> = array_flatten(@Array<Array<Int>>.0);
  let @Int = array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  );
  IO.print(int_to_string(@Int.0))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "123456"

    def test_array_sort_by(self, tmp_path: Path) -> None:
        """sort ascending [3,1,2] → 123 across the browser boundary."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Int> = [3, 1, 2];
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) {
      if @Int.1 < @Int.0 then { Less } else {
        if @Int.1 > @Int.0 then { Greater } else { Equal }
      }
    }
  );
  let @Int = array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  );
  IO.print(int_to_string(@Int.0))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "123"

    def test_array_sort_by_stability(self, tmp_path: Path) -> None:
        """Browser parity for the stability fingerprint test.

        Mirrors ``test_array_sort_by_stability`` from ``test_codegen_arrays.py``
        — same input ``[100, 101, 202, 203, 104]`` (keys 10, 10, 20,
        20, 10 with payloads encoded in the units digit), same
        comparator that ignores the payload, same position-weighted
        fold fingerprint.  Stable expected output is the exact
        15-digit string ``100101104202203``; any instability would
        produce a different fingerprint.

        The Node.js wasmtime here uses the same WAT as the Python
        wasmtime, so the test is really verifying that nothing in
        the browser host's call_indirect / GC interaction perturbs
        the comparator's relative-order semantics.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Int> = array_concat(
    array_concat(
      array_concat(
        array_concat(array_range(100, 101), array_range(101, 102)),
        array_range(202, 203)
      ),
      array_range(203, 204)
    ),
    array_range(104, 105)
  );
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) {
      if @Int.1 / 10 < @Int.0 / 10 then { Less } else {
        if @Int.1 / 10 > @Int.0 / 10 then { Greater } else { Equal }
      }
    }
  );
  let @Int = array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 1000 + @Int.0 }
  );
  IO.print(int_to_string(@Int.0))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "100101104202203"


class TestBrowserStringUtilities:
    """Browser parity for string utility built-ins (#470).

    All eight ops are pure-WASM byte-level loops with no host imports,
    so the Python (wasmtime) and browser (Node.js) runtimes should
    produce bit-identical output.  When an op returns ``Array<String>``
    (``string_chars``/``string_lines``/``string_words``) we fold it
    back to a single integer count or join it to a single ``String`` to
    keep cross-runtime comparisons exact.
    """

    def test_string_reverse(self, tmp_path: Path) -> None:
        """reverse("hello") → "olleh"; empty string round-trips."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_reverse("hello"));
  IO.print(",");
  IO.print(string_reverse(""))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "olleh,"

    def test_string_trim(self, tmp_path: Path) -> None:
        """trim_start keeps trailing spaces; trim_end keeps leading
        spaces.  Also exercises VT (\\u{0B}) and FF (\\u{0C}) at both
        ends — the new whitespace predicate (Python's str.isspace()
        ASCII set) must treat them as whitespace identically across
        the Python and browser runtimes.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_trim_start("  hi  "));
  IO.print("|");
  IO.print(string_trim_end("  hi  "));
  IO.print("|");
  -- VT/FF mixed in with regular whitespace.
  IO.print(string_trim_start(" \\u{0B}\\u{0C}hi  "));
  IO.print("|");
  IO.print(string_trim_end("  hi\\u{0B}\\u{0C} "));
  IO.print("|")
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "hi  |  hi|hi  |  hi|"

    def test_string_strip_vt_ff(self, tmp_path: Path) -> None:
        """Browser regression: ``string_strip`` (which delegates to
        ``_translate_trim`` after PR #510) must treat VT (\\u{0B}) and
        FF (\\u{0C}) as whitespace identically to the trim functions.

        This pins the strip→trim delegation contract under the
        browser runtime: if a future refactor accidentally re-opens
        the old narrow {space, tab, LF, CR} predicate for strip, the
        leading and trailing VT/FF would survive and break this
        assertion.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_strip("\\u{0B}\\u{0C}hi \\u{0B}"));
  IO.print("|")
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "hi|"

    def test_string_pad(self, tmp_path: Path) -> None:
        """pad_start/pad_end cycle the fill; pad of longer string is
        a no-op; empty fill is a no-op (cannot infinitely loop).
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_pad_start("x", 5, "0"));
  IO.print(",");
  IO.print(string_pad_end("x", 5, "0"));
  IO.print(",");
  IO.print(string_pad_start("x", 7, "ab"));
  IO.print(",");
  IO.print(string_pad_start("hello", 3, "*"));
  IO.print(",");
  -- empty-fill no-op: both sides should return input unchanged
  IO.print(string_pad_start("x", 5, ""));
  IO.print(",");
  IO.print(string_pad_end("x", 5, ""));
  IO.print(",");
  IO.print(string_pad_start("hello", 10, ""))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        # pad_start target=7, slen=1, pad_len=6; fill="ab" cycled
        # for 6 bytes starting at pos 0: a,b,a,b,a,b → "ababab" + "x".
        assert node["stdout"] == (
            "0000x,x0000,abababx,hello,x,x,hello"
        )

    def test_string_chars_count(self, tmp_path: Path) -> None:
        """string_chars("abc") has length 3; empty → 0."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(int_to_string(nat_to_int(array_length(string_chars("abc")))));
  IO.print(",");
  IO.print(int_to_string(nat_to_int(array_length(string_chars("")))))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "3,0"

    def test_string_chars_join(self, tmp_path: Path) -> None:
        """Round-trip: split "abc" into chars, join with "-" → "a-b-c"."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_join(string_chars("abc"), "-"))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "a-b-c"

    def test_string_lines(self, tmp_path: Path) -> None:
        """lines splits on \\n, \\r\\n, \\r (Python splitlines
        semantics).  Also exercises the empty-input path
        (``string_lines("")``) so the ``$alloc(0)`` branch in
        ``_translate_structural_split`` is covered under the browser
        runtime — Node's WASM linker has stricter zero-size handling
        than wasmtime in some past versions.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_join(string_lines("a\\nb\\nc"), "|"));
  IO.print(",");
  IO.print(string_join(string_lines("a\\r\\nb\\rc"), "|"));
  IO.print(",");
  IO.print(int_to_string(nat_to_int(array_length(string_lines("a\\n")))));
  IO.print(",");
  -- empty input → empty array (length 0)
  IO.print(int_to_string(nat_to_int(array_length(string_lines("")))))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        # Trailing newline does NOT create empty final segment;
        # empty input → empty array.
        assert node["stdout"] == "a|b|c,a|b|c,1,0"

    def test_string_words(self, tmp_path: Path) -> None:
        """words splits on runs of whitespace; empty segments
        discarded.  Also exercises VT (\\u{0B}) and FF (\\u{0C}) as
        word separators — they're part of Python's str.split()
        whitespace set and the browser runtime must agree.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_join(string_words("  foo  bar "), "|"));
  IO.print(",");
  IO.print(int_to_string(nat_to_int(array_length(string_words("   ")))));
  IO.print(",");
  -- VT/FF act as separators
  IO.print(string_join(string_words(" \\u{0B}foo\\u{0C}bar "), "|"));
  IO.print(",");
  -- A string of only VT/FF yields zero words
  IO.print(int_to_string(nat_to_int(array_length(string_words(" \\u{0B}\\u{0C} ")))))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == "foo|bar,0,foo|bar,0"


class TestBrowserCharClassification:
    """Browser parity for character classification built-ins (#471).

    All eight classifiers are single-byte ASCII range checks with no
    host imports — inline WAT identical in the Python and browser
    runtimes.  We pack multiple calls into one program to minimize
    compile latency while still exercising each predicate against at
    least one passing and one failing byte.
    """

    def test_classifiers(self, tmp_path: Path) -> None:
        """Every classifier exercised with both a passing and a failing
        byte, plus the empty-string rejection shared by all six.

        The `is_whitespace` block also covers the full Python
        `str.isspace()` ASCII set — tab, LF, VT (0x0B), FF (0x0C), CR,
        and space — because those two control codes are easy to miss
        in an ASCII-range check that collapses to a contiguous
        subrange.
        """
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  -- is_digit: pass + fail
  IO.print(bool_to_string(is_digit("5"))); IO.print(",");
  IO.print(bool_to_string(is_digit("x"))); IO.print(",");
  -- is_alpha: pass + fail
  IO.print(bool_to_string(is_alpha("A"))); IO.print(",");
  IO.print(bool_to_string(is_alpha("9"))); IO.print(",");
  -- is_alphanumeric: pass (letter), pass (digit), fail
  IO.print(bool_to_string(is_alphanumeric("a"))); IO.print(",");
  IO.print(bool_to_string(is_alphanumeric("7"))); IO.print(",");
  IO.print(bool_to_string(is_alphanumeric(" "))); IO.print(",");
  -- is_whitespace: full Python isspace() ASCII set + non-ws
  IO.print(bool_to_string(is_whitespace(" ")));   IO.print(",");
  IO.print(bool_to_string(is_whitespace("\\t"))); IO.print(",");
  IO.print(bool_to_string(is_whitespace("\\n"))); IO.print(",");
  IO.print(bool_to_string(is_whitespace("\\u{0B}"))); IO.print(",");
  IO.print(bool_to_string(is_whitespace("\\u{0C}"))); IO.print(",");
  IO.print(bool_to_string(is_whitespace("\\r"))); IO.print(",");
  IO.print(bool_to_string(is_whitespace("x")));   IO.print(",");
  -- is_upper / is_lower: pass + fail (not just pass)
  IO.print(bool_to_string(is_upper("A"))); IO.print(",");
  IO.print(bool_to_string(is_upper("a"))); IO.print(",");
  IO.print(bool_to_string(is_lower("a"))); IO.print(",");
  IO.print(bool_to_string(is_lower("A"))); IO.print(",");
  -- Empty string rejects every predicate
  IO.print(bool_to_string(is_digit("")));        IO.print(",");
  IO.print(bool_to_string(is_alpha("")));        IO.print(",");
  IO.print(bool_to_string(is_alphanumeric("")));  IO.print(",");
  IO.print(bool_to_string(is_whitespace("")));    IO.print(",");
  IO.print(bool_to_string(is_upper("")));        IO.print(",");
  IO.print(bool_to_string(is_lower("")))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == (
            # is_digit
            "true,false,"
            # is_alpha
            "true,false,"
            # is_alphanumeric
            "true,true,false,"
            # is_whitespace: 6 passes + 1 fail
            "true,true,true,true,true,true,false,"
            # is_upper + is_lower
            "true,false,true,false,"
            # 6 empty-string rejections
            "false,false,false,false,false,false"
        )

    def test_char_case(self, tmp_path: Path) -> None:
        """char_to_upper/lower: only the first byte is transformed."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(char_to_upper("abc"));
  IO.print(",");
  IO.print(char_to_lower("ABC"));
  IO.print(",");
  IO.print(char_to_upper(""));
  IO.print("|");
  IO.print(char_to_upper("5xyz"))
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        # Empty string round-trips; non-letter first byte passes through.
        assert node["stdout"] == "Abc,aBC,|5xyz"


class TestBrowserJsonAccessors:
    """Browser parity for JSON typed accessors (#366).

    All eleven accessors are pure-Vera prelude functions (no new host
    imports; `json_parse` is the only one that routes through a host
    and already has browser parity coverage elsewhere).  These tests
    assert the Python (wasmtime) and browser (Node.js) runtimes agree
    on the Option<T> shape returned by each accessor.
    """

    def test_layer1_coercions(self, tmp_path: Path) -> None:
        """Layer-1: every json_as_* accessor, matched and mismatched."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  -- json_as_string matches JString
  match json_as_string(JString("hi")) {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("?")
  };
  IO.print(",");
  -- mismatch on JNumber
  match json_as_string(JNumber(1.0)) {
    Some(@String) -> IO.print("!"),
    None -> IO.print("none")
  };
  IO.print(",");
  -- json_as_number on JNumber
  match json_as_number(JNumber(3.14)) {
    Some(@Float64) -> IO.print(float_to_string(@Float64.0)),
    None -> IO.print("?")
  };
  IO.print(",");
  -- json_as_bool true/false
  match json_as_bool(JBool(true)) {
    Some(@Bool) -> IO.print(bool_to_string(@Bool.0)),
    None -> IO.print("?")
  };
  IO.print(",");
  -- json_as_int truncates
  match json_as_int(JNumber(42.7)) {
    Some(@Int) -> IO.print(int_to_string(@Int.0)),
    None -> IO.print("?")
  };
  IO.print(",");
  -- json_as_int on NaN returns None
  match json_as_int(JNumber(0.0 / 0.0)) {
    Some(@Int) -> IO.print("!"),
    None -> IO.print("none")
  };
  IO.print(",");
  -- json_as_int on +inf returns None
  match json_as_int(JNumber(infinity())) {
    Some(@Int) -> IO.print("!"),
    None -> IO.print("none")
  };
  IO.print(",");
  -- json_as_int on -inf returns None
  match json_as_int(JNumber(0.0 - infinity())) {
    Some(@Int) -> IO.print("!"),
    None -> IO.print("none")
  };
  IO.print(",");
  -- json_as_int on +2^63 (finite overflow; i64 upper bound is
  -- exclusive) returns None
  match json_as_int(JNumber(9223372036854775808.0)) {
    Some(@Int) -> IO.print("!"),
    None -> IO.print("none")
  };
  IO.print(",");
  -- json_as_int on -2^63 (i64 lower bound is inclusive) returns
  -- Some(INT64_MIN).  Note the asymmetry: upper bound exclusive,
  -- lower bound inclusive, matching WASM's i64 range.  Two indirect
  -- probes pin the value to INT64_MIN without hitting #475 bug 9
  -- (int_to_string(INT64_MIN) negation overflow):
  --   (a) @Int.0 < 0 is true;
  --   (b) @Int.0 + 1 prints as "-9223372036854775807", which IS
  --       representable and serialisable without hitting the bug.
  match json_as_int(JNumber(0.0 - 9223372036854775808.0)) {
    Some(@Int) -> {
      IO.print(bool_to_string(@Int.0 < 0));
      IO.print(";");
      IO.print(int_to_string(@Int.0 + 1))
    },
    None -> IO.print("none")
  };
  IO.print(",");
  -- json_as_int on strictly below -2^63 returns None.  Next
  -- representable Float64 below -2^63 is -2^63 - 2048.
  match json_as_int(JNumber(0.0 - 9223372036854777856.0)) {
    Some(@Int) -> IO.print("!"),
    None -> IO.print("none")
  };
  IO.print(",");
  -- json_as_array matches JArray
  match json_as_array(JArray([JNumber(1.0), JNumber(2.0)])) {
    Some(@Array<Json>) -> IO.print(int_to_string(nat_to_int(array_length(@Array<Json>.0)))),
    None -> IO.print("?")
  };
  IO.print(",");
  -- json_as_object matches JObject (parsed so we get a real Map)
  match json_parse("{\\"k\\":1}") {
    Err(@String) -> IO.print("ERR"),
    Ok(@Json) ->
      match json_as_object(@Json.0) {
        Some(@Map<String, Json>) -> IO.print("obj"),
        None -> IO.print("?")
      }
  }
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert node["stdout"] == (
            # hi, none (mismatch), 3.14, true, 42, none (NaN),
            # none (+inf), none (-inf), none (+2^63),
            # (-2^63 branch: "true;" + INT64_MIN+1 = "-9223372036854775807"),
            # none (below -2^63), 2 (array length), obj.
            "hi,none,3.14,true,42,none,none,none,none,"
            "true;-9223372036854775807,none,2,obj"
        )

    def test_layer2_compound_accessors(self, tmp_path: Path) -> None:
        """Layer-2: every json_get_* accessor against a parsed object."""
        source = '''\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_parse("{\\"name\\":\\"Alice\\",\\"age\\":30,\\"active\\":true,\\"score\\":3.14,\\"tags\\":[1,2,3]}") {
    Err(@String) -> IO.print("ERR"),
    Ok(@Json) -> {
      match json_get_string(@Json.0, "name") {
        Some(@String) -> IO.print(@String.0),
        None -> IO.print("?")
      };
      IO.print(",");
      match json_get_int(@Json.0, "age") {
        Some(@Int) -> IO.print(int_to_string(@Int.0)),
        None -> IO.print("?")
      };
      IO.print(",");
      match json_get_bool(@Json.0, "active") {
        Some(@Bool) -> IO.print(bool_to_string(@Bool.0)),
        None -> IO.print("?")
      };
      IO.print(",");
      match json_get_number(@Json.0, "score") {
        Some(@Float64) -> IO.print(float_to_string(@Float64.0)),
        None -> IO.print("?")
      };
      IO.print(",");
      match json_get_array(@Json.0, "tags") {
        Some(@Array<Json>) -> IO.print(int_to_string(nat_to_int(array_length(@Array<Json>.0)))),
        None -> IO.print("?")
      };
      IO.print(",");
      -- missing field → None
      match json_get_int(@Json.0, "nope") {
        Some(@Int) -> IO.print("!"),
        None -> IO.print("none")
      };
      IO.print(",");
      -- wrong type → None
      match json_get_int(@Json.0, "name") {
        Some(@Int) -> IO.print("!"),
        None -> IO.print("none")
      }
    }
  };
  IO.print(",");
  -- json_get_* on a non-object Json: every accessor returns None
  -- because the underlying json_get returns None for non-JObject.
  let @Json = JArray([JNumber(1.0)]);
  match json_get_string(@Json.0, "x") {
    Some(@String) -> IO.print("!"), None -> IO.print("none")
  };
  IO.print(",");
  match json_get_int(@Json.0, "x") {
    Some(@Int) -> IO.print("!"), None -> IO.print("none")
  };
  IO.print(",");
  match json_get_bool(@Json.0, "x") {
    Some(@Bool) -> IO.print("!"), None -> IO.print("none")
  };
  IO.print(",");
  match json_get_number(@Json.0, "x") {
    Some(@Float64) -> IO.print("!"), None -> IO.print("none")
  };
  IO.print(",");
  match json_get_array(@Json.0, "x") {
    Some(@Array<Json>) -> IO.print("!"), None -> IO.print("none")
  }
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        # Object accessors hit, then the non-object run (5 Nones).
        assert node["stdout"] == (
            "Alice,30,true,3.14,3,none,none,none,none,none,none,none"
        )


class TestBrowserState:
    """Test State<T> host bindings in the Node.js runtime."""

    def test_state_int(self, tmp_path: Path) -> None:
        """State<Int> get/put works correctly."""
        path = EXAMPLES_DIR / "increment.vera"
        wasm_path, result = _compile_file(path, tmp_path)

        # increment takes @Unit -> @Unit, modifies State<Int>
        py_result = _run_python(result, fn_name="increment")
        node_result = _run_node(wasm_path, fn="increment")

        assert node_result["value"] == py_result.value
        # Both should show state changed from 0 to 1
        assert node_result["state"] == {"Int": 1}

    def test_state_initial_value(self, tmp_path: Path) -> None:
        """State starts at the correct default value."""
        path = EXAMPLES_DIR / "effect_handler.vera"
        wasm_path, result = _compile_file(path, tmp_path)

        py_result = _run_python(result, fn_name="test_state_init")
        node_result = _run_node(wasm_path, fn="test_state_init")

        assert node_result["value"] == py_result.value

    def test_state_put_get_roundtrip(self, tmp_path: Path) -> None:
        """State put then get returns the put value."""
        path = EXAMPLES_DIR / "effect_handler.vera"
        wasm_path, result = _compile_file(path, tmp_path)

        py_result = _run_python(result, fn_name="test_put_get")
        node_result = _run_node(wasm_path, fn="test_put_get")

        assert node_result["value"] == py_result.value

    def test_state_composite_type_arg_parity(self, tmp_path: Path) -> None:
        """#914: `State<Option<Int>>` — the mangled `state_*` import names
        (`state_get_Option_LInt_R` etc.) are discovered and paired into one
        cell by the Node runtime's import regex exactly as the Python host
        does, so a composite State roundtrips identically in both runtimes."""
        source = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(5)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    put(Some(9));
    option_unwrap_or(get(()), 0)
  }
}
"""
        vera_file = tmp_path / "state_composite.vera"
        vera_file.write_text(source, encoding="utf-8")
        tree = parse_file(str(vera_file))
        ast = transform(tree)
        result = codegen_compile(ast, source=source, file=str(vera_file))
        assert result.ok, f"Compile errors: {result.diagnostics}"
        wasm_path = tmp_path / "state_composite.wasm"
        wasm_path.write_bytes(result.wasm_bytes)

        py_result = _run_python(result, fn_name="main")
        node_result = _run_node(wasm_path, fn="main")

        assert py_result.value == 9
        assert node_result["value"] == py_result.value

    def test_state_composite_default_read_parity(self, tmp_path: Path) -> None:
        """#920: a composite `State<Tuple<Float64, Int>>` READ before any
        `put` must seed the same default cell in both runtimes.

        The cell is an i32 heap pointer, so its native default (`state.py`)
        is the null pointer 0 (a plain integer).  The pre-#920 browser default
        keyed on ``key.includes('Float')`` — the mangled composite suffix
        ``Tuple_LFloat64_CInt_R`` matches ``Float`` *inside* the composite name
        — accidentally seeding it with the JS float ``0.0``.  That happened to
        coerce onto the i32 import here, so #920 fixes this in lockstep with the
        genuinely-throwing ``Option<Int>`` sibling below by keying the default
        on the import's actual WASM value type, not a substring.  Either way,
        the browser value must equal the native (wasmtime) value.
        """
        source = """\
public fn read_default(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Tuple<Float64, Int>>>)
{
  let @Tuple<Float64, Int> = Tuple(9.0, 7);
  match get(()) {
    Tuple(@Float64, @Int) -> @Int.0
  }
}
"""
        wasm_path, result = _compile_state_default(source, tmp_path)

        py_result = _run_python(result, fn_name="read_default")
        node_result = _run_node(wasm_path, fn="read_default")

        assert node_result["error"] is None, (
            f"Node errored reading the composite State default: "
            f"{node_result['error']!r}"
        )
        assert node_result["value"] == py_result.value, (
            "Composite State<Tuple<Float64, Int>> default diverges:\n"
            f"  Python: {py_result.value!r}\n"
            f"  Node:   {node_result['value']!r}"
        )

    def test_state_option_default_read_parity(self, tmp_path: Path) -> None:
        """#920: a composite `State<Option<Int>>` READ before any `put` — the
        mangled suffix ``Option_LInt_R`` contains no ``Float`` substring, so the
        pre-#920 browser default seeded it with ``BigInt(0)``.  A JS BigInt
        cannot cross the i32 pointer import ("Cannot convert a BigInt value to a
        number"), so the base runtime *threw* the moment the default was read,
        while native (wasmtime) returned the null-pointer value.  After #920 the
        default is the plain-number null pointer 0 and both runtimes agree.
        """
        source = """\
public fn read_default(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Option<Int>>>)
{
  let @Option<Int> = Some(7);
  option_unwrap_or(get(()), 99)
}
"""
        wasm_path, result = _compile_state_default(source, tmp_path)

        py_result = _run_python(result, fn_name="read_default")
        node_result = _run_node(wasm_path, fn="read_default")

        assert node_result["error"] is None, (
            f"Node errored reading the composite State default: "
            f"{node_result['error']!r}"
        )
        assert node_result["value"] == py_result.value, (
            "Composite State<Option<Int>> default diverges:\n"
            f"  Python: {py_result.value!r}\n"
            f"  Node:   {node_result['value']!r}"
        )

    def test_state_adt_default_read_parity(self, tmp_path: Path) -> None:
        """#920: a user-ADT `State<Box>` READ before any `put`.  A bare ADT
        name mangles to itself (`state_get_Box`, no ``Float`` substring), so the
        pre-#920 browser default seeded it with ``BigInt(0)`` — which threw on
        the i32 heap-pointer import exactly like ``State<Option<Int>>``.  Guards
        the whole pointer-typed-`State` class (not just generic composites)
        against the substring heuristic; after #920 both runtimes return the
        null-pointer value.
        """
        source = """\
private data Box {
  Full(Int),
  Empty
}

public fn read_default(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Box>>)
{
  let @Box = Full(3);
  match get(()) {
    Full(@Int) -> @Int.0,
    Empty -> 0
  }
}
"""
        wasm_path, result = _compile_state_default(source, tmp_path)

        py_result = _run_python(result, fn_name="read_default")
        node_result = _run_node(wasm_path, fn="read_default")

        assert node_result["error"] is None, (
            f"Node errored reading the ADT State default: "
            f"{node_result['error']!r}"
        )
        assert node_result["value"] == py_result.value, (
            "State<Box> ADT default diverges:\n"
            f"  Python: {py_result.value!r}\n"
            f"  Node:   {node_result['value']!r}"
        )

    def test_state_bare_float64_default_read_parity(self, tmp_path: Path) -> None:
        """#920 regression: a BARE `State<Float64>` READ before any `put` must
        STILL seed the JS float default ``0.0`` (its imports are ``f64``, which
        requires a plain-number 0.0 — a BigInt would throw).  This guards
        against over-correcting the composite fix into breaking primitive
        Float64 state.
        """
        source = """\
public fn read_default(@Unit -> @Float64)
  requires(true)
  ensures(true)
  effects(<State<Float64>>)
{
  get(())
}
"""
        wasm_path, result = _compile_state_default(source, tmp_path)

        py_result = _run_python(result, fn_name="read_default")
        node_result = _run_node(wasm_path, fn="read_default")

        assert node_result["error"] is None, (
            f"Node errored reading the bare Float64 State default: "
            f"{node_result['error']!r}"
        )
        assert node_result["value"] == py_result.value, (
            "Bare State<Float64> default diverges:\n"
            f"  Python: {py_result.value!r}\n"
            f"  Node:   {node_result['value']!r}"
        )


# =====================================================================
# TestBrowserContracts — contract_fail parity
# =====================================================================


class TestBrowserContracts:
    """Test that contract violations produce matching errors."""

    def test_precondition_failure(self, tmp_path: Path) -> None:
        """Calling a function with a violated precondition traps in both runtimes."""
        path = EXAMPLES_DIR / "safe_divide.vera"
        wasm_path, result = _compile_file(path, tmp_path)

        # safe_divide(@Int, @Int -> @Int) with requires(@Int.1 != 0)
        # @Int.1 is the first (leftmost) arg.  safe_divide(0, 5) makes
        # @Int.1 = 0, violating the precondition.
        py_error: str | None = None
        py_kind: str | None = None
        try:
            _run_python(result, fn_name="safe_divide", args=[0, 5])
        except WasmTrapError as exc:
            py_error = str(exc)
            py_kind = exc.kind

        node_result = _run_node(wasm_path, fn="safe_divide", fn_args=["0", "5"])

        # Both should have errors (contract violation).  The kind is pinned
        # so an unrelated Python-side trap cannot pass for parity.
        assert py_error is not None, "Python should report contract error"
        assert py_kind == "contract_violation", py_kind
        assert node_result["error"] is not None, "Node should report contract error"

    def test_overflow_trap_parity(self, tmp_path: Path) -> None:
        """#808: an @Int overflow traps in BOTH runtimes with an
        overflow-flavoured message, and the browser bundle still instantiates.

        The #798 guard now declares the `vera.overflow_trap` host import, so
        `runtime.mjs`'s dynamic import builder must provide a binding — without
        it `WebAssembly.instantiate` raises a `LinkError` on *any* arithmetic
        program.  This is the cross-runtime parity for the wasmtime-side
        `TestOverflowTrapKind808` (which classifies `kind="overflow"`)."""
        source = (
            "public fn add(@Int, @Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.1 + @Int.0 }\n"
        )
        vera_file = tmp_path / "ovf.vera"
        vera_file.write_text(source, encoding="utf-8")
        wasm_path, result = _compile_file(vera_file, tmp_path)

        # i64.MAX + 1 overflows i64 → both runtimes must trap.
        py_error: str | None = None
        py_kind: str | None = None
        try:
            _run_python(result, fn_name="add", args=[9223372036854775807, 1])
        except WasmTrapError as exc:
            py_error = str(exc)
            py_kind = exc.kind

        node_result = _run_node(
            wasm_path, fn="add", fn_args=["9223372036854775807", "1"],
        )

        assert py_error is not None, "Python should trap on overflow"
        assert py_kind == "overflow", py_kind
        assert "overflow" in py_error.lower(), py_error
        # Node must instantiate (overflow_trap import provided) and surface the
        # overflow as an error, not a silent wrap.
        assert node_result["error"] is not None, (
            "Node should report the overflow trap"
        )
        assert "overflow" in node_result["error"].lower(), node_result["error"]

        # Companion no-trap: a safe sum returns cleanly in Node — proving the
        # trap above is the guard firing, not the bundle failing to instantiate.
        safe = _run_node(wasm_path, fn="add", fn_args=["10", "5"])
        assert safe["error"] is None, safe
        assert safe["value"] == 15, safe


# =====================================================================
# TestBrowserMarkdown — md_* host bindings
# =====================================================================


class TestBrowserMarkdown:
    """Test Markdown host bindings produce identical output."""

    def test_markdown_example_parity(self, tmp_path: Path) -> None:
        """The markdown.vera example must produce identical stdout."""
        path = EXAMPLES_DIR / "markdown.vera"
        wasm_path, result = _compile_file(path, tmp_path)

        py_result = _run_python(result)
        node_result = _run_node(wasm_path)

        assert node_result["stdout"] == py_result.stdout, (
            f"Markdown stdout mismatch:\n"
            f"  Python: {py_result.stdout!r}\n"
            f"  Node:   {node_result['stdout']!r}"
        )

    def test_md_parse_render_roundtrip(self, tmp_path: Path) -> None:
        """md_parse then md_render should produce valid output in both runtimes."""
        source = '''\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Hello\\n\\nWorld");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> IO.print(md_render(@MdBlock.0)),
    Err(@String) -> IO.print(@String.0)
  }
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)
        node = _run_node(wasm_path)
        assert "Hello" in node["stdout"]
        assert node["error"] is None

    def test_md_has_heading(self, tmp_path: Path) -> None:
        """md_has_heading correctly detects headings."""
        source = '''\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Title\\n\\nParagraph");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      if md_has_heading(@MdBlock.0, 1) then {
        IO.print("has_h1 ")
      } else {
        IO.print("no_h1 ")
      };
      if md_has_heading(@MdBlock.0, 2) then {
        IO.print("has_h2")
      } else {
        IO.print("no_h2")
      };
      ()
    },
    Err(@String) -> IO.print(@String.0)
  }
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)

        node = _run_node(wasm_path)
        assert node["stdout"] == "has_h1 no_h2"
        assert node["error"] is None

    def test_md_has_code_block(self, tmp_path: Path) -> None:
        """md_has_code_block correctly detects code blocks."""
        source = '''\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("```python\\nprint()\\n```");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      if md_has_code_block(@MdBlock.0, "python") then {
        IO.print("has_py ")
      } else {
        IO.print("no_py ")
      };
      if md_has_code_block(@MdBlock.0, "rust") then {
        IO.print("has_rs")
      } else {
        IO.print("no_rs")
      };
      ()
    },
    Err(@String) -> IO.print(@String.0)
  }
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)

        node = _run_node(wasm_path)
        assert node["stdout"] == "has_py no_rs"
        assert node["error"] is None

    def test_md_extract_code_blocks(self, tmp_path: Path) -> None:
        """md_extract_code_blocks returns code block contents."""
        source = '''\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("```vera\\nlet x = 1\\n```\\n\\n```python\\nprint()\\n```");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Array<String> = md_extract_code_blocks(@MdBlock.0, "vera");
      IO.print(int_to_string(array_length(@Array<String>.0)))
    },
    Err(@String) -> IO.print(@String.0)
  }
}
'''
        wasm_path, _ = _compile_vera(source, tmp_path)

        node = _run_node(wasm_path)
        assert node["stdout"] == "1"
        assert node["error"] is None


# =====================================================================
# TestBrowserEmit — CLI --target browser
# =====================================================================


class TestBrowserEmit:
    """Test the browser bundle emission."""

    def test_emit_produces_three_files(self, tmp_path: Path) -> None:
        """vera compile --target browser produces module.wasm, runtime.mjs, index.html."""
        from vera.browser.emit import emit_browser_bundle

        # Compile a simple program
        path = EXAMPLES_DIR / "hello_world.vera"
        build_dir = tmp_path / "build"
        build_dir.mkdir()
        _, result = _compile_file(path, build_dir)

        out_dir = tmp_path / "bundle"
        files = emit_browser_bundle(result.wasm_bytes, out_dir)

        assert (out_dir / "module.wasm").exists()
        assert (out_dir / "runtime.mjs").exists()
        assert (out_dir / "index.html").exists()
        assert len(files) == 3

    def test_emitted_wasm_runs_in_node(self, tmp_path: Path) -> None:
        """The emitted module.wasm works with the Node.js harness."""
        from vera.browser.emit import emit_browser_bundle

        path = EXAMPLES_DIR / "hello_world.vera"
        build_dir = tmp_path / "build"
        build_dir.mkdir()
        _, result = _compile_file(path, build_dir)

        out_dir = tmp_path / "bundle"
        emit_browser_bundle(result.wasm_bytes, out_dir)

        node = _run_node(out_dir / "module.wasm")
        assert node["stdout"] == "Hello, World!"

    def test_cli_target_browser(self, tmp_path: Path) -> None:
        """vera compile --target browser via subprocess."""
        out_dir = tmp_path / "browser_out"
        # Prefer the venv vera to avoid picking up a system-installed binary
        venv_vera = ROOT / ".venv" / "bin" / "vera"
        vera_bin = str(venv_vera) if venv_vera.exists() else (shutil.which("vera") or "vera")
        proc = subprocess.run(
            [
                vera_bin,
                "compile", "--target", "browser",
                str(EXAMPLES_DIR / "hello_world.vera"),
                "-o", str(out_dir),
            ],
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=60,  # Windows runner Node startup variance + cold V8 exnref codegen — see #694
            check=False,
        )
        assert proc.returncode == 0, f"stderr: {proc.stderr}"
        assert (out_dir / "module.wasm").exists()
        assert (out_dir / "runtime.mjs").exists()
        assert (out_dir / "index.html").exists()

    def test_index_html_contains_import(self, tmp_path: Path) -> None:
        """The generated index.html imports from runtime.mjs."""
        from vera.browser.emit import emit_browser_bundle

        path = EXAMPLES_DIR / "hello_world.vera"
        build_dir = tmp_path / "build"
        build_dir.mkdir()
        _, result = _compile_file(path, build_dir)

        out_dir = tmp_path / "bundle"
        emit_browser_bundle(result.wasm_bytes, out_dir)

        html = (out_dir / "index.html").read_text(encoding="utf-8")
        assert "runtime.mjs" in html
        assert "module.wasm" in html
        assert "type=\"module\"" in html


# =====================================================================
# TestBrowserExports — export list parity
# =====================================================================


class TestRuntimeSourcePath:
    """Cover the _runtime_source_path fallback in browser/emit.py."""

    def test_fallback_when_no_fspath(self) -> None:
        """When importlib.resources returns a non-fspath Traversable,
        _runtime_source_path falls back to __file__-relative path."""
        from unittest.mock import MagicMock, patch
        from vera.browser.emit import _runtime_source_path

        # Create a mock Traversable that lacks __fspath__
        mock_ref = MagicMock(spec=[])  # no __fspath__ attribute
        mock_files = MagicMock()
        mock_files.joinpath.return_value = mock_ref

        with patch("importlib.resources.files", return_value=mock_files):
            result = _runtime_source_path()

        # Should fall back to Path(__file__).parent / "runtime.mjs"
        assert result.name == "runtime.mjs"
        assert "vera" in str(result) or "browser" in str(result)

    def test_fallback_on_type_error(self) -> None:
        """When importlib.resources raises TypeError,
        _runtime_source_path falls back gracefully."""
        from unittest.mock import patch
        from vera.browser.emit import _runtime_source_path

        with patch("importlib.resources.files", side_effect=TypeError):
            result = _runtime_source_path()

        assert result.name == "runtime.mjs"

    def test_fallback_on_file_not_found_error(self) -> None:
        """When importlib.resources raises FileNotFoundError,
        _runtime_source_path falls back gracefully."""
        from unittest.mock import patch
        from vera.browser.emit import _runtime_source_path

        with patch("importlib.resources.files", side_effect=FileNotFoundError):
            result = _runtime_source_path()

        assert result.name == "runtime.mjs"


class TestBrowserExports:
    """Verify the exports list matches between runtimes."""

    @pytest.mark.parametrize("example", EXAMPLES_WITH_MAIN)
    def test_exports_include_main(self, example: str, tmp_path: Path) -> None:
        """Examples with main should export 'main' in both runtimes."""
        path = EXAMPLES_DIR / f"{example}.vera"
        wasm_path, result = _compile_file(path, tmp_path)
        node_result = _run_node(wasm_path)

        assert "main" in result.exports
        assert "main" in node_result["exports"]


class TestBrowserMapHostStoreGCReachability695:
    """Browser-runtime parallel of
    ``test_codegen_gc_rooting.py::TestMapHostStoreGCReachability695``.

    PR #707 review (pr-test-analyzer I3): the JS-side
    ``attach_bucket_to_wrapper`` implementation (~115 LOC of bucket
    population, val-word-first ordering, zero-fill, BigInt→0
    coercion, JS ``gcShadowPush`` / ``gcShadowPop`` discipline,
    ``readJson`` / ``readHtml`` bit-31 mask) was covered only by
    stdout-parity tests with default GC pressure.  A regression in
    any of those browser-side paths would silently ship.

    These tests compile the same three #695 / #705 reproducers with
    ``VERA_EAGER_GC=1`` set in the environment (which the codegen
    reads to inject a forced ``$gc_collect`` on every ``$alloc``),
    then run the compiled WASM under Node.js using the browser
    runtime in ``vera/browser/runtime.mjs``.  The expected output
    matches the CLI side — any divergence (truncated JArray length,
    early bailout, exception) indicates a browser-runtime regression.

    Why this matters specifically: the browser runtime can't access
    the WAT shadow stack the way the Python ``_ShadowGuard`` does, so
    it uses the JS ``gcShadowPush`` / ``gcShadowPop`` helpers added
    in commit ``1ff7f7c``.  Those helpers drive the exported
    ``$gc_sp`` / ``$gc_stack_limit`` mutable globals — a contract
    that needs CI gating, not just code review.
    """

    def _run_eager_gc_node(
        self,
        src: str,
        monkeypatch: pytest.MonkeyPatch,
        tmp_path: Path,
    ) -> str:
        """Compile ``src`` with ``VERA_EAGER_GC=1`` set at codegen
        time, then run in node and return the (whitespace-stripped)
        stdout produced by ``IO.print`` calls.
        """
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        wasm_path, _ = _compile_vera(src, tmp_path)
        result = _run_node(wasm_path)
        # PR #707 review: the Node harness surfaces traps / runtime errors
        # via ``result["error"]``.  Eager-GC regression tests must distinguish
        # "ran cleanly with the expected stdout" from "trapped en route" — a
        # silent ``result.get("stdout", "")`` would hide a fresh UAF behind
        # whatever partial output the IO.print buffer flushed before the trap.
        assert not result.get("error"), (
            f"Node harness reported error during VERA_EAGER_GC run: {result.get('error')!r}"
        )
        return result.get("stdout", "").strip()

    def test_eager_gc_set_of_json_browser(
        self,
        monkeypatch: pytest.MonkeyPatch,
        tmp_path: Path,
    ) -> None:
        """Browser parallel of
        ``test_codegen_gc_rooting.py::test_eager_gc_set_of_json_post_walk_uaf``.
        Exercises the JS-side ``attach_bucket_to_wrapper`` Set branch
        plus the ``allocMapWrapper`` JS rooting (#707 round 2 fix).
        """
        src = """
private fn build_set(-> @Set<Json>)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse(
    "[1,2,3,4,5,6,7,8,9,10]"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> set_add(set_new(), @Json.0),
    Err(@String) -> set_new()
  }
}

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Set<Json> = build_set();
  let @Array<Json> = set_to_array(@Set<Json>.0);
  let @Int = array_fold(@Array<Json>.0, 0, fn(@Int, @Json -> @Int) effects(pure) {
    json_array_length(@Json.0) + @Int.0
  });
  IO.print(int_to_string(@Int.0))
}
"""
        assert self._run_eager_gc_node(src, monkeypatch, tmp_path) == "10"

    def test_eager_gc_json_object_with_array_child_browser(
        self,
        monkeypatch: pytest.MonkeyPatch,
        tmp_path: Path,
    ) -> None:
        """Browser parallel of
        ``test_codegen_gc_rooting.py::test_eager_gc_json_object_with_array_child_post_walk_uaf``.
        Exercises the JS-side ``allocMapWrapper`` (which wraps the
        JSON-parser-produced ``Map<String, Json>``) plus the
        ``readJson`` bit-31 mask fix (CR round 1 finding 2).
        """
        src = """
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Json, String> = json_parse(
    "{\\"key\\": [1,2,3,4,5,6,7,8,9,10]}"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> {
      let @Option<Json> = json_get(@Json.0, "key");
      match @Option<Json>.0 {
        Some(@Json) -> {
          let @Int = json_array_length(@Json.0);
          IO.print(int_to_string(@Int.0))
        },
        None -> IO.print("none")
      }
    },
    Err(@String) -> IO.print("err")
  }
}
"""
        assert self._run_eager_gc_node(src, monkeypatch, tmp_path) == "10"

    def test_eager_gc_map_of_json_user_level_browser(
        self,
        monkeypatch: pytest.MonkeyPatch,
        tmp_path: Path,
    ) -> None:
        """Browser parallel of
        ``test_codegen_gc_rooting.py::test_eager_gc_map_of_json_user_level_post_walk_uaf``.
        Exercises the user-level ``map_insert(map_new(), ...)`` path
        through the JS-side ``attach_bucket_to_wrapper`` Map branch,
        with EAGER_GC pressure on every alloc.
        """
        src = """
private fn build_map(-> @Map<String, Json>)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse(
    "[1,2,3,4,5,6,7,8,9,10]"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> map_insert(map_new(), "arr", @Json.0),
    Err(@String) -> map_new()
  }
}

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<String, Json> = build_map();
  let @Option<Json> = map_get(@Map<String, Json>.0, "arr");
  match @Option<Json>.0 {
    Some(@Json) -> {
      let @Int = json_array_length(@Json.0);
      IO.print(int_to_string(@Int.0))
    },
    None -> IO.print("none")
  }
}
"""
        assert self._run_eager_gc_node(src, monkeypatch, tmp_path) == "10"


class TestBrowserRound4Fixes743:
    """Browser-runtime parallel of ``test_codegen_gc_rooting.py``'s
    ``TestAdtBuilderRooting743`` and ``test_codegen_gc_reclamation.py``'s
    ``TestSameValueZeroKeys743`` — pins
    the JS ``gcRooted`` ADT-builder rooting and the ``sameValueZero``
    Float64-key comparison (folded into #706, surfaced by the CodeRabbit
    review).
    """

    def _eager_stdout(
        self, src: str, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> str:
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        wasm_path, _ = _compile_vera(src, tmp_path)
        result = _run_node(wasm_path)
        assert not result.get("error"), (
            f"Node harness reported error during VERA_EAGER_GC run: "
            f"{result.get('error')!r}"
        )
        return result.get("stdout", "").strip()

    def test_map_get_string_value_survives_eager_gc_browser(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        """``mapAllocOption('s')`` roots the string across the option
        struct alloc — 200 ``map_get`` calls on a ``Map<Int, String>``
        under eager GC each return the live string (pre-fix: 0)."""
        src = """
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<Int, String> = map_insert(map_new(), 1, "alphabet_soup_xyz");
  let @Int = array_fold(
    array_range(0, 200),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match map_get(@Map<Int, String>.0, 1) {
        Some(@String) ->
          if string_contains(@String.0, "soup") then { @Int.1 + 1 }
          else { @Int.1 },
        None -> @Int.1
      }
    }
  );
  IO.print(int_to_string(@Int.0))
}
"""
        assert self._eager_stdout(src, monkeypatch, tmp_path) == "200"

    def test_nan_float_map_key_round_trips_browser(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        """A NaN ``Float64`` map key is found via the JS ``sameValueZero``
        ``map_contains`` / native-Map ``map_get`` (pre-fix the
        ``decodeColumn`` ``===`` could not find NaN)."""
        src = """
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Float64 = 0.0 / 0.0;
  let @Map<Float64, Int> = map_insert(map_new(), @Float64.0, 42);
  let @Int = if map_contains(@Map<Float64, Int>.0, @Float64.0) then {
    match map_get(@Map<Float64, Int>.0, @Float64.0) {
      Some(@Int) -> @Int.0,
      None -> -2
    }
  } else { -1 };
  IO.print(int_to_string(@Int.0))
}
"""
        assert self._eager_stdout(src, monkeypatch, tmp_path) == "42"

    def test_nan_float_set_element_round_trips_browser(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        """A NaN ``Float64`` Set element dedups and is found via the JS
        ``sameValueZero`` ``set_contains`` (parallel of the Map case)."""
        src = """
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Float64 = 0.0 / 0.0;
  let @Set<Float64> = set_add(set_add(set_new(), @Float64.0), @Float64.0);
  let @Int = if set_contains(@Set<Float64>.0, @Float64.0) then {
    nat_to_int(set_size(@Set<Float64>.0))
  } else { -1 };
  IO.print(int_to_string(@Int.0))
}
"""
        # deduped to size 1; contains finds NaN → 1.
        assert self._eager_stdout(src, monkeypatch, tmp_path) == "1"

    def test_decimal_from_string_wrapper_survives_eager_gc_browser(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        """Browser parallel of the CLI Decimal-wrapper rooting:
        ``decimal_from_string`` wraps the handle in ``Option.Some`` via
        ``gcRooted(wrapHandle(3, h))``; 200x under eager GC the Decimal
        reads back as "3.14"."""
        src = """
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = array_fold(
    array_range(0, 200),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match decimal_from_string("3.14") {
        Some(@Decimal) ->
          if string_contains(decimal_to_string(@Decimal.0), "3.14")
          then { @Int.1 + 1 } else { @Int.1 },
        None -> @Int.1
      }
    }
  );
  IO.print(int_to_string(@Int.0))
}
"""
        assert self._eager_stdout(src, monkeypatch, tmp_path) == "200"


class TestBrowserMdBuilderRooting744:
    """Browser-runtime parallel of ``test_codegen_gc_rooting.py``'s
    ``TestHostWalkerGCRooting692.test_md_parse_200_headings`` — pins the
    #744 fix: the JS-side markdown tree builders (``writeMdInline`` /
    ``writeInlineArray`` / ``writeMdBlock`` / ``writeBlockArray`` in
    ``vera/browser/runtime.mjs``) must root intermediate WASM heap
    pointers on the shadow stack, mirroring the ``writeJson`` /
    ``writeHtml`` ``gcGuard`` + ``gcShadowPush`` discipline (#692 /
    #708) and the CLI ``vera/wasm/markdown.py`` fields-first-then-body
    convention (which was already hardened; the browser mirror was the
    missed sibling).

    Pre-fix, every ``writeMd*`` branch allocated the node body FIRST
    and held it in a JS local across the child / string allocations,
    and the array helpers held their backing buffers unrooted across
    the per-element recursion.  With ``VERA_EAGER_GC=1`` (codegen
    injects a forced ``$gc_collect`` on every ``$alloc``) the
    unreferenced body / backing block is swept and reused mid-build,
    corrupting the tree — observed as ``readMdBlock`` throwing
    ``Unknown MdBlock tag`` or the walk trapping out-of-bounds.
    """

    def _eager_gc_node(
        self, src: str, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> str:
        """Compile with ``VERA_EAGER_GC=1``, run under Node, return stdout."""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        wasm_path, _ = _compile_vera(src, tmp_path)
        result = _run_node(wasm_path)
        assert not result.get("error"), (
            f"Node harness reported error during VERA_EAGER_GC run: "
            f"{result.get('error')!r}"
        )
        return result.get("stdout", "").strip()

    def _eager_gc_parity(
        self, src: str, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> tuple[str, str]:
        """Compile ONCE with ``VERA_EAGER_GC=1``, run the same wasm bytes
        under Python/wasmtime (hardened CLI markdown builders) and Node
        (browser runtime), returning both stdouts.  A divergence isolates
        the browser-runtime builders — the module bytes are identical.
        """
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        src_path = tmp_path / "md744.vera"
        src_path.write_text(src, encoding="utf-8")
        wasm_path, result = _compile_file(src_path, tmp_path)
        py_result = _run_python(result)
        node_result = _run_node(wasm_path)
        assert not node_result.get("error"), (
            f"Node harness reported error during VERA_EAGER_GC run: "
            f"{node_result.get('error')!r}"
        )
        return py_result.stdout, node_result.get("stdout", "")

    def test_eager_gc_md_all_node_types_parity(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        """Round-trip a document exercising EVERY MdInline / MdBlock
        writer branch (text, code span, emph, strong, link, image;
        heading, paragraph, code block, blockquote, unordered + ordered
        list, thematic break, table, document) under eager GC and
        assert browser stdout matches the CLI byte-for-byte."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "# Title *emph* **strong** `code`\\n\\nPara [link](https://x.example/) and ![alt](img.png) tail\\n\\n> quoted *deep* text\\n\\n- alpha\\n- beta\\n\\n1. one\\n2. two\\n\\n---\\n\\n| h1 | h2 |\\n| --- | --- |\\n| *c1* | c2 |\\n\\n```py\\ncode_here()\\n```\\n";
  match md_parse(@String.0) {
    Ok(@MdBlock) -> IO.print(md_render(@MdBlock.0)),
    Err(@String) -> IO.print(string_concat("parse_err:", @String.0))
  }
}
"""
        py_out, node_out = self._eager_gc_parity(src, monkeypatch, tmp_path)
        assert "Title" in py_out  # sanity: the CLI round-trip really ran
        assert node_out == py_out, (
            f"Markdown eager-GC round-trip diverged:\n"
            f"  Python: {py_out!r}\n"
            f"  Node:   {node_out!r}"
        )

    def test_eager_gc_md_extract_code_blocks_volume(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        """60 heading + paragraph + fenced-code units built under eager
        GC, then a full-tree read-back via ``md_extract_code_blocks``
        — the count is exact (pre-fix: corrupted tree / trap)."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_repeat("# heading\\n\\npara text\\n\\n```py\\ncode_here()\\n```\\n\\n", 60);
  match md_parse(@String.0) {
    Ok(@MdBlock) -> {
      let @Array<String> = md_extract_code_blocks(@MdBlock.0, "py");
      IO.print(int_to_string(array_length(@Array<String>.0)))
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert self._eager_gc_node(src, monkeypatch, tmp_path) == "60"


# (id, code point, label).  Every character either runtime's built-in
# trim treats as whitespace, plus the six §9.7.2 now names.  The two
# host libraries disagree about this set in BOTH directions, which is
# why the rule has to be written down rather than inherited: Python's
# ``str.strip`` takes U+001C–U+001F and U+0085, JavaScript's ``trim``
# does not; ``trim`` takes U+FEFF, ``strip`` does not.
_DECIMAL_WS_CASES = [
    # The set §9.7.2 states — the same one `is_whitespace` uses.
    ("tab", 0x09, True), ("lf", 0x0A, True), ("vt", 0x0B, True),
    ("ff", 0x0C, True), ("cr", 0x0D, True), ("space", 0x20, True),
    # Python-only: the four information separators and NEL.
    ("fs", 0x1C, False), ("gs", 0x1D, False), ("rs", 0x1E, False),
    ("us", 0x1F, False), ("nel", 0x85, False),
    # Accepted by both built-ins, in neither runtime's stated set.
    ("nbsp", 0xA0, False), ("ogham", 0x1680, False),
    ("en_quad", 0x2000, False), ("line_sep", 0x2028, False),
    ("para_sep", 0x2029, False), ("narrow_nbsp", 0x202F, False),
    ("mmsp", 0x205F, False), ("ideographic", 0x3000, False),
    # JavaScript-only: the byte-order mark.
    ("bom", 0xFEFF, False),
]


class TestBrowserDecimalWhitespaceSet856:
    """`decimal_from_string` ignores ONE stated whitespace set (#1303
    review).

    §9.7.2 says the grammar is "applied after ignoring surrounding
    whitespace" and that the accepted domain is defined by the grammar
    "rather than inherited from whatever the host library parses" — but
    the whitespace half was inherited, from ``str.strip`` on one host
    and ``String.prototype.trim`` on the other.  Those two sets differ
    in both directions, so six code points parted the runtimes: a
    decimal wrapped in U+0085 was ``Some`` natively and ``None`` in the
    browser, and one wrapped in U+FEFF was the other way round.

    The set is now the one the language already states for
    `is_whitespace` (§9.7.x): tab, LF, VT, FF, CR, space.  Nothing else
    is trimmed on either runtime, so a decimal padded with a no-break
    space is refused by both rather than accepted by both for reasons
    neither specification names.
    """

    _SRC = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  match decimal_from_string("{lit}") {{
    Some(@Decimal) -> IO.print("ACCEPT"),
    None -> IO.print("REFUSE")
  }}
}}
"""

    @pytest.mark.parametrize(
        ("case_id", "code_point", "trimmed"),
        _DECIMAL_WS_CASES,
        ids=[c[0] for c in _DECIMAL_WS_CASES],
    )
    @pytest.mark.parametrize("where", ["leading", "trailing"])
    def test_whitespace_acceptance_agrees(
        self, where: str, case_id: str, code_point: int, trimmed: bool,
        tmp_path: Path,
    ) -> None:
        esc = f"\\u{{{code_point:04X}}}"
        lit = esc + "1.5" if where == "leading" else "1.5" + esc
        expected = "ACCEPT" if trimmed else "REFUSE"
        out = _parity_stdout(
            self._SRC.format(lit=lit), tmp_path, f"decws_{where}_{case_id}",
        )
        assert out == expected


class TestBrowserLeadingBomParity1303:
    """A leading U+FEFF survives the trip into the browser host.

    ``new TextDecoder('utf-8')`` defaults to ``ignoreBOM: false``, whose
    meaning is the reverse of its name: it REMOVES a byte-order mark at
    the start of the buffer.  Every Vera string reaching a host binding
    goes through that decoder, so any string whose first character was
    U+FEFF arrived one character shorter than it left — while the
    reference host's ``safe_utf8_decode`` passes it straight through.

    Found from the `decimal_from_string` whitespace work, where it was
    the one code point still diverging after both hosts agreed on a
    trim set; the cause turned out to have nothing to do with trimming
    and to reach much further than `Decimal`.  The cases below are the
    three families that showed it, each asserted for cross-host
    equality *and* against the expected string, since two hosts both
    dropping the mark would satisfy equality alone.
    """

    @pytest.mark.parametrize(("case_id", "body", "expected"), [
        # The mark is the first character of the buffer — the only
        # position the default decoder strips.
        ("print", 'IO.print("\\u{FEFF}x")', "﻿x"),
        # Control: not first, so it was never at risk.  Pinned so a
        # future "fix" that strips U+FEFF everywhere goes red.
        ("print_trailing", 'IO.print("x\\u{FEFF}")', "x﻿"),
        # A BOM-prefixed document is not JSON; both hosts must refuse.
        (
            "json_parse",
            'match json_parse("\\u{FEFF}{}") { Ok(@Json) -> IO.print("OK"),'
            ' Err(@String) -> IO.print("ERR") }',
            "ERR",
        ),
        # Markdown keeps it as text rather than losing it.
        (
            "md_parse",
            'match md_parse("\\u{FEFF}hi") {'
            ' Ok(@MdBlock) -> IO.print(md_render(@MdBlock.0)),'
            ' Err(@String) -> IO.print("ERR") }',
            "﻿hi",
        ),
    ])
    def test_leading_bom_is_not_swallowed(
        self, case_id: str, body: str, expected: str, tmp_path: Path,
    ) -> None:
        src = f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  {body}
}}
"""
        assert _parity_stdout(src, tmp_path, f"bom_{case_id}") == expected


class TestBrowserDecimalExact856:
    """Browser↔native Decimal parity (#856).

    Spec §9.7.2 promises `Decimal` provides *exact* decimal arithmetic.
    The browser runtime used to route the family through JS `Number` /
    `Math.round`, so it (a) lost precision vs the Python runtime's
    `decimal.Decimal` and (b) *contradicted itself*: `decimal_compare`
    converted via `Number()` (so `"1.0"` == `"1"` → `Equal`) while
    `decimal_eq` did strict string comparison (same operands → `false`).

    Each test compiles ONE `.wasm` and runs it under both wasmtime
    (Python reference runtime) and Node (browser runtime), asserting
    byte-identical stdout.  Because the module bytes are identical, a
    divergence isolates the browser host imports in
    ``vera/browser/runtime.mjs``.  Pre-fix these are RED (wrong browser
    values / the self-contradiction); post-fix GREEN.
    """

    # --- helper prelude used by every fixture -----------------------
    # ``d(s)`` parses a decimal string with a 0 fallback (all inputs are
    # valid, so the fallback is never taken); ``show`` renders it.
    _PRELUDE = """
private fn d(@String -> @Decimal)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(decimal_from_string(@String.0), decimal_from_int(0))
}
"""

    def test_add_0_1_plus_0_2_is_exact(self, tmp_path: Path) -> None:
        """0.1 + 0.2 is exactly 0.3 — the canonical binary-float trap.
        Pre-fix the browser printed 0.30000000000000004."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(decimal_to_string(decimal_add(d("0.1"), d("0.2"))))
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "0.3"

    def test_sub_0_3_minus_0_1_is_exact(self, tmp_path: Path) -> None:
        """0.3 - 0.1 is exactly 0.2 — the subtraction dual of the 0.1+0.2
        trap (binary float gives 0.19999999999999998).  Pins decimal_sub
        parity, which the other arithmetic fixtures did not cover."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(decimal_to_string(decimal_sub(d("0.3"), d("0.1"))))
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "0.2"

    def test_mul_high_precision(self, tmp_path: Path) -> None:
        """A product with >16 significant digits that `Number` rounds
        wrong.  Native decimal keeps 28 significant digits."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(decimal_to_string(
    decimal_mul(d("1.23456789012345"), d("1.00000000000001"))))
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "1.234567890123462345678901234"

    def test_div_repeating_and_ideal_exponent(self, tmp_path: Path) -> None:
        """Division: 1/3 keeps 28 sig digits; 2.00/4 preserves the
        ideal-exponent trailing zero (0.50)."""
        # NB: extract via ``match`` rather than ``option_unwrap_or`` in
        # ``main`` — the latter tickles #878 (mono instantiation
        # inference misses user-fn return types in argument position,
        # so the Bool phantom default drops the ``main`` export); it is
        # orthogonal to the Decimal semantics under test here.
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = match decimal_div(d("1"), d("3")) {
    Some(@Decimal) -> decimal_to_string(@Decimal.0),
    None -> "none"
  };
  let @String = string_concat(@String.0, "|");
  let @String = match decimal_div(d("2.00"), d("4")) {
    Some(@Decimal) -> string_concat(@String.0, decimal_to_string(@Decimal.0)),
    None -> string_concat(@String.0, "none")
  };
  IO.print(@String.0)
}
"""
        expected = "0.3333333333333333333333333333|0.50"
        assert _parity_stdout(src, tmp_path, "dec856") == expected

    def test_div_by_zero_is_none(self, tmp_path: Path) -> None:
        """Division by zero returns None in both runtimes."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match decimal_div(d("5"), d("0")) {
    Some(@Decimal) -> IO.print(decimal_to_string(@Decimal.0)),
    None -> IO.print("none")
  }
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "none"

    def test_round_half_even(self, tmp_path: Path) -> None:
        """round() uses ROUND_HALF_EVEN like Python's quantize, not
        JS Math.round (half-up).  0.125→0.12, 2.675→2.68, -0.5→-0."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = decimal_to_string(decimal_round(d("0.125"), 2));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_round(d("2.675"), 2)));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_round(d("-0.5"), 0)));
  IO.print(@String.0)
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "0.12|2.68|-0"

    def test_neg_and_abs_edges(self, tmp_path: Path) -> None:
        """neg canonicalises signed zero to positive; abs clears sign;
        exponents are preserved."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = decimal_to_string(decimal_neg(d("0")));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_neg(d("1.50"))));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_abs(d("-3.14"))));
  IO.print(@String.0)
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "0|-1.50|3.14"

    def test_compare_eq_self_consistency(self, tmp_path: Path) -> None:
        """The self-contradiction pair: "1.0" vs "1".  Both operations,
        both runtimes, must agree — compare == Equal AND eq == true.
        Pre-fix the browser had compare==Equal but eq==false, and
        eq diverged from the numeric-equal Python runtime."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = match decimal_compare(d("1.0"), d("1")) {
    Less -> "less",
    Equal -> "equal",
    Greater -> "greater"
  };
  let @String = string_concat(string_concat(@String.0, "|"),
    if decimal_eq(d("1.0"), d("1")) then { "eq" } else { "ne" });
  IO.print(@String.0)
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "equal|eq"

    def test_compare_ordering_directions(self, tmp_path: Path) -> None:
        """compare returns Less / Greater on unequal values, matching
        the exact numeric ordering (not a Number() approximation)."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = match decimal_compare(d("0.1"), d("0.2")) {
    Less -> "less", Equal -> "equal", Greater -> "greater"
  };
  let @String = string_concat(string_concat(@String.0, "|"),
    match decimal_compare(d("100"), d("99.9")) {
      Less -> "less", Equal -> "equal", Greater -> "greater"
    });
  IO.print(@String.0)
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "less|greater"

    def test_eq_normalized_values(self, tmp_path: Path) -> None:
        """eq is numeric: 0.10 == 0.1, but 0.1 != 0.2."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if decimal_eq(d("0.10"), d("0.1")) then { "y" } else { "n" };
  let @String = string_concat(@String.0,
    if decimal_eq(d("0.1"), d("0.2")) then { "y" } else { "n" });
  IO.print(@String.0)
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "yn"

    def test_big_integer_add_no_float_rounding(self, tmp_path: Path) -> None:
        """Integers beyond Number.MAX_SAFE_INTEGER add exactly."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(decimal_to_string(
    decimal_add(d("9007199254740993"), d("9007199254740993"))))
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "18014398509481986"

    def test_neg_abs_context_rounding_29_digits(self, tmp_path: Path) -> None:
        """Python's unary minus and abs() APPLY THE CONTEXT: a 29-digit
        operand (exact in the store — the constructor does not round)
        is rounded to 28 significant digits by neg/abs.  Pre-fix the
        browser only flipped/cleared the sign bit, returning all 29
        digits (PR #877 engine-soundness panel, finding A)."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = decimal_to_string(decimal_neg(d("12345678901234567890123456789")));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_abs(d("-12345678901234567890123456789"))));
  IO.print(@String.0)
}
"""
        expected = ("-1.234567890123456789012345679E+28"
                    "|1.234567890123456789012345679E+28")
        assert _parity_stdout(src, tmp_path, "dec856") == expected

    def test_round_negative_places_beyond_prec(self, tmp_path: Path) -> None:
        """For places <= -28 the Python host's quantum ``Decimal(10)**-places``
        is itself context-rounded, so its exponent is ``-places - 27``, not 0.
        Pre-fix the browser hardcoded target exponent 0 for all negative
        places, producing wrong exponents AND wrong values (PR #877
        engine-soundness panel, finding B)."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = decimal_to_string(decimal_round(d("52746E+25"), -31));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_round(d("986480576275650962365099E-24"), -37)));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_round(d("5"), -28)));
  IO.print(@String.0)
}
"""
        expected = "5.2746000000000000000000000E+29|0E+10|0E+1"
        assert _parity_stdout(src, tmp_path, "dec856") == expected

    def test_round_absurd_places_overflow_fallback(self, tmp_path: Path) -> None:
        """places < -Emax (-999999): the Python host's quantum
        ``Decimal(10)**-places`` raises ``decimal.Overflow`` — previously
        an uncaught raw traceback (only InvalidOperation was caught),
        while the browser returned a value (0E+1999973): a crash path
        AND a cross-runtime divergence.  Both runtimes now return the
        operand unchanged, extending the InvalidOperation fallback rule;
        the -999999 boundary still quantizes (0E+999972).  Bare negative
        literals are avoided via ``0 - n`` (PR #877 fold-in)."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = decimal_to_string(decimal_round(d("1"), 0 - 2000000));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_round(d("1"), 0 - 999999)));
  IO.print(@String.0)
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "1|0E+999972"

    def test_binary_ops_large_finite_no_overflow(self, tmp_path: Path) -> None:
        """Large finite operands (the from_string grammar admits exponent
        tokens up to |exp| = 999999) whose exact result exceeds the
        default context's Emax must NOT overflow: the host binary ops
        run in a widened context (Emax/Emin = decimal.MAX_EMAX/MIN_EMIN,
        prec 28, ROUND_HALF_EVEN) so they return the same exact value the
        unbounded browser scaled-BigInt engine already produces.  Pre-fix
        ``decimal_mul(1e999999, 1e999999)`` exited ``vera run`` with a raw
        ``decimal.Overflow`` traceback while the browser returned
        1E+1999998 — a check-green crash AND a cross-runtime divergence
        (PR #877 CodeRabbit round, finding 3518540519).  Operation
        RESULTS may exceed the input-token bound; only inputs are
        bounded."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = decimal_to_string(decimal_mul(d("1e999999"), d("1e999999")));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_add(d("1e999999"), d("1e999999"))));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_sub(d("1e999999"), d("-1e999999"))));
  let @String = match decimal_div(d("1e999999"), d("1e-999999")) {
    Some(@Decimal) -> string_concat(string_concat(@String.0, "|"),
      decimal_to_string(@Decimal.0)),
    None -> string_concat(@String.0, "|none")
  };
  IO.print(@String.0)
}
"""
        expected = "1E+1999998|2E+999999|2E+999999|1E+1999998"
        assert _parity_stdout(src, tmp_path, "dec856") == expected

    def test_compare_eq_negative_operands(self, tmp_path: Path) -> None:
        """Negative-operand compare/eq parity: trailing-zero-equal pairs
        and strict ordering under sign (coverage was all-nonnegative
        before this — PR #877 CodeRabbit round)."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = match decimal_compare(d("-1.0"), d("-1")) {
    Less -> "less", Equal -> "equal", Greater -> "greater"
  };
  let @String = string_concat(string_concat(@String.0, "|"),
    if decimal_eq(d("-0.10"), d("-0.1")) then { "eq" } else { "ne" });
  let @String = string_concat(string_concat(@String.0, "|"),
    match decimal_compare(d("-0.2"), d("-0.1")) {
      Less -> "less", Equal -> "equal", Greater -> "greater"
    });
  let @String = string_concat(string_concat(@String.0, "|"),
    match decimal_compare(d("-100"), d("-99.9")) {
      Less -> "less", Equal -> "equal", Greater -> "greater"
    });
  IO.print(@String.0)
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "equal|eq|less|less"

    def test_from_string_acceptance_parity(self, tmp_path: Path) -> None:
        """Both runtimes accept EXACTLY the spec §9.7.2 grammar (ASCII
        finite decimals; no NaN/Inf/sNaN, no underscores, no non-ASCII
        digits).  Pre-fix the Python host accepted whatever
        ``decimal.Decimal`` does (NaN, Infinity, ``1_000``, unicode
        digits) while the browser rejected them — an undisclosed
        cross-target divergence (PR #877 CodeRabbit + panel; grammar
        unification per DESIGN.md: explicit over host-incidental)."""
        src = """
private fn acc(@String -> @String)
  requires(true) ensures(true) effects(pure)
{
  match decimal_from_string(@String.0) {
    Some(@Decimal) -> "y",
    None -> "n"
  }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = acc("1.5");
  let @String = string_concat(@String.0, acc("+1"));
  let @String = string_concat(@String.0, acc(".5"));
  let @String = string_concat(@String.0, acc("5."));
  let @String = string_concat(@String.0, acc("1e5"));
  let @String = string_concat(@String.0, acc("  1.5  "));
  let @String = string_concat(@String.0, acc("1e999999"));
  let @String = string_concat(@String.0, acc("1e-999999"));
  let @String = string_concat(@String.0, acc("NaN"));
  let @String = string_concat(@String.0, acc("Infinity"));
  let @String = string_concat(@String.0, acc("-Inf"));
  let @String = string_concat(@String.0, acc("sNaN"));
  let @String = string_concat(@String.0, acc("1_000"));
  let @String = string_concat(@String.0, acc("١٢٣"));
  let @String = string_concat(@String.0, acc("abc"));
  let @String = string_concat(@String.0, acc("1.2.3"));
  let @String = string_concat(@String.0, acc(""));
  let @String = string_concat(@String.0, acc("1e1000000"));
  let @String = string_concat(@String.0, acc("1e-1000000"));
  let @String = string_concat(@String.0, acc("1e9007199254740993"));
  let @String = string_concat(@String.0, acc("-1e-9007199254740993"));
  IO.print(@String.0)
}
"""
        # Eight conforming accepts (incl. the ±999999 exponent-bound
        # boundary), then thirteen rejects (specials, underscores,
        # unicode digits, malformed, out-of-range exponent tokens incl.
        # the beyond-MAX_SAFE_INTEGER probe).
        assert _parity_stdout(src, tmp_path, "dec856") == "y" * 8 + "n" * 13

    def test_from_string_exponent_token_bound(self, tmp_path: Path) -> None:
        """Exponent tokens beyond MAX_SAFE_INTEGER (CR finding
        3518083324): the browser's ``parseInt`` silently ROUNDED
        "1e9007199254740993" to exponent ...992 while the Python host
        stored it exactly — Some(1E+9007199254740993) natively vs
        Some(1E+9007199254740992) in the browser, a silent value
        divergence.  The spec grammar now bounds the exponent token to
        |exp| <= 999999 (the context's Emax/Emin floor — a larger
        literal could never participate in any operation without
        overflow), so BOTH runtimes reject the probe with None, and the
        browser checks the token as a string before any numeric
        conversion."""
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match decimal_from_string("1e9007199254740993") {
    Some(@Decimal) -> IO.print(decimal_to_string(@Decimal.0)),
    None -> IO.print("none")
  }
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "none"

    def test_from_float_formatting_parity(self, tmp_path: Path) -> None:
        """``decimal_from_float`` mirrors Python's ``Decimal(str(v))``,
        including Python float-repr FORMATTING: integral floats keep
        ``.0`` (so the stored exponent is -1, not 0).  The divergence
        propagates through arithmetic: from_float(100.0)*2 must be
        "200.0", not "200" (PR #877 panel, from_float residual +
        blast-radius chain finding)."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = decimal_to_string(decimal_from_float(100.0));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_mul(decimal_from_float(100.0), decimal_from_int(2))));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_from_float(0.0001)));
  let @String = string_concat(string_concat(@String.0, "|"),
    decimal_to_string(decimal_from_float(3.14)));
  IO.print(@String.0)
}
"""
        assert _parity_stdout(src, tmp_path, "dec856") == "100.0|200.0|0.0001|3.14"


class TestDbBrowserStub229:
    """#229 — the ``<DB>`` effect is host-backed (stdlib ``sqlite3``); the
    browser runtime cannot run SQL, so ``db_query`` / ``db_execute`` are
    deliberate ``Result.Err`` stubs (a driver + credentials can't live in
    client-side JS).  A DB program therefore links and runs in the browser,
    taking the ``Err`` arm — never a ``LinkError`` for a missing import."""

    def test_db_query_takes_err_arm_in_browser(self, tmp_path: Path) -> None:
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<DB>)
{
  match DB.query("SELECT 1", []) {
    Ok(@Array<Array<Option<String>>>) -> 1,
    Err(@String) -> 0
  }
}
"""
        wasm_path, _ = _compile_vera(src, tmp_path)
        result = _run_node(wasm_path, fn="main")
        assert result["value"] == 0  # the Err stub, not a LinkError

    def test_db_execute_takes_err_arm_in_browser(self, tmp_path: Path) -> None:
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<DB>)
{
  match DB.execute("CREATE TABLE t (x)", []) {
    Ok(@Int) -> 1,
    Err(@String) -> 0
  }
}
"""
        wasm_path, _ = _compile_vera(src, tmp_path)
        result = _run_node(wasm_path, fn="main")
        assert result["value"] == 0


# ---------------------------------------------------------------------------
# #349 — targeted browser-runtime coverage
# ---------------------------------------------------------------------------
#
# Baseline for this block was 81.74% line coverage on
# ``vera/browser/runtime.mjs`` (2700/3303, measured with
# ``VERA_JS_COVERAGE=1 pytest tests/test_browser.py``).  The classes below
# aim at the specific host imports the c8 report showed as *registered but
# never invoked* — their closure bodies had zero hits:
#
#   * ``map_get`` / ``map_size`` / ``map_values`` / ``mapAllocArrayOfStrings``
#   * ``rebuildWithout`` (the shared ``map_remove`` / ``set_remove`` rebuild)
#   * ``set_to_array``
#   * ``readJson`` (every ADT tag) and ``json_stringify``
#   * several ``decParse`` / ``decRoundPlaces`` / ``decDiv`` branches
#   * the ``Result.Err`` arms of the Regex and Json host bindings
#
# Every case compiles ONE ``.wasm`` and runs it under both runtimes, so a
# failure isolates ``runtime.mjs`` rather than codegen.

# (id, value type, first value, second value, unwrap_or fallback,
#  expression template rendering the value as a String, expected head)
#
# Fallbacks are deliberately chosen NOT to equal the value being read back,
# so a ``map_get`` that wrongly returned ``None`` would change the output
# instead of coinciding with the right answer.
_MAP_VALUE_CASES = [
    ("int", "Int", "10", "20", "0", "int_to_string({})", "20"),
    ("float64", "Float64", "1.5", "2.25", "0.0",
     "float_to_string({})", "2.25"),
    ("string", "String", '"x"', '"y"', '"?"', "{}", "y"),
    ("bool", "Bool", "true", "false", "true", "bool_to_string({})", "false"),
]

# (id, key type, first key, second key, lookup key)
_MAP_KEY_CASES = [
    ("int", "Int", "7", "8", "8"),
    ("float64", "Float64", "1.5", "2.5", "2.5"),
    ("string", "String", '"a"', '"b"', '"b"'),
    ("bool", "Bool", "true", "false", "false"),
]

# (id, element type, first element, second element)
_SET_ELEMENT_CASES = [
    ("string", "String", '"x"', '"y"'),
    ("int", "Int", "1", "2"),
    ("float64", "Float64", "1.5", "2.5"),
    ("bool", "Bool", "true", "false"),
]

# (id, JSON input as written in Vera source, expected canonical
#  json_stringify output).  One case per Json ADT tag, plus nesting.
# Since #1293 the expected string is the *shared* output of both hosts,
# not the browser's alone: spec §9.7.1 names the compact form canonical.
_JSON_TAG_CASES = [
    ("jnull", "null", "null"),
    ("jbool_true", "true", "true"),
    ("jbool_false", "false", "false"),
    ("jnumber", "3.5", "3.5"),
    ("jstring", '\\"hi\\"', '"hi"'),
    ("jarray", "[1,2,3]", "[1,2,3]"),
    ("jobject", '{\\"a\\":1}', '{"a":1}'),
    (
        "nested",
        '{\\"a\\":{\\"b\\":[1,{\\"c\\":null}]},\\"d\\":[true,\\"x\\"]}',
        '{"a":{"b":[1,{"c":null}]},"d":[true,"x"]}',
    ),
    ("array_of_objects", '[{\\"k\\":1},{\\"k\\":2}]', '[{"k":1},{"k":2}]'),
    ("empty_array", "[]", "[]"),
    ("empty_object", "{}", "{}"),
]

# (id, JSON input as written in Vera source, expected canonical output).
# Number rendering is where the two hosts diverged most widely (#1293):
# the integral ``1`` → ``1.0`` mutation the issue names is one row of a
# larger table, because Python's ``repr`` and ECMAScript's
# Number::toString disagree on *four* independent boundaries.  Every row
# here was measured on both hosts before the fix and is a boundary, not a
# sample: the exponential thresholds (10^21 upward, 10^-7 downward), the
# exponent's own spelling, and negative zero.
_JSON_NUMBER_CASES = [
    # Integral values render without a fractional part — the #1293 axis.
    ("integral", "[1,2]", "[1,2]"),
    ("integral_negative", "[-1]", "[-1]"),
    ("integral_zero", "[0]", "[0]"),
    # Negative zero keeps its sign bit through the ADT but renders "0".
    ("negative_zero", "[-0.0]", "[0]"),
    # Fractional values are untouched by the integral rule.
    ("fractional", "[1.5,2.25]", "[1.5,2.25]"),
    ("fractional_small", "[0.1]", "[0.1]"),
    ("fractional_long", "[12345.6789]", "[12345.6789]"),
    # Upper exponential boundary: plain digits below 10^21, exponent at
    # and above it.  Python's repr switches at 10^16 instead.
    ("plain_1e15", "[1e15]", "[1000000000000000]"),
    ("plain_1e16", "[1e16]", "[10000000000000000]"),
    ("plain_1e20", "[1e20]", "[100000000000000000000]"),
    ("exp_1e21", "[1e21]", "[1e+21]"),
    ("exp_1e30", "[1e30]", "[1e+30]"),
    ("plain_17_digits", "[123456789012345680]", "[123456789012345680]"),
    # Lower exponential boundary: plain digits down to 10^-6, exponent
    # below it.  Python's repr switches at 10^-5 instead.
    ("plain_1e_minus_6", "[0.000001]", "[0.000001]"),
    ("exp_1e_minus_7", "[1e-7]", "[1e-7]"),
    ("exp_1e_minus_300", "[1e-300]", "[1e-300]"),
    # Exponent spelling: no zero padding, explicit sign only when
    # positive... which is exactly where Python writes "1e-07".
    ("exp_multi_digit_mantissa", "[1.25e-9]", "[1.25e-9]"),
    ("exp_max_double", "[1.7976931348623157e308]",
     "[1.7976931348623157e+308]"),
    ("exp_min_subnormal", "[5e-324]", "[5e-324]"),
]


class TestBrowserMapValueTypes349:
    """Per-value-type and per-key-type Map host-import parity (#349).

    ``runtime.mjs`` dispatches Map bindings on a mangled
    ``map_insert$k<kt>_v<vt>`` suffix and decodes each bucket column with
    a type tag (``i`` i64, ``f`` f64, ``s`` String, else i32).  The
    existing suite only ever drove String→Int maps, so the f64 slot
    writer, the String-array emitter, and the ``map_get`` / ``map_size``
    / ``map_values`` closures were never invoked in the browser.
    """

    @pytest.mark.parametrize(
        ("case_id", "vtype", "va", "vb", "fallback", "show", "head"),
        _MAP_VALUE_CASES,
        ids=[c[0] for c in _MAP_VALUE_CASES],
    )
    def test_map_value_type_variants(
        self,
        case_id: str,
        vtype: str,
        va: str,
        vb: str,
        fallback: str,
        show: str,
        head: str,
        tmp_path: Path,
    ) -> None:
        """String-keyed Map carrying each supported value type, driven
        through get / size / values / keys / remove in one program."""
        mt = f"@Map<String, {vtype}>"
        got = show.format(f"option_unwrap_or(map_get({mt}.0, \"b\"), {fallback})")
        src = f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  let {mt} = map_insert(map_insert(map_new(), "a", {va}), "b", {vb});
  let @String = {got};
  let @String = string_concat(@String.0,
    string_concat("|", int_to_string(map_size({mt}.0))));
  let @String = string_concat(@String.0,
    string_concat("|", int_to_string(array_length(map_values({mt}.0)))));
  let @String = string_concat(@String.0,
    string_concat("|", int_to_string(array_length(map_keys({mt}.0)))));
  let @String = string_concat(@String.0,
    string_concat("|", int_to_string(map_size(map_remove({mt}.0, "a")))));
  IO.print(@String.0)
}}
"""
        out = _parity_stdout(src, tmp_path, f"map_v_{case_id}")
        assert out == f"{head}|2|2|2|1"

    @pytest.mark.parametrize(
        ("case_id", "ktype", "ka", "kb", "lookup"),
        _MAP_KEY_CASES,
        ids=[c[0] for c in _MAP_KEY_CASES],
    )
    def test_map_key_type_variants(
        self,
        case_id: str,
        ktype: str,
        ka: str,
        kb: str,
        lookup: str,
        tmp_path: Path,
    ) -> None:
        """Each supported key type through get / contains / keys / remove.

        ``map_keys`` is what routes an i64 / f64 / i32 / String key column
        into ``emitArray``; the String arm is the only caller of
        ``mapAllocArrayOfStrings``.
        """
        mt = f"@Map<{ktype}, Int>"
        src = f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  let {mt} = map_insert(map_insert(map_new(), {ka}, 10), {kb}, 20);
  let @String = int_to_string(
    option_unwrap_or(map_get({mt}.0, {lookup}), 0));
  let @String = string_concat(@String.0,
    string_concat("|", int_to_string(array_length(map_keys({mt}.0)))));
  let @String = string_concat(@String.0,
    string_concat("|", int_to_string(map_size(map_remove({mt}.0, {lookup})))));
  let @String = if map_contains({mt}.0, {lookup}) then {{
    string_concat(@String.0, "|yes")
  }} else {{
    string_concat(@String.0, "|no")
  }};
  IO.print(@String.0)
}}
"""
        out = _parity_stdout(src, tmp_path, f"map_k_{case_id}")
        assert out == "20|2|1|yes"


class TestBrowserSetElementTypes349:
    """Per-element-type Set host-import parity (#349).

    ``set_to_array`` and the ``set_remove`` structural rebuild
    (``rebuildWithout``, shared with ``map_remove``) had no browser-side
    caller at all.
    """

    @pytest.mark.parametrize(
        ("case_id", "etype", "ea", "eb"),
        _SET_ELEMENT_CASES,
        ids=[c[0] for c in _SET_ELEMENT_CASES],
    )
    def test_set_element_type_variants(
        self,
        case_id: str,
        etype: str,
        ea: str,
        eb: str,
        tmp_path: Path,
    ) -> None:
        st = f"@Set<{etype}>"
        src = f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  let {st} = set_add(set_add(set_new(), {ea}), {eb});
  let @String = int_to_string(array_length(set_to_array({st}.0)));
  let @String = string_concat(@String.0,
    string_concat("|", int_to_string(set_size({st}.0))));
  let @String = string_concat(@String.0,
    string_concat("|", int_to_string(set_size(set_remove({st}.0, {ea})))));
  let @String = string_concat(@String.0,
    string_concat("|", int_to_string(
      array_length(set_to_array(set_remove({st}.0, {ea}))))));
  let @String = if set_contains(set_remove({st}.0, {ea}), {eb}) then {{
    string_concat(@String.0, "|yes")
  }} else {{
    string_concat(@String.0, "|no")
  }};
  IO.print(@String.0)
}}
"""
        out = _parity_stdout(src, tmp_path, f"set_{case_id}")
        assert out == "2|2|1|1|yes"

    def test_set_add_duplicate_dedups_in_browser(self, tmp_path: Path) -> None:
        """Int elements stay BigInt end-to-end so the JS ``Set`` dedups
        consistently with the i64 round trip (the comment above the Set
        bindings in ``runtime.mjs`` calls this out explicitly)."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Set<Int> = set_add(set_add(set_add(set_new(), 5), 5), 6);
  IO.print(string_concat(
    int_to_string(set_size(@Set<Int>.0)),
    string_concat("|", int_to_string(array_length(set_to_array(@Set<Int>.0))))))
}
"""
        assert _parity_stdout(src, tmp_path, "set_dup") == "2|2"


class TestBrowserDecimalBranches349:
    """Decimal branches the #856 suite left cold (#349).

    ``TestBrowserDecimalExact856`` pinned the headline arithmetic; the
    c8 report still showed the exact-zero sign rule in ``decAdd``, the
    negative-shift arm of ``decDiv``, two ``decRoundPlaces`` special
    cases, the exponential arm of ``pyFloatRepr``, ``decimalAlloc``
    (non-finite storage) and ``decimal_to_float`` with zero hits.
    """

    _PRELUDE = """
private fn d(@String -> @Decimal)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(decimal_from_string(@String.0), decimal_from_int(0))
}
"""

    def test_exact_zero_sum_sign_and_round_special_cases(
        self, tmp_path: Path,
    ) -> None:
        """Six branches in one program:

        ``1 + -1`` takes ``decAdd``'s exact-zero arm with a positive
        result; ``-0 + -0`` takes the same arm with the both-negative
        rule that yields ``-0``.  ``round(0, 2)`` hits the zero
        short-circuit in ``decRoundPlaces``; ``round(1E+30, 2)`` hits
        the InvalidOperation fall-through that returns the operand
        unchanged.  ``decimal_to_float`` had no caller at all.
        """
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = decimal_to_string(decimal_add(d("1"), d("-1")));
  let @String = string_concat(@String.0, string_concat("|",
    decimal_to_string(decimal_add(d("-0"), d("-0")))));
  let @String = string_concat(@String.0, string_concat("|",
    decimal_to_string(decimal_round(d("0"), 2))));
  let @String = string_concat(@String.0, string_concat("|",
    decimal_to_string(decimal_round(d("1E+30"), 2))));
  let @String = string_concat(@String.0, string_concat("|",
    float_to_string(decimal_to_float(d("1.5")))));
  IO.print(@String.0)
}
"""
        out = _parity_stdout(src, tmp_path, "dec_branches")
        assert out == "0|-0|0.00|1E+30|1.5"

    def test_div_negative_shift_amount(self, tmp_path: Path) -> None:
        """``decDiv`` computes ``shiftAmt = digits(b) - digits(a) + 29``
        and only takes its ``else`` arm when the dividend has ~30 more
        digits than the divisor.  36 digits over 1 gives ``shiftAmt =
        -6``, so the divisor is scaled up instead of the dividend.
        """
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match decimal_div(d("123456789012345678901234567890123456"), d("7")) {
    Some(@Decimal) -> IO.print(decimal_to_string(@Decimal.0)),
    None -> IO.print("none")
  }
}
"""
        out = _parity_stdout(src, tmp_path, "dec_div_shift")
        assert out == "1.763668414462081127160493827E+34"

    def test_from_float_exponential_and_non_finite(
        self, tmp_path: Path,
    ) -> None:
        """``pyFloatRepr`` ports Python's float ``repr`` so
        ``decimal_from_float`` matches ``Decimal(str(v))`` byte for byte.
        Magnitudes outside ``1e-4 .. 1e16`` take its exponential arm;
        NaN / ±Infinity are stored verbatim through ``decimalAlloc``
        (the only caller), which ``decimalAllocVal`` would mangle.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = decimal_to_string(decimal_from_float(0.0000000001));
  let @String = string_concat(@String.0, string_concat("|",
    decimal_to_string(decimal_from_float(100000000000000000000.0))));
  let @String = string_concat(@String.0, string_concat("|",
    decimal_to_string(decimal_from_float(nan()))));
  let @String = string_concat(@String.0, string_concat("|",
    decimal_to_string(decimal_from_float(infinity()))));
  let @String = string_concat(@String.0, string_concat("|",
    decimal_to_string(decimal_from_float(0.0 - infinity()))));
  IO.print(@String.0)
}
"""
        out = _parity_stdout(src, tmp_path, "dec_from_float")
        assert out == "1E-10|1E+20|NaN|Infinity|-Infinity"


_JSON_ROUND_TRIP_PRELUDE = """
private fn round_trip(@String -> @String)
  requires(true) ensures(true) effects(pure)
{
  match json_parse(@String.0) {
    Ok(@Json) -> json_stringify(@Json.0),
    Err(@String) -> string_concat("ERR:", @String.0)
  }
}
"""


def _json_round_trip_src(json_text: str, *, times: int = 1) -> str:
    """A ``main`` that parses ``json_text`` and stringifies it ``times``
    times, re-parsing between each — the observable form of the
    ``json_stringify ∘ json_parse`` idempotence property."""
    inner = 'round_trip("' + json_text + '")'
    for _ in range(times - 1):
        inner = f"round_trip({inner})"
    return _JSON_ROUND_TRIP_PRELUDE + f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  IO.print({inner})
}}
"""


class TestBrowserJsonRoundTrip349:
    """``readJson`` / ``json_stringify`` coverage (#349).

    ``json_parse`` was exercised (``writeJson`` builds the ADT), but
    nothing in the suite ever called ``json_stringify``, so the whole of
    ``readJson`` — all six ADT tags including the ``decodeMap``-backed
    JObject arm — never ran in the browser.

    These were Node-only assertions while ``json_stringify`` diverged
    between the hosts (#1293).  Since that closed they are full parity
    assertions: the same ``.wasm`` runs under both runtimes and one
    expected string covers both, so a regression in either host's
    serializer — not just ``readJson``'s tag decoding — fails here.
    """

    @pytest.mark.parametrize(
        ("case_id", "json_text", "expected"),
        _JSON_TAG_CASES,
        ids=[c[0] for c in _JSON_TAG_CASES],
    )
    def test_json_stringify_tag_round_trip(
        self, case_id: str, json_text: str, expected: str, tmp_path: Path,
    ) -> None:
        src = _json_round_trip_src(json_text)
        assert _parity_stdout(src, tmp_path, f"json_{case_id}") == expected


class TestBrowserJsonStringifyParity349:
    """``json_stringify`` agrees byte for byte across the two runtimes
    (#349 finding, tracked as #1293, closed by the canonical form).

    Both hosts emit the compact form spec §9.7.1 pins: ``,`` / ``:``
    with no padding, and numbers rendered by ECMAScript's
    Number::toString.  Before the fix the Python host called
    ``json.dumps(value, ensure_ascii=False, allow_nan=False)`` — ``", "``
    / ``": "`` separators, and ``read_json`` hands it Python ``float``\\ s
    so an integral JNumber rendered as ``1.0`` — while the browser host
    called bare ``JSON.stringify(value)``.

    The class is a parity battery rather than a pair of pinned strings
    because there is no longer a divergence to pin.  It keeps the shape
    that made the pins useful: an exact expected string on every case, so
    a broken compile, a dead Node harness or an unrelated ``runtime.mjs``
    regression cannot read as "as expected".
    """

    def test_number_and_spacing(self, tmp_path: Path) -> None:
        """The headline #1293 case: integral numbers and separators."""
        src = _json_round_trip_src("[1,2]")
        assert _parity_stdout(src, tmp_path, "json_parity") == "[1,2]"

    @pytest.mark.parametrize(
        ("case_id", "json_text", "expected"),
        _JSON_NUMBER_CASES,
        ids=[c[0] for c in _JSON_NUMBER_CASES],
    )
    def test_number_rendering_boundaries(
        self, case_id: str, json_text: str, expected: str, tmp_path: Path,
    ) -> None:
        """Every boundary where ``repr(float)`` and Number::toString part
        company, not only the integral one #1293's title names.

        Fixing the integral case alone would leave ``1e16``, ``1e-7``,
        ``0.000001`` and ``-0.0`` diverging, and a battery built only
        around the reported symptom would not have noticed.
        """
        src = _json_round_trip_src(json_text)
        assert _parity_stdout(src, tmp_path, f"jsonnum_{case_id}") == expected

    @pytest.mark.parametrize(
        ("case_id", "json_text", "expected"),
        _JSON_TAG_CASES + _JSON_NUMBER_CASES,
        ids=[c[0] for c in _JSON_TAG_CASES + _JSON_NUMBER_CASES],
    )
    def test_stringify_is_idempotent(
        self, case_id: str, json_text: str, expected: str, tmp_path: Path,
    ) -> None:
        """``json_stringify(json_parse(·))`` is a fixed point on both hosts.

        A canonical form that is not idempotent is not canonical: feeding
        one host's output back through the pair must land on the same
        bytes, or ``1`` → ``1.0`` → ``1.0`` style drift can still
        accumulate across a pipeline.  Three passes, so a form that only
        stabilises after the first is caught too.
        """
        src = _json_round_trip_src(json_text, times=3)
        assert _parity_stdout(src, tmp_path, f"jsonidem_{case_id}") == expected


# (id, JSON input as written in Vera source, expected canonical output).
# Every row is a *key* the canonical form must carry through the browser
# host's JS intermediates unchanged.  None of them can be spelled with an
# alphabetically-ordered object, which is all the rest of the JSON
# battery uses — so none of them was covered.
_JSON_KEY_ORDER_CASES = [
    # Two array-index keys, written in descending order.
    ("descending_index", '{\\"2\\":1,\\"1\\":2}', '{"2":1,"1":2}'),
    # Numeric, not lexicographic: "10" before "9", with a non-index key
    # after both so the two orderings cannot coincide.
    ("numeric_vs_lexical", '{\\"10\\":1,\\"9\\":1,\\"a\\":1}',
     '{"10":1,"9":1,"a":1}'),
    # An index key inserted *after* a non-index one — the shape that
    # moves to the front rather than merely swapping with a neighbour.
    ("index_after_name", '{\\"b\\":1,\\"3\\":2,\\"a\\":3}',
     '{"b":1,"3":2,"a":3}'),
    ("nested_in_object", '{\\"x\\":{\\"2\\":1,\\"1\\":2}}',
     '{"x":{"2":1,"1":2}}'),
    ("nested_in_array", '[{\\"2\\":1,\\"1\\":2}]', '[{"2":1,"1":2}]'),
    # ``__proto__`` is not an ordering case: assigning it to an ordinary
    # JS object runs Object.prototype's setter and creates no own
    # property at all, so the whole field vanishes from the output.
    ("proto_key", '{\\"__proto__\\":{\\"a\\":1}}', '{"__proto__":{"a":1}}'),
    # A duplicate key keeps the LAST value at the FIRST position, which
    # is what a Python dict and a JS Map both do — pinned so the fix
    # cannot quietly move the survivor to the end.
    ("duplicate_key", '{\\"b\\":1,\\"a\\":1,\\"b\\":2}', '{"b":2,"a":1}'),
]


class TestBrowserJsonKeyOrderParity1293:
    """Object key order survives the browser host's JS intermediates.

    Canonical (§9.7.1) key order is insertion order — what both hosts'
    underlying ``Map<String, Json>`` bucket already holds, and what
    ``dumps_canonical`` documents itself as preserving.  The browser host
    used to reach that bucket through *ordinary JS objects* on both sides
    of the WASM boundary: ``JSON.parse`` returns one, ``writeJson``
    enumerated it with ``Object.entries``, and ``readJson`` rebuilt one
    key by key.  An ordinary object cannot carry insertion order —
    ES OrdinaryOwnPropertyKeys lists array-index keys first, in ascending
    numeric order — nor a key named ``__proto__``, whose assignment hits
    ``Object.prototype``'s setter instead of creating an own property.

    Both losses are silent and neither is visible to an object with
    alphabetically-ordered, non-numeric keys, which is the only shape
    the rest of the JSON battery uses.  So the hole sat inside exactly
    the property #1293 claims to have fixed.
    """

    @pytest.mark.parametrize(
        ("case_id", "json_text", "expected"),
        _JSON_KEY_ORDER_CASES,
        ids=[c[0] for c in _JSON_KEY_ORDER_CASES],
    )
    def test_key_order_round_trip(
        self, case_id: str, json_text: str, expected: str, tmp_path: Path,
    ) -> None:
        src = _json_round_trip_src(json_text)
        assert _parity_stdout(src, tmp_path, f"jsonkey_{case_id}") == expected

    @pytest.mark.parametrize(
        ("case_id", "json_text", "expected"),
        _JSON_KEY_ORDER_CASES,
        ids=[c[0] for c in _JSON_KEY_ORDER_CASES],
    )
    def test_key_order_is_idempotent(
        self, case_id: str, json_text: str, expected: str, tmp_path: Path,
    ) -> None:
        """Three passes, not one.

        A host that reorders on every pass and a host that reorders once
        into a fixed point are both wrong, but only the first is caught
        by a single round trip when the input happens to already be in
        the host's preferred order.
        """
        src = _json_round_trip_src(json_text, times=3)
        assert (
            _parity_stdout(src, tmp_path, f"jsonkeyidem_{case_id}") == expected
        )

    def test_constructed_object_keeps_its_build_order(
        self, tmp_path: Path,
    ) -> None:
        """A ``JObject`` the program *built* rather than parsed.

        A round trip cannot tell "both sides were fixed" from "neither
        was": two compensating reorderings cancel, and the parse side's
        ascending-index order happens to be a fixed point of the
        stringify side's.  This case has no parse side at all — the map
        is built by ``map_insert`` in Vera, so the bucket order is the
        program's, and only ``readJson`` plus the serialiser stand
        between it and the output.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<String, Json> = map_insert(map_insert(map_insert(
    map_new(), "b", JNumber(1.0)), "3", JNumber(2.0)), "a", JNumber(3.0));
  IO.print(json_stringify(JObject(@Map<String, Json>.0)))
}
"""
        assert (
            _parity_stdout(src, tmp_path, "jsonbuiltorder")
            == '{"b":1,"3":2,"a":3}'
        )


class TestBrowserJsonStringifyNonFinite1293:
    """A non-finite ``JNumber`` refuses to serialise on BOTH hosts (#1293).

    RFC 8259 has no NaN and no Infinity, so there is no right answer to
    return — only a right way to fail.  The native host has always
    refused; the browser silently emitted ``null``, turning a value the
    format cannot carry into a *different, valid* value that no later
    consumer can tell from a genuine JSON ``null``.  That is the silent
    wrong answer DESIGN §Design principles 2 rules out, and it is the
    asymmetry #1293 folds in beside the formatting axes.

    The assertion is deliberately two-sided: the call must raise, **and**
    nothing may reach stdout.  Asserting only "raises" would still pass a
    host that printed ``null`` and then failed for some later reason.
    """

    _SRC = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  IO.print(json_stringify(JNumber({expr})))
}}
"""

    @pytest.mark.parametrize(
        ("case_id", "expr", "rendered"),
        [
            ("nan", "nan()", "NaN"),
            ("infinity", "infinity()", "Infinity"),
            ("negative_infinity", "0.0 - infinity()", "-Infinity"),
        ],
    )
    def test_non_finite_fails_on_both_hosts(
        self, case_id: str, expr: str, rendered: str, tmp_path: Path,
    ) -> None:
        native, browser = _both_failures(
            self._SRC.format(expr=expr), tmp_path, f"jsonnf_{case_id}",
        )
        # The WHOLE sentence, taken from the reference implementation, so
        # the browser's hand-copied duplicate in ``runtime.mjs`` is held
        # against the original rather than against a shared fragment
        # short enough for both to satisfy while saying different things
        # — including the value's own spelling ("NaN" / "Infinity" /
        # "-Infinity"), which each host derives independently.
        expected = _non_finite_message(rendered)
        assert "not representable in JSON" in expected  # guards the guard
        # Substring, not equality: wasmtime and the Node harness each
        # wrap the host message in a frame of their own.
        assert expected in native, native
        assert expected in browser, browser


# The four probe inputs from #1306's table, plus the container and
# multi-constant shapes that pin how far the refusal reaches and which
# constant names it.
_JSON_NON_FINITE_CASES = [
    ("bare_nan", "NaN", "NaN"),
    ("bare_infinity", "Infinity", "Infinity"),
    ("bare_negative_infinity", "-Infinity", "-Infinity"),
    ("nan_in_array", "[NaN]", "NaN"),
    ("infinity_in_object", '{"a":Infinity}', "Infinity"),
    ("negative_infinity_in_object", '{"a":-Infinity}', "-Infinity"),
    ("first_of_two_wins", "[NaN,Infinity]", "NaN"),
]

# Positions × escape casings for #1308: keys as well as values, nested
# anywhere, either spelling of the hex digits.
_JSON_LONE_SURROGATE_CASES = [
    ("value_lower", '{"k":"a\\ud800b"}', 0xD800),
    ("value_upper", '{"k":"a\\uD800b"}', 0xD800),
    ("value_low_surrogate", '{"k":"a\\udc00b"}', 0xDC00),
    ("key", '{"a\\ud800b":1}', 0xD800),
    ("key_upper", '{"a\\uD800b":1}', 0xD800),
    ("array_element", '["a\\ud800b"]', 0xD800),
    ("nested_object", '{"o":{"k":"a\\ud800b"}}', 0xD800),
    ("nested_array_in_object", '{"o":[1,"a\\ud800b"]}', 0xD800),
    ("top_level_string", '"a\\ud800b"', 0xD800),
    ("high_then_ascii_escape", '{"k":"\\ud800\\u0041"}', 0xD800),
    ("high_then_high", '{"k":"\\ud800\\ud800"}', 0xD800),
    ("low_then_valid_pair", '{"k":"\\udc00\\ud83d\\ude00"}', 0xDC00),
]

# The boundary the #1308 refusal must not overshoot, and the documents
# neither refusal may touch.
_JSON_ACCEPTED_CASES = [
    ("paired_surrogate_value", '{"k":"a\\ud83d\\ude00b"}', '{"k":"a\U0001F600b"}'),
    ("paired_surrogate_upper", '{"k":"a\\uD83D\\uDE00b"}', '{"k":"a\U0001F600b"}'),
    ("paired_surrogate_key", '{"a\\ud83d\\ude00b":1}', '{"a\U0001F600b":1}'),
    ("two_pairs", '["\\ud83d\\ude00\\ud83d\\ude80"]', '["\U0001F600\U0001F680"]'),
    ("pair_at_end", '{"k":"ab\\ud83d\\ude00"}', '{"k":"ab\U0001F600"}'),
    ("literal_astral", '{"k":"\U0001F600"}', '{"k":"\U0001F600"}'),
    ("nan_as_string_value", '{"k":"NaN"}', '{"k":"NaN"}'),
    ("infinity_as_string_value", '{"k":"Infinity"}', '{"k":"Infinity"}'),
    ("nan_as_key", '{"NaN":1}', '{"NaN":1}'),
    ("negative_number", "-1.5", "-1.5"),
    ("object_and_array", '{"a":1,"b":[true,null]}', '{"a":1,"b":[true,null]}'),
    ("escaped_backslash_u", '{"k":"\\\\ud800"}', '{"k":"\\\\ud800"}'),
]


# A syntactically valid number that overflows Float64 — the second entry
# route to a non-finite JNumber, and the one the constant refusal alone
# left open on BOTH hosts.
_JSON_OVERFLOW_CASES = [
    ("bare", "1e999", "Infinity"),
    ("bare_negative", "-1e999", "-Infinity"),
    ("in_array", "[1e999]", "Infinity"),
    ("in_object", '{"a":1e309}', "Infinity"),
    ("capital_exponent", "1E999", "Infinity"),
    ("doubly_nested", "[[1e999]]", "Infinity"),
    ("negative_in_object", '{"a":-1e999}', "-Infinity"),
]

# Finite boundary controls, underflow among them: 1e-999 decodes to 0,
# which is finite and in the domain.
_JSON_FINITE_BOUNDARY_CASES = [
    ("max_float", "1e308", "1e+308"),
    ("negative_max_float", "-1e308", "-1e+308"),
    ("largest_representable", "1.7976931348623157e308",
     "1.7976931348623157e+308"),
    ("underflow_to_zero", "1e-999", "0"),
    ("underflow_in_array", "[1e-999]", "[0]"),
]

# Text that is malformed for a reason the domain has nothing to say
# about.  Each must keep its host-native syntax message on both hosts —
# these are where a scan that matched a constant token anywhere, rather
# than only where a value may begin, would manufacture a shared sentence
# on one host and not the other.
_JSON_HOST_NATIVE_ERROR_CASES = [
    ("malformed", "{not json"),
    ("constant_lookalike", "[Infinity_x]"),
    ("nan_lookalike", "[NaNx]"),
    ("constant_as_bare_key", "{Infinity:1}"),
    ("signed_nan", "-NaN"),
    ("signed_nan_in_array", "[-NaN]"),
    ("plus_infinity", "+Infinity"),
    ("lowercase_infinity", "infinity"),
    ("lowercase_nan", "nan"),
    ("constant_suffix", "-Infinityx"),
]


# The integer arm of the overflow route.  ``json.loads`` yields a Python
# ``int`` for a digit string with no fraction or exponent, so these never
# reach a float range check on the reference host; ``JSON.parse`` has no
# such split and produced an ``Infinity`` here all along.  The bound is
# the double ROUNDING boundary — an integer above ``sys.float_info.max``
# but below the midpoint to 2**1024 rounds down and is accepted by both.

_JSON_INT_OVERFLOW_CASES = [
    ("digits_309", "1" + "0" * 309, "Infinity"),
    ("digits_400", "1" + "0" * 400, "Infinity"),
    ("negative_309", "-1" + "0" * 309, "-Infinity"),
    ("in_array", "[1" + "0" * 309 + "]", "Infinity"),
    ("in_object", '{"a":1' + "0" * 309 + "}", "Infinity"),
    ("exact_rounding_boundary", str(INT_ROUNDS_TO_INFINITY), "Infinity"),
]

_JSON_INT_ACCEPTED_CASES = [
    ("digits_308", "1" + "0" * 308, "1e+308"),
    ("negative_digits_308", "-1" + "0" * 308, "-1e+308"),
    ("boundary_minus_one", str(INT_ROUNDS_TO_INFINITY - 1),
     "1.7976931348623157e+308"),
    ("max_finite_as_int_plus_one", str(MAX_FINITE_AS_INT + 1),
     "1.7976931348623157e+308"),
    ("ordinary_integer", "42", "42"),
]


class TestBrowserJsonAcceptDomainParity1306_1308:
    """``json_parse`` accepts the same texts on both hosts (#1306, #1308).

    Three exclusions, and only one of them was a disagreement BETWEEN
    the hosts.  For the JavaScript constants the reference host was the
    lax one — Python's ``json.loads`` admits ``NaN`` / ``Infinity`` /
    ``-Infinity`` through its default ``parse_constant``, so the text
    parsed and the refusal landed at ``json_stringify`` instead, a
    *different call* from the browser's (#1306).

    The other two diverged from the stated domain on BOTH hosts at once,
    which is the harder shape to notice because a parity suite sees
    nothing wrong.  A lone-surrogate escape was accepted by both parsers
    and the memory boundary decided what happened next — ``TextEncoder``
    substituted U+FFFD in the browser, ``.encode()`` raised in the
    reference host (#1308).  A number that overflows (``1e999``) is
    accepted by both parsers as well, decoding to an infinite
    ``JNumber`` on each, and then dying at ``json_stringify`` on each
    (#1306 again, by a second entry route).

    Vera's own domain now settles all three, at one refusal point:
    ``json_parse`` accepts exactly RFC 8259-valid text that decodes to
    finite numbers and strings of Unicode scalar values.

    Every case runs the SAME ``.wasm`` under both runtimes and compares
    the full stdout, so the assertion covers the arm taken *and* the
    message — and the expected message is imported from the reference
    implementation, holding ``runtime.mjs``'s hand-copied duplicate
    against the original rather than against a fragment loose enough for
    both to satisfy while saying different things.
    """

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "name"),
        _JSON_NON_FINITE_CASES,
        ids=[c[0] for c in _JSON_NON_FINITE_CASES],
    )
    def test_non_finite_constants_refused_identically(
        self, case_id: str, raw_json: str, name: str, tmp_path: Path,
    ) -> None:
        out = _parity_stdout(
            accept_domain_src(raw_json), tmp_path, f"jsonnfp_{case_id}",
        )
        assert out == err(non_finite_parse_message(name))

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "code_point"),
        _JSON_LONE_SURROGATE_CASES,
        ids=[c[0] for c in _JSON_LONE_SURROGATE_CASES],
    )
    def test_lone_surrogates_refused_identically(
        self, case_id: str, raw_json: str, code_point: int, tmp_path: Path,
    ) -> None:
        out = _parity_stdout(
            accept_domain_src(raw_json), tmp_path, f"jsonls_{case_id}",
        )
        assert out == err(lone_surrogate_message(code_point))

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "expected"),
        _JSON_ACCEPTED_CASES,
        ids=[c[0] for c in _JSON_ACCEPTED_CASES],
    )
    def test_accepted_documents_are_unchanged(
        self, case_id: str, raw_json: str, expected: str, tmp_path: Path,
    ) -> None:
        """Controls, run beside the refusals rather than in another file.

        A paired surrogate escape is the ordinary way to write an astral
        character, and ``"NaN"`` as a string value is ordinary JSON — a
        refusal that reached either of them would break real documents,
        and would still look like a pass to a battery that only asserted
        the refusals fire.
        """
        out = _parity_stdout(
            accept_domain_src(raw_json), tmp_path, f"jsonok_{case_id}",
        )
        assert out == ok(expected)

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "name"),
        _JSON_OVERFLOW_CASES,
        ids=[c[0] for c in _JSON_OVERFLOW_CASES],
    )
    def test_overflow_to_infinity_refused_identically(
        self, case_id: str, raw_json: str, name: str, tmp_path: Path,
    ) -> None:
        """The route the constant refusal left open, on both hosts.

        ``1e999`` is grammatically valid RFC 8259 that ``json.loads``
        and ``JSON.parse`` both accept, decoding to an infinite number
        on each — so before this the domain's "no non-finite value gets
        in" claim was false in the same way on both hosts, and the
        program died at ``json_stringify`` instead.
        """
        out = _parity_stdout(
            accept_domain_src(raw_json), tmp_path, f"jsonovf_{case_id}",
        )
        assert out == err(non_finite_number_message(name))

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "expected"),
        _JSON_FINITE_BOUNDARY_CASES,
        ids=[c[0] for c in _JSON_FINITE_BOUNDARY_CASES],
    )
    def test_finite_numbers_at_the_boundary_are_unchanged(
        self, case_id: str, raw_json: str, expected: str, tmp_path: Path,
    ) -> None:
        """Including underflow, which is a different question.

        ``1e-999`` names a value neither host can represent either, but
        what it decodes to is ``0`` — finite, and in the domain.  A
        refusal generalised from "the text names an unrepresentable
        magnitude" rather than from "the decoded number is not finite"
        would take it.
        """
        out = _parity_stdout(
            accept_domain_src(raw_json), tmp_path, f"jsonfin_{case_id}",
        )
        assert out == ok(expected)

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "name"),
        _JSON_INT_OVERFLOW_CASES,
        ids=[c[0] for c in _JSON_INT_OVERFLOW_CASES],
    )
    def test_integer_overflow_refused_identically(
        self, case_id: str, raw_json: str, name: str, tmp_path: Path,
    ) -> None:
        """The route only the reference host had a hole in.

        A digit string with no fraction and no exponent decodes to a
        Python ``int``, which a float-only range check never examined —
        and then had to become an f64 at the WASM boundary, where the
        conversion raised.  ``JSON.parse`` produces a double either way,
        so the browser side of this parity assertion was already right;
        what it pins is that the reference host now says the same
        sentence rather than dying with a CPython one.
        """
        out = _parity_stdout(
            accept_domain_src(raw_json), tmp_path, f"jsonint_{case_id}",
        )
        assert out == err(non_finite_number_message(name))

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "expected"),
        _JSON_INT_ACCEPTED_CASES,
        ids=[c[0] for c in _JSON_INT_ACCEPTED_CASES],
    )
    def test_integers_that_round_into_range_are_unchanged(
        self, case_id: str, raw_json: str, expected: str, tmp_path: Path,
    ) -> None:
        """The boundary pair, and the band between the two candidate bounds.

        ``max_finite_as_int_plus_one`` is larger than the largest finite
        double and still rounds to it, so both hosts accept it.  A
        reference-host bound of ``sys.float_info.max`` would refuse it
        and trade one divergence for its mirror image — invisible to any
        battery whose only large case is a round number of zeros.
        """
        out = _parity_stdout(
            accept_domain_src(raw_json), tmp_path, f"jsonintok_{case_id}",
        )
        assert out == ok(expected)

    @pytest.mark.parametrize(
        ("case_id", "raw_json"),
        _JSON_HOST_NATIVE_ERROR_CASES,
        ids=[c[0] for c in _JSON_HOST_NATIVE_ERROR_CASES],
    )
    def test_malformed_text_keeps_its_host_native_message(
        self, case_id: str, raw_json: str, tmp_path: Path,
    ) -> None:
        """Only the domain refusals are shared sentences.

        Syntax errors keep their host-native message — Python ``json``
        on one side, ECMAScript ``JSON`` on the other — the long-standing
        convention ``TestBrowserHostErrorPaths349`` documents.  The
        browser reaches its shared sentence by asking whether stripping
        the bare constants makes the text parse, and it only considers a
        token where a value may begin; ``-NaN`` is the case that needs
        both rules, since the substitution alone would turn it into
        ``-0`` and report a refusal the reference host never makes.
        """
        native, browser = _both_stdouts(
            accept_domain_src(raw_json), tmp_path, f"jsonsyn_{case_id}",
        )
        assert native.startswith(ERR_PREFIX)
        assert browser.startswith(ERR_PREFIX)
        assert "json_parse:" not in native, native
        assert "json_parse:" not in browser, browser

    def test_a_non_finite_constant_outranks_a_lone_surrogate(
        self, tmp_path: Path,
    ) -> None:
        """Precedence, pinned, because the two hosts reach it differently.

        The reference host never gets to the surrogate scan — the
        constant makes ``json.loads`` itself raise.  The browser never
        gets to ``parseJsonOrdered`` — ``JSON.parse`` refused the text.
        Both arrive at the non-finite sentence, but only a test says so.
        """
        out = _parity_stdout(
            accept_domain_src('["\\ud800",NaN]'), tmp_path, "jsonprec",
        )
        assert out == err(non_finite_parse_message("NaN"))

    def test_the_two_walk_refusals_share_one_document_order(
        self, tmp_path: Path,
    ) -> None:
        """Overflow and lone surrogate are found by ONE walk, both hosts.

        Both are properties of the decoded value, so both are found by
        the same document-order traversal and whichever comes first
        names the refusal.  Two hosts each with its own precedence rule
        would agree on every single-violation document and diverge only
        here.
        """
        assert _parity_stdout(
            accept_domain_src('["a\\ud800b",1e999]'), tmp_path, "jsonwalk1",
        ) == err(lone_surrogate_message(0xD800))
        assert _parity_stdout(
            accept_domain_src('[1e999,"a\\ud800b"]'), tmp_path, "jsonwalk2",
        ) == err(non_finite_number_message("Infinity"))


class TestCanonicalNumberFormatMatchesEcmascript1293:
    """``format_json_number`` is differentially checked against the real
    ``JSON.stringify``, not against a table someone typed (#1293).

    The reference host now renders numbers itself instead of delegating
    to ``json.dumps``, so "matches ECMAScript" became a claim about a
    reimplementation.  A hand-written boundary table — which
    ``TestCanonicalNumberFormat`` in ``tests/test_codegen_json.py`` also
    has — only proves the cases its author thought of, and those are the
    cases the implementation was written to handle.  This runs the two
    implementations against each other over a deterministic random
    sample of doubles drawn from raw bit patterns, so the inputs are not
    ones either side was designed around.
    """

    @staticmethod
    def _ecmascript_strings(values: list[float], tmp_path: Path) -> list[str]:
        """``JSON.stringify(n)`` for each value, computed by Node."""
        literals = [repr(v) for v in values]
        script = tmp_path / "numfmt.mjs"
        script.write_text(
            "const xs = " + json.dumps(literals) + ";\n"
            "console.log(JSON.stringify("
            "xs.map(s => JSON.stringify(Number(s)))));\n",
            encoding="utf-8",
        )
        proc = subprocess.run(
            [NODE or "node", str(script)],
            capture_output=True, text=True, encoding="utf-8",
            timeout=60, check=True,
        )
        return list(json.loads(proc.stdout))

    def test_random_doubles_match_json_stringify(self, tmp_path: Path) -> None:
        # Seeded: a flaky parity test is worse than a smaller sample.
        rng = random.Random(20260813)
        values: list[float] = []
        while len(values) < 2000:
            bits = rng.getrandbits(64)
            (candidate,) = struct.unpack("<d", struct.pack("<Q", bits))
            if math.isfinite(candidate):
                values.append(candidate)
        # Mix in magnitudes the uniform bit sampler almost never lands
        # on: small integers and the exponential thresholds.
        values.extend(float(i) for i in range(-50, 51))
        values.extend([
            1e-7, 1e-6, 1e15, 1e16, 1e20, 1e21, 1e30, 5e-324,
            1.7976931348623157e308, 0.1, 0.5, 1.5, -0.0,
        ])

        expected = self._ecmascript_strings(values, tmp_path)
        # A short Node reply would otherwise truncate the comparison
        # silently: a bare ``zip`` stops at the shorter input, so a
        # harness that returned the first ten strings and died would
        # read as ten passes rather than one failure.  Both the length
        # assertion and ``strict=True`` are here because they catch it
        # at different points — the assertion names the shortfall, and
        # ``strict`` also guards a future refactor that builds the two
        # lists separately.
        assert len(expected) == len(values), (
            f"Node returned {len(expected)} strings for {len(values)} "
            f"doubles; the differential would have compared only the "
            f"common prefix"
        )
        mismatches = [
            (v, format_json_number(v), want)
            for v, want in zip(values, expected, strict=True)
            if format_json_number(v) != want
        ]
        assert not mismatches, (
            f"{len(mismatches)} of {len(values)} doubles render differently "
            f"from JSON.stringify; first five: {mismatches[:5]}"
        )

    def test_the_differential_can_fail(self, tmp_path: Path) -> None:
        """The differential above is only evidence if it can go red.

        ``repr`` is what the old ``json.dumps`` path emitted, and it is
        the natural wrong answer here, so the check that would have
        passed the pre-#1293 implementation is run explicitly and
        required to FAIL.  Without this, a broken Node invocation or an
        empty sample would make the differential vacuously green.
        """
        values = [1.0, 1e16, 1e-7, -0.0]
        expected = self._ecmascript_strings(values, tmp_path)
        assert expected == ["1", "10000000000000000", "1e-7", "0"]
        assert [repr(v) for v in values] != expected


class TestBrowserHostErrorPaths349:
    """``Result.Err`` arms of the Regex / Json / IO host bindings (#349).

    Each of these ``catch`` blocks and browser stubs was dead in the
    coverage report.  The Err *message* text differs between the two
    hosts (Python ``re`` / ``json`` vs JS ``RegExp`` / ``JSON``), so the
    parity cases assert only on which arm was taken — never on the
    message.
    """

    _PRELUDE = """
private fn find_no_match(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{
  match regex_find("abc", "z+") {
    Ok(@Option<String>) -> match @Option<String>.0 {
      Some(@String) -> "some",
      None -> "nomatch"
    },
    Err(@String) -> "err"
  }
}

private fn find_bad_pattern(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{
  match regex_find("abc", "[") {
    Ok(@Option<String>) -> "ok",
    Err(@String) -> "err"
  }
}

private fn find_all_bad_pattern(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{
  match regex_find_all("abc", "[") {
    Ok(@Array<String>) -> "ok",
    Err(@String) -> "err"
  }
}

private fn replace_bad_pattern(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{
  match regex_replace("abc", "[", "x") {
    Ok(@String) -> "ok",
    Err(@String) -> "err"
  }
}

private fn parse_bad_json(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{not json") {
    Ok(@Json) -> "ok",
    Err(@String) -> "err"
  }
}
"""

    def test_regex_and_json_err_arms(self, tmp_path: Path) -> None:
        """An unterminated character class ``[`` is rejected by both
        ``re.compile`` and ``new RegExp``, so all three Regex bindings
        take their ``invalid regex:`` catch; ``json_parse`` of malformed
        text takes its ``JSON.parse`` catch.  ``regex_find`` with a
        non-matching pattern also pins the ``allocOptionNone`` arm,
        which is a separate uncovered branch from the error path.
        """
        src = self._PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = find_no_match(());
  let @String = string_concat(@String.0,
    string_concat("|", find_bad_pattern(())));
  let @String = string_concat(@String.0,
    string_concat("|", find_all_bad_pattern(())));
  let @String = string_concat(@String.0,
    string_concat("|", replace_bad_pattern(())));
  let @String = string_concat(@String.0,
    string_concat("|", parse_bad_json(())));
  IO.print(@String.0)
}
"""
        out = _parity_stdout(src, tmp_path, "err_arms")
        assert out == "nomatch|err|err|err|err"

    def test_read_file_is_err_stub_in_browser(self, tmp_path: Path) -> None:
        """``IO.read_file`` has no browser implementation, so
        ``hostReadFile`` returns ``Err('File I/O not available in
        browser')`` where the native runtime really reads the file.  A
        deliberate non-parity path — it is why ``file_io`` is excluded
        from ``EXAMPLES_WITH_MAIN`` — so both sides are pinned, not
        compared.

        The file must **exist**.  Against a missing path the native host
        also returns ``Err``, so the browser stub and a genuine
        not-found are indistinguishable and the assertion would hold
        even if ``hostReadFile`` were fully implemented — the
        coinciding-default trap.  Reading a file that is really there
        is what makes ``Ok`` reachable on one side only.
        """
        present = tmp_path / "present.txt"
        present.write_text("hello", encoding="utf-8")
        # POSIX form: a Windows backslash would parse as a Vera escape.
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_file("%s") {
    Ok(@String) -> IO.print("ok"),
    Err(@String) -> IO.print("err")
  }
}
""" % present.as_posix()
        native, browser = _both_stdouts(src, tmp_path, "read_file_stub")
        assert native == "ok"
        assert browser == "err"

    def test_write_file_is_err_stub_in_browser(self, tmp_path: Path) -> None:
        """``IO.write_file``'s browser stub, pinned the way its
        ``read_file`` sibling is.

        ``test_file_io_returns_error`` runs the ``file_io`` example
        through Node and asserts only that the harness reported no
        error, which holds whether ``hostWriteFile`` returns ``Err`` or
        writes the file for real — smoke coverage, not a pin on the
        branch.  This asserts the branch: the same module bytes print
        ``ok`` under wasmtime and ``err`` under Node.

        The target directory must be **writable**.  Against an
        unwritable path the native host also returns ``Err``, so the
        stub and a genuine permission failure would be
        indistinguishable and the assertion would hold even if
        ``hostWriteFile`` were fully implemented — the coinciding-default
        trap that the ``read_file`` case documents in the other
        direction.  Reading the file back afterwards is what proves the
        native ``Ok`` arm really wrote, rather than merely reporting
        success.
        """
        target = tmp_path / "written.txt"
        # POSIX form: a Windows backslash would parse as a Vera escape.
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.write_file("%s", "written by vera") {
    Ok(_) -> IO.print("ok"),
    Err(@String) -> IO.print("err")
  }
}
""" % target.as_posix()
        native, browser = _both_stdouts(src, tmp_path, "write_file_stub")
        assert native == "ok"
        assert browser == "err"
        # The native Ok arm is only meaningful if the write happened.
        assert target.read_text(encoding="utf-8") == "written by vera"

    def test_read_char_is_err_stub_in_browser(self, tmp_path: Path) -> None:
        """``IO.read_char`` shipped natively in #618; the browser half
        needs JSPI suspend/resume (#609, still open).  Until that lands
        ``hostReadChar`` is an ``Err`` stub, so a program using it links
        and runs rather than failing to instantiate.
        """
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_char(()) {
    Ok(@String) -> 1,
    Err(@String) -> 0
  }
}
"""
        wasm_path, _ = _compile_vera(src, tmp_path)
        result = _run_node(wasm_path, fn="main")
        assert result["value"] == 0


class TestBrowserMarkdownNesting349:
    """Nested-block Markdown walks in the browser runtime (#349).

    Three loops were uncovered: the per-list-item lazy-continuation
    loop in ``parseBlocks`` (once for unordered, once for ordered
    lists), and the recursive ``child.forEach`` descents in
    ``hasHeading`` / ``hasCodeBlock`` / ``extractCodeBlocks``, which only
    run when a heading or fence is nested inside another block.
    ``examples/markdown.vera`` is flat, so none of them ever ran.

    ``md_render`` used to diverge on exactly this input (#1294), so the
    rendered prefix was asserted browser-side only.  It now agrees, and
    the whole string is compared across the two runtimes.  The three
    parse-side fields are still checked separately as well — each host's
    against the expected values, since the whole-string equality already
    makes the two sides the same text: they were the control that scoped
    #1294 to the renderer, and keeping them named means a future
    renderer regression cannot be mistaken for a parser one.
    """

    # A blockquote wrapping an h2 and a fenced block, so the recursive
    # descents have something to descend into.
    _SRC = r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match md_parse("- first\n  continued\n- second\n\n1. one\n   also one\n2. two\n\n> ## Quoted\n>\n> ```py\n> x = 1\n> ```\n") {
    Ok(@MdBlock) -> IO.print(string_concat(md_render(@MdBlock.0),
      string_concat("|",
      string_concat(bool_to_string(md_has_heading(@MdBlock.0, 2)),
      string_concat("|",
      string_concat(bool_to_string(md_has_code_block(@MdBlock.0, "py")),
      string_concat("|",
      int_to_string(array_length(
        md_extract_code_blocks(@MdBlock.0, "py")))))))))),
    Err(@String) -> IO.print(string_concat("ERR:", @String.0))
  }
}
"""

    def test_nested_walks_and_list_continuations(self, tmp_path: Path) -> None:
        native, browser = _both_stdouts(self._SRC, tmp_path, "md_nesting")
        # Whole string, renderer included, since #1294 closed.
        assert browser == native
        rendered, has_h2, has_py, n_blocks = browser.rsplit("|", 3)
        # The parse-side fields kept as a named control: they are what
        # scoped #1294 to the renderer, so a future divergence can still
        # be told apart from a parser one.  Each host is held against
        # the EXPECTED values, not against the other one (#1303 review):
        # the equality above already makes the two strings identical, so
        # a second cross-host comparison of fields sliced out of them
        # asserts nothing at all.
        expected_fields = ["true", "true", "1"]
        assert native.rsplit("|", 3)[1:] == expected_fields
        assert [has_h2, has_py, n_blocks] == expected_fields
        # Continuation lines survived the per-item loop in both list kinds
        # *and* stayed inside their item, which is the renderer's half.
        assert "- first continued" in rendered
        assert "1. one also one" in rendered


_MD_ROUND_TRIP_PRELUDE = r"""
private fn md_round_trip(@String -> @String)
  requires(true) ensures(true) effects(pure)
{
  match md_parse(@String.0) {
    Ok(@MdBlock) -> md_render(@MdBlock.0),
    Err(@String) -> string_concat("ERR:", @String.0)
  }
}
"""


def _md_round_trip_src(markdown: str, *, times: int = 1) -> str:
    """A ``main`` that runs ``markdown`` through ``md_render ∘ md_parse``
    ``times`` times and prints the result.

    ``markdown`` is written as it appears inside a Vera string literal —
    ``\n`` as the two characters, which Vera's lexer turns into a
    newline.
    """
    inner = 'md_round_trip("' + markdown + '")'
    for _ in range(times - 1):
        inner = f"md_round_trip({inner})"
    return _MD_ROUND_TRIP_PRELUDE + f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  IO.print({inner})
}}
"""


# (id, Markdown as written in a Vera string literal, canonical render).
# The four cases #1294 measured across the two hosts, in the order its
# table lists them.
_MD_RENDER_CASES = [
    ("list_continuation", r"- first\n  continued\n", "- first continued"),
    ("blockquote_pair", r"> a\n> b\n", "> a b"),
    (
        "nested_bq_fence",
        r"> ## Quoted\n>\n> ```py\n> x = 1\n> ```\n",
        # The bare `>` between the quote's two children survives the
        # round trip since the #1294 review; the render is now the
        # input back, byte for byte, minus the trailing newline.
        "> ## Quoted\n>\n> ```py\n> x = 1\n> ```",
    ),
    ("plain_paragraph", r"hello\nworld\n", "hello world"),
    # A quote holding two paragraphs — the shape whose separator the
    # reference renderer dropped, merging them into one on re-parse.
    ("blockquote_two_paragraphs", r"> a\n>\n> b\n", "> a\n>\n> b"),
]

# Corpus for the §9.7.3 round-trip property.  The first eight mirror
# ``TestRoundTrip`` in ``tests/test_markdown.py``, so the two runtimes
# are held to the corpus the reference renderer is already held to; the
# rest are the container/multi-line shapes #1294 was about, which that
# corpus has none of — every one of its eight entries is single-line or
# fence-only, which is exactly why a renderer that dropped container
# prefixes passed it.
_MD_ROUND_TRIP_CORPUS = [
    ("heading", r"# Hello"),
    ("paragraph", r"Some text here."),
    ("fence", r"```python\nprint(42)\n```"),
    ("thematic_break", r"---"),
    ("unordered_list", r"- item 1\n- item 2"),
    ("ordered_list", r"1. first\n2. second"),
    ("blockquote", r"> quoted"),
    ("table", r"| A | B |\n| --- | --- |\n| 1 | 2 |"),
    ("list_continuation", r"- first\n  continued\n"),
    ("ordered_continuation", r"1. one\n   also one\n2. two\n"),
    ("blockquote_pair", r"> a\n> b\n"),
    ("nested_bq_fence", r"> ## Quoted\n>\n> ```py\n> x = 1\n> ```\n"),
    ("plain_paragraph", r"hello\nworld\n"),
    # Multi-child containers — the shape whose separator the reference
    # renderer dropped (#1294 review).
    ("blockquote_two_paragraphs", r"> a\n>\n> b\n"),
    ("blockquote_para_then_list", r"> a\n>\n> - b\n> - c\n"),
    ("blockquote_three_children",
     r"> # H\n>\n> para\n>\n> ```py\n> x = 1\n> ```\n"),
    # Lazy continuation: an unmarked line continues the quote.
    ("blockquote_lazy_continuation", r"> a\nb\n"),
    ("blockquote_no_space", r">no space\n"),
    # An empty container: it has to survive its own render or the block
    # disappears and the document's spacing goes with it.
    ("blockquote_empty", r"---\n>\n"),
    ("blockquote_empty_between", r"> a\n\n>\n\n> b\n"),
    # A code span whose content holds a backtick — the shape that tells
    # a run-length scan apart from a next-single-backtick scan.
    ("code_span_interior_tick", r"``a`b``"),
    ("quoted_list", r"> - a\n>   b\n> - c\n"),
    ("quoted_multiline_fence", r"> ```sh\n> one\n> two\n> ```\n"),
    ("list_with_fence", r"- item\n  ```py\n  a = 1\n  b = 2\n  ```\n"),
    ("inlines", r"*em* and **strong** and `code` in one line\n"),
    ("link_and_image", r"[text](http://example.com) then ![alt](img.png)\n"),
    (
        "multi_block_document",
        r"# Title\n\nIntro line\ncontinued here.\n\n> note one\n> note two"
        r"\n\n- a\n  b\n- c\n\n```rs\nfn one() {}\nfn two() {}\n```\n\n---\n",
    ),
]


class TestBrowserMarkdownRenderParity349:
    """``md_render`` agrees with the reference renderer and is a fixed
    point (#349 finding, tracked as #1294, closed).

    The browser used to preserve a paragraph's internal soft line breaks
    and not re-apply the container prefix (``> ``, list-item indent) on
    output, where the reference renderer collapses the breaks to spaces
    and prefixes every line of every child.  The scope was any
    multi-line paragraph, not the list lazy continuation first observed,
    and the render was **not stable**: re-rendering its own output moved
    content out of its container (``> a b`` → ``> a\\nb`` →
    ``> a\\n\\nb``), so it broke both the round-trip property spec §9.7.3
    states for ``md_render`` and §12.9.3's identical-results requirement.
    On a blockquote wrapping a heading and a fenced block it destroyed
    the document outright the second time round.

    ``examples/markdown.vera`` is flat enough to miss all of it, and
    nothing else rendered Markdown under Node, which is why it went
    uncaught.  The battery below is therefore three-layered — cross-host
    equality, an exact expected string, and stability under re-render —
    because equality alone would pass two hosts that agree on the wrong
    answer, and an exact string alone would pass a renderer that is
    correct once and drifts on the second pass.
    """

    @pytest.mark.parametrize(
        ("case_id", "markdown", "expected"),
        _MD_RENDER_CASES,
        ids=[c[0] for c in _MD_RENDER_CASES],
    )
    def test_render_matches_across_hosts(
        self, case_id: str, markdown: str, expected: str, tmp_path: Path,
    ) -> None:
        """Byte-identical across the hosts, and equal to the reference
        renderer's answer written out."""
        src = _md_round_trip_src(markdown)
        assert _parity_stdout(src, tmp_path, f"md1_{case_id}") == expected

    @pytest.mark.parametrize(
        ("case_id", "markdown", "expected"),
        _MD_RENDER_CASES,
        ids=[c[0] for c in _MD_RENDER_CASES],
    )
    def test_render_is_stable_under_re_render(
        self, case_id: str, markdown: str, expected: str, tmp_path: Path,
    ) -> None:
        """Rendering the render changes nothing, on both hosts.

        This is where the browser's defect stopped being cosmetic: the
        nested blockquote's second render fragmented the fence into
        three and lifted ``x = 1`` clean out of the quote, past recovery
        by any subsequent parse.
        """
        src = _md_round_trip_src(markdown, times=2)
        assert _parity_stdout(src, tmp_path, f"md2_{case_id}") == expected

    @pytest.mark.parametrize(
        ("case_id", "markdown"),
        _MD_ROUND_TRIP_CORPUS,
        ids=[c[0] for c in _MD_ROUND_TRIP_CORPUS],
    )
    def test_round_trip_property_holds_on_both_hosts(
        self, case_id: str, markdown: str, tmp_path: Path,
    ) -> None:
        """``md_parse(md_render(b)) == Ok(b)`` (spec §9.7.3), in its
        observable form.

        Vera has no structural equality on ``MdBlock``, so the property
        is exercised through the one channel a Vera program can see:
        ``md_render`` composed with ``md_parse`` reaches a fixed point
        after the first application.  If a round trip lost or moved
        structure, the second render would differ from the first — which
        is exactly how the browser's blockquote failure showed up.  Both
        hosts must reach the *same* fixed point, so this is a parity
        assertion as well as a property one.
        """
        once = _parity_stdout(
            _md_round_trip_src(markdown), tmp_path, f"mdrt1_{case_id}",
        )
        twice = _parity_stdout(
            _md_round_trip_src(markdown, times=2), tmp_path,
            f"mdrt2_{case_id}",
        )
        assert twice == once
        assert not once.startswith("ERR:"), once


class TestBrowserMarkdownRenderConstructedAdt1294:
    """``md_render`` on ADTs a Vera program *built*, not parsed (#1294).

    Every other Markdown case in this file reaches the renderer through
    ``md_parse``, so it can only exercise the shapes the parser happens
    to produce.  ``MdBlock`` and ``MdInline`` are ordinary prelude ADTs
    a program can construct directly, and those values reach the same
    host import — so a renderer rule that only the parser never triggers
    is still reachable, and still has to agree across the two hosts.
    """

    @pytest.mark.parametrize(("case_id", "code", "rendered"), [
        ("plain", "code", "`code`"),
        ("one_backtick", "a`b", "``a`b``"),
        ("two_backticks", "a``b", "```a``b```"),
        ("leading_backtick", "`x", "`` `x ``"),
        ("trailing_backtick", "x`", "`` x` ``"),
    ])
    def test_code_span_fence(
        self, case_id: str, code: str, rendered: str, tmp_path: Path,
    ) -> None:
        """The fence is one backtick longer than the content's longest
        run, padded only when the content starts or ends with one.

        Reachable only from a constructed ADT for the multi-backtick
        cases, which is why the browser renderer was missing the rule
        entirely while every parse-driven test passed — and why the
        reference's own rule ("two backticks and padding") was wrong for
        two backticks without anything noticing.
        """
        src = f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  IO.print(md_render(MdDocument([MdParagraph([MdCode("{code}")])])))
}}
"""
        assert _parity_stdout(src, tmp_path, f"md_tick_{case_id}") == rendered

    @pytest.mark.parametrize(("case_id", "source", "expected"), [
        # Content WITH an interior backtick, so a scan that stops at the
        # next single tick lands somewhere else.  ``` ``double`` ``` on
        # its own does not distinguish the two scans: both recover
        # "double", which is how a wrong parser passes a plausible test.
        ("interior_tick", r"``a`b``", "``a`b``"),
        ("plain_double", r"``double``", "`double`"),
        # A three-backtick run at the start of a line is a BLOCK fence
        # before any inline parsing happens, so this is an unterminated
        # code block whose language tag is the rest of the line.  Both
        # hosts agree on that, which is the claim here; that the shape
        # is unrepresentable at line start is a limitation of the
        # §9.7.3 subset, pinned natively in tests/test_markdown.py.
        ("triple_is_a_block_fence", r"```a``b```", "```a``b```\n\n```"),
    ])
    def test_code_span_parses_by_run_length(
        self, case_id: str, source: str, expected: str, tmp_path: Path,
    ) -> None:
        """``md_parse`` closes a span on a run of EQUAL length.

        The browser scanned for the next single backtick, so
        ``` ``a`b`` ``` closed on the interior tick and left the rest as
        stray text — a parse divergence, not a render one, and the
        reason the fence rule above needs the parser fixed in the same
        change: without it the browser cannot read back its own output.
        """
        src = f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  match md_parse("{source}") {{
    Ok(@MdBlock) -> IO.print(md_render(@MdBlock.0)),
    Err(@String) -> IO.print(string_concat("ERR:", @String.0))
  }}
}}
"""
        assert _parity_stdout(src, tmp_path, f"md_span_{case_id}") == expected

    @pytest.mark.parametrize(("case_id", "code", "rendered"), [
        ("both_ends", " x ", "`  x  `"),
        ("all_spaces", "  ", "`    `"),
        ("wider", "  x  ", "`   x   `"),
        # One space is below the parser's two-character strip threshold,
        # so it is neither stripped nor padded.
        ("single_space", " ", "` `"),
        # Space padding and backtick padding are one space, not two.
        ("spaced_backticks", " `x` ", "``  `x`  ``"),
        # Only one end is a space — nothing is stripped, nothing padded.
        ("leading_only", " a", "` a`"),
        ("trailing_only", "a ", "`a `"),
    ])
    def test_code_span_pads_space_bounded_content(
        self, case_id: str, code: str, rendered: str, tmp_path: Path,
    ) -> None:
        """A span whose content starts *and* ends with a space (#1303
        review).

        Both parsers strip one such pair unconditionally, so without a
        matching pad on the way out the content's own spaces are eaten:
        ``MdCode(" x ")`` rendered ``` ` x ` ``` and read back as
        ``MdCode("x")``.  Constructed, because the shape is unreachable
        by parsing — the strip removes it on the way in — which is why
        the round-trip corpus never produced it on either host.
        """
        src = f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  IO.print(md_render(MdDocument([MdParagraph([MdCode("{code}")])])))
}}
"""
        assert _parity_stdout(src, tmp_path, f"md_sp_{case_id}") == rendered

    def test_code_span_padding_keeps_two_values_apart(
        self, tmp_path: Path,
    ) -> None:
        """``MdCode(" `x` ")`` and ``MdCode("`x`")`` used to render to
        the same bytes on both hosts, so the loss was not recoverable
        even by guessing.  Asserted as a *difference*, which a pair of
        per-value expected strings would not catch if both were equal.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat(
    md_render(MdDocument([MdParagraph([MdCode(" `x` ")])])),
    string_concat("|",
      md_render(MdDocument([MdParagraph([MdCode("`x`")])])))))
}
"""
        out = _parity_stdout(src, tmp_path, "md_sp_distinct")
        spaced, bare = out.split("|")
        assert spaced != bare
        assert (spaced, bare) == ("``  `x`  ``", "`` `x` ``")

    @pytest.mark.parametrize(("case_id", "expr", "rendered"), [
        ("only_item", "MdList(false, [[]])", "- "),
        (
            "empty_then_full",
            'MdList(false, [[], [MdParagraph([MdText("b")])]])',
            "- \n- b",
        ),
        # The ordered case corrupts silently: dropping the empty item
        # renumbers every item after it.
        (
            "ordered_middle",
            'MdList(true, [[MdParagraph([MdText("a")])], [], '
            '[MdParagraph([MdText("c")])]])',
            "1. a\n2. \n3. c",
        ),
    ])
    def test_empty_list_item_keeps_its_place(
        self, case_id: str, expr: str, rendered: str, tmp_path: Path,
    ) -> None:
        """An item with no blocks is a value the *parser* produces —
        ``- `` reads back as one empty item — so the renderer owes it a
        form (#1303 review).  Both hosts dropped it, which deleted the
        item and, in an ordered list, renumbered the rest.
        """
        src = f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  IO.print(md_render(MdDocument([{expr}])))
}}
"""
        assert _parity_stdout(src, tmp_path, f"md_ei_{case_id}") == rendered

    @pytest.mark.parametrize(("case_id", "expr", "rendered"), [
        ("list_then_para",
         'MdList(false, []), MdParagraph([MdText("after")])', "after"),
        ("para_then_list",
         'MdParagraph([MdText("before")]), MdList(false, [])', "before"),
        ("table_between",
         'MdParagraph([MdText("a")]), MdTable([]), '
         'MdParagraph([MdText("b")])', "a\n\nb"),
    ])
    def test_zero_line_child_takes_no_separator(
        self, case_id: str, expr: str, rendered: str, tmp_path: Path,
    ) -> None:
        """A list with no items and a table with no rows render to
        nothing, and must not drag the document separator in with them
        (#1303 review).

        Counting them left a blank line standing for an absent block,
        which the next parse cannot attribute to anything — so the
        render stopped being a fixed point.  The expected strings here
        have no leading or interior stray blank line, which is what the
        assertion is really about.
        """
        src = f"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  IO.print(md_render(MdDocument([{expr}])))
}}
"""
        assert _parity_stdout(src, tmp_path, f"md_zl_{case_id}") == rendered

    def test_empty_blockquote_still_occupies_a_line(
        self, tmp_path: Path,
    ) -> None:
        """A quote with no children renders as a bare ``>``.

        Rendering it as no lines at all makes the block vanish on
        re-parse and turns the document's separator into a stray blank
        line, so ``---\\n>`` came back as just ``---``.  Built directly
        *and* exercised through the corpus round trip below, because the
        constructed form is what pins the bytes and the parsed form is
        what proves the parser agrees they are the same block.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(md_render(MdDocument([MdThematicBreak(), MdBlockQuote([])])))
}
"""
        assert _parity_stdout(src, tmp_path, "md_empty_bq") == "---\n\n>"

    def test_multi_line_code_block_inside_a_blockquote(
        self, tmp_path: Path,
    ) -> None:
        """Every line of a container's child carries the prefix.

        The single case that a first-line-only prefix cannot fake, and
        the one whose second render destroyed the document.  Built
        directly so the assertion is about the renderer alone.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(md_render(MdDocument([MdBlockQuote([
    MdCodeBlock("sh", "one\\ntwo\\nthree")
  ])])))
}
"""
        assert _parity_stdout(src, tmp_path, "md_bq_fence_adt") == (
            "> ```sh\n> one\n> two\n> three\n> ```"
        )

    def test_nested_documents_separator_is_quoted(
        self, tmp_path: Path,
    ) -> None:
        """A *nested ``MdDocument``* separates its blocks with a blank
        line, and the enclosing quote turns that into a bare ``>``.

        The separator here comes from the ``MdDocument`` arm, not the
        blockquote arm — the quote has exactly one child.  What this
        pins is the quoting of a child's blank line: an unquoted empty
        line would end the quote on re-parse and split one blockquote
        into two.  The blockquote arm's own separator is a different
        rule with a different owner, pinned by the test below on the
        shape ``md_parse`` actually produces.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(md_render(MdDocument([MdBlockQuote([
    MdDocument([
      MdParagraph([MdText("first")]),
      MdParagraph([MdText("second")])
    ])
  ])])))
}
"""
        assert _parity_stdout(src, tmp_path, "md_bq_blank_adt") == (
            "> first\n>\n> second"
        )

    def test_blockquote_separates_its_own_children(
        self, tmp_path: Path,
    ) -> None:
        """The twin of the test above, on the shape the parser builds.

        ``md_parse`` wraps a quote's blocks as ``MdBlockQuote``'s direct
        children — there is no nested ``MdDocument`` — so the separator
        has to come from the blockquote arm itself.  It did not: two
        quoted paragraphs rendered as two adjacent quoted lines, which
        ``md_parse`` reads back as ONE paragraph, silently and on both
        hosts (#1294 review).  The test above passed throughout,
        because the arm it exercises was never the broken one.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(md_render(MdDocument([MdBlockQuote([
    MdParagraph([MdText("first")]),
    MdParagraph([MdText("second")])
  ])])))
}
"""
        assert _parity_stdout(src, tmp_path, "md_bq_children_adt") == (
            "> first\n>\n> second"
        )


class TestMdParseCrossHostAdtDifferential1301:
    """`md_parse` produces the SAME ADT on both hosts, byte for byte (#1301).

    Every other Markdown case in this file observes the parser through
    ``md_render``, which is what let the largest divergence class hide:
    the browser emitted one ``MdText`` per scan segment where the
    reference coalesces adjacent runs, so ``**unclosed`` was
    ``[MdEmph([]), MdText("unclosed")]`` natively and
    ``[MdText("*"), MdText("*unclosed")]`` in the browser — two different
    ADTs whose renders are the same string.  A Vera program that matches
    on ``MdParagraph``'s children sees the difference, which makes it a
    §12.9.3 violation rather than a cosmetic one.

    So this gate compares the ADTs, not the renders, and it compares them
    over a *generated* corpus rather than a curated list: the nine
    measured classes, then every block-opening line template taken one,
    two and three at a time (a dispatch-order difference shows up as soon
    as two branches compete for a line), then every inline shape in the
    four positions that reach the inline parser, then a seeded fuzz leg.
    A tenth class cannot appear without landing in one of those.

    Both legs are fed the identical corpus from
    ``tests/md_parse_corpus.py`` — a corpus written twice would let the
    gate pass on two hosts that were never asked the same question — and
    the browser leg runs as ONE Node process for the whole corpus, so the
    gate stays fast enough to actually be run.
    """

    @staticmethod
    def _browser_encodings(inputs: list[str], tmp_path: Path) -> list[str]:
        """Run the whole corpus through the browser parser in one process."""
        payload = tmp_path / "md_corpus.json"
        payload.write_text(
            json.dumps(inputs, ensure_ascii=True), encoding="utf-8",
        )
        proc = subprocess.run(
            [NODE or "node", str(ROOT / "tests" / "md_parse_bridge.mjs"),
             str(payload)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=120,
            check=False,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                f"md_parse bridge failed (rc={proc.returncode}):\n"
                f"stderr: {proc.stderr}"
            )
        return proc.stdout.splitlines()

    def test_every_corpus_input_parses_to_the_same_adt(
        self, tmp_path: Path,
    ) -> None:
        corpus = md_corpus()
        native = [encode_json(parse_markdown(text)) for _, text in corpus]
        browser = self._browser_encodings(
            [text for _, text in corpus], tmp_path,
        )
        assert len(browser) == len(native), (
            f"bridge returned {len(browser)} encodings for "
            f"{len(native)} inputs"
        )
        divergent = [
            (case_id, text, n, b)
            for (case_id, text), n, b in zip(corpus, native, browser)
            if n != b
        ]
        if divergent:
            shown = "\n".join(
                f"  {case_id}: {text!r}\n"
                f"    native : {n}\n"
                f"    browser: {b}"
                for case_id, text, n, b in divergent[:12]
            )
            raise AssertionError(
                f"{len(divergent)} of {len(corpus)} inputs parse to "
                f"different ADTs across the hosts:\n{shown}"
            )

    @pytest.mark.parametrize(
        ("case_id", "markdown"),
        CLASS_REPROS,
        ids=[c[0] for c in CLASS_REPROS],
    )
    def test_measured_divergence_class_repro_agrees(
        self, case_id: str, markdown: str, tmp_path: Path,
    ) -> None:
        """Each of the nine classes named in #1301, on its own repro.

        The sweep above would catch these too; naming them one per cell
        means a regression reports WHICH class came back rather than a
        count.
        """
        native = encode_json(parse_markdown(markdown))
        browser = self._browser_encodings([markdown], tmp_path)[0]
        assert browser == native, (
            f"{case_id} ({markdown!r}) diverges:\n"
            f"  native : {native}\n"
            f"  browser: {browser}"
        )


class TestMdGrammarSharedTable1301:
    """The two parsers read ONE grammar table (#1301).

    ``vera/markdown_grammar.py`` is the single source of every pattern
    and numeric constant the block dispatch turns on; the browser
    runtime carries a generated copy of it.  This asserts the copy is
    byte-identical to what the generator emits, so a pattern edited on
    one side and not the other cannot reach ``main`` — which is how the
    ``+`` bullet, the ``n)`` ordered marker and the separator-less table
    came to be three different grammars in the first place.
    """

    def test_runtime_mjs_carries_the_generated_block_verbatim(self) -> None:
        source = (ROOT / "vera" / "browser" / "runtime.mjs").read_text(
            encoding="utf-8",
        )
        assert js_grammar_block() in source, (
            "vera/browser/runtime.mjs does not carry the generated grammar "
            "block verbatim.  Regenerate it with:\n"
            "  python -c \"from vera.markdown_grammar import "
            "js_grammar_block; print(js_grammar_block())\""
        )
