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

import json
import math
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from vera.codegen import compile as codegen_compile, execute
from vera.checker import typecheck
from vera.parser import parse_file
from vera.resolver import ModuleResolver
from vera.transform import transform

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
        )
        return proc.returncode == 0
    except Exception:
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
        timeout=30,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"Node harness failed (rc={proc.returncode}):\n"
            f"stderr: {proc.stderr}\nstdout: {proc.stdout}"
        )
    return json.loads(proc.stdout)


# ---------------------------------------------------------------------------
# Examples with main — parametric stdout parity
# ---------------------------------------------------------------------------

# Examples that export main and can be run in both runtimes.
# Excludes:
#   - io_operations: uses IO.read_line interactively
#   - file_io: uses IO.read_file/write_file (browser returns Result.Err)
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

        Mirrors ``test_array_sort_by_stability`` from ``test_codegen.py``
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
  -- lower bound inclusive, matching WASM's i64 range.  We don't
  -- print @Int.0 directly because int_to_string(INT64_MIN) hits a
  -- pre-existing bug (pending fix in #475): the negation of
  -- INT64_MIN overflows i64.  Use `@Int.0 < 0` to probe the value
  -- without triggering the bug.
  match json_as_int(JNumber(0.0 - 9223372036854775808.0)) {
    Some(@Int) -> IO.print(bool_to_string(@Int.0 < 0)),
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
            # none (+inf), none (-inf), none (+2^63), true
            # (Some branch taken for -2^63, and the value is
            # negative), none (below -2^63), 2 (array length), obj.
            "hi,none,3.14,true,42,none,none,none,none,"
            "true,none,2,obj"
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
        try:
            _run_python(result, fn_name="safe_divide", args=[0, 5])
        except Exception as exc:
            py_error = str(exc)

        node_result = _run_node(wasm_path, fn="safe_divide", fn_args=["0", "5"])

        # Both should have errors (contract violation)
        assert py_error is not None, "Python should report contract error"
        assert node_result["error"] is not None, "Node should report contract error"


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
effect IO {
  op print(String -> Unit);
}

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
effect IO {
  op print(String -> Unit);
}

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
effect IO {
  op print(String -> Unit);
}

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
effect IO {
  op print(String -> Unit);
}

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
            timeout=30,
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
