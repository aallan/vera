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


# =====================================================================
# TestBrowserState — State<T> host bindings
# =====================================================================


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
        # Use the 'vera' entry point (installed via console_scripts)
        vera_bin = shutil.which("vera") or str(
            ROOT / ".venv" / "bin" / "vera"
        )
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
