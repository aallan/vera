"""Tests for vera.codegen — io (IO operations and the host-imported Markdown/Regex builtins).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

from pathlib import Path

from vera.codegen import (
    execute,
)

from tests.codegen_helpers import (
    _IO_PRELUDE,
    _compile_ok,
    _run_io,
)


# =====================================================================
# IO operations (C8.5 — #135)
# =====================================================================

class TestIOOperations:
    """Codegen and execution tests for all IO operations."""

    def test_io_read_line_echo(self) -> None:
        """IO.read_line reads from stdin; echo back via IO.print."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        exec_result = execute(
            result, fn_name="main", stdin="hello world\n",
        )
        assert exec_result.stdout == "hello world"

    # IO.read_char — pins the stdin_buf fixture short-circuit in
    # host_read_char.  Subprocess-based tests in test_cli.py cover
    # the real-pipe (non-TTY) path; these in-process tests pin
    # the StringIO fixture path that production code can hit via
    # `execute(stdin=...)`.  The TTY-raw-mode and Windows-msvcrt
    # paths are out of reach for automated testing without a
    # headless PTY harness — documented in the host_read_char
    # comment block.

    def test_io_read_char_stdin_buf_single(self) -> None:
        """stdin_buf path returns the first character on read_char."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_char(()) {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="A")
        assert exec_result.stdout == "A"
        assert exec_result.stderr == ""

    def test_io_read_char_stdin_buf_empty(self) -> None:
        """Empty stdin_buf returns Err("EOF"), not a crash or hang."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_char(()) {
    Ok(@String) -> IO.print(string_concat("got: ", @String.0)),
    Err(@String) -> IO.print(@String.0)
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="")
        assert exec_result.stdout == "EOF"
        assert exec_result.stderr == ""

    def test_io_read_char_stdin_buf_sequential(self) -> None:
        """Two reads from the same stdin_buf advance the cursor.

        Pins that `stdin_buf.read(1)` consumes characters in order.
        Catches regressions that would replace `.read(1)` with
        `.getvalue()[0]` or similar non-advancing reads.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = match IO.read_char(()) {
    Ok(@String) -> @String.0,
    Err(@String) -> "X"
  };
  let @String = match IO.read_char(()) {
    Ok(@String) -> @String.0,
    Err(@String) -> "X"
  };
  IO.print(string_concat(@String.1, @String.0))
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="AB")
        assert exec_result.stdout == "AB"
        assert exec_result.stderr == ""

    def test_io_read_char_stdin_buf_then_eof(self) -> None:
        """Read-succeeds-then-EOF: first call Ok, second call Err."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = match IO.read_char(()) {
    Ok(@String) -> @String.0,
    Err(@String) -> "E1"
  };
  let @String = match IO.read_char(()) {
    Ok(@String) -> string_concat("got: ", @String.0),
    Err(@String) -> @String.0
  };
  IO.print(string_concat(@String.1, "|"));
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="A")
        assert exec_result.stdout == "A|EOF"
        assert exec_result.stderr == ""

    def test_io_read_char_stdin_buf_utf8(self) -> None:
        """Multi-byte UTF-8 is read as one Unicode character.

        StringIO's `read(1)` returns one character (not one byte),
        so `é` (2-byte UTF-8) round-trips intact through the
        stdin_buf path.  Platform-independent (no reliance on the
        host's stdin encoding, unlike the subprocess tests).
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_char(()) {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="é")
        assert exec_result.stdout == "é"
        assert exec_result.stderr == ""

    def test_io_read_char_stdin_buf_passes_eot_literally(self) -> None:
        """Piped `\\x04` (Ctrl-D / EOT) stays a literal byte.

        The Unix TTY cbreak branch maps `\\x04` to EOF (so a user
        pressing Ctrl-D in a real-time CLI gets EOF semantics
        despite ICANON being disabled).  The non-TTY paths must
        NOT do that mapping — a pipe is a byte stream and the
        producer chose to include `\\x04`.  This pins the
        intentional asymmetry: stdin_buf returns `Ok("\\x04")`,
        not `Err("EOF")`.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_char(()) {
    Ok(@String) -> IO.print(string_concat("byte: ", @String.0)),
    Err(@String) -> IO.print(string_concat("err: ", @String.0))
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="\x04")
        assert exec_result.stdout == "byte: \x04"
        assert exec_result.stderr == ""

    def test_io_read_file_success(self) -> None:
        """IO.read_file reads a file and returns Ok(contents)."""
        import tempfile
        import os
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".txt", delete=False, encoding="utf-8",
        ) as f:
            f.write("file contents")
            f.flush()
            tmp_path = f.name
        # Hardcode the path in the Vera source (can't pass String args
        # to WASM functions from the host).  Convert to POSIX form so
        # backslashes in Windows paths (e.g. `C:\Users\...`) don't
        # collide with Vera's string-literal escape grammar — `\U`
        # would trip [E009] "invalid escape sequence" at parse time.
        # Windows file APIs accept forward slashes natively.  (#642)
        vera_path = Path(tmp_path).as_posix()
        source = f"""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  match IO.read_file("{vera_path}") {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }}
}}
"""
        try:
            result = _compile_ok(source)
            exec_result = execute(result, fn_name="main")
            assert exec_result.stdout == "file contents"
        finally:
            os.unlink(tmp_path)

    def test_io_read_file_roundtrip(self) -> None:
        """Write a file, then read it back, verify contents."""
        import tempfile
        import os
        tmp_dir = tempfile.mkdtemp()
        tmp_file = os.path.join(tmp_dir, "vera_test.txt")
        # Write a file from Vera, then read it back.  Convert to POSIX
        # form so backslashes in Windows paths don't trip Vera's
        # string-literal escape grammar — see `test_io_read_file_success`
        # for the same fix and #642 for the original repro.
        vera_path = Path(tmp_file).as_posix()
        source = f"""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  match IO.write_file("{vera_path}", "hello from vera") {{
    Ok(_) -> {{
      match IO.read_file("{vera_path}") {{
        Ok(@String) -> IO.print(@String.0),
        Err(@String) -> IO.print(@String.0)
      }}
    }},
    Err(@String) -> IO.print(@String.0)
  }}
}}
"""
        try:
            result = _compile_ok(source)
            exec_result = execute(result, fn_name="main")
            assert exec_result.stdout == "hello from vera"
        finally:
            if os.path.exists(tmp_file):
                os.unlink(tmp_file)
            os.rmdir(tmp_dir)

    def test_io_read_file_not_found(self) -> None:
        """IO.read_file on nonexistent file returns Err."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_file("/nonexistent/path/xyz.txt") {
    Ok(@String) -> IO.print("unexpected ok"),
    Err(@String) -> IO.print("got error")
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "got error"

    def test_io_write_file_bad_path(self) -> None:
        """IO.write_file on invalid path returns Err."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.write_file("/nonexistent/dir/file.txt", "data") {
    Ok(_) -> IO.print("unexpected ok"),
    Err(@String) -> IO.print("got error")
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "got error"

    def test_io_args_empty(self) -> None:
        """IO.args(()) with no CLI args returns empty array."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  array_length(@Array<String>.0)
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", cli_args=[])
        assert exec_result.value == 0

    def test_io_args_with_values(self) -> None:
        """IO.args(()) with CLI args returns correct values."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  IO.print(@Array<String>.0[0])
}
"""
        result = _compile_ok(source)
        exec_result = execute(
            result, fn_name="main", cli_args=["hello"],
        )
        assert exec_result.stdout == "hello"

    def test_io_exit_zero(self) -> None:
        """IO.exit(0) returns exit code 0."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("before exit");
  IO.exit(0)
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.exit_code == 0
        assert exec_result.stdout == "before exit"

    def test_io_exit_nonzero(self) -> None:
        """IO.exit(1) returns exit code 1."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.exit(1)
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.exit_code == 1

    def test_io_get_env_found(self) -> None:
        """IO.get_env with existing variable returns Some."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.get_env("TEST_VAR") {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("not found")
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(
            result, fn_name="main",
            env_vars={"TEST_VAR": "hello"},
        )
        assert exec_result.stdout == "hello"

    def test_io_get_env_not_found(self) -> None:
        """IO.get_env with missing variable returns None."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.get_env("NONEXISTENT_VAR") {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("not found")
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(
            result, fn_name="main", env_vars={},
        )
        assert exec_result.stdout == "not found"

    # ----------------------------------------------------------------
    # IO.sleep, IO.time, IO.stderr — added in #463.
    # ----------------------------------------------------------------

    def test_io_time_returns_positive_nat(self) -> None:
        """IO.time() returns current Unix time in ms — bracketed by host clock.

        Captures the Python-side time in milliseconds immediately
        before and after execution, then asserts the Vera program's
        reading falls inside that window.  Doesn't depend on a
        hard-coded epoch threshold, so it can't false-negative on
        hosts with skewed or frozen clocks.
        """
        import time as _time_mod
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Nat = IO.time(());
  IO.print(nat_to_string(@Nat.0))
}
"""
        result = _compile_ok(source)
        before_ms = int(_time_mod.time() * 1000)
        exec_result = execute(result, fn_name="main")
        after_ms = int(_time_mod.time() * 1000)
        vera_ms = int(exec_result.stdout)
        assert before_ms <= vera_ms <= after_ms, (
            f"IO.time() returned {vera_ms}, expected value in "
            f"[{before_ms}, {after_ms}]"
        )

    def test_io_sleep_completes(self) -> None:
        """IO.sleep(ms) returns without trapping; program continues.

        Doesn't test timing precision — that's host-dependent and
        flaky under load.  The contract is just that sleep returns
        and subsequent statements execute.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("before ");
  IO.sleep(1);
  IO.print("after")
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "before after"

    def test_io_sleep_zero_is_noop(self) -> None:
        """IO.sleep(0) is a no-op — doesn't block, doesn't error."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.sleep(0);
  IO.print("ok")
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "ok"

    def test_io_stderr_captured_when_requested(self) -> None:
        """IO.stderr output is captured into ExecuteResult.stderr.

        Confirms the stderr/stdout separation: IO.print goes to
        stdout, IO.stderr goes to stderr, neither crosses over.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("to stdout");
  IO.stderr("to stderr");
  IO.print(" more stdout")
}
"""
        result = _compile_ok(source)
        exec_result = execute(
            result, fn_name="main", capture_stderr=True,
        )
        assert exec_result.stdout == "to stdout more stdout"
        assert exec_result.stderr == "to stderr"

    def test_io_stderr_default_not_captured(self) -> None:
        """Without capture_stderr=True, stderr field is empty string.

        Preserves the pre-#463 ExecuteResult shape: tests that don't
        opt in to capture don't see anything in ``stderr``, even if
        the Vera program wrote to it (that output went to the real
        sys.stderr).  Also asserts stdout is empty — a program that
        only calls IO.stderr must not leak any bytes into the stdout
        stream.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.stderr("uncaptured")
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stderr == ""
        assert exec_result.stdout == ""

    def test_alloc_exported(self) -> None:
        """WAT exports $alloc when IO ops that allocate are used."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        assert '(export "alloc"' in result.wat

    def test_alloc_not_exported_for_print_only(self) -> None:
        """WAT does not export $alloc when only IO.print is used."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello") }
"""
        result = _compile_ok(source)
        assert '(export "alloc"' not in result.wat


# =====================================================================
# Markdown built-ins (§9.7.3) — host-imported functions
# =====================================================================


class TestMarkdown:
    """Markdown built-in functions: md_parse, md_render, md_has_heading,
    md_has_code_block, md_extract_code_blocks."""

    _PREAMBLE = """
effect IO { op print(String -> Unit); }
"""

    def test_md_parse_heading(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Hello");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> IO.print("ok"),
    Err(@String) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "ok"

    def test_md_has_heading_true(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Title");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Bool = md_has_heading(@MdBlock.0, 1);
      if @Bool.0 then { IO.print("yes") } else { IO.print("no") }
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "yes"

    def test_md_has_heading_false(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Title");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Bool = md_has_heading(@MdBlock.0, 2);
      if @Bool.0 then { IO.print("yes") } else { IO.print("no") }
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "no"

    def test_md_has_code_block_true(self) -> None:
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("```python\\ncode\\n```");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Bool = md_has_code_block(@MdBlock.0, "python");
      if @Bool.0 then { IO.print("yes") } else { IO.print("no") }
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "yes"

    def test_md_has_code_block_false(self) -> None:
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("```python\\ncode\\n```");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Bool = md_has_code_block(@MdBlock.0, "rust");
      if @Bool.0 then { IO.print("yes") } else { IO.print("no") }
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "no"

    def test_md_render_round_trip(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Hello");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "# Hello"

    def test_md_extract_code_blocks(self) -> None:
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("```python\\nprint(1)\\n```\\n\\n```python\\nprint(2)\\n```");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Array<String> = md_extract_code_blocks(@MdBlock.0, "python");
      IO.print(int_to_string(array_length(@Array<String>.0)));
      IO.print(@Array<String>.0[0]);
      IO.print(@Array<String>.0[1])
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "2print(1)print(2)"

    def test_md_extract_code_blocks_empty(self) -> None:
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Just a heading");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Array<String> = md_extract_code_blocks(@MdBlock.0, "python");
      IO.print(int_to_string(array_length(@Array<String>.0)))
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "0"


class TestRegex:
    """Regex built-in functions: regex_match, regex_find, regex_find_all,
    regex_replace."""

    _PREAMBLE = """
effect IO { op print(String -> Unit); }
"""

    # ---- regex_match ----

    def test_regex_match_found(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Bool, String> = regex_match("hello123", "\\d+");
  match @Result<Bool, String>.0 {
    Ok(@Bool) -> if @Bool.0 then { IO.print("yes") } else { IO.print("no") },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "yes"

    def test_regex_match_not_found(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Bool, String> = regex_match("hello", "\\d+");
  match @Result<Bool, String>.0 {
    Ok(@Bool) -> if @Bool.0 then { IO.print("yes") } else { IO.print("no") },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "no"

    def test_regex_match_invalid_pattern(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Bool, String> = regex_match("test", "[bad");
  match @Result<Bool, String>.0 {
    Ok(_) -> IO.print("unexpected"),
    Err(@String) -> IO.print("caught")
  }
}
"""
        assert _run_io(source, fn="main") == "caught"

    # ---- regex_find ----

    def test_regex_find_some(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Option<String>, String> = regex_find("abc123def", "\\d+");
  match @Result<Option<String>, String>.0 {
    Ok(@Option<String>) -> match @Option<String>.0 {
      Some(@String) -> IO.print(@String.0),
      None -> IO.print("none")
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "123"

    def test_regex_find_none(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Option<String>, String> = regex_find("hello", "\\d+");
  match @Result<Option<String>, String>.0 {
    Ok(@Option<String>) -> match @Option<String>.0 {
      Some(_) -> IO.print("some"),
      None -> IO.print("none")
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "none"

    # ---- regex_find_all ----

    def test_regex_find_all_multiple(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Array<String>, String> = regex_find_all("a1b2c3", "\\d");
  match @Result<Array<String>, String>.0 {
    Ok(@Array<String>) -> IO.print(int_to_string(array_length(@Array<String>.0))),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "3"

    def test_regex_find_all_no_matches(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Array<String>, String> = regex_find_all("hello", "\\d");
  match @Result<Array<String>, String>.0 {
    Ok(@Array<String>) -> IO.print(int_to_string(array_length(@Array<String>.0))),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "0"

    # ---- regex_replace ----

    def test_regex_replace_first_only(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<String, String> = regex_replace("hello world", "world", "vera");
  match @Result<String, String>.0 {
    Ok(@String) -> IO.print(@String.0),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "hello vera"

    def test_regex_replace_pattern(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<String, String> = regex_replace("abc123def", "\\d+", "NUM");
  match @Result<String, String>.0 {
    Ok(@String) -> IO.print(@String.0),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "abcNUMdef"

    def test_regex_replace_no_match(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<String, String> = regex_replace("hello", "\\d+", "NUM");
  match @Result<String, String>.0 {
    Ok(@String) -> IO.print(@String.0),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "hello"
