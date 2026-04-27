"""Runtime trap categorisation + stdout-on-trap preservation.

Exercises ``execute()``'s ``except Exception`` branch (in
``vera/codegen/api.py``) and ``cmd_run``'s ``WasmTrapError`` handler
(in ``vera/cli.py``).

Covers two paired bug fixes:

* **#522** — Output written via ``IO.print`` before a runtime trap was
  silently discarded because the captured ``output_buf`` was only
  surfaced on the success path. ``WasmTrapError`` now carries the
  buffer; ``cmd_run`` writes it to ``sys.stdout`` (text mode) or
  includes it in the JSON envelope (JSON mode) before reporting the
  error.

* **#516 (Stage 1)** — Every WASM trap was relabelled
  "Runtime contract violation" by ``cmd_run``'s catch-all. The
  classifier now maps the wasmtime trap reason substring to a stable
  ``kind`` and a Vera-native message; only true contract-host-import
  traps keep the contract-violation label.

Stage 2 (source mapping the trapping function) and Stage 3 (per-kind
``Fix:`` paragraphs) are deferred — see #516 for the campaign plan.
"""

from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from vera.cli import cmd_run
from vera.codegen.api import WasmTrapError, _classify_trap

if TYPE_CHECKING:
    from _pytest.capture import CaptureFixture


# =====================================================================
# _classify_trap — pure helper, easy to unit test in isolation
# =====================================================================


class _FakeTrap(Exception):
    """Stand-in for wasmtime's Trap/WasmtimeError without importing them.

    The classifier inspects ``str(exc)`` for the trap reason substring,
    so any exception whose ``str()`` matches the expected wasmtime
    rendering is sufficient for unit testing.
    """


class TestClassifyTrap:
    """``_classify_trap`` maps a wasmtime trap reason to (kind, message)."""

    def test_contract_violation_takes_precedence(self) -> None:
        # When ``last_violation`` is set, the host import was called and
        # we have the precise contract message. Trap reason is irrelevant.
        kind, message = _classify_trap(
            _FakeTrap("wasm trap: integer divide by zero"),
            ["Precondition violation in foo: @Int.0 > 0"],
        )
        assert kind == "contract_violation"
        assert message == "Precondition violation in foo: @Int.0 > 0"

    def test_divide_by_zero(self) -> None:
        kind, message = _classify_trap(
            _FakeTrap("wasm trap: integer divide by zero"), []
        )
        assert kind == "divide_by_zero"
        assert "division by zero" in message.lower()

    def test_out_of_bounds_memory(self) -> None:
        kind, message = _classify_trap(
            _FakeTrap("wasm trap: out of bounds memory access"), []
        )
        assert kind == "out_of_bounds"
        assert "out-of-bounds" in message.lower()

    def test_call_stack_exhausted(self) -> None:
        kind, message = _classify_trap(
            _FakeTrap("wasm trap: call stack exhausted"), []
        )
        assert kind == "stack_exhausted"
        assert "stack" in message.lower()

    def test_unreachable(self) -> None:
        kind, message = _classify_trap(
            _FakeTrap("wasm trap: wasm `unreachable` instruction executed"),
            [],
        )
        assert kind == "unreachable"
        assert "unreachable" in message.lower()

    def test_integer_overflow(self) -> None:
        kind, message = _classify_trap(
            _FakeTrap("wasm trap: integer overflow"), []
        )
        assert kind == "overflow"
        assert "overflow" in message.lower()

    def test_unknown_trap_surfaces_raw_message(self) -> None:
        kind, message = _classify_trap(
            _FakeTrap("wasm trap: some novel reason we have not classified"),
            [],
        )
        assert kind == "unknown"
        # Raw message preserved so the user still sees something useful.
        assert "novel reason" in message


# =====================================================================
# WasmTrapError — exception shape and inheritance
# =====================================================================


class TestWasmTrapError:
    """``WasmTrapError`` is a RuntimeError subclass carrying buffers + kind."""

    def test_is_runtime_error_subclass(self) -> None:
        # Existing ``except RuntimeError`` blocks still catch it; this
        # preserves backward compatibility.
        assert issubclass(WasmTrapError, RuntimeError)

    def test_carries_stdout_stderr_kind(self) -> None:
        exc = WasmTrapError(
            "Integer division by zero",
            stdout="line 1\nline 2\n",
            stderr="warn\n",
            kind="divide_by_zero",
        )
        assert str(exc) == "Integer division by zero"
        assert exc.stdout == "line 1\nline 2\n"
        assert exc.stderr == "warn\n"
        assert exc.kind == "divide_by_zero"

    def test_defaults(self) -> None:
        exc = WasmTrapError("trap")
        assert exc.stdout == ""
        assert exc.stderr == ""
        assert exc.kind == "unknown"


# =====================================================================
# End-to-end via cmd_run — text mode
# =====================================================================


_DIVZERO_WITH_PRINTS = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("line 1 before crash\\n");
  IO.print("line 2 before crash\\n");
  IO.print("line 3 before crash\\n");
  IO.print("line 4 before crash\\n");
  let @Nat = 42 / 0;
  ()
}
"""


_PRECONDITION_FAIL = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
"""


class TestStdoutOnTrap522:
    """#522 — IO.print output preceding a trap reaches the user."""

    def test_text_mode_prints_buffered_stdout_before_error(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        path = tmp_path / "divzero.vera"
        path.write_text(_DIVZERO_WITH_PRINTS)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        # All four IO.print lines must appear, in order, before the
        # error message hits stderr.
        for n in range(1, 5):
            assert f"line {n} before crash" in captured.out, (
                f"Expected 'line {n} before crash' in stdout, got: "
                f"{captured.out!r}"
            )
        # Error message itself goes to stderr.
        assert "Error" in captured.err

    def test_text_mode_cross_stream_ordering(
        self, tmp_path: Path,
    ) -> None:
        """The four IO.print lines appear before the error in code order.

        Sibling regression to the per-stream test above. ``capsys`` gives
        us per-stream content but not the relative order of writes across
        streams — for that we redirect both ``sys.stdout`` and
        ``sys.stderr`` into the *same* ``io.StringIO``, which preserves
        Python-level write order verbatim. If a future refactor were to
        swap the stdout-replay and error-print blocks in ``cmd_run``'s
        ``WasmTrapError`` handler, this test fails.

        Caveat: this test does **not** exercise the OS-level buffering
        concern that ``sys.stdout.flush()`` defends against. With both
        streams aimed at one ``StringIO`` the flush is a no-op (StringIO
        has no OS-level buffer). The flush matters only when stdout and
        stderr are independent file descriptors merged by a shell
        ``2>&1`` redirect — see #522 for the original symptom.
        """
        path = tmp_path / "divzero.vera"
        path.write_text(_DIVZERO_WITH_PRINTS)

        merged = io.StringIO()
        with contextlib.redirect_stdout(merged), \
                contextlib.redirect_stderr(merged):
            rc = cmd_run(str(path))

        assert rc == 1
        text = merged.getvalue()

        # All four print lines appear in order.
        positions = [
            text.find(f"line {n} before crash") for n in range(1, 5)
        ]
        assert all(p >= 0 for p in positions), (
            f"Missing some 'line N before crash' lines in merged output: "
            f"{text!r}"
        )
        assert positions == sorted(positions), (
            f"Print lines out of code order in merged output: positions="
            f"{positions}, text={text!r}"
        )

        # And the error message lands AFTER all four print lines.
        error_pos = text.find("Error")
        assert error_pos > positions[-1], (
            f"Error message should appear AFTER the last print line, but "
            f"error at {error_pos} vs last print at {positions[-1]}: "
            f"{text!r}"
        )

    def test_json_mode_includes_stdout_in_envelope(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        path = tmp_path / "divzero.vera"
        path.write_text(_DIVZERO_WITH_PRINTS)

        rc = cmd_run(str(path), as_json=True)

        assert rc == 1
        captured = capsys.readouterr()
        envelope = json.loads(captured.out)
        assert envelope["ok"] is False
        # Captured stdout is in the envelope, not on the actual stdout
        # stream (which would corrupt the JSON output).
        assert "stdout" in envelope
        for n in range(1, 5):
            assert f"line {n} before crash" in envelope["stdout"]
        # JSON-mode invariant: nothing leaks to the actual stderr stream.
        # The error message lives inside the envelope's diagnostics, not
        # on a sibling stream that would split the machine-readable output
        # for downstream consumers.
        assert captured.err == "", (
            "JSON mode must not write to stderr; got: " f"{captured.err!r}"
        )

    def test_json_mode_includes_stderr_in_envelope(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        # Sibling regression covering the stderr-capture half of the
        # WasmTrapError contract. Without ``capture_stderr=True`` in
        # the cmd_run -> execute() call, ``WasmTrapError.stderr`` was
        # always empty even though the exception class advertised it.
        # Pin the wired-through behaviour: IO.stderr writes preceding
        # a trap reach the JSON envelope's ``stderr`` field.
        source = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.stderr("warning A\\n");
  IO.stderr("warning B\\n");
  let @Nat = 42 / 0;
  ()
}
"""
        path = tmp_path / "divzero_stderr.vera"
        path.write_text(source)

        rc = cmd_run(str(path), as_json=True)

        assert rc == 1
        captured = capsys.readouterr()
        envelope = json.loads(captured.out)
        assert envelope["ok"] is False
        assert "stderr" in envelope, (
            "Expected captured IO.stderr in envelope; got envelope keys: "
            f"{sorted(envelope.keys())}. cmd_run must pass "
            "capture_stderr=True to execute() for this field to populate."
        )
        assert "warning A" in envelope["stderr"]
        assert "warning B" in envelope["stderr"]
        # JSON-mode invariant: IO.stderr writes go into the envelope, NOT
        # to the actual sys.stderr stream — otherwise the captured-stderr
        # mechanism would be doubled (envelope + live), confusing JSON
        # consumers who rely on the structured field.
        assert captured.err == "", (
            "JSON mode must not write captured IO.stderr to actual "
            f"stderr; got: {captured.err!r}"
        )


# =====================================================================
# End-to-end via cmd_run — trap categorisation
# =====================================================================


class TestTrapCategorisation516Stage1:
    """#516 Stage 1 — wasmtime trap reason mapped to a stable kind."""

    def test_divide_by_zero_not_labelled_contract_violation(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        path = tmp_path / "divzero.vera"
        path.write_text(_DIVZERO_WITH_PRINTS)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        # The historical mis-labelling: every trap was reported as
        # "Runtime contract violation". A divide-by-zero is not a
        # contract violation, and the new label must reflect that.
        assert "Runtime contract violation" not in captured.err
        assert "division by zero" in captured.err.lower()

    def test_contract_violation_still_labelled_correctly(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        # Counter-case: a real precondition failure still surfaces the
        # contract message (via the host-import-recorded ``last_violation``
        # path), not a generic wasmtime trap reason.
        path = tmp_path / "trap.vera"
        path.write_text(_PRECONDITION_FAIL)

        rc = cmd_run(str(path), fn_name="positive", fn_args=[0])

        assert rc == 1
        captured = capsys.readouterr()
        # Either the literal contract message or the spec-standard label
        # for a precondition failure must appear.
        combined = (captured.err + captured.out).lower()
        assert (
            "precondition" in combined or "requires" in combined
        ), f"Expected contract-violation label, got: {captured.err!r}"

    def test_json_mode_includes_trap_kind(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        path = tmp_path / "divzero.vera"
        path.write_text(_DIVZERO_WITH_PRINTS)

        rc = cmd_run(str(path), as_json=True)

        assert rc == 1
        captured = capsys.readouterr()
        envelope = json.loads(captured.out)
        diag = envelope["diagnostics"][0]
        # Stable identifier for downstream consumers (LSP, agents).
        assert diag.get("trap_kind") == "divide_by_zero"
        # JSON-mode invariant — see TestStdoutOnTrap522 for context.
        assert captured.err == "", (
            "JSON mode must not write to stderr; got: " f"{captured.err!r}"
        )

    def test_json_contract_violation_kind(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        path = tmp_path / "trap.vera"
        path.write_text(_PRECONDITION_FAIL)

        rc = cmd_run(str(path), fn_name="positive", fn_args=[0],
                     as_json=True)

        assert rc == 1
        captured = capsys.readouterr()
        envelope = json.loads(captured.out)
        diag = envelope["diagnostics"][0]
        assert diag.get("trap_kind") == "contract_violation"
        # JSON-mode invariant — see TestStdoutOnTrap522 for context.
        assert captured.err == "", (
            "JSON mode must not write to stderr; got: " f"{captured.err!r}"
        )


# =====================================================================
# #543 — IO.print streams live to sys.stdout in cmd_run text mode
# =====================================================================


class TestStdoutTee543:
    """#543 — ``IO.print`` writes mirror live to ``sys.stdout`` (text mode).

    Before this fix, ``host_print`` only appended to an in-memory
    ``output_buf`` (correct for the #522 trap-preservation fix), and
    ``cmd_run`` flushed the whole buffer to ``sys.stdout`` after
    ``execute()`` returned.  That meant any program using ANSI escape
    sequences (cursor home, clear screen) for animation — Conway's Game
    of Life, progress bars, TUIs, REPL-style output — was invisible
    until exit, at which point the entire transcript flushed in
    microseconds and the terminal processed all of the cursor-home
    escapes faster than a human eye can resolve.  Only the *last*
    frame ended up visible.

    Fix is a tee: ``host_print`` always writes to ``output_buf`` (so
    the trap-preservation contract from #522 still holds), and *also*
    writes to ``sys.stdout`` with an explicit flush per call when
    ``execute(tee_stdout=True)``.  ``cmd_run`` text mode opts in;
    JSON mode stays off (live stdout writes would corrupt the JSON
    envelope for downstream consumers parsing our output).
    """

    _ANIM_PROGRAM = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("frame 1\\n");
  IO.print("frame 2\\n");
  IO.print("frame 3\\n")
}
"""

    def test_text_mode_streams_each_print_live(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """Text mode: every IO.print appears on stdout exactly once."""
        path = tmp_path / "anim.vera"
        path.write_text(self._ANIM_PROGRAM)

        rc = cmd_run(str(path))

        assert rc == 0
        captured = capsys.readouterr()
        # Each frame appears, in order...
        assert "frame 1" in captured.out
        assert "frame 2" in captured.out
        assert "frame 3" in captured.out
        # ...and each appears exactly once. The pre-fix bug had the
        # whole transcript flush at exit; the fix mirrors live; if a
        # future refactor accidentally did both, every frame would
        # appear twice. Pin that invariant.
        assert captured.out.count("frame 1") == 1
        assert captured.out.count("frame 2") == 1
        assert captured.out.count("frame 3") == 1

    def test_text_mode_preserves_print_order(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """Live writes preserve the IO.print call order."""
        path = tmp_path / "anim.vera"
        path.write_text(self._ANIM_PROGRAM)

        rc = cmd_run(str(path))

        assert rc == 0
        captured = capsys.readouterr()
        positions = [captured.out.find(f"frame {n}") for n in (1, 2, 3)]
        assert all(p >= 0 for p in positions)
        assert positions == sorted(positions), (
            f"Frames out of order in stdout: {positions}, {captured.out!r}"
        )

    def test_json_mode_does_not_tee_to_stdout(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """JSON mode never tees — would corrupt the envelope."""
        path = tmp_path / "anim.vera"
        path.write_text(self._ANIM_PROGRAM)

        rc = cmd_run(str(path), as_json=True)

        assert rc == 0
        captured = capsys.readouterr()
        # The actual stdout contains exactly one thing: the JSON
        # envelope. The frame text lives inside it under "stdout",
        # not as a sibling write that would split the parse.
        envelope = json.loads(captured.out)
        assert envelope["ok"] is True
        assert "frame 1" in envelope["stdout"]
        assert "frame 2" in envelope["stdout"]
        assert "frame 3" in envelope["stdout"]
        # Crucial: the frames must NOT also appear outside the JSON
        # envelope, or downstream consumers parsing our stdout would
        # see "frame 1\\nframe 2\\nframe 3\\n{...}" and fail.
        # Strip the parsed envelope from the captured output and
        # check what's left.
        envelope_text = json.dumps(envelope, indent=2) + "\n"
        residue = captured.out.replace(envelope_text, "", 1)
        assert "frame" not in residue, (
            f"Live stdout writes leaked outside JSON envelope: "
            f"residue={residue!r}"
        )

    def test_tee_does_not_break_trap_preservation(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """#522 invariant: prints before a trap still reach the user.

        The tee fix mustn't regress the buffered-stdout-on-trap fix.
        ``output_buf`` is still populated on every host_print, so
        ``WasmTrapError.stdout`` is still complete; the cmd_run trap
        handler now skips the re-print (since tee already wrote
        live) but emits a closing newline if needed.
        """
        source = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("about to crash\\n");
  let @Nat = 42 / 0;
  ()
}
"""
        path = tmp_path / "anim_trap.vera"
        path.write_text(source)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        # Pre-trap stdout reached the user — appears exactly once
        # (live write only; trap handler does NOT re-print).
        assert "about to crash" in captured.out
        assert captured.out.count("about to crash") == 1
        # Error message lands on stderr after the live stdout.
        assert "Error" in captured.err

    def test_tee_flushes_each_write(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Each IO.print call flushes sys.stdout immediately.

        The whole point of the fix is real-time output — buffering at
        the Python io layer would defeat it just as effectively as
        buffering at the WASM layer did.  Pin the per-write flush by
        counting flush calls against IO.print calls.
        """
        path = tmp_path / "flush.vera"
        path.write_text(self._ANIM_PROGRAM)

        flush_count = 0
        write_count = 0
        original_write = __import__("sys").stdout.write
        original_flush = __import__("sys").stdout.flush

        def counting_write(s: str) -> int:
            nonlocal write_count
            if "frame" in s:
                write_count += 1
            return original_write(s)

        def counting_flush() -> None:
            nonlocal flush_count
            flush_count += 1
            original_flush()

        import sys as _sys
        monkeypatch.setattr(_sys.stdout, "write", counting_write)
        monkeypatch.setattr(_sys.stdout, "flush", counting_flush)

        rc = cmd_run(str(path))

        assert rc == 0
        # Three IO.print("frame N\\n") calls => three live writes...
        assert write_count == 3, f"expected 3 live writes, got {write_count}"
        # ...and at least three flushes (one per live write; the
        # cmd_run trailing "no closing newline needed" branch may
        # flush once more, but never fewer than the per-write flushes).
        assert flush_count >= 3, (
            f"expected at least 3 flushes (one per IO.print), got "
            f"{flush_count}"
        )

    def test_default_execute_does_not_tee(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """``execute()`` defaults to no tee — protects test suite silence.

        ``_run_io()`` and ``_run()`` in test_codegen.py call
        ``execute()`` without ``tee_stdout`` and rely on the captured
        ``ExecuteResult.stdout`` for assertions.  If the default
        flipped to True, every test that runs an IO.print program
        would dump the captured text into pytest's capsys stream and
        pollute test output.  Pin the default off.
        """
        from vera.codegen import compile as compile_program
        from vera.codegen import execute as _execute
        from vera.parser import parse_to_ast

        source = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("should not appear in capsys")
}
"""
        program = parse_to_ast(source)
        compile_result = compile_program(program, source=source)

        # capsys.readouterr() resets the buffer; readouterr after
        # execute captures only what execute itself wrote.
        capsys.readouterr()
        exec_result = _execute(compile_result)

        # The string is in the captured buffer (always).
        assert exec_result.stdout == "should not appear in capsys"
        # But not on the actual sys.stdout — tee defaulted off.
        captured = capsys.readouterr()
        assert "should not appear" not in captured.out
