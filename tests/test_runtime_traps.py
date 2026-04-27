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
        # JSON-mode invariant — see TestStdoutOnTrap522 for context.
        # No human-readable text may leak to the actual stderr stream;
        # error info, captured stderr, and trap kind all live inside
        # the JSON envelope so downstream consumers parsing our output
        # see exactly one machine-readable document.
        assert captured.err == "", (
            "JSON mode must not write to stderr; got: " f"{captured.err!r}"
        )
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


# =====================================================================
# #516 Stage 2 — runtime trap source mapping
# =====================================================================


class TestResolveTrapFrames516:
    """Unit tests for ``_resolve_trap_frames`` in isolation.

    The helper takes any object with a ``frames`` attribute (in
    practice ``wasmtime.Trap``) plus the ``fn_source_map`` from a
    ``CompileResult`` and produces a structured backtrace.  We
    exercise it with a ``_FakeFrame`` shim so the tests don't need to
    construct real wasmtime traps for every shape.
    """

    @staticmethod
    def _make_exc(*frames: object) -> object:
        """Build a frames-carrying exception stand-in."""
        class _FakeTrapExc(Exception):
            pass
        exc = _FakeTrapExc()
        exc.frames = list(frames)  # type: ignore[attr-defined]
        return exc

    @staticmethod
    def _frame(name: str, **kwargs: object) -> object:
        """Build a wasmtime.Frame stand-in."""
        class _FakeFrame:
            def __init__(self, n: str) -> None:
                self.func_name = n
                self.func_index = kwargs.get("func_index", 0)
                self.func_offset = kwargs.get("func_offset", 0)
                self.module_offset = kwargs.get("module_offset", 0)
                self.module_name = kwargs.get("module_name", None)
        return _FakeFrame(name)

    def test_user_function_resolves_to_file_lines(self) -> None:
        from vera.codegen.api import _resolve_trap_frames
        src_map = {"divide": ("/tmp/a.vera", 5, 9)}
        exc = self._make_exc(self._frame("divide"))

        frames = _resolve_trap_frames(exc, src_map)

        assert len(frames) == 1
        assert frames[0]["func"] == "divide"
        assert frames[0]["file"] == "/tmp/a.vera"
        assert frames[0]["line_start"] == 5
        assert frames[0]["line_end"] == 9
        assert frames[0]["is_builtin"] is False

    def test_builtin_helpers_tagged_as_builtin(self) -> None:
        """alloc / gc_collect / contract_fail must NOT claim a source.

        A frame inside ``$gc_collect`` carries the WAT name
        ``gc_collect``; the resolver must recognise it as runtime
        infrastructure and tag it accordingly rather than reporting
        a misleading file:line lookup miss as ``<unknown>``.
        """
        from vera.codegen.api import _resolve_trap_frames
        src_map: dict[str, tuple[str, int, int]] = {}

        for name in ("alloc", "gc_collect", "contract_fail"):
            exc = self._make_exc(self._frame(name))
            frames = _resolve_trap_frames(exc, src_map)
            assert len(frames) == 1
            assert frames[0]["func"] == name
            assert frames[0]["file"] == "<builtin>"
            assert frames[0]["line_start"] is None
            assert frames[0]["is_builtin"] is True, name

    def test_builtin_prefix_matches(self) -> None:
        """exn_* / vera.* / closure_sig_* are also runtime infrastructure."""
        from vera.codegen.api import _resolve_trap_frames

        for name in ("exn_String", "vera.print", "closure_sig_3"):
            exc = self._make_exc(self._frame(name))
            frames = _resolve_trap_frames(exc, {})
            assert frames[0]["is_builtin"] is True, name

    def test_monomorphized_name_resolves_to_base(self) -> None:
        """`identity$Int` looks up `identity` after the rightmost `$`.

        Generic monomorphization mangles names like
        ``identity$Map_String_Int``; the source map only stores the
        original generic.  The resolver strips at the rightmost ``$``
        and retries.
        """
        from vera.codegen.api import _resolve_trap_frames
        src_map = {"identity": ("/tmp/m.vera", 3, 6)}
        exc = self._make_exc(self._frame("identity$Int"))

        frames = _resolve_trap_frames(exc, src_map)

        assert frames[0]["func"] == "identity$Int"  # original WAT name
        assert frames[0]["file"] == "/tmp/m.vera"
        assert frames[0]["line_start"] == 3

    def test_unknown_user_function_keeps_frame_with_unknown_loc(
        self,
    ) -> None:
        """A user-named frame not in the map gets ``<unknown>`` not dropped.

        Better to surface the WAT name with no location than to drop
        the frame entirely — the user still benefits from knowing
        which function trapped, and any future source-map gap can be
        diagnosed from the unknown markers.
        """
        from vera.codegen.api import _resolve_trap_frames
        exc = self._make_exc(self._frame("mystery_helper"))

        frames = _resolve_trap_frames(exc, {})

        assert len(frames) == 1
        assert frames[0]["func"] == "mystery_helper"
        assert frames[0]["file"] == "<unknown>"
        assert frames[0]["is_builtin"] is False

    def test_no_frames_attribute_returns_empty_list(self) -> None:
        """Defensive: a trap-shaped exception with no `frames` returns []."""
        from vera.codegen.api import _resolve_trap_frames
        # Exception with no frames attribute at all.
        exc = RuntimeError("not a real trap")
        assert _resolve_trap_frames(exc, {}) == []

    def test_frames_preserved_in_outermost_first_order(self) -> None:
        """Order matches wasmtime's backtrace (outermost first)."""
        from vera.codegen.api import _resolve_trap_frames
        src_map = {
            "outer": ("/tmp/x.vera", 10, 15),
            "inner": ("/tmp/x.vera", 1, 5),
        }
        exc = self._make_exc(
            self._frame("inner"), self._frame("outer"),
        )
        frames = _resolve_trap_frames(exc, src_map)
        # wasmtime returns inner-first; we preserve that order so
        # the human reading the backtrace sees the leaf first
        # (matches the wasmtime CLI convention).
        assert [f["func"] for f in frames] == ["inner", "outer"]


_DIVIDE_BY_ZERO_USER_FN = """\
public fn divide(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.1 / @Int.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  divide(42, 0)
}
"""


class TestTrapSourceBacktrace516:
    """End-to-end: cmd_run surfaces resolved trap frames."""

    def test_text_mode_shows_source_backtrace(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        path = tmp_path / "div.vera"
        path.write_text(_DIVIDE_BY_ZERO_USER_FN)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        # The error line itself
        assert "Integer division by zero" in captured.err
        # The backtrace heading + the two user frames
        assert "Source backtrace:" in captured.err
        assert "in divide" in captured.err
        assert "in main" in captured.err
        # File + line range — exact path matches the temp fixture
        assert str(path) in captured.err
        # divide is on lines 1-5, main on 7-11 (0-indexed line 1 is
        # the first line of the source).  Check at least one of
        # them surfaces with a colon-separated line range.
        assert ":1-5" in captured.err
        assert ":7-11" in captured.err

    def test_text_mode_orders_leaf_first(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """The trapping function appears BEFORE its caller.

        wasmtime emits frames leaf-first (closest to the trap site);
        we preserve that order so the user reading top-to-bottom
        sees the trap origin first and the call chain widening
        outward — matches gdb / Python tracebacks / wasmtime CLI.
        """
        path = tmp_path / "div.vera"
        path.write_text(_DIVIDE_BY_ZERO_USER_FN)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        divide_pos = captured.err.find("in divide")
        main_pos = captured.err.find("in main")
        assert divide_pos >= 0 and main_pos >= 0
        assert divide_pos < main_pos, (
            "Expected leaf frame (divide) before caller (main); got: "
            f"{captured.err!r}"
        )

    def test_json_mode_includes_frames_array(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        path = tmp_path / "div.vera"
        path.write_text(_DIVIDE_BY_ZERO_USER_FN)

        rc = cmd_run(str(path), as_json=True)

        assert rc == 1
        captured = capsys.readouterr()
        envelope = json.loads(captured.out)
        diag = envelope["diagnostics"][0]
        assert diag["trap_kind"] == "divide_by_zero"
        # Structured frames present
        assert "frames" in diag
        assert isinstance(diag["frames"], list)
        # Both user frames there, with file + line metadata
        funcs = [f["func"] for f in diag["frames"]]
        assert "divide" in funcs
        assert "main" in funcs
        for frame in diag["frames"]:
            if frame["func"] in ("divide", "main"):
                assert frame["file"] == str(path)
                assert isinstance(frame["line_start"], int)
                assert isinstance(frame["line_end"], int)
                assert frame["is_builtin"] is False
        # JSON-mode invariant from #543 — see TestStdoutOnTrap522.
        assert captured.err == "", (
            "JSON mode must not write to stderr; got: " f"{captured.err!r}"
        )

    _CONTRACT_VIOLATION_PROGRAM = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  positive(0 - 5)
}
"""

    def test_contract_violation_carries_backtrace(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """Contract violations get the same source-mapping treatment.

        A precondition failure traps via ``$contract_fail`` which is
        a built-in; the user frame above it is the function whose
        precondition was violated.  Pre-Stage-2 the user only got
        the contract message; now they get the user-frame chain too.
        """
        path = tmp_path / "ctr.vera"
        path.write_text(self._CONTRACT_VIOLATION_PROGRAM)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        assert "Precondition violation" in captured.err
        assert "Source backtrace:" in captured.err
        # Both user frames surface; positive is the one whose
        # precondition failed (so the leaf), main is the caller.
        assert "in positive" in captured.err
        assert "in main" in captured.err

    def test_contract_violation_json_mode_includes_frames(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """JSON variant of the contract-violation backtrace test.

        The text-mode test above pins the human-readable `Source
        backtrace:` block; this one pins the structured `frames`
        array in the JSON envelope and the JSON-mode-no-stderr-leak
        invariant from #543.  Without this regression, a future
        refactor could surface the backtrace in text mode but drop
        it from the JSON path (or leak the trap message to stderr in
        JSON mode and corrupt the envelope for downstream
        consumers).
        """
        path = tmp_path / "ctr.vera"
        path.write_text(self._CONTRACT_VIOLATION_PROGRAM)

        rc = cmd_run(str(path), as_json=True)

        assert rc == 1
        captured = capsys.readouterr()
        envelope = json.loads(captured.out)
        diag = envelope["diagnostics"][0]
        assert diag["trap_kind"] == "contract_violation"
        # Structured frames present and includes both user frames
        assert "frames" in diag
        assert isinstance(diag["frames"], list)
        funcs = [f["func"] for f in diag["frames"]]
        assert "positive" in funcs
        assert "main" in funcs
        # Each user frame has the file + line metadata
        for frame in diag["frames"]:
            if frame["func"] in ("positive", "main"):
                assert frame["file"] == str(path)
                assert isinstance(frame["line_start"], int)
                assert isinstance(frame["line_end"], int)
                assert frame["is_builtin"] is False
        # JSON-mode invariant — same as the four `TestStdoutOnTrap522`
        # JSON tests pin: no human-readable text leaks to stderr in
        # JSON mode (would split downstream parsing of our output).
        assert captured.err == "", (
            "JSON mode must not write to stderr; got: " f"{captured.err!r}"
        )

    def test_default_execute_attaches_frames_to_wasmtraperror(
        self, tmp_path: Path,
    ) -> None:
        """``WasmTrapError.frames`` is populated even without cmd_run.

        Direct callers of ``execute()`` (tests, future LSP, library
        consumers) get the structured backtrace too, not just the
        CLI text rendering.
        """
        from vera.codegen import compile as compile_program
        from vera.codegen import execute as _execute
        from vera.codegen.api import WasmTrapError
        from vera.parser import parse_to_ast

        program = parse_to_ast(_DIVIDE_BY_ZERO_USER_FN)
        result = compile_program(program, source=_DIVIDE_BY_ZERO_USER_FN)
        assert result.fn_source_map  # source map populated
        assert "divide" in result.fn_source_map
        assert "main" in result.fn_source_map

        try:
            _execute(result, fn_name="main")
        except WasmTrapError as exc:
            assert exc.kind == "divide_by_zero"
            assert exc.frames, "frames should be populated"
            funcs = [f["func"] for f in exc.frames]
            assert "divide" in funcs
            assert "main" in funcs
        else:
            raise AssertionError("Expected WasmTrapError, got no exception")

    def test_text_mode_collapses_leading_runtime_helper_frames(
        self,
        tmp_path: Path,
        capsys: CaptureFixture[str],
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """When the leaf frame is a runtime helper, cmd_run shows the
        suppression marker and surfaces the first user frame at the top.

        Real GC / allocator traps that produce a builtin-leaf frame
        chain are timing-sensitive (they fire only under specific
        heap-pressure conditions), so this test monkeypatches
        ``vera.codegen.execute`` to raise a ``WasmTrapError`` with a
        synthetic frame list — the runtime-helper-collapse logic in
        ``cmd_run`` is pure given ``exc.frames``, so a deterministic
        synthetic input pins the contract that real traps would
        exercise.
        """
        # Trivial program that compiles cleanly — execute() never runs
        # because we patch it before cmd_run gets there.
        path = tmp_path / "trivial.vera"
        path.write_text("""\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
""")

        # Synthetic frame chain: two runtime helpers (gc_collect
        # then alloc) at the leaf, then the user code that called
        # into them.  Matches the wasmtime backtrace shape that #515
        # produced before the fix landed.
        synthetic_frames: list[dict[str, object]] = [
            {
                "func": "gc_collect", "file": "<builtin>",
                "line_start": None, "line_end": None,
                "is_builtin": True,
            },
            {
                "func": "alloc", "file": "<builtin>",
                "line_start": None, "line_end": None,
                "is_builtin": True,
            },
            {
                "func": "main", "file": str(path),
                "line_start": 1, "line_end": 3,
                "is_builtin": False,
            },
        ]

        from vera.codegen.api import WasmTrapError

        def fake_execute(*args: object, **kwargs: object) -> None:
            raise WasmTrapError(
                "Out-of-bounds memory access",
                stdout="",
                stderr="",
                kind="out_of_bounds",
                frames=synthetic_frames,
            )

        # cmd_run does `from vera.codegen import compile, execute` at
        # call time, so patching the module attribute is sufficient.
        import vera.codegen
        monkeypatch.setattr(vera.codegen, "execute", fake_execute)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        # Suppression marker present and counts both leading helpers
        assert "suppressed 2 runtime-helper frames" in captured.err, (
            f"Expected suppression marker for 2 collapsed frames; "
            f"got stderr: {captured.err!r}"
        )
        # User frame surfaces at the top of the displayed backtrace
        assert "in main" in captured.err
        # Helper frames collapsed away — should not appear inline
        # (they're counted by the suppression marker, not listed).
        assert "in gc_collect" not in captured.err
        assert "in alloc" not in captured.err

    def test_text_mode_does_not_collapse_when_all_frames_are_builtins(
        self,
        tmp_path: Path,
        capsys: CaptureFixture[str],
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """With no user frames, every helper frame is displayed.

        The collapse logic only fires when at least one user frame
        would remain after suppression — otherwise the user gets an
        empty backtrace and no information.  Sibling regression to
        the test above; pins the "only collapse if a user frame
        remains" guard in cmd_run.
        """
        path = tmp_path / "trivial.vera"
        path.write_text("""\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
""")

        synthetic_frames: list[dict[str, object]] = [
            {
                "func": "gc_collect", "file": "<builtin>",
                "line_start": None, "line_end": None,
                "is_builtin": True,
            },
            {
                "func": "alloc", "file": "<builtin>",
                "line_start": None, "line_end": None,
                "is_builtin": True,
            },
        ]

        from vera.codegen.api import WasmTrapError

        def fake_execute(*args: object, **kwargs: object) -> None:
            raise WasmTrapError(
                "Out-of-bounds memory access",
                kind="out_of_bounds",
                frames=synthetic_frames,
            )

        import vera.codegen
        monkeypatch.setattr(vera.codegen, "execute", fake_execute)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        # No suppression marker — there's nothing left to surface
        assert "suppressed" not in captured.err
        # Both helper frames displayed
        assert "in gc_collect" in captured.err
        assert "in alloc" in captured.err


class TestSourceMapPopulation516:
    """The CompileResult source map is populated for every user fn.

    Lighter-weight than the end-to-end trap tests above — purely
    inspects the ``fn_source_map`` field after compile() to pin the
    contract that codegen registers source locations for top-level
    fns AND for lifted closures.
    """

    @staticmethod
    def _compile(source: str) -> object:
        from vera.codegen import compile as compile_program
        from vera.parser import parse_to_ast
        program = parse_to_ast(source)
        return compile_program(program, source=source)

    def test_top_level_fn_in_source_map(self) -> None:
        result = self._compile("""\
public fn add_one(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0 + 1
}
""")
        assert "add_one" in result.fn_source_map  # type: ignore[attr-defined]
        _file, start, end = result.fn_source_map["add_one"]  # type: ignore[attr-defined]
        assert start == 1
        # Function spans through line 5 inclusive (the closing brace).
        assert end >= 4

    def test_lifted_closure_registered_under_anon_id(self) -> None:
        """Each ``fn(...) { ... }`` lifts to ``$anon_N`` with a source loc.

        The trap-frame resolver looks up ``anon_N`` in the map; if
        registration broke, traps inside closures would fall through
        to ``<unknown>`` and the user would lose the location of the
        actual closure body.
        """
        source = """\
public fn run(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) {
    @Int.0 * 2
  });
  @Array<Int>.0[0]
}
"""
        result = self._compile(source)
        anon_keys = [
            k for k in result.fn_source_map  # type: ignore[attr-defined]
            if k.startswith("anon_")
        ]
        assert anon_keys, (
            "Expected at least one anon_N entry in fn_source_map; got: "
            f"{list(result.fn_source_map)}"  # type: ignore[attr-defined]
        )

        # Validate the registered span actually points at the closure
        # body, not at some surrounding location.  The closure literal
        # `fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }` opens on
        # line 4 of `source` (the `array_map(...)` line) and closes on
        # line 6 (the `})` line).  Anything outside that range would
        # mean we're registering the wrong AST node — e.g. picking up
        # the enclosing `array_map` call instead of the AnonFn itself,
        # which would surface the wrong file:line on a trap inside
        # the closure body.
        anon_loc = result.fn_source_map[anon_keys[0]]  # type: ignore[attr-defined]
        anon_file, anon_start, anon_end = anon_loc
        # File comes from the temp path threaded through compile()'s
        # `source=...` channel; in this test path it's empty (we use
        # parse_to_ast directly), so the codegen falls back to
        # "<unknown>".  Keep that contract pinned so a future
        # refactor that wires file= through doesn't silently change
        # the shape.
        assert anon_file == "<unknown>", (
            f"Expected '<unknown>' file for compile-from-string; got "
            f"{anon_file!r}"
        )
        # Closure body spans lines 4-6 in the source above (1-indexed,
        # counting from the first line which is `public fn run(...)`).
        assert anon_start == 4, (
            f"Expected closure to start at line 4 (the array_map call); "
            f"got {anon_start}"
        )
        assert anon_end == 6, (
            "Expected closure to end at line 6 (the closing brace); "
            f"got {anon_end}"
        )

    def test_no_spurious_entries_for_builtins(self) -> None:
        """Compiler-emitted helpers (alloc, gc_collect) must NOT appear.

        If they did, the resolver would surface them as "user" frames
        with bogus locations.  Our codegen registers source map
        entries only when ``decl.span is not None``, which built-in
        injections lack.
        """
        result = self._compile("""\
public fn make_box(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0
}
""")
        # The synthetic runtime helpers must never be source-mapped.
        for forbidden in ("alloc", "gc_collect", "contract_fail"):
            assert forbidden not in result.fn_source_map, (  # type: ignore[attr-defined]
                f"Built-in {forbidden!r} leaked into fn_source_map"
            )
