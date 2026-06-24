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
import re
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from vera.cli import cmd_run
from vera.runtime.traps import WasmTrapError, _classify_trap

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
    """``_classify_trap`` maps a wasmtime trap reason to (kind, description, fix).

    Stage 3 (#516, #547) split the previous (kind, message) tuple
    into a 3-tuple so the description and the Fix paragraph live
    in distinct fields.  The description is a clean trap label;
    the Fix paragraph is canned per-kind text that names the
    likely cause and the recommended remediation.
    """

    def test_contract_violation_takes_precedence(self) -> None:
        # When ``last_violation`` is set, the host import was called and
        # we have the precise contract message. Trap reason is irrelevant.
        kind, description, fix = _classify_trap(
            _FakeTrap("wasm trap: integer divide by zero"),
            ["Precondition violation in foo: @Int.0 > 0"],
        )
        assert kind == "contract_violation"
        assert description == "Precondition violation in foo: @Int.0 > 0"
        # Empty fix — the contract message itself already explains
        # what failed; a generic "fix your contract" paragraph would
        # be patronising and add noise.
        assert fix == ""

    def test_divide_by_zero(self) -> None:
        kind, description, fix = _classify_trap(
            _FakeTrap("wasm trap: integer divide by zero"), []
        )
        assert kind == "divide_by_zero"
        assert "division by zero" in description.lower()
        # Fix paragraph should mention the canonical remediation.
        assert "requires(divisor != 0)" in fix
        assert "Z3" in fix

    def test_out_of_bounds_memory(self) -> None:
        kind, description, fix = _classify_trap(
            _FakeTrap("wasm trap: out of bounds memory access"), []
        )
        assert kind == "out_of_bounds"
        assert "out-of-bounds" in description.lower()
        # Fix paragraph names the two most-likely causes (array
        # indexing, string slicing) and the runtime-helper escape
        # hatch (file an issue if the trap is inside `gc_collect` /
        # `alloc` / etc.).
        assert "array_length" in fix
        assert "string_slice" in fix
        assert "gc_collect" in fix or "compiler bug" in fix

    def test_call_stack_exhausted(self) -> None:
        kind, description, fix = _classify_trap(
            _FakeTrap("wasm trap: call stack exhausted"), []
        )
        assert kind == "stack_exhausted"
        assert "stack" in description.lower()
        # Fix paragraph references #517 (the open TCO issue) so an
        # agent reading the Fix knows this is a known limitation
        # rather than a bug they should report.  When #517 ships,
        # this paragraph should be rewritten to reference
        # `return_call` as a supported feature.
        assert "#517" in fix
        assert "return_call" in fix

    def test_unreachable(self) -> None:
        kind, description, fix = _classify_trap(
            _FakeTrap("wasm trap: wasm `unreachable` instruction executed"),
            [],
        )
        assert kind == "unreachable"
        assert "unreachable" in description.lower()
        # Fix paragraph names the most-likely cause (non-exhaustive
        # match) and the resolution path (add the missing arm).
        assert "match" in fix.lower()

    def test_integer_overflow(self) -> None:
        kind, description, fix = _classify_trap(
            _FakeTrap("wasm trap: integer overflow"), []
        )
        assert kind == "overflow"
        assert "overflow" in description.lower()
        # Fix paragraph names the i64 range and the canonical
        # remediation (precondition guarded by Z3).
        assert "i64" in fix or "2^63" in fix
        assert "requires" in fix

    def test_unknown_trap_surfaces_raw_message(self) -> None:
        kind, description, fix = _classify_trap(
            _FakeTrap("wasm trap: some novel reason we have not classified"),
            [],
        )
        assert kind == "unknown"
        # Raw message preserved so the user still sees something useful.
        assert "novel reason" in description
        # Empty fix — by definition we don't know what to suggest
        # for unrecognised trap reasons.
        assert fix == ""


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
            fix="Add a `requires(divisor != 0)` precondition.",
        )
        assert str(exc) == "Integer division by zero"
        assert exc.stdout == "line 1\nline 2\n"
        assert exc.stderr == "warn\n"
        assert exc.kind == "divide_by_zero"
        assert exc.fix == "Add a `requires(divisor != 0)` precondition."

    def test_defaults(self) -> None:
        exc = WasmTrapError("trap")
        assert exc.stdout == ""
        assert exc.stderr == ""
        assert exc.kind == "unknown"
        assert exc.frames == []
        assert exc.fix == ""


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
        from vera.runtime.traps import _resolve_trap_frames
        src_map = {"divide": ("/tmp/a.vera", 5, 9)}
        exc = self._make_exc(self._frame("divide"))

        frames = _resolve_trap_frames(exc, src_map)

        assert len(frames) == 1
        assert frames[0].func == "divide"
        assert frames[0].file == "/tmp/a.vera"
        assert frames[0].line_start == 5
        assert frames[0].line_end == 9
        assert frames[0].is_builtin is False

    def test_builtin_helpers_tagged_as_builtin(self) -> None:
        """alloc / gc_collect / contract_fail must NOT claim a source.

        A frame inside ``$gc_collect`` carries the WAT name
        ``gc_collect``; the resolver must recognise it as runtime
        infrastructure and tag it accordingly rather than reporting
        a misleading file:line lookup miss as ``<unknown>``.
        """
        from vera.runtime.traps import _resolve_trap_frames
        src_map: dict[str, tuple[str, int, int]] = {}

        for name in ("alloc", "gc_collect", "contract_fail"):
            exc = self._make_exc(self._frame(name))
            frames = _resolve_trap_frames(exc, src_map)
            assert len(frames) == 1
            assert frames[0].func == name
            assert frames[0].file == "<builtin>"
            assert frames[0].line_start is None
            assert frames[0].is_builtin is True, name

    def test_builtin_prefix_matches(self) -> None:
        """exn_* / vera.* / closure_sig_* are also runtime infrastructure."""
        from vera.runtime.traps import _resolve_trap_frames

        for name in ("exn_String", "vera.print", "closure_sig_3"):
            exc = self._make_exc(self._frame(name))
            frames = _resolve_trap_frames(exc, {})
            assert frames[0].is_builtin is True, name

    def test_monomorphized_name_resolves_to_base(self) -> None:
        """`identity$Int` looks up `identity` after the rightmost `$`.

        Generic monomorphization mangles names like
        ``identity$Map_String_Int``; the source map only stores the
        original generic.  The resolver strips at the rightmost ``$``
        and retries.
        """
        from vera.runtime.traps import _resolve_trap_frames
        src_map = {"identity": ("/tmp/m.vera", 3, 6)}
        exc = self._make_exc(self._frame("identity$Int"))

        frames = _resolve_trap_frames(exc, src_map)

        assert frames[0].func == "identity$Int"  # original WAT name
        assert frames[0].file == "/tmp/m.vera"
        assert frames[0].line_start == 3

    def test_unknown_user_function_keeps_frame_with_unknown_loc(
        self,
    ) -> None:
        """A user-named frame not in the map gets ``<unknown>`` not dropped.

        Better to surface the WAT name with no location than to drop
        the frame entirely — the user still benefits from knowing
        which function trapped, and any future source-map gap can be
        diagnosed from the unknown markers.
        """
        from vera.runtime.traps import _resolve_trap_frames
        exc = self._make_exc(self._frame("mystery_helper"))

        frames = _resolve_trap_frames(exc, {})

        assert len(frames) == 1
        assert frames[0].func == "mystery_helper"
        assert frames[0].file == "<unknown>"
        assert frames[0].is_builtin is False

    def test_no_frames_attribute_returns_empty_list(self) -> None:
        """Defensive: a trap-shaped exception with no `frames` returns []."""
        from vera.runtime.traps import _resolve_trap_frames
        # Exception with no frames attribute at all.
        exc = RuntimeError("not a real trap")
        assert _resolve_trap_frames(exc, {}) == []

    def test_prelude_function_tagged_as_builtin(self) -> None:
        """Prelude / inject_prelude functions tag as ``<builtin>``.

        Regression for the CodeRabbit finding on PR #546 round 3:
        prelude functions (``array_map``, ``option_unwrap_or``, ADT
        auto-derived methods, etc.) have no source span (they're
        synthetic AST nodes injected by ``inject_prelude``), so they
        don't end up in ``fn_source_map``.  Pre-fix the resolver
        would fall through to the "not a builtin allowlist match
        either" branch and surface them as ``<unknown>`` user code,
        which:
          (a) lies — the user didn't write `array_map`
          (b) prevents the CLI's suppression-marker collapse from
              firing (only `is_builtin=True` frames get collapsed)

        The fix is a separate ``prelude_fn_names`` set on
        ``CompileResult`` populated by the post-prelude registration
        loop in ``compile_program`` (a FnDecl is identified as
        prelude by *registration position* — i.e. it landed in the
        decl list during ``inject_prelude`` rather than parsing of
        user source — not by ``decl.span`` being None, since
        ``inject_prelude`` calls ``parse_to_ast`` on inline Vera
        source and so its FnDecls do have spans, just synthetic
        ones).  The resolver consults ``prelude_fn_names``
        alongside the runtime-helper allowlist.
        """
        from vera.runtime.traps import _resolve_trap_frames
        prelude_names = {"array_map", "option_unwrap_or"}
        exc = self._make_exc(self._frame("array_map"))

        frames = _resolve_trap_frames(exc, {}, prelude_names)

        assert frames[0].func == "array_map"
        assert frames[0].file == "<builtin>"
        assert frames[0].is_builtin is True

    def test_monomorphized_prelude_tagged_as_builtin(self) -> None:
        """Prelude classification handles monomorphized base names too.

        ``array_map$Int`` should resolve to the same builtin tag as
        ``array_map`` — the rightmost-`$` strip rule applies to the
        prelude check, not just to the source-map lookup.  Without
        this, every monomorphized prelude call (which is most of
        them in practice) would still mis-classify as user code.
        """
        from vera.runtime.traps import _resolve_trap_frames
        prelude_names = {"array_map"}
        exc = self._make_exc(self._frame("array_map$Int"))

        frames = _resolve_trap_frames(exc, {}, prelude_names)

        assert frames[0].func == "array_map$Int"
        assert frames[0].is_builtin is True
        assert frames[0].file == "<builtin>"

    def test_prelude_fn_names_optional_for_backward_compat(self) -> None:
        """Resolver works with prelude_fn_names omitted (defaults None).

        Direct callers of ``_resolve_trap_frames`` (older tests, future
        consumers) shouldn't need to pass an empty set — the parameter
        defaults to ``None`` and the prelude check short-circuits.
        Pins the optional shape so an accidental signature tightening
        breaks loudly.
        """
        from vera.runtime.traps import _resolve_trap_frames
        exc = self._make_exc(self._frame("user_function"))
        # No prelude set passed; user_function is not a known builtin.
        frames = _resolve_trap_frames(exc, {})
        assert frames[0].is_builtin is False
        assert frames[0].file == "<unknown>"

    def test_frames_preserved_in_leaf_first_order(self) -> None:
        """Order matches wasmtime's backtrace (innermost / leaf first).

        Terminology note: "innermost" / "leaf" / "inner-first" all
        mean the same thing — closest to where the trap fired,
        which is the bottom of the call stack and the first frame
        wasmtime emits.  Python tracebacks order the OPPOSITE way
        (outermost / root first); we follow wasmtime / gdb here so
        the human reading the backtrace sees the trap origin first
        and the call chain widening outward.  The previous test
        name said "outermost-first" which was the literal opposite
        of what this asserts (CodeRabbit round 6).
        """
        from vera.runtime.traps import _resolve_trap_frames
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
        assert [f.func for f in frames] == ["inner", "outer"]


# Test fixture for source-backtrace assertions.  The `let` binding
# in `main` is INTENTIONAL — without it, the call to `divide(42, 0)`
# would be in tail position and #517 (TCO, v0.0.126) would emit
# `return_call $divide` instead of `call $divide`, discarding
# `main`'s frame before `divide` traps.  The assertions below want
# both `divide` AND `main` to appear in the resolved backtrace, so
# we keep the call non-tail by binding its result and producing it
# with a separate slot reference.  The trap still fires inside
# `divide`, but `main`'s frame is preserved on the WASM call stack
# and so shows up in `wasmtime.Trap.frames` for the resolver.
_DIVIDE_BY_ZERO_USER_FN = """\
public fn divide(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.1 / @Int.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = divide(42, 0);
  @Int.0
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
        # divide is on lines 1-5, main on 7-12 (the let + trailing
        # expression body shape).  Check at least one of them
        # surfaces with a colon-separated line range.
        assert ":1-5" in captured.err
        assert ":7-12" in captured.err

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

    # `let` is intentional — see the comment on _DIVIDE_BY_ZERO_USER_FN
    # above for the TCO interaction.  `main` calls `positive` in
    # non-tail position so both frames are preserved when the
    # precondition fails inside `positive`.
    _CONTRACT_VIOLATION_PROGRAM = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = positive(0 - 5);
  @Int.0
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
        from vera.runtime.traps import WasmTrapError
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
            funcs = [f.func for f in exc.frames]
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
        from vera.runtime.traps import TrapFrame, WasmTrapError
        synthetic_frames: list[TrapFrame] = [
            TrapFrame(
                func="gc_collect", file="<builtin>",
                line_start=None, line_end=None, is_builtin=True,
            ),
            TrapFrame(
                func="alloc", file="<builtin>",
                line_start=None, line_end=None, is_builtin=True,
            ),
            TrapFrame(
                func="main", file=str(path),
                line_start=1, line_end=3, is_builtin=False,
            ),
        ]

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
        # Ordering pin (CodeRabbit round 6): the "Source backtrace:"
        # header reads before the suppression marker, which reads
        # before the user frames.  The suppression line is metadata
        # about the backtrace below it — should appear under the
        # heading, not above it.
        header_pos = captured.err.find("Source backtrace:")
        suppress_pos = captured.err.find("suppressed 2 runtime-helper")
        main_pos = captured.err.find("in main")
        assert 0 <= header_pos < suppress_pos < main_pos, (
            f"Expected order: Source backtrace: header < suppression "
            f"line < user frame.  Got positions header={header_pos}, "
            f"suppress={suppress_pos}, main={main_pos}.  Stderr was: "
            f"{captured.err!r}"
        )

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

        from vera.runtime.traps import TrapFrame, WasmTrapError
        synthetic_frames: list[TrapFrame] = [
            TrapFrame(
                func="gc_collect", file="<builtin>",
                line_start=None, line_end=None, is_builtin=True,
            ),
            TrapFrame(
                func="alloc", file="<builtin>",
                line_start=None, line_end=None, is_builtin=True,
            ),
        ]

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

    def test_json_mode_preserves_full_frame_chain_including_builtins(
        self,
        tmp_path: Path,
        capsys: CaptureFixture[str],
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """JSON envelope includes the FULL backtrace, not the
        text-mode-collapsed view.

        The CLI's text-mode collapse is a *display* convenience —
        helper frames above the first user code get folded into the
        suppression marker.  But the JSON envelope is a machine-
        readable surface; downstream consumers (telemetry, LSP, agent
        post-processing) need the full unmodified chain so they can
        decide what to display themselves.  Pin that contract: the
        ``frames`` array carries every ``TrapFrame`` the resolver
        produced, including ``is_builtin=True`` helpers, in
        leaf-first order.
        """
        path = tmp_path / "trivial.vera"
        path.write_text("""\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
""")

        # Same synthetic shape as the text-mode collapse test, so a
        # single mock surface exercises both paths.  The wire output
        # of cmd_run text vs cmd_run --json must diverge cleanly:
        # text collapses, JSON preserves.
        from vera.runtime.traps import TrapFrame, WasmTrapError
        synthetic_frames: list[TrapFrame] = [
            TrapFrame(
                func="gc_collect", file="<builtin>",
                line_start=None, line_end=None, is_builtin=True,
            ),
            TrapFrame(
                func="alloc", file="<builtin>",
                line_start=None, line_end=None, is_builtin=True,
            ),
            TrapFrame(
                func="main", file=str(path),
                line_start=1, line_end=3, is_builtin=False,
            ),
        ]

        def fake_execute(*args: object, **kwargs: object) -> None:
            raise WasmTrapError(
                "Out-of-bounds memory access",
                kind="out_of_bounds",
                frames=synthetic_frames,
            )

        import vera.codegen
        monkeypatch.setattr(vera.codegen, "execute", fake_execute)

        rc = cmd_run(str(path), as_json=True)

        assert rc == 1
        captured = capsys.readouterr()
        # JSON-mode invariant — see TestStdoutOnTrap522 / #543.
        assert captured.err == "", (
            "JSON mode must not write to stderr; got: " f"{captured.err!r}"
        )
        envelope = json.loads(captured.out)
        diag = envelope["diagnostics"][0]
        assert diag["trap_kind"] == "out_of_bounds"
        # Full chain present, leaf-first order preserved, helpers
        # tagged is_builtin=True (NOT filtered or rewritten — the
        # text-mode collapse stays out of the JSON path).
        funcs = [f["func"] for f in diag["frames"]]
        assert funcs == ["gc_collect", "alloc", "main"], (
            f"Expected leaf-first chain ['gc_collect','alloc','main'] in "
            f"JSON envelope; got: {funcs}"
        )
        # Built-in tagging round-trips through the JSON serialisation.
        assert diag["frames"][0]["is_builtin"] is True
        assert diag["frames"][0]["file"] == "<builtin>"
        assert diag["frames"][1]["is_builtin"] is True
        assert diag["frames"][1]["file"] == "<builtin>"
        assert diag["frames"][2]["is_builtin"] is False
        assert diag["frames"][2]["file"] == str(path)


# =====================================================================
# #516 Stage 3 (#547) — per-kind Fix paragraphs
# =====================================================================


# `let` keeps the divide call non-tail — see the comment on
# _DIVIDE_BY_ZERO_USER_FN at line ~901 for the TCO interaction
# (#517 / v0.0.126 emits return_call for tail positions, which
# would discard `main`'s frame and shorten the backtrace).
_DIVZERO_FOR_FIX = """\
public fn divide(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.1 / @Int.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = divide(42, 0);
  @Int.0
}
"""


class TestTrapFixParagraphs547:
    """Stage 3: per-kind ``Fix:`` paragraphs surface in CLI + JSON."""

    def test_text_mode_shows_fix_block_after_backtrace(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """Text mode emits a ``Fix:`` block after the source backtrace.

        Order: error message → ``Source backtrace:`` → frames →
        ``Fix:`` → wrapped paragraph.  Pre-Stage-3 the runtime-trap
        surface stopped at the backtrace; the user got "what" and
        "where" but no "what to do about it".  Stage 3 closes the
        gap — runtime traps now match compile-time `Diagnostic`
        outputs which have always carried a Fix paragraph.
        """
        path = tmp_path / "div.vera"
        path.write_text(_DIVZERO_FOR_FIX)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        # Block heading present
        assert "Fix:" in captured.err
        # Canonical content from `_TRAP_FIX_PARAGRAPHS["divide_by_zero"]`
        assert "requires(divisor != 0)" in captured.err
        # Position invariant: Fix: comes after the LAST FRAME, not
        # merely after the "Source backtrace:" header.  Asserting
        # only against the header would miss a regression where
        # the Fix block landed between the header and the frames
        # (e.g. if a future refactor reordered the cli.py print
        # statements).  Frame format is `  in <funcname>  (file:N)`;
        # rfind to locate the last frame line in the stderr capture.
        backtrace_pos = captured.err.find("Source backtrace:")
        last_frame_pos = captured.err.rfind("\n  in ")
        fix_pos = captured.err.find("Fix:")
        assert 0 <= backtrace_pos, (
            f"Source backtrace: header missing from stderr: "
            f"{captured.err!r}"
        )
        assert backtrace_pos < last_frame_pos, (
            f"Expected at least one user frame after Source backtrace: "
            f"header.  backtrace={backtrace_pos}, "
            f"last_frame={last_frame_pos}.  stderr={captured.err!r}"
        )
        assert last_frame_pos < fix_pos, (
            f"Expected Fix: block AFTER the last frame, not between "
            f"the header and the frames.  backtrace={backtrace_pos}, "
            f"last_frame={last_frame_pos}, fix={fix_pos}.  "
            f"stderr={captured.err!r}"
        )

    def test_text_mode_omits_fix_block_for_contract_violation(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """No empty `Fix:` header when the kind has no canned suggestion.

        Contract violations carry their own precise message in the
        description (the contract that failed, with the violating
        function name and slot ref); a generic Fix paragraph would
        be patronising.  ``_TRAP_FIX_PARAGRAPHS["contract_violation"]``
        is the empty string and the CLI suppresses the block when
        ``exc.fix`` is empty.
        """
        source = """\
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
        path = tmp_path / "ctr.vera"
        path.write_text(source)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        # The error description and backtrace surface as usual.
        assert "Precondition violation" in captured.err
        assert "Source backtrace:" in captured.err
        # But there's no empty Fix: block.
        assert "Fix:" not in captured.err

    def test_json_mode_includes_fix_field(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """JSON envelope includes the ``fix`` key on every trap diagnostic.

        Always-present (possibly empty string) so consumers can read
        ``diag["fix"]`` directly without `.get(..., "")` ceremony.
        Same shape stability principle as ``trap_kind`` and
        ``frames``.
        """
        path = tmp_path / "div.vera"
        path.write_text(_DIVZERO_FOR_FIX)

        rc = cmd_run(str(path), as_json=True)

        assert rc == 1
        captured = capsys.readouterr()
        envelope = json.loads(captured.out)
        diag = envelope["diagnostics"][0]
        assert diag["trap_kind"] == "divide_by_zero"
        assert "fix" in diag
        assert isinstance(diag["fix"], str)
        assert "requires(divisor != 0)" in diag["fix"]
        # JSON-mode invariant from #543.
        assert captured.err == ""

    def test_json_mode_includes_fix_field_for_contract_violation(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """JSON ``fix`` field is present-but-empty for contract violations.

        Schema stability matters more than envelope minimalism for a
        structural field — same reasoning as the always-present
        ``frames`` array (CodeRabbit round 5 made that one
        unconditional).  Empty string is the canonical "no
        suggestion" value; consumers that want a non-empty fix
        check `if diag["fix"]:` rather than `.get`.
        """
        source = """\
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
        path = tmp_path / "ctr.vera"
        path.write_text(source)

        rc = cmd_run(str(path), as_json=True)

        assert rc == 1
        captured = capsys.readouterr()
        envelope = json.loads(captured.out)
        diag = envelope["diagnostics"][0]
        assert diag["trap_kind"] == "contract_violation"
        # Field present, value empty (kind has no canned suggestion).
        assert diag["fix"] == ""
        # JSON-mode invariant.
        assert captured.err == ""

    def test_fix_paragraph_table_covers_every_known_kind(self) -> None:
        """Every trap kind in the taxonomy has an entry in ``_TRAP_FIX_PARAGRAPHS``.

        Adding a new ``kind`` to ``_classify_trap`` without also
        adding its Fix paragraph would silently surface ``""`` to
        the user — the test catches the omission immediately.  The
        canonical kind list comes from the ``WasmTrapError``
        docstring; if a future kind is added there, the table must
        gain a row to keep this test passing.
        """
        from vera.runtime.traps import _TRAP_FIX_PARAGRAPHS
        expected_kinds = {
            "contract_violation",
            "divide_by_zero",
            "out_of_bounds",
            "stack_exhausted",
            "unreachable",
            "overflow",
            "unknown",
        }
        assert set(_TRAP_FIX_PARAGRAPHS.keys()) == expected_kinds, (
            f"_TRAP_FIX_PARAGRAPHS keys drifted from canonical kind "
            f"taxonomy.  Expected: {sorted(expected_kinds)}.  "
            f"Got: {sorted(_TRAP_FIX_PARAGRAPHS.keys())}."
        )

    def test_fix_paragraph_wraps_at_76_columns_in_text_mode(
        self, tmp_path: Path, capsys: CaptureFixture[str],
    ) -> None:
        """Text-mode Fix block wraps long paragraphs to ~76 columns.

        Matches the compile-time `Diagnostic` rendering style.  The
        canonical Fix paragraphs in ``_TRAP_FIX_PARAGRAPHS`` are
        single long sentences for editorial flexibility; the CLI
        wraps them at output time so terminals don't show
        runaway-line content.  Each wrapped line carries a leading
        ``"  "`` indent so the block visually nests under ``Fix:``.
        """
        path = tmp_path / "div.vera"
        path.write_text(_DIVZERO_FOR_FIX)

        rc = cmd_run(str(path))

        assert rc == 1
        captured = capsys.readouterr()
        # Find the Fix: block and inspect the lines below it.
        lines = captured.err.splitlines()
        fix_idx = next(
            i for i, ln in enumerate(lines) if ln == "Fix:"
        )
        fix_body_lines = lines[fix_idx + 1:]
        # Skip any blank trailing lines.
        fix_body_lines = [ln for ln in fix_body_lines if ln.strip()]
        # At least one wrapped line of body content.
        assert fix_body_lines, "Fix: block has no body content"
        # Each body line indents with two spaces.
        for ln in fix_body_lines:
            assert ln.startswith("  "), (
                f"Fix-block line missing indent: {ln!r}"
            )
        # No line exceeds 76 chars.  textwrap.fill counts the
        # initial_indent / subsequent_indent strings as part of
        # `width` (verified empirically — width=76 with 2-char
        # indent produces lines of at most 76 chars total, of which
        # 2 are indent and up to 74 are body), so 76 is the strict
        # ceiling for fully-wrapped lines.  Caveat: a single token
        # longer than 74 chars could exceed; the canonical Fix
        # paragraphs in `_TRAP_FIX_PARAGRAPHS` don't contain any
        # such tokens (longest backtick-bounded literal is
        # `requires(divisor != 0)` at 22 chars), so the strict
        # ceiling is achievable today.  Loosen this if a future
        # paragraph adds a longer single-token literal — but flag
        # that as a separate decision rather than letting the
        # ceiling drift silently.
        for ln in fix_body_lines:
            assert len(ln) <= 76, (
                f"Fix-block line too long ({len(ln)} chars): {ln!r}"
            )


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

    def test_prelude_functions_registered_as_builtins(self) -> None:
        """Prelude / inject_prelude functions land in ``prelude_fn_names``.

        Companion to ``test_prelude_function_tagged_as_builtin`` in
        ``TestResolveTrapFrames516``: that one tests the resolver
        against a synthetic prelude name; this one verifies that a
        real compile actually populates the set with the names the
        resolver expects.  Together they pin both ends of the
        plumbing — the codegen registers, the resolver consults.

        Note: ``array_map`` is NOT a prelude FnDecl — it's a WASM
        translator built-in (recognised directly by `_translate_call`
        in `calls_arrays.py`, no AST body needed).  The actual prelude
        FnDecls are the option/result combinators in `vera/prelude.py`,
        which `inject_prelude` parses from inline Vera source and
        prepends to `program.declarations`.
        """
        # `option_unwrap_or` is one of the canonical prelude combinators;
        # any program that uses it forces inject_prelude to add the full
        # set of option/result combinators (they're added unconditionally
        # when their detection names appear in source).
        result = self._compile("""\
public fn run(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(@Option<Int>.0, 0)
}
""")
        names = result.prelude_fn_names  # type: ignore[attr-defined]
        # option_unwrap_or is the canonical user-facing prelude
        # combinator; if it doesn't land here the whole prelude-as-
        # builtin classification collapses (and traps inside it would
        # surface bogus file:line coordinates pointing into the
        # prelude's *embedded* source string, not the user's file).
        assert "option_unwrap_or" in names, (
            f"Expected 'option_unwrap_or' in prelude_fn_names; got: "
            f"{sorted(names)}"
        )
        # No spurious user-fn entries — the user's `run` function has
        # a real span pointing at user source, so it goes in
        # fn_source_map, not here.
        assert "run" not in names
        # The user's run IS in fn_source_map with valid coordinates.
        assert "run" in result.fn_source_map  # type: ignore[attr-defined]
        # Conversely, prelude functions must NOT be in fn_source_map
        # (they were moved out by the post-prelude registration loop).
        assert "option_unwrap_or" not in result.fn_source_map, (  # type: ignore[attr-defined]
            "option_unwrap_or leaked into fn_source_map with bogus "
            "coordinates from the prelude's embedded source string"
        )

    def test_no_spurious_entries_for_builtins(self) -> None:
        """Compiler-emitted helpers (alloc, gc_collect) must NOT appear.

        If they did, the resolver would surface them as "user" frames
        with bogus locations.  These WASM helpers (`$alloc`,
        `$gc_collect`, `$contract_fail`, `$exn_*`, `$vera.*`) are
        emitted directly into WAT by the assembly module — they
        never go through `_register_fn` at all, which is why no
        entry exists.  Prelude-injected functions (a different class
        of "built-in") DO go through `_register_fn` and are then
        moved out of `_fn_source_map` into `_prelude_fn_names` by
        the post-`inject_prelude` registration loop in
        `compile_program`; that path is covered by
        ``test_prelude_functions_registered_as_builtins`` above.
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


# =====================================================================
# #589 — host_print never crashes Python on invalid UTF-8
# =====================================================================


class TestHostPrintInvalidUtf8589:
    """#589 — ``host_print`` (and siblings) decode with ``errors="replace"``
    so an upstream codegen bug producing a corrupt String (ptr, len) pair
    never escapes as a raw Python ``UnicodeDecodeError`` through wasmtime's
    trampoline.

    Triggered in the wild by the captured-Array-indexing-in-closure bug
    (#588) producing corrupt String pointers in a Conway's Game of Life
    program; the user saw a 30+ line Python traceback ending in
    ``UnicodeDecodeError: 'utf-8' codec can't decode byte 0xc1`` instead
    of a Vera-native runtime trap.  A user-level program should never
    produce a Python traceback regardless of what the program does — this
    is the WasmTrapError contract from #516 / #522 / #547 applied to the
    UTF-8-decode paths.

    Tests here are primarily structural assertions on the source: each
    affected decode site (four in ``vera/codegen/api.py``, one in
    ``vera/wasm/markdown.py``) must use ``errors="replace"``.  These
    catch a regression that drops the flag from any of the production
    sites.  Plus one end-to-end test using a synthetic WAT module that
    imports ``vera.print`` and calls it with raw invalid UTF-8 bytes —
    that test pins the wasmtime-trampoline contract (a Python
    ``UnicodeDecodeError`` escapes a host import as a "python exception"
    cause iff the host decode is strict).  It mirrors the production
    code rather than wiring up the real ``host_print`` so the production
    regression is caught by the structural tests, not this one.
    """

    def _file_body_after(
        self, file_path: str, marker: str, *, span: int = 1500,
    ) -> str:
        from pathlib import Path
        repo_root = Path(__file__).parent.parent
        src = (repo_root / file_path).read_text()
        idx = src.index(marker)
        return src[idx:idx + span]

    def _api_body_after(self, marker: str, *, span: int = 1500) -> str:
        return self._file_body_after("vera/codegen/api.py", marker, span=span)

    def test_host_print_uses_errors_replace(self) -> None:
        """host_print decodes with errors='replace' so invalid UTF-8
        bytes from a corrupt String surface as U+FFFD instead of a
        raw Python exception escaping through wasmtime's trampoline.

        Anchors on ``def host_print(`` rather than a nearby comment so
        the test isn't fragile to comment refactoring.
        """
        body = self._api_body_after("def host_print(")
        assert 'data.decode("utf-8", errors="replace")' in body, (
            "host_print must decode with errors='replace' so invalid "
            "UTF-8 bytes don't escape as a Python UnicodeDecodeError "
            "through wasmtime's trampoline (#589)."
        )

    def test_host_stderr_uses_errors_replace(self) -> None:
        """host_stderr decodes with errors='replace' for the same
        reason as host_print — IO.stderr must never crash Python.
        """
        body = self._api_body_after("def host_stderr(")
        assert 'data.decode("utf-8", errors="replace")' in body, (
            "host_stderr must decode with errors='replace' (#589)."
        )

    def test_host_contract_fail_uses_errors_replace(self) -> None:
        """host_contract_fail decodes with errors='replace' so a corrupt
        contract-violation message itself doesn't mask the underlying
        violation with a Python traceback.
        """
        body = self._api_body_after("def host_contract_fail(")
        assert 'data.decode("utf-8", errors="replace")' in body, (
            "host_contract_fail must decode with errors='replace' (#589)."
        )

    def test_read_wasm_string_uses_errors_replace(self) -> None:
        """_read_wasm_string (used by read_file path / get_env / etc.)
        decodes with errors='replace' so any corrupt-bytes input surfaces
        as U+FFFD downstream rather than crashing Python.

        Asserts on the literal `.decode("utf-8", errors="replace")`
        call form rather than just the substring `errors="replace"` —
        the latter is also present in the function's docstring (where
        the `errors="replace"` strategy is explained in prose), so a
        substring check would pass spuriously even if the actual call
        was reverted to strict-mode `.decode("utf-8")`.
        """
        body = self._file_body_after(
            "vera/runtime/heap.py",
            '"""Read a UTF-8 string from WASM memory.',
        )
        assert '.decode("utf-8", errors="replace")' in body, (
            "_read_wasm_string must decode with errors='replace' (#589)."
        )

    def test_markdown_read_string_uses_errors_replace(self) -> None:
        """vera/wasm/markdown.py::_read_string is the fifth UTF-8 decode
        site — invoked from host_md_render / host_md_has_heading /
        host_md_extract_text / host_md_count_blocks for every Markdown
        host import.  Same failure mode as the four api.py sites: a
        corrupt String passed to md_render would have escaped as a
        Python UnicodeDecodeError through wasmtime's trampoline.  Pins
        the fix at the markdown.py site too (#589).

        Asserts on the literal `.decode("utf-8", errors="replace")`
        call form rather than just the substring `errors="replace"`
        for the same reason as the `_read_wasm_string` test above —
        the docstring explains the strategy in prose so a substring
        check would spuriously pass even if the call was reverted.
        """
        body = self._file_body_after(
            "vera/wasm/markdown.py",
            "def _read_string(",
        )
        assert '.decode("utf-8", errors="replace")' in body, (
            "vera/wasm/markdown.py::_read_string must decode with "
            "errors='replace' for parity with the four api.py sites (#589)."
        )

    def test_extract_string_uses_errors_replace(self) -> None:
        """The String-return decoder in execute() (api.py around
        line 3260) was previously try/except → pointer fallback, which
        silently mutated the return type from str to int when bytes
        weren't valid UTF-8.  That fallback was a worse silent failure
        than visible U+FFFD chars (downstream CLI printer printed an
        integer where a string was expected).  Post-fix: errors='replace'
        keeps the value typed as str (#589).
        """
        body = self._api_body_after("# Extract return value", span=2200)
        assert 'raw_bytes.decode("utf-8", errors="replace")' in body, (
            "_extract_string path must use errors='replace' instead of "
            "the old try/except → pointer fallback (#589 — silently "
            "mutating str → int is worse than U+FFFD)."
        )

    def test_invalid_utf8_through_host_print_does_not_raise(self) -> None:
        """End-to-end: synthesise a wasmtime instance that imports vera.print
        and call it with raw invalid UTF-8 bytes.  Pre-fix, the
        UnicodeDecodeError escaped wasmtime's trampoline as a "python
        exception" cause and the user's CLI saw a Python traceback.
        Post-fix, the host import returns cleanly (or wraps as a
        WasmTrapError); the test asserts no Python exception escapes.
        """
        import wasmtime

        # Bytes that are invalid UTF-8 (0xc1 is a never-valid lead byte
        # — the same byte value the user's Conway's Life crash report
        # showed in position 123).
        invalid_bytes = b"hello \xc1 world"

        # Minimal WAT module that imports vera.print, has linear memory
        # populated with our test bytes, and exports a `run` function
        # calling vera.print(0, len(invalid_bytes)).
        # WAT data-section escape syntax is `\HH` per byte; in a Python
        # string that's a single literal backslash followed by two hex
        # digits.
        wat_bytes = "".join(f"\\{b:02x}" for b in invalid_bytes)
        wat = (
            "(module\n"
            '  (import "vera" "print" (func $print (param i32 i32)))\n'
            '  (memory (export "memory") 1)\n'
            f'  (data (i32.const 0) "{wat_bytes}")\n'
            '  (func (export "run")\n'
            "    i32.const 0\n"
            f"    i32.const {len(invalid_bytes)}\n"
            "    call $print\n"
            "  )\n"
            ")\n"
        )

        # Build a host_print closure mirroring the production one.
        decoded: list[str] = []

        def host_print(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> None:
            memory = caller["memory"]
            assert isinstance(memory, wasmtime.Memory)
            buf = memory.data_ptr(caller)
            data = bytes(buf[ptr:ptr + length])
            # The behaviour under test: must use errors="replace" so a
            # corrupt String never raises a UnicodeDecodeError that
            # escapes wasmtime's trampoline.
            decoded.append(data.decode("utf-8", errors="replace"))

        engine = wasmtime.Engine()
        store = wasmtime.Store(engine)
        linker = wasmtime.Linker(engine)
        print_type = wasmtime.FuncType(
            [wasmtime.ValType.i32(), wasmtime.ValType.i32()], [],
        )
        linker.define_func(
            "vera", "print", print_type, host_print, access_caller=True,
        )

        module = wasmtime.Module(engine, wat)
        instance = linker.instantiate(store, module)
        run_export = instance.exports(store)["run"]
        assert isinstance(run_export, wasmtime.Func)

        # The actual test: this call must not raise UnicodeDecodeError.
        run_export(store)

        # Decoded result has the U+FFFD replacement char at the bad-byte
        # position, with valid bytes preserved on either side.
        assert len(decoded) == 1
        assert "hello " in decoded[0]
        assert " world" in decoded[0]
        assert "�" in decoded[0], (
            "Expected U+FFFD replacement char where 0xc1 was; got "
            f"{decoded[0]!r}"
        )


# =====================================================================
# #591 — HTTP / Inference network-response UTF-8 decode hygiene
# =====================================================================


class TestNetworkResponseUtf8Hygiene591:
    """#591 — network-response decode sites in ``vera/codegen/api.py``
    must not leak Python ``UnicodeDecodeError`` text into Vera-level
    ``Result::Err`` strings.

    The three sites are siblings of the WASM-memory-decode sites in
    #589 (covered by ``TestHostPrintInvalidUtf8589`` above) but with
    different ergonomics: the bytes here come from a *remote* server,
    not a corrupt-program codegen bug.  A failure here surfaces as a
    Vera-level ``Result::Err`` (via the ``try/except Exception``
    wrappers) rather than a wasmtime-trampoline-wrapped Python
    crash — so the practical impact is "bad error message" rather
    than "Python traceback escapes".  Two strategies in use:

    - ``Http.get`` / ``Http.post`` — ``errors="replace"`` so the user
      gets the response body with U+FFFD substitutions for bad bytes.
      Their intent is "fetch this URL"; preserving data beats
      preserving the (rare) signal that bytes were non-UTF-8.

    - ``Inference.complete`` — explicit ``UnicodeDecodeError`` catch
      that raises a Vera-shaped ``RuntimeError`` ("provider returned
      a response body that is not valid UTF-8 (invalid byte at
      position N)").  Non-UTF-8 from an LLM API is genuinely broken;
      we want loud failure with a Vera-native message, not the
      ``codec can't decode byte 0x...`` Python form.

    Structural assertions on the source: the same shape as #589's
    coverage above, anchored on each function's definition.
    """

    def _file_body_after(
        self, relpath: str, marker: str, *, span: int = 1500,
    ) -> str:
        from pathlib import Path
        repo_root = Path(__file__).parent.parent
        src = (repo_root / relpath).read_text(encoding="utf-8")
        idx = src.index(marker)
        return src[idx:idx + span]

    def test_http_get_uses_errors_replace(self) -> None:
        """``host_http_get`` decodes the response body with
        ``errors="replace"`` so a remote server's invalid UTF-8
        produces U+FFFD substitutions in the OK-branch string rather
        than a ``UnicodeDecodeError`` message leaking into the
        Err-branch string.
        """
        body = self._file_body_after(
            "vera/runtime/http.py", "def host_http_get(", span=2500,
        )
        assert 'resp.read().decode("utf-8", errors="replace")' in body, (
            "host_http_get must decode the response body with "
            "errors='replace' so non-UTF-8 bytes from a misconfigured "
            "remote server don't surface as Python error noise in "
            "the Result::Err string (#591)."
        )

    def test_http_post_uses_errors_replace(self) -> None:
        """``host_http_post`` decodes the response body with
        ``errors="replace"`` for the same reason as ``host_http_get``.

        Asserts on the **contiguous decode expression** rather than
        the bare substring ``errors="replace"`` (which also appears
        in the explanatory comment above the call site).  Removing
        ``errors="replace"`` from the actual decode call while
        leaving the comment intact must fail this assertion.
        CodeRabbit-flagged pre-fix vulnerability on PR #649.
        """
        body = self._file_body_after(
            "vera/runtime/http.py", "def host_http_post(", span=2500,
        )
        # Use regex with DOTALL-like matching so the multi-line
        # form (decode call wrapped across two source lines) still
        # matches.  The pattern requires `errors="replace"` to be
        # part of the same `resp.read().decode(...)` expression —
        # whitespace and the `"utf-8"` argument between
        # ``decode(`` and ``errors=`` are allowed, but no closing
        # paren can appear before ``errors="replace"``.
        m = re.search(
            r'resp\.read\(\)\.decode\([^)]*errors="replace"',
            body,
        )
        assert m, (
            "host_http_post must decode the response body with "
            "errors='replace' as part of the same resp.read().decode(...) "
            "expression — a bare `errors=\"replace\"` substring in a "
            "comment does not satisfy this (#591)."
        )

    def test_inference_complete_catches_unicode_decode_error(self) -> None:
        """``Inference.complete``'s network-response decode site
        catches ``UnicodeDecodeError`` explicitly and raises a
        ``RuntimeError`` with a Vera-shaped message, so the Err
        string the user sees doesn't contain Python-internals text
        like ``'utf-8' codec can't decode byte 0x...`` (#591).

        Anchored on ``_call_inference_provider`` (the private helper
        that performs the urlopen + decode), not the public
        ``host_inference_complete`` which only handles the
        provider-config validation around the call.

        Asserts on the **contiguous except-then-raise expression**
        rather than the bare substrings ``"except UnicodeDecodeError"``
        and ``"not valid UTF-8"`` (which could in principle appear
        independently in comments or unrelated code paths).  The
        regex requires the catch + raise + message to form one
        coherent handler block.  CodeRabbit-flagged hardening on
        PR #649.
        """
        body = self._file_body_after(
            "vera/runtime/inference.py",
            "def _call_inference_provider(", span=3000,
        )
        m = re.search(
            r"except\s+UnicodeDecodeError[^\n]*?:\s*\n"
            r"(?:[^\n]*\n){0,10}?"  # up to 10 lines until raise
            r"\s*raise\s+RuntimeError\(",
            body,
        )
        assert m, (
            "_call_inference_provider must catch UnicodeDecodeError "
            "and re-raise as a RuntimeError in the same handler "
            "block (#591).  Both substrings must appear in a "
            "contiguous except/raise structure — a stray "
            "`except UnicodeDecodeError` comment does not satisfy."
        )
        # The Vera-shaped error message must include "not valid UTF-8"
        # within the raise call's argument string(s).  Python permits
        # implicit adjacent-literal concatenation, so the production
        # code splits the message across multiple ``f"..."`` lines for
        # readability; the phrase can appear in any one of them.
        # Match `raise RuntimeError(` followed by `"..."` (possibly
        # `f"..."`, possibly preceded by other `f"..."` adjacent
        # literals, possibly spanning multiple lines), as long as the
        # phrase lands inside a string-literal token before the
        # matching `)`.  DOTALL handles the multi-line case; the
        # bounded `.{0,400}?` keeps the regex non-greedy enough to
        # stop at the close of the raise.
        m_msg = re.search(
            r'raise\s+RuntimeError\(.{0,400}?"[^"]*not valid UTF-8',
            body,
            flags=re.DOTALL,
        )
        assert m_msg, (
            "The Vera-shaped error message for the UnicodeDecodeError "
            "case must include 'not valid UTF-8' as part of the "
            "raise's string argument (#591) — a bare substring in a "
            "comment does not satisfy."
        )


# =====================================================================
# IO.sleep + Ctrl-C never escapes as a Python traceback
# =====================================================================


class TestHostSleepKeyboardInterrupt:
    """Ctrl-C arriving during ``IO.sleep`` (or ``IO.read_char``) must
    surface as a clean process exit (exit code 130, conventional
    SIGINT) rather than a raw Python ``KeyboardInterrupt`` traceback
    escaping through wasmtime's trampoline.

    Originally discovered (#595) when a user Ctrl-C'd a Conway's Life
    animation that uses ``IO.sleep(120)`` between frames: with
    ``wasmtime-py < 45`` the trampoline caught only ``Exception``, so a
    raw ``KeyboardInterrupt`` escaped into Rust with an undefined ABI
    return value and aborted with a libmalloc SIGABRT.  Vera bridged
    that with four per-host-import ``except KeyboardInterrupt: raise
    _VeraExit(130)`` guards (one in ``host_sleep``, three across
    ``host_read_char``'s platform branches) that laundered the
    interrupt into an ``Exception`` the buggy trampoline could catch.

    #599: ``wasmtime-py >= 45.0.0`` catches ``BaseException`
    (bytecodealliance/wasmtime-py#337), so the raw ``KeyboardInterrupt``
    now unwinds the wasm call safely and re-raises in Python at the
    ``func(store, ...)`` call site.  The four guards were removed and
    replaced by a single ``except KeyboardInterrupt`` handler in
    ``execute()`` that maps it to ``ExecuteResult(exit_code=130)`` —
    one source of truth instead of four.
    """

    def test_keyboard_interrupt_handled_centrally_not_per_import(
        self,
    ) -> None:
        """Structural assertion for the #599 relocation: the per-import
        ``_VeraExit(130)`` guards are gone and the single centralized
        ``except KeyboardInterrupt`` handler lives at the ``execute()``
        call site.  Survives refactors that move host-import bodies into
        helpers, as long as the SIGINT mapping stays centralized.
        """
        from pathlib import Path
        api_src = (
            Path(__file__).parent.parent / "vera/codegen/api.py"
        ).read_text(encoding="utf-8")

        # The four per-host-import launder guards must be gone.  Their
        # signature was the `raise _VeraExit(130)` statement in
        # executable code.  Strip full-line comments first so the
        # surviving history-describing mentions (which legitimately
        # quote the old `raise _VeraExit(130)` form) don't trip the
        # assertion — only an actual `raise` statement should fail it.
        code_only = "\n".join(
            ln for ln in api_src.splitlines()
            if not ln.lstrip().startswith("#")
        )
        assert "raise _VeraExit(130)" not in code_only, (
            "The per-host-import `raise _VeraExit(130)` guards must be "
            "removed (#599) — KeyboardInterrupt now propagates to the "
            "centralized handler in execute() instead of being "
            "laundered into _VeraExit at each blocking call."
        )

        # host_sleep must no longer wrap time.sleep in a try/except.
        sleep_idx = api_src.index("def host_sleep(")
        sleep_body = api_src[sleep_idx:sleep_idx + 600]
        assert "except KeyboardInterrupt" not in sleep_body, (
            "host_sleep must let KeyboardInterrupt propagate (#599); "
            "the per-import guard is replaced by execute()'s handler."
        )

        # execute() must carry the single centralized handler that maps
        # KeyboardInterrupt -> exit_code=130.
        exec_idx = api_src.index("def execute(")
        exec_body = api_src[exec_idx:]
        assert "except KeyboardInterrupt:" in exec_body, (
            "execute() must catch KeyboardInterrupt at the wasm-call "
            "site so a Ctrl-C in any host import exits cleanly (#599)."
        )
        # The handler maps to exit_code=130 (assert proximity of the
        # handler to an exit_code=130 ExecuteResult field).
        ki_idx = exec_body.index("except KeyboardInterrupt:")
        # The ExecuteResult(exit_code=130) return sits after the
        # handler's (long) rationale comment.  A forward window is
        # safe here: the only `exit_code=130` literal in the whole
        # file is this handler (the IO.exit handler above uses
        # `exit_code=exit_exc.code`, not the literal 130).
        assert "exit_code=130" in exec_body[ki_idx:ki_idx + 2500], (
            "execute()'s KeyboardInterrupt handler must return "
            "ExecuteResult(exit_code=130) (conventional SIGINT code)."
        )

    def test_host_sleep_keyboard_interrupt_end_to_end(self) -> None:
        """End-to-end behavioural test: compile a real Vera program
        that calls ``IO.sleep(...)``, monkey-patch ``time.sleep`` to
        raise ``KeyboardInterrupt``, run via the production
        ``execute()`` entrypoint, and assert the result surfaces as
        ``ExecuteResult.exit_code == 130`` — not a raw Python
        ``KeyboardInterrupt`` escaping wasmtime's trampoline.

        Exercises the full import/trampoline path: WAT compile →
        wasmtime instance → host_sleep callback (the production
        closure, not a local mirror) → ctypes/ffi → KeyboardInterrupt
        raised inside ``time.sleep`` → wasmtime-py 45's
        ``except BaseException`` trampoline unwinds the wasm call and
        re-raises → caught by ``execute()``'s single
        ``except KeyboardInterrupt`` handler → returned as
        ``ExecuteResult(exit_code=130)``.

        This is the real behavioural contract for #599: it passed both
        before (per-import ``_VeraExit(130)`` guard) and after (central
        handler + ``wasmtime>=45``) the relocation, which is exactly
        why the guard could be removed without changing UX.

        Replaced an earlier local-helper test that mirrored
        ``host_sleep`` in test code and asserted Python's stdlib
        behaviour rather than the production path.  CodeRabbit on
        PR #594 correctly flagged the local-helper form as the same
        "test-the-test" gap that #589's structural-only e2e test had
        — fixing this one symmetrically.
        """
        import time as _time
        from unittest.mock import patch

        from vera.codegen import compile as compile_program, execute
        from vera.parser import parse_to_ast

        # Vera program that calls IO.sleep with a value the host will
        # see as positive (so the guard branch fires).  IO.print
        # before the sleep gives us a tee point in stdout to
        # observe the program reached the sleep call.
        source = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("before sleep");
  IO.sleep(120);
  IO.print("after sleep")
}
"""
        program = parse_to_ast(source)
        result = compile_program(program, source=source)
        assert result.ok, (
            f"compile failed: "
            f"{[d.description for d in result.diagnostics]}"
        )

        # Patch time.sleep to raise KeyboardInterrupt unconditionally
        # — simulates the user pressing Ctrl-C the moment IO.sleep
        # enters the host import.
        with patch.object(_time, "sleep", side_effect=KeyboardInterrupt):
            try:
                exec_result = execute(result)
            except KeyboardInterrupt:  # pragma: no cover
                raise AssertionError(
                    "KeyboardInterrupt escaped execute() — the "
                    "centralized handler must map it to exit_code=130 "
                    "so the wasmtime trampoline doesn't surface a raw "
                    "Python traceback (#594 / #595 / #599)."
                ) from None

        assert exec_result.exit_code == 130, (
            f"expected exit_code=130 (SIGINT), got {exec_result.exit_code}"
        )
        # The IO.print("before sleep") executed before the sleep was
        # interrupted, so the captured stdout should contain it (with
        # output preserved across the trap, per the #522 contract).
        assert "before sleep" in exec_result.stdout, (
            "Pre-sleep IO.print output should be preserved in "
            "ExecuteResult.stdout even when the program exits via "
            "_VeraExit(130) (#522 trap-preservation contract)."
        )
        # The IO.print("after sleep") should NOT have executed.
        assert "after sleep" not in exec_result.stdout, (
            "Post-sleep IO.print should not have run; KeyboardInterrupt "
            "during sleep must propagate to the exit-130 handler without "
            "letting the program continue."
        )

    def test_host_read_char_keyboard_interrupt_end_to_end(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Sibling of the IO.sleep e2e test for the second host import
        that blocks on real input: ``IO.read_char``.  #599 removed three
        per-platform ``_VeraExit(130)`` guards from ``host_read_char``
        (Unix non-TTY, Unix TTY cbreak, Windows getwch); this test pins
        that a Ctrl-C during the blocking read still exits cleanly with
        code 130 via the centralized ``execute()`` handler.

        Exercises the Unix non-TTY branch (``sys.stdin.read(1)``), which
        is the cross-platform-reachable path: a fake stdin whose
        ``read`` raises ``KeyboardInterrupt`` plus ``os.isatty`` forced
        False routes execution through that branch on any OS.  No
        ``stdin=`` is passed to ``execute()`` so the StringIO test
        fixture does not short-circuit the real-stdin path.
        """
        import os as _os
        import sys as _sys

        from vera.codegen import compile as compile_program, execute
        from vera.parser import parse_to_ast

        source = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("before read");
  match IO.read_char(()) {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.stderr(@String.0)
  }
}
"""
        program = parse_to_ast(source)
        result = compile_program(program, source=source)
        assert result.ok, (
            f"compile failed: "
            f"{[d.description for d in result.diagnostics]}"
        )

        class _KIStdin:
            """Minimal stdin stand-in: a real fileno (so the fd resolve
            succeeds) whose ``read`` raises KeyboardInterrupt — simulates
            Ctrl-C the instant ``IO.read_char`` blocks on input."""

            def fileno(self) -> int:
                return 0

            def read(self, _n: int = -1) -> str:
                raise KeyboardInterrupt

        # Force the non-TTY branch (`sys.stdin.read(1)`) on every OS and
        # feed it the interrupt-raising stdin.
        monkeypatch.setattr(_os, "isatty", lambda _fd: False)
        monkeypatch.setattr(_sys, "stdin", _KIStdin())

        try:
            exec_result = execute(result)
        except KeyboardInterrupt:  # pragma: no cover
            raise AssertionError(
                "KeyboardInterrupt escaped execute() during "
                "IO.read_char — the centralized handler must map it to "
                "exit_code=130 (#599)."
            ) from None

        assert exec_result.exit_code == 130, (
            f"expected exit_code=130 (SIGINT) from a Ctrl-C during "
            f"IO.read_char, got {exec_result.exit_code}"
        )
        assert "before read" in exec_result.stdout, (
            "Pre-read IO.print output should be preserved in stdout "
            "even when the program exits via the SIGINT handler."
        )


class TestRuntimePackageImportHygiene421:
    """#421: every `vera.runtime` submodule must import standalone.

    A cold `import vera.runtime.<x>` with no prior `vera.codegen` import must
    not raise -- the decomposition's point is to make the runtime families
    addressable as modules.  Regression for the
    `heap.py -> codegen.memory -> codegen/__init__ -> api -> runtime.decimal
    -> heap` cycle that surfaced when `_validate_wrap_handle` (a runtime heap
    concern) was parked in the compile-time `codegen/memory.py`: cold import
    re-entered a partially-initialised `heap` for `_WRAP_KIND_DECIMAL` and
    raised ImportError.  Each module is imported in a FRESH interpreter so a
    warm `sys.modules` cache cannot mask the cycle.
    """

    def test_all_runtime_submodules_cold_importable(self) -> None:
        import subprocess
        import sys

        modules = [
            "heap", "collections", "traps", "random", "math", "md", "json",
            "regex", "html", "map", "set", "decimal", "http", "inference",
            "state",
        ]
        for mod in modules:
            result = subprocess.run(
                [sys.executable, "-c", f"import vera.runtime.{mod}"],
                capture_output=True,
                text=True,
            )
            assert result.returncode == 0, (
                f"cold `import vera.runtime.{mod}` failed (circular import "
                f"via vera.codegen?):\n{result.stderr}"
            )
