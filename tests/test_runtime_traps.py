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
