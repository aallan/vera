"""Characterization harness for ``execute()`` — the #421 decomposition gate.

``execute()`` (`vera/codegen/api.py`) is the single highest-risk
decomposition target in the codebase: a ~3,400-line body with 150+
nested host-binding closures, slated to be split into a
``vera/runtime/`` package one host-binding family per PR (#421).  This
module pins its **observable contract** in one place so that every
extraction PR has a single green gate to keep — a reviewer can read
this file top-to-bottom and know that if it stays green, the externally
visible behaviour of ``execute()`` was preserved.

The contract has three *asymmetric* completion modes:

* **Normal return** — returns ``ExecuteResult(value=…, exit_code=None)``.
* **WASM trap** — does **not** return; it *raises* ``WasmTrapError``
  (carrying ``stdout`` / ``stderr`` / ``kind`` / ``frames`` / ``fix``).
  Pinning this raise-not-return asymmetry is the most important thing
  this harness does: it is the behaviour most likely to be silently
  broken when the closures move into a package.
* **Interrupt / exit** — returns ``ExecuteResult(value=None,
  exit_code=<n>)``; ``IO.exit(n)`` → ``n``, Ctrl-C → ``130``; stdout /
  stderr / state captured before the exit are preserved.

Crossed with the five ``ExecuteResult`` fields the issue scopes —
``value`` (int / float / str / heap-pointer / None), ``stdout``,
``state``, ``exit_code``, ``stderr`` — plus the positional-constructor
compatibility shape and ``capture_stderr`` True-vs-default.

Reuse, not duplication: many of these cells were already exercised
*indirectly* by feature tests scattered across the ``test_codegen_*.py`` suite and
``test_runtime_traps.py``.  Where so, the fixture is reused verbatim and
the overlap is named in a ``# overlaps`` comment — but each cell here
adds the *discriminating* assertion the scattered tests lacked (e.g.
``value is None`` on ``IO.exit``, the declared field order, the
str-decode-vs-array-pointer asymmetry pinned side by side).  Out of
scope: ``host_store_sizes`` (#573) and ``peak_heap_bytes`` (#706),
already pinned by the GC-reclamation suite in ``test_codegen_gc_reclamation.py``.

Every assertion is chosen to be *discriminating*: it would change if the
field's own code path broke.  The companion mutation sweep (#734 / #387 —
9 mutations) confirmed each test flips RED when its target return path is
deliberately broken, so none is green-for-the-wrong-reason.
"""

from __future__ import annotations

import time as _time
from dataclasses import fields
from unittest.mock import patch

import pytest

from vera.codegen import CompileResult, compile as compile_program, execute
from vera.codegen.api import ExecuteResult, WasmTrapError
from vera.parser import parse_to_ast

# =====================================================================
# Helper
# =====================================================================


def _compile(source: str) -> CompileResult:
    """Parse + compile a Vera source string, asserting no compile errors.

    Mirrors the ``parse_to_ast`` → ``compile`` seam used by
    ``tests/test_runtime_traps.py`` (no temp file, Windows-portable).
    """
    program = parse_to_ast(source)
    result = compile_program(program, source=source)
    assert result.ok, (
        f"compile failed: {[d.description for d in result.diagnostics]}"
    )
    return result


# Proven runtime-trap fixtures, copied verbatim from
# ``tests/test_runtime_traps.py`` so this harness stays self-contained
# (a #421 gate should not couple to another test module's internals).

# overlaps test_runtime_traps.py::_DIVZERO_WITH_PRINTS — a literal
# ``42 / 0`` traps at runtime (codegen emits the divide; execute() does
# not verify, so #680's static E526 never fires here).  The four prints
# give a stdout tee-point to prove output-before-trap is preserved.
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

# overlaps test_runtime_traps.py::_PRECONDITION_FAIL — calling
# ``positive`` with 0 fires the compiled runtime precondition guard.
_PRECONDITION_FAIL = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
"""

# An opaque array index that is out of bounds at runtime.  Codegen
# lowers an OOB index to a WASM ``unreachable``
# (test_codegen_arrays.py::test_array_wat_has_bounds_check); the index is a param
# so #680 routes it to honest Tier-3 at verify, and execute() (no verify)
# just traps at runtime.  The array is let-bound before indexing (the
# proven shape in test_array_wat_has_bounds_check) — a bare index on an
# array *literal* does not register an export.
_ARRAY_INDEX_OOB = """\
public fn idx(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[@Int.0]
}
"""


# =====================================================================
# value — normal-return shapes (int / float / str / heap-ptr / None)
# =====================================================================


class TestExecuteValueField734:
    """``ExecuteResult.value`` carries the right Python type per return shape."""

    def test_int_return(self) -> None:
        """An @Int return surfaces as a Python int."""
        # overlaps test_codegen_expressions.py::TestIntLit — adds the isinstance pin.
        result = _compile(
            "public fn f(-> @Int) requires(true) ensures(true) "
            "effects(pure) { 42 }"
        )
        r = execute(result, fn_name="f")
        assert r.value == 42
        assert isinstance(r.value, int) and not isinstance(r.value, bool)

    def test_float_return(self) -> None:
        """A @Float64 return surfaces as a Python float, not an int."""
        # overlaps test_codegen_expressions.py::TestFloatSlotRef — the isinstance pin
        # is the discriminator: a regression returning the int bit-pattern
        # would still satisfy ``== 7.5`` under Python numeric coercion in
        # some paths, but not ``isinstance float``.
        result = _compile(
            "public fn id(@Float64 -> @Float64) requires(true) ensures(true) "
            "effects(pure) { @Float64.0 }"
        )
        r = execute(result, fn_name="id", args=[7.5])
        assert r.value == 7.5
        assert isinstance(r.value, float)

    def test_string_return_is_decoded(self) -> None:
        """A @String return is decoded to a Python str, not a bare pointer."""
        # overlaps test_codegen_strings.py::test_string_return_execution.  KEY
        # cell: a ``@String`` return is decoded from the (ptr,len) pair to
        # a Python ``str`` because ``hello`` is in ``fn_string_returns``.
        # Pinned side-by-side with the array case below to lock the
        # decode-vs-bare-pointer asymmetry.
        result = _compile(
            'public fn hello(-> @String) requires(true) ensures(true) '
            'effects(pure) { "hello" }'
        )
        r = execute(result, fn_name="hello")
        assert r.value == "hello"
        assert isinstance(r.value, str)

    def test_array_return_is_bare_heap_pointer(self) -> None:
        """An Array<T> return stays a raw heap-pointer int, never decoded."""
        # overlaps test_codegen_strings.py::test_array_return_unchanged.  The
        # other half of the asymmetry: an ``Array<T>`` return is NOT
        # decoded — ``value`` is the raw heap pointer (an int), never a
        # Python list and never a decoded string.
        result = _compile(
            "public fn nums(-> @Array<Int>) requires(true) ensures(true) "
            "effects(pure) { [1, 2, 3] }"
        )
        r = execute(result, fn_name="nums")
        assert isinstance(r.value, int)
        assert not isinstance(r.value, bool)
        assert r.value > 0  # a real heap pointer, not the contents

    def test_unit_return_is_none(self) -> None:
        """A @Unit return surfaces as None."""
        result = _compile(
            "public fn nothing(@Unit -> @Unit) requires(true) ensures(true) "
            "effects(pure) { () }"
        )
        r = execute(result, fn_name="nothing")  # @Unit param takes no arg
        assert r.value is None


# =====================================================================
# stdout — captured IO.print output
# =====================================================================


class TestExecuteStdoutField734:
    """``ExecuteResult.stdout`` captures IO.print output, in order, exactly."""

    def test_stdout_captured(self) -> None:
        """IO.print output is captured into stdout."""
        result = _compile(
            'public fn main(-> @Unit) requires(true) ensures(true) '
            'effects(<IO>) { IO.print("hello") }'
        )
        r = execute(result, fn_name="main")
        assert r.stdout == "hello"

    def test_stdout_order_preserved(self) -> None:
        """Multiple IO.print calls are captured in call order."""
        # Discriminator: order, not just membership — concatenation must
        # follow call order, so a reversed/buffered regression flips RED.
        result = _compile(
            'public fn main(-> @Unit) requires(true) ensures(true) '
            'effects(<IO>) { IO.print("a"); IO.print("b"); IO.print("c") }'
        )
        r = execute(result, fn_name="main")
        assert r.stdout == "abc"

    def test_stdout_empty_when_no_print(self) -> None:
        """A program that prints nothing yields empty stdout."""
        # Pairs with the captured cases: a program that prints nothing
        # must yield "" exactly, so a leak from another stream flips RED.
        result = _compile(
            "public fn f(-> @Int) requires(true) ensures(true) "
            "effects(pure) { 7 }"
        )
        r = execute(result, fn_name="f")
        assert r.stdout == ""


# =====================================================================
# state — final State<T> snapshot
# =====================================================================


class TestExecuteStateField734:
    """``ExecuteResult.state`` is the post-run State<T> snapshot."""

    def test_state_reflects_final_put(self) -> None:
        """state holds the final State<Int> value after a put."""
        # overlaps test_codegen_effects.py::TestStateEffect::test_increment_pattern.
        result = _compile(
            "public fn increment(@Unit -> @Unit) requires(true) ensures(true) "
            "effects(<State<Int>>) { let @Int = get(()); put(@Int.0 + 1); () }"
        )
        r = execute(result, fn_name="increment")  # @Unit param takes no arg
        assert r.state["State_Int"] == 1
        assert r.value is None  # Unit return, alongside the state mutation

    def test_initial_state_round_trips(self) -> None:
        """initial_state seeds the starting State<Int> value."""
        # overlaps test_codegen_effects.py::test_state_initial_value.  10 is
        # distinct from the State<Int> default of 0, so this fails if the
        # initial_state seam is ignored.
        result = _compile(
            "public fn f(-> @Int) requires(true) ensures(true) "
            "effects(<State<Int>>) { get(()) }"
        )
        r = execute(result, fn_name="f", initial_state={"State_Int": 10})
        assert r.value == 10

    def test_state_empty_when_pure(self) -> None:
        """A pure program leaves state empty."""
        result = _compile(
            "public fn f(-> @Int) requires(true) ensures(true) "
            "effects(pure) { 7 }"
        )
        r = execute(result, fn_name="f")
        assert r.state == {}


# =====================================================================
# exit_code — None on normal return, set on IO.exit
# =====================================================================


class TestExecuteExitCodeField734:
    """``ExecuteResult.exit_code`` distinguishes normal return from exit."""

    def test_exit_code_none_on_normal_return(self) -> None:
        """A normal return leaves exit_code as None."""
        # Gap: no existing test pins that a normal return leaves
        # exit_code as None (the sentinel for "did not exit").
        result = _compile(
            "public fn f(-> @Int) requires(true) ensures(true) "
            "effects(pure) { 42 }"
        )
        r = execute(result, fn_name="f")
        assert r.exit_code is None

    def test_io_exit_sets_code_and_value_none(self) -> None:
        """IO.exit(n) sets exit_code to n with value None."""
        # overlaps test_codegen_io.py::test_io_exit_nonzero — adds the
        # ``value is None`` pin the existing test omits.
        result = _compile(
            'public fn main(-> @Unit) requires(true) ensures(true) '
            'effects(<IO>) { IO.print("before exit"); IO.exit(42) }'
        )
        r = execute(result, fn_name="main")
        assert r.exit_code == 42
        assert r.value is None
        assert r.stdout == "before exit"  # output before exit preserved

    def test_io_exit_zero_is_distinct_from_none(self) -> None:
        """IO.exit(0) sets exit_code to 0, distinct from None."""
        # overlaps test_codegen_io.py::test_io_exit_zero.  Discriminator: 0
        # is falsy but is NOT None — a regression conflating "exited with
        # 0" and "did not exit" (e.g. ``exit_code or None``) flips RED
        # here where ``== 0`` and ``is not None`` disagree with None.
        result = _compile(
            'public fn main(-> @Unit) requires(true) ensures(true) '
            'effects(<IO>) { IO.print("before exit"); IO.exit(0) }'
        )
        r = execute(result, fn_name="main")
        assert r.exit_code == 0
        assert r.exit_code is not None
        assert r.value is None
        assert r.stdout == "before exit"


# =====================================================================
# stderr — captured only when capture_stderr=True
# =====================================================================


class TestExecuteStderrField734:
    """``ExecuteResult.stderr`` is gated by the ``capture_stderr`` flag."""

    # The same program run two ways: the discriminating *pair*.  A
    # default-only test would pass even if stderr capture were completely
    # broken (the default is ""), so the contract is only pinned by
    # showing the flag toggles the field.
    _STDERR_PROG = (
        'public fn main(-> @Unit) requires(true) ensures(true) effects(<IO>) '
        '{ IO.print("to stdout"); IO.stderr("to stderr"); '
        'IO.print(" more stdout") }'
    )

    def test_stderr_captured_when_requested(self) -> None:
        """capture_stderr=True captures IO.stderr into stderr."""
        # overlaps test_codegen_io.py::test_io_stderr_captured_when_requested.
        result = _compile(self._STDERR_PROG)
        r = execute(result, fn_name="main", capture_stderr=True)
        assert r.stderr == "to stderr"
        assert r.stdout == "to stdout more stdout"  # streams don't cross

    def test_stderr_empty_by_default(self) -> None:
        """Without capture_stderr, stderr stays empty."""
        # overlaps test_codegen_io.py::test_io_stderr_default_not_captured.
        result = _compile(self._STDERR_PROG)
        r = execute(result, fn_name="main")  # capture_stderr defaults False
        assert r.stderr == ""


# =====================================================================
# WASM trap — execute() RAISES (does not return)
# =====================================================================


class TestExecuteTrapMode734:
    """A WASM trap *raises* ``WasmTrapError`` — it never returns a result.

    Pins the asymmetry that makes the trap path unlike the other two
    completion modes, plus the classified ``kind`` and the #522
    output-before-trap preservation contract.

    The three kinds exercised (``divide_by_zero`` / ``contract_violation``
    / ``unreachable``) are the ones reliably producible through a real
    ``execute()`` end-to-end.  The remaining taxonomy kinds
    (``out_of_bounds`` / ``stack_exhausted`` / ``overflow``) cannot be
    reproduced from a small program here; their classification is
    unit-pinned in ``test_runtime_traps.py`` against a synthetic
    ``_FakeTrap``.
    """

    def test_divide_by_zero_raises_with_kind_and_stdout(self) -> None:
        """A divide-by-zero raises WasmTrapError, carrying kind and pre-trap stdout."""
        result = _compile(_DIVZERO_WITH_PRINTS)
        with pytest.raises(WasmTrapError) as excinfo:
            execute(result, fn_name="main")
        exc = excinfo.value
        assert exc.kind == "divide_by_zero"
        # Output written before the trap is carried on the exception
        # (#522), not discarded as execute() unwinds.
        assert "line 1 before crash" in exc.stdout
        assert "line 4 before crash" in exc.stdout

    def test_contract_violation_raises_with_kind(self) -> None:
        """A failed precondition raises WasmTrapError (contract_violation)."""
        result = _compile(_PRECONDITION_FAIL)
        with pytest.raises(WasmTrapError) as excinfo:
            execute(result, fn_name="positive", args=[0])
        assert excinfo.value.kind == "contract_violation"

    def test_array_index_oob_raises(self) -> None:
        """An out-of-bounds index raises WasmTrapError rather than returning."""
        # An out-of-bounds index traps rather than returning a result.
        # The kind is pinned to whatever codegen actually lowers an OOB
        # index to (a WASM ``unreachable``), characterizing real
        # behaviour — not asserting an assumed taxonomy.
        result = _compile(_ARRAY_INDEX_OOB)
        with pytest.raises(WasmTrapError) as excinfo:
            execute(result, fn_name="idx", args=[5])
        assert excinfo.value.kind == "unreachable"


# =====================================================================
# Interrupt — Ctrl-C during a host import maps to exit_code 130
# =====================================================================


class TestExecuteInterruptMode734:
    """A ``KeyboardInterrupt`` in a host import returns exit_code 130."""

    def test_keyboard_interrupt_maps_to_130(self) -> None:
        """A KeyboardInterrupt in a host import returns exit_code 130."""
        # overlaps test_runtime_traps.py::test_host_sleep_keyboard_interrupt
        # _end_to_end.  Patching ``time.sleep`` to raise KeyboardInterrupt
        # simulates Ctrl-C the instant IO.sleep enters the host import;
        # wasmtime's trampoline unwinds and execute()'s single handler
        # maps it to the conventional SIGINT exit code (130 = 128 + 2).
        result = _compile(
            'public fn main(@Unit -> @Unit) requires(true) ensures(true) '
            'effects(<IO>) { IO.print("before sleep"); IO.sleep(120); '
            'IO.print("after sleep") }'
        )
        with patch.object(_time, "sleep", side_effect=KeyboardInterrupt):
            r = execute(result)
        assert r.exit_code == 130
        assert r.value is None
        assert "before sleep" in r.stdout  # output before the interrupt kept
        assert "after sleep" not in r.stdout  # program did not continue


# =====================================================================
# Positional-constructor compatibility shape
# =====================================================================


class TestExecutePositionalShape734:
    """The dataclass's documented external shape: (value, stdout, state,
    exit_code), with stderr appended last so the pre-#463 positional
    constructor still works for external callers."""

    def test_positional_constructor_compat(self) -> None:
        """The (value, stdout, state, exit_code) positional shape still works."""
        # The four-positional shape the dataclass comment promises.
        r = ExecuteResult(7, "out", {"State_Int": 1}, 3)
        assert r.value == 7
        assert r.stdout == "out"
        assert r.state == {"State_Int": 1}
        assert r.exit_code == 3
        assert r.stderr == ""  # 5th field, defaulted

    def test_field_order_matches_documented_shape(self) -> None:
        """The declared ExecuteResult field order matches the documented shape."""
        # The discriminator: pins the declared field ORDER, so a refactor
        # that reorders the dataclass fields (silently breaking every
        # positional caller) flips RED.
        names = [f.name for f in fields(ExecuteResult)]
        assert names[:5] == [
            "value", "stdout", "state", "exit_code", "stderr",
        ]
