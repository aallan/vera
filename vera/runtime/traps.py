"""Runtime-trap classification and source-backtrace resolution.

Extracted from `vera/codegen/api.py` (#421).  `WasmTrapError` / `TrapFrame`
are the public trap types (re-exported from `vera.codegen.api`); the
`_classify_trap` / `_resolve_trap_frames` helpers are used by `execute()`
and unit-tested directly.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import re
from dataclasses import dataclass

from vera.trap_registry import (
    NATIVE_TRAP_OPCODES,
    TRAP_KINDS,
    WASMTIME_NATIVE_TRAPS,
    kind_for_code,
    native_trap_kind,
)

if TYPE_CHECKING:
    pass


@dataclass(frozen=True)
class TrapFrame:
    """One resolved frame in a runtime-trap source backtrace (#516 Stage 2).

    Built by ``_resolve_trap_frames`` from a ``wasmtime.Frame`` plus
    the ``CompileResult.fn_source_map`` / ``prelude_fn_names`` data.
    Carried on ``WasmTrapError.frames`` and consumed by the CLI text
    formatter and the JSON envelope builder.

    A frozen dataclass instead of a ``dict[str, object]`` so mypy
    can type-check field access — the previous shape was a hand-
    rolled dict with stringly-typed keys (``frame["func"]``), which
    silently allowed typos and made it impossible to track the
    contract across consumers.
    """

    func: str
    """The WAT function name as reported by wasmtime, with any
    leading ``$`` stripped.  For monomorphized generics (e.g.
    ``identity$Int``) this is the mangled name."""

    file: str
    """Source path, ``"<builtin>"`` for runtime helpers / prelude
    injections, or ``"<unknown>"`` for user-named frames not found
    in the source map."""

    line_start: int | None
    """Source line range start of the function definition.  ``None``
    for built-ins and unknown-name frames."""

    line_end: int | None
    """Source line range end of the function definition.  ``None``
    for built-ins and unknown-name frames."""

    is_builtin: bool
    """``True`` for ``alloc`` / ``gc_collect`` / ``contract_fail`` /
    ``exn_*`` / ``vera.*`` runtime helpers and for prelude /
    inject_prelude functions; ``False`` for user-named frames
    (including ``<unknown>`` lookups)."""

    def to_dict(self) -> dict[str, object]:
        """Serialise to a JSON-compatible dict for envelope output.

        Used by ``cmd_run --json`` to preserve the wire format that
        downstream consumers (LSP, agents, telemetry) parse.  Each
        field becomes a key with its native type (``None`` serialises
        to JSON null, matching the Stage 2 contract for built-in
        frames with no source line range)."""
        return {
            "func": self.func,
            "file": self.file,
            "line_start": self.line_start,
            "line_end": self.line_end,
            "is_builtin": self.is_builtin,
        }


class WasmTrapError(RuntimeError):
    """A WASM runtime trap, classified and carrying buffered output.

    Raised by ``execute()`` in place of the raw ``wasmtime.Trap`` /
    ``WasmtimeError`` so that consumers (the CLI, tests, future LSP)
    receive a uniform shape regardless of which underlying wasmtime
    exception fired:

    * ``message`` — a Vera-native description of the trap reason
      (e.g. "Integer division by zero"), passed to ``RuntimeError``.
      Existing ``except RuntimeError`` blocks therefore still catch
      this error and see a sensible string.

    * ``stdout`` / ``stderr`` — whatever the program wrote via
      ``IO.print`` / ``IO.eprint`` before trapping. Without this, the
      output would be discarded as the exception unwound out of
      ``execute()`` (#522).

    * ``kind`` — a stable identifier for the trap class. One of:

        * ``contract_violation`` — a runtime-checked Vera contract
          failed (precondition, postcondition, decreases, etc.).
        * ``divide_by_zero`` — integer division (or modulo) by zero.
        * ``out_of_bounds`` — WASM memory access outside the linear
          memory bounds.
        * ``stack_exhausted`` — WASM call stack overflow (#517-class).
        * ``unreachable`` — an ``unreachable`` no signal named: one of the
          internal causes ``vera.trap_registry.INTERNAL_TRAPS`` lists
          (shadow-stack overflow, a collector limit, a WASI host I/O
          failure, a compiler bug), never a check on a program value.
        * ``overflow`` — integer overflow trap.
        * ``widen_guard`` — a ``@Nat`` above ``i64.MAX`` was widened into
          an ``@Int`` slot, where it would reinterpret as negative (#1438).
        * ``nat_guard`` — a negative ``@Int`` was bound into a ``@Nat``
          slot and the narrowing guard caught it (#754).
        * ``nat_underflow`` — a ``@Nat`` subtraction would have gone
          negative (#1479).
        * ``assertion_failed`` — a body ``assert(...)`` was false (#1479).
        * ``index_out_of_bounds`` — an array index outside
          ``[0, array_length)`` (#1479).
        * ``string_index_out_of_bounds`` — a ``string_char_code`` index
          outside ``[0, string_length)`` (#1479).
        * ``float_conversion`` — ``float_to_int`` / ``floor`` / ``ceil`` /
          ``round`` given NaN, an infinity or a value outside the ``@Int``
          range (#1479).
        * ``heap_exhausted`` — an allocation the heap could not satisfy
          (#1479).
        * ``uncaught_exception`` — an ``Exn<T>`` no ``handle[Exn<T>]``
          caught left the entry point; the message names its type and,
          where printable, the value thrown (#1479).
        * ``host_error`` — a host import (an effect operation
          implemented outside WASM) raised rather than trapping; the
          message is the host binding's own (#1302).  Everything
          escaping the guest invocation carries one of these kinds:
          the conversion is keyed on the boundary, not on the
          exception's type.
        * ``unknown`` — could not classify; raw wasmtime message in
          ``str()``.

    * ``frames`` — a ``list[TrapFrame]`` resolved trap backtrace
      (#516 Stage 2).  Innermost (leaf) frame first, matching the
      wasmtime backtrace order.  See ``TrapFrame`` for the field
      shape; serialise to JSON via
      ``[f.to_dict() for f in exc.frames]``.

    * ``fix`` — a per-kind suggestion paragraph (#516 Stage 3 /
      #547).  Empty string for ``contract_violation`` (the contract
      message itself already says what failed) and ``unknown`` (no
      actionable suggestion possible).  Otherwise contains the
      canonical text from ``_TRAP_FIX_PARAGRAPHS``: a concrete
      paragraph naming the most-likely cause and the recommended
      remediation, formatted to match the rest of the toolchain's
      compile-time ``Diagnostic`` shape (description / rationale /
      fix / spec_ref).

    Stage 1 of #516 (v0.0.120) established the ``kind`` taxonomy.
    Stage 2 (v0.0.124) added source mapping (the ``frames`` field).
    Stage 3 (this version) adds the ``fix`` field so runtime traps
    carry actionable Vera-native suggestions like compile-time
    errors do.
    """

    def __init__(
        self,
        message: str,
        *,
        stdout: str = "",
        stderr: str = "",
        kind: str = "unknown",
        frames: list[TrapFrame] | None = None,
        fix: str = "",
    ) -> None:
        super().__init__(message)
        self.stdout = stdout
        self.stderr = stderr
        self.kind = kind
        self.frames: list[TrapFrame] = frames or []
        self.fix: str = fix


def _find_frames_in_exception_chain(
    exc: BaseException,
) -> object | None:
    """Walk the exception chain looking for a ``frames`` attribute.

    Some wasmtime call paths raise a ``WasmtimeError`` whose
    ``__cause__`` is the underlying ``wasmtime.Trap`` carrying the
    backtrace data; if we only inspect the outer exception we lose
    the frames silently.  Walks ``exc.frames`` first, then
    ``__cause__`` / ``__context__`` recursively until a frame
    sequence is found or the chain terminates.  Mirrors the
    ``_VeraExit`` chain walk pattern already used in ``execute()``.

    Returns the first non-empty ``.frames`` attribute encountered,
    or ``None``.
    """
    seen: set[int] = set()
    cursor: BaseException | None = exc
    while cursor is not None and id(cursor) not in seen:
        seen.add(id(cursor))
        frames: object | None = getattr(cursor, "frames", None)
        if frames:
            return frames
        cursor = cursor.__cause__ or cursor.__context__
    return None


def _resolve_trap_frames(
    exc: BaseException,
    fn_source_map: dict[str, tuple[str, int, int]],
    prelude_fn_names: set[str] | None = None,
) -> list[TrapFrame]:
    """Resolve ``wasmtime.Trap.frames`` against the codegen source map.

    Walks the trap's frame list and produces a structured backtrace,
    one ``TrapFrame`` per frame (see ``TrapFrame`` for field shape).

    Resolution rules:

    * The WAT function name is normalised by stripping a single
      leading ``$`` defensively (current wasmtime-py strips it
      already; a future version that doesn't would otherwise
      silently break every lookup below).
    * Built-in WAT helpers (``alloc`` / ``gc_collect`` /
      ``contract_fail``) plus anything starting with ``exn_`` /
      ``vera.`` / ``closure_sig_`` are tagged ``is_builtin=True``,
      ``file="<builtin>"``.
    * Prelude / inject_prelude functions are tagged the same way,
      via the ``prelude_fn_names`` parameter (positive source of
      truth populated by the post-prelude registration loop).  The
      check matches the exact name first, then tries the base name
      (the part before the rightmost ``$``) for monomorphized
      generics — ``option_unwrap_or$Int`` resolves to the same
      builtin tag as ``option_unwrap_or``.
    * User-named frames look up exact-then-base in
      ``fn_source_map``; on miss the frame is surfaced with
      ``file="<unknown>"`` rather than dropped.

    On any failure (no ``frames`` attribute, exception during
    iteration, etc.) returns an empty list — the trap message
    survives even if the backtrace can't be resolved.  Per-function
    granularity matches the issue's stated Stage 2 success criterion
    (#516).

    Walks the exception chain (``__cause__`` / ``__context__``) to
    find the first frame-bearing exception.  Some wasmtime call
    paths wrap a ``Trap`` (which carries ``frames``) inside a
    ``WasmtimeError`` (which doesn't); without the chain walk we'd
    silently lose the backtrace whenever wrapping happens.  Mirrors
    the ``_VeraExit`` chain walk in ``execute()``.
    """
    raw_frames = _find_frames_in_exception_chain(exc)
    if not raw_frames:
        return []

    # WAT names that the codegen emits as runtime-only infrastructure.
    # Treat any frame matching one of these (or any name starting with
    # one of the prefixes below) as a built-in with no source location.
    _BUILTIN_NAMES = {
        "alloc", "gc_collect", "contract_fail",
    }
    _BUILTIN_PREFIXES = (
        "exn_",        # generated exception throwers ($exn_String etc.)
        "vera.",       # host imports ($vera.print, $vera.state_get_*, ...)
        "closure_sig_",  # synthetic closure signatures
    )

    resolved: list[TrapFrame] = []
    try:
        # raw_frames is `object | None` from the chain walker (we
        # only know it's truthy and presumed iterable — wasmtime's
        # Trap.frames is a list-of-Frame in practice).  Cast via
        # `list()` to materialise; the broad except below catches
        # pathological inputs (a frames attribute that isn't
        # iterable) so this stays robust.
        iter_frames = list(raw_frames)  # type: ignore[call-overload]
    except Exception:  # pragma: no cover — defensive  # noqa: BLE001
        return []

    for frame in iter_frames:
        name = getattr(frame, "func_name", None) or ""
        # Some wasmtime versions return the name with a leading `$`
        # for un-named functions, or `None` for true anonymous frames.
        # Skip frames we can't even name — they'd be useless in the
        # backtrace.
        if not name:
            continue
        # Defensive normalisation — strip a single leading `$` so the
        # builtin allowlist and source-map lookup work uniformly across
        # wasmtime versions.  Current wasmtime-py strips this already
        # (verified with a divide-by-zero trap inside `(func $bad ...)`
        # returning func_name='bad'); a future version that doesn't
        # strip would otherwise silently break every lookup below.
        if name.startswith("$"):
            name = name[1:]

        # Prelude / built-in injection check.  Match either the exact
        # WAT name or, for monomorphized generics, the base name (the
        # part before the rightmost `$`).  This mirrors the source-
        # map suffix-strip rule below — `array_map$Int` should resolve
        # to the same builtin tag as `array_map`.  Without this
        # fallback, monomorphized prelude calls would mis-classify as
        # `<unknown>` user code (see CodeRabbit finding on PR #546
        # round 3).
        is_prelude = False
        if prelude_fn_names is not None:
            if name in prelude_fn_names:
                is_prelude = True
            elif "$" in name:
                base = name.rsplit("$", 1)[0]
                if base in prelude_fn_names:
                    is_prelude = True

        is_builtin = (
            name in _BUILTIN_NAMES
            or any(name.startswith(p) for p in _BUILTIN_PREFIXES)
            or is_prelude
        )
        if is_builtin:
            resolved.append(TrapFrame(
                func=name,
                file="<builtin>",
                line_start=None,
                line_end=None,
                is_builtin=True,
            ))
            continue

        # Try the exact name first; on miss, try the base name (the
        # part before the rightmost `$`) for monomorphized generics.
        # `$` cannot appear in user-written Vera identifiers, so any
        # `$` in a WAT name was inserted by the monomorphizer.
        loc = fn_source_map.get(name)
        if loc is None and "$" in name:
            base = name.rsplit("$", 1)[0]
            loc = fn_source_map.get(base)

        if loc is None:
            # Not a user function we have a source for, but not on the
            # builtin allowlist either (could be a future codegen
            # helper, a closure that didn't register, etc.).  Surface
            # the name with no location rather than dropping the frame
            # — the user still benefits from knowing which WAT
            # function trapped.
            resolved.append(TrapFrame(
                func=name,
                file="<unknown>",
                line_start=None,
                line_end=None,
                is_builtin=False,
            ))
            continue

        file_path, line_start, line_end = loc
        resolved.append(TrapFrame(
            func=name,
            file=file_path,
            line_start=line_start,
            line_end=line_end,
            is_builtin=False,
        ))

    return resolved


# #516 Stage 3 (#547) — per-kind Fix paragraphs, keyed by the stable trap
# kind so consumers can look up the suggestion text without re-parsing the
# trap reason.  Derived from `vera.trap_registry.TRAP_KINDS` (#1479), the one
# table every host names a trap from, so the wasmtime, WASI and browser hosts
# cannot give one kind two remedies.  Empty for `contract_violation` and
# `host_error` (the message is itself the instruction) and for `unknown`
# (nothing general to suggest); the `unreachable` paragraph is derived from
# the internal roster and names exactly the causes that can reach it.
_TRAP_FIX_PARAGRAPHS: dict[str, str] = {
    name: kind.fix for name, kind in TRAP_KINDS.items()
}


def _classify_host_error(exc: BaseException) -> tuple[str, str, str]:
    """Classify a host-callback exception into ``(kind, description, fix)``.

    The companion to :func:`_classify_trap` for the other half of what
    can escape a guest invocation.  A host import that raises an
    ordinary Python exception — ``json_stringify`` refusing a non-finite
    ``JNumber``, say — is re-raised through wasmtime's trampoline and
    arrives at ``execute()``'s handler as that exception, not as a
    ``Trap``.  Before #1302 it fell past the conversion entirely and
    reached the user as a raw interpreter traceback.

    The description is the exception's own message: a host binding that
    refuses something states why and what to do about it (DESIGN
    principle 1), so there is nothing to add and everything to lose by
    paraphrasing.  An exception with no message would render as an empty
    line, so the type name stands in.

    The Fix paragraph is empty for the same reason it is empty for
    ``contract_violation``: the description already carries the specific
    instruction, and a canned paragraph beneath it would be noise.

    Unlike :func:`_classify_trap` this does not consult the
    ``last_violation`` channel.  That channel exists because a WASM trap
    reason is less specific than the contract message the host recorded
    just before it; here the host's message IS the specific one, and
    letting a stale violation win would replace it.
    """
    return (
        "host_error",
        str(exc) or type(exc).__name__,
        _TRAP_FIX_PARAGRAPHS["host_error"],
    )


#: How wasmtime renders a trap: its backtrace, then ``Caused by:`` and the
#: engine's own reason, usually as ``wasm trap: <reason>``.
_CAUSED_BY = re.compile(r"^\s*Caused by:\s*$", re.MULTILINE)
_TRAP_REASON = re.compile(r"^\s*wasm trap:\s*(.*?)\s*$", re.MULTILINE)
_BACKTRACE_LINE = re.compile(r"^\s*\d+:\s+0x[0-9a-f]+\s+-\s", re.MULTILINE)


def trap_reason(message: str) -> str:
    """The engine's own reason for a trap, from wasmtime's rendering of it.

    The first line under the last ``Caused by:`` (without its ``wasm
    trap:``), or a ``wasm trap:`` line — never the backtrace above them,
    whose frames name the program's functions: a function called
    ``unreachable`` must not be read as the reason an ``INT_MIN / -1``
    trapped (#1479).  A message with no backtrace is all reason; one with a
    backtrace and no cause has none a host can trust."""
    causes = list(_CAUSED_BY.finditer(message))
    if causes:
        for line in message[causes[-1].end():].splitlines():
            if line.strip():
                return line.strip().removeprefix("wasm trap:").strip()
        return ""
    reasons = _TRAP_REASON.findall(message)
    if reasons:
        return str(reasons[-1])
    return "" if _BACKTRACE_LINE.search(message) else message


def trap_code_name(exc: BaseException) -> str | None:
    """wasmtime's structured trap code for *exc* (its ``TrapCode`` member's
    name), found through the exception chain; None where there is none —
    a component call, a host error, a synthetic exception."""
    seen: set[int] = set()
    cursor: BaseException | None = exc
    while cursor is not None and id(cursor) not in seen:
        seen.add(id(cursor))
        code = getattr(cursor, "trap_code", None)
        name = getattr(code, "name", None)
        if isinstance(name, str):
            return name
        cursor = cursor.__cause__ or cursor.__context__
    return None


def trapping_instruction(
    exc: BaseException, wasm_bytes: bytes | bytearray,
) -> str | None:
    """The natively trapping instruction a wasmtime trap stopped at, or None.

    The innermost frame's offset into the module is the trapping
    instruction's, so the opcode there says which instruction it was
    (#1479) — needed because wasmtime gives a truncation past its range and
    ``INT_MIN / -1`` the same reason, "integer overflow".  The frames are
    found through the exception chain, as the backtrace's are: some call
    paths raise a ``WasmtimeError`` whose cause is the ``Trap`` holding
    them."""
    try:
        frames = _find_frames_in_exception_chain(exc)
        offset = frames[0].module_offset if frames else None  # type: ignore[index]
    except (AttributeError, IndexError, TypeError, ValueError):
        return None
    if offset is None or not 0 <= offset < len(wasm_bytes):
        return None
    return NATIVE_TRAP_OPCODES.get(wasm_bytes[offset])


def _classify_trap(
    exc: BaseException,
    last_violation: list[str],
    last_trap: list[tuple[int, str]] | None = None,
    instruction: str | None = None,
) -> tuple[str, str, str]:
    """Classify a wasmtime trap into ``(kind, description, fix)``.

    Two host-import channels are consulted before the trap reason, because
    each is more specific than the ``unreachable`` a check executes after
    signalling:

    * ``last_violation`` — the contract message ``host_contract_fail``
      stored.  It always wins: the host import gave the precise contract.
    * ``last_trap`` — the ``(code, message)`` a named check passed to
      ``vera.trap`` (#1479).  The code names the kind in
      ``vera.trap_registry.TRAP_KINDS``; the message, when the check
      carries one, is the description, and the kind's canonical
      description stands in when it does not.

    Otherwise the trap is the engine's own: its kind comes from
    ``native_trap_kind`` — the trapping *instruction*, where the host can
    report it (``trapping_instruction``); wasmtime's structured trap code,
    where the exception carries one (``trap_code_name``); and the trap
    reason (``trap_reason``: the engine's words only, never the backtrace's
    function names) matched against ``WASMTIME_NATIVE_TRAPS`` (first match
    wins).  An
    unrecognised reason is ``unknown`` and surfaces verbatim so the user is
    never left without a message.  The third element is the kind's Fix
    paragraph (#547).
    """
    if last_violation:
        return (
            "contract_violation",
            last_violation[0],
            _TRAP_FIX_PARAGRAPHS["contract_violation"],
        )

    # Checked before the reason scan, which would otherwise match the
    # trailing `unreachable` every signalled trap executes.
    if last_trap:
        code, message = last_trap[0]
        named = kind_for_code(code)
        if named is not None:
            return (named.name, message or named.description, named.fix)

    native = native_trap_kind(
        trap_reason(str(exc)).lower(), instruction, WASMTIME_NATIVE_TRAPS,
        code=trap_code_name(exc))
    if native is not None:
        return (native, TRAP_KINDS[native].description,
                _TRAP_FIX_PARAGRAPHS[native])
    # Couldn't classify — surface the raw wasmtime message verbatim so the
    # user still sees something diagnostic.  `str(exc)` directly rather than
    # `f"WASM trap: {exc}"`: the wasmtime text already contains "wasm trap:"
    # in its "Caused by:" tail, and a prefix would double it.
    return ("unknown", str(exc), _TRAP_FIX_PARAGRAPHS["unknown"])
