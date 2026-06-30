"""Runtime-trap classification and source-backtrace resolution.

Extracted from `vera/codegen/api.py` (#421).  `WasmTrapError` / `TrapFrame`
are the public trap types (re-exported from `vera.codegen.api`); the
`_classify_trap` / `_resolve_trap_frames` helpers are used by `execute()`
and unit-tested directly.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from dataclasses import dataclass

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
        * ``unreachable`` — ``unreachable`` instruction executed (the
          WASM panic primitive — typically a non-exhaustive match).
        * ``overflow`` — integer overflow trap.
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
    except Exception:  # pragma: no cover — defensive
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


# #516 Stage 3 (#547) — per-kind Fix paragraphs.  Keyed by the
# stable trap kind so consumers can look up the suggestion text
# without having to re-parse the trap reason.  Stage 3 splits the
# previous (kind, message) pair into (kind, description, fix), so
# a contract-violated description like "Out-of-bounds memory
# access" is no longer crowded with an inline Fix-shaped clause —
# the suggestion lives in its own field, formatted alongside the
# rest of the toolchain's compile-time `Diagnostic` shape
# (description / rationale / fix / spec_ref) for consistency.
#
# Empty string for `contract_violation` (the host import already
# wrote a precise message into ``last_violation``; the user
# already knows which contract failed and where, so adding a
# generic "fix your contract" paragraph would be patronising) and
# for `unknown` (by definition we don't know what to suggest).
_TRAP_FIX_PARAGRAPHS: dict[str, str] = {
    "divide_by_zero": (
        "Add a precondition `requires(divisor != 0)` on the function "
        "performing the division, or guard the division site with a "
        "non-zero check.  The Z3 verifier will then prove the division "
        "is safe at every call site at compile time."
    ),
    "out_of_bounds": (
        "Most often caused by `Array<T>[i]` with `i` outside `[0, "
        "array_length(arr))` or by `string_slice(s, start, end)` with "
        "out-of-range indices.  Add a `requires(i < "
        "array_length(arr))` precondition or guard the access "
        "explicitly.  If the trapping frame is `gc_collect`, "
        "`alloc`, or another runtime helper this is a compiler bug "
        "rather than a user error — please file a minimal reproducer "
        "at https://github.com/aallan/vera/issues/new."
    ),
    "stack_exhausted": (
        "Vera compiles tail-position calls to WASM `return_call` (#517, "
        "shipped in v0.0.126; allocating tail calls covered by GC-aware "
        "TCO in #549, v0.0.154), so iteration-shaped recursion runs in "
        "constant stack space — if you're still hitting this trap the "
        "recursion isn't actually in tail position.  Restructure with "
        "an accumulator parameter so the recursive call is the LAST "
        "thing the function does (no work after it, no `let`-binding "
        "of its result, no enclosing arithmetic).  One remaining "
        "exception: functions with a non-trivial runtime "
        "postcondition (`ensures` that emits a Tier-3 check) revert "
        "to plain `call` so the post-check runs after each call — "
        "either simplify the postcondition to one the verifier can "
        "discharge statically (Tier 1), or iterate via `array_fold` / "
        "`array_map` (which compile to WASM loops rather than "
        "recursion)."
    ),
    "unreachable": (
        "Usually a non-exhaustive `match` whose missing arm would have "
        "required user code, or a compiler-generated assertion (e.g. an "
        "ADT field offset that didn't resolve).  If the trap is inside "
        "a `match` expression, add the missing arm explicitly rather "
        "than relying on a wildcard — the type checker will tell you "
        "which constructors are uncovered."
    ),
    "overflow": (
        "Integer arithmetic produced a value outside the representable "
        "range — the signed i64 range `[-2^63, 2^63)` for `@Int`, or the "
        "unsigned u64 range `[0, 2^64)` for `@Nat` (#808 routes `@Nat` "
        "overflows here too).  Add a `requires` precondition that "
        "constrains the operands so Z3 can prove the result is "
        "representable, or change the operation to a saturating / checked "
        "variant via a helper function."
    ),
    "contract_violation": "",
    "unknown": "",
}


def _classify_trap(
    exc: BaseException,
    last_violation: list[str],
    last_overflow: list[object] | None = None,
) -> tuple[str, str, str]:
    """Classify a wasmtime trap into ``(kind, description, fix)``.

    A contract-violation host-import (``host_contract_fail``) writes
    the precise contract message into ``last_violation`` before WASM
    traps. When that channel is populated, it always wins over the
    wasmtime trap reason: the host-import path is more specific and
    already Vera-native.

    For everything else we inspect ``str(exc)`` for the wasmtime trap
    reason substring — wasmtime renders these as ``wasm trap: <reason>``
    in the exception message. The mapping is intentionally narrow:
    only reasons we can describe in Vera-native terms, with a known
    cause, get classified. Unknown reasons fall through to ``unknown``
    and surface verbatim so the user is never left without a message.

    The third return value is the per-kind Fix paragraph (#547,
    Stage 3), keyed by ``kind`` in ``_TRAP_FIX_PARAGRAPHS``.
    Empty string for ``contract_violation`` and ``unknown`` —
    those kinds either already have specific information in the
    description (the contract message) or have no actionable
    suggestion possible by definition.

    Stage 1 (v0.0.120) established the kind taxonomy.  Stage 2
    (v0.0.124, #546) added the source backtrace via
    ``WasmTrapError.frames``.  Stage 3 (this version) adds the
    Fix paragraph so the runtime-trap surface matches the rest of
    the toolchain's diagnostic style (compile-time errors have
    description / rationale / fix / spec_ref; runtime traps now
    have description / fix / kind / frames).
    """
    # Contract violation takes precedence — the host import gave us
    # the precise message; wasmtime's trap reason is just "unreachable
    # executed" in that path and would lose detail.
    if last_violation:
        return (
            "contract_violation",
            last_violation[0],
            _TRAP_FIX_PARAGRAPHS["contract_violation"],
        )

    # #808: the #798 integer-overflow guard calls the ``vera.overflow_trap``
    # host import (which signals this channel) immediately before its
    # ``unreachable``, so the trap classifies as the precise ``overflow`` kind
    # with its Fix paragraph rather than the generic ``unreachable`` a bare
    # instruction produces.  Checked before the ``str(exc)`` substring scan
    # below — that scan would otherwise match the trailing ``unreachable``
    # first (the host signals but the WASM still traps via ``unreachable``).
    if last_overflow:
        return (
            "overflow",
            "Integer overflow",
            _TRAP_FIX_PARAGRAPHS["overflow"],
        )

    msg = str(exc).lower()
    kind: str
    description: str
    if "integer divide by zero" in msg:
        kind = "divide_by_zero"
        description = "Integer division by zero"
    elif "out of bounds memory access" in msg:
        kind = "out_of_bounds"
        description = "Out-of-bounds memory access"
    elif "call stack exhausted" in msg:
        kind = "stack_exhausted"
        description = "WASM call stack exhausted"
    elif "unreachable" in msg:
        kind = "unreachable"
        description = "Reached `unreachable` WASM instruction"
    elif "integer overflow" in msg:
        kind = "overflow"
        description = "Integer overflow"
    else:
        # Couldn't classify — surface the raw wasmtime message
        # verbatim so the user still sees something diagnostic.
        # Use ``str(exc)`` directly rather than `f"WASM trap: {exc}"`
        # because the wasmtime exception text already contains the
        # "wasm trap:" substring (in its "Caused by:" tail), and a
        # synthetic mock that begins with "wasm trap: ..." would
        # otherwise produce a double-prefix message
        # ("WASM trap: wasm trap: ...").
        return ("unknown", str(exc), _TRAP_FIX_PARAGRAPHS["unknown"])

    return (kind, description, _TRAP_FIX_PARAGRAPHS[kind])
