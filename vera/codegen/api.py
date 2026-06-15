"""Public API for the Vera code generator.

Standalone functions (``compile``, ``execute``), result dataclasses,
and ADT memory-layout helpers.  These are the only symbols imported
by external modules.

See spec/11-compilation.md for the compilation specification.
"""

from __future__ import annotations

import os
import struct
import sys
import time
from dataclasses import dataclass, field
from io import StringIO
from pathlib import Path
from typing import TYPE_CHECKING, Any

import wasmtime

from vera import ast

if TYPE_CHECKING:
    from vera.resolver import ResolvedModule


# =====================================================================
# ADT memory layout
# =====================================================================


@dataclass
class ConstructorLayout:
    """WASM memory layout for a single ADT constructor."""

    tag: int  # discriminant (0, 1, 2, ...)
    field_offsets: tuple[tuple[int, str], ...]  # (byte_offset, wasm_type) per field
    total_size: int  # total bytes, 8-byte aligned


def _validate_wrap_handle(
    raw_handle: object, kind: int, body_ptr: int,
) -> None:
    """#578 invariant: raw_handle must fit in 31 unsigned bits.

    Wrapper ADTs store ``raw_handle | 0x80000000`` at body offset 4 so
    the in-heap field is structurally outside the conservative-scan
    heap-range check (`heap_ptr` is hard-capped at 0x80000000 by the
    `$alloc` heap-ceiling guard).  The unwrap site recovers the raw
    handle with ``& 0x7FFFFFFF``.  Both directions break silently
    outside ``[0, 0x80000000)``:

    - Negative ints have bit 31 set in two's complement.
      ``raw_handle | 0x80000000`` is a no-op and the unwrap mask
      returns the WRONG handle.
    - Values ``>= 0x80000000`` alias into the top half and collide
      with the tag-bit pattern.
    - Values ``>= 0x100000000`` truncate on ``_write_i32`` and
      silently lose information.
    - Non-int values would ``TypeError`` deeper in the stack;
      catching them here makes the diagnostic actionable.
    - ``bool`` values: Python's ``bool`` subclasses ``int``, so
      ``isinstance(True, int)`` is ``True`` and the value would
      pass an ``isinstance``-only check, silently aliasing to
      handles 1 and 0.  The strict ``type(raw_handle) is int``
      check rejects bools without accepting any int subclass.

    Practical alloc counters are bounded well below 2^31 — a 2B-handle
    session is wall-clock infeasible — but a silent round-trip
    failure is exactly the corruption class #578 sought to eliminate.
    Fail fast.

    Module-level helper so it can be unit-tested directly without
    standing up a wasmtime instance (``_wrap_handle`` is nested
    inside ``execute()`` and not importable on its own).
    """
    # ``type(x) is int`` rather than ``isinstance(x, int)`` so we
    # reject ``bool`` (which would otherwise pass — bool subclasses
    # int in Python and silently aliases to handles 0 / 1).
    if not (
        type(raw_handle) is int
        and 0 <= raw_handle < 0x80000000
    ):
        raise RuntimeError(
            f"#578: raw_handle={raw_handle!r} (kind={kind!r}, "
            f"body_ptr={body_ptr!r}) is outside the valid "
            f"range [0, 0x80000000); cannot tag for the "
            f"conservative-scan disjointness invariant.  "
            f"Host-store handle counters must be unsigned "
            f"31-bit integers.  Either a counter overflowed, "
            f"a negative sentinel flowed in, or a non-integer "
            f"value flowed into _wrap_handle."
        )


def _wasm_type_size(wt: str) -> int:
    """Byte size of a WASM value type."""
    if wt == "i32":
        return 4
    if wt in ("i64", "f64"):
        return 8
    if wt == "i32_pair":
        return 8
    raise ValueError(f"Unknown WASM type: {wt}")


def _wasm_type_align(wt: str) -> int:
    """Natural alignment of a WASM value type."""
    if wt == "i32":
        return 4
    if wt in ("i64", "f64"):
        return 8
    if wt == "i32_pair":
        return 4
    raise ValueError(f"Unknown WASM type: {wt}")


def _align_up(offset: int, align: int) -> int:
    """Round offset up to the next multiple of align."""
    return (offset + align - 1) & ~(align - 1)


# =====================================================================
# Public API
# =====================================================================

@dataclass
class CompileResult:
    """Result of compiling a Vera program to WebAssembly."""

    wat: str
    wasm_bytes: bytes
    exports: list[str]
    diagnostics: list["Diagnostic"] = field(default_factory=list)
    state_types: list[tuple[str, str]] = field(default_factory=list)
    md_ops_used: set[str] = field(default_factory=set)
    regex_ops_used: set[str] = field(default_factory=set)
    map_ops_used: set[str] = field(default_factory=set)
    set_ops_used: set[str] = field(default_factory=set)
    decimal_ops_used: set[str] = field(default_factory=set)
    json_ops_used: set[str] = field(default_factory=set)
    html_ops_used: set[str] = field(default_factory=set)
    http_ops_used: set[str] = field(default_factory=set)
    inference_ops_used: set[str] = field(default_factory=set)
    random_ops_used: set[str] = field(default_factory=set)  # #465
    math_ops_used: set[str] = field(default_factory=set)  # #467
    fn_param_types: dict[str, list[str]] = field(default_factory=dict)
    # Functions whose Vera return type is `String` (after alias
    # resolution).  Used by ``execute()`` to decode the (ptr, len)
    # pair returned by such functions back into a Python `str` for
    # display purposes — without this, `vera run` on a String-returning
    # `main` printed only the heap pointer (the first half of the
    # i32_pair return), not the actual string content.  Populated in
    # `compile_program` by inspecting each FnDecl's return type
    # against the resolved alias chain.  Functions returning `Array<T>`
    # are deliberately *not* in this set — the (ptr, len) representation
    # is the same shape but the bytes-at-ptr aren't UTF-8.
    fn_string_returns: set[str] = field(default_factory=set)
    # #516 Stage 2 — runtime-trap source mapping.  Maps WAT function
    # name (without leading `$`) → (file, start_line, end_line).
    # Populated by CodeGenerator during _register_fn (top-level) and
    # the closure-lifting pass (anonymous fns become `anon_N`).
    # Consumed by execute() to resolve `wasmtime.Trap.frames` to
    # source locations for the WasmTrapError backtrace.
    fn_source_map: dict[str, tuple[str, int, int]] = field(
        default_factory=dict,
    )
    # #516 Stage 2 — positive source-of-truth for prelude / built-in
    # function classification.  Populated by the post-prelude
    # registration loop in `compile_program` (`vera/codegen/core.py`):
    # any FnDecl that wasn't registered before `inject_prelude()` ran
    # but is registered after is by definition a prelude / built-in
    # injection, not user code.  Detection is by registration-flow
    # position, NOT by `decl.span` being None — `inject_prelude`
    # calls `parse_to_ast` on inline Vera source so its synthetic
    # FnDecls do have spans (just spans pointing into that synthetic
    # source, which would land bogus coordinates in `fn_source_map`
    # if used directly).
    #
    # Consumed by `_resolve_trap_frames` alongside the runtime-helper
    # allowlist so trap frames inside prelude functions
    # (`option_unwrap_or`, ADT auto-derived methods, …) are tagged as
    # `<builtin>` rather than falling through to `<unknown>` user
    # code.  Without it the CLI's suppression-marker collapse cannot
    # fire for traps that go through prelude functions.
    prelude_fn_names: set[str] = field(default_factory=set)

    @property
    def ok(self) -> bool:
        """True if compilation succeeded with no errors."""
        return not any(d.severity == "error" for d in self.diagnostics)


@dataclass
class ExecuteResult:
    """Result of executing a WASM function."""

    # Return value: int / float for primitive returns, str for `String`
    # returns (decoded from the (ptr, len) pair so callers don't see a
    # bare heap pointer), int (the heap pointer half) for Array<T> and
    # ADT returns where element-aware formatting would be needed,
    # None for void/Unit functions.
    value: int | float | str | None
    stdout: str  # Captured IO.print output
    state: dict[str, int | float] = field(default_factory=dict)
    exit_code: int | None = None  # Set by IO.exit
    # stderr is last so the positional constructor shape pre-#463
    # (value, stdout, state, exit_code) still works for external
    # callers.  Default "" preserves backward compatibility — only
    # populated when execute(capture_stderr=True).
    stderr: str = ""
    # #573: post-execution snapshot of host-side store sizes so
    # tests can verify GC reclamation actually happened.  Populated
    # only when the corresponding store was created (i.e. when the
    # program used Map/Set/Decimal at all).  Sizes here are taken
    # *after* the program returns but *before* the linker is
    # dropped, so the dict reflects the steady-state population
    # (any wrappers the GC reclaimed via Phase 2c are already
    # gone; any survivors that were live at exit are still
    # counted).  Empty when no host stores were used.
    host_store_sizes: dict[str, int] = field(default_factory=dict)
    # #706: the exported ``$heap_ptr`` bump frontier (monotonic
    # high-water mark of bytes ever allocated) read after the program
    # returns.  Map / Set are now bucket-as-truth — their transient
    # wrappers + buckets are plain heap objects reclaimed by the
    # mark-sweep GC rather than evicted from a Python store, so the
    # reclamation tests assert this stays bounded as N scales (a
    # working free-list plateaus heap_ptr; a leak grows it linearly).
    # 0 for modules compiled without the GC runtime.
    peak_heap_bytes: int = 0


class _VeraExit(Exception):
    """Sentinel exception raised by IO.exit to abort WASM execution."""

    def __init__(self, code: int) -> None:
        self.code = code
        super().__init__(f"IO.exit({code})")


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
        "Integer arithmetic produced a value outside the i64 range "
        "`[-2^63, 2^63)`.  Add a `requires` precondition that constrains "
        "the operands so Z3 can prove the result is representable, or "
        "change the operation to a saturating / checked variant via a "
        "helper function."
    ),
    "contract_violation": "",
    "unknown": "",
}


def _classify_trap(
    exc: BaseException, last_violation: list[str]
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


# Import Diagnostic here to avoid circular imports at module level
from vera.errors import Diagnostic, SourceLocation  # noqa: E402


def compile(
    program: ast.Program,
    source: str = "",
    file: str | None = None,
    resolved_modules: list[ResolvedModule] | None = None,
) -> CompileResult:
    """Compile a type-checked Vera Program AST to WebAssembly.

    Returns a CompileResult with WAT text, WASM binary, exports,
    and any diagnostics.  The program should already have passed
    type checking and (optionally) verification.
    """
    from vera.codegen.core import CodeGenerator

    gen = CodeGenerator(
        source=source, file=file, resolved_modules=resolved_modules,
    )
    return gen.compile_program(program)


_INFERENCE_TIMEOUT: int = 60  # seconds; prevents indefinite hangs on slow providers


@dataclass(frozen=True)
class _ProviderConfig:
    """Configuration for a single LLM inference provider."""

    env_key: str         # environment variable holding the API key
    url: str             # chat completions endpoint URL
    default_model: str   # cheap/fast default when VERA_INFERENCE_MODEL is unset
    auth_style: str      # "anthropic" | "bearer"
    response_style: str  # "anthropic" | "openai"


#: Registry of supported inference providers.
#: Adding a new OpenAI-compatible provider is a one-row change here.
_PROVIDERS: dict[str, _ProviderConfig] = {
    "anthropic": _ProviderConfig(
        env_key="VERA_ANTHROPIC_API_KEY",
        url="https://api.anthropic.com/v1/messages",
        default_model="claude-haiku-4-5-20251001",
        auth_style="anthropic",
        response_style="anthropic",
    ),
    "openai": _ProviderConfig(
        env_key="VERA_OPENAI_API_KEY",
        url="https://api.openai.com/v1/chat/completions",
        default_model="gpt-4o-mini",
        auth_style="bearer",
        response_style="openai",
    ),
    "moonshot": _ProviderConfig(
        env_key="VERA_MOONSHOT_API_KEY",
        url="https://api.moonshot.ai/v1/chat/completions",
        default_model="kimi-k2-0905-preview",
        auth_style="bearer",
        response_style="openai",
    ),
    "mistral": _ProviderConfig(
        env_key="VERA_MISTRAL_API_KEY",
        url="https://api.mistral.ai/v1/chat/completions",
        default_model="mistral-small-latest",
        auth_style="bearer",
        response_style="openai",
    ),
}


def _call_inference_provider(
    provider: str,
    prompt: str,
    model: str,
    api_key: str,
) -> str:
    """Dispatch a completion request to the configured LLM provider.

    Looks up *provider* in ``_PROVIDERS``, builds the appropriate request,
    and returns the completion string.  Raises on network or API errors;
    the caller wraps the result in Ok/Err and writes it to WASM memory.
    """
    import json as _json
    import urllib.request as _urlreq

    cfg = _PROVIDERS.get(provider)
    if cfg is None:
        valid = ", ".join(sorted(_PROVIDERS))
        raise ValueError(
            f"Unknown inference provider '{provider}'. "
            f"Valid values: {valid}."
        )

    chosen_model = model or cfg.default_model

    if cfg.auth_style == "anthropic":
        headers = {
            "Content-Type": "application/json",
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
        }
        body = _json.dumps({
            "model": chosen_model,
            "max_tokens": 1024,
            "messages": [{"role": "user", "content": prompt}],
        }).encode("utf-8")
    else:  # bearer
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        }
        body = _json.dumps({
            "model": chosen_model,
            "messages": [{"role": "user", "content": prompt}],
        }).encode("utf-8")

    req = _urlreq.Request(cfg.url, data=body, headers=headers, method="POST")  # noqa: S310
    with _urlreq.urlopen(req, timeout=_INFERENCE_TIMEOUT) as resp:  # noqa: S310
        raw = resp.read()
        # #591 — strict-mode `.decode("utf-8")` previously leaked
        # the raw `UnicodeDecodeError` message (including byte
        # offsets and Python-internals jargon) into the
        # `Result::Err` string the user sees from
        # `Inference.complete`.  An LLM-API response that isn't
        # valid UTF-8 is genuinely broken — we want to fail loudly
        # but with a Vera-native message, not Python noise.
        try:
            decoded = raw.decode("utf-8")
        except UnicodeDecodeError as ude:
            raise RuntimeError(
                f"Inference provider '{provider}' returned a "
                f"response body that is not valid UTF-8 "
                f"(invalid byte at position {ude.start}).",
            ) from None
        data = _json.loads(decoded)

    if cfg.response_style == "anthropic":
        return str(data["content"][0]["text"])
    else:  # openai
        return str(data["choices"][0]["message"]["content"])


def execute(
    result: CompileResult,
    fn_name: str | None = None,
    args: list[int | float] | None = None,
    raw_args: list[str] | None = None,
    initial_state: dict[str, int | float] | None = None,
    stdin: str | None = None,
    cli_args: list[str] | None = None,
    env_vars: dict[str, str] | None = None,
    capture_stderr: bool = False,
    tee_stdout: bool = False,
) -> ExecuteResult:
    """Execute a function from a compiled WASM module.

    Uses wasmtime to instantiate the module with host bindings
    for IO and State effects.  Returns the function's return value,
    any captured stdout output, and final state values.

    Parameters
    ----------
    raw_args : list[str] | None
        Unparsed CLI string arguments to type-parse using ``result.fn_param_types``.
        Takes precedence over ``args`` when provided.
    stdin : str | None
        Input for ``IO.read_line``.  If *None*, reads from ``sys.stdin``.
    cli_args : list[str] | None
        Command-line arguments returned by ``IO.args``.
    env_vars : dict[str, str] | None
        Environment variables for ``IO.get_env``.  If *None*, uses
        ``os.environ``.
    capture_stderr : bool
        If *True*, ``IO.stderr`` writes are captured into
        ``ExecuteResult.stderr`` (an in-memory ``StringIO``) rather
        than forwarded to ``sys.stderr``.  Default ``False`` —
        matches the pre-#463 behaviour where there was no stderr.
    tee_stdout : bool
        If *True*, ``IO.print`` writes are *both* appended to the
        in-memory ``output_buf`` (so ``ExecuteResult.stdout`` and
        ``WasmTrapError.stdout`` still see every byte) *and* mirrored
        live to ``sys.stdout`` with an explicit flush per write.
        Default *False* — matches the post-#522 behaviour where the
        whole transcript is buffered until completion (correct for
        JSON mode and tests, broken for animations and TUIs).
        ``cmd_run`` text mode opts in so interactive output appears
        in real time (#543).
    """
    if not result.ok:
        raise RuntimeError("Cannot execute: compilation had errors")

    config = wasmtime.Config()
    config.wasm_exceptions = True
    engine = wasmtime.Engine(config)
    module = wasmtime.Module(engine, result.wat)
    linker = wasmtime.Linker(engine)
    store = wasmtime.Store(engine)

    # Captured output from IO.print
    output_buf = StringIO()

    # stdin buffer for IO.read_line
    stdin_buf = StringIO(stdin) if stdin is not None else None

    # stderr buffer for IO.stderr — only captured when requested
    # (default: fall through to real sys.stderr so CLI-style programs
    # see error output where they expect it).
    stderr_buf: StringIO | None = StringIO() if capture_stderr else None

    # #573: introspection hook for tests verifying GC reclamation of
    # host-side stores.  Populated by reference inside the
    # ``result.map_ops_used`` etc. branches below; we read its
    # entries' ``len()`` after the program returns and ship them
    # in ``ExecuteResult.host_store_sizes``.  Empty for programs
    # that never used Map / Set / Decimal.
    _host_store_refs: dict[str, dict[int, object]] = {}

    # -----------------------------------------------------------------
    # Memory helpers for host → WASM string/ADT allocation
    # -----------------------------------------------------------------

    def _read_wasm_string(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> str:
        """Read a UTF-8 string from WASM memory.

        Uses ``errors="replace"`` so that a corrupt (ptr, len) pair from
        an upstream codegen bug surfaces as U+FFFD replacement characters
        rather than a raw ``UnicodeDecodeError`` escaping through
        wasmtime's trampoline (#589).  Path / env-var / file-content
        consumers downstream may then surface their own "file not found"
        / "value not set" errors when the replacement chars don't match
        anything, which is a strict improvement over a Python traceback.
        """
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)  # noqa: S101
        buf = memory.data_ptr(store)
        return bytes(buf[ptr:ptr + length]).decode("utf-8", errors="replace")

    def _write_bytes(
        caller: wasmtime.Caller, offset: int, data: bytes,
    ) -> None:
        """Write raw bytes into WASM linear memory.

        Uses wasmtime's batched ``Memory.write`` (one bounds-checked
        copy) rather than a per-byte ``data_ptr`` loop: the old loop was
        O(n) Python-level assignments and turned bucket-array writes into
        an O(N²) hot path on large Map / Set chains (#706).
        """
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)  # noqa: S101
        memory.write(caller, data, offset)

    def _write_i32(
        caller: wasmtime.Caller, offset: int, value: int,
    ) -> None:
        """Write a little-endian i32 into WASM memory."""
        _write_bytes(caller, offset, struct.pack("<I", value & 0xFFFF_FFFF))

    def _call_alloc(caller: wasmtime.Caller, size: int) -> int:
        """Call the exported $alloc to allocate WASM heap memory."""
        alloc_fn = caller["alloc"]
        assert isinstance(alloc_fn, wasmtime.Func)  # noqa: S101
        ptr = alloc_fn(caller, size)
        assert isinstance(ptr, int)  # noqa: S101
        return ptr

    def _read_i32_at(caller: wasmtime.Caller, offset: int) -> int:
        """Read a little-endian i32 from WASM memory at `offset`.

        Module-factory-level counterpart to ``_write_i32`` (line ~944).
        A nested ``_read_i32`` exists later inside the decimal closures;
        this version is shared by all module-level helpers that need
        to inspect linear memory (e.g. the bucket-array
        helpers added below for #695/#705).
        """
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)  # noqa: S101
        buf = memory.data_ptr(caller)
        return int(struct.unpack_from("<I", bytes(buf[offset:offset + 4]))[0])

    def _read_bytes_at(
        caller: wasmtime.Caller, offset: int, length: int,
    ) -> bytes:
        """Read `length` raw bytes from WASM linear memory at `offset`."""
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)  # noqa: S101
        buf = memory.data_ptr(caller)
        return bytes(buf[offset:offset + length])

    # ------------------------------------------------------------------
    # #706: Map / Set bucket-array sizing
    # ------------------------------------------------------------------
    # The bucket codec itself (header + 20-byte slots) lives further
    # down near the wrapper helpers; this is just the shared minimum-
    # capacity constant.

    # Minimum bucket-array capacity.  Small enough to keep memory
    # footprint reasonable for empty / tiny maps; large enough that
    # parser-built maps with up to 4 keys avoid an immediate grow.
    # Caller is responsible for sizing up (typically ``max(_BUCKET_
    # INITIAL_CAPACITY, len(d) * 2)`` to keep linear-probe scans
    # short).
    _BUCKET_INITIAL_CAPACITY = 8

    # ------------------------------------------------------------------
    # #692: Host-side shadow-stack rooting for multi-alloc walkers
    # ------------------------------------------------------------------
    #
    # The conservative GC scan in ``$gc_collect`` (Phase 2a) only walks
    # the WASM shadow stack (``$gc_sp`` .. ``$gc_stack_limit``) when
    # tracing roots.  Host code that holds WASM heap pointers in
    # Python locals across multiple ``_call_alloc`` calls is therefore
    # invisible to GC — if one of those allocs triggers
    # ``$gc_collect`` (because bump-alloc would overflow current
    # memory), the Python-held pointers are reclaimed and the next
    # write scribbles into freed memory → free-list corruption →
    # ``Out-of-bounds memory access`` trap from inside ``$alloc``.
    # Same #570/#515/#593 bug class but on the host side.
    #
    # ``_ShadowGuard`` provides exception-safe push/pop discipline.
    # Used by ``write_html`` / ``write_json`` / markdown serde to
    # root intermediate ``arr_ptr`` / ``name_ptr`` / ``wrapper_ptr``
    # across sub-tree recursion and the final Result wrapper alloc.
    #
    # Design: ``__enter__`` snapshots the current ``$gc_sp``;
    # ``__exit__`` resets ``$gc_sp`` to that snapshot, atomically
    # popping every entry pushed within the ``with`` block — on both
    # success and exception paths.  Callers push freely without
    # counting; the outer ``with`` is the unwind boundary.

    class _ShadowGuard:
        """Push intermediate WASM heap pointers onto the GC shadow
        stack so they survive any ``$gc_collect`` that fires during
        a multi-alloc host walker.  Exception-safe — ``__exit__``
        resets ``$gc_sp`` to the entry value on both success and
        exception paths.  See #692."""

        __slots__ = ("_caller", "_sp_global", "_limit_global", "_initial_sp")

        def __init__(self, caller: wasmtime.Caller) -> None:
            self._caller = caller
            # Lookup-failure path: a host walker should never run
            # against a module that didn't export ``$gc_sp`` /
            # ``$gc_stack_limit`` (assembly.py exports both whenever
            # ``$gc_collect`` is emitted, and any host walker
            # requires the GC).  But hand-crafted ``.wat`` fixtures
            # or future host imports that bypass the codegen flow
            # could trigger the KeyError below.  Re-raise as a
            # clearer ``RuntimeError`` so the wasmtime trampoline
            # surfaces a diagnostic that names the missing exports
            # rather than a bare ``KeyError`` becoming a generic
            # "python exception" trap.
            try:
                sp_global = caller["gc_sp"]
                limit_global = caller["gc_stack_limit"]
            except KeyError as exc:
                raise RuntimeError(
                    "#692: host walker requires the module to "
                    "export `$gc_sp` and `$gc_stack_limit` (missing "
                    f"{exc}); the calling module was built without "
                    "GC support",
                ) from exc
            assert isinstance(sp_global, wasmtime.Global)  # noqa: S101
            self._sp_global = sp_global
            assert isinstance(limit_global, wasmtime.Global)  # noqa: S101
            self._limit_global = limit_global
            self._initial_sp: int | None = None

        def __enter__(self) -> "_ShadowGuard":
            sp = self._sp_global.value(self._caller)
            assert isinstance(sp, int)  # noqa: S101
            self._initial_sp = sp
            return self

        def push(self, ptr: int) -> int:
            """Push ``ptr`` onto the shadow stack.  Returns ``ptr``
            for chaining inside an assignment expression."""
            sp = self._sp_global.value(self._caller)
            limit = self._limit_global.value(self._caller)
            assert isinstance(sp, int)  # noqa: S101
            assert isinstance(limit, int)  # noqa: S101
            if sp >= limit:
                # Same diagnostic shape as the WAT-side overflow path
                # (``unreachable`` in ``gc_shadow_push``) — surface
                # as a host-side error rather than a wasmtime trap.
                raise RuntimeError(
                    f"#692: host shadow-stack overflow "
                    f"(sp={sp}, limit={limit})",
                )
            # Write i32 little-endian at [gc_sp].  Re-acquire
            # ``data_ptr`` each push because ``memory.grow`` (which
            # can fire inside ``_call_alloc``) can move the buffer.
            # Byte-by-byte indexing through the ctypes pointer
            # matches ``_write_bytes`` — ``struct.pack_into`` does
            # NOT work here because wasmtime-py's ``data_ptr``
            # returns an LP_c_ubyte, which lacks the buffer
            # protocol that ``pack_into`` requires.
            memory = self._caller["memory"]
            assert isinstance(memory, wasmtime.Memory)  # noqa: S101
            buf = memory.data_ptr(self._caller)
            packed = struct.pack("<I", ptr & 0xFFFF_FFFF)
            for i, b in enumerate(packed):
                buf[sp + i] = b
            # Advance gc_sp by 4 (i32 width).
            self._sp_global.set_value(self._caller, sp + 4)
            return ptr

        def __exit__(
            self,
            exc_type: object,
            exc_val: object,
            exc_tb: object,
        ) -> None:
            # Restore gc_sp to its entry value — atomically pops
            # everything pushed within the ``with`` block, regardless
            # of whether we're exiting normally or via exception.
            # ``__enter__`` always sets ``_initial_sp`` before
            # returning, so ``__exit__`` should always have a
            # snapshot to restore.  The assert pins the invariant —
            # if it ever fails, someone is calling ``__exit__``
            # without going through ``__enter__`` (i.e. misuse of
            # the context manager outside a ``with`` block).
            assert self._initial_sp is not None  # noqa: S101
            self._sp_global.set_value(
                self._caller, self._initial_sp,
            )

    # #573: wrapper-ADT layout constants (must match
    # ``vera/wasm/calls_containers.py``).  Tag values are picked
    # well outside the user-ADT tag range as a debugging aid; the
    # wrap-table is the source of truth for "is this object a
    # wrapper", so a tag collision wouldn't cause incorrect
    # destructor firing.
    _WRAP_KIND_MAP = 1
    _WRAP_KIND_SET = 2
    _WRAP_KIND_DECIMAL = 3
    _MAP_HANDLE_TAG = 0xFEEDC001
    _SET_HANDLE_TAG = 0xFEEDC002
    _DECIMAL_HANDLE_TAG = 0xFEEDC003
    _KIND_TO_TAG_API = {
        _WRAP_KIND_MAP: _MAP_HANDLE_TAG,
        _WRAP_KIND_SET: _SET_HANDLE_TAG,
        _WRAP_KIND_DECIMAL: _DECIMAL_HANDLE_TAG,
    }
    # #695/#706: 12-byte wrapper with a ``bucket_ptr`` field at +8.
    # Layout depends on the type:
    #   +0  tag (i32)                                 [#573]
    #   +4  Decimal: handle | 0x80000000 (bit-31)     [#578]
    #       Map / Set: vestigial (0) — no handle post-#706
    #   +8  bucket_ptr (i32, real heap pointer or 0)  [#695/#706]
    #
    # #706: for Map / Set the ``bucket_ptr`` points to the WASM-side
    # bucket that IS the map / set (see ``_alloc_bucket`` and the codec
    # below); the host imports read and rebuild it directly — there is
    # no ``_map_store`` / ``_set_store`` mirror.  Decimal leaves it 0
    # (value-typed) and the conservative scan skips 0 as
    # out-of-heap-range.  Must agree with ``_WRAPPER_BODY_SIZE`` in
    # ``vera/wasm/calls_containers.py``.
    _WRAPPER_BODY_SIZE = 12

    def _call_register_wrapper(
        caller: wasmtime.Caller, ptr: int, kind: int, handle: int,
    ) -> None:
        """Register a wrapper ADT with the WASM-side wrap table.

        Calls the exported ``$register_wrapper`` so Phase 2c of
        ``$gc_collect`` will fire ``host_decref_handle(kind, handle)``
        when ``ptr`` becomes unreachable.  No-op when the WAT
        module didn't enable the wrap table (i.e. no Map / Set /
        Decimal use); host-side JSON / HTML parsers can call this
        unconditionally and it'll just skip.
        """
        register_fn = caller["register_wrapper"]
        if register_fn is None:  # pragma: no cover — wrap table disabled
            return
        assert isinstance(register_fn, wasmtime.Func)  # noqa: S101
        register_fn(caller, ptr, kind, handle)

    def _wrap_handle(
        caller: wasmtime.Caller, kind: int, raw_handle: int,
    ) -> int:
        """Wrap an existing host handle into a GC-tracked ADT (#573;
        Decimal-only post-#706).

        Allocates a 12-byte wrapper ADT in WASM memory (tag at
        body[0], handle at body[4]), registers with the wrap
        table, and returns the wrapper pointer.  Used by host
        helpers that have already allocated their store entry
        and need to lift the resulting handle to a wrapper
        pointer before storing in a user-visible structure (e.g.
        ``decimal_from_string`` wrapping its Decimal handle
        inside an ``Option<Decimal>``'s Some payload).
        """
        tag = _KIND_TO_TAG_API.get(kind)
        if tag is None:  # pragma: no cover
            raise ValueError(f"#573: unknown wrap kind {kind}")
        body_ptr = _call_alloc(caller, _WRAPPER_BODY_SIZE)
        _write_i32(caller, body_ptr, tag)
        # #578: validate raw_handle is in the unsigned-31-bit range
        # before tagging.  See ``_validate_wrap_handle`` at module
        # scope (extracted so unit tests can exercise the 5 failure
        # modes without standing up a wasmtime instance).
        _validate_wrap_handle(raw_handle, kind, body_ptr)
        # #578: store the handle ORed with 0x80000000 so the
        # in-heap field can't be mistaken for a heap pointer by
        # the conservative GC scan.  Mirrors the WAT-side
        # ``_emit_wrap_handle`` in
        # ``vera/wasm/calls_containers.py``.  ``$register_wrapper``
        # still gets the RAW handle — the wrap table uses it for
        # ``host_decref_handle`` calls.
        _write_i32(caller, body_ptr + 4, raw_handle | 0x80000000)
        # Decimal wrappers carry no bucket (value-typed), so
        # bucket_ptr stays 0.  (``_wrap_handle`` is Decimal-only
        # post-#706; Map / Set wrappers come from ``_alloc_wrapper``
        # with a real bucket_ptr.)
        _write_i32(caller, body_ptr + 8, 0)
        _call_register_wrapper(caller, body_ptr, kind, raw_handle)
        return body_ptr

    # ------------------------------------------------------------------
    # #706: bucket-as-truth codec for Map / Set
    # ------------------------------------------------------------------
    #
    # The WASM-resident bucket array is now the SOLE source of truth
    # for Map / Set contents (``_map_store`` / ``_set_store`` deleted).
    # Host imports take the wrapper pointer, decode the bucket into a
    # transient Python dict / set, run the operation, and (for the
    # copy-on-write ops) encode a fresh wrapper + bucket.  The wrapper
    # IS the map / set value.
    #
    # Bucket region layout (grown from the 12-byte write-only mirror):
    #   header (8 bytes):  capacity (i32 @+0), count (i32 @+4)
    #   slot i at HEADER + i*20:
    #     +0  occupancy (i32: 1 = live, 0 = empty)
    #     +4  key_lo / +8  key_hi   — i64 (``<q``) / f64 (``<d``) /
    #                                  (ptr,len) for String / i32 in lo
    #     +12 val_lo / +16 val_hi   — same encoding by value tag
    #
    # The explicit occupancy flag (rather than ``key_word_0 == 0``)
    # distinguishes an empty slot from a legitimate ``0`` Int key or an
    # empty-string key (``_alloc_string("")`` → ``(0, 0)``), closing the
    # collision flagged in the #707 review.
    _BKT_HEADER = 8
    _BKT_SLOT = 20

    def _bkt_region_size(capacity: int) -> int:
        return _BKT_HEADER + capacity * _BKT_SLOT

    def _alloc_bucket(caller: wasmtime.Caller, capacity: int) -> int:
        """Allocate a zero-filled bucket region; write capacity, count=0."""
        total = _bkt_region_size(capacity)
        bucket_ptr = _call_alloc(caller, total)
        _write_bytes(caller, bucket_ptr, b"\x00" * total)
        _write_i32(caller, bucket_ptr, capacity)
        return bucket_ptr

    def _alloc_wrapper(
        caller: wasmtime.Caller, kind: int, bucket_ptr: int = 0,
    ) -> int:
        """Allocate a Map / Set wrapper ADT (#706).

        Body: tag @+0, 0 @+4 (vestigial — the host handle is gone),
        bucket_ptr @+8 (the GC-traced pointer to the bucket region).
        No wrap-table registration: Map / Set wrappers and their
        buckets are now plain heap objects reclaimed by ordinary
        mark-sweep, so the Phase 2c destructor path is Decimal-only.
        """
        body_ptr = _call_alloc(caller, _WRAPPER_BODY_SIZE)
        _write_i32(caller, body_ptr, _KIND_TO_TAG_API[kind])
        _write_i32(caller, body_ptr + 4, 0)
        _write_i32(caller, body_ptr + 8, bucket_ptr)
        return body_ptr

    def _encode_field(tag: str, value: Any) -> bytes:
        """Encode an inline (non-String) key/val into its 8-byte field."""
        if tag == "i":
            return struct.pack("<q", int(value))  # signed i64
        if tag == "f":
            return struct.pack("<d", float(value))
        # "b": Bool / Byte / ADT / heap pointer — i32 in lo, 0 in hi.
        return struct.pack("<II", int(value) & 0xFFFF_FFFF, 0)

    def _decode_field(
        caller: wasmtime.Caller, tag: str, buf: bytes, off: int,
    ) -> object:
        """Decode an 8-byte field at ``off`` within ``buf`` per tag."""
        if tag == "i":
            return int(struct.unpack_from("<q", buf, off)[0])
        if tag == "f":
            return float(struct.unpack_from("<d", buf, off)[0])
        if tag == "s":
            ptr, ln = struct.unpack_from("<II", buf, off)
            return _read_wasm_string(caller, ptr, ln) if ln else ""
        return int(struct.unpack_from("<I", buf, off)[0])

    # ------------------------------------------------------------------
    # #706: SameValueZero key/element comparison.
    # ------------------------------------------------------------------
    # Float64 keys / Set elements compare under SameValueZero (the
    # semantics native JS Map/Set use): NaN equals NaN, and +0.0 == -0.0.
    # Python's ``==`` and dict / set / list membership all treat NaN as
    # unequal to itself, so without this a NaN key can never be found,
    # removed, or deduped.  The browser runtime carries the parallel
    # ``sameValueZero`` helper.  These collapse to plain ``==`` / dict
    # ops for every non-float key, so the Int-keyed hot paths (e.g. the
    # 10K insert chain) are unaffected.
    def _is_nan(v: object) -> bool:
        return isinstance(v, float) and v != v

    def _same_value_zero(a: object, b: object) -> bool:
        return a is b or a == b or (_is_nan(a) and _is_nan(b))

    def _map_lookup(d: dict[object, object], k: object) -> object:
        """``d.get(k)`` with SameValueZero (finds a NaN key); O(1) for
        the common non-NaN case."""
        if _is_nan(k):
            return next((vv for kk, vv in d.items() if _is_nan(kk)), None)
        return d.get(k)

    def _map_put(d: dict[object, object], k: object, v: object) -> None:
        """``d[k] = v`` with SameValueZero key dedup (NaN keys collapse
        to one entry; a plain dict cannot dedup NaN)."""
        if _is_nan(k):
            for existing in [kk for kk in d if _is_nan(kk)]:
                del d[existing]
        d[k] = v

    def _set_add_svz(s: set[object], e: object) -> None:
        """``s.add(e)`` with SameValueZero dedup (at most one NaN)."""
        if _is_nan(e) and any(_is_nan(x) for x in s):
            return
        s.add(e)

    def _decode_map(
        caller: wasmtime.Caller, wrapper_ptr: int, kt: str, vt: str,
    ) -> dict[object, object]:
        """Decode a Map wrapper's bucket into a Python dict."""
        bucket_ptr = _read_i32_at(caller, wrapper_ptr + 8)
        if bucket_ptr == 0:
            return {}
        cap, count = struct.unpack(
            "<II", _read_bytes_at(caller, bucket_ptr, _BKT_HEADER),
        )
        if count == 0:
            return {}
        slots = _read_bytes_at(
            caller, bucket_ptr + _BKT_HEADER, cap * _BKT_SLOT,
        )
        d: dict[object, object] = {}
        for i in range(cap):
            base = i * _BKT_SLOT
            if struct.unpack_from("<I", slots, base)[0] == 0:
                continue
            k = _decode_field(caller, kt, slots, base + 4)
            v = _decode_field(caller, vt, slots, base + 12)
            d[k] = v
            if len(d) == count:
                break
        return d

    def _decode_set(
        caller: wasmtime.Caller, wrapper_ptr: int, et: str,
    ) -> set[object]:
        """Decode a Set wrapper's bucket into a Python set."""
        bucket_ptr = _read_i32_at(caller, wrapper_ptr + 8)
        if bucket_ptr == 0:
            return set()
        cap, count = struct.unpack(
            "<II", _read_bytes_at(caller, bucket_ptr, _BKT_HEADER),
        )
        if count == 0:
            return set()
        slots = _read_bytes_at(
            caller, bucket_ptr + _BKT_HEADER, cap * _BKT_SLOT,
        )
        s: set[object] = set()
        for i in range(cap):
            base = i * _BKT_SLOT
            if struct.unpack_from("<I", slots, base)[0] == 0:
                continue
            s.add(_decode_field(caller, et, slots, base + 4))
            if len(s) == count:
                break
        return s

    def _bkt_capacity(count: int) -> int:
        """Slot capacity for ``count`` entries, rounded UP to a power of
        two (min ``_BUCKET_INITIAL_CAPACITY``).

        Power-of-two sizing keeps the heap bounded under copy-on-write:
        consecutive inserts that land in the same size class reuse the
        just-freed bucket from the GC free list instead of bumping the
        heap frontier, so an N-element insert chain's high-water mark
        grows ~O(N) rather than ~O(N^2) (a flat ``count * 2`` produces a
        distinct, never-reused size on every insert).
        """
        want = max(_BUCKET_INITIAL_CAPACITY, count * 2)
        cap = _BUCKET_INITIAL_CAPACITY
        while cap < want:
            cap *= 2
        return cap

    def _decode_column(
        caller: wasmtime.Caller, wrapper_ptr: int, tag: str, off: int,
    ) -> list[object]:
        """Decode one field column (keys at off=4, vals at off=12).

        Returns occupied-slot values in insertion order — used by
        ``map_keys`` / ``map_values`` / ``set_to_array``, which need only
        one side of each slot and don't have both type tags in scope.
        """
        bucket_ptr = _read_i32_at(caller, wrapper_ptr + 8)
        if bucket_ptr == 0:
            return []
        cap, count = struct.unpack(
            "<II", _read_bytes_at(caller, bucket_ptr, _BKT_HEADER),
        )
        if count == 0:
            return []
        slots = _read_bytes_at(
            caller, bucket_ptr + _BKT_HEADER, cap * _BKT_SLOT,
        )
        out: list[object] = []
        for i in range(cap):
            base = i * _BKT_SLOT
            if struct.unpack_from("<I", slots, base)[0] == 0:
                continue
            out.append(_decode_field(caller, tag, slots, base + off))
            if len(out) == count:
                break
        return out

    def _bkt_count(caller: wasmtime.Caller, wrapper_ptr: int) -> int:
        """O(1) live-entry count from the bucket header (0 if empty)."""
        bucket_ptr = _read_i32_at(caller, wrapper_ptr + 8)
        if bucket_ptr == 0:
            return 0
        return _read_i32_at(caller, bucket_ptr + 4)

    def _bkt_raw_entries(
        caller: wasmtime.Caller, wrapper_ptr: int,
    ) -> "list[tuple[bytes, bytes]]":
        """Occupied slots as verbatim (key_field, val_field) byte pairs.

        Used by ``map_remove`` / ``set_remove``, which rebuild the
        collection without interpreting the value type: the 8-byte key
        and val fields are copied as-is, so String / heap-pointer blocks
        are SHARED with the source (immutable, so sharing is safe) and
        no re-encode tag is needed.
        """
        bucket_ptr = _read_i32_at(caller, wrapper_ptr + 8)
        if bucket_ptr == 0:
            return []
        cap, count = struct.unpack(
            "<II", _read_bytes_at(caller, bucket_ptr, _BKT_HEADER),
        )
        if count == 0:
            return []
        slots = _read_bytes_at(
            caller, bucket_ptr + _BKT_HEADER, cap * _BKT_SLOT,
        )
        out: list[tuple[bytes, bytes]] = []
        for i in range(cap):
            base = i * _BKT_SLOT
            if struct.unpack_from("<I", slots, base)[0] == 0:
                continue
            out.append((slots[base + 4:base + 12], slots[base + 12:base + 20]))
            if len(out) == count:
                break
        return out

    def _encode_raw(
        caller: wasmtime.Caller,
        kind: int,
        raws: "list[tuple[bytes, bytes]]",
    ) -> int:
        """Encode verbatim (key_field, val_field) pairs into a wrapper.

        No string re-allocation (fields copied as-is), so always the
        single-batched-write fast path.  Survivor heap blocks stay live
        via the source wrapper across the wrapper / bucket allocs, then
        via the new bucket after the write.
        """
        count = len(raws)
        capacity = _bkt_capacity(count)
        wrapper_ptr = _alloc_wrapper(caller, kind, 0)
        with _ShadowGuard(caller) as guard:
            guard.push(wrapper_ptr)
            bucket_ptr = _alloc_bucket(caller, capacity)
            guard.push(bucket_ptr)
            buf = bytearray(capacity * _BKT_SLOT)
            for i, (kb, vb) in enumerate(raws):
                base = i * _BKT_SLOT
                struct.pack_into("<I", buf, base, 1)
                buf[base + 4:base + 12] = kb
                buf[base + 12:base + 20] = vb
            _write_bytes(caller, bucket_ptr + _BKT_HEADER, bytes(buf))
            _write_i32(caller, bucket_ptr + 4, count)
            _write_i32(caller, wrapper_ptr + 8, bucket_ptr)  # link
        return wrapper_ptr

    def _encode_entries(
        caller: wasmtime.Caller,
        kind: int,
        entries: "list[tuple[object, object]]",
        kt: str,
        vt: str | None,
    ) -> int:
        """Encode (key, val) entries into a fresh wrapper + bucket (#706).

        ``vt`` is None for Sets (val field stays zero).  Returns the new
        wrapper pointer.  GC discipline: the new wrapper and bucket are
        shadow-rooted across the whole encode; incoming heap-pointer
        keys / values stay live via their own source's rooting for the
        duration of this synchronous host call (see plan).  FAST path
        (no String key / val) builds the whole bucket as one ``bytes``
        and emits a single ``memory.write``; SLOW path (String present)
        writes each slot in place, val-first, allocating key / val
        strings into the already-rooted bucket.
        """
        needs_string = kt == "s" or vt == "s"
        count = len(entries)
        capacity = _bkt_capacity(count)
        wrapper_ptr = _alloc_wrapper(caller, kind, 0)
        with _ShadowGuard(caller) as guard:
            guard.push(wrapper_ptr)
            bucket_ptr = _alloc_bucket(caller, capacity)
            guard.push(bucket_ptr)
            slots_base = bucket_ptr + _BKT_HEADER
            if not needs_string:
                buf = bytearray(capacity * _BKT_SLOT)
                for i, (k, v) in enumerate(entries):
                    base = i * _BKT_SLOT
                    struct.pack_into("<I", buf, base, 1)
                    buf[base + 4:base + 12] = _encode_field(kt, k)
                    if vt is not None:
                        buf[base + 12:base + 20] = _encode_field(vt, v)
                _write_bytes(caller, slots_base, bytes(buf))
            else:
                for i, (k, v) in enumerate(entries):
                    slot = slots_base + i * _BKT_SLOT
                    _write_i32(caller, slot, 1)
                    # Val first: roots a heap-pointer value before the
                    # key-string alloc can fire GC.
                    if vt == "s":
                        vp, vl = _alloc_string(caller, str(v))
                        _write_i32(caller, slot + 12, vp)
                        _write_i32(caller, slot + 16, vl)
                    elif vt is not None:
                        _write_bytes(caller, slot + 12, _encode_field(vt, v))
                    if kt == "s":
                        kp, kl = _alloc_string(caller, str(k))
                        _write_i32(caller, slot + 4, kp)
                        _write_i32(caller, slot + 8, kl)
                    else:
                        _write_bytes(caller, slot + 4, _encode_field(kt, k))
            _write_i32(caller, bucket_ptr + 4, count)  # header.count
            _write_i32(caller, wrapper_ptr + 8, bucket_ptr)  # link
        return wrapper_ptr

    def _encode_map(
        caller: wasmtime.Caller, d: dict[object, object], kt: str, vt: str,
    ) -> int:
        """Encode a Python dict into a fresh Map wrapper + bucket."""
        return _encode_entries(
            caller, _WRAP_KIND_MAP, list(d.items()), kt, vt,
        )

    def _encode_set(
        caller: wasmtime.Caller, s: set[object], et: str,
    ) -> int:
        """Encode a Python set into a fresh Set wrapper + bucket."""
        return _encode_entries(
            caller, _WRAP_KIND_SET, [(e, 0) for e in s], et, None,
        )

    def _alloc_map_wrapper(
        caller: wasmtime.Caller, d: dict[object, object],
    ) -> int:
        """Build a Map<String, V> wrapper from a host-built dict (#706).

        Used by the JSON / HTML parser paths (``write_json``'s JObject
        branch, HtmlElement attrs), whose keys are always strings.
        Bucket-as-truth: the wrapper's bucket IS the map; no
        ``_map_store`` entry.  Heap-pointer values stay reachable from
        the conservative scan via wrapper → bucket → val word, closing
        the #695 silent-UAF window.  Keys are coerced to ``str`` per
        ``write_json``'s ``map_dict[str(k)] = val`` invariant.
        """
        items: list[tuple[object, object]] = [
            (str(k), v) for k, v in d.items()
        ]
        # Value tag follows the caller: write_json's JObject values are
        # Json heap pointers (int → "b"); write_html's attrs values are
        # strings ("s").  The two callers never mix value types, so a
        # single uniform tag per map is correct.
        vt = "s" if any(isinstance(v, str) for _, v in items) else "b"
        return _encode_entries(caller, _WRAP_KIND_MAP, items, "s", vt)

    def _decode_jobject(
        caller: wasmtime.Caller, wrapper_ptr: int,
    ) -> dict[object, object]:
        """Decode a JObject's Map<String, Json> (values are Json ptrs)."""
        return _decode_map(caller, wrapper_ptr, "s", "b")

    def _decode_attrs(
        caller: wasmtime.Caller, wrapper_ptr: int,
    ) -> dict[object, object]:
        """Decode an HtmlElement's Map<String, String> attributes."""
        return _decode_map(caller, wrapper_ptr, "s", "s")

    def _alloc_string(
        caller: wasmtime.Caller, s: str,
    ) -> tuple[int, int]:
        """Allocate a string in WASM memory; returns (ptr, len)."""
        encoded = s.encode("utf-8")
        length = len(encoded)
        if length == 0:
            return (0, 0)
        ptr = _call_alloc(caller, length)
        _write_bytes(caller, ptr, encoded)
        return (ptr, length)

    def _alloc_result_ok_string(
        caller: wasmtime.Caller, s: str,
    ) -> int:
        """Allocate Result.Ok(String) on the WASM heap; returns ADT ptr."""
        str_ptr, str_len = _alloc_string(caller, s)
        # GC-rooting (folded into #706): ``str_ptr`` lives only in this
        # Python local across the struct ``_call_alloc`` below; the
        # conservative scan can't see it, so a GC there would sweep the
        # string block and we'd store a dangling pointer.  Root it across
        # the alloc; its reachability transfers to the ADT's +4 field.
        with _ShadowGuard(caller) as guard:
            if str_ptr != 0:
                guard.push(str_ptr)
            # Layout: tag(i32)=0 at +0, str_ptr(i32) at +4, str_len(i32) at +8
            adt_ptr = _call_alloc(caller, 12)
            _write_i32(caller, adt_ptr, 0)       # tag = Ok
            _write_i32(caller, adt_ptr + 4, str_ptr)
            _write_i32(caller, adt_ptr + 8, str_len)
        return adt_ptr

    def _alloc_result_err_string(
        caller: wasmtime.Caller, s: str,
    ) -> int:
        """Allocate Result.Err(String) on the WASM heap; returns ADT ptr."""
        str_ptr, str_len = _alloc_string(caller, s)
        # GC-rooting (folded into #706): see _alloc_result_ok_string —
        # root str_ptr across the struct alloc so a GC can't sweep it.
        with _ShadowGuard(caller) as guard:
            if str_ptr != 0:
                guard.push(str_ptr)
            # Layout: tag(i32)=1 at +0, str_ptr(i32) at +4, str_len(i32) at +8
            adt_ptr = _call_alloc(caller, 12)
            _write_i32(caller, adt_ptr, 1)       # tag = Err
            _write_i32(caller, adt_ptr + 4, str_ptr)
            _write_i32(caller, adt_ptr + 8, str_len)
        return adt_ptr

    def _alloc_result_ok_unit(caller: wasmtime.Caller) -> int:
        """Allocate Result.Ok(()) on the WASM heap; returns ADT ptr."""
        # Layout: tag(i32)=0 at +0, no payload
        adt_ptr = _call_alloc(caller, 4)
        _write_i32(caller, adt_ptr, 0)       # tag = Ok
        return adt_ptr

    def _alloc_option_some_string(
        caller: wasmtime.Caller, s: str,
    ) -> int:
        """Allocate Option.Some(String) on the WASM heap; returns ADT ptr."""
        str_ptr, str_len = _alloc_string(caller, s)
        # GC-rooting (folded into #706): see _alloc_result_ok_string —
        # root str_ptr across the struct alloc so a GC can't sweep it.
        with _ShadowGuard(caller) as guard:
            if str_ptr != 0:
                guard.push(str_ptr)
            # Layout: tag(i32)=1 at +0, str_ptr(i32) at +4, str_len(i32) at +8
            adt_ptr = _call_alloc(caller, 12)
            _write_i32(caller, adt_ptr, 1)       # tag = Some
            _write_i32(caller, adt_ptr + 4, str_ptr)
            _write_i32(caller, adt_ptr + 8, str_len)
        return adt_ptr

    def _alloc_option_none(caller: wasmtime.Caller) -> int:
        """Allocate Option.None on the WASM heap; returns ADT ptr."""
        # Layout: tag(i32)=0 at +0, no payload
        adt_ptr = _call_alloc(caller, 4)
        _write_i32(caller, adt_ptr, 0)       # tag = None
        return adt_ptr

    def _alloc_ordering(caller: wasmtime.Caller, tag: int) -> int:
        """Allocate an Ordering value on the WASM heap.

        Tags: 0 = Less, 1 = Equal, 2 = Greater.
        """
        adt_ptr = _call_alloc(caller, 4)
        _write_i32(caller, adt_ptr, tag)
        return adt_ptr

    def _alloc_array_of_strings(
        caller: wasmtime.Caller, strings: list[str],
    ) -> tuple[int, int]:
        """Allocate an Array<String> on the WASM heap.

        Returns (backing_ptr, count) — the WASM pair representation.
        Each element occupies 8 bytes: (i32 ptr, i32 len).
        """
        count = len(strings)
        if count == 0:
            return (0, 0)
        # GC-rooting (folded into #706): root the backing array across the
        # per-element string allocs.  It lives only in this Python local and
        # would otherwise be swept by a GC inside the loop; each element's
        # str_ptr is written into the (now rooted) backing immediately, so
        # no element pointer is ever held unrooted across an alloc.
        with _ShadowGuard(caller) as guard:
            backing_ptr = _call_alloc(caller, count * 8)
            guard.push(backing_ptr)
            for i, s in enumerate(strings):
                str_ptr, str_len = _alloc_string(caller, s)
                _write_i32(caller, backing_ptr + i * 8, str_ptr)
                _write_i32(caller, backing_ptr + i * 8 + 4, str_len)
        return (backing_ptr, count)

    def _alloc_result_ok_i32(
        caller: wasmtime.Caller, value: int,
    ) -> int:
        """Allocate Result.Ok(i32) — wraps a heap pointer in Ok."""
        # GC-rooting (folded into #706): ``value`` is a heap pointer held
        # only in this Python local across the struct alloc below; root it
        # so a GC there can't sweep the payload the caller just built (the
        # Option / Json / HtmlNode / regex match).  Harmless for the one
        # Bool caller — 0 no-ops, 1 is out of heap range.
        with _ShadowGuard(caller) as guard:
            if value != 0:
                guard.push(value)
            # Layout: tag(i32)=0 at +0, value(i32) at +4
            adt_ptr = _call_alloc(caller, 8)
            _write_i32(caller, adt_ptr, 0)       # tag = Ok
            _write_i32(caller, adt_ptr + 4, value)
        return adt_ptr

    # -----------------------------------------------------------------
    # IO host functions
    # -----------------------------------------------------------------

    # Host function: vera.print(ptr: i32, len: i32) -> ()
    def host_print(caller: wasmtime.Caller, ptr: int, length: int) -> None:
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)  # noqa: S101
        buf = memory.data_ptr(store)
        data = bytes(buf[ptr:ptr + length])
        # `errors="replace"` so an upstream codegen bug producing a
        # corrupt String (ptr, len) pair surfaces as U+FFFD characters
        # in the user's output rather than a raw Python `UnicodeDecodeError`
        # escaping through wasmtime's trampoline as a "python exception"
        # cause (#589).  A user-level program must never produce a Python
        # traceback regardless of what the program does — the WasmTrapError
        # contract from #516/#522/#547 holds here too.
        text = data.decode("utf-8", errors="replace")
        # Always capture into output_buf so ExecuteResult.stdout and
        # WasmTrapError.stdout reflect every byte the program printed
        # (the trap-preservation contract from #522 must hold even
        # when we mirror live to sys.stdout).
        output_buf.write(text)
        # tee_stdout (#543) mirrors writes live to sys.stdout with an
        # explicit flush, so animations / progress bars / TUIs see
        # output as it happens instead of one buffered burst at exit.
        if tee_stdout:
            sys.stdout.write(text)
            sys.stdout.flush()

    print_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [],
    )
    linker.define_func(
        "vera", "print", print_type, host_print, access_caller=True
    )

    # Host function: vera.read_line() -> (i32, i32)  [String pair]
    def host_read_line(caller: wasmtime.Caller) -> tuple[int, int]:
        if stdin_buf is not None:
            line = stdin_buf.readline()
        else:
            try:
                line = sys.stdin.readline()
            except EOFError:
                line = ""
        # Strip trailing newline (like getline)
        if line.endswith("\n"):
            line = line[:-1]
        return _alloc_string(caller, line)

    read_line_type = wasmtime.FuncType(
        [],
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "read_line", read_line_type,
        host_read_line, access_caller=True,
    )

    # Host function: vera.read_file(ptr, len) -> i32  [Result<String,String>]
    def host_read_file(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> int:
        path = _read_wasm_string(caller, ptr, length)
        try:
            contents = Path(path).read_text(encoding="utf-8")
            return _alloc_result_ok_string(caller, contents)
        except Exception as exc:
            return _alloc_result_err_string(caller, str(exc))

    read_file_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "read_file", read_file_type,
        host_read_file, access_caller=True,
    )

    # Host function: vera.write_file(p_ptr, p_len, d_ptr, d_len) -> i32
    # Result<Unit, String>
    def host_write_file(
        caller: wasmtime.Caller,
        p_ptr: int, p_len: int,
        d_ptr: int, d_len: int,
    ) -> int:
        path = _read_wasm_string(caller, p_ptr, p_len)
        data = _read_wasm_string(caller, d_ptr, d_len)
        try:
            Path(path).write_text(data, encoding="utf-8")
            return _alloc_result_ok_unit(caller)
        except Exception as exc:
            return _alloc_result_err_string(caller, str(exc))

    write_file_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
         wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "write_file", write_file_type,
        host_write_file, access_caller=True,
    )

    # Host function: vera.args() -> (i32, i32)  [Array<String> pair]
    def host_args(caller: wasmtime.Caller) -> tuple[int, int]:
        return _alloc_array_of_strings(caller, cli_args or [])

    args_type = wasmtime.FuncType(
        [],
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "args", args_type, host_args, access_caller=True,
    )

    # Host function: vera.exit(code: i64) -> ()
    def host_exit(_caller: wasmtime.Caller, code: int) -> None:
        raise _VeraExit(code)

    exit_type = wasmtime.FuncType(
        [wasmtime.ValType.i64()],
        [],
    )
    linker.define_func(
        "vera", "exit", exit_type, host_exit, access_caller=True,
    )

    # Host function: vera.sleep(ms: i64) -> ()
    # #463 — pause execution for `ms` milliseconds.
    #
    # Ctrl-C during the sleep raises `KeyboardInterrupt` here; it is
    # allowed to propagate.  wasmtime-py 45.0.0's trampoline
    # (`except BaseException`) unwinds the wasm call safely and
    # re-raises it at the `func(store, ...)` call site in `execute()`,
    # where the single `except KeyboardInterrupt` handler maps it to a
    # clean exit code 130 (#599).  Pre-45 this needed a per-import
    # `_VeraExit(130)` launder; see that handler for the full history.
    def host_sleep(_caller: wasmtime.Caller, ms: int) -> None:
        if ms > 0:
            time.sleep(ms / 1000.0)

    sleep_type = wasmtime.FuncType(
        [wasmtime.ValType.i64()],
        [],
    )
    linker.define_func(
        "vera", "sleep", sleep_type, host_sleep, access_caller=True,
    )

    # Host function: vera.time() -> i64  (current Unix time in ms).
    # Unit arg at the Vera level is erased at the WASM boundary, so
    # the import takes no parameters.
    def host_time(_caller: wasmtime.Caller) -> int:
        return int(time.time() * 1000)

    time_type = wasmtime.FuncType(
        [],
        [wasmtime.ValType.i64()],
    )
    linker.define_func(
        "vera", "time", time_type, host_time, access_caller=True,
    )

    # Host function: vera.stderr(ptr, len) -> ()
    # Mirrors host_print but writes to stderr instead of stdout.
    # No line terminator added — callers include \n if they want one,
    # exactly like IO.print.
    def host_stderr(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> None:
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)  # noqa: S101
        buf = memory.data_ptr(store)
        data = bytes(buf[ptr:ptr + length])
        # `errors="replace"` for the same reason as `host_print` (#589).
        text = data.decode("utf-8", errors="replace")
        if stderr_buf is not None:
            stderr_buf.write(text)
        else:
            sys.stderr.write(text)
            sys.stderr.flush()

    stderr_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [],
    )
    linker.define_func(
        "vera", "stderr", stderr_type, host_stderr, access_caller=True,
    )

    # Host function: vera.read_char() -> i32  [Result<String, String>]
    # #618 — single-character input for real-time CLI programs.
    #
    # Cross-platform shape:
    #   - Unix TTY: termios cbreak-mode context, sys.stdin.read(1),
    #     restore on exit.  Reads at most one Unicode character
    #     (sys.stdin is text mode; UTF-8 multi-byte sequences are
    #     decoded by the stream).  cbreak (not raw) keeps ISIG
    #     enabled so Ctrl-C still raises SIGINT → KeyboardInterrupt
    #     and the program can exit cleanly.
    #   - Unix non-TTY (stdin piped/redirected): no raw mode needed,
    #     just sys.stdin.read(1).  The caller's pipeline already
    #     delivers data byte-by-byte (or character-by-character for
    #     text streams).
    #   - Windows: msvcrt.getwch() (Unicode-aware; no raw-mode setup).
    #   - Test harness: stdin_buf (StringIO from execute(stdin=...))
    #     wins over real stdin, no raw mode needed.  Mirrors the
    #     host_read_line precedent for deterministic test fixtures.
    #
    # Failure modes returned as Err:
    #   - EOF (Ctrl-D on Unix, Ctrl-Z on Windows, end of piped input,
    #     empty stdin_buf): Err("EOF")
    #   - termios / msvcrt call fails (no TTY where expected, system
    #     error, restore failed): Err("<exception text>")
    #
    # KeyboardInterrupt handling: a Ctrl-C during any blocking read
    # (read(1), getwch()) raises `KeyboardInterrupt`, which is allowed
    # to propagate out of this host import.  wasmtime-py 45.0.0's
    # trampoline unwinds the wasm call safely and re-raises it at the
    # `func(store, ...)` call site in `execute()`, where the single
    # `except KeyboardInterrupt` handler maps it to a clean exit code
    # 130 (#599).  The Unix-TTY path's terminal restore lives in a
    # `finally` (below), so the terminal is always returned to its
    # original mode before the interrupt propagates — independent of
    # the interrupt handling.  The user still sees Ctrl-C terminate
    # the program cleanly (exit code 130, the conventional 128 +
    # SIGINT-2 value).
    def host_read_char(caller: wasmtime.Caller) -> int:
        # Test fixture wins first — execute(stdin="x") feeds chars
        # in order without touching real stdin / raw mode.  Uses
        # StringIO so KeyboardInterrupt is not possible here.
        if stdin_buf is not None:
            ch = stdin_buf.read(1)
            if not ch:
                return _alloc_result_err_string(caller, "EOF")
            return _alloc_result_ok_string(caller, ch)

        # Resolve the stdin fd up front so the TTY-vs-pipe check
        # below shares one fileno() call across platforms.  Each
        # host-side call wraps in `except Exception` so system
        # errors (closed stdin, monkey-patched stream without a
        # fileno, termios.error on weird devices) become Result.Err
        # rather than propagating as wasmtime traps.  `Exception`
        # deliberately excludes `KeyboardInterrupt` and `SystemExit`
        # (direct `BaseException` subclasses): a Ctrl-C must NOT be
        # swallowed into a `Result.Err` here — it has to propagate to
        # the single `except KeyboardInterrupt` handler in `execute()`
        # that maps it to exit code 130 (#599).
        try:
            fd = sys.stdin.fileno()
        except Exception as exc:
            return _alloc_result_err_string(
                caller, f"stdin.fileno() failed: {exc}",
            )

        # Non-TTY (redirected / piped) is shared across platforms:
        # a pipe is a pipe.  Important on Windows — calling
        # `msvcrt.getwch()` on redirected stdin technically works
        # via Win32's `_getch` fallback but decodes differently
        # from `sys.stdin.read(1)` (raw bytes vs Python's stdin
        # encoding).  Routing redirected stdin through
        # `sys.stdin.read(1)` on both platforms keeps the
        # encoding contract identical to the Unix path.
        if not os.isatty(fd):
            try:
                ch = sys.stdin.read(1)
            except Exception as exc:
                return _alloc_result_err_string(
                    caller, f"stdin.read failed: {exc}",
                )
            if not ch:
                return _alloc_result_err_string(caller, "EOF")
            return _alloc_result_ok_string(caller, ch)

        # TTY path forks by platform.

        # Windows TTY: msvcrt.getwch() for raw single-key reads.
        if sys.platform == "win32":
            try:
                import msvcrt  # type: ignore[import-not-found]
            except ImportError as exc:  # pragma: no cover — Windows-only
                return _alloc_result_err_string(
                    caller, f"msvcrt unavailable: {exc}",
                )
            try:
                ch = msvcrt.getwch()  # type: ignore[attr-defined]
            except Exception as exc:  # pragma: no cover — Windows-only
                return _alloc_result_err_string(
                    caller, f"getwch failed: {exc}",
                )
            if not ch:  # pragma: no cover — defensive; getwch is not
                # documented to return empty.
                return _alloc_result_err_string(caller, "EOF")
            return _alloc_result_ok_string(caller, ch)

        # Unix TTY: enter raw mode, read one char, restore.
        try:
            import termios
            import tty
        except ImportError as exc:  # pragma: no cover — unlikely on Unix
            return _alloc_result_err_string(
                caller, f"termios/tty unavailable: {exc}",
            )

        # Acquire current termios state outside the raw-mode block
        # so its failure has its own distinct error message — a
        # tcgetattr failure means raw mode never started, so
        # "raw-mode read failed" would mislead a debugger.
        try:
            old = termios.tcgetattr(fd)
        except Exception as exc:
            return _alloc_result_err_string(
                caller, f"tcgetattr failed: {exc}",
            )

        # Enter cbreak mode (NOT raw): cbreak disables ICANON and
        # ECHO (so we get one character without waiting for Enter
        # and without echoing) but PRESERVES ISIG.  With ISIG on,
        # Ctrl-C still generates SIGINT and Python turns that into
        # `KeyboardInterrupt`, which propagates (after the `finally`
        # restores the terminal) to `execute()`'s exit-130 handler.
        # `tty.setraw()` would clear ISIG, in which case Ctrl-C
        # arrives in the read buffer as the literal byte `\x03` and
        # the program never exits — exactly what a Tetris-style game
        # user would expect to NOT happen.
        #
        # The restore_exc dance below preserves both error sources
        # rather than letting one mask the other.  The inner finally
        # guarantees the restore is attempted; capturing the
        # exception (instead of swallowing) lets the post-restore
        # logic surface it iff the read itself succeeded.  If both
        # the read and the restore fail, the read error wins
        # (more actionable for debugging); the terminal may be left
        # in cbreak mode in that pathological case, but there is
        # nothing more the host can do here.
        restore_exc: Exception | None = None
        try:
            try:
                tty.setcbreak(fd)
                ch = sys.stdin.read(1)
            finally:
                # Always restore the terminal mode, even on Ctrl-C.
                # This `finally` runs before a `KeyboardInterrupt`
                # propagates, so the terminal is returned to its
                # original (canonical/echo) mode before the interrupt
                # reaches `execute()`'s exit-130 handler (#599).
                try:
                    termios.tcsetattr(fd, termios.TCSADRAIN, old)
                except Exception as exc:
                    restore_exc = exc
        except Exception as exc:
            # Read (or setcbreak) failed.  Prefer the read error
            # over any restore_exc — restore failure is less
            # actionable than the original problem.  `Exception`
            # excludes `KeyboardInterrupt`, so a Ctrl-C propagates
            # past here (terminal already restored by the `finally`)
            # to the centralized exit-130 handler in `execute()`.
            return _alloc_result_err_string(
                caller, f"raw-mode read failed: {exc}",
            )

        # Read succeeded.  If restore failed, surface it now so
        # the failure is not silently swallowed.
        if restore_exc is not None:
            return _alloc_result_err_string(
                caller, f"raw-mode restore failed: {restore_exc}",
            )

        # Ctrl-D (ASCII EOT, `\x04`) in cbreak mode arrives as a
        # literal byte rather than triggering an empty-read EOF —
        # cbreak disables ICANON, which is the line discipline
        # layer that normally turns Ctrl-D-at-start-of-line into
        # an empty read.  The user pressing Ctrl-D in a real-time
        # CLI program still means "I'm done", though, so map it
        # to EOF here.  This is the conventional Unix-TTY
        # interpretation and is restricted to this branch only:
        # piped `\x04` on the non-TTY shared path is left
        # untouched (a pipe is a byte stream, the producer chose
        # to include `\x04`), and the Windows TTY branch uses
        # `msvcrt.getwch()` which has its own end-of-input
        # semantics (Ctrl-Z `\x1A` is the Windows analog —
        # similar mapping could be added there if a regression
        # surfaces; left untouched for now).
        if not ch or ch == "\x04":
            return _alloc_result_err_string(caller, "EOF")
        return _alloc_result_ok_string(caller, ch)

    read_char_type = wasmtime.FuncType(
        [],
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "read_char", read_char_type,
        host_read_char, access_caller=True,
    )

    # Host function: vera.get_env(ptr, len) -> i32  [Option<String>]
    def host_get_env(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> int:
        name = _read_wasm_string(caller, ptr, length)
        if env_vars is not None:
            value = env_vars.get(name)
        else:
            value = os.environ.get(name)
        if value is not None:
            return _alloc_option_some_string(caller, value)
        return _alloc_option_none(caller)

    get_env_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "get_env", get_env_type,
        host_get_env, access_caller=True,
    )

    # -----------------------------------------------------------------
    # Contract violation reporting
    # -----------------------------------------------------------------

    # Host function: vera.contract_fail(ptr: i32, len: i32) -> ()
    # Stores the violation message so it can be reported on trap.
    last_violation: list[str] = []

    def host_contract_fail(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> None:
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)  # noqa: S101
        buf = memory.data_ptr(store)
        data = bytes(buf[ptr:ptr + length])
        last_violation.clear()
        # `errors="replace"` so a corrupt violation message itself
        # doesn't crash with a `UnicodeDecodeError` and mask the
        # underlying contract violation that triggered the trap (#589).
        last_violation.append(data.decode("utf-8", errors="replace"))

    contract_fail_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [],
    )
    linker.define_func(
        "vera", "contract_fail", contract_fail_type,
        host_contract_fail, access_caller=True,
    )

    # State<T> host functions
    _WASM_VAL_TYPE = {
        "i64": wasmtime.ValType.i64(),
        "i32": wasmtime.ValType.i32(),
        "f64": wasmtime.ValType.f64(),
    }
    _DEFAULT_STATE: dict[str, int | float] = {
        "i64": 0, "i32": 0, "f64": 0.0,
    }

    # Each key maps to a stack of values: push on handler entry, pop on exit.
    # This allows nested handle[State<T>] of the same type to have independent
    # state cells (#417).
    state_store: dict[str, list[int | float]] = {}

    for type_name, wasm_t in result.state_types:
        state_key = f"State_{type_name}"
        state_store[state_key] = [_DEFAULT_STATE[wasm_t]]
        val_type = _WASM_VAL_TYPE[wasm_t]

        # Closure factories to capture correct state_key per type
        def _make_host_get(key: str):  # type: ignore[no-untyped-def]
            def host_get() -> int | float:
                return state_store[key][-1]
            return host_get

        def _make_host_put(key: str):  # type: ignore[no-untyped-def]
            def host_put(val: int | float) -> None:
                state_store[key][-1] = val
            return host_put

        def _make_host_push(key: str, default: int | float):  # type: ignore[no-untyped-def]
            def host_push() -> None:
                state_store[key].append(default)
            return host_push

        def _make_host_pop(key: str):  # type: ignore[no-untyped-def]
            def host_pop() -> None:
                if len(state_store[key]) > 1:
                    state_store[key].pop()
            return host_pop

        get_type = wasmtime.FuncType([], [val_type])
        linker.define_func(
            "vera", f"state_get_{type_name}", get_type,
            _make_host_get(state_key),
        )

        put_type = wasmtime.FuncType([val_type], [])
        linker.define_func(
            "vera", f"state_put_{type_name}", put_type,
            _make_host_put(state_key),
        )

        push_type = wasmtime.FuncType([], [])
        linker.define_func(
            "vera", f"state_push_{type_name}", push_type,
            _make_host_push(state_key, _DEFAULT_STATE[wasm_t]),
        )

        pop_type = wasmtime.FuncType([], [])
        linker.define_func(
            "vera", f"state_pop_{type_name}", pop_type,
            _make_host_pop(state_key),
        )

    # Apply initial state overrides (for testing)
    if initial_state:
        for key, val in initial_state.items():
            if key in state_store:
                state_store[key][-1] = val

    # -----------------------------------------------------------------
    # Markdown host functions (§9.7.3)
    # -----------------------------------------------------------------

    if result.md_ops_used:
        from vera.markdown import (
            extract_code_blocks as _md_extract_code_blocks,
            has_code_block as _md_has_code_block,
            has_heading as _md_has_heading,
            parse_markdown as _md_parse,
            render_markdown as _md_render,
        )
        from vera.wasm.markdown import (
            read_md_block,
            write_md_block,
        )

        # md_parse(ptr, len) → i32 (Result<MdBlock, String>)
        def host_md_parse(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            text = _read_wasm_string(caller, ptr, length)
            # Parse errors are user-domain — convert to Result.Err.
            # The shadow-stack work + write_md_block + Result.Ok
            # alloc are deliberately OUTSIDE this except so host-
            # side invariant violations (shadow-stack overflow
            # from _ShadowGuard, unknown-tag ValueError from
            # write_md_block's exhaustive match, AssertionErrors
            # from internal bugs) propagate as wasmtime traps
            # rather than being swallowed as parse errors.
            # Matches the parse-only-in-try structure of
            # host_html_parse and host_json_parse (both narrow
            # their catch around only the parse call, with
            # _ShadowGuard usage outside).
            try:
                doc = _md_parse(text)
            except Exception as exc:
                return _alloc_result_err_string(caller, str(exc))
            # #692: same shadow-stack-rooting concern as
            # ``host_html_parse`` / ``host_json_parse``.
            # write_md_block holds intermediate pointers (string
            # bodies, child-array backings) in Python locals
            # across many sub-allocs; ``guard`` keeps them
            # visible to the conservative GC scan.
            with _ShadowGuard(caller) as guard:
                block_ptr = write_md_block(
                    caller, _call_alloc, _write_i32,
                    _write_bytes, _alloc_string, guard, doc,
                )
                guard.push(block_ptr)
                return _alloc_result_ok_i32(caller, block_ptr)

        md_parse_type = wasmtime.FuncType(
            [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
            [wasmtime.ValType.i32()],
        )
        linker.define_func(
            "vera", "md_parse", md_parse_type,
            host_md_parse, access_caller=True,
        )

        # md_render(ptr) → (i32, i32) (String pair)
        def host_md_render(
            caller: wasmtime.Caller, ptr: int,
        ) -> tuple[int, int]:
            block = read_md_block(caller, ptr)
            text = _md_render(block)
            return _alloc_string(caller, text)

        md_render_type = wasmtime.FuncType(
            [wasmtime.ValType.i32()],
            [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        )
        linker.define_func(
            "vera", "md_render", md_render_type,
            host_md_render, access_caller=True,
        )

        # md_has_heading(ptr, level_i64) → i32 (Bool)
        def host_md_has_heading(
            caller: wasmtime.Caller, ptr: int, level: int,
        ) -> int:
            block = read_md_block(caller, ptr)
            return 1 if _md_has_heading(block, level) else 0

        md_has_heading_type = wasmtime.FuncType(
            [wasmtime.ValType.i32(), wasmtime.ValType.i64()],
            [wasmtime.ValType.i32()],
        )
        linker.define_func(
            "vera", "md_has_heading", md_has_heading_type,
            host_md_has_heading, access_caller=True,
        )

        # md_has_code_block(ptr, lang_ptr, lang_len) → i32 (Bool)
        def host_md_has_code_block(
            caller: wasmtime.Caller,
            ptr: int, lang_ptr: int, lang_len: int,
        ) -> int:
            block = read_md_block(caller, ptr)
            lang = _read_wasm_string(caller, lang_ptr, lang_len)
            return 1 if _md_has_code_block(block, lang) else 0

        md_has_code_block_type = wasmtime.FuncType(
            [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
             wasmtime.ValType.i32()],
            [wasmtime.ValType.i32()],
        )
        linker.define_func(
            "vera", "md_has_code_block", md_has_code_block_type,
            host_md_has_code_block, access_caller=True,
        )

        # md_extract_code_blocks(ptr, lang_ptr, lang_len) → (i32, i32)
        def host_md_extract_code_blocks(
            caller: wasmtime.Caller,
            ptr: int, lang_ptr: int, lang_len: int,
        ) -> tuple[int, int]:
            block = read_md_block(caller, ptr)
            lang = _read_wasm_string(caller, lang_ptr, lang_len)
            codes = _md_extract_code_blocks(block, lang)
            return _alloc_array_of_strings(caller, codes)

        md_extract_type = wasmtime.FuncType(
            [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
             wasmtime.ValType.i32()],
            [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        )
        linker.define_func(
            "vera", "md_extract_code_blocks", md_extract_type,
            host_md_extract_code_blocks, access_caller=True,
        )

    # -----------------------------------------------------------------
    # Regex host functions (§9.6.15)
    # -----------------------------------------------------------------

    if result.regex_ops_used:
        import re as _re

        def host_regex_match(
            caller: wasmtime.Caller,
            in_ptr: int, in_len: int, pat_ptr: int, pat_len: int,
        ) -> int:
            input_str = _read_wasm_string(caller, in_ptr, in_len)
            pattern = _read_wasm_string(caller, pat_ptr, pat_len)
            try:
                matched = _re.search(pattern, input_str) is not None
                return _alloc_result_ok_i32(caller, 1 if matched else 0)
            except _re.error as exc:
                return _alloc_result_err_string(
                    caller, f"invalid regex: {exc}",
                )

        regex_match_type = wasmtime.FuncType(
            [wasmtime.ValType.i32()] * 4,
            [wasmtime.ValType.i32()],
        )
        linker.define_func(
            "vera", "regex_match", regex_match_type,
            host_regex_match, access_caller=True,
        )

        def host_regex_find(
            caller: wasmtime.Caller,
            in_ptr: int, in_len: int, pat_ptr: int, pat_len: int,
        ) -> int:
            input_str = _read_wasm_string(caller, in_ptr, in_len)
            pattern = _read_wasm_string(caller, pat_ptr, pat_len)
            try:
                m = _re.search(pattern, input_str)
                if m:
                    option_ptr = _alloc_option_some_string(
                        caller, m.group(0),
                    )
                else:
                    option_ptr = _alloc_option_none(caller)
                return _alloc_result_ok_i32(caller, option_ptr)
            except _re.error as exc:
                return _alloc_result_err_string(
                    caller, f"invalid regex: {exc}",
                )

        regex_find_type = wasmtime.FuncType(
            [wasmtime.ValType.i32()] * 4,
            [wasmtime.ValType.i32()],
        )
        linker.define_func(
            "vera", "regex_find", regex_find_type,
            host_regex_find, access_caller=True,
        )

        def host_regex_find_all(
            caller: wasmtime.Caller,
            in_ptr: int, in_len: int, pat_ptr: int, pat_len: int,
        ) -> int:
            input_str = _read_wasm_string(caller, in_ptr, in_len)
            pattern = _read_wasm_string(caller, pat_ptr, pat_len)
            try:
                # Use finditer + group(0) to always get full match
                # strings, even when the pattern has capture groups.
                matches = [
                    m.group(0)
                    for m in _re.finditer(pattern, input_str)
                ]
                backing_ptr, count = _alloc_array_of_strings(
                    caller, matches,
                )
                # GC-rooting (folded into #706): root backing_ptr across
                # the Result.Ok struct alloc so a GC can't sweep it.
                with _ShadowGuard(caller) as guard:
                    if backing_ptr != 0:
                        guard.push(backing_ptr)
                    # Wrap in Result.Ok: tag=0, backing_ptr, count (12 bytes)
                    adt_ptr = _call_alloc(caller, 12)
                    _write_i32(caller, adt_ptr, 0)            # tag = Ok
                    _write_i32(caller, adt_ptr + 4, backing_ptr)
                    _write_i32(caller, adt_ptr + 8, count)
                return adt_ptr
            except _re.error as exc:
                return _alloc_result_err_string(
                    caller, f"invalid regex: {exc}",
                )

        regex_find_all_type = wasmtime.FuncType(
            [wasmtime.ValType.i32()] * 4,
            [wasmtime.ValType.i32()],
        )
        linker.define_func(
            "vera", "regex_find_all", regex_find_all_type,
            host_regex_find_all, access_caller=True,
        )

        def host_regex_replace(
            caller: wasmtime.Caller,
            in_ptr: int, in_len: int,
            pat_ptr: int, pat_len: int,
            rep_ptr: int, rep_len: int,
        ) -> int:
            input_str = _read_wasm_string(caller, in_ptr, in_len)
            pattern = _read_wasm_string(caller, pat_ptr, pat_len)
            replacement = _read_wasm_string(caller, rep_ptr, rep_len)
            try:
                result_str = _re.sub(
                    pattern, replacement, input_str, count=1,
                )
                return _alloc_result_ok_string(caller, result_str)
            except _re.error as exc:
                return _alloc_result_err_string(
                    caller, f"invalid regex: {exc}",
                )

        regex_replace_type = wasmtime.FuncType(
            [wasmtime.ValType.i32()] * 6,
            [wasmtime.ValType.i32()],
        )
        linker.define_func(
            "vera", "regex_replace", regex_replace_type,
            host_regex_replace, access_caller=True,
        )

    # -----------------------------------------------------------------
    # Shared helpers for Map<K, V> and Set<T> host functions
    # -----------------------------------------------------------------

    # Shared helpers for collection host functions (Map and Set).
    # Defined once, used by both Map and Set sections below.
    if (result.map_ops_used or result.set_ops_used
            or result.decimal_ops_used or result.json_ops_used
            or result.html_ops_used):
        def _write_i64(
            caller: wasmtime.Caller, offset: int, value: int,
        ) -> None:
            _write_bytes(
                caller, offset,
                struct.pack("<q", value),
            )

        def _write_f64(
            caller: wasmtime.Caller, offset: int, value: float,
        ) -> None:
            _write_bytes(
                caller, offset,
                struct.pack("<d", value),
            )

        def _read_i32(caller: wasmtime.Caller, offset: int) -> int:
            """Read a little-endian i32 from WASM memory."""
            memory = caller["memory"]
            assert isinstance(memory, wasmtime.Memory)  # noqa: S101
            buf = memory.data_ptr(caller)
            val: int = struct.unpack_from(
                "<I", bytes(buf[offset:offset + 4]),
            )[0]
            return val

        def _read_f64(caller: wasmtime.Caller, offset: int) -> float:
            """Read a little-endian f64 from WASM memory."""
            memory = caller["memory"]
            assert isinstance(memory, wasmtime.Memory)  # noqa: S101
            buf = memory.data_ptr(caller)
            val: float = struct.unpack_from(
                "<d", bytes(buf[offset:offset + 8]),
            )[0]
            return val

        def _alloc_option_some_i64(
            caller: wasmtime.Caller, value: int,
        ) -> int:
            """Option.Some wrapping an i64 value.

            Layout: tag(i32) at +0, padding at +4, payload(i64) at +8.
            Total 16 bytes (i64 aligned to 8-byte boundary).
            """
            adt_ptr = _call_alloc(caller, 16)
            _write_i32(caller, adt_ptr, 1)  # tag = Some
            _write_i64(caller, adt_ptr + 8, value)
            return adt_ptr

        def _alloc_option_some_i32(
            caller: wasmtime.Caller, value: int,
        ) -> int:
            """Option.Some wrapping an i32 value."""
            # GC-rooting (folded into #706): root a heap-pointer payload
            # (e.g. a Decimal wrapper from decimal_from_string /
            # decimal_div) across the struct alloc.  Harmless for
            # non-pointer i32 values — 0 no-ops, small ints are out of
            # heap range.  Mirrors _alloc_result_ok_i32.
            with _ShadowGuard(caller) as guard:
                if value != 0:
                    guard.push(value)
                adt_ptr = _call_alloc(caller, 8)
                _write_i32(caller, adt_ptr, 1)  # tag = Some
                _write_i32(caller, adt_ptr + 4, value)
            return adt_ptr

        def _alloc_option_some_f64(
            caller: wasmtime.Caller, value: float,
        ) -> int:
            """Option.Some wrapping an f64 value.

            Layout: tag(i32) at +0, padding at +4, payload(f64) at +8.
            Total 16 bytes (f64 aligned to 8-byte boundary).
            """
            adt_ptr = _call_alloc(caller, 16)
            _write_i32(caller, adt_ptr, 1)  # tag = Some
            _write_f64(caller, adt_ptr + 8, value)
            return adt_ptr

        def _alloc_array_of_i64(
            caller: wasmtime.Caller, values: list[int],
        ) -> tuple[int, int]:
            """Allocate Array<Int/Nat> — each element is 8 bytes."""
            count = len(values)
            if count == 0:
                return (0, 0)
            ptr = _call_alloc(caller, count * 8)
            for i, v in enumerate(values):
                _write_i64(caller, ptr + i * 8, v)
            return (ptr, count)

        def _alloc_array_of_i32(
            caller: wasmtime.Caller, values: list[int],
        ) -> tuple[int, int]:
            """Allocate Array<Bool/Byte/ADT> — each element is 4 bytes."""
            count = len(values)
            if count == 0:
                return (0, 0)
            ptr = _call_alloc(caller, count * 4)
            for i, v in enumerate(values):
                _write_i32(caller, ptr + i * 4, v)
            return (ptr, count)

        def _alloc_array_of_f64(
            caller: wasmtime.Caller, values: list[float],
        ) -> tuple[int, int]:
            """Allocate Array<Float64> — each element is 8 bytes."""
            count = len(values)
            if count == 0:
                return (0, 0)
            ptr = _call_alloc(caller, count * 8)
            for i, v in enumerate(values):
                _write_f64(caller, ptr + i * 8, v)
            return (ptr, count)

        _VAL_WASM_TYPES = {
            "i": [wasmtime.ValType.i64()],
            "f": [wasmtime.ValType.f64()],
            "b": [wasmtime.ValType.i32()],
            "s": [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        }

    # -----------------------------------------------------------------
    # Map<K, V> host functions
    # -----------------------------------------------------------------

    # #573 / #706: Phase 2c destructor host import.  Only Decimal keeps
    # a value-typed Python store and registers its wrappers with the
    # wrap table; Map / Set are now bucket-as-truth (plain heap objects
    # reclaimed by ordinary mark-sweep, no store, no registration).  The
    # import stays gated on the broad predicate so it is defined for any
    # program that might declare it on the WAT side; the body only
    # evicts Decimal handles.
    _decref_used = (
        result.map_ops_used or result.set_ops_used
        or result.decimal_ops_used
        or result.json_ops_used or result.html_ops_used
    )
    if _decref_used:
        def host_decref_handle(
            _caller: wasmtime.Caller, kind: int, handle: int,
        ) -> None:
            # #706: only Decimal (kind=3) keeps a Python store to evict.
            # Map (1) / Set (2) are bucket-as-truth — no store entry, and
            # their wrappers are not registered with the wrap table, so
            # Phase 2c never fires for them.  Other kinds: silent no-op.
            if kind == 3 and result.decimal_ops_used:
                _decimal_store.pop(handle, None)

        linker.define_func(
            "vera", "host_decref_handle",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [],
            ),
            host_decref_handle, access_caller=True,
        )

        # #706: attach_bucket_to_wrapper no longer populates a bucket.
        # Map / Set wrappers carry their bucket directly (bucket-as-truth)
        # and Decimal is value-typed, so nothing needs a bucket attached.
        # The import stays defined because Decimal's ``_emit_wrap_handle``
        # still emits a call to it; the body is a tripwire asserting only
        # Decimal (kind=3) reaches this path, so a regression that routes a
        # Map / Set wrapper back through ``_emit_wrap_handle`` fails loudly
        # here instead of silently leaving its bucket unpopulated.
        def host_attach_bucket(
            _caller: wasmtime.Caller, _wrapper_ptr: int, kind: int,
            _handle: int,
        ) -> None:
            # Only Decimal (kind=3) should reach this no-op path; Map (1)
            # and Set (2) are bucket-as-truth and never wrap a handle.
            if kind != 3:
                raise RuntimeError(
                    f"#706: attach_bucket_to_wrapper called with kind={kind}; "
                    "expected Decimal (3).  A Map/Set wrapper was routed back "
                    "through _emit_wrap_handle — the bucket-as-truth invariant "
                    "is violated."
                )

        linker.define_func(
            "vera", "attach_bucket_to_wrapper",
            wasmtime.FuncType(
                [
                    wasmtime.ValType.i32(),  # wrapper_ptr
                    wasmtime.ValType.i32(),  # kind
                    wasmtime.ValType.i32(),  # handle
                ],
                [],
            ),
            host_attach_bucket, access_caller=True,
        )

    if result.map_ops_used:

        # map_new() → wrapper_ptr for an empty bucket-as-truth Map (#706).
        def host_map_new(caller: wasmtime.Caller) -> int:
            return _alloc_wrapper(caller, _WRAP_KIND_MAP, 0)

        linker.define_func(
            "vera", "map_new",
            wasmtime.FuncType([], [wasmtime.ValType.i32()]),
            host_map_new, access_caller=True,
        )

        # #706: every Map host import now takes the wrapper pointer
        # (``wp``) instead of an opaque handle, decodes the wrapper's
        # bucket into a transient Python dict, runs the operation, and —
        # for the copy-on-write ops — encodes a fresh wrapper + bucket.

        def _define_map_insert(kt: str, vt: str) -> None:
            name = f"map_insert$k{kt}_v{vt}"
            key_types = _VAL_WASM_TYPES[kt]
            val_types = _VAL_WASM_TYPES[vt]
            param_types = (
                [wasmtime.ValType.i32()]  # wrapper_ptr
                + key_types + val_types
            )
            ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

            if kt == "s" and vt == "s":
                def host_fn(
                    caller: wasmtime.Caller,
                    wp: int, kp: int, kl: int, vp: int, vl: int,
                ) -> int:
                    k = _read_wasm_string(caller, kp, kl)
                    v = _read_wasm_string(caller, vp, vl)
                    new_d = _decode_map(caller, wp, kt, vt)
                    _map_put(new_d, k, v)
                    return _encode_map(caller, new_d, kt, vt)
            elif kt == "s":
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller,
                    wp: int, kp: int, kl: int, v: int | float,
                ) -> int:
                    k = _read_wasm_string(caller, kp, kl)
                    new_d = _decode_map(caller, wp, kt, vt)
                    _map_put(new_d, k, v)
                    return _encode_map(caller, new_d, kt, vt)
            elif vt == "s":
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller,
                    wp: int, k: int | float, vp: int, vl: int,
                ) -> int:
                    v = _read_wasm_string(caller, vp, vl)
                    new_d = _decode_map(caller, wp, kt, vt)
                    _map_put(new_d, k, v)
                    return _encode_map(caller, new_d, kt, vt)
            else:
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller,
                    wp: int, k: int | float, v: int | float,
                ) -> int:
                    new_d = _decode_map(caller, wp, kt, vt)
                    _map_put(new_d, k, v)
                    return _encode_map(caller, new_d, kt, vt)

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        def _define_map_get(kt: str, vt: str) -> None:
            name = f"map_get$k{kt}_v{vt}"
            key_types = _VAL_WASM_TYPES[kt]
            param_types = [wasmtime.ValType.i32()] + key_types
            ftype = wasmtime.FuncType(
                param_types, [wasmtime.ValType.i32()],
            )

            def _make_option(
                caller: wasmtime.Caller, val: object,
            ) -> int:
                """Construct Option<V> on the WASM heap."""
                if val is None:
                    return _alloc_option_none(caller)
                if vt == "i":
                    assert isinstance(val, int)  # noqa: S101
                    return _alloc_option_some_i64(caller, val)
                if vt == "f":
                    assert isinstance(val, (int, float))  # noqa: S101
                    return _alloc_option_some_f64(caller, float(val))
                if vt == "s":
                    assert isinstance(val, str)  # noqa: S101
                    return _alloc_option_some_string(caller, val)
                # i32 (Bool, Byte, ADT, Map handle)
                assert isinstance(val, int)  # noqa: S101
                return _alloc_option_some_i32(caller, val)

            if kt == "s":
                def host_fn(
                    caller: wasmtime.Caller,
                    wp: int, kp: int, kl: int,
                ) -> int:
                    k = _read_wasm_string(caller, kp, kl)
                    d = _decode_map(caller, wp, kt, vt)
                    return _make_option(caller, _map_lookup(d, k))
            else:
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller,
                    wp: int, k: int | float,
                ) -> int:
                    d = _decode_map(caller, wp, kt, vt)
                    return _make_option(caller, _map_lookup(d, k))

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        def _define_map_contains(kt: str) -> None:
            name = f"map_contains$k{kt}"
            key_types = _VAL_WASM_TYPES[kt]
            param_types = [wasmtime.ValType.i32()] + key_types
            ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

            if kt == "s":
                def host_fn(
                    caller: wasmtime.Caller,
                    wp: int, kp: int, kl: int,
                ) -> int:
                    k = _read_wasm_string(caller, kp, kl)
                    return 1 if any(
                        _same_value_zero(k, x)
                        for x in _decode_column(caller, wp, kt, 4)
                    ) else 0
            else:
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller,
                    wp: int, k: int | float,
                ) -> int:
                    return 1 if any(
                        _same_value_zero(k, x)
                        for x in _decode_column(caller, wp, kt, 4)
                    ) else 0

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        def _define_map_remove(kt: str) -> None:
            name = f"map_remove$k{kt}"
            key_types = _VAL_WASM_TYPES[kt]
            param_types = [wasmtime.ValType.i32()] + key_types
            ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

            # Structural rebuild: drop the matching key's slot and copy the
            # rest verbatim (vt not needed — value fields are opaque here).
            def _without(
                caller: wasmtime.Caller, wp: int, k: object,
            ) -> int:
                survivors = [
                    (kb, vb)
                    for kb, vb in _bkt_raw_entries(caller, wp)
                    if not _same_value_zero(_decode_field(caller, kt, kb, 0), k)
                ]
                return _encode_raw(caller, _WRAP_KIND_MAP, survivors)

            if kt == "s":
                def host_fn(
                    caller: wasmtime.Caller,
                    wp: int, kp: int, kl: int,
                ) -> int:
                    return _without(caller, wp, _read_wasm_string(caller, kp, kl))
            else:
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller,
                    wp: int, k: int | float,
                ) -> int:
                    return _without(caller, wp, k)

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        # map_size(wp) → i64 (O(1) from the bucket header).
        def host_map_size(
            caller: wasmtime.Caller, wp: int,
        ) -> int:
            return _bkt_count(caller, wp)

        linker.define_func(
            "vera", "map_size",
            wasmtime.FuncType(
                [wasmtime.ValType.i32()], [wasmtime.ValType.i64()],
            ),
            host_map_size, access_caller=True,
        )

        def _define_map_keys(kt: str) -> None:
            name = f"map_keys$k{kt}"
            ftype = wasmtime.FuncType(
                [wasmtime.ValType.i32()],
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
            )

            def host_fn(
                caller: wasmtime.Caller, wp: int,
            ) -> tuple[int, int]:
                keys = _decode_column(caller, wp, kt, 4)
                if kt == "s":
                    return _alloc_array_of_strings(caller, keys)  # type: ignore[arg-type]
                if kt == "i":
                    return _alloc_array_of_i64(caller, keys)  # type: ignore[arg-type]
                if kt == "f":
                    return _alloc_array_of_f64(caller, keys)  # type: ignore[arg-type]
                return _alloc_array_of_i32(caller, keys)  # type: ignore[arg-type]

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        def _define_map_values(vt: str) -> None:
            name = f"map_values$v{vt}"
            ftype = wasmtime.FuncType(
                [wasmtime.ValType.i32()],
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
            )

            def host_fn(
                caller: wasmtime.Caller, wp: int,
            ) -> tuple[int, int]:
                vals = _decode_column(caller, wp, vt, 12)
                if vt == "s":
                    return _alloc_array_of_strings(caller, vals)  # type: ignore[arg-type]
                if vt == "i":
                    return _alloc_array_of_i64(caller, vals)  # type: ignore[arg-type]
                if vt == "f":
                    return _alloc_array_of_f64(caller, vals)  # type: ignore[arg-type]
                return _alloc_array_of_i32(caller, vals)  # type: ignore[arg-type]

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        # Register type-specific imports based on what the WAT uses.
        # Parse the import names from map_ops_used to determine types.
        for op_name in result.map_ops_used:
            if op_name.startswith("map_insert$"):
                # e.g. "map_insert$ki_vi"
                suffix = op_name[len("map_insert$"):]
                kt = suffix[1]  # after 'k'
                vt = suffix[4]  # after '_v'
                _define_map_insert(kt, vt)
            elif op_name.startswith("map_get$"):
                suffix = op_name[len("map_get$"):]
                kt = suffix[1]
                vt = suffix[4]
                _define_map_get(kt, vt)
            elif op_name.startswith("map_contains$"):
                suffix = op_name[len("map_contains$"):]
                kt = suffix[1]
                _define_map_contains(kt)
            elif op_name.startswith("map_remove$"):
                suffix = op_name[len("map_remove$"):]
                kt = suffix[1]
                _define_map_remove(kt)
            elif op_name.startswith("map_keys$"):
                suffix = op_name[len("map_keys$"):]
                kt = suffix[1]
                _define_map_keys(kt)
            elif op_name.startswith("map_values$"):
                suffix = op_name[len("map_values$"):]
                vt = suffix[1]
                _define_map_values(vt)

    # -----------------------------------------------------------------
    # Set<T> host functions
    # -----------------------------------------------------------------

    if result.set_ops_used:
        # set_new() → wrapper_ptr for an empty bucket-as-truth Set (#706).
        def host_set_new(caller: wasmtime.Caller) -> int:
            return _alloc_wrapper(caller, _WRAP_KIND_SET, 0)

        linker.define_func(
            "vera", "set_new",
            wasmtime.FuncType([], [wasmtime.ValType.i32()]),
            host_set_new, access_caller=True,
        )

        # #706: every Set host import takes the wrapper pointer (``wp``)
        # and goes through the bucket codec — the element lives in the
        # slot's key field, the val field is unused.

        def _define_set_add(et: str) -> None:
            name = f"set_add$e{et}"
            elem_types = _VAL_WASM_TYPES[et]
            param_types = [wasmtime.ValType.i32()] + elem_types
            ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

            if et == "s":
                def host_fn(
                    caller: wasmtime.Caller, wp: int, ep: int, el: int,
                ) -> int:
                    s = _decode_set(caller, wp, et)
                    _set_add_svz(s, _read_wasm_string(caller, ep, el))
                    return _encode_set(caller, s, et)
            else:
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller, wp: int, e: int | float,
                ) -> int:
                    s = _decode_set(caller, wp, et)
                    _set_add_svz(s, e)
                    return _encode_set(caller, s, et)

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        def _define_set_contains(et: str) -> None:
            name = f"set_contains$e{et}"
            elem_types = _VAL_WASM_TYPES[et]
            param_types = [wasmtime.ValType.i32()] + elem_types
            ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

            if et == "s":
                def host_fn(
                    caller: wasmtime.Caller, wp: int, ep: int, el: int,
                ) -> int:
                    e = _read_wasm_string(caller, ep, el)
                    return 1 if any(
                        _same_value_zero(e, x)
                        for x in _decode_column(caller, wp, et, 4)
                    ) else 0
            else:
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller, wp: int, e: int | float,
                ) -> int:
                    return 1 if any(
                        _same_value_zero(e, x)
                        for x in _decode_column(caller, wp, et, 4)
                    ) else 0

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        def _define_set_remove(et: str) -> None:
            name = f"set_remove$e{et}"
            elem_types = _VAL_WASM_TYPES[et]
            param_types = [wasmtime.ValType.i32()] + elem_types
            ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

            # Structural rebuild dropping the matching element (the elem
            # lives in the key field; val field is copied verbatim).
            def _without(
                caller: wasmtime.Caller, wp: int, e: object,
            ) -> int:
                survivors = [
                    (kb, vb)
                    for kb, vb in _bkt_raw_entries(caller, wp)
                    if not _same_value_zero(_decode_field(caller, et, kb, 0), e)
                ]
                return _encode_raw(caller, _WRAP_KIND_SET, survivors)

            if et == "s":
                def host_fn(
                    caller: wasmtime.Caller, wp: int, ep: int, el: int,
                ) -> int:
                    return _without(caller, wp, _read_wasm_string(caller, ep, el))
            else:
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller, wp: int, e: int | float,
                ) -> int:
                    return _without(caller, wp, e)

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        # set_size(wp) → i64 (O(1) from the bucket header).
        def host_set_size(caller: wasmtime.Caller, wp: int) -> int:
            return _bkt_count(caller, wp)

        linker.define_func(
            "vera", "set_size",
            wasmtime.FuncType(
                [wasmtime.ValType.i32()],
                [wasmtime.ValType.i64()],
            ),
            host_set_size, access_caller=True,
        )

        def _define_set_to_array(et: str) -> None:
            name = f"set_to_array$e{et}"
            ftype = wasmtime.FuncType(
                [wasmtime.ValType.i32()],
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
            )

            def host_fn(
                caller: wasmtime.Caller, wp: int,
            ) -> tuple[int, int]:
                elems = _decode_column(caller, wp, et, 4)
                if et == "s":
                    return _alloc_array_of_strings(caller, elems)  # type: ignore[arg-type]
                if et == "i":
                    return _alloc_array_of_i64(caller, elems)  # type: ignore[arg-type]
                if et == "f":
                    return _alloc_array_of_f64(caller, elems)  # type: ignore[arg-type]
                return _alloc_array_of_i32(caller, elems)  # type: ignore[arg-type]

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        # Register type-specific imports based on what the WAT uses.
        for op_name in result.set_ops_used:
            if op_name.startswith("set_add$"):
                et = op_name[len("set_add$e"):]
                _define_set_add(et)
            elif op_name.startswith("set_contains$"):
                et = op_name[len("set_contains$e"):]
                _define_set_contains(et)
            elif op_name.startswith("set_remove$"):
                et = op_name[len("set_remove$e"):]
                _define_set_remove(et)
            elif op_name.startswith("set_to_array$"):
                et = op_name[len("set_to_array$e"):]
                _define_set_to_array(et)

    # ── Decimal host functions ───────────────────────────────────
    if result.decimal_ops_used:
        from decimal import Decimal as PyDecimal, InvalidOperation

        _decimal_store: dict[int, PyDecimal] = {}
        _decimal_next_handle = [1]
        # Decimal keeps a value-typed Python store — the only host store
        # remaining after #706 moved Map / Set to bucket-as-truth.
        _host_store_refs["decimal"] = _decimal_store  # type: ignore[assignment]
        # #695/#706: Decimal is intentionally EXEMPT from the bucket-as-
        # truth migration.  ``PyDecimal`` is value-typed (immutable
        # digit/sign/exponent attributes, no WASM heap pointers inside
        # the stored object), so the silent-UAF window that affects
        # Map<K, T_heap> and Set<T_heap> cannot occur for Decimal.  Its
        # wrapper keeps the #573 tagged-handle layout (initialised by
        # ``_emit_wrap_handle`` / JS ``wrapHandle``), leaves ``bucket_ptr``
        # 0, and ``host_attach_bucket`` accepts only kind=3.

        def _decimal_alloc(d: PyDecimal) -> int:
            h = _decimal_next_handle[0]
            _decimal_next_handle[0] = h + 1
            _decimal_store[h] = d
            return h

        if "decimal_from_int" in result.decimal_ops_used:
            def host_decimal_from_int(
                _caller: wasmtime.Caller, v: int,
            ) -> int:
                return _decimal_alloc(PyDecimal(v))
            linker.define_func(
                "vera", "decimal_from_int",
                wasmtime.FuncType([wasmtime.ValType.i64()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_from_int, access_caller=True,
            )

        if "decimal_from_float" in result.decimal_ops_used:
            def host_decimal_from_float(
                _caller: wasmtime.Caller, v: float,
            ) -> int:
                return _decimal_alloc(PyDecimal(str(v)))
            linker.define_func(
                "vera", "decimal_from_float",
                wasmtime.FuncType([wasmtime.ValType.f64()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_from_float, access_caller=True,
            )

        if "decimal_from_string" in result.decimal_ops_used:
            def host_decimal_from_string(
                caller: wasmtime.Caller, ptr: int, length: int,
            ) -> int:
                s = _read_wasm_string(caller, ptr, length)
                try:
                    d = PyDecimal(s)
                    # #573 phase 3: wrap the Decimal handle so the
                    # Option<Decimal>'s Some payload is a wrapper
                    # pointer (matching what every other Decimal-
                    # producing op now returns).
                    raw = _decimal_alloc(d)
                    wrapped = _wrap_handle(
                        caller, _WRAP_KIND_DECIMAL, raw,
                    )
                    return _alloc_option_some_i32(caller, wrapped)
                except InvalidOperation:
                    return _alloc_option_none(caller)
            linker.define_func(
                "vera", "decimal_from_string",
                wasmtime.FuncType([wasmtime.ValType.i32(),
                                   wasmtime.ValType.i32()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_from_string, access_caller=True,
            )

        if "decimal_to_string" in result.decimal_ops_used:
            def host_decimal_to_string(
                caller: wasmtime.Caller, h: int,
            ) -> tuple[int, int]:
                s = str(_decimal_store[h])
                return _alloc_string(caller, s)
            linker.define_func(
                "vera", "decimal_to_string",
                wasmtime.FuncType([wasmtime.ValType.i32()],
                                  [wasmtime.ValType.i32(),
                                   wasmtime.ValType.i32()]),
                host_decimal_to_string, access_caller=True,
            )

        if "decimal_to_float" in result.decimal_ops_used:
            def host_decimal_to_float(
                _caller: wasmtime.Caller, h: int,
            ) -> float:
                return float(_decimal_store[h])
            linker.define_func(
                "vera", "decimal_to_float",
                wasmtime.FuncType([wasmtime.ValType.i32()],
                                  [wasmtime.ValType.f64()]),
                host_decimal_to_float, access_caller=True,
            )

        if "decimal_add" in result.decimal_ops_used:
            def host_decimal_add(
                _caller: wasmtime.Caller, a: int, b: int,
            ) -> int:
                return _decimal_alloc(_decimal_store[a] + _decimal_store[b])
            linker.define_func(
                "vera", "decimal_add",
                wasmtime.FuncType([wasmtime.ValType.i32(),
                                   wasmtime.ValType.i32()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_add, access_caller=True,
            )

        if "decimal_sub" in result.decimal_ops_used:
            def host_decimal_sub(
                _caller: wasmtime.Caller, a: int, b: int,
            ) -> int:
                return _decimal_alloc(_decimal_store[a] - _decimal_store[b])
            linker.define_func(
                "vera", "decimal_sub",
                wasmtime.FuncType([wasmtime.ValType.i32(),
                                   wasmtime.ValType.i32()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_sub, access_caller=True,
            )

        if "decimal_mul" in result.decimal_ops_used:
            def host_decimal_mul(
                _caller: wasmtime.Caller, a: int, b: int,
            ) -> int:
                return _decimal_alloc(_decimal_store[a] * _decimal_store[b])
            linker.define_func(
                "vera", "decimal_mul",
                wasmtime.FuncType([wasmtime.ValType.i32(),
                                   wasmtime.ValType.i32()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_mul, access_caller=True,
            )

        if "decimal_div" in result.decimal_ops_used:
            def host_decimal_div(
                caller: wasmtime.Caller, a: int, b: int,
            ) -> int:
                # #573 phase 3: ``a`` and ``b`` are raw handles
                # (the WASM-side translator unwraps wrapper
                # pointers before this call, matching the
                # pattern for every other Decimal binary op).
                # The result handle is wrapped here because the
                # host constructs ``Option<Decimal>`` internally
                # — its Some payload must be a wrapper pointer
                # to match what user code post-match expects.
                divisor = _decimal_store[b]
                if divisor == 0:
                    return _alloc_option_none(caller)
                raw = _decimal_alloc(_decimal_store[a] / divisor)
                wrapped = _wrap_handle(
                    caller, _WRAP_KIND_DECIMAL, raw,
                )
                return _alloc_option_some_i32(caller, wrapped)
            linker.define_func(
                "vera", "decimal_div",
                wasmtime.FuncType([wasmtime.ValType.i32(),
                                   wasmtime.ValType.i32()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_div, access_caller=True,
            )

        if "decimal_neg" in result.decimal_ops_used:
            def host_decimal_neg(
                _caller: wasmtime.Caller, h: int,
            ) -> int:
                return _decimal_alloc(-_decimal_store[h])
            linker.define_func(
                "vera", "decimal_neg",
                wasmtime.FuncType([wasmtime.ValType.i32()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_neg, access_caller=True,
            )

        if "decimal_compare" in result.decimal_ops_used:
            def host_decimal_compare(
                caller: wasmtime.Caller, a: int, b: int,
            ) -> int:
                da, db = _decimal_store[a], _decimal_store[b]
                if da < db:
                    tag = 0  # Less
                elif da == db:
                    tag = 1  # Equal
                else:
                    tag = 2  # Greater
                return _alloc_ordering(caller, tag)
            linker.define_func(
                "vera", "decimal_compare",
                wasmtime.FuncType([wasmtime.ValType.i32(),
                                   wasmtime.ValType.i32()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_compare, access_caller=True,
            )

        if "decimal_eq" in result.decimal_ops_used:
            def host_decimal_eq(
                _caller: wasmtime.Caller, a: int, b: int,
            ) -> int:
                return 1 if _decimal_store[a] == _decimal_store[b] else 0
            linker.define_func(
                "vera", "decimal_eq",
                wasmtime.FuncType([wasmtime.ValType.i32(),
                                   wasmtime.ValType.i32()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_eq, access_caller=True,
            )

        if "decimal_round" in result.decimal_ops_used:
            def host_decimal_round(
                _caller: wasmtime.Caller, h: int, places: int,
            ) -> int:
                d = _decimal_store[h]
                # Use quantize for precise rounding
                q = PyDecimal(10) ** -places
                try:
                    return _decimal_alloc(d.quantize(q))
                except InvalidOperation:
                    # Extreme exponent — return original value unchanged
                    return _decimal_alloc(d)
            linker.define_func(
                "vera", "decimal_round",
                wasmtime.FuncType([wasmtime.ValType.i32(),
                                   wasmtime.ValType.i64()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_round, access_caller=True,
            )

        if "decimal_abs" in result.decimal_ops_used:
            def host_decimal_abs(
                _caller: wasmtime.Caller, h: int,
            ) -> int:
                return _decimal_alloc(abs(_decimal_store[h]))
            linker.define_func(
                "vera", "decimal_abs",
                wasmtime.FuncType([wasmtime.ValType.i32()],
                                  [wasmtime.ValType.i32()]),
                host_decimal_abs, access_caller=True,
            )

    # -----------------------------------------------------------------
    # Json host functions
    # -----------------------------------------------------------------
    if result.json_ops_used:
        import json as _json

        from vera.wasm.json_serde import read_json, write_json

        if "json_parse" in result.json_ops_used:
            def host_json_parse(
                caller: wasmtime.Caller, ptr: int, length: int,
            ) -> int:
                text = _read_wasm_string(caller, ptr, length)
                try:
                    parsed = _json.loads(text)
                except (ValueError, TypeError) as exc:
                    return _alloc_result_err_string(caller, str(exc))
                # #692: hold the shadow-stack window open across the
                # full tree marshalling AND the final Result.Ok
                # wrapper alloc.  ``guard.__exit__`` restores
                # ``$gc_sp`` on the way out — pops everything we
                # pushed.
                with _ShadowGuard(caller) as guard:
                    json_ptr = write_json(
                        caller, _call_alloc, _write_i32, _write_f64,
                        _alloc_string, _alloc_map_wrapper, guard, parsed,
                    )
                    # Push the tree root before the Result.Ok alloc —
                    # that alloc could trigger GC and free the
                    # otherwise-unrooted tree.
                    guard.push(json_ptr)
                    return _alloc_result_ok_i32(caller, json_ptr)

            linker.define_func(
                "vera", "json_parse",
                wasmtime.FuncType(
                    [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                    [wasmtime.ValType.i32()],
                ),
                host_json_parse, access_caller=True,
            )

        if "json_stringify" in result.json_ops_used:
            def host_json_stringify(
                caller: wasmtime.Caller, ptr: int,
            ) -> tuple[int, int]:
                value = read_json(
                    caller, ptr, _read_i32, _read_f64,
                    _read_wasm_string, _decode_jobject,
                )
                # Note: json.dumps rejects NaN/Infinity by default
                # (raises ValueError).  This matches the JSON spec
                # (RFC 8259) which forbids these values.  The JS
                # runtime's JSON.stringify outputs "null" for them
                # instead.  Both behaviours are acceptable: Vera's
                # JNumber wraps Float64, so users should guard against
                # NaN/Infinity before serialising.
                text = _json.dumps(
                    value, ensure_ascii=False, allow_nan=False,
                )
                return _alloc_string(caller, text)

            linker.define_func(
                "vera", "json_stringify",
                wasmtime.FuncType(
                    [wasmtime.ValType.i32()],
                    [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                ),
                host_json_stringify, access_caller=True,
            )

    # -----------------------------------------------------------------
    # Html host functions (§9.7.4)
    # -----------------------------------------------------------------
    if result.html_ops_used:
        from html.parser import HTMLParser as _HTMLParser

        from vera.wasm.html_serde import read_html, write_html

        class _VeraHTMLParser(_HTMLParser):
            """Lenient HTML parser producing a tree of node dicts."""

            def __init__(self) -> None:
                super().__init__(convert_charrefs=True)
                self._root: dict[str, Any] = {
                    "tag": "element", "name": "html",
                    "attrs": {}, "children": [],
                }
                self._stack: list[dict[str, Any]] = [self._root]

            def handle_starttag(
                self, tag: str, attrs: list[tuple[str, str | None]],
            ) -> None:
                node: dict[str, Any] = {
                    "tag": "element",
                    "name": tag,
                    "attrs": {k: (v or "") for k, v in attrs},
                    "children": [],
                }
                self._stack[-1]["children"].append(node)
                # Void elements don't get pushed
                if tag.lower() not in (
                    "area", "base", "br", "col", "embed", "hr", "img",
                    "input", "link", "meta", "param", "source", "track",
                    "wbr",
                ):
                    self._stack.append(node)

            def handle_endtag(self, tag: str) -> None:
                # Pop back to matching tag (lenient)
                for i in range(len(self._stack) - 1, 0, -1):
                    if self._stack[i]["name"] == tag:
                        self._stack[i + 1:] = []
                        break

            def handle_data(self, data: str) -> None:
                if data:
                    self._stack[-1]["children"].append(
                        {"tag": "text", "content": data},
                    )

            def handle_comment(self, data: str) -> None:
                self._stack[-1]["children"].append(
                    {"tag": "comment", "content": data},
                )

            def get_root(self) -> dict[str, Any]:
                children: list[Any] = self._root["children"]
                if len(children) == 1 and children[0].get("tag") == "element":
                    result: dict[str, Any] = children[0]
                    return result
                return self._root

        def _html_escape(s: str) -> str:
            """Escape &, <, > for HTML text content."""
            return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

        def _html_escape_attr(s: str) -> str:
            """Escape &, <, >, " for HTML attribute values."""
            return (s.replace("&", "&amp;").replace("<", "&lt;")
                     .replace(">", "&gt;").replace('"', "&quot;"))

        def _html_to_string_py(node: dict[str, Any]) -> str:
            """Serialize Python HtmlNode dict to HTML string."""
            tag = node.get("tag", "text")
            if tag == "text":
                return _html_escape(str(node.get("content", "")))
            if tag == "comment":
                content = str(node.get("content", "")).replace("-->", "-- >")
                return f"<!--{content}-->"
            # element
            name = node.get("name", "div")
            attrs: dict[str, str] = node.get("attrs", {})
            children: list[Any] = node.get("children", [])
            attr_str = ""
            for k, v in attrs.items():
                attr_str += f' {k}="{_html_escape_attr(v)}"'
            if str(name).lower() in (
                "area", "base", "br", "col", "embed", "hr", "img",
                "input", "link", "meta", "param", "source", "track",
                "wbr",
            ):
                return f"<{name}{attr_str}>"
            inner = "".join(_html_to_string_py(c) for c in children)
            return f"<{name}{attr_str}>{inner}</{name}>"

        def _html_query_py(
            node: dict[str, Any], selector: str,
        ) -> list[dict[str, Any]]:
            """Simple CSS selector query on HtmlNode tree."""
            results: list[dict[str, Any]] = []
            parts = selector.strip().split()
            if not parts:
                return results
            _html_query_walk(node, parts, 0, results)
            return results

        def _html_matches_selector(
            node: dict[str, Any], sel: str,
        ) -> bool:
            """Check if a single element matches a simple selector."""
            if node.get("tag") != "element":
                return False
            name = str(node.get("name", ""))
            attrs: dict[str, str] = node.get("attrs", {})
            if sel.startswith("#"):
                return bool(attrs.get("id", "") == sel[1:])
            if sel.startswith("."):
                classes = str(attrs.get("class", "")).split()
                return sel[1:] in classes
            if sel.startswith("[") and sel.endswith("]"):
                attr_name = sel[1:-1]
                return bool(attr_name in attrs)
            return bool(name == sel)

        def _html_query_walk(
            node: dict[str, Any],
            parts: list[str],
            depth: int,
            results: list[dict[str, Any]],
        ) -> None:
            """Walk tree matching descendant combinator selectors."""
            if node.get("tag") != "element":
                return
            if _html_matches_selector(node, parts[depth]):
                if depth == len(parts) - 1:
                    results.append(node)
                else:
                    # Continue matching remaining parts in descendants
                    for child in node.get("children", []):
                        _html_query_walk(child, parts, depth + 1, results)
            # Always try matching from the start in all descendants
            for child in node.get("children", []):
                _html_query_walk(child, parts, 0, results)

        def _html_text_py(node: dict[str, Any]) -> str:
            """Extract text content recursively from HtmlNode."""
            tag = node.get("tag", "text")
            if tag == "text":
                return str(node.get("content", ""))
            if tag == "comment":
                return ""
            # element — concatenate children text
            children: list[Any] = node.get("children", [])
            return "".join(
                _html_text_py(c) for c in children
            )

        if "html_parse" in result.html_ops_used:
            def host_html_parse(
                caller: wasmtime.Caller, ptr: int, length: int,
            ) -> int:
                text = _read_wasm_string(caller, ptr, length)
                # Parse-domain errors → Result.Err.  Narrow catch:
                # parser failures (lenient HTMLParser raising on a
                # genuinely malformed input) surface as
                # ``Result.Err(str(exc))``.  We deliberately do NOT
                # catch invariant violations (e.g. the
                # ``_wrap_handle`` RuntimeError from #578 for an
                # out-of-range handle, or any AssertionError from
                # internal compiler bugs); those propagate as
                # wasmtime traps so the diagnostic text reaches
                # the user instead of being repackaged.
                try:
                    parser = _VeraHTMLParser()
                    parser.feed(text)
                    root = parser.get_root()
                except (ValueError, TypeError, AttributeError) as exc:
                    return _alloc_result_err_string(caller, str(exc))
                # #692: hold the shadow-stack window open across
                # the full tree marshalling AND the final
                # Result.Ok wrapper alloc.  Shadow-stack work is
                # OUTSIDE the parse try/except so host-side
                # invariant violations (``_ShadowGuard`` overflow,
                # ``_wrap_handle`` RuntimeError, AssertionErrors)
                # propagate as wasmtime traps rather than being
                # repackaged as user-domain parse errors.  Matches
                # ``host_md_parse`` and ``host_json_parse``
                # structurally — caught by pr-review-toolkit:
                # before this restructure, the with-block was
                # inside the narrow except above, contradicting
                # the comment that claimed otherwise.
                with _ShadowGuard(caller) as guard:
                    html_ptr = write_html(
                        caller, _call_alloc, _write_i32,
                        _alloc_string, _alloc_map_wrapper,
                        guard, root,
                    )
                    guard.push(html_ptr)
                    return _alloc_result_ok_i32(caller, html_ptr)

            linker.define_func(
                "vera", "html_parse",
                wasmtime.FuncType(
                    [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                    [wasmtime.ValType.i32()],
                ),
                host_html_parse, access_caller=True,
            )

        if "html_to_string" in result.html_ops_used:
            def host_html_to_string(
                caller: wasmtime.Caller, ptr: int,
            ) -> tuple[int, int]:
                node = read_html(
                    caller, ptr, _read_i32,
                    _read_wasm_string, _decode_attrs,
                )
                text = _html_to_string_py(node)
                return _alloc_string(caller, text)

            linker.define_func(
                "vera", "html_to_string",
                wasmtime.FuncType(
                    [wasmtime.ValType.i32()],
                    [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                ),
                host_html_to_string, access_caller=True,
            )

        if "html_query" in result.html_ops_used:
            def host_html_query(
                caller: wasmtime.Caller,
                node_ptr: int, sel_ptr: int, sel_len: int,
            ) -> tuple[int, int]:
                node = read_html(
                    caller, node_ptr, _read_i32,
                    _read_wasm_string, _decode_attrs,
                )
                selector = _read_wasm_string(caller, sel_ptr, sel_len)
                matches = _html_query_py(node, selector)
                count = len(matches)
                if count > 0:
                    # #692: same shadow-stack-rooting concern as
                    # ``host_html_parse`` — arr_ptr would otherwise
                    # be reclaimed if a recursive write_html grew
                    # the heap mid-walk.  Push arr_ptr; each child
                    # write also routes through ``guard``.  The
                    # returned (arr_ptr, count) pair is unrooted
                    # at the point of return (``__exit__`` resets
                    # ``$gc_sp`` before the function returns); the
                    # WASM-side caller is responsible for re-rooting
                    # via ``gc_shadow_push`` once the values land in
                    # locals — emitted by ``_translate_html_query``
                    # in ``vera/wasm/calls_markup.py``.  Safe in
                    # practice because no allocation happens between
                    # the call return and the receiving local-store,
                    # but the guard's protection does NOT extend past
                    # the function boundary.
                    with _ShadowGuard(caller) as guard:
                        arr_ptr = _call_alloc(caller, count * 4)
                        guard.push(arr_ptr)
                        for i, m in enumerate(matches):
                            m_ptr = write_html(
                                caller, _call_alloc, _write_i32,
                                _alloc_string, _alloc_map_wrapper,
                                guard, m,
                            )
                            _write_i32(caller, arr_ptr + i * 4, m_ptr)
                else:
                    arr_ptr = 0
                return (arr_ptr, count)

            linker.define_func(
                "vera", "html_query",
                wasmtime.FuncType(
                    [wasmtime.ValType.i32(),
                     wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                    [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                ),
                host_html_query, access_caller=True,
            )

        if "html_text" in result.html_ops_used:
            def host_html_text(
                caller: wasmtime.Caller, ptr: int,
            ) -> tuple[int, int]:
                node = read_html(
                    caller, ptr, _read_i32,
                    _read_wasm_string, _decode_attrs,
                )
                text = _html_text_py(node)
                return _alloc_string(caller, text)

            linker.define_func(
                "vera", "html_text",
                wasmtime.FuncType(
                    [wasmtime.ValType.i32()],
                    [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                ),
                host_html_text, access_caller=True,
            )

    # -----------------------------------------------------------------
    # Http host functions
    # -----------------------------------------------------------------
    if result.http_ops_used:
        if "http_get" in result.http_ops_used:
            def host_http_get(
                caller: wasmtime.Caller, ptr: int, length: int,
            ) -> int:
                url = _read_wasm_string(caller, ptr, length)
                try:
                    import urllib.request
                    with urllib.request.urlopen(url, timeout=_INFERENCE_TIMEOUT) as resp:  # noqa: S310
                        # #591 — `errors="replace"` keeps the response
                        # data flowing to the user even when the
                        # remote server's Content-Type lies about
                        # the encoding.  Invalid bytes surface as
                        # U+FFFD inside the OK-branch string rather
                        # than as a Python `UnicodeDecodeError`
                        # message leaking into the Err branch.  The
                        # data trade-off is acceptable for a generic
                        # HTTP GET — the user's intent is "fetch
                        # this URL's body", not "fail if it isn't
                        # cleanly UTF-8".
                        body = resp.read().decode("utf-8", errors="replace")
                    return _alloc_result_ok_string(caller, body)
                except Exception as exc:
                    return _alloc_result_err_string(caller, str(exc))

            linker.define_func(
                "vera", "http_get",
                wasmtime.FuncType(
                    [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                    [wasmtime.ValType.i32()],
                ),
                host_http_get, access_caller=True,
            )

        if "http_post" in result.http_ops_used:
            def host_http_post(
                caller: wasmtime.Caller,
                url_ptr: int, url_len: int,
                body_ptr: int, body_len: int,
            ) -> int:
                url = _read_wasm_string(caller, url_ptr, url_len)
                body = _read_wasm_string(caller, body_ptr, body_len)
                try:
                    import urllib.request
                    # Http.post is intentionally JSON-only: the Vera-level API
                    # takes a String body and always sends it as application/json.
                    # Custom Content-Type headers require #351 (custom headers).
                    req = urllib.request.Request(  # noqa: S310
                        url, data=body.encode("utf-8"), method="POST",
                        headers={"Content-Type": "application/json"},
                    )
                    with urllib.request.urlopen(req, timeout=_INFERENCE_TIMEOUT) as resp:  # noqa: S310
                        # #591 — `errors="replace"` for the same
                        # reason as `http_get`: keep response data
                        # flowing as U+FFFD substitutions rather
                        # than letting a `UnicodeDecodeError`
                        # message leak into the Err branch.
                        response_body = resp.read().decode(
                            "utf-8", errors="replace",
                        )
                    return _alloc_result_ok_string(caller, response_body)
                except Exception as exc:
                    return _alloc_result_err_string(caller, str(exc))

            linker.define_func(
                "vera", "http_post",
                wasmtime.FuncType(
                    [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
                     wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                    [wasmtime.ValType.i32()],
                ),
                host_http_post, access_caller=True,
            )

    # -----------------------------------------------------------------
    # Inference effect host functions
    # -----------------------------------------------------------------
    if result.inference_ops_used:
        if "inference_complete" in result.inference_ops_used:
            def host_inference_complete(
                caller: wasmtime.Caller, ptr: int, length: int,
            ) -> int:
                import json as _json
                import os as _os
                import urllib.request as _urlreq

                prompt = _read_wasm_string(caller, ptr, length)
                _env = env_vars if env_vars is not None else _os.environ
                provider = _env.get("VERA_INFERENCE_PROVIDER", "").lower()

                # Auto-detect provider from whichever key is set,
                # respecting registry insertion order (anthropic first).
                if not provider:
                    for _pname, _pcfg in _PROVIDERS.items():
                        if _env.get(_pcfg.env_key, ""):
                            provider = _pname
                            break

                if not provider:
                    key_vars = ", ".join(
                        c.env_key for c in _PROVIDERS.values()
                    )
                    return _alloc_result_err_string(
                        caller,
                        f"No inference provider configured. "
                        f"Set {key_vars}.",
                    )

                cfg = _PROVIDERS.get(provider)
                api_key = _env.get(cfg.env_key, "") if cfg else ""

                if cfg is not None and not api_key:
                    return _alloc_result_err_string(
                        caller,
                        f"Inference provider '{provider}' selected but "
                        f"{cfg.env_key} is not set.",
                    )

                try:
                    model = _env.get("VERA_INFERENCE_MODEL", "")
                    completion = _call_inference_provider(
                        provider, prompt, model, api_key,
                    )
                    return _alloc_result_ok_string(caller, completion)
                except Exception as exc:
                    return _alloc_result_err_string(caller, str(exc))

            linker.define_func(
                "vera", "inference_complete",
                wasmtime.FuncType(
                    [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                    [wasmtime.ValType.i32()],
                ),
                host_inference_complete, access_caller=True,
            )

    # ---------------------------------------------------------------
    # Random host functions (#465).  Lazy import — `random` is
    # stdlib so the import is cheap, but only pull it in when needed.
    # ---------------------------------------------------------------
    if result.random_ops_used:
        import random as _random_mod

        if "random_int" in result.random_ops_used:
            # vera.random_int(low: i64, high: i64) -> i64
            # Inclusive range [low, high].  Caller is required by
            # contract to ensure low <= high; we don't double-check.
            def host_random_int(
                _caller: wasmtime.Caller, low: int, high: int,
            ) -> int:
                # S311 — Random effect is for games / simulations /
                # Monte Carlo, not crypto.  #465 explicitly scopes
                # the effect that way; secure randomness would
                # warrant a separate `Crypto` effect with
                # `secrets.randbelow`.
                return _random_mod.randint(low, high)  # noqa: S311

            linker.define_func(
                "vera", "random_int",
                wasmtime.FuncType(
                    [wasmtime.ValType.i64(), wasmtime.ValType.i64()],
                    [wasmtime.ValType.i64()],
                ),
                host_random_int, access_caller=True,
            )

        if "random_float" in result.random_ops_used:
            # vera.random_float() -> f64 in [0.0, 1.0)
            def host_random_float(_caller: wasmtime.Caller) -> float:
                # S311 — see host_random_int; non-crypto by design.
                return _random_mod.random()  # noqa: S311

            linker.define_func(
                "vera", "random_float",
                wasmtime.FuncType([], [wasmtime.ValType.f64()]),
                host_random_float, access_caller=True,
            )

        if "random_bool" in result.random_ops_used:
            # vera.random_bool() -> i32 (0 or 1)
            def host_random_bool(_caller: wasmtime.Caller) -> int:
                # S311 — see host_random_int; non-crypto by design.
                return 1 if _random_mod.random() < 0.5 else 0  # noqa: S311

            linker.define_func(
                "vera", "random_bool",
                wasmtime.FuncType([], [wasmtime.ValType.i32()]),
                host_random_bool, access_caller=True,
            )

    # ---------------------------------------------------------------
    # Math host functions (#467).  Ten functions share one shape
    # (Float64 → Float64) except `atan2` which takes two.  All are
    # thin wrappers over Python's `math` module — IEEE 754
    # semantics (NaN for out-of-domain inputs, ±inf for overflow)
    # are preserved across the WASM boundary.
    # ---------------------------------------------------------------
    if result.math_ops_used:
        import math as _math_mod

        _f64_unary = wasmtime.FuncType(
            [wasmtime.ValType.f64()], [wasmtime.ValType.f64()]
        )
        from typing import Callable

        def _math_unary_host(
            py_fn: Callable[[float], float],
        ) -> Callable[[wasmtime.Caller, float], float]:
            """Wrap a `math.*` function as a wasmtime host callback.

            Factored into its own function so the captured `py_fn`
            is bound at call time rather than at loop-variable time —
            the classic Python late-binding closure trap.

            Python's `math` module raises `ValueError` on
            out-of-domain inputs (e.g., `math.log(-1)`).  IEEE 754
            and the JavaScript host runtime both return NaN in those
            cases, so we translate the exception into NaN to keep
            the two WASM runtimes observationally equivalent and
            let Vera programs detect the condition via
            `float_is_nan(...)` instead of trapping.
            """
            def host(_caller: wasmtime.Caller, x: float) -> float:
                try:
                    return py_fn(x)
                except ValueError:
                    return float("nan")
            return host

        _math_unary_specs: tuple[tuple[str, Callable[[float], float]], ...] = (
            ("log",   _math_mod.log),
            ("log2",  _math_mod.log2),
            ("log10", _math_mod.log10),
            ("sin",   _math_mod.sin),
            ("cos",   _math_mod.cos),
            ("tan",   _math_mod.tan),
            ("asin",  _math_mod.asin),
            ("acos",  _math_mod.acos),
            ("atan",  _math_mod.atan),
        )
        for op_name, py_fn in _math_unary_specs:
            if op_name in result.math_ops_used:
                linker.define_func(
                    "vera", op_name, _f64_unary,
                    _math_unary_host(py_fn), access_caller=True,
                )

        if "atan2" in result.math_ops_used:
            def host_atan2(
                _caller: wasmtime.Caller, y: float, x: float,
            ) -> float:
                # `math.atan2` doesn't raise for any Float64 input
                # (it's total over the real numbers), but we mirror
                # the unary wrapper's pattern so future changes stay
                # uniform.
                try:
                    return _math_mod.atan2(y, x)
                except ValueError:
                    return float("nan")
            linker.define_func(
                "vera", "atan2",
                wasmtime.FuncType(
                    [wasmtime.ValType.f64(), wasmtime.ValType.f64()],
                    [wasmtime.ValType.f64()],
                ),
                host_atan2, access_caller=True,
            )

    instance = linker.instantiate(store, module)

    def _peak_heap_bytes() -> int:
        """Read the exported ``$heap_ptr`` global (bump high-water mark).

        #706: the GC heap stat the reclamation tests use to confirm
        transient Map / Set wrappers + buckets are reclaimed.  Returns 0
        for modules compiled without the GC runtime (no ``heap_ptr``
        export).
        """
        hp = instance.exports(store).get("heap_ptr")
        if not isinstance(hp, wasmtime.Global):
            return 0
        val = hp.value(store)
        return val if isinstance(val, int) else 0

    # Determine function to call
    auto_selected = False
    if fn_name is None:
        # Try "main" first, then first export
        if "main" in result.exports:
            fn_name = "main"
        elif result.exports:
            fn_name = result.exports[0]
            auto_selected = True
        else:
            raise RuntimeError("No exported functions to call")

    func = instance.exports(store).get(fn_name)
    if func is None or not isinstance(func, wasmtime.Func):
        exports_str = ", ".join(result.exports) if result.exports else "(none)"
        raise RuntimeError(
            f"Function '{fn_name}' not found in exports. "
            f"Available: {exports_str}"
        )

    # Type-aware parsing of CLI raw string arguments
    if raw_args is not None:
        vera_params = result.fn_param_types.get(fn_name or "", [])
        if len(raw_args) != len(vera_params):
            n = len(vera_params)
            m = len(raw_args)
            msg = (
                f"Function '{fn_name}' expects {n} "
                f"argument{'s' if n != 1 else ''} "
                f"but {m} {'were' if m != 1 else 'was'} provided."
            )
            raise RuntimeError(msg)

        memory_export = instance.exports(store).get("memory")
        alloc_export = instance.exports(store).get("alloc")

        def _alloc_string_arg(s: str) -> tuple[int, int]:
            if not isinstance(memory_export, wasmtime.Memory):
                raise RuntimeError(
                    "Cannot allocate String argument: module has no 'memory' export"
                )
            if not isinstance(alloc_export, wasmtime.Func):
                raise RuntimeError(
                    "Cannot allocate String argument: module has no 'alloc' export"
                )
            encoded = s.encode("utf-8")
            ptr = alloc_export(store, len(encoded))
            if not isinstance(ptr, int):
                raise RuntimeError(
                    f"String allocator returned unexpected type {type(ptr).__name__!r}"
                )
            buf = memory_export.data_ptr(store)
            for i, b in enumerate(encoded):
                buf[ptr + i] = b
            return ptr, len(encoded)

        parsed: list[int | float] = []
        for raw, wasm_type in zip(raw_args, vera_params, strict=True):
            try:
                if wasm_type == "i64":
                    parsed.append(int(raw))
                elif wasm_type == "f64":
                    parsed.append(float(raw))
                elif wasm_type == "i32":
                    # Bool or Byte: accept true/false or integer
                    if raw.lower() in ("true", "yes", "1"):
                        parsed.append(1)
                    elif raw.lower() in ("false", "no", "0"):
                        parsed.append(0)
                    else:
                        parsed.append(int(raw))
                elif wasm_type == "i32_pair":
                    ptr, length = _alloc_string_arg(raw)
                    parsed.extend([ptr, length])
                else:
                    parsed.append(int(raw))  # fallback
            except (ValueError, TypeError) as exc:
                raise RuntimeError(
                    f"Argument {raw!r} is not valid for parameter type "
                    f"'{wasm_type}': {exc}"
                ) from exc
        args = parsed

    # Check parameter count before calling
    call_args: list[int | float] = args or []
    func_type = func.type(store)
    expected = len(func_type.params)
    given = len(call_args)
    if given != expected:
        exports_str = ", ".join(result.exports)
        msg = (
            f"Function '{fn_name}' expects {expected} "
            f"parameter{'s' if expected != 1 else ''} "
            f"but {given} {'were' if given != 1 else 'was'} provided."
        )
        if auto_selected:
            msg += (
                f"\n\nNo 'main' function found. "
                f"'{fn_name}' was selected as the first export."
            )
        msg += (
            f"\n\nAvailable exports: {exports_str}"
            f"\n\nTo call a specific function with arguments:"
            f"\n\n  vera run <file> --fn {fn_name} -- <args>"
        )
        raise RuntimeError(msg)

    try:
        raw_result = func(store, *call_args)
    except _VeraExit as exit_exc:
        # IO.exit(code) — return captured output with exit code.
        # #573: include host_store_sizes here too so the field is
        # always populated, mirroring the normal-completion path
        # below.  Programs that exit via IO.exit can still observe
        # host-store population (e.g. for tests verifying that
        # reclamation happened before exit).
        return ExecuteResult(
            value=None,
            stdout=output_buf.getvalue(),
            stderr=stderr_buf.getvalue() if stderr_buf is not None else "",
            state={k: v[-1] for k, v in state_store.items()},
            exit_code=exit_exc.code,
            host_store_sizes={
                k: len(v) for k, v in _host_store_refs.items()
            },
            peak_heap_bytes=_peak_heap_bytes(),
        )
    except KeyboardInterrupt:
        # Ctrl-C arriving while a host import is on the stack (e.g.
        # ``IO.sleep``'s ``time.sleep`` or ``IO.read_char``'s blocking
        # read).  Python raises ``KeyboardInterrupt`` in the host
        # callback; wasmtime's trampoline catches it (as a
        # ``BaseException``), unwinds the wasm call safely, and
        # re-raises the original ``KeyboardInterrupt`` here — so it
        # lands as a bare ``KeyboardInterrupt`` at this call site
        # rather than escaping the process or arriving wrapped in a
        # ``Trap``.  Map it to the conventional SIGINT exit code (130
        # = 128 + signal-2), preserving captured stdout/stderr/state
        # exactly as the ``IO.exit`` path above does.
        #
        # #599: this single handler replaces four per-host-import
        # ``except KeyboardInterrupt: raise _VeraExit(130)`` guards
        # (one in ``host_sleep``, three across ``host_read_char``'s
        # platform branches).  Those guards existed because the
        # ``wasmtime<45`` trampoline caught only ``Exception``, so a
        # raw ``KeyboardInterrupt`` (a ``BaseException``) escaped into
        # Rust with an undefined ABI return value and aborted with a
        # libmalloc SIGABRT (#595).  ``KeyboardInterrupt`` had to be
        # laundered into ``_VeraExit`` (an ``Exception``) to be caught.
        # wasmtime-py 45.0.0 ([bytecodealliance/wasmtime-py#337],
        # `except Exception` → `except BaseException`) makes the raw
        # propagation safe, so the mapping moves to one place.
        return ExecuteResult(
            value=None,
            stdout=output_buf.getvalue(),
            stderr=stderr_buf.getvalue() if stderr_buf is not None else "",
            state={k: v[-1] for k, v in state_store.items()},
            exit_code=130,
            host_store_sizes={
                k: len(v) for k, v in _host_store_refs.items()
            },
            peak_heap_bytes=_peak_heap_bytes(),
        )
    except Exception as exc:
        # _VeraExit may be wrapped by wasmtime in a Trap/WasmtimeError.
        # Check the exception chain for our sentinel.
        cause: BaseException | None = exc
        while cause is not None:
            if isinstance(cause, _VeraExit):
                return ExecuteResult(
                    value=None,
                    stdout=output_buf.getvalue(),
                    stderr=stderr_buf.getvalue() if stderr_buf is not None else "",
                    state={k: v[-1] for k, v in state_store.items()},
                    exit_code=cause.code,
                    host_store_sizes={
                        k: len(v) for k, v in _host_store_refs.items()
                    },
                    peak_heap_bytes=_peak_heap_bytes(),
                )
            cause = cause.__cause__ or cause.__context__
            if cause is exc:
                break  # avoid infinite loop

        # Convert wasmtime traps to a WasmTrapError carrying:
        #   * the captured stdout/stderr, so the CLI can surface output
        #     written before the trap (#522 — previously discarded);
        #   * a Vera-native classification of the trap reason, so the
        #     CLI can present "Integer division by zero" instead of
        #     "Runtime contract violation: ... wasm trap: integer
        #     divide by zero" (#516 Stage 1 — previously every trap
        #     was relabelled "Runtime contract violation").
        # WasmTrapError is a RuntimeError subclass, so existing
        # ``except RuntimeError`` blocks remain backward-compatible.
        exc_name = type(exc).__name__
        if exc_name in ("Trap", "WasmtimeError"):
            # #516 Stage 3 (#547) — _classify_trap now returns
            # (kind, description, fix).  The Fix paragraph is
            # canned per-kind text (empty string for the kinds that
            # don't admit a generic suggestion: contract_violation /
            # unknown).
            kind, message, fix = _classify_trap(exc, last_violation)
            # #516 Stage 2 — resolve trap frames against the source map.
            # Pre-Stage-2 the user got a hex-offset wasmtime backtrace
            # in the exception message and nothing else; now they get
            # a structured list of (file, line) pairs they can act on.
            frames = _resolve_trap_frames(
                exc, result.fn_source_map, result.prelude_fn_names,
            )
            raise WasmTrapError(
                message,
                stdout=output_buf.getvalue(),
                stderr=stderr_buf.getvalue() if stderr_buf is not None else "",
                kind=kind,
                frames=frames,
                fix=fix,
            ) from exc
        raise

    # Extract return value
    value: int | float | str | None
    if raw_result is None:
        value = None
    elif isinstance(raw_result, (tuple, list)):
        # Multi-value return (e.g. String/Array as (ptr, len)).  For
        # String returns we decode the UTF-8 bytes from linear memory
        # so callers (notably the CLI's `vera run` printer) see the
        # actual string instead of a bare heap pointer.  Array returns
        # keep the existing pointer-only fallback — their bytes-at-ptr
        # aren't UTF-8 and we'd need element-type-aware formatting to
        # render them meaningfully (separate scope).
        if (
            len(raw_result) == 2
            and fn_name in result.fn_string_returns
            and isinstance(raw_result[0], int)
            and isinstance(raw_result[1], int)
        ):
            ptr, length = raw_result[0], raw_result[1]
            memory_export = instance.exports(store).get("memory")
            if isinstance(memory_export, wasmtime.Memory) and length >= 0:
                buf = memory_export.data_ptr(store)
                mem_size = memory_export.data_len(store)
                if 0 <= ptr and ptr + length <= mem_size:
                    raw_bytes = bytes(buf[ptr:ptr + length])
                    # `errors="replace"` rather than the previous
                    # try/except → pointer-fallback pattern (#589).  The
                    # old fallback silently mutated the return type from
                    # ``str`` to ``int`` when bytes weren't valid UTF-8,
                    # so a downstream consumer (CLI printer) printed an
                    # integer where a string was expected — a worse
                    # footgun than visible U+FFFD chars.  Now invalid
                    # bytes surface as replacement characters in the
                    # decoded string and ``value`` stays a ``str``.
                    value = raw_bytes.decode("utf-8", errors="replace")
                else:  # pragma: no cover — out-of-bounds defensive path
                    value = ptr
            else:  # pragma: no cover — module without memory export
                value = ptr
        else:
            value = raw_result[0] if raw_result else None
    elif isinstance(raw_result, float):
        value = raw_result
    elif isinstance(raw_result, int):
        value = raw_result
    else:
        value = int(raw_result)

    return ExecuteResult(
        value=value,
        stdout=output_buf.getvalue(),
        stderr=stderr_buf.getvalue() if stderr_buf is not None else "",
        state={k: v[-1] for k, v in state_store.items()},
        host_store_sizes={k: len(v) for k, v in _host_store_refs.items()},
        peak_heap_bytes=_peak_heap_bytes(),
    )
