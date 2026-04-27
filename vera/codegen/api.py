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
    # function classification.  Populated by `_register_fn` when a
    # FnDecl has no span (the marker `inject_prelude` uses for
    # synthetic injections).  Consumed by `_resolve_trap_frames`
    # alongside the runtime-helper allowlist so trap frames inside
    # prelude functions (`array_map`, `option_unwrap_or`, ADT auto-
    # derived methods, …) are tagged as `<builtin>` rather than
    # falling through to `<unknown>` user code.  Without it the
    # CLI's suppression-marker collapse cannot fire for traps that
    # go through prelude functions.
    prelude_fn_names: set[str] = field(default_factory=set)

    @property
    def ok(self) -> bool:
        """True if compilation succeeded with no errors."""
        return not any(d.severity == "error" for d in self.diagnostics)


@dataclass
class ExecuteResult:
    """Result of executing a WASM function."""

    value: int | float | None  # Return value (None for void/Unit functions)
    stdout: str  # Captured IO.print output
    state: dict[str, int | float] = field(default_factory=dict)
    exit_code: int | None = None  # Set by IO.exit
    # stderr is last so the positional constructor shape pre-#463
    # (value, stdout, state, exit_code) still works for external
    # callers.  Default "" preserves backward compatibility — only
    # populated when execute(capture_stderr=True).
    stderr: str = ""


class _VeraExit(Exception):
    """Sentinel exception raised by IO.exit to abort WASM execution."""

    def __init__(self, code: int) -> None:
        self.code = code
        super().__init__(f"IO.exit({code})")


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

    * ``frames`` — a list of resolved trap frames (#516 Stage 2).
      Each entry is a dict with keys ``func`` (WAT function name as
      reported by wasmtime), ``file``, ``line_start``, ``line_end``,
      and ``is_builtin`` (True for runtime helpers like ``alloc``,
      ``gc_collect``, ``contract_fail`` that have no source mapping).
      Outermost (most recent) frame first, matching the wasmtime
      backtrace order.

    Stage 1 of #516 established the ``kind`` taxonomy.  Stage 2 adds
    source mapping (the ``frames`` field).  Stage 3 will layer per-
    kind ``Fix:`` suggestion paragraphs on top.
    """

    def __init__(
        self,
        message: str,
        *,
        stdout: str = "",
        stderr: str = "",
        kind: str = "unknown",
        frames: list[dict[str, object]] | None = None,
    ) -> None:
        super().__init__(message)
        self.stdout = stdout
        self.stderr = stderr
        self.kind = kind
        self.frames: list[dict[str, object]] = frames or []


def _resolve_trap_frames(
    exc: BaseException,
    fn_source_map: dict[str, tuple[str, int, int]],
    prelude_fn_names: set[str] | None = None,
) -> list[dict[str, object]]:
    """Resolve ``wasmtime.Trap.frames`` against the codegen source map.

    Walks the trap's frame list and produces a structured backtrace,
    one dict per frame.  Each dict has:

    * ``func`` — the WAT function name as reported by wasmtime, with
      any leading ``$`` stripped defensively (current wasmtime-py
      versions strip it already, but we normalise anyway so a future
      version that omits the strip can't silently break the builtin
      lookup or the source-map join).  For monomorphized generics
      (``identity$Int``) this is the mangled name; the resolver also
      tries the base name (the part before the rightmost ``$``) as a
      fallback because the source map only stores the original
      generic.
    * ``file`` — source path, or ``"<builtin>"`` for runtime helpers
      that have no Vera source.
    * ``line_start`` / ``line_end`` — source line range of the
      function definition.  ``None`` for built-ins.
    * ``is_builtin`` — True for ``alloc`` / ``gc_collect`` /
      ``contract_fail`` / ``exn_*`` / ``vera.*`` (host imports), all
      of which are runtime infrastructure with no user-visible source
      location.

    On any failure (no ``frames`` attribute, exception during iter,
    etc.) returns an empty list — the trap message survives even if
    the backtrace can't be resolved.  Per-function granularity matches
    the issue's stated Stage 2 success criterion (#516).
    """
    raw_frames = getattr(exc, "frames", None)
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

    resolved: list[dict[str, object]] = []
    try:
        iter_frames = list(raw_frames)
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
            resolved.append({
                "func": name,
                "file": "<builtin>",
                "line_start": None,
                "line_end": None,
                "is_builtin": True,
            })
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
            resolved.append({
                "func": name,
                "file": "<unknown>",
                "line_start": None,
                "line_end": None,
                "is_builtin": False,
            })
            continue

        file_path, line_start, line_end = loc
        resolved.append({
            "func": name,
            "file": file_path,
            "line_start": line_start,
            "line_end": line_end,
            "is_builtin": False,
        })

    return resolved


def _classify_trap(
    exc: BaseException, last_violation: list[str]
) -> tuple[str, str]:
    """Classify a wasmtime trap into ``(kind, user-facing-message)``.

    A contract-violation host-import (``host_contract_fail``) writes
    the precise contract message into ``last_violation`` before WASM
    traps. When that channel is populated, it always wins over the
    wasmtime trap reason: the host-import path is more specific and
    already Vera-native.

    For everything else we inspect ``str(exc)`` for the wasmtime trap
    reason substring — wasmtime renders these as ``wasm trap: <reason>``
    in the exception message. The mapping is intentionally narrow: only
    reasons we can describe in Vera-native terms, with a known cause,
    get classified. Unknown reasons fall through to ``unknown`` and
    surface verbatim so the user is never left without a message.

    Stage 1 of #516. The links to related issues in the messages help
    agents recognise that what they hit is a known limitation rather
    than a bug they should report.
    """
    # Contract violation takes precedence — the host import gave us
    # the precise message; wasmtime's trap reason is just "unreachable
    # executed" in that path and would lose detail.
    if last_violation:
        return ("contract_violation", last_violation[0])

    msg = str(exc).lower()
    if "integer divide by zero" in msg:
        return ("divide_by_zero", "Integer division by zero")
    if "out of bounds memory access" in msg:
        return (
            "out_of_bounds",
            "Out-of-bounds memory access "
            "(if the trapping frame is gc_collect, see #515; "
            "otherwise check array indexing or string slicing)",
        )
    if "call stack exhausted" in msg:
        return (
            "stack_exhausted",
            "WASM call stack exhausted "
            "(tail-recursive functions blow the stack at "
            "~tens of thousands of frames until #517 ships TCO)",
        )
    if "unreachable" in msg:
        return (
            "unreachable",
            "Reached `unreachable` WASM instruction "
            "(typically a non-exhaustive match arm or an explicit panic)",
        )
    if "integer overflow" in msg:
        return ("overflow", "Integer overflow")

    # Couldn't classify — surface the raw wasmtime message verbatim so
    # the user still sees something diagnostic.
    return ("unknown", f"WASM trap: {exc}")


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
        data = _json.loads(resp.read().decode("utf-8"))

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

    # -----------------------------------------------------------------
    # Memory helpers for host → WASM string/ADT allocation
    # -----------------------------------------------------------------

    def _read_wasm_string(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> str:
        """Read a UTF-8 string from WASM memory."""
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)  # noqa: S101
        buf = memory.data_ptr(store)
        return bytes(buf[ptr:ptr + length]).decode("utf-8")

    def _write_bytes(
        caller: wasmtime.Caller, offset: int, data: bytes,
    ) -> None:
        """Write raw bytes into WASM linear memory."""
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)  # noqa: S101
        buf = memory.data_ptr(store)
        for i, b in enumerate(data):
            buf[offset + i] = b

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
        backing_ptr = _call_alloc(caller, count * 8)
        for i, s in enumerate(strings):
            str_ptr, str_len = _alloc_string(caller, s)
            _write_i32(caller, backing_ptr + i * 8, str_ptr)
            _write_i32(caller, backing_ptr + i * 8 + 4, str_len)
        return (backing_ptr, count)

    def _alloc_result_ok_i32(
        caller: wasmtime.Caller, value: int,
    ) -> int:
        """Allocate Result.Ok(i32) — wraps a heap pointer in Ok."""
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
        text = data.decode("utf-8")
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
        text = data.decode("utf-8")
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
        last_violation.append(data.decode("utf-8"))

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
            try:
                doc = _md_parse(text)
                block_ptr = write_md_block(
                    caller, _call_alloc, _write_i32,
                    _write_bytes, _alloc_string, doc,
                )
                return _alloc_result_ok_i32(caller, block_ptr)
            except Exception as exc:
                return _alloc_result_err_string(caller, str(exc))

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

    # Map store is needed for direct Map ops, Json (JObject), and Html (HtmlElement attrs).
    if result.map_ops_used or result.json_ops_used or result.html_ops_used:
        # Handle table: maps i32 handles to Python dicts.
        _map_store: dict[int, dict[object, object]] = {}
        _map_next_handle = [1]

        def _map_alloc(d: dict[object, object]) -> int:
            h = _map_next_handle[0]
            _map_next_handle[0] = h + 1
            _map_store[h] = d
            return h

    if result.map_ops_used:
        # map_new() → i32 handle
        def host_map_new(_caller: wasmtime.Caller) -> int:
            return _map_alloc({})

        linker.define_func(
            "vera", "map_new",
            wasmtime.FuncType([], [wasmtime.ValType.i32()]),
            host_map_new, access_caller=True,
        )

        # Dynamically define type-specific Map host imports based on
        # what the compiled program actually uses.
        _KEY_READERS = {
            "i": lambda _c, k: k,            # i64 key as-is
            "f": lambda _c, k: k,            # f64 key as-is
            "b": lambda _c, k: k,            # i32 key as-is
            "s": lambda c, p, l: _read_wasm_string(c, p, l),  # String
        }

        def _define_map_insert(kt: str, vt: str) -> None:
            name = f"map_insert$k{kt}_v{vt}"
            key_types = _VAL_WASM_TYPES[kt]
            val_types = _VAL_WASM_TYPES[vt]
            param_types = (
                [wasmtime.ValType.i32()]  # handle
                + key_types + val_types
            )
            ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

            if kt == "s" and vt == "s":
                def host_fn(
                    caller: wasmtime.Caller,
                    h: int, kp: int, kl: int, vp: int, vl: int,
                ) -> int:
                    k = _read_wasm_string(caller, kp, kl)
                    v = _read_wasm_string(caller, vp, vl)
                    new_d = dict(_map_store.get(h, {}))
                    new_d[k] = v
                    return _map_alloc(new_d)
            elif kt == "s":
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller,
                    h: int, kp: int, kl: int, v: int | float,
                ) -> int:
                    k = _read_wasm_string(caller, kp, kl)
                    new_d = dict(_map_store.get(h, {}))
                    new_d[k] = v
                    return _map_alloc(new_d)
            elif vt == "s":
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller,
                    h: int, k: int | float, vp: int, vl: int,
                ) -> int:
                    v = _read_wasm_string(caller, vp, vl)
                    new_d = dict(_map_store.get(h, {}))
                    new_d[k] = v
                    return _map_alloc(new_d)
            else:
                def host_fn(  # type: ignore[misc]
                    _caller: wasmtime.Caller,
                    h: int, k: int | float, v: int | float,
                ) -> int:
                    new_d = dict(_map_store.get(h, {}))
                    new_d[k] = v
                    return _map_alloc(new_d)

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
                    h: int, kp: int, kl: int,
                ) -> int:
                    k = _read_wasm_string(caller, kp, kl)
                    d = _map_store.get(h, {})
                    return _make_option(caller, d.get(k))
            else:
                def host_fn(  # type: ignore[misc]
                    caller: wasmtime.Caller,
                    h: int, k: int | float,
                ) -> int:
                    d = _map_store.get(h, {})
                    return _make_option(caller, d.get(k))

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
                    h: int, kp: int, kl: int,
                ) -> int:
                    k = _read_wasm_string(caller, kp, kl)
                    return 1 if k in _map_store.get(h, {}) else 0
            else:
                def host_fn(  # type: ignore[misc]
                    _caller: wasmtime.Caller,
                    h: int, k: int | float,
                ) -> int:
                    return 1 if k in _map_store.get(h, {}) else 0

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        def _define_map_remove(kt: str) -> None:
            name = f"map_remove$k{kt}"
            key_types = _VAL_WASM_TYPES[kt]
            param_types = [wasmtime.ValType.i32()] + key_types
            ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

            if kt == "s":
                def host_fn(
                    caller: wasmtime.Caller,
                    h: int, kp: int, kl: int,
                ) -> int:
                    k = _read_wasm_string(caller, kp, kl)
                    new_d = dict(_map_store.get(h, {}))
                    new_d.pop(k, None)
                    return _map_alloc(new_d)
            else:
                def host_fn(  # type: ignore[misc]
                    _caller: wasmtime.Caller,
                    h: int, k: int | float,
                ) -> int:
                    new_d = dict(_map_store.get(h, {}))
                    new_d.pop(k, None)
                    return _map_alloc(new_d)

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        # map_size(h) → i64
        def host_map_size(
            _caller: wasmtime.Caller, h: int,
        ) -> int:
            return len(_map_store.get(h, {}))

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
                caller: wasmtime.Caller, h: int,
            ) -> tuple[int, int]:
                d = _map_store.get(h, {})
                keys = list(d.keys())
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
                caller: wasmtime.Caller, h: int,
            ) -> tuple[int, int]:
                d = _map_store.get(h, {})
                vals = list(d.values())
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
        _set_store: dict[int, set[object]] = {}
        _set_next_handle = [1]

        def _set_alloc(s: set[object]) -> int:
            h = _set_next_handle[0]
            _set_next_handle[0] = h + 1
            _set_store[h] = s
            return h

        # set_new() → i32 handle
        def host_set_new(_caller: wasmtime.Caller) -> int:
            return _set_alloc(set())

        linker.define_func(
            "vera", "set_new",
            wasmtime.FuncType([], [wasmtime.ValType.i32()]),
            host_set_new, access_caller=True,
        )

        def _define_set_add(et: str) -> None:
            name = f"set_add$e{et}"
            elem_types = _VAL_WASM_TYPES[et]
            param_types = [wasmtime.ValType.i32()] + elem_types
            ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

            if et == "s":
                def host_fn(
                    caller: wasmtime.Caller, h: int, ep: int, el: int,
                ) -> int:
                    e = _read_wasm_string(caller, ep, el)
                    new_s = set(_set_store.get(h, set()))
                    new_s.add(e)
                    return _set_alloc(new_s)
            elif et == "i":
                def host_fn(  # type: ignore[misc]
                    _caller: wasmtime.Caller, h: int, e: int,
                ) -> int:
                    new_s = set(_set_store.get(h, set()))
                    new_s.add(e)
                    return _set_alloc(new_s)
            elif et == "f":
                def host_fn(  # type: ignore[misc]
                    _caller: wasmtime.Caller, h: int, e: float,
                ) -> int:
                    new_s = set(_set_store.get(h, set()))
                    new_s.add(e)
                    return _set_alloc(new_s)
            else:  # "b" — Bool/Byte/ADT handle
                def host_fn(  # type: ignore[misc]
                    _caller: wasmtime.Caller, h: int, e: int,
                ) -> int:
                    new_s = set(_set_store.get(h, set()))
                    new_s.add(e)
                    return _set_alloc(new_s)

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
                    caller: wasmtime.Caller, h: int, ep: int, el: int,
                ) -> int:
                    e = _read_wasm_string(caller, ep, el)
                    return 1 if e in _set_store.get(h, set()) else 0
            elif et == "f":
                def host_fn(  # type: ignore[misc]
                    _caller: wasmtime.Caller, h: int, e: float,
                ) -> int:
                    return 1 if e in _set_store.get(h, set()) else 0
            else:  # "i" or "b"
                def host_fn(  # type: ignore[misc]
                    _caller: wasmtime.Caller, h: int, e: int,
                ) -> int:
                    return 1 if e in _set_store.get(h, set()) else 0

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        def _define_set_remove(et: str) -> None:
            name = f"set_remove$e{et}"
            elem_types = _VAL_WASM_TYPES[et]
            param_types = [wasmtime.ValType.i32()] + elem_types
            ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

            if et == "s":
                def host_fn(
                    caller: wasmtime.Caller, h: int, ep: int, el: int,
                ) -> int:
                    e = _read_wasm_string(caller, ep, el)
                    new_s = set(_set_store.get(h, set()))
                    new_s.discard(e)
                    return _set_alloc(new_s)
            elif et == "f":
                def host_fn(  # type: ignore[misc]
                    _caller: wasmtime.Caller, h: int, e: float,
                ) -> int:
                    new_s = set(_set_store.get(h, set()))
                    new_s.discard(e)
                    return _set_alloc(new_s)
            else:  # "i" or "b"
                def host_fn(  # type: ignore[misc]
                    _caller: wasmtime.Caller, h: int, e: int,
                ) -> int:
                    new_s = set(_set_store.get(h, set()))
                    new_s.discard(e)
                    return _set_alloc(new_s)

            linker.define_func(
                "vera", name, ftype, host_fn, access_caller=True,
            )

        # set_size() — unparameterised, always i32 → i64
        def host_set_size(_caller: wasmtime.Caller, h: int) -> int:
            return len(_set_store.get(h, set()))

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
                caller: wasmtime.Caller, h: int,
            ) -> tuple[int, int]:
                elems = list(_set_store.get(h, set()))
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
                    # Allocate Some(handle)
                    handle = _decimal_alloc(d)
                    return _alloc_option_some_i32(caller, handle)
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
                divisor = _decimal_store[b]
                if divisor == 0:
                    return _alloc_option_none(caller)
                handle = _decimal_alloc(_decimal_store[a] / divisor)
                return _alloc_option_some_i32(caller, handle)
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
                json_ptr = write_json(
                    caller, _call_alloc, _write_i32, _write_f64,
                    _alloc_string, _map_alloc, parsed,
                )
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
                    _read_wasm_string, _map_store,
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
                try:
                    parser = _VeraHTMLParser()
                    parser.feed(text)
                    root = parser.get_root()
                    html_ptr = write_html(
                        caller, _call_alloc, _write_i32,
                        _alloc_string, _map_alloc, root,
                    )
                    return _alloc_result_ok_i32(caller, html_ptr)
                except Exception as exc:
                    return _alloc_result_err_string(caller, str(exc))

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
                    _read_wasm_string, _map_store,
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
                    _read_wasm_string, _map_store,
                )
                selector = _read_wasm_string(caller, sel_ptr, sel_len)
                matches = _html_query_py(node, selector)
                count = len(matches)
                if count > 0:
                    arr_ptr = _call_alloc(caller, count * 4)
                    for i, m in enumerate(matches):
                        m_ptr = write_html(
                            caller, _call_alloc, _write_i32,
                            _alloc_string, _map_alloc, m,
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
                    _read_wasm_string, _map_store,
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
                        body = resp.read().decode("utf-8")
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
                        response_body = resp.read().decode("utf-8")
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
        # IO.exit(code) — return captured output with exit code
        return ExecuteResult(
            value=None,
            stdout=output_buf.getvalue(),
            stderr=stderr_buf.getvalue() if stderr_buf is not None else "",
            state={k: v[-1] for k, v in state_store.items()},
            exit_code=exit_exc.code,
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
            kind, message = _classify_trap(exc, last_violation)
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
            ) from exc
        raise

    # Extract return value
    value: int | float | None
    if raw_result is None:
        value = None
    elif isinstance(raw_result, (tuple, list)):
        # Multi-value return (e.g. String/Array as (ptr, len))
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
    )
