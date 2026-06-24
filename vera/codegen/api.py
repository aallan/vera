"""Public API for the Vera code generator.

Standalone functions (``compile``, ``execute``), result dataclasses,
and ADT memory-layout helpers.  These are the only symbols imported
by external modules.

See spec/11-compilation.md for the compilation specification.
"""

from __future__ import annotations

import os
import sys
import time
from dataclasses import dataclass, field
from io import StringIO
from pathlib import Path
from typing import TYPE_CHECKING

import wasmtime

from vera import ast
from vera.runtime.decimal import register_decimal
from vera.runtime.heap import (
    _alloc_array_of_strings,
    _alloc_option_none,
    _alloc_option_some_string,
    _alloc_result_err_string,
    _alloc_result_ok_string,
    _alloc_result_ok_unit,
    _alloc_string,
    _read_wasm_string,
)
from vera.runtime.html import register_html
from vera.runtime.json import register_json
from vera.runtime.map import register_map
from vera.runtime.math import register_math
from vera.runtime.md import register_md
from vera.runtime.random import register_random
from vera.runtime.regex import register_regex
from vera.runtime.set import register_set
from vera.runtime.traps import (
    WasmTrapError as WasmTrapError,  # re-export: part of execute()'s contract
)
from vera.runtime.traps import (
    _classify_trap,
    _resolve_trap_frames,
)

if TYPE_CHECKING:
    from decimal import Decimal as PyDecimal

    from vera.errors import Diagnostic
    from vera.resolver import ResolvedModule


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
        register_md(linker)

    # -----------------------------------------------------------------
    # Regex host functions (§9.6.15)
    # -----------------------------------------------------------------

    if result.regex_ops_used:
        register_regex(linker)

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
    # #421: the Decimal value store is created up-front (outside the Decimal
    # branch) so the shared host_decref_handle below can close over it;
    # register_decimal populates it when Decimal ops are actually used.
    _decimal_store: dict[int, PyDecimal] = {}

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
        register_map(linker, result.map_ops_used)

    # -----------------------------------------------------------------
    # Set<T> host functions
    # -----------------------------------------------------------------

    if result.set_ops_used:
        register_set(linker, result.set_ops_used)

    # ── Decimal host functions ───────────────────────────────────
    if result.decimal_ops_used:
        register_decimal(linker, result.decimal_ops_used, _decimal_store, _host_store_refs)

    # -----------------------------------------------------------------
    # Json host functions
    # -----------------------------------------------------------------
    if result.json_ops_used:
        register_json(linker, result.json_ops_used)

    # -----------------------------------------------------------------
    # Html host functions (§9.7.4)
    # -----------------------------------------------------------------
    if result.html_ops_used:
        register_html(linker, result.html_ops_used)

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
                import os as _os

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
        register_random(linker, result.random_ops_used)
    # ---------------------------------------------------------------
    # Math host functions (#467).  Ten functions share one shape
    # (Float64 → Float64) except `atan2` which takes two.  All are
    # thin wrappers over Python's `math` module — IEEE 754
    # semantics (NaN for out-of-domain inputs, ±inf for overflow)
    # are preserved across the WASM boundary.
    # ---------------------------------------------------------------
    if result.math_ops_used:
        register_math(linker, result.math_ops_used)
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
