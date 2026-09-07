"""#1442 — ``validate_handler`` must read the handler's VERA types.

The #305 serve driver marshals an ``HttpRequestData`` into a guest
``Request`` ADT, calls ``handle``, and decodes the returned pointer as a
``Response``.  Both halves are raw linear-memory work, so the guard in
front of them has to establish that ``handle`` really takes the prelude
``Request`` and really returns the prelude ``Response``.

It used to establish neither.  It asked two PROXY questions — are
``Request`` and ``Response`` in ``adt_layouts``, and does ``handle``
lower to ``["i32"]`` — and both proxies are satisfiable without the
handler having those types at all:

- the prelude injects the ADTs when the PROGRAM mentions them, so any
  other function can supply the layouts on ``handle``'s behalf; and
- ``i32`` is the lowered shape of ``Bool``, of every heap ADT, and of
  every boxed value, so the ABI cannot tell them apart.

A ``Bool``-typed ``handle`` therefore passed the guard, received the
Request pointer as a ``Bool``, handed it straight back, and the host
decoded it as a ``Response`` — reading a garbage headers pointer through
``_read_i32_at``, whose raw ``ctypes`` slice has no bounds check, past
the end of linear memory and into wasmtime's guard page.  That is a
``SIGBUS`` in the *host*: not a trap, not an exception, a dead process.

So the cells below come in two layers, and both are load-bearing:

1. **Identity** (``TestTheGuardReadsVeraTypes``, ``TestOwnershipAware``)
   — the guard refuses anything whose declared parameter/return is not
   the PRELUDE's ``Request``/``Response``, including a user ADT that
   shadows the prelude name.
2. **Containment** (``TestTheDecodersAreBoundsChecked``) — the raw
   readers refuse an out-of-bounds ``(offset, length)`` instead of
   reading it, so a future gap in layer 1 is a clean trap rather than a
   crash.

Nothing here reproduces the crash.  The cells assert the GUARD — that
an out-of-range pair raises before any slice is taken — which is a
property of the check and observable without faulting.  Reproducing a
``SIGBUS`` would kill the pytest worker, which reports nothing and
costs a host crash report per run; the pre-fix behaviour is recorded
once, in #1442, and belongs there rather than in the suite.
"""

from __future__ import annotations

from dataclasses import replace

import pytest
import wasmtime

from tests.codegen_helpers import _compile_ok
from vera.codegen.wasi import emit_wasi_component
from vera.runtime.heap import (
    _read_bytes_at,
    _read_f64,
    _read_i32,
    _read_i32_at,
    _require_readable,
)
from vera.wasm.markdown import _read_i32 as _md_read_i32
from vera.wasm.markdown import _read_i64 as _md_read_i64
from vera.runtime.server import make_server, validate_handler


# A String return forces a `memory` export and pulls in no host imports,
# so the module instantiates with an empty import list.
MEMORY_PROBE = """
public fn main(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }
"""

# A handler with the right types, for the control cells.
VALID = """
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{ Response(200, map_new(), "ok") }
"""

# `keep` mentions Request/Response, so the prelude injects both layouts;
# `handle` has nothing to do with them.  Both of the old guard's proxies
# are satisfied and neither of its questions is the real one.
BOOL_HANDLER_WITH_LAYOUTS = """
public fn keep(@Request -> @Response)
  requires(true) ensures(true) effects(pure)
{ Response(200, map_new(), "ok") }

public fn handle(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 }
"""

# Same trick, but the handler's types are a user ADT rather than a
# primitive: an ADT is a heap pointer, so it shares the `i32` ABI with
# Request/Response exactly.  The ABI proxy cannot separate these at all.
UNRELATED_ADT_HANDLER = """
private data Parcel {
  Parcel(Int)
}

public fn keep(@Request -> @Response)
  requires(true) ensures(true) effects(pure)
{ Response(200, map_new(), "ok") }

public fn handle(@Parcel -> @Parcel)
  requires(true) ensures(true) effects(pure)
{ @Parcel.0 }
"""

# Right parameter, wrong return: the request marshalling would succeed
# and the RESPONSE decode would read a Bool as a heap pointer.
RIGHT_PARAM_WRONG_RETURN = """
public fn keep(@Request -> @Response)
  requires(true) ensures(true) effects(pure)
{ Response(200, map_new(), "ok") }

public fn handle(@Request -> @Bool)
  requires(true) ensures(true) effects(pure)
{ true }
"""

# Wrong parameter, right return.  The mirror of the case above: the
# host allocates a Request and passes the pointer to a Bool parameter.
WRONG_PARAM_RIGHT_RETURN = """
public fn handle(@Bool -> @Response)
  requires(true) ensures(true) effects(pure)
{ Response(200, map_new(), "ok") }
"""

# Two parameters.  Arity was the one thing the ABI check did catch, so
# this cell pins that the rewrite did not lose it.
TWO_PARAMS = """
public fn keep(@Request -> @Response)
  requires(true) ensures(true) effects(pure)
{ Response(200, map_new(), "ok") }

public fn handle(@Request, @Int -> @Response)
  requires(true) ensures(true) effects(pure)
{ Response(200, map_new(), "ok") }
"""

# A VALID handler whose types are written through `type` aliases.
# `_declared_adt_name` resolves aliases via `naming.alias_body`, the
# same spine `_return_type_is_string` uses, so this is the prelude
# Request/Response and must be ACCEPTED.  Without that branch the guard
# sees a name the namespace does not declare as an ADT, answers None,
# and refuses a program that is entirely correct.
ALIASED_HANDLER = """
type Req = Request;

type Resp = Response;

public fn handle(@Req -> @Resp)
  requires(true) ensures(true) effects(<HttpServer>)
{ Response(200, map_new(), "ok") }
"""

# The entry file declares its own `data Request`, which SHADOWS the
# prelude's injection (`vera/prelude.py`, `_source_mentions_http_server`
# → "a user-defined data Request / data Response shadows the prelude").
# The name is spelled `Request` and the layout map has a `Request` key,
# so a NAME comparison accepts it — but it is a different type, with a
# different shape, owned by the entry file rather than the prelude.
SHADOWED_REQUEST = """
private data Request {
  Request(Int)
}

public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(pure)
{ Response(200, map_new(), "ok") }
"""


class TestTheGuardReadsVeraTypes:
    """The refusal is decided by the DECLARED types, not by the ABI."""

    @pytest.mark.parametrize(
        ("label", "src"),
        [
            ("bool handler, layouts from elsewhere", BOOL_HANDLER_WITH_LAYOUTS),
            ("unrelated ADT sharing the i32 ABI", UNRELATED_ADT_HANDLER),
            ("right parameter, wrong return", RIGHT_PARAM_WRONG_RETURN),
            ("wrong parameter, right return", WRONG_PARAM_RIGHT_RETURN),
            ("two parameters", TWO_PARAMS),
        ],
    )
    def test_refused(self, label: str, src: str) -> None:
        result = _compile_ok(src)
        with pytest.raises(ValueError, match="Request"):
            validate_handler(result)

    def test_the_valid_handler_is_still_accepted(self) -> None:
        """The control.  A guard that refuses everything is not a fix."""
        validate_handler(_compile_ok(VALID))

    def test_a_handler_written_through_type_aliases_is_accepted(self) -> None:
        """`type Req = Request` is still the prelude Request.

        The guard resolves aliases through `naming.alias_body`, so a
        handler spelled with them is the same handler.  This is the cell
        that fails if the alias branch of `_declared_adt_name` is
        removed: every refusal cell stays green without it, because
        refusing more is invisible to a suite that only checks refusals
        — a legitimate program silently flips to refused instead.
        """
        validate_handler(_compile_ok(ALIASED_HANDLER))

    def test_the_alias_resolves_to_the_prelude_type_not_the_alias_name(
        self,
    ) -> None:
        """Pin WHAT the resolution produces, not just that it passes.

        A guard that accepted `@Req` by some other route — treating an
        unknown name as acceptable, say — would pass the cell above
        while being far more permissive.  This asserts the recorded
        signature is the resolved prelude pair.
        """
        result = _compile_ok(ALIASED_HANDLER)
        assert result.fn_adt_signatures["handle"] == (("Request",), "Response")

    def test_the_layouts_really_are_present_in_the_refused_programs(
        self,
    ) -> None:
        """Pin the PREMISE of the cells above.

        If the prelude stopped injecting the layouts for these programs
        the refusals would still pass — for the old, wrong reason — and
        the cells would silently stop testing anything.
        """
        for src in (
            BOOL_HANDLER_WITH_LAYOUTS,
            UNRELATED_ADT_HANDLER,
            RIGHT_PARAM_WRONG_RETURN,
        ):
            result = _compile_ok(src)
            assert "Request" in result.adt_layouts
            assert "Response" in result.adt_layouts
            assert result.fn_param_types.get("handle") == ["i32"]


class TestOwnershipAware:
    """Identity, not spelling: whose ``Request`` is it?"""

    def test_an_entry_declared_request_is_not_the_prelude_request(
        self,
    ) -> None:
        result = _compile_ok(SHADOWED_REQUEST)
        # The premise: the name IS in the layout map, so a name-only
        # check would accept this program.
        assert "Request" in result.adt_layouts
        with pytest.raises(ValueError, match="Request"):
            validate_handler(result)

    def test_the_prelude_set_records_who_supplied_each_adt(self) -> None:
        shadowed = _compile_ok(SHADOWED_REQUEST)
        assert "Request" not in shadowed.prelude_injected_adts
        # `Response` was NOT shadowed, so the prelude still supplied it.
        assert "Response" in shadowed.prelude_injected_adts
        both = _compile_ok(VALID)
        assert {"Request", "Response"} <= both.prelude_injected_adts


class TestTheRefusalNamesTheRemedy:
    """Three ways to be wrong, three remedies, three messages.

    A single "must take @Request and return @Response" tells a reader
    with a shadowing `data Request` nothing at all — their program DOES
    say `@Request`.  These pin that each branch says which thing to
    change, not merely that something is wrong.
    """

    def _message(self, src: str) -> str:
        with pytest.raises(ValueError) as exc:
            validate_handler(_compile_ok(src))
        return str(exc.value)

    def test_a_shadowing_declaration_is_named_as_such(self) -> None:
        msg = self._message(SHADOWED_REQUEST)
        assert "shadows the prelude" in msg
        # And it must NOT read as the flat contradiction "its parameter
        # is @Request, not the prelude @Request".
        assert "not the prelude @Request" not in msg

    def test_a_different_data_type_is_named(self) -> None:
        msg = self._message(UNRELATED_ADT_HANDLER)
        assert "@Parcel" in msg
        assert "shadows" not in msg

    def test_a_non_data_type_says_so(self) -> None:
        msg = self._message(BOOL_HANDLER_WITH_LAYOUTS)
        assert "not a data type" in msg
        assert "shadows" not in msg

    def test_the_arity_message_reports_the_count(self) -> None:
        assert "2 parameter(s)" in self._message(TWO_PARAMS)

    def test_the_context_prefixes_the_refusal(self) -> None:
        """`context` names the surface that rejected the program."""
        with pytest.raises(ValueError, match="--target wasi-p2"):
            validate_handler(
                _compile_ok(BOOL_HANDLER_WITH_LAYOUTS),
                context="--target wasi-p2 --world server",
            )


class TestAnExportedHandlerWithNoSignature:
    """The one refusal that is not about the program.

    `handle` in `exports` with no entry in `fn_adt_signatures` cannot
    happen for a program codegen accepted -- the map is built from the
    same declarations codegen compiles.  If it ever does, the guard must
    still refuse (it cannot check what it cannot see), but it must not
    route through the arity branch and tell the author their handler
    "takes 0 parameter(s)", which is both false and unactionable.
    """

    def test_it_is_reported_as_an_internal_error(self) -> None:
        result = _compile_ok(VALID)
        # Exported, but with the recorded signature removed.
        stripped = replace(
            result,
            fn_adt_signatures={
                k: v for k, v in result.fn_adt_signatures.items()
                if k != "handle"
            },
        )
        assert "handle" in stripped.exports
        with pytest.raises(ValueError, match="internal error") as exc:
            validate_handler(stripped)
        assert "0 parameter(s)" not in str(exc.value)


class TestTheWasiValidatorRefusesToo:
    """Both serving surfaces share one guard, so both must refuse."""

    def test_wasi_server_world_refuses_the_bool_handler(self) -> None:
        result = _compile_ok(BOOL_HANDLER_WITH_LAYOUTS)
        with pytest.raises(ValueError, match="Request"):
            emit_wasi_component(result, world="server")

    def test_native_serving_refuses_the_bool_handler(self) -> None:
        result = _compile_ok(BOOL_HANDLER_WITH_LAYOUTS)
        with pytest.raises(ValueError, match="Request"):
            make_server(result, host="127.0.0.1", port=0)


class TestTheDecodersAreBoundsChecked:
    """``_read_i32_at`` / ``_read_bytes_at`` must refuse, not read.

    Containment for the bug above: the raw ``ctypes`` slice in these two
    helpers reads straight past the end of linear memory into wasmtime's
    guard page, which is a ``SIGBUS`` in the HOST process — not a guest
    trap, not an exception, a dead interpreter.  ``_read_wasm_string``
    was given exactly this guard under #1145; these two were left
    without one, and they are the readers ``decode_response_adt`` uses
    for the status, the headers pointer and the body ``(ptr, len)``.

    These cells NEVER provoke that fault.  They assert the guard turns
    an out-of-range pair into a clean ``wasmtime.WasmtimeError`` before
    the slice is reached, which is a property of the check and needs no
    crash to observe.  The pre-fix behaviour is recorded once, in #1442,
    and is deliberately not reproduced here: a cell that faults takes
    the pytest worker down with it and reports nothing.

    ``test_the_predicate_refuses_directly`` comes FIRST on purpose.  It
    drives ``_require_readable``, which decides and returns without
    touching memory, so it cannot fault however the code around it
    changes — if the guard is ever removed from the two readers, that
    cell fails cleanly and names the cause before any cell that would
    reach a raw slice.
    """

    def _memory_and_caller(self) -> tuple[int, object]:
        """A real instantiated module's memory, plus a Caller-alike.

        A ``String`` return forces a ``memory`` export and pulls in no
        host imports, so the module instantiates with an empty import
        list.  ``_FakeCaller`` supplies the only two surfaces the
        readers use: ``caller["memory"]`` and the ``_context()`` every
        wasmtime memory accessor calls on a store-like object.
        """
        result = _compile_ok(MEMORY_PROBE)
        engine = wasmtime.Engine()
        store = wasmtime.Store(engine)
        module = wasmtime.Module(engine, result.wasm_bytes)
        instance = wasmtime.Instance(store, module, [])
        memory = instance.exports(store)["memory"]

        class _FakeCaller:
            def __getitem__(self, key: str) -> object:
                if key == "memory":
                    return memory
                raise KeyError(key)

            def _context(self) -> object:
                return store._context()

        return memory.data_len(store), _FakeCaller()

    def test_the_predicate_refuses_directly(self) -> None:
        """``_require_readable`` decides without reading, so start here."""
        size, caller = self._memory_and_caller()
        memory = caller["memory"]
        for offset, nbytes, why in [
            (size + 4096, 4, "past the end"),
            (size - 2, 4, "straddling the end"),
            (-8, 4, "negative offset"),
            (0, -1, "negative length"),
            (16, size, "length overflowing the offset"),
        ]:
            with pytest.raises(wasmtime.WasmtimeError, match="out of bounds"):
                _require_readable(memory, caller, offset, nbytes, "probe")
        # And it permits what is genuinely in range.
        _require_readable(memory, caller, 0, 8, "probe")
        _require_readable(memory, caller, size - 4, 4, "probe")

    def test_read_i32_at_is_guarded(self) -> None:
        size, caller = self._memory_and_caller()
        for offset in (size + 4096, size - 2, -8):
            with pytest.raises(wasmtime.WasmtimeError, match="out of bounds"):
                _read_i32_at(caller, offset)

    def test_read_bytes_at_is_guarded(self) -> None:
        size, caller = self._memory_and_caller()
        for offset, length in ((size + 4096, 16), (size - 2, 16),
                               (-8, 16), (0, -1), (16, size)):
            with pytest.raises(wasmtime.WasmtimeError, match="out of bounds"):
                _read_bytes_at(caller, offset, length)

    def test_every_raw_reader_in_the_family_is_guarded(self) -> None:
        """The whole family, not the two on the Response path.

        The first fix guarded `_read_i32_at` / `_read_bytes_at` because
        those are what `decode_response_adt` uses.  That was the wrong
        boundary: `heap._read_i32` / `heap._read_f64` take the same raw
        slice and are reached from `read_json` on the `json_stringify`
        path, and `markdown._read_i32` / `_read_i64` are a third and
        fourth copy walking a guest-built AST by pointers read out of
        that AST.  In every one of them the offset is guest DATA rather
        than an allocator's answer, which is the property that makes a
        raw slice unsafe.

        Enumerated from the code (`memory.data_ptr` followed by a raw
        slice) rather than from memory, so the claim is checkable.  The
        two remaining `data_ptr` sites in the tree are WRITES into
        just-allocated regions at allocator-supplied offsets
        (`_ShadowGuard.push`, the String-argument marshaller in
        `codegen/api.py`) and are not part of this family.
        """
        size, caller = self._memory_and_caller()
        for reader, width, name in [
            (_read_i32, 4, "heap._read_i32"),
            (_read_f64, 8, "heap._read_f64"),
            (_md_read_i32, 4, "markdown._read_i32"),
            (_md_read_i64, 8, "markdown._read_i64"),
        ]:
            for offset in (size + 4096, size - (width - 2), -8):
                with pytest.raises(
                    wasmtime.WasmtimeError, match="out of bounds",
                ):
                    reader(caller, offset)
            # ...and each still reads what is genuinely in range.
            reader(caller, 0)
            reader(caller, size - width)

    def test_in_bounds_reads_still_work(self) -> None:
        """The control: a guard that refuses everything is not a fix."""
        size, caller = self._memory_and_caller()
        assert len(_read_bytes_at(caller, 0, 8)) == 8
        assert isinstance(_read_i32_at(caller, 0), int)
        # Exactly-at-the-limit reads are legal, not off-by-one refusals.
        assert len(_read_bytes_at(caller, size - 4, 4)) == 4
        assert isinstance(_read_i32_at(caller, size - 4), int)

    def test_the_message_names_the_offending_pair(self) -> None:
        """The refusal is classified as an OOB trap and says what it saw."""
        size, caller = self._memory_and_caller()
        with pytest.raises(wasmtime.WasmtimeError) as exc:
            _read_bytes_at(caller, size + 32, 16)
        msg = str(exc.value)
        # `execute()` classifies on this reason, so it is load-bearing.
        assert "out of bounds memory access" in msg
        assert str(size + 32) in msg and str(size) in msg
