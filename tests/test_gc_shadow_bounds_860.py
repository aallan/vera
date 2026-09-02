"""#860 — the four sibling shadow-stack bounds, made slot-complete.

#791 fixed ``_ShadowGuard.push`` (``vera/runtime/heap.py``): the push writes a
FOUR-byte slot at ``[sp..sp+3]``, so its overflow bound has to reject
``sp + 4 > limit``, not ``sp >= limit``.  A ``gc_sp`` left with 1-3 bytes of
headroom passed the slot-start check and then spilled past the shadow-stack
window into the adjacent GC worklist region.

That PR's sweep found four structurally identical bounds elsewhere, each
protected by the same alignment invariant (generated code advances ``gc_sp``
in 4-byte steps from a 4-aligned base) and each therefore unreachable while
the invariant holds — defence in depth for the GC trust root, not a live-bug
regression:

* ``gc_shadow_push`` in ``vera/wasm/helpers.py`` — the WAT emitter;
* the ``$register_wrapper`` slow-path root push in
  ``vera/codegen/assembly.py``;
* ``gcRooted`` and ``gcShadowPush`` in ``vera/browser/runtime.mjs``.

Two instruments, because the two halves fail differently:

* the WAT emitter is *executed* against a hand-built module whose ``gc_sp``
  is placed at each headroom — the only way to show the bound actually
  rejects, since no compiled Vera program can reach a misaligned ``gc_sp``;
* the other three are pinned by COMPLETENESS: no shadow-stack bound anywhere
  in the emitted module or in the browser runtime may still use the
  slot-start form.  A count or a spot-check would pass while a fifth site
  kept the old shape; asking "is any site still slot-start?" cannot.
"""
from __future__ import annotations

import re
import struct
from pathlib import Path

import pytest
import wasmtime

from vera.wasm.helpers import gc_shadow_push

from tests.codegen_helpers import _compile_ok


_RUNTIME_MJS = Path(__file__).resolve().parents[1] / "vera" / "browser" / "runtime.mjs"


class TestEmittedShadowPushBoundIsSlotComplete860:
    """The WAT ``gc_shadow_push`` sequence, executed at each headroom.

    Mirrors ``TestShadowGuardPushBound791`` on the host side, and for the
    same reason it hand-builds a module rather than compiling Vera: the
    misaligned ``gc_sp`` this bound exists for cannot be produced by
    generated code.
    """

    # Shadow-stack window [64, 96) — 8 slots, 4-aligned like the real
    # layout.  Memory past `limit` is zero-initialised, so a spill is
    # observable as non-zero bytes.
    _STACK_BASE = 64
    _STACK_LIMIT = 96

    def _instance(self) -> tuple[wasmtime.Store, wasmtime.Instance]:
        body = "\n".join(f"    {i}" for i in gc_shadow_push(0))
        wat = (
            "(module\n"
            '  (memory (export "memory") 1)\n'
            f'  (global $gc_sp (export "gc_sp") (mut i32) '
            f"(i32.const {self._STACK_BASE}))\n"
            f'  (global $gc_stack_limit (export "gc_stack_limit") i32 '
            f"(i32.const {self._STACK_LIMIT}))\n"
            '  (func (export "push") (param i32)\n'
            f"{body}\n"
            "  )\n"
            ")\n"
        )
        engine = wasmtime.Engine()
        store = wasmtime.Store(engine)
        instance = wasmtime.Instance(
            store, wasmtime.Module(engine, wat), [],
        )
        return store, instance

    @pytest.mark.parametrize("headroom", [1, 2, 3])
    def test_push_traps_on_a_partial_final_slot(self, headroom: int) -> None:
        """1-3 bytes of headroom cannot hold the 4-byte slot.

        Under the slot-start bound the check passed and ``i32.store``
        wrote ``4 - headroom`` bytes past ``$gc_stack_limit``, into the
        GC worklist region the mark phase reads.
        """
        store, instance = self._instance()
        sp = instance.exports(store)["gc_sp"]
        assert isinstance(sp, wasmtime.Global)
        sp.set_value(store, self._STACK_LIMIT - headroom)
        push = instance.exports(store)["push"]
        assert isinstance(push, wasmtime.Func)
        with pytest.raises(wasmtime.Trap):
            push(store, 0x1234)
        memory = instance.exports(store)["memory"]
        assert isinstance(memory, wasmtime.Memory)
        spill = bytes(memory.read(
            store,
            self._STACK_LIMIT - headroom,
            self._STACK_LIMIT - headroom + 4,
        ))
        assert spill == b"\x00" * 4, (
            f"a partial slot leaked past the window at headroom {headroom}: "
            f"{spill!r}"
        )

    def test_push_accepts_the_exact_final_slot(self) -> None:
        """``sp == limit - 4`` is the LAST valid slot.

        Guards against over-tightening to ``sp + 4 >= limit``, which
        would silently shrink the shadow stack by one root.
        """
        store, instance = self._instance()
        exports = instance.exports(store)
        sp = exports["gc_sp"]
        assert isinstance(sp, wasmtime.Global)
        sp.set_value(store, self._STACK_LIMIT - 4)
        push = exports["push"]
        assert isinstance(push, wasmtime.Func)
        push(store, 0x1234)
        assert sp.value(store) == self._STACK_LIMIT
        memory = exports["memory"]
        assert isinstance(memory, wasmtime.Memory)
        assert bytes(memory.read(
            store, self._STACK_LIMIT - 4, self._STACK_LIMIT,
        )) == struct.pack("<I", 0x1234)

    def test_push_traps_on_a_full_window(self) -> None:
        """``sp == limit`` was rejected by the old bound too — pin it."""
        store, instance = self._instance()
        exports = instance.exports(store)
        sp = exports["gc_sp"]
        assert isinstance(sp, wasmtime.Global)
        sp.set_value(store, self._STACK_LIMIT)
        push = exports["push"]
        assert isinstance(push, wasmtime.Func)
        with pytest.raises(wasmtime.Trap):
            push(store, 0x1234)


# The slot-START form, in the emitted WAT: read `$gc_sp`, compare it
# straight against `$gc_stack_limit`.  Whitespace-tolerant so indentation
# inside `$register_wrapper` does not hide a match.
_SLOT_START_WAT = re.compile(
    r"global\.get \$gc_sp\s+global\.get \$gc_stack_limit\s+i32\.ge_u",
)

# The slot-COMPLETE form: `$gc_sp + 4` against `$gc_stack_limit`.
_SLOT_COMPLETE_WAT = re.compile(
    r"global\.get \$gc_sp\s+i32\.const 4\s+i32\.add\s+"
    r"global\.get \$gc_stack_limit\s+i32\.gt_u",
)

# The slot-START form in JavaScript: `sp` compared straight against the
# limit global's value.
_SLOT_START_JS = re.compile(r"sp\s*>=\s*wasm\.gc_stack_limit\.value")

# The slot-COMPLETE form in JavaScript, matching `_ShadowGuard.push`'s
# predicate (negative `sp` rejected outright).
_SLOT_COMPLETE_JS = re.compile(
    r"sp\s*<\s*0\s*\|\|\s*sp\s*\+\s*4\s*>\s*wasm\.gc_stack_limit\.value",
)


def _fn_body(wat: str, name: str) -> str:
    """The WAT text of ``$name``, up to the next top-level ``(func``.

    Scoping the assertion to one function is the whole point of the
    ``$register_wrapper`` cell: every allocating function in a module carries
    a shadow bound, so a module-wide search is answered by any of them.
    """
    start = wat.index(f"(func ${name} ")
    rest = wat[start + 1:]
    nxt = rest.find("\n  (func ")
    return rest if nxt < 0 else rest[:nxt]


# A program that needs BOTH the shadow stack and the wrap table, so the
# emitted module carries `$register_wrapper` (whose slow path holds the
# fourth bound) alongside ordinary `gc_shadow_push` sites.
_WRAP_TABLE_SOURCE = """\
public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match map_get(map_insert(map_new(), "k", 1), "k") {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
"""


class TestEveryShadowBoundIsSlotComplete860:
    """Completeness, not a count: NO site may keep the slot-start form.

    A per-site assertion would pass while a fifth bound was added with the
    old shape — the sweep #791 had to do by hand.  Asking the whole
    artefact whether any slot-start bound survives is what makes a new one
    fail on arrival.
    """

    def test_emitted_module_has_no_slot_start_bound(self) -> None:
        wat = _compile_ok(_WRAP_TABLE_SOURCE).wat
        assert "$register_wrapper" in wat, (
            "fixture no longer emits $register_wrapper — the fourth bound "
            "is not in the artefact under test"
        )
        assert not _SLOT_START_WAT.search(wat), (
            "an emitted shadow-stack bound still compares $gc_sp directly "
            "against $gc_stack_limit; the push writes four bytes, so the "
            "bound must be on $gc_sp + 4 (#860)"
        )

    def test_emitted_module_carries_the_slot_complete_bound(self) -> None:
        """The negative half alone would pass on a module with no bound
        at all — assert the replacement is actually present.

        Counted per SITE, not module-wide: a module-wide count of two is
        satisfied by two ordinary ``gc_shadow_push`` bounds while
        ``$register_wrapper``'s slow path keeps the old shape, which is
        exactly the site a module-wide count was meant to cover.  So the
        wrapper's body is extracted and asked on its own.
        """
        wat = _compile_ok(_WRAP_TABLE_SOURCE).wat
        assert _SLOT_COMPLETE_WAT.search(wat), (
            "no slot-complete bound anywhere in the emitted module"
        )
        wrapper = _fn_body(wat, "register_wrapper")
        assert _SLOT_COMPLETE_WAT.search(wrapper), (
            "$register_wrapper's slow-path root push does not carry the "
            f"slot-complete bound:\n{wrapper}"
        )
        assert not _SLOT_START_WAT.search(wrapper), (
            f"$register_wrapper still carries a slot-start bound:\n{wrapper}"
        )

    def test_browser_runtime_has_no_slot_start_bound(self) -> None:
        source = _RUNTIME_MJS.read_text(encoding="utf-8")
        assert not _SLOT_START_JS.search(source), (
            "a browser-runtime shadow-stack bound still compares sp "
            "directly against gc_stack_limit (#860)"
        )

    def test_browser_runtime_carries_both_slot_complete_bounds(self) -> None:
        source = _RUNTIME_MJS.read_text(encoding="utf-8")
        assert len(_SLOT_COMPLETE_JS.findall(source)) == 2, (
            "expected the slot-complete bound in exactly the two browser "
            "push sites, gcRooted and gcShadowPush"
        )
