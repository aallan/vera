"""Widths and pointer-ness at a closure/effect boundary: #1255, #1256, #1269.

Three defects of one seam — a boundary asks what a declared type IS, and
answers from something other than that type.  Each is the #1213 thesis
(one fact, one derivation) at a different boundary:

* **#1255** — GC pointer-ness was classified from the SYNTACTIC type head.
  ``_type_expr_to_slot_name(te) not in ('Bool', 'Byte', None)`` sees
  ``SmallByte``, never the ``Byte`` it resolves to, so an alias or
  refinement over a scalar was rooted on the GC shadow stack at every
  closure boundary (parameter, return, capture) and at the named-function
  twins.  Inert today only because the root scan's first guard rejects a
  value below ``gc_heap_start`` and the string pool holds that above 259 —
  an invariant nothing enforced.  The cost was a shadow slot and six dead
  instructions per boundary; the exposure was a build with an empty string
  pool.
* **#1256** — the ``apply_fn`` call-site ``call_indirect`` signature took
  each parameter's width from the ARGUMENT's inferred type, while the
  lifted closure's own signature takes it from the DECLARED formal.  A
  ``@Byte`` formal fed an int literal registered two incompatible
  ``$closure_sig`` types for one call and trapped with ``indirect call type
  mismatch``.  The result width was already derived from the closure type
  (``_infer_apply_fn_return_type``); the parameters now come from the same
  place.
* **#1269** — ``throw``'s payload was not a ``@Byte`` write boundary.  The
  ``Exn<E>`` tag's width is derived from the resolved family base and was
  correct at i32 all along; the thrown literal defaulted to ``i64.const``,
  so ``throw(5)`` into ``Exn<{@Byte | …}>`` emitted a module WASM
  validation rejects.  This is the #1212 marking machinery meeting one more
  boundary, not a classification defect — the fix is the same
  ``_mark_byte_write_value`` every other write boundary drives.

The last two share the #1212 marking half: once ``apply_fn``'s signature
says i32, the literal argument must lower at i32 too, which is the same
extension ``throw``'s payload needs.  They are fixed by ONE derivation of
the boundary's representation base (``WasmContext._boundary_base``) driving
one marking, so the two boundaries cannot disagree the way the two sides of
#1256 did.

Every test carries a VALUE oracle rather than "it compiles": a width defect
that happened to validate would still read back the wrong number.  The
#1255 tests assert on emitted WAT (the push is the whole observable — the
defect is inert at runtime by construction) and are paired with
``VERA_EAGER_GC=1`` runs, which force a collection at every allocation so a
genuinely missing root would surface as a use-after-free rather than as
luck.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from tests.codegen_helpers import _compile_ok, _run
from vera.codegen import (
    CompileResult,
    assembly,
    compile as _vera_compile,
    execute,
)
from vera.parser import parse_file
from vera.resolver import ModuleResolver
from vera.skip import CodegenInvariantError
from vera.transform import transform
from vera.wasm.helpers import MAX_INLINE_I32_VALUE

# =====================================================================
# Shared fixtures
# =====================================================================

# The three spellings of one scalar, substituted into a single program
# template.  `Byte` is the base written directly and is the ORACLE the other
# two are compared against — an alias behaves exactly like its target
# written directly, which is the invariant the alias canonicalisers already
# state and the one #1255 broke for rooting alone.
_BASE = ("Byte", "")
_REFINEMENT = ("SmallByte",
               "type SmallByte = { @Byte | byte_to_int(@Byte.0) < 100 };\n")
_ALIAS = ("Octet", "type Octet = Byte;\n")

# A `@Byte`-producing helper that is not a literal, so a fixture can build a
# value of the type under test without depending on the literal-width
# machinery that is itself under test in the #1256/#1269 half of this file.
# Its own return type is the substituted name, so `mk` is a fourth instance
# of the named-function boundary rather than a `Byte`-typed escape hatch.
_MK = """
private fn mk(@Int -> @{T})
  requires(@Int.0 >= 0 && @Int.0 < 100)
  ensures(true)
  effects(pure)
{{
  match int_to_byte(@Int.0) {{
    Some(@Byte) -> @Byte.0,
    None -> 0
  }}
}}
"""

# The opening of a `gc_shadow_push` sequence: the slot-complete overflow
# bound (#860 — `$gc_sp + 4` against `$gc_stack_limit`, since the store
# writes four bytes).  Matching the bound rather than the store is what
# keeps this a PUSH count: the `$gc_sp` restore that closes a function or a
# match scope reads the same global and stores nothing.
_SHADOW_PUSH = re.compile(
    r"global\.get \$gc_sp\n\s*i32\.const 4\n\s*i32\.add"
    r"\n\s*global\.get \$gc_stack_limit")


def _fn_body(wat: str, name: str) -> str:
    """The WAT text of function *name*, up to the next top-level ``(func``.

    Scoped rather than whole-module because every allocating function in the
    module pushes SOMETHING; the claim under test is about one function's
    roots, and a module-wide count would be satisfied by any other push.
    """
    start = wat.index(f"(func ${name} ")
    rest = wat[start + 1:]
    nxt = rest.find("\n  (func ")
    return rest if nxt < 0 else rest[:nxt]


def _shadow_pushes(wat: str, fn: str) -> int:
    return len(_SHADOW_PUSH.findall(_fn_body(wat, fn)))


def _pushes_for(template: str, spelling: tuple[str, str], fn: str) -> int:
    """Shadow-stack pushes in *fn* when *template* is spelled with *spelling*.

    The template carries `{T}` at every position of the type under test and
    `{PRELUDE}` where its declaration goes, so the three spellings differ in
    NOTHING but the name — which is what makes an inequality below a
    statement about the classification rather than about two programs.
    """
    name, prelude = spelling
    source = template.format(T=name, PRELUDE=prelude, MK=_MK.format(T=name))
    return _shadow_pushes(_compile_ok(source).wat, fn)


# =====================================================================
# #1255 — pointer-ness resolves through the alias chain
# =====================================================================

# The closure RETURN boundary (`vera/codegen/closures.py`,
# `ret_is_pointer`).  The closure body does not allocate, which is the shape
# that emits the return push and nothing else.
_CLOSURE_RETURN = """{PRELUDE}{MK}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  byte_to_int(apply_fn(fn(@Int -> @{T}) effects(pure) {{
    mk(@Int.0)
  }}, 37))
}}
"""

# The closure PARAMETER boundary (`gc_pointer_params`).  The body allocates
# (`int_to_string`), which is what emits the parameter prologue at all — and
# is also why the counts below are not zero: that intermediate String is a
# genuine root.  The differential is what isolates the parameter's own
# classification from it.
_CLOSURE_PARAM = """{PRELUDE}{MK}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  apply_fn(fn(@{T} -> @Int) effects(pure) {{
    let @String = int_to_string(byte_to_int(@{T}.0));
    byte_to_int(@{T}.0)
  }}, mk(37))
}}
"""

# The closure CAPTURE boundary (`gc_capture_pushes`) — the only one of the
# five carrying a slot NAME rather than a type expression, so it resolves
# through the name hop instead.
_CLOSURE_CAPTURE = """{PRELUDE}{MK}
private fn hold(@{T} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @{T} = @{T}.0;
  apply_fn(fn(@Int -> @Int) effects(pure) {{
    let @String = int_to_string(@Int.0);
    byte_to_int(@{T}.0) + @Int.0
  }}, 0)
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  hold(mk(37))
}}
"""

# The NAMED-function twins (`vera/codegen/functions.py`), which carry the
# same two classifications over the same alias chain.  The body allocates so
# the GC prologue/epilogue is emitted at all.
_NAMED_FN = """{PRELUDE}{MK}
private fn roundtrip(@{T} -> @{T})
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @String = int_to_string(byte_to_int(@{T}.0));
  @{T}.0
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  byte_to_int(roundtrip(mk(37)))
}}
"""

_BOUNDARIES = [
    pytest.param(_CLOSURE_RETURN, "anon_0", id="closure_return"),
    pytest.param(_CLOSURE_PARAM, "anon_0", id="closure_param"),
    pytest.param(_CLOSURE_CAPTURE, "anon_0", id="closure_capture"),
    pytest.param(_NAMED_FN, "roundtrip", id="named_fn_param_and_return"),
]

# The pointer CONTROLS: a genuine heap pointer at each of the same four
# boundaries.  Without them, "roots like its base" is equally satisfied by a
# fix that switched the rooting off everywhere — which is a use-after-free,
# the thing the push exists to prevent.
_CONTROL_CLOSURE_RETURN = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_length(apply_fn(fn(@Int -> @String) effects(pure) {
    int_to_string(@Int.0)
  }, 37))
}
"""

_CONTROL_CLOSURE_PARAM = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@String -> @Int) effects(pure) {
    string_length(string_concat(@String.0, "x"))
  }, "ab")
}
"""

_CONTROL_CLOSURE_CAPTURE = """
private fn hold(@String -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @String = @String.0;
  apply_fn(fn(@Int -> @Int) effects(pure) {
    string_length(string_concat(@String.0, int_to_string(@Int.0)))
  }, 1)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  hold("ab")
}
"""

_CONTROL_NAMED_FN = """
private fn roundtrip(@String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(@String.0, "!")
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_length(roundtrip("ab"))
}
"""


class TestPointerNessResolvesThroughTheAliasChain:
    """#1255: a refined or aliased scalar is not a heap pointer.

    The oracle is a DIFFERENTIAL against the base spelling rather than an
    absolute push count: these bodies allocate (they must, or no prologue is
    emitted at all), so they legitimately root their own intermediates, and
    a bare count would be measuring those too.  Comparing `@SmallByte` and
    `@Octet` against `@Byte` in the otherwise identical program isolates the
    one decision — and states the invariant the fix is FOR, which is that an
    alias behaves exactly like its target written directly.

    Each is paired with a pointer control at the same boundary, because
    "roots like its base" is equally satisfied by rooting nothing anywhere.
    """

    @pytest.mark.parametrize(("template", "fn"), _BOUNDARIES)
    @pytest.mark.parametrize(
        "spelling",
        [pytest.param(_REFINEMENT, id="refinement"),
         pytest.param(_ALIAS, id="alias")],
    )
    def test_a_hidden_scalar_roots_exactly_as_the_base_spelling_does(
        self, template: str, fn: str, spelling: tuple[str, str],
    ) -> None:
        """Pre-fix the hidden spelling rooted a 0..255 value the base did not."""
        hidden = _pushes_for(template, spelling, fn)
        base = _pushes_for(template, _BASE, fn)
        assert hidden == base, (spelling[0], hidden, base)

    @pytest.mark.parametrize(
        ("template", "fn", "expected"),
        [
            pytest.param(_CLOSURE_RETURN, "anon_0", 0, id="closure_return"),
            pytest.param(_CLOSURE_PARAM, "anon_0", 5, id="closure_param"),
            pytest.param(_CLOSURE_CAPTURE, "anon_0", 5, id="closure_capture"),
            pytest.param(_NAMED_FN, "roundtrip", 4,
                         id="named_fn_param_and_return"),
        ],
    )
    def test_the_base_spellings_own_count_is_pinned(
        self, template: str, fn: str, expected: int,
    ) -> None:
        """The differential's other half: what `@Byte` alone roots.

        Equality above would also hold if BOTH spellings rooted the scalar —
        the state a mutation deleting the scalar exclusion outright would
        produce, and the state every spelling was in before the fix.  These
        are the measured counts with the scalar correctly excluded: zero for
        the non-allocating return shape, and for the three allocating shapes
        the roots their `let @String` intermediate genuinely needs.  A
        scalar wrongly joining them adds exactly one, which is what the
        equality test then reports as an inequality.

        Re-baselined by #1371 (5 / 5 / 4, from 4 / 4 / 3), which is a fall in
        cost and not a rise: root scoping adds one push — the re-root that
        carries a scope's value out — against TWO restores, so per function
        the live roots at the deepest point go 3 → 2, 3 → 2 and 2 → 1.  A
        raw push count no longer measures what a frame HOLDS, only what it
        pushes at some point; the equality above is what this class actually
        turns on, and it is unchanged.
        """
        assert _pushes_for(template, _BASE, fn) == expected

    @pytest.mark.parametrize(
        ("source", "fn"),
        [
            pytest.param(_CONTROL_CLOSURE_RETURN, "anon_0",
                         id="closure_return"),
            pytest.param(_CONTROL_CLOSURE_PARAM, "anon_0", id="closure_param"),
            pytest.param(_CONTROL_CLOSURE_CAPTURE, "anon_0",
                         id="closure_capture"),
            pytest.param(_CONTROL_NAMED_FN, "roundtrip", id="named_fn"),
        ],
    )
    def test_a_real_pointer_at_the_same_boundary_is_still_rooted(
        self, source: str, fn: str,
    ) -> None:
        """The control: the classification still says yes when it should."""
        wat = _compile_ok(source).wat
        assert _shadow_pushes(wat, fn) > 0, _fn_body(wat, fn)

    @pytest.mark.parametrize(("template", "_fn"), _BOUNDARIES)
    @pytest.mark.parametrize(
        "spelling",
        [pytest.param(_BASE, id="base"),
         pytest.param(_REFINEMENT, id="refinement"),
         pytest.param(_ALIAS, id="alias")],
    )
    def test_each_shape_still_computes_its_value_under_eager_gc(
        self, template: str, _fn: str, spelling: tuple[str, str],
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """`VERA_EAGER_GC=1`: a collection at EVERY allocation.

        Removing a push that was load-bearing shows up here and nowhere
        else — with a collection forced at each `$alloc`, a value whose only
        root was the removed slot is reclaimed while still in use, and the
        program reads back something other than 37.  Read at compile time
        (the knob bakes a `call $gc_collect` into `$alloc`), so it must be
        set before the compile.

        37 is the value at every boundary, and cannot coincide with a
        collected-then-reused slot (zero) or with the string length (2) the
        allocating bodies compute alongside it.
        """
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        name, prelude = spelling
        source = template.format(
            T=name, PRELUDE=prelude, MK=_MK.format(T=name))
        assert _run(source) == 37

    @pytest.mark.parametrize(
        "source",
        [
            pytest.param(_CONTROL_CLOSURE_RETURN, id="closure_return"),
            pytest.param(_CONTROL_CLOSURE_PARAM, id="closure_param"),
            pytest.param(_CONTROL_CLOSURE_CAPTURE, id="closure_capture"),
            pytest.param(_CONTROL_NAMED_FN, id="named_fn"),
        ],
    )
    def test_the_pointer_controls_survive_eager_gc_too(
        self, source: str, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The rooting that REMAINS is still load-bearing under eager GC."""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(source) > 0


# A module with no string literal at all, so the data section is empty and
# `data_end` contributes nothing to the heap's start address.  #1255 named
# this the exposure: the classification's inertness was said to rest on the
# string pool holding `gc_heap_start` above the scalar range.
_NO_STRING_POOL = """
private data Box {
  MkB(Int)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match MkB(37) {
    MkB(@Int) -> @Int.0
  }
}
"""


class TestTheHeapStartsAboveTheInlineScalarRange:
    """#1255's second half: the layout invariant, made executable.

    The mark phase rejects a shadow-stack entry below `$gc_heap_start + 4`
    before reading its header, which is why a wrongly-rooted `@Byte` was
    inert rather than a collection bug.  The fix above means nothing should
    rely on that any more — but the reliance was UNCHECKED, and an unchecked
    invariant is what turns a future layout change into a silent
    use-after-free.  The margin is structural (16 KiB shadow stack + 64 KiB
    worklist, both compile-time constants, before the data section
    contributes anything), so the empty-pool module is the worst case and
    still clears the range by five orders of magnitude.
    """

    def test_a_module_with_no_string_pool_still_clears_the_scalar_range(
        self,
    ) -> None:
        result = _compile_ok(_NO_STRING_POOL)
        assert '(data ' not in result.wat, "fixture grew a string constant"
        starts = re.findall(
            r"\(global \$gc_heap_start i32 \(i32\.const (\d+)\)\)", result.wat)
        assert len(starts) == 1, starts
        assert int(starts[0]) > MAX_INLINE_I32_VALUE + 4, starts

    def test_the_guard_refuses_a_layout_that_would_break_it(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The guard fires when the property does not hold.

        Unreachable by construction, so it is exercised by shrinking the two
        constants that create the margin — the exact edit a future layout
        rework would make.  Without this the guard is untested code claiming
        to defend an invariant, which is the state the invariant was already
        in when #1255 was filed.
        """
        monkeypatch.setattr(assembly, "GC_STACK_SIZE", 16)
        monkeypatch.setattr(assembly, "GC_WORKLIST_SIZE", 16)
        with pytest.raises(CodegenInvariantError, match="inline i32 scalar"):
            _compile_ok(_NO_STRING_POOL)


# =====================================================================
# #1256 — the apply_fn signature is the closure's, not the argument's
# =====================================================================

# The issue's repro, verbatim in shape: a `@Byte` formal fed an int
# literal.  The literal's inferred width is i64 and the formal's is i32, so
# the call site registered `(param i32) (param i64) (result i64)` against
# the closure's own `(param i32) (param i32) (result i64)`.
_APPLY_BYTE_LITERAL = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Byte -> @Int) effects(pure) { byte_to_int(@Byte.0) }, 200)
}
"""

# The JOIN spelling: the argument is an `if` whose arms are literals.  The
# issue records this failing identically, and it is the spelling that needs
# the #1212 branch descent rather than a bare-`IntLit` test.
_APPLY_BYTE_JOIN = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Byte -> @Int) effects(pure) { byte_to_int(@Byte.0) },
    if @Bool.0 then { 200 } else { 3 })
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

# The declared formal reached through a refinement, so the signature
# derivation has to resolve the same chain #1255's does.
_APPLY_REFINED_BYTE_LITERAL = _REFINEMENT[1] + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@SmallByte -> @Int) effects(pure) {
    byte_to_int(@SmallByte.0)
  }, 37)
}
"""

# The alias-of-a-function-type spelling: the closure arrives as a `SlotRef`
# whose type resolves through `resolve_fn_type_alias`, which is the OTHER
# arm of the formal-type recovery.
_APPLY_VIA_FN_ALIAS = """
type ByteFn = fn(Byte -> Int) effects(pure);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @ByteFn = fn(@Byte -> @Int) effects(pure) { byte_to_int(@Byte.0) };
  apply_fn(@ByteFn.0, 200)
}
"""

# The named-function CONTROL: the same literal into the same declared
# `@Byte` formal, called directly.  This path has coerced since #865, so it
# is what says the defect was the apply_fn boundary specifically.
_NAMED_BYTE_LITERAL = """
private fn byte_id(@Byte -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(@Byte.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_id(200)
}
"""

# The i64 control: an `@Int` formal must keep its i64 parameter.  A fix that
# read the formal but mapped every width to i32 would pass every test above
# and silently truncate here, so the oracle is a value above 2^32.
_APPLY_INT_LITERAL = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 }, 5000000000)
}
"""


class TestTheApplyFnSignatureComesFromTheClosureType:
    """#1256: one signature, derived from the type both sides declare."""

    @pytest.mark.parametrize(
        ("source", "expected"),
        [
            pytest.param(_APPLY_BYTE_LITERAL, 200, id="literal"),
            pytest.param(_APPLY_BYTE_JOIN, 200, id="join"),
            pytest.param(_APPLY_REFINED_BYTE_LITERAL, 37, id="refined"),
            pytest.param(_APPLY_VIA_FN_ALIAS, 200, id="fn_type_alias"),
            pytest.param(_NAMED_BYTE_LITERAL, 200, id="control_named_fn"),
            pytest.param(_APPLY_INT_LITERAL, 5000000000, id="control_i64"),
        ],
    )
    def test_a_literal_into_a_byte_formal_runs(
        self, source: str, expected: int,
    ) -> None:
        """Pre-fix: `wasm trap: indirect call type mismatch`."""
        assert _run(source) == expected

    def test_one_signature_is_registered_for_the_call(self) -> None:
        """The mechanism, not just the symptom.

        The trap's cause is legible in the WAT: two `$closure_sig` type
        declarations for a module holding one closure and one call.  A
        value-only oracle would also pass if the two sides had converged on
        the WRONG shared width, so the shape is pinned here.
        """
        wat = _compile_ok(_APPLY_BYTE_LITERAL).wat
        sigs = re.findall(r"\(type \$closure_sig_\d+ \(func ([^\n]*)\)\)", wat)
        assert sigs == ["(param i32) (param i32) (result i64)"], sigs


# =====================================================================
# #1269 — throw's payload is a @Byte write boundary
# =====================================================================

def _thrower(payload: str, value: str, prelude: str, handler: str) -> str:
    """A `throw` into `Exn<payload>` and the handler that catches it."""
    return f"""
{prelude}
private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<{payload}>>)
{{
  throw({value})
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[Exn<{payload}>] {{
    throw(@{payload}) -> {{ {handler} }}
  }} in {{
    boom(())
  }}
}}
"""


_THROW_REFINED_BYTE = _thrower(
    "Small", "5", "type Small = { @Byte | @Byte.0 < 10 };\n",
    "byte_to_int(@Small.0)")

# The bare `@Byte` payload: same boundary, no refinement in the way, so a
# fix that only handled the refined spelling is caught here.
_THROW_BARE_BYTE = _thrower("Byte", "200", "", "byte_to_int(@Byte.0)")

# The alias spelling.
_THROW_ALIASED_BYTE = _thrower(
    "Octet", "200", _ALIAS[1], "byte_to_int(@Octet.0)")

# The JOIN spelling — the payload is an `if` over two literals, which needs
# the branch descent rather than a bare-`IntLit` test.
_THROW_BYTE_JOIN = """
type Small = { @Byte | @Byte.0 < 10 };

private fn boom(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Small>>)
{
  throw(if @Bool.0 then { 5 } else { 3 })
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Small>] {
    throw(@Small) -> { byte_to_int(@Small.0) }
  } in {
    boom(true)
  }
}
"""

# A `throw` written INSIDE the handled body, where the `throw` op is
# injected by the handle site rather than by the enclosing declaration's
# effect row.  The two registrations are separate code paths and only one
# of them carried the payload's cell before the fix.
_THROW_INSIDE_HANDLED_BODY = """
type Small = { @Byte | @Byte.0 < 10 };

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Small>] {
    throw(@Small) -> { byte_to_int(@Small.0) }
  } in {
    throw(5)
  }
}
"""

# The QUALIFIED spelling.  `Exn.throw(v)` reaches a different dispatcher
# from the bare `throw(v)`, and the qualified one had no marking of its own —
# the same split `State.put` was found on.
_THROW_QUALIFIED = """
type Small = { @Byte | @Byte.0 < 10 };

private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Small>>)
{
  Exn.throw(5)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Small>] {
    throw(@Small) -> { byte_to_int(@Small.0) }
  } in {
    boom(())
  }
}
"""

# The i64 control: an `@Int` payload must stay i64, asserted above 2^32.
_THROW_INT = _thrower("Int", "5000000000", "", "@Int.0")


class TestTheThrowPayloadIsAByteWriteBoundary:
    """#1269: the thrown literal lowers at the tag's declared width."""

    @pytest.mark.parametrize(
        ("source", "expected"),
        [
            pytest.param(_THROW_REFINED_BYTE, 5, id="refinement"),
            pytest.param(_THROW_BARE_BYTE, 200, id="bare_byte"),
            pytest.param(_THROW_ALIASED_BYTE, 200, id="alias"),
            pytest.param(_THROW_BYTE_JOIN, 5, id="join"),
            pytest.param(_THROW_INSIDE_HANDLED_BODY, 5, id="inside_body"),
            pytest.param(_THROW_QUALIFIED, 5, id="qualified"),
            pytest.param(_THROW_INT, 5000000000, id="control_i64"),
        ],
    )
    def test_a_byte_payload_throw_runs(
        self, source: str, expected: int,
    ) -> None:
        """Pre-fix: `type mismatch: expected i32, found i64` at validation."""
        assert _run(source) == expected

    def test_the_tag_and_the_thrown_value_agree_on_i32(self) -> None:
        """The mechanism: the tag was i32 all along; the value now is too.

        Pinning both halves is what makes this a WIDTH-agreement test rather
        than "it runs" — a fix that widened the TAG to i64 would also run,
        and would put a Byte cell at eight bytes everywhere else.

        The value half no longer reads as adjacency.  #1268 made the payload
        a guarded write boundary as well as a sized one, so a REFINED payload
        routes through a guard local between the literal and the `throw`;
        asserting `i32.const 5\\n    throw` would then be a test of where the
        guard is, not of how wide the value is.  What the width claim needs
        is that the value the `throw` consumes is i32 by whichever route it
        arrives — so the pushed operand is resolved: a literal directly, or
        the guard local, whose DECLARED width is the thing checked.
        """
        wat = _compile_ok(_THROW_REFINED_BYTE).wat
        tags = re.findall(r"\(tag \$exn_\S+ \(param ([^)]*)\)\)", wat)
        assert tags == ["i32"], tags
        body = _fn_body(wat, "boom")
        # Token-anchored: a bare substring also matches `i32.const 50`
        # and `i64.const 512`, so any later constant beginning with 5
        # would flip either assertion with no width regression
        # (#1330 review).
        assert re.search(r"\bi32\.const 5\b", body), body
        assert not re.search(r"\bi64\.const 5\b", body), body
        lines = [ln.strip() for ln in body.strip().splitlines()]
        throw_at = next(i for i, ln in enumerate(lines)
                        if ln.startswith("throw $exn_"))
        pushed = lines[throw_at - 1]
        if pushed.startswith("local.get "):
            idx = pushed.split()[1]
            assert f"(local $l{idx} i32)" in body, body
        else:
            assert pushed == "i32.const 5", body


# =====================================================================
# Cross-module registration parity (#1269)
# =====================================================================

# `Small` is declared and used in `xmodlib`, whose alias environment is the
# only one that can resolve it.  The IMPORTER declares its own `Small` over a
# DIFFERENT base — the decoy that makes this a parity test rather than a
# smoke test: a type alias is module-local (spec 8.4.1), so if either side of
# the payload derivation read the importer's environment it would answer
# `Int` (i64) where the other answered `Byte` (i32), and the two would
# disagree exactly the way #1269's two widths did.
_XMOD_LIB = """\
module xmodlib;

type Small = { @Byte | @Byte.0 < 10 };

private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Small>>)
{
  throw(5)
}

public fn catch_it(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Small>] {
    throw(@Small) -> { byte_to_int(@Small.0) }
  } in {
    boom(())
  }
}
"""

_XMOD_MAIN = """\
import xmodlib;

type Small = Int;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Small = catch_it(());
  @Small.0
}
"""

# The single-module twin, the same declarations with no module boundary
# between them.  It is the ORACLE: the claim is that crossing a module
# boundary changes nothing about the emitted throw, and only a comparison
# can say that.
_XMOD_SAME_MODULE = """\
type Small = { @Byte | @Byte.0 < 10 };

private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Small>>)
{
  throw(5)
}

public fn catch_it(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Small>] {
    throw(@Small) -> { byte_to_int(@Small.0) }
  } in {
    boom(())
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  catch_it(())
}
"""


def _compile_xmod(tmp_path: Path) -> CompileResult:
    """Resolve and compile the two-module program through the real resolver."""
    (tmp_path / "xmodlib.vera").write_text(_XMOD_LIB, encoding="utf-8")
    main_file = tmp_path / "main.vera"
    main_file.write_text(_XMOD_MAIN, encoding="utf-8")
    tree = parse_file(str(main_file))
    prog = transform(tree)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(prog, main_file)
    assert not resolver.errors, [e.description for e in resolver.errors]
    result = _vera_compile(
        prog,
        source=main_file.read_text(encoding="utf-8"),
        file=str(main_file),
        resolved_modules=resolved,
    )
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, [d.description for d in errors]
    return result


class TestTheThrowPayloadResolvesInItsOwnModule:
    """#1269's not-probed axis: the two producers read different alias envs.

    The payload's representation is derived on the CodeGenerator side
    (`_family_base_te`, over the generator's `_alias_env`, scoped to the
    declaring module) and again on the WasmContext side (`_family_base`, over
    the context's own copy).  Nothing forces those two objects to hold the
    same aliases within one compilation of many modules, so "they agree" is a
    claim about the scoping — and a single-module program cannot test it,
    there being only one environment for both to read.
    """

    def test_the_emitted_throw_is_identical_across_the_module_boundary(
        self, tmp_path: Path,
    ) -> None:
        """Same declarations, one module or two: the same throw sequence.

        A structural equality, not a spot check — if either producer read the
        importer's `type Small = Int` the tag would take an i64 parameter or
        the value would be an `i64.const`, and the two bodies would differ.
        """
        xmod = _fn_body(_compile_xmod(tmp_path).wat, "boom")
        same = _fn_body(_compile_ok(_XMOD_SAME_MODULE).wat, "boom")
        assert xmod == same, (xmod, same)
        assert "i32.const 5" in xmod, xmod

    def test_the_tag_is_i32_and_the_program_returns_the_payload(
        self, tmp_path: Path,
    ) -> None:
        """The value oracle, so the agreement is on the RIGHT width.

        5 is the payload.  It cannot coincide with the importer's decoy
        `type Small = Int` being read instead: that spelling is i64, which
        either fails validation against the i32 tag or delivers a different
        number.
        """
        result = _compile_xmod(tmp_path)
        tags = re.findall(
            r"\(tag \$exn_\S+ \(param ([^)]*)\)\)", result.wat)
        assert tags == ["i32"], tags
        exec_result = execute(result, fn_name="main")
        assert exec_result.value == 5, exec_result.value

    def test_the_width_assertion_can_go_red(self, tmp_path: Path) -> None:
        """The companion that makes the two above mean something.

        Both assert i32.  If the payload width were i32 for every spelling
        the tests would pass without discriminating anything, so the same
        two-module program is compiled with the LIBRARY's `Small` changed to
        `Int` — the value the importer's decoy would supply if a producer
        read the wrong environment.  That must emit an i64 tag and an
        `i64.const`; the assertions above are therefore reading a width that
        genuinely tracks the declaring module's alias.
        """
        (tmp_path / "xmodlib.vera").write_text(
            _XMOD_LIB.replace(
                "type Small = { @Byte | @Byte.0 < 10 };", "type Small = Int;")
            .replace("byte_to_int(@Small.0)", "@Small.0"),
            encoding="utf-8")
        main_file = tmp_path / "main.vera"
        main_file.write_text(_XMOD_MAIN, encoding="utf-8")
        tree = parse_file(str(main_file))
        prog = transform(tree)
        resolver = ModuleResolver(_root=tmp_path)
        resolved = resolver.resolve_imports(prog, main_file)
        assert not resolver.errors, [e.description for e in resolver.errors]
        result = _vera_compile(
            prog, source=main_file.read_text(encoding="utf-8"),
            file=str(main_file), resolved_modules=resolved)
        tags = re.findall(
            r"\(tag \$exn_\S+ \(param ([^)]*)\)\)", result.wat)
        assert tags == ["i64"], tags
        assert "i64.const 5" in _fn_body(result.wat, "boom")
