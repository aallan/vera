"""Tests for #1060 — wildcard over a type-parameter field instantiated to Unit.

A generic constructor's type-parameter field (``Box<T>`` field ``T``) registers
in the layout as the generic 4-byte i32 placeholder.  Construction, however,
lays each instantiation out concretely: ``Box<Unit>`` *erases* the field to zero
bytes, ``Box<String>`` widens it to an i32_pair, ``Box<Int>`` to an i64.  A
WILDCARD sub-pattern over such a field used to advance the offset walk by the
generic i32 width regardless — so on a ``Box<Unit>`` every field *after* the
erased one was read four bytes too high, silently, on a check-green program with
no diagnostics:

* ``match b { MkB(@Int, _, @Int) -> @Int.0 }`` on ``Box<Unit>`` returned 0, not
  the real trailing Int;
* ``N(_, @String)`` on ``Named<Unit>`` read the String header at the wrong
  offset (garbage);
* ``En(_, MkBox(@Int))`` on ``Entry<Unit>`` read the nested constructor tag at a
  shifted address and matched the wrong arm.

Only the WILDCARD walks were wrong — ``@Unit`` bindings, let-destructures, and
structural ``Eq`` / ``show`` / ``hash`` already recompute each field from the
concrete instantiation and were correct *for the literal ``Unit`` spelling*
(pinned below as regression controls).  A NON-literal erases-to-Unit type
argument (``Box<U>`` with ``type U = Unit;``, ``Box<Future<Unit>>``, chains)
hit the same class of hole in the width recomputation AND in ``Eq``'s dispatch
— that is #1070, pinned in ``test_codegen_erased_alias_typeargs_1070.py``.

The fix makes the two wildcard walks (``_extract_constructor_fields`` and
``_sub_pattern_wasm_type``) instantiation-aware: a bare type-parameter field's
width is recomputed from the scrutinee's concrete type args, mirroring the
eq/show recomputation.  A concrete field keeps its (#1043-erasure-aware)
registered width.

#1065 then closes the DIRECT-CALL gap for a non-generic callee: a
``match mk() { … }`` scrutinee's concrete type is recovered from the callee's
declared return type (``mk() -> @Box<Unit>``), so those shapes now compile and
read the real value exactly like a slot scrutinee.  Before #1065 the FnCall
Vera-type inference dropped the ``<Unit>`` arg, so a wildcard followed by a read
LOUD-skipped (E602) — the sound interim behavior — while a trailing wildcard
(whose unknown width is never consumed) stayed compilable.

#1072 closes the GENERIC-call sibling: a ``match wrap(5) { … }`` scrutinee where
``forall<T> fn wrap(@T -> @P2<T, Unit>)`` resolves the declared return's type
variables from the call site (the same unification the generic call-rewrite
performs) and renders the full instantiation (``P2<Int, Unit>``).  On main this
family was a SILENT wrong value (the #1060 walk was not instantiation-aware at
all); the #1049 stack made it a sound LOUD-skip; now it compiles and reads the
real value.  An unresolved type variable still falls back to the LOUD-skip
(sound) — though no check-green shape reaches it: instantiating the var itself
at Unit is E206-rejected and a phantom-var callee is E121-rejected.

#1073 closes the MODULE-call door: ``match boxlib::mk() { … }`` resolves the
qualified target through the single shared resolver and recurses into the same
declared-return recovery, covering the imported non-generic AND imported
generic (#1072 x #1073 compound) scrutinees — also a SILENT wrong value on
main, a sound LOUD-skip on the #1049 stack, compiled correctly now.
"""
from __future__ import annotations

from tests.codegen_helpers import (
    _compile,
    _run,
)
from tests.module_fixture_helpers import resolved_module
from tests import pipeline


def _warnings(source: str) -> list[str]:
    """Warning codes emitted compiling *source* (severity == 'warning')."""
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "warning"]


def _errors(source: str) -> list[str]:
    """Error codes emitted compiling *source* (severity == 'error')."""
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "error"]


# =====================================================================
# The core silent-wrong shapes: a WILDCARD over a type-parameter field
# instantiated to Unit, followed by a field that IS read.  Each returns the
# real value only when the erased field advances the offset by 0 bytes.
# The scrutinee is a slot (`@Box<Unit>.0`) whose type args are recoverable.
# =====================================================================

_BOX_UNIT = """\
data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Unit> = mk();
  match @Box<Unit>.0 {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_box_unit_wildcard_reads_trailing_int() -> None:
    """MkB(@Int, _, @Int) on Box<Unit>: @Int.0 is the real trailing 22, not 0."""
    assert _run(_BOX_UNIT, fn="f") == 22


_BOX_UNIT_FIRST = """\
data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Unit> = mk();
  match @Box<Unit>.0 {
    MkB(@Int, _, @Int) -> @Int.1
  }
}
"""


def test_box_unit_field_before_erased_is_unaffected() -> None:
    """@Int.1 (field 0, BEFORE the erased field) was always correct — 11."""
    assert _run(_BOX_UNIT_FIRST, fn="f") == 11


_NAMED_UNIT = """\
data Named<T> { N(T, String) }

private fn mk(-> @Named<Unit>)
  requires(true) ensures(true) effects(pure)
{ N((), "payload") }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Named<Unit> = mk();
  match @Named<Unit>.0 {
    N(_, @String) -> eq(@String.0, "payload")
  }
}
"""


def test_named_unit_wildcard_reads_string_at_right_offset() -> None:
    """N(_, @String) on Named<Unit>: the String header is read @4, not @8."""
    assert _run(_NAMED_UNIT, fn="f") == 1


_ENTRY_UNIT = """\
data BB { MkBox(Int), MkNot(Int) }
data Entry<T> { En(T, BB) }

private fn mk(-> @Entry<Unit>)
  requires(true) ensures(true) effects(pure)
{ En((), MkBox(314)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Entry<Unit> = mk();
  match @Entry<Unit>.0 {
    En(_, MkBox(@Int)) -> @Int.0,
    En(_, MkNot(@Int)) -> 0 - @Int.0
  }
}
"""


def test_entry_unit_wildcard_before_nested_ctor() -> None:
    """En(_, MkBox(@Int)) on Entry<Unit>: the nested tag is read @4, hits the
    MkBox arm, and extracts the real 314 (both the condition tag-walk and the
    field-extraction walk must give the erased field zero width)."""
    assert _run(_ENTRY_UNIT, fn="f") == 314


_BOOL_FOLLOWING = """\
data Bx<T> { MkBx(T, Bool) }

private fn mk(-> @Bx<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkBx((), true) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Bx<Unit> = mk();
  match @Bx<Unit>.0 {
    MkBx(_, @Bool) -> @Bool.0
  }
}
"""


def test_bool_following_erased_typeparam() -> None:
    """A Bool (align 4) after the erased field is a RED shape — the spurious +4
    is not masked by re-alignment.  MkBx(_, @Bool) reads the real true."""
    assert _run(_BOOL_FOLLOWING, fn="f") == 1


_SECOND_TYPEPARAM = """\
data P2<A, B> { MkP2(Int, B, Int) }

private fn mk(-> @P2<Int, Unit>)
  requires(true) ensures(true) effects(pure)
{ MkP2(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @P2<Int, Unit> = mk();
  match @P2<Int, Unit>.0 {
    MkP2(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_second_type_parameter_instantiated_to_unit() -> None:
    """The erased field is the SECOND type parameter (P2<Int, Unit> field B):
    the positional tp-index lookup must resolve B, not A."""
    assert _run(_SECOND_TYPEPARAM, fn="f") == 22


_NESTED_GENERIC = """\
data Inner<T> { MkI(Int, T, Int) }
data Outer<T> { MkO(Inner<T>) }

private fn mk(-> @Outer<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkO(MkI(11, (), 22)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Outer<Unit> = mk();
  match @Outer<Unit>.0 {
    MkO(MkI(@Int, _, @Int)) -> @Int.0
  }
}
"""


def test_nested_generic_wildcard_resolves_inner_instantiation() -> None:
    """A wildcard over Inner's type parameter one level DOWN: recursing into
    MkO's Inner<T> field must substitute the outer <Unit> so Inner<Unit>'s
    erased field advances by 0 bytes and the trailing Int is read as 22."""
    assert _run(_NESTED_GENERIC, fn="f") == 22


# =====================================================================
# Builtin Option / Result — a wildcard over the payload type parameter
# instantiated to Unit.  The payload is the last field, so nothing is read
# after it (harmless), but the arm must still match and return correctly.
# =====================================================================

_OPTION_UNIT = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Unit> = Some(());
  match @Option<Unit>.0 {
    Some(_) -> 5,
    None -> 9
  }
}
"""


def test_option_unit_some_wildcard() -> None:
    assert _run(_OPTION_UNIT, fn="f") == 5


_RESULT_UNIT = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Unit, Int> = Ok(());
  match @Result<Unit, Int>.0 {
    Ok(_) -> 5,
    Err(@Int) -> @Int.0
  }
}
"""


def test_result_unit_ok_wildcard() -> None:
    assert _run(_RESULT_UNIT, fn="f") == 5


# =====================================================================
# Controls — a type-parameter wildcard whose instantiation is NOT Unit.  The
# fix must recompute these widths correctly too (String → i32_pair, Int → i64).
# Box<Int> / Box<Bool> were green even before the fix (alignment coincidence);
# they pin that the recomputation keeps them green.
# =====================================================================

_BOX_STRING = """\
data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<String>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, "x", 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<String> = mk();
  match @Box<String>.0 {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_box_string_wildcard_recomputes_i32_pair_width() -> None:
    """Box<String>: the erased-field slot is an i32_pair (8 bytes); the trailing
    Int is still read correctly."""
    assert _run(_BOX_STRING, fn="f") == 22


_BOX_INT = """\
data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, 55, 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Int> = mk();
  match @Box<Int>.0 {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_box_int_wildcard_control() -> None:
    """Box<Int>: i64 payload; green before and after (alignment coincidence)."""
    assert _run(_BOX_INT, fn="f") == 22


_TAGGED_UNIT = """\
data Tagged<T> { Tag(T, Int) }

private fn mk(-> @Tagged<Unit>)
  requires(true) ensures(true) effects(pure)
{ Tag((), 99) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Tagged<Unit> = mk();
  match @Tagged<Unit>.0 {
    Tag(_, @Int) -> @Int.0
  }
}
"""


def test_tagged_unit_alignment_masked_control() -> None:
    """Tag(T, Int) as Tagged<Unit>: the spurious +4 is re-aligned away by the
    following i64, so this shape was CORRECT even before the fix.  Pin it green
    so the fix does not perturb the alignment-masked case."""
    assert _run(_TAGGED_UNIT, fn="f") == 99


# =====================================================================
# Trailing type-parameter wildcard — the erased field is LAST, so its width is
# never consumed.  Green whether or not the instantiation is recoverable.
# =====================================================================

_TRAILING_SLOT = """\
data W<T> { MkW(Int, T) }

private fn mk(-> @W<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkW(5, ()) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @W<Unit> = mk();
  match @W<Unit>.0 {
    MkW(@Int, _) -> @Int.0
  }
}
"""


def test_trailing_typeparam_wildcard_slot() -> None:
    assert _run(_TRAILING_SLOT, fn="f") == 5


# =====================================================================
# Direct-call scrutinee (#1065) — the concrete instantiation is recovered from
# the callee's DECLARED return type, so a type-parameter wildcard's width is
# instantiation-aware exactly as for a slot scrutinee.  Before #1065 the FnCall
# Vera-type inference dropped the type args (returning the bare base head) and a
# wildcard followed by a read LOUD-skipped (E602) — the sound #1060 interim
# behavior; now the width is recovered and the function reads the real value.
# =====================================================================

_DIRECT_CALL_READ = """\
data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match mk() {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_direct_call_wildcard_reads_trailing_int() -> None:
    """`match mk() { MkB(@Int, _, @Int) }` on a direct-call `mk() -> @Box<Unit>`
    scrutinee: #1065 recovers `Box<Unit>` from mk's declared return type, so the
    erased field advances by 0 bytes and the trailing Int reads the real 22 — no
    LOUD-skip, and not the 0 a shifted read would return."""
    assert "E602" not in _warnings(_DIRECT_CALL_READ)
    assert _errors(_DIRECT_CALL_READ) == []
    assert _run(_DIRECT_CALL_READ, fn="f") == 22


_DIRECT_CALL_NESTED = """\
data BB { MkBox(Int), MkNot(Int) }
data Entry<T> { En(T, BB) }

private fn mk(-> @Entry<Unit>)
  requires(true) ensures(true) effects(pure)
{ En((), MkBox(314)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match mk() {
    En(_, MkBox(@Int)) -> @Int.0,
    En(_, MkNot(@Int)) -> 0 - @Int.0
  }
}
"""


def test_direct_call_wildcard_before_nested_ctor() -> None:
    """Direct-call `mk() -> @Entry<Unit>` scrutinee, wildcard over the erased T
    before a nested constructor: #1065 recovers `Entry<Unit>` so BOTH the
    condition tag-walk and the extraction walk give the erased field zero width —
    the nested tag is read @4, hits the MkBox arm, and extracts the real 314."""
    assert "E602" not in _warnings(_DIRECT_CALL_NESTED)
    assert _run(_DIRECT_CALL_NESTED, fn="f") == 314


_DIRECT_CALL_NAMED_STRING = """\
data Named<T> { N(T, String) }

private fn mk(-> @Named<Unit>)
  requires(true) ensures(true) effects(pure)
{ N((), "payload") }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match mk() {
    N(_, @String) -> eq(@String.0, "payload")
  }
}
"""


def test_direct_call_wildcard_reads_string_at_right_offset() -> None:
    """Direct-call `mk() -> @Named<Unit>` scrutinee: #1065 recovers `Named<Unit>`
    so the wildcard over the erased T gives zero width and the String header is
    read @4 (not @8 garbage) — `eq(@String.0, "payload")` is true."""
    assert "E602" not in _warnings(_DIRECT_CALL_NAMED_STRING)
    assert _run(_DIRECT_CALL_NAMED_STRING, fn="f") == 1


_DIRECT_CALL_TRAILING = """\
data W<T> { MkW(Int, T) }

private fn mk(-> @W<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkW(5, ()) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match mk() {
    MkW(@Int, _) -> @Int.0
  }
}
"""


def test_direct_call_trailing_wildcard_compiles() -> None:
    """Direct-call scrutinee with a TRAILING type-parameter wildcard — its width
    is never consumed, so this compiled even while the instantiation was
    unrecoverable (pre-#1065), and keeps compiling now that it is recovered.
    Reads field 0 (5)."""
    assert "E602" not in _warnings(_DIRECT_CALL_TRAILING)
    assert _run(_DIRECT_CALL_TRAILING, fn="f") == 5


# =====================================================================
# Generic-call scrutinee (#1072) — the callee's declared return carries type
# VARIABLES (`forall<T> fn wrap(@T -> @P2<T, Unit>)`), resolved from the call
# site by the same unification the generic call-rewrite performs, then rendered
# in full (`P2<Int, Unit>`).  On main this family read shifted offsets SILENTLY
# (the #1060 class); the #1049 stack turned it into a sound E602 LOUD-skip;
# now it compiles and reads the real value.  Instantiating the var itself at
# Unit is E206-rejected, so the generic Unit-erasure arrives via a concrete
# Unit type argument in the declared return.
# =====================================================================

_GENERIC_CALL_READ = """\
data P2<A, B> { MkP2(Int, B, Int) }

forall<T> fn wrap(@T -> @P2<T, Unit>)
  requires(true) ensures(true) effects(pure)
{ MkP2(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match wrap(5) {
    MkP2(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_generic_call_wildcard_reads_trailing_int() -> None:
    """`match wrap(5)` where `forall<T> fn wrap(@T -> @P2<T, Unit>)`: #1072
    unifies T=Int from the call site and renders `P2<Int, Unit>`, so the erased
    B=Unit field advances 0 bytes and the trailing Int reads the real 22 — on
    main this returned 0 silently; on the #1049 stack it LOUD-skipped."""
    assert "E602" not in _warnings(_GENERIC_CALL_READ)
    assert _errors(_GENERIC_CALL_READ) == []
    assert _run(_GENERIC_CALL_READ, fn="f") == 22


_GENERIC_CALL_STRING_WIDTH = """\
data Box<T> { MkB(Int, T, Int) }

forall<T> fn wrap(@T -> @Box<T>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, @T.0, 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match wrap("x") {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_generic_call_string_typeparam_width() -> None:
    """The wildcarded field IS the forall var, instantiated at String via
    `wrap("x")`: the recovered `Box<String>` gives the erased-field slot the
    i32_pair width (8 bytes, not the generic 4), so the trailing Int is 22."""
    assert "E602" not in _warnings(_GENERIC_CALL_STRING_WIDTH)
    assert _run(_GENERIC_CALL_STRING_WIDTH, fn="f") == 22


_GENERIC_CALL_CONCRETE_RET = """\
data Box<T> { MkB(Int, T, Int) }

forall<T> fn wrap(@T -> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match wrap(5) {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_generic_call_concrete_parameterized_return() -> None:
    """A generic fn whose declared return is fully CONCRETE (`-> @Box<Unit>`,
    no variables to resolve): the render needs zero substitutions but the
    pre-#1072 non-generic gate still skipped it — now it reads 22."""
    assert "E602" not in _warnings(_GENERIC_CALL_CONCRETE_RET)
    assert _run(_GENERIC_CALL_CONCRETE_RET, fn="f") == 22


_GENERIC_CALL_NESTED = """\
data BB { MkBox(Int), MkNot(Int) }
data EntryAB<A, B> { En(B, BB) }

forall<T> fn wrap(@T -> @EntryAB<T, Unit>)
  requires(true) ensures(true) effects(pure)
{ En((), MkBox(314)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match wrap(7) {
    En(_, MkBox(@Int)) -> @Int.0,
    En(_, MkNot(@Int)) -> 0 - @Int.0
  }
}
"""


def test_generic_call_wildcard_before_nested_ctor() -> None:
    """Generic-call scrutinee, wildcard over the erased B=Unit before a nested
    constructor: BOTH the condition tag-walk and the extraction walk receive the
    rendered `EntryAB<Int, Unit>` — the nested tag is read @4, hits the MkBox
    arm, and extracts the real 314."""
    assert "E602" not in _warnings(_GENERIC_CALL_NESTED)
    assert _run(_GENERIC_CALL_NESTED, fn="f") == 314


_GENERIC_CALL_NAMED_STRING = """\
data NamedAB<A, B> { N(B, String) }

forall<T> fn wrap(@T -> @NamedAB<T, Unit>)
  requires(true) ensures(true) effects(pure)
{ N((), "payload") }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match wrap(3) {
    N(_, @String) -> eq(@String.0, "payload")
  }
}
"""


def test_generic_call_wildcard_reads_string_at_right_offset() -> None:
    """Generic-call scrutinee: the rendered `NamedAB<Int, Unit>` gives the
    erased B=Unit wildcard zero width, so the String header is read @4 (not @8
    garbage) — `eq(@String.0, "payload")` is true."""
    assert "E602" not in _warnings(_GENERIC_CALL_NAMED_STRING)
    assert _run(_GENERIC_CALL_NAMED_STRING, fn="f") == 1


_GENERIC_CALL_TRAILING = """\
data WAB<A, B> { MkW(Int, B) }

forall<T> fn wrap(@T -> @WAB<T, Unit>)
  requires(true) ensures(true) effects(pure)
{ MkW(5, ()) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match wrap(9) {
    MkW(@Int, _) -> @Int.0
  }
}
"""


def test_generic_call_trailing_wildcard_compiles() -> None:
    """Generic-call scrutinee with a TRAILING type-parameter wildcard — a
    control: its width is never consumed, so this compiled (and read the right
    field 0) even before #1072 recovered the instantiation, and keeps doing so
    after."""
    assert "E602" not in _warnings(_GENERIC_CALL_TRAILING)
    assert _run(_GENERIC_CALL_TRAILING, fn="f") == 5


# =====================================================================
# Module-call scrutinee (#1073) — `match boxlib::mk() { … }` resolves the
# qualified target through the shared resolver and recurses into the same
# declared-return recovery, so the imported callee's `Box<Unit>` reaches the
# wildcard walks.  On main this door read shifted offsets SILENTLY; the #1049
# stack turned it into a sound E602 LOUD-skip; now it compiles.
# =====================================================================

def _compile_with_module(
    main_source: str, module_path: tuple[str, ...], module_source: str,
):
    """Compile *main_source* with one resolved module (Windows-safe temps)."""
    resolved = resolved_module(module_path, module_source)
    return pipeline.compile(
        main_source, file="fixture.vera", modules=[resolved], checked=False,
    ).result


_BOXLIB_MODULE = """\
module boxlib;

public data Box<T> { MkB(Int, T, Int) }

public fn mk(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }
"""

_MODULE_CALL_READ = """\
import boxlib;

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match boxlib::mk() {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_module_call_wildcard_reads_trailing_int() -> None:
    """`match boxlib::mk()` where the imported `mk() -> @Box<Unit>`: #1073
    resolves the qualified target and recovers `Box<Unit>` from its declared
    return, so the erased field advances 0 bytes and the trailing Int reads the
    real 22 — on main this returned 0 silently; on the #1049 stack it
    LOUD-skipped."""
    from vera.codegen import execute as _execute

    result = _compile_with_module(_MODULE_CALL_READ, ("boxlib",), _BOXLIB_MODULE)
    warns = [d.error_code for d in result.diagnostics if d.severity == "warning"]
    errs = [d.error_code for d in result.diagnostics if d.severity == "error"]
    assert "E602" not in warns
    assert errs == []
    exec_result = _execute(result, fn_name="f")
    assert exec_result.value == 22


_GENLIB_MODULE = """\
module genlib;

public data P2<A, B> { MkP2(Int, B, Int) }

public forall<T> fn wrap(@T -> @P2<T, Unit>)
  requires(true) ensures(true) effects(pure)
{ MkP2(11, (), 22) }
"""

_MODULE_GENERIC_CALL_READ = """\
import genlib;

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match genlib::wrap(5) {
    MkP2(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_module_call_generic_wildcard_reads_trailing_int() -> None:
    """The #1072 x #1073 compound: an IMPORTED generic (`genlib::wrap(5)`,
    declared `-> @P2<T, Unit>`) as the scrutinee — the resolver hands the
    recursion a name whose declared return resolves (clone or template), so the
    erased field advances 0 bytes and the trailing Int reads the real 22."""
    from vera.codegen import execute as _execute

    result = _compile_with_module(
        _MODULE_GENERIC_CALL_READ, ("genlib",), _GENLIB_MODULE)
    warns = [d.error_code for d in result.diagnostics if d.severity == "warning"]
    errs = [d.error_code for d in result.diagnostics if d.severity == "error"]
    assert "E602" not in warns
    assert errs == []
    exec_result = _execute(result, fn_name="f")
    assert exec_result.value == 22


# =====================================================================
# Regression controls — structural Eq / show over a type-parameter-Unit
# instantiation were ALREADY correct (they recompute from the concrete type).
# Pin them so the wildcard fix does not perturb the recomputation path.
# =====================================================================

_EQ_EQUAL = """\
data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Unit> = a();
  let @Box<Unit> = a();
  @Box<Unit>.0 == @Box<Unit>.1
}
"""


def test_eq_box_unit_equal_control() -> None:
    assert _run(_EQ_EQUAL, fn="f") == 1


_EQ_DISTINCT = """\
data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

private fn b(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 99) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Unit> = a();
  let @Box<Unit> = b();
  @Box<Unit>.1 == @Box<Unit>.0
}
"""


def test_eq_box_unit_distinct_trailing_int_control() -> None:
    """Distinct trailing Int → unequal: Eq reads the real field, not garbage."""
    assert _run(_EQ_DISTINCT, fn="f") == 0


_SHOW_NAMED = """\
data Named<T> { N(T, String) }

private fn a(-> @Named<Unit>)
  requires(true) ensures(true) effects(pure)
{ N((), "hi") }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Named<Unit> = a();
  eq(show(@Named<Unit>.0), "N(unit, hi)")
}
"""


def test_show_named_unit_control() -> None:
    assert _run(_SHOW_NAMED, fn="f") == 1


class TestRecoveredAliasTypeArgWidths:
    """The #1080 review's regression shapes: a recovered scrutinee
    instantiation whose type ARGUMENT is an alias or ``Future<Unit>``
    spelling.  On the pre-#1070/#1076 base these read silently wrong
    offsets (5-for-22, 0-for-22) because the wildcard-width function
    could not size the raw recovered spelling; the erasure keying
    (#1070) and alias grounding (#1076) now compose with the #1065/
    #1072 recovery so every spelling reads the constructed offset.
    These pins guard that composition."""

    def test_generic_call_int_alias_type_arg(self) -> None:
        """``wrap(mkAge())`` with ``type Age = Int``: the recovered
        instantiation ``W<Age>`` must size the field via the grounded
        ``Int`` (i64-slot), not the 4-byte raw-alias default — the
        review's R1 read 5 (the field) instead of 22 (the trailing
        Int) on the unfixed base."""
        src = """
type Age = Int;

private data W<X> { MkW(X, Int) }

private fn mkAge(-> @Age)
  requires(true) ensures(true) effects(pure)
{ 5 }

private forall<T> fn wrap(@T -> @W<T>)
  requires(true) ensures(true) effects(pure)
{ MkW(@T.0, 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match wrap(mkAge()) { MkW(_, @Int) -> @Int.0 }
}
"""
        assert _run(src, fn="f") == 22

    def test_direct_call_unit_alias_type_arg(self) -> None:
        """``mk() -> @Box<U>`` with ``type U = Unit``: the recovered
        ``Box<U>`` must erase the wildcarded field (0 bytes) so the
        trailing ``Int`` reads 22 — the review's R2 read 0 on the
        unfixed base."""
        src = """
type U = Unit;

private data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<U>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match mk() {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""
        assert _run(src, fn="f") == 22

    def test_direct_call_future_unit_type_arg(self) -> None:
        """``mk() -> @Box<Future<Unit>>``: the transparent erasure
        spelling recovered from a direct call must also erase — the
        review's R3 read 0 on the unfixed base."""
        src = """
private data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<Future<Unit>>)
  requires(true) ensures(true) effects(<Async>)
{ MkB(11, async(()), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  match mk() { MkB(@Int, _, @Int) -> @Int.0 }
}
"""
        assert _run(src, fn="f") == 22
