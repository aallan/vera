"""Regression tests for #921 — ``compare`` / ordering on a user ADT is a
*silent wrong result*, the severest failure class.

The bug had two manifestations sharing one root — the type-checker accepted
``compare(a, b)`` on operands of *any* type, including a user ADT, because the
``Ord`` ability op's parameter is a bare type variable that the ability-op
check never constrained to an actually-orderable type:

1. **Codegen — silent wrong result.**  Pass 1.6 rewrites ``compare(a, b)`` to
   the ``Ordering`` if-chain ``a < b ? Less : (a == b ? Equal : Greater)``.
   The ``==`` arm has structural ADT equality, but the ``<`` arm falls through
   to a scalar ``i32.lt_s`` on the *boxed heap pointers* (allocation order), so
   ``compare(Cons(1, Nil), Cons(1, Nil))`` — two structurally-equal lists —
   returned ``Less`` instead of ``Equal``.  check-green, verify-green, wrong at
   runtime.

2. **Verifier — uncaught traceback.**  ``smt._translate_binary`` translated the
   ``<`` arm with a bare Python ``left < right``; on Z3 ``DatatypeRef`` operands
   that raises ``TypeError: '<' not supported`` — a hard traceback out of
   ``vera verify``.

Root fix (spec-faithful): §4.5 defines ``<`` / ``>`` / ``<=`` / ``>=`` **only**
on ``Int`` / ``Nat`` / ``Float64`` / ``Byte`` / ``String``, and §9.8.1 lists
``Ord``'s "Satisfied by:" set as exactly those primitives — ADTs are *not*
Ord-derivable in v0.1.0 (unlike ``Eq`` / ``Hash`` / ``Show``, whose "Satisfied
by:" clauses explicitly include composite types).  The checker already rejects a
direct ``MkBox(1) < MkBox(2)`` with E143; ``compare`` is the ability spelling of
that same if-chain (§6.4), so it must reject on the same domain.  The fix rejects
``compare`` on a non-orderable operand at *check* time (E242) — the single gate
both codegen and the verifier trust — plus a defensive guard in ``smt.py`` so a
datatype operand can never reach a raw Python ``<`` even via the direct
``verify()`` API.

Written test-first: each RED test FAILS on the pre-fix compiler (a wrong run
value; a check that returns no error; a verifier ``TypeError``).

#927 (folded in): the SAME ordering-lowering code miscompiled ``String``
operands.  ``String`` IS orderable (spec §4.5, lexicographic), so it must be
*implemented*, not rejected — but codegen lowered ``<`` / ``>`` / ``<=`` /
``>=`` (and ``compare``) on strings to a scalar ``i64.lt_s`` on the (ptr, len)
pair, both wrong-order AND an i32/i64 type mismatch that crashed WASM
translation (``vera check`` / ``vera verify`` were green — the verifier already
models String ordering via Z3 ``StringSort``).  Fixed by lowering String
ordering to a byte-wise three-way ``$rt.cmp_String`` helper (proper-prefix-is-less,
matching Z3), so ``vera verify`` and ``vera run`` agree.  The
``TestStringOrdering927`` cases below WASM-crashed on the pre-fix compiler.
"""

from __future__ import annotations

import tempfile

from vera.checker import typecheck, typecheck_with_artifacts
from vera.codegen import CompileResult, compile as codegen_compile, execute
from vera.parser import parse_file, parse_to_ast
from vera.transform import transform
from vera.verifier import VerifyResult, verify


# ---------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------

def _errors(source: str) -> list[str]:
    prog = parse_to_ast(source)
    diags = typecheck(prog, source=source)
    return [d.error_code for d in diags if d.severity == "error"]


def _error_descs(source: str) -> list[str]:
    prog = parse_to_ast(source)
    diags = typecheck(prog, source=source)
    return [d.description for d in diags if d.severity == "error"]


def _compile(source: str) -> CompileResult:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    tree = parse_file(path)
    ast = transform(tree)
    return codegen_compile(ast, source=source, file=path)


def _run(source: str, fn: str | None = None) -> int:
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected compile errors: {errors}"
    exec_result = execute(result, fn_name=fn)
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _verify(source: str) -> VerifyResult:
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast, source)
    return verify(
        ast, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


# =====================================================================
# 1. The checker rejects compare / ordering on a user ADT (E242)
# =====================================================================

class TestCompareAdtRejected921:
    def test_compare_on_recursive_adt_rejected(self) -> None:
        # RED on base: this checks OK, then runs to the wrong Ordering.
        src = """
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match compare(Cons(1, Nil), Cons(1, Nil)) {
    Equal -> 1,
    Less -> 2,
    Greater -> 3
  }
}
"""
        assert "E242" in _errors(src)

    def test_compare_on_simple_adt_rejected(self) -> None:
        # A one-field record is just as non-orderable as a recursive type.
        src = """
private data Box { MkBox(Int) }

public fn f(@Box -> @Ordering)
  requires(true)
  ensures(true)
  effects(pure)
{
  compare(@Box.0, @Box.0)
}
"""
        assert "E242" in _errors(src)

    def test_compare_on_enum_rejected(self) -> None:
        # A nullary-only enum has no total order in v0.1.0 either.
        src = """
private data Color { Red, Green, Blue }

public fn f(@Color -> @Ordering)
  requires(true)
  ensures(true)
  effects(pure)
{
  compare(@Color.0, @Color.0)
}
"""
        assert "E242" in _errors(src)

    def test_constrained_generic_compare_is_accepted(self) -> None:
        # A `forall<T where Ord<T>>` body may `compare(@T, @T)` — the Ord
        # constraint promises orderability, and the bare type variable is
        # deferred to monomorphization.  The E242 gate must NOT fire on the
        # unresolved `T`; rejecting it would break constrained generics.
        src = """
private forall<T where Ord<T>> fn cmp_sign(@T, @T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match compare(@T.1, @T.0) { Less -> 0 - 1, Equal -> 0, Greater -> 1 }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  cmp_sign(2, 5)
}
"""
        assert _errors(src) == []
        # And a correct Ord instantiation still runs (2 < 5 → Less → -1).
        assert _run(src, fn="main") == -1

    def test_constrained_generic_instantiated_with_adt_rejected(self) -> None:
        # SOUNDNESS: deferring the TypeVar in the generic body must NOT open a
        # hole — instantiating a `forall<T where Ord<T>>` with a non-Ord ADT is
        # caught by the monomorphizer's constraint gate (E613) at compile time,
        # so it can never silently miscompile.
        src = """
private data Box { MkBox(Int) }

private forall<T where Ord<T>> fn cmp_sign(@T, @T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match compare(@T.1, @T.0) { Less -> 0 - 1, Equal -> 0, Greater -> 1 }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  cmp_sign(MkBox(1), MkBox(2))
}
"""
        result = _compile(src)
        codes = [d.error_code for d in result.diagnostics
                 if d.severity == "error"]
        assert "E613" in codes, f"Expected E613, got: {codes}"

    def test_rejection_names_the_type(self) -> None:
        src = """
private data Box { MkBox(Int) }

public fn f(@Box -> @Ordering)
  requires(true)
  ensures(true)
  effects(pure)
{
  compare(@Box.0, @Box.0)
}
"""
        descs = " ".join(_error_descs(src)).lower()
        assert "box" in descs
        assert "orderable" in descs or "ord" in descs


# =====================================================================
# 2. The verifier does not traceback on compare-in-contract over an ADT
# =====================================================================

class TestVerifierNoTracebackOnAdtCompare921:
    def test_compare_adt_in_ensures_no_traceback(self) -> None:
        # RED on base: verify() raised TypeError('<' not supported between
        # instances of 'DatatypeRef').  The checker gate now stops it earlier,
        # but the direct verify() API must not crash even if reached: the
        # smt.py guard demotes an ADT ordering to Tier 3 rather than raising.
        src = """
private data Box { MkBox(Int) }

public fn f(@Box -> @Ordering)
  requires(true)
  ensures(eq(compare(@Box.0, @Box.0), Equal))
  effects(pure)
{
  compare(@Box.0, @Box.0)
}
"""
        # Must not raise; a clean VerifyResult (errors, no Python traceback).
        result = _verify(src)
        assert result is not None


# =====================================================================
# 3. Regression — compare / ordering on primitives is UNCHANGED
# =====================================================================

class TestPrimitiveOrderingUnchanged921:
    def test_compare_int_equal(self) -> None:
        src = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match compare(5, 5) { Equal -> 1, Less -> 2, Greater -> 3 }
}
"""
        assert _run(src, fn="main") == 1

    def test_compare_int_less(self) -> None:
        src = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match compare(2, 5) { Equal -> 1, Less -> 2, Greater -> 3 }
}
"""
        assert _run(src, fn="main") == 2

    def test_compare_int_greater(self) -> None:
        src = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match compare(9, 5) { Equal -> 1, Less -> 2, Greater -> 3 }
}
"""
        assert _run(src, fn="main") == 3

    def test_compare_string_ok_check(self) -> None:
        # String is orderable (§4.5), so the checker must still accept it.
        # (Note: string `<`/compare codegen is a separate pre-existing bug,
        # unrelated to #921's ADT-ordering fix — checker acceptance is the
        # scope here.)
        src = """
public fn f(@String -> @Ordering)
  requires(true)
  ensures(true)
  effects(pure)
{
  compare(@String.0, @String.0)
}
"""
        assert _errors(src) == []

    def test_compare_nat_ok_check(self) -> None:
        src = """
public fn f(@Nat -> @Ordering)
  requires(true)
  ensures(true)
  effects(pure)
{
  compare(@Nat.0, @Nat.0)
}
"""
        assert _errors(src) == []

    def test_compare_float_ok_check(self) -> None:
        src = """
public fn f(@Float64 -> @Ordering)
  requires(true)
  ensures(true)
  effects(pure)
{
  compare(@Float64.0, @Float64.0)
}
"""
        assert _errors(src) == []

    def test_compare_byte_ok_check(self) -> None:
        src = """
public fn f(@Byte -> @Ordering)
  requires(true)
  ensures(true)
  effects(pure)
{
  compare(@Byte.0, @Byte.0)
}
"""
        assert _errors(src) == []


# =====================================================================
# 4. Regression — eq / == on ADTs is UNCHANGED (structural equality)
# =====================================================================

class TestAdtEqUnchanged921:
    def test_eq_adt_structural_still_works(self) -> None:
        # `eq` on an ADT is the structural-equality path (#773), untouched.
        src = """
private data List<T> { Nil, Cons(T, List<T>) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if eq(Cons(1, Nil), Cons(1, Nil)) then { 1 } else { 0 }
}
"""
        assert _run(src, fn="main") == 1

    def test_eq_adt_check_ok(self) -> None:
        src = """
private data Box { MkBox(Int) }

public fn f(@Box -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(@Box.0, @Box.0)
}
"""
        assert _errors(src) == []


# =====================================================================
# 5. Soundness — primitive compare in an ensures still proves at Tier 1
# =====================================================================

class TestCompareContractSoundness921:
    def test_compare_int_ensures_verifies_tier1(self) -> None:
        # A true postcondition over primitive compare must still Tier-1 verify
        # (the checker gate rejects only ADT operands, not primitives).
        src = """
public fn cmp_self(@Int -> @Ordering)
  requires(true)
  ensures(compare(@Int.0, @Int.0) == Equal)
  effects(pure)
{
  compare(@Int.0, @Int.0)
}
"""
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Unexpected verify errors: {errors}"
        assert result.summary.tier1_verified >= 1

    def test_false_compare_ensures_rejected(self) -> None:
        # A FALSE postcondition over primitive compare must be rejected by
        # verify (no false Tier-1): compare(a, a) is Equal, never Less.
        src = """
public fn cmp_self_bad(@Int -> @Ordering)
  requires(true)
  ensures(compare(@Int.0, @Int.0) == Less)
  effects(pure)
{
  compare(@Int.0, @Int.0)
}
"""
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, "Expected a verify error for the false postcondition"


# =====================================================================
# 5b. Bool reached through a constrained generic — the ONE non-orderable
#     operand that slipped past both the E242 check gate and the E613
#     constraint gate (PR #929 adversarial-review finding).
# =====================================================================

class TestBoolThroughGenericRejected921:
    """`forall<T where Ord<T>>` instantiated at `Bool` was a silent
    wrong runtime result AND a verifier `TypeError` crash.

    The checker's E242 gate deliberately DEFERS a bare-``TypeVar`` operand to
    monomorphization, trusting the E613 ``Ord``-constraint gate to reject a bad
    instantiation.  For an ADT instantiation E613 fires (the ctor type is not in
    codegen's ``_ORD_TYPES``).  For **Bool** it did NOT, because ``_ORD_TYPES``
    still contained ``"Bool"`` — so ``Ord<Bool>`` wrongly satisfied the
    constraint and the monomorphized clone lowered ``compare`` / ``<`` on the two
    Bool ``i32`` values to a signed ``i32.lt_s``: a silent order for a type Vera
    says has no order (§4.5 never orders Bool).  The verifier had the parallel
    hole — it monomorphizes minus the constraint filter, and the smt guard only
    degraded ``DatatypeSortRef`` (not ``BoolSortRef``), so a Bool-through-generic
    ``compare`` in a contract predicate crashed ``verify()`` with
    ``TypeError: '<' not supported between instances of 'BoolRef' and 'BoolRef'``.

    Each RED assertion below FAILS on the pre-fix compiler:
    ``run`` returns ``1`` / ``-1`` instead of raising E613; ``verify()`` raises.
    """

    _CMP2 = """
private forall<T where Ord<T>> fn cmp2(@T, @T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match compare(@T.0, @T.1) { Less -> 0 - 1, Equal -> 0, Greater -> 1 } }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ cmp2(false, true) }
"""

    def test_bool_through_generic_check_passes(self) -> None:
        # The deferral is intentional: a bare `T` under `Ord<T>` is NOT rejected
        # at check time — the constraint gate is trusted to catch a bad concrete
        # instantiation.  So `vera check` must still pass (exit 0 / no errors).
        assert _errors(self._CMP2) == []

    def test_bool_through_generic_compile_rejects_e613(self) -> None:
        # RED on base: compiled clean and `execute` returned a silent `1`
        # (`i32.lt_s` decided `false < true`).  With `"Bool"` gone from
        # `_ORD_TYPES`, the `Ord<Bool>` instantiation now trips the constraint
        # gate → a clean E613, NO binary, NO silent numeric result.
        result = _compile(self._CMP2)
        codes = [d.error_code for d in result.diagnostics
                 if d.severity == "error"]
        assert "E613" in codes, f"Expected E613, got: {codes}"

    def test_bool_through_generic_reversed_also_rejected(self) -> None:
        # The mirror instantiation `cmp2(true, false)` returned a silent `-1` on
        # the pre-fix compiler; it must reject on the same E613, not run.
        src = self._CMP2.replace("cmp2(false, true)", "cmp2(true, false)")
        result = _compile(src)
        codes = [d.error_code for d in result.diagnostics
                 if d.severity == "error"]
        assert "E613" in codes, f"Expected E613, got: {codes}"

    def test_bool_through_generic_verify_no_traceback(self) -> None:
        # RED on base: `verify()` raised `TypeError: '<' not supported between
        # instances of 'BoolRef' and 'BoolRef'` — an uncaught traceback out of
        # the verifier (it monomorphizes minus the constraint filter, so E613
        # never runs there; the smt guard only degraded DatatypeSortRef).  The
        # widened guard now degrades a Bool-sorted ordering to Tier 3, so the
        # direct verify() API returns a clean VerifyResult instead of crashing.
        src = """
private forall<T where Ord<T>> fn cmp2(@T, @T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ match compare(@T.0, @T.1) { Less -> true, Equal -> true, Greater -> false } }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(cmp2(false, false) == true)
  effects(pure)
{ cmp2(false, false) }
"""
        # Must not raise a Python traceback; a clean VerifyResult is enough.
        result = _verify(src)
        assert result is not None

    def test_int_through_generic_positive_control(self) -> None:
        # POSITIVE CONTROL: the SAME generic instantiated at `Int` — a genuinely
        # orderable primitive — must still compile AND run.  The body compares
        # `@T.0` (De Bruijn most-recent = 2nd arg = 5) to `@T.1` (1st arg = 2),
        # i.e. `compare(5, 2)` → Greater → 1.  This proves the fix removes ONLY
        # Bool, not the legitimate Ord primitives.
        src = self._CMP2.replace("cmp2(false, true)", "cmp2(2, 5)")
        assert _errors(src) == []
        assert _run(src, fn="main") == 1

    def test_int_through_generic_less_control(self) -> None:
        # And the Less arm: `cmp2(5, 2)` → `compare(2, 5)` → Less → -1.  Two
        # distinct non-fallback values (1 above, -1 here) pin real ordering, so
        # a scalar mis-lowering could not coincide with both.
        src = self._CMP2.replace("cmp2(false, true)", "cmp2(5, 2)")
        assert _errors(src) == []
        assert _run(src, fn="main") == -1

    def test_string_through_generic_positive_control(self) -> None:
        # POSITIVE CONTROL: String IS orderable (§4.5), so the same generic at
        # String must compile AND run.  `cmp2("apple", "banana")` compares
        # `@T.0` ("banana") to `@T.1` ("apple") → Greater → 1.
        src = self._CMP2.replace('cmp2(false, true)', 'cmp2("apple", "banana")')
        assert _errors(src) == []
        assert _run(src, fn="main") == 1


# =====================================================================
# 6. #927 — String ordering is IMPLEMENTED (lexicographic), not rejected
# =====================================================================

def _run_bool(cond: str) -> int:
    """Run `if <cond> then {1} else {0}` and return the 1/0 result."""
    src = (
        "public fn main(@Unit -> @Int) requires(true) ensures(true) "
        "effects(pure)\n"
        "{ if " + cond + " then { 1 } else { 0 } }\n"
    )
    return _run(src, fn="main")


class TestStringOrdering927:
    # Every case below WASM-crashed on the pre-fix compiler ("type mismatch:
    # expected i64, found i32" — an i64 op emitted on the string (ptr,len)
    # pair).  String IS orderable (§4.5), so it is implemented lexicographically.

    def test_string_lt_true(self) -> None:
        assert _run_bool('"apple" < "banana"') == 1

    def test_string_lt_false(self) -> None:
        assert _run_bool('"banana" < "apple"') == 0

    def test_string_lt_equal(self) -> None:
        # Equal strings: `<` is false.  (Distinct from a fallback: a scalar
        # pointer compare would give an allocation-order answer here.)
        assert _run_bool('"a" < "a"') == 0

    def test_string_lt_proper_prefix(self) -> None:
        # Proper prefix is less (matches Z3 StringSort ordering).
        assert _run_bool('"a" < "ab"') == 1

    def test_string_lt_prefix_reverse(self) -> None:
        assert _run_bool('"ab" < "a"') == 0

    def test_string_gt(self) -> None:
        assert _run_bool('"banana" > "apple"') == 1

    def test_string_le_equal(self) -> None:
        assert _run_bool('"ab" <= "ab"') == 1

    def test_string_ge_equal(self) -> None:
        assert _run_bool('"a" >= "a"') == 1

    def test_string_byte_order_uppercase(self) -> None:
        # ASCII byte order: 'Z' (0x5A) < 'a' (0x61).
        assert _run_bool('"Z" < "a"') == 1

    def test_string_differing_later_byte(self) -> None:
        # 'f' (0x66) > 'e' (0x65) at the last position.
        assert _run_bool('"applf" > "apple"') == 1

    def test_compare_string_less(self) -> None:
        src = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match compare("apple", "banana") { Less -> 1, Equal -> 2, Greater -> 3 }
}
"""
        assert _run(src, fn="main") == 1

    def test_compare_string_equal(self) -> None:
        src = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match compare("hi", "hi") { Less -> 1, Equal -> 2, Greater -> 3 }
}
"""
        assert _run(src, fn="main") == 2

    def test_compare_string_greater(self) -> None:
        src = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match compare("zebra", "apple") { Less -> 1, Equal -> 2, Greater -> 3 }
}
"""
        assert _run(src, fn="main") == 3

    def test_string_order_ensures_verifies_and_runs(self) -> None:
        # SOUNDNESS differential: a TRUE string-order postcondition must
        # verify at Tier 1 (the verifier models String via Z3 StringSort) AND
        # run without trapping — proving the WASM `$rt.cmp_String` lowering agrees
        # with Z3's ordering.
        src = """
public fn apple_lt_banana(@Unit -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{
  "apple" < "banana"
}

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  apple_lt_banana(())
}
"""
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Unexpected verify errors: {errors}"
        assert result.summary.tier1_verified >= 1
        assert _run(src, fn="main") == 1

    def test_false_string_order_ensures_rejected(self) -> None:
        # A FALSE string-order postcondition must be rejected by verify (no
        # false Tier-1): "banana" < "apple" is false.
        src = """
public fn bad(@Unit -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{
  "banana" < "apple"
}
"""
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, "Expected a verify error for the false string ordering"
