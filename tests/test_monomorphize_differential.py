"""#732 differential soundness test for per-monomorphization verification.

Per-monomorphization static verification is sound only if the verifier checks
EVERY concrete instantiation codegen actually emits.  If the verifier's
instantiation discovery missed one, a monomorphized clone would run at runtime
whose contract was never statically checked — a false Tier-1, the forbidden
silent failure.

This test runs BOTH discoveries on the same programs and asserts the verifier's
set covers codegen's:

* name coverage — every generic codegen emits at least one instantiation of is
  also discovered by the verifier (catches a missed prelude generic, the #1
  parity risk);
* per-instantiation coverage — every concrete ``(name, types)`` codegen emits is
  discovered by the verifier (after normalizing the verifier's more-precise
  scalars through codegen's WAT collapse), so the right COUNT with the wrong
  tuples can't false-pass.

The verifier deliberately uses MORE precise type names than codegen (``Nat``
where codegen WAT-collapses to ``Int``), so it may *split* a codegen
instantiation into several — never merge — which is why coverage is one-directional
(verifier ⊇ codegen) rather than exact equality.  That extra precision is sound:
the verifier checks each body under the type the checker proved actually flows.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

from vera.codegen.core import CodeGenerator
from vera.parser import parse_file
from vera.transform import transform
from vera.verifier import ContractVerifier

_REPO_ROOT = Path(__file__).resolve().parent.parent

# Real, known-good programs that already compile + verify.  Exercise multi
# type-var generics (const<A, B>), ADT-param generics (is_some<T> over Option),
# and ability-constrained generics (ch09).
_REPO_CORPUS = [
    "tests/conformance/ch02_generics.vera",
    "tests/conformance/ch09_abilities.vera",
    "examples/generics.vera",
]

# Targeted cases for the soundness-critical scenarios.
_INLINE_CORPUS = {
    # Two type vars collapse to the same concrete type (A=B=Int) — exercises
    # the De Bruijn reindex inside _monomorphize_fn during discovery.
    "collapsed_typevars": """
private forall<A, B> fn pick_first(@A, @B -> @A)
  requires(true)
  ensures(@A.result == @A.0)
  effects(pure)
{
  @A.0
}

public fn use_collapsed(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick_first(@Int.1, @Int.0)
}
""",
    # Instantiates a PRELUDE generic (option_map).  Codegen emits
    # option_map$Int_JInt; the verifier must discover it via prelude injection.
    # This is the #1 parity risk — verify the verifier doesn't miss it.
    "prelude_option_map": """
public fn use_option_map(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_map(Some(@Int.0), fn(@Int -> @Int) effects(pure) { @Int.0 + 1 })
}
""",
    # A generic whose body calls another generic — the instantiation of `wrap`
    # is only reachable transitively, through the monomorphized body of
    # `wrap_twice`.  Exercises the transitive worklist.
    "transitive_generic": """
private forall<T> fn wrap(@T -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@T.0)
}

private forall<T> fn wrap_twice(@T -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrap(@T.0)
}

public fn use_transitive(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrap_twice(@Int.0)
}
""",
    # #769 gap 1: a PARAMETERIZED-return builtin (string_chars → Array<String>)
    # in generic-arg position — both discoveries must bind T=String from the
    # shared _BUILTIN_PARAMETERIZED_RETURNS table, never the Bool phantom.
    "builtin_param_return_769": """
private forall<T> fn first769(@Array<T> -> @T)
  requires(array_length(@Array<T>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<T>.0[0]
}

public fn use_first769(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  first769(string_chars("abc"))
}
""",
    # #769 gap 2: nested type-argument unification — E binds at depth 2 from
    # Array<Array<Int>> on both sides via the shared _unify_type_arg_pair.
    "nested_unify_769": """
private forall<E> fn head_head769(@Array<Array<E>> -> @E)
  requires(
    array_length(@Array<Array<E>>.0) > 0
      && array_length(@Array<Array<E>>.0[0]) > 0
  )
  ensures(true)
  effects(pure)
{
  @Array<Array<E>>.0[0][0]
}

public fn use_head_head769(@Array<Array<Int>> -> @Int)
  requires(
    array_length(@Array<Array<Int>>.0) > 0
      && array_length(@Array<Array<Int>>.0[0]) > 0
  )
  ensures(true)
  effects(pure)
{
  head_head769(@Array<Array<Int>>.0)
}
""",
    # #769 logic-arm parity: apply_fn / async / await returns binding a bare
    # @T — the verifier's discovery must reach the same instantiations
    # (ident769$Int, ident769$Future<Int>) codegen emits.
    "logic_arm_returns_769": """
private forall<T> fn ident769(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

private fn work769(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}

public fn use_logic_arms769(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Async>)
{
  let @Int = ident769(apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }, 21));
  let @Int = await(ident769(async(work769(@Int.0))));
  ident769(await(async(work769(@Int.1))))
}
""",
    # #898: cross-argument type-argument merge — the verifier's discovery
    # (`_collect_instantiations`, which shares `_infer_type_args_from_args` with
    # codegen) must merge the two sparse constructor arguments into the same
    # `eq2$Res<String, Int>` clone codegen emits, or the verifier⊇codegen
    # invariant breaks (a clone codegen emits that the verifier never proves).
    "cross_arg_merge_eq": """
private data Res<A, B> { MkOk(A), MkErr(B) }

private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(@T.1, @T.0)
}

public fn use_cross_arg(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq2(MkErr(5), MkOk("x"))
}
""",
    # #990: a forall<T> where-helper under a NON-generic parent is a mono base
    # — codegen emits its concrete clones (`gid$Int`, `gid$Bool`), so the
    # verifier's discovery must collect nested generics identically or the
    # clones run with contracts the verifier never proved (verifier⊇codegen
    # breaks).  Two instantiations, one reached from the parent body and one
    # from a sibling plain helper, so both discovery walks are exercised.
    "nested_generic_where_helper": """
private fn parent(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if flag(true) then { gid(@Int.0) + 5 } else { 0 }
}
where {
  forall<T> fn gid(@T -> @T)
    requires(true)
    ensures(@T.result == @T.0)
    effects(pure)
  {
    @T.0
  }
  fn flag(@Bool -> @Bool)
    requires(true)
    ensures(true)
    effects(pure)
  {
    gid(@Bool.0)
  }
}

public fn use_nested(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent(10)
}
""",
}


def _codegen_emitted(
    program: object, source: str, path: str,
) -> set[tuple[str, tuple[str, ...]]]:
    """The (generic name, concrete types) set codegen actually monomorphizes."""
    gen = CodeGenerator(source=source, file=path)
    gen.compile_program(program)  # type: ignore[arg-type]
    return getattr(gen, "_emitted_instances", set())


def _verifier_discovered(
    program: object, source: str, path: str,
) -> set[tuple[str, tuple[str, ...]]]:
    """The (generic name, concrete types) set the verifier discovers.

    Reads the registered ``_instances`` (which ``register_program`` populates via
    ``_collect_instantiations`` and per-monomorphization verification actually
    consumes) rather than recomputing — so a regression in the registration seam
    surfaces here instead of being masked (PR #767 review).
    """
    verifier = ContractVerifier(source=source, file=path)
    verifier.register_program(program)  # type: ignore[arg-type]
    result = verifier._instances
    return {(name, ct) for name, cts in result.items() for ct in cts}


def _resolved_module(path: tuple[str, ...], src: str) -> object:
    """Build a ``ResolvedModule`` from source text (shared by the cross-module
    differential tests, which each need one or more imported modules)."""
    from vera.resolver import ResolvedModule

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(src)
        f.flush()
        fp = f.name
    try:
        return ResolvedModule(
            path=path, file_path=Path(fp),
            program=transform(parse_file(fp)), source=src,
        )
    finally:
        os.unlink(fp)


def _cross_module_sets(
    main_src: str, modules: list[object],
) -> tuple[set[tuple[str, tuple[str, ...]]], set[tuple[str, tuple[str, ...]]]]:
    """Return ``(codegen_emitted, verifier_discovered)`` for ``main_src`` compiled
    and registered against ``modules`` — the shared codegen↔verifier differential
    harness for the cross-module generic tests.  Reads the verifier's registered
    ``_instances`` (what per-monomorphization verification actually consumes), not
    a fresh recompute, so a registration-seam regression surfaces here."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(main_src)
        f.flush()
        mp = f.name
    try:
        prog = transform(parse_file(mp))
        gen = CodeGenerator(source=main_src, file=mp, resolved_modules=modules)
        gen.compile_program(prog)  # type: ignore[arg-type]
        codegen_set = getattr(gen, "_emitted_instances", set())
        verifier = ContractVerifier(
            source=main_src, file=mp, resolved_modules=modules,
        )
        verifier.register_program(prog)  # type: ignore[arg-type]
        verifier_set = {
            (n, ct)
            for n, cts in verifier._instances.items()
            for ct in cts
        }
    finally:
        os.unlink(mp)
    return codegen_set, verifier_set


def _assert_covers(
    program: object, source: str, path: str, label: str,
) -> None:
    codegen_set = _codegen_emitted(program, source, path)
    verifier_set = _verifier_discovered(program, source, path)

    # Guard against a vacuous pass: every corpus entry instantiates generics, so
    # an empty codegen set means the harness silently stopped exercising them.
    assert codegen_set, (
        f"[{label}] codegen emitted no instantiations — the differential "
        f"check would pass vacuously; corpus entry no longer exercises generics"
    )

    codegen_names = {n for (n, _) in codegen_set}
    verifier_names = {n for (n, _) in verifier_set}
    missing = codegen_names - verifier_names
    assert not missing, (
        f"[{label}] verifier missed generic(s) codegen emits: {sorted(missing)}\n"
        f"  codegen  = {sorted(codegen_set)}\n"
        f"  verifier = {sorted(verifier_set)}"
    )

    # Per-instantiation coverage (stronger than per-generic counts, which could
    # pass with the right COUNT but the wrong concrete tuples): every (name,
    # types) codegen emits must actually be discovered by the verifier.  The
    # verifier may infer MORE precise scalar types than codegen's WAT collapse
    # (Nat vs Int, Byte vs Bool — sound, it checks the type the value really
    # has), so normalize the verifier's set through that collapse before the
    # subset check.  (If a future corpus program diverges beyond scalars, this
    # fails loudly rather than silently passing on a wrong tuple.)
    collapse = {"Nat": "Int", "Byte": "Bool"}

    def _norm(types: tuple[str, ...]) -> tuple[str, ...]:
        return tuple(collapse.get(t, t) for t in types)

    verifier_norm = {(n, _norm(ct)) for (n, ct) in verifier_set}
    uncovered = {
        (n, ct) for (n, ct) in codegen_set if (n, _norm(ct)) not in verifier_norm
    }
    assert not uncovered, (
        f"[{label}] verifier did not cover instantiation(s) codegen emits: "
        f"{sorted(uncovered)}\n"
        f"  codegen  = {sorted(codegen_set)}\n"
        f"  verifier = {sorted(verifier_set)}"
    )


# =====================================================================
# Third consultor: call-rewrite ↔ emitted-clone agreement (#899)
# =====================================================================
# The verifier⊇codegen differential above covers TWO of the three
# monomorphization consultors: instantiation DISCOVERY (which clones get
# emitted) and the VERIFIER's discovery.  It does NOT exercise the WASM
# CALL-REWRITE (`_resolve_generic_call` / `_infer_fncall_vera_type`), which
# independently re-derives the mangled name each generic call site references.
# When call-rewrite and discovery disagree on a clone name, the call site
# references a symbol Pass 1.5 never emitted — a check-green / verify-green
# program whose `main` is dropped at `vera run` (#878's own failure class,
# reintroduced by PR #899's one-sided consultor edits).  These corpus entries
# exercise exactly the user-fn-return-into-generic-arg shapes that slipped.

_CALL_REWRITE_CORPUS: dict[str, str] = {
    # Issue 1: non-generic user fn returning a PARAMETERIZED type in
    # `Option<T>` position — call-rewrite recovers `Decimal`, discovery must too.
    "param_user_fn_return": """
private fn maybe(@Int -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ Some(decimal_from_int(@Int.0)) }

private forall<T> fn first_opt(@Option<T>, @Int -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{ @Option<T>.0 }

public fn main(@Unit -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ first_opt(maybe(3), 0) }
""",
    # Issue 1 variant: Result<Decimal, String> return.
    "param_user_fn_result_return": """
private fn tryit(@Int -> @Result<Decimal, String>)
  requires(true) ensures(true) effects(pure)
{ Ok(decimal_from_int(@Int.0)) }

private forall<T> fn first_res(@Result<T, String>, @Int -> @Result<T, String>)
  requires(true) ensures(true) effects(pure)
{ @Result<T, String>.0 }

public fn main(@Unit -> @Result<Decimal, String>)
  requires(true) ensures(true) effects(pure)
{ first_res(tryit(5), 0) }
""",
    # Issue 2: user fn returning a scalar-resolving alias in bare `@T` position
    # — discovery/verifier key on the RAW name `Age`, call-rewrite must too.
    "alias_scalar_return": """
type Age = Int;

private fn getage(@Int -> @Age)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

private forall<T> fn pick_last(@T, @T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ pick_last(getage(1), getage(2)) }
""",
    # Issue 2 variant: named refinement of a scalar.
    "refinement_scalar_return": """
type PosInt = { @Int | @Int.0 > 0 };

private fn getpos(@Int -> @PosInt)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }

private forall<T> fn pick_last(@T, @T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ pick_last(getpos(1), getpos(2)) }
""",
    # Issue 3 (#899 round 3, a NET regression vs base): a NON-generic user fn
    # returning a LITERAL PARAMETERIZED type (`Option<…>`/`Result<…>`/`Box<…>`)
    # bound to a generic's BARE `@T`.  Discovery keys the clone on the base
    # name (`pick_last$Option`); pre-fix the call-rewrite's `not ret_te.type_args`
    # gate bailed and fell through to the i32→`Bool` collapse → `pick_last$Bool`,
    # never emitted.  (`_call_rewrite_desync` on the repro shows
    # `emitted=['pick_last$Option'], dangling=['pick_last$Bool']`.)
    # #769 gap 1b: builtin SIMPLE-name returns in bare `@T` position — the
    # completed _BUILTIN_VERA_RETURN_TYPES dict is consulted by BOTH sides;
    # pre-fix discovery phantom-defaulted (ident$Bool) while the rewrite
    # chain mangled ident$String / ident$Array — dangling, main dropped.
    "builtin_simple_return_769": """
private forall<T> fn ident769(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = ident769(int_to_string(42));
  array_length(ident769(string_chars(@String.0)))
}
""",
    # #769 generic-return parity: a generic call's i32-handle / declared-Nat
    # return in generic-arg position — the rewrite's generic branch now
    # substitutes the DECLARED return (pass769$Option / natret769$Nat) exactly
    # as discovery does, instead of WAT-collapsing to Bool / Int.
    "generic_return_into_bare_typevar_769": """
private forall<T> fn ident769(@T, @T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private forall<U> fn pass769(@U -> @U)
  requires(true) ensures(true) effects(pure)
{ @U.0 }

private forall<U> fn natret769(@U -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 7 }

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = ident769(pass769(Some(42)), pass769(Some(1)));
  natret769(ident769(natret769(1), natret769(2)))
}
""",
    # #769 logic-arm parity: apply_fn closure return in bare `@T` position —
    # discovery's new _closure_arg_return_te arm mirrors the rewrite chain.
    "apply_fn_return_769": """
private forall<T> fn ident769(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ ident769(apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }, 21)) }
""",
    "param_return_into_bare_typevar": """
private fn mk(@Int -> @Option<Option<Decimal>>)
  requires(true) ensures(true) effects(pure)
{ Some(Some(decimal_from_int(@Int.0))) }

private forall<VeraT> fn pick_last(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match pick_last(mk(1), mk(2)) { Some(@Option<Decimal>) -> 0, None -> 1 } }
""",
    "result_return_into_bare_typevar": """
private fn mkr(@Int -> @Result<Option<Decimal>, String>)
  requires(true) ensures(true) effects(pure)
{ Ok(Some(decimal_from_int(@Int.0))) }

private forall<VeraT> fn pick_last(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match pick_last(mkr(1), mkr(2)) { Ok(@Option<Decimal>) -> 0, Err(@String) -> 1 } }
""",
    "adt_return_into_bare_typevar": """
private data Box<T> { MkBox(T) }

private fn mkb(@Int -> @Box<Decimal>)
  requires(true) ensures(true) effects(pure)
{ MkBox(decimal_from_int(@Int.0)) }

private forall<VeraT> fn pick_last(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match pick_last(mkb(1), mkb(2)) { MkBox(@Decimal) -> 0 } }
""",
    # #898: CROSS-ARGUMENT type-argument merge.  `eq2(MkErr(5), MkOk("x"))`
    # over `data Res<A, B> { MkOk(A), MkErr(B) }` — the first argument fixes
    # `B = Int`, the second fixes `A = String` — so discovery, the verifier, AND
    # the call-rewrite must all merge the two partial recoveries into the ONE
    # clone `eq2$Res<String, Int>`.  A one-sided merge (call-rewrite resolves
    # the bare `eq2$Res` while discovery emits `eq2$Res<String, Int>`, or vice
    # versa) drops `main` with an `unknown func` — exactly what this differential
    # exists to catch.  This is the entry that was MISSING when the merge landed.
    "cross_arg_merge_eq": """
private data Res<A, B> { MkOk(A), MkErr(B) }

private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.1, @T.0) }

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq2(MkErr(5), MkOk("x")) }
""",
    # #898: cross-argument merge, REVERSED argument order — the merge must be
    # order-independent (arg 0 fixes `A`, arg 1 fixes `B`), and all three
    # consultors must still agree on the ONE `eq2$Res<String, Int>` clone.  A
    # first-argument-wins consultor would key `eq2$Res<String, ?>` here vs the
    # `eq2$Res<?, Int>` of the non-reversed entry, so pairing the two orders
    # pins that the merged name is stable regardless of which argument arrives
    # first.
    "cross_arg_merge_eq_reversed": """
private data Res<A, B> { MkOk(A), MkErr(B) }

private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.1, @T.0) }

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq2(MkOk("x"), MkErr(5)) }
""",
}

def _mangle(name: str, types: tuple[str, ...]) -> str:
    """The mono-clone symbol for ``(name, types)`` — the shared injective
    mangler both discovery (clone emission) and call-rewrite use."""
    from vera.monomorphize import Monomorphizer

    return Monomorphizer._mangle_fn_name(name, types)


def _call_rewrite_desync(source: str) -> tuple[set[str], list[str]]:
    """Compile ``source`` in a FRESH CodeGenerator, capturing every mono-clone
    symbol the WASM CALL-REWRITE (`_resolve_generic_call`) resolves to, and
    return ``(emitted_clone_symbols, dangling_targets)``.

    A dangling target is a symbol a generic call site references but that
    discovery never emitted — the exact call-rewrite↔discovery desync #899
    caught.  Captured at the consultor level (a monkeypatch on
    `_resolve_generic_call`) rather than by scraping the WAT, because a desync
    causes the CALLING function to be SKIPPED (E602), which elides its body —
    and with it the dangling `call` — from the WAT entirely, so a WAT scan
    can't see the very evidence it needs (the mistake this test was first
    written with).  Each call builds its own compile pipeline so
    `_emitted_instances` never cross-contaminates across corpus entries.
    """
    from vera.wasm.calls import CallsMixin

    captured: list[str | None] = []
    orig = CallsMixin._resolve_generic_call

    def _spy(self: object, call: object) -> object:
        result = orig(self, call)  # type: ignore[arg-type]
        captured.append(result)  # type: ignore[arg-type]
        return result

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    try:
        program = transform(parse_file(path))
        gen = CodeGenerator(source=source, file=path)
        CallsMixin._resolve_generic_call = _spy  # type: ignore[assignment]
        try:
            gen.compile_program(program)  # type: ignore[arg-type]
        finally:
            CallsMixin._resolve_generic_call = orig  # type: ignore[assignment]
        emitted = {
            _mangle(name, types)
            for (name, types) in getattr(gen, "_emitted_instances", set())
        }
    finally:
        os.unlink(path)
    targets = {t for t in captured if t is not None}
    dangling = sorted(targets - emitted)
    return emitted, dangling


@pytest.mark.parametrize("label", sorted(_CALL_REWRITE_CORPUS))
def test_call_rewrite_matches_emitted_clones(label: str) -> None:
    """Every mono-clone a generic call site references must be an emitted
    clone — the call-rewrite consultor must pick the same name discovery /
    the verifier did.  A dangling target is the #899 desync (`main` dropped
    at run on a check-green program)."""
    source = _CALL_REWRITE_CORPUS[label]
    emitted, dangling = _call_rewrite_desync(source)
    assert emitted, (
        f"[{label}] no mono clones emitted — corpus entry no longer exercises "
        f"generic instantiation, the check would pass vacuously"
    )
    assert not dangling, (
        f"[{label}] call site references clone(s) never emitted (call-rewrite "
        f"↔ discovery desync, #899): {dangling}\n  emitted = {sorted(emitted)}"
    )


@pytest.mark.parametrize("rel", _REPO_CORPUS)
def test_verifier_covers_codegen_repo(rel: str) -> None:
    path = str(_REPO_ROOT / rel)
    program = transform(parse_file(path))
    source = Path(path).read_text(encoding="utf-8")
    _assert_covers(program, source, path, rel)


@pytest.mark.parametrize("label", sorted(_INLINE_CORPUS))
def test_verifier_covers_codegen_inline(label: str) -> None:
    source = _INLINE_CORPUS[label]
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    try:
        program = transform(parse_file(path))
        _assert_covers(program, source, path, label)
    finally:
        os.unlink(path)


@pytest.mark.parametrize("call_form", ["bare", "qualified"])
def test_imported_generic_symmetric_between_codegen_and_verifier(
    call_form: str,
) -> None:
    """A generic imported from another module and instantiated by the importer
    is monomorphized by BOTH codegen and the verifier at the SAME concrete type
    (#774).  The importer discovers the instantiation from its own call site and
    emits the clone into its own flat module; the verifier's discovery merges the
    imported (unshadowed) generic identically, so the differential invariant
    (verifier covers exactly codegen's emitted set) holds with equality — no
    false Tier-1 from cross-module generics.

    Both the bare call ``ext_id(42)`` and the module-qualified ``a::ext_id(42)``
    (an ``ast.ModuleCall`` that the shared discovery now walks, and that desugars
    to the bare target at codegen) must produce the SAME single ``ext_id<Int>``
    instantiation on both sides — a divergence between the two forms, or between
    codegen and the verifier, would reintroduce the gap this pins.

    Flips the pre-#774 tripwire: this test previously asserted NEITHER side
    monomorphized (both empty).  Now both monomorphize; the equality assertion is
    the lockstep the #732 differential demands.
    """
    from vera.resolver import ResolvedModule

    a_src = (
        "public forall<T> fn ext_id(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
    )
    call = "ext_id(42)" if call_form == "bare" else "a::ext_id(42)"
    b_src = (
        "import a;\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        f"{{ {call} }}\n"
    )

    def _resolved(path: tuple[str, ...], src: str) -> "ResolvedModule":
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(src)
            f.flush()
            fp = f.name
        try:
            return ResolvedModule(
                path=path, file_path=Path(fp),
                program=transform(parse_file(fp)), source=src,
            )
        finally:
            os.unlink(fp)

    mod_a = _resolved(("a",), a_src)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(b_src)
        f.flush()
        bp = f.name
    try:
        prog_b = transform(parse_file(bp))
        gen = CodeGenerator(source=b_src, file=bp, resolved_modules=[mod_a])
        gen.compile_program(prog_b)  # type: ignore[arg-type]
        codegen_set = getattr(gen, "_emitted_instances", set())
        verifier = ContractVerifier(
            source=b_src, file=bp, resolved_modules=[mod_a],
        )
        verifier.register_program(prog_b)  # type: ignore[arg-type]
        # Read the registered ``_instances`` that per-monomorphization verification
        # actually consumes, not a fresh recompute — so a regression in the
        # registration seam surfaces here rather than being masked (PR #767 review).
        verifier_set = {
            (n, ct)
            for n, cts in verifier._instances.items()
            for ct in cts
        }
    finally:
        os.unlink(bp)

    # Both sides monomorphize the imported generic at exactly ext_id<Int>.
    assert ("ext_id", ("Int",)) in codegen_set, (
        f"codegen must emit ext_id<Int> for the {call_form} call, "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — cross-module generic lockstep"
    )


def test_shadowed_imported_generic_symmetric_between_codegen_and_verifier(
) -> None:
    """`#814` asymmetric variant: an imported generic (`gen`) shadowed by a
    LOCAL non-generic AND module-qualified called (`g::gen`) is monomorphized by
    codegen under a ``mod$…`` name and recorded in ``_emitted_instances`` under
    that ``mod$g$gen`` base (NOT the bare `gen`, which a same-named local owns —
    CR 3519156263), so the verifier must discover the SAME qualified
    instantiation under the SAME base — else the pre-fix false Tier-1 returns
    (verify resolved the module generic's contract while codegen ran the local
    shadow).

    Pins the shadowed-side lockstep: the differential must catch a desync where
    only one of the two discovers the qualified `mod$g$gen<Int>` instantiation.
    """
    mod_a = _resolved_module(("g",), (
        "public forall<T> fn gen(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
    ))
    b_src = (
        "import g;\n\n"
        "private fn gen(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Int.0 + 100 }\n\n"
        "public fn probe(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ g::gen(5) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(b_src, [mod_a])

    assert ("mod$g$gen", ("Int",)) in codegen_set, (
        f"codegen must emit the shadowed generic's clone under its mod$… base, "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — shadowed cross-module generic "
        f"lockstep (the #814 false-Tier-1 guard)"
    )


@pytest.mark.parametrize("inner_shadowed", [False, True])
def test_transitive_shadowed_generic_symmetric(inner_shadowed: bool) -> None:
    """`#774` review (CR 3518737014): a SHADOWED imported generic whose body
    calls ANOTHER generic emits that TRANSITIVE clone — codegen and the verifier
    must discover the SAME transitive set, or a cross-module transitive clone
    runs unverified (a new false Tier-1).

    `outer<T>` (shadowed, calls `inner(@T.0)`) → `inner<T>`.  The parametrization
    covers `inner` unshadowed (a normal clone keyed `inner`) and `inner` ALSO
    shadowed (a same-module sibling keyed `mod$g$inner` — CR 3519156263: a
    shadowed clone is namespaced by its `mod$…` base so it never collides with a
    same-named local generic).  Both must appear on both sides — a desync of the
    transitive scan (codegen or verifier) flips the equality.
    """
    mod_a = _resolved_module(("g",), (
        "public forall<T> fn inner(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
        "public forall<T> fn outer(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ inner(@T.0) }\n"
    ))
    inner_local = (
        "private fn inner(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Int.0 + 200 }\n\n"
    ) if inner_shadowed else ""
    b_src = (
        "import g;\n\n"
        "private fn outer(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Int.0 + 100 }\n\n"
        f"{inner_local}"
        "public fn probe(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ g::outer(7) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(b_src, [mod_a])

    # The shadowed outer is keyed under its mod$… base; the transitive inner is
    # keyed `mod$g$inner` when a local shadows it, else the bare `inner`.
    inner_key = ("mod$g$inner", ("Int",)) if inner_shadowed else (
        ("inner", ("Int",))
    )
    assert ("mod$g$outer", ("Int",)) in codegen_set and (
        inner_key in codegen_set
    ), (
        f"codegen must emit mod$g$outer<Int> and its transitive {inner_key[0]}"
        f"<Int>, got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — transitive shadowed generic "
        f"lockstep; a missing transitive clone is a new false Tier-1"
    )


def test_unshadowed_generic_calling_shadowed_sibling_symmetric() -> None:
    """`#774` review (CR 3519063445): an UNSHADOWED generic `caller<T>` whose
    body qualified-calls a SHADOWED `g::gen` reaches that shadowed generic only
    through its clone (`caller$Int`) — codegen scans the emitted normal clones
    for shadowed ModuleCalls, and the verifier must mirror that scan, or it
    discovers a strict subset (the `mod$g$gen<Int>` clone runs unverified: a
    false Tier-1).
    """
    mod_a = _resolved_module(("g",), (
        "public forall<T> fn gen(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
    ))
    b_src = (
        "import g;\n\n"
        "private fn gen(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Int.0 + 100 }\n\n"
        "private forall<T> fn caller(@T -> @T)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ g::gen(@T.0) }\n\n"
        "public fn probe(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ caller(5) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(b_src, [mod_a])

    assert ("caller", ("Int",)) in codegen_set and (
        ("mod$g$gen", ("Int",)) in codegen_set
    ), (
        f"codegen must emit caller<Int> and the shadowed mod$g$gen<Int> it "
        f"reaches, got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — an unshadowed generic reaching "
        f"a shadowed sibling; a miss is a new false Tier-1"
    )


def test_generic_typearg_from_where_helper_return_is_discovered() -> None:
    """A generic whose type arg is fixed ONLY by a where-helper's return must be
    discovered by the verifier at the same concrete type codegen emits.

    Codegen registers every where-helper's WAT signature in ``_fn_sigs``
    (bare-name keyed), so it resolves ``wrap(scale(@Int.0))`` to ``wrap<Float64>``
    from ``scale``'s return.  If the verifier's discovery omits where-helper
    return types, the unresolved type var falls to the ``"Bool"`` phantom-var
    default in ``_infer_type_args_from_call`` and the verifier discovers
    ``wrap<Bool>`` — MISSING codegen's ``wrap<Float64>`` clone, a false Tier-1.

    The helper deliberately returns ``Float64`` (not ``Bool``) so the phantom
    default cannot coincide with the real type and mask the bug — the exact gap
    a ``Bool``-returning helper let slip through earlier (PR #767 review).
    """
    src = (
        "private forall<T>\n"
        "fn wrap(@T -> @Option<T>)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ Some(@T.0) }\n\n"
        "private fn caller(@Int -> @Option<Float64>)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ wrap(scale(@Int.0)) }\n"
        "where {\n"
        "  fn scale(@Int -> @Float64)\n"
        "    requires(true) ensures(true) effects(pure)\n"
        "  { 1.5 }\n"
        "}\n"
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(src)
        f.flush()
        path = f.name
    try:
        program = transform(parse_file(path))
        codegen_set = _codegen_emitted(program, src, path)
        verifier_set = _verifier_discovered(program, src, path)
    finally:
        os.unlink(path)

    wrap_cg = {ct for (n, ct) in codegen_set if n == "wrap"}
    wrap_ver = {ct for (n, ct) in verifier_set if n == "wrap"}
    assert wrap_cg == {("Float64",)}, (
        f"codegen should emit wrap<Float64> from scale's return, got {wrap_cg}"
    )
    # The verifier must discover EXACTLY codegen's wrap<Float64> — no more, no
    # less.  Membership alone would pass even if a stale wrap<Bool> phantom were
    # ALSO discovered; exact-set equality fails on both a miss (false Tier-1) and
    # a phantom extra (the `"Bool"` default leaking through).
    assert wrap_ver == {("Float64",)}, (
        f"verifier must discover exactly wrap<Float64> (discovered {wrap_ver}) — "
        f"where-helper return-type discovery: a miss is a false Tier-1, a stale "
        f"wrap<Bool> extra means the phantom default leaked"
    )


def test_generic_typearg_from_imported_constructor_is_discovered() -> None:
    """A local generic whose type arg is inferred from an IMPORTED constructor
    must be discovered at the same type codegen emits.

    Codegen's monomorphizer context includes imported ADTs' constructors, so it
    resolves ``id2(MkBox(7))`` to ``id2<Box>`` from ``MkBox``'s owning ADT.  The
    verifier's ``_build_mono_context`` builds ``ctor_to_adt`` from
    ``env.data_types`` + local/prelude ``DataDecl``s only — imported public
    constructors live in ``_module_constructors`` instead.  If they are omitted,
    the verifier cannot map ``MkBox`` → ``Box``, the type var falls to the
    ``"Bool"`` phantom default, and it discovers ``id2<Bool>`` — MISSING
    codegen's ``id2<Box>`` clone, a false Tier-1 (PR #767 review).
    """
    from vera.resolver import ResolvedModule

    a_src = "public data Box<T> {\n  MkBox(T)\n}\n"
    b_src = (
        "import a;\n\n"
        "private forall<T> fn id2(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n\n"
        "public fn main(@Unit -> @Box<Int>)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ id2(MkBox(7)) }\n"
    )

    def _resolved(path: tuple[str, ...], src: str) -> "ResolvedModule":
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(src)
            f.flush()
            fp = f.name
        try:
            return ResolvedModule(
                path=path, file_path=Path(fp),
                program=transform(parse_file(fp)), source=src,
            )
        finally:
            os.unlink(fp)

    mod_a = _resolved(("a",), a_src)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(b_src)
        f.flush()
        bp = f.name
    try:
        prog_b = transform(parse_file(bp))
        gen = CodeGenerator(source=b_src, file=bp, resolved_modules=[mod_a])
        gen.compile_program(prog_b)  # type: ignore[arg-type]
        cg = {ct for n, ct in getattr(gen, "_emitted_instances", set())
              if n == "id2"}
        verifier = ContractVerifier(
            source=b_src, file=bp, resolved_modules=[mod_a],
        )
        verifier.register_program(prog_b)  # type: ignore[arg-type]
        ver = {
            ct
            for n, cts in verifier._instances.items()
            for ct in cts
            if n == "id2"
        }
    finally:
        os.unlink(bp)

    assert cg == {("Box",)}, f"codegen should emit exactly id2<Box>, got {cg}"
    assert ver == {("Box",)}, (
        f"verifier should discover exactly id2<Box> (discovered {ver}) — "
        f"imported-constructor discovery gap, false Tier-1"
    )


def test_generic_typearg_from_imported_function_return_is_discovered() -> None:
    """A local generic whose type arg is inferred from an IMPORTED function's
    RETURN must be discovered at the same type codegen emits.

    Codegen's monomorphizer context seeds ``fn_ret_types`` from imported modules
    (``vera/codegen/modules.py`` ``setdefault`` over ``temp._fn_ret_type_exprs``),
    so it resolves ``id_g(make_int(...))`` to ``id_g<Int>`` from ``make_int``'s
    return type.  The verifier's ``_build_mono_context`` recorded return types
    from local/prelude declarations ONLY — imported public functions live in
    ``env.functions`` (injected by ``_register_modules``) but were never seeded
    into ``fn_ret_types``.  Without them the type var falls to the ``"Bool"``
    phantom default and the verifier discovers ``id_g<Bool>`` while codegen emits
    ``id_g<Int>``: an ASYMMETRIC miss = false Tier-1 (verified the wrong clone).
    Differentially confirmed (PR #767 review, CodeRabbit).
    """
    from vera.resolver import ResolvedModule

    a_src = (
        "public fn make_int(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 7 }\n"
    )
    b_src = (
        "import a;\n\n"
        "private forall<T> fn id_g(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ id_g(make_int(@Unit.0)) }\n"
    )

    def _resolved(path: tuple[str, ...], src: str) -> "ResolvedModule":
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(src)
            f.flush()
            fp = f.name
        try:
            return ResolvedModule(
                path=path, file_path=Path(fp),
                program=transform(parse_file(fp)), source=src,
            )
        finally:
            os.unlink(fp)

    mod_a = _resolved(("a",), a_src)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(b_src)
        f.flush()
        bp = f.name
    try:
        prog_b = transform(parse_file(bp))
        gen = CodeGenerator(source=b_src, file=bp, resolved_modules=[mod_a])
        gen.compile_program(prog_b)  # type: ignore[arg-type]
        cg = {ct for n, ct in getattr(gen, "_emitted_instances", set())
              if n == "id_g"}
        verifier = ContractVerifier(
            source=b_src, file=bp, resolved_modules=[mod_a],
        )
        verifier.register_program(prog_b)  # type: ignore[arg-type]
        ver = {
            ct
            for n, cts in verifier._instances.items()
            for ct in cts
            if n == "id_g"
        }
    finally:
        os.unlink(bp)

    assert cg == {("Int",)}, f"codegen should emit exactly id_g<Int>, got {cg}"
    assert ver == {("Int",)}, (
        f"verifier should discover exactly id_g<Int> (discovered {ver}) — "
        f"imported-function-return discovery gap, false Tier-1"
    )


def test_imported_private_shadow_fn_return_stays_symmetric() -> None:
    """The imported-function `fn_ret_types` seeding must stay UNFILTERED — exactly
    as codegen does — even when a resolved module has a private function whose
    bare name shadows an imported public one.

    Codegen harvests every resolved module's `_fn_ret_type_exprs` via `setdefault`
    (`vera/codegen/modules.py`, "including private helpers", first-seen wins), so a
    private `mk -> Bool` in module `a` (iterated first) wins the bare-name key over
    the public `mk -> Int` in module `b`.  Both codegen AND the verifier then
    discover the SAME `id_g` instantiation — the wrong one, but SYMMETRICALLY
    wrong, so `vera verify` clean still implies the runtime matches (no false
    Tier-1; the inference imprecision itself is the #769 family).

    A reviewer suggested filtering the verifier's seeding to import-public only;
    that would make the verifier discover `id_g<Int>` while codegen stays on the
    shadowed instantiation — an ASYMMETRY = the false Tier-1 it was meant to
    avoid.  This pins the symmetry so that "fix" cannot land silently, while
    asserting only agreement (not the incidental concrete type) so a later #769
    precision fix that moves BOTH sides together still passes (PR #767 review)."""
    from vera.resolver import ResolvedModule

    a_src = (
        "private fn mk(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ false }\n\n"
        "public fn a_thing(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 1 }\n"
    )
    b_src = (
        "public fn mk(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 7 }\n"
    )
    main_src = (
        "import a;\n"
        "import b;\n\n"
        "private forall<T> fn id_g(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ id_g(mk(@Unit.0)) }\n"
    )

    def _resolved(path: tuple[str, ...], src: str) -> "ResolvedModule":
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(src)
            f.flush()
            fp = f.name
        try:
            return ResolvedModule(
                path=path, file_path=Path(fp),
                program=transform(parse_file(fp)), source=src,
            )
        finally:
            os.unlink(fp)

    mods = [_resolved(("a",), a_src), _resolved(("b",), b_src)]
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(main_src)
        f.flush()
        mp = f.name
    try:
        prog = transform(parse_file(mp))
        gen = CodeGenerator(source=main_src, file=mp, resolved_modules=mods)
        gen.compile_program(prog)  # type: ignore[arg-type]
        cg = {ct for n, ct in getattr(gen, "_emitted_instances", set())
              if n == "id_g"}
        verifier = ContractVerifier(
            source=main_src, file=mp, resolved_modules=mods,
        )
        verifier.register_program(prog)  # type: ignore[arg-type]
        ver = {
            ct
            for n, cts in verifier._instances.items()
            for ct in cts
            if n == "id_g"
        }
    finally:
        os.unlink(mp)

    assert len(cg) == 1 and cg == ver, (
        f"codegen ({cg}) and verifier ({ver}) must discover the SAME single "
        f"id_g instantiation — the verifier's imported-fn seeding mirrors "
        f"codegen's unfiltered first-seen-wins harvest; a public/import filter "
        f"on the verifier side would diverge into a false Tier-1 (PR #767 review)"
    )


def test_codegen_emits_generic_reached_only_via_contract_or_where_helper() -> None:
    """A generic called ONLY from a contract clause or a ``where`` helper body
    must be emitted by codegen.

    Vera lowers ``requires``/``ensures`` to a runtime contract check, and
    compiles ``where`` helper bodies, so such a generic is invoked at run time.
    Codegen's Pass 1.5 seeds from the shared node-level walk
    (``collect_calls_in_node`` = body + contracts + ``where_fns``), not just
    ``decl.body`` — walking only the body left the clone unemitted and produced
    a ``CodegenSkip`` (`call target 'is_ok$Int' not registered`) at run time,
    while the verifier (which walks contracts/helpers) discovered it: a discovery
    divergence (PR #767 review).
    """
    src = (
        "private forall<T> fn is_ok(@T -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure) { true }\n\n"
        "private forall<T> fn innerw(@T -> @T)\n"
        "  requires(true) ensures(true) effects(pure) { @T.0 }\n\n"
        "private fn checked(@Int -> @Int)\n"
        "  requires(is_ok(@Int.0)) ensures(true) effects(pure) { hw(@Int.0) }\n"
        "where {\n"
        "  fn hw(@Int -> @Int) requires(true) ensures(true) effects(pure)\n"
        "  { innerw(@Int.0) }\n"
        "}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure) { checked(5) }\n"
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(src)
        f.flush()
        path = f.name
    try:
        program = transform(parse_file(path))
        cg = _codegen_emitted(program, src, path)
        ver = _verifier_discovered(program, src, path)
    finally:
        os.unlink(path)

    # Codegen must emit exactly the contract-reachable (`is_ok`) and
    # where-helper-reachable (`innerw`) generics — nothing more, nothing less
    # (else a missing one is a CodegenSkip at run time).
    expected = {("is_ok", ("Int",)), ("innerw", ("Int",))}
    assert cg == expected, (
        f"codegen emitted {sorted(cg)}, expected {sorted(expected)}"
    )
    # Discovery is shared, so the verifier discovers exactly what codegen emits.
    assert ver == expected, (
        f"verifier discovery diverged from codegen: {sorted(ver)}"
    )


def test_mono_emission_order_is_deterministic(tmp_path: Path) -> None:
    """Monomorphized clone emission order must be stable across runs, so that
    ``vera compile --wat`` is byte-reproducible.

    The worklist that drives ``mono_decls.append`` (and hence WAT emission
    order) is seeded from ``set[tuple[str, ...]]`` instantiation sets; sorting
    them makes the order independent of ``PYTHONHASHSEED``.  Without the sort the
    three ``idg`` clones below emit in a hash-seed-dependent order and the WAT
    differs run-to-run (clone bodies identical, only their order) — bad for
    reproducible builds (PR #767 review).
    """
    src = (
        "private forall<T> fn idg(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{\n"
        "  let @Int = idg(1);\n"
        "  let @Bool = idg(true);\n"
        "  let @Float64 = idg(1.5);\n"
        "  @Int.0\n"
        "}\n"
    )
    f = tmp_path / "det.vera"
    f.write_text(src, encoding="utf-8")
    outputs = set()
    for seed in ("0", "1", "2", "3", "4"):
        proc = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile", "--wat", str(f)],
            capture_output=True, text=True, encoding="utf-8",
            env={**os.environ, "PYTHONHASHSEED": seed},
            timeout=120,  # bound each child: a mono hang fails fast here, not at the CI timeout
        )
        assert proc.returncode == 0, proc.stderr
        outputs.add(proc.stdout)
    assert len(outputs) == 1, (
        f"`vera compile --wat` not byte-stable across PYTHONHASHSEED: "
        f"{len(outputs)} distinct outputs"
    )
