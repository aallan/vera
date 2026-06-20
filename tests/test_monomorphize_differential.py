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
    # option_map$Int_Int; the verifier must discover it via prelude injection.
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
    """The (generic name, concrete types) set the verifier discovers."""
    verifier = ContractVerifier(source=source, file=path)
    verifier.register_program(program)  # type: ignore[arg-type]
    result = verifier._collect_instantiations(program)  # type: ignore[arg-type]
    return {(name, ct) for name, cts in result.items() for ct in cts}


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


def test_imported_generic_symmetric_between_codegen_and_verifier() -> None:
    """A generic imported from another module and instantiated by the importer
    is monomorphized by NEITHER codegen nor the verifier: both build their
    instantiation set from the local ``program.declarations`` only (codegen's
    mono pipeline carries no module attribution — pinned for #661 in
    test_codegen_modules).  So they stay symmetric and the differential
    invariant (verifier covers exactly codegen's emitted set) holds with
    equality — there is no false Tier-1 from cross-module generics.  If codegen
    ever gains cross-module monomorphization, this test flags that the verifier's
    discovery must match it."""
    from vera.resolver import ResolvedModule

    a_src = (
        "public forall<T> fn ext_id(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
    )
    b_src = (
        "import a;\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ ext_id(42) }\n"
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
        verifier_set = {
            (n, ct)
            for n, cts in verifier._collect_instantiations(prog_b).items()
            for ct in cts
        }
    finally:
        os.unlink(bp)

    # Neither side monomorphizes the imported generic → symmetric (both empty).
    assert not any(n == "ext_id" for n, _ in codegen_set)
    assert verifier_set == codegen_set
