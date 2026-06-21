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
    # The verifier must cover codegen's wrap<Float64>; phantom-defaulting to
    # wrap<Bool> would leave codegen's executing clone statically unverified.
    assert ("Float64",) in wrap_ver, (
        f"verifier missed wrap<Float64> (discovered {wrap_ver}) — where-helper "
        f"return-type discovery regressed: false Tier-1"
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
            capture_output=True, text=True,
            env={**os.environ, "PYTHONHASHSEED": seed},
        )
        assert proc.returncode == 0, proc.stderr
        outputs.add(proc.stdout)
    assert len(outputs) == 1, (
        f"`vera compile --wat` not byte-stable across PYTHONHASHSEED: "
        f"{len(outputs)} distinct outputs"
    )
