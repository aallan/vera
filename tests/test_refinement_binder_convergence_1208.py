"""Codegen's refinement guard and :mod:`vera.naming` share ONE derivation.

The runtime guard for a refined parameter has to bind its predicate under
exactly the key the predicate's own ``@Base.n`` resolves to — and under the
key the checker bound that binder to.  Two hand-maintained derivations of
"chase the alias chain, name the base, conjoin the base's implicit range"
existed (``ContractsMixin._refinement_guard_parts`` and
:func:`vera.naming.refinement_binder_parts`) and had already drifted at two
corners, so this pins the surviving one against its consumer.

A DIFFERENTIAL, not a unit test on either side: the failure mode is the two
disagreeing, which a green test of each alone cannot see.  Codegen's two
WASM-specific decisions — reject a nested refinement base loudly (E618),
emit no guard at all for an erased base — are layered on top and are pinned
here too, because "converge the derivations" must not quietly drop them.
"""
from __future__ import annotations

import pytest

from vera import ast, naming
from vera.codegen import CodeGenerator, CompileResult
from vera.resolver import ResolvedModule
from vera.codegen.api import WasmTrapError

from tests import pipeline
from tests.codegen_helpers import _compile, _compile_ok, _run
from tests.module_fixture_helpers import resolved_module as _resolved


def _compile_mod(
    source: str, modules: list[ResolvedModule],
) -> CompileResult:
    """Compile *source* against *modules*, asserting it type-checks first.

    Check-clean is the premise: a fixture rejected before codegen would never
    reach the emission path under test, and an assertion about which codegen
    diagnostics came out would pass vacuously.
    """
    checked = pipeline.check(source, file="fixture.vera", modules=modules)
    _ = checked.program  # raises the parse or transform error
    check_errors = list(checked.errors)
    assert not check_errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:70]) for d in check_errors]}"
    )
    return pipeline.compile(
        source, file="fixture.vera", modules=modules, checked=False,
    ).result


_PRELUDE = """\
type Pos = { @Int | @Int.0 > 0 };
type Pos2 = Pos;
type Count = Nat;
type SmallCount = { @Count | @Count.0 < 10 };
type Txt = String;
type Sized = { @Array<Txt> | array_length(@Array<Txt>.0) > 0 };
type Small = { @Byte | @Byte.0 > 5 };
type Plain = Int;
"""


def _generator(source: str) -> CodeGenerator:
    """A CodeGenerator with *source*'s aliases registered, mid-compile state.

    Compiling is what populates the flat alias maps and the ``_alias_env``
    derived from them, so the guard derivation is exercised against the same
    environment a real compile uses rather than a hand-built one.
    """
    compiled = pipeline.compile(source, file="<conv>", checked=False)
    _ = compiled.result  # raises the parse or transform error
    assert compiled.generator is not None
    return compiled.generator


_SHAPES = ["Pos", "Pos2", "SmallCount", "Sized", "Small", "Count", "Plain"]


@pytest.mark.parametrize("alias", _SHAPES)
def test_codegen_guard_and_naming_agree(alias: str) -> None:
    """One derivation: codegen's guard is naming's answer, or naming says None.

    Covers a direct refinement, a refinement reached through an alias hop, a
    ``@Nat``-based and a ``@Byte``-based refinement (both range-conjoining),
    a composite base whose binder is a RESOLVED argument list
    (``Array<String>``, not the source's ``Array<Txt>``), and two
    non-refinements that must return ``None`` on both sides.
    """
    source = _PRELUDE + f"""
public fn probe(@{alias} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}
"""
    gen = _generator(source)
    te = ast.NamedType(name=alias, type_args=None)

    parts = naming.refinement_binder_parts(te, gen._alias_env)
    guard = gen._refinement_guard_parts(te)

    if parts is None:
        assert guard is None, (
            f"codegen emits a guard for @{alias} that naming reports no "
            f"binder for: {guard}"
        )
        return
    assert guard is not None, (
        f"naming derives a binder for @{alias} ({parts.binder_name}) that "
        "codegen drops"
    )
    predicate, binder_name = guard
    assert binder_name == parts.binder_name
    assert predicate == parts.predicate


def test_binder_is_the_key_a_predicate_reference_resolves_to() -> None:
    """The property the convergence exists to hold: bind side == reference side.

    A guard that pushes the value under one name while the predicate's
    ``@Base.n`` resolves under another emits a check that reads nothing.
    """
    source = _PRELUDE + """
public fn probe(@Sized -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""
    gen = _generator(source)
    guard = gen._refinement_guard_parts(
        ast.NamedType(name="Sized", type_args=None))
    assert guard is not None
    _, binder_name = guard
    assert binder_name == naming.slot_ref_key(
        ast.SlotRef(
            type_name="Array",
            type_args=(ast.NamedType(name="Txt", type_args=None),),
            index=0,
        ),
        gen._alias_env,
    )


def test_nested_refinement_base_still_rejected_loudly() -> None:
    """The E618 codegen layers on top of the shared derivation (#746 review).

    Naming reports the shape (``base_is_refinement``); codegen decides it is
    an error, because the guard it could emit would check only the OUTER
    predicate and silently drop the inner membership — accepting ``-1`` for
    ``type Tiny = { @Pos | @Pos.0 < 10 }`` over ``Pos = { @Int | @Int.0 > 0 }``.
    """
    source = """
type Pos = { @Int | @Int.0 > 0 };
type Tiny = { @Pos | @Pos.0 < 10 };
public fn f(@Tiny -> @Int) requires(true) ensures(true) effects(pure) { 0 }
"""
    result = _compile(source)
    errs = [d for d in result.diagnostics
            if d.severity == "error" and d.error_code == "E618"]
    assert errs, f"expected E618; diagnostics: {result.diagnostics}"
    assert "resolves to another refinement" in errs[0].description
    # ONE per declaration: `_refinement_guard_parts` is consulted from several
    # places per function, so a per-visit report would already double here.
    assert len(errs) == 1, [d.description for d in errs]


def test_nested_refinement_base_reports_once_per_declaration() -> None:
    """One declaration, one E618 — across monomorphized clones too.

    A generic carrying a CONCRETE nested-refinement parameter is compiled once
    per instantiation from the same spans, so the two clones of ``g`` below
    reported the single ``@Tiny`` parameter twice, at identical file/line/
    column (PR #1224 review).  Distinct sites must still each report, which is
    what the second half pins — a fix that deduped by error code alone would
    swallow the second declaration's diagnostic.
    """
    two_clones = """
type Pos = { @Int | @Int.0 > 0 };
type Tiny = { @Pos | @Pos.0 < 10 };

public forall<T> fn g(@T, @Tiny -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(1, 5) + g(true, 5)
}
"""
    errs = [d for d in _compile(two_clones).diagnostics
            if d.error_code == "E618"]
    assert len(errs) == 1, [
        (d.location.line, d.location.column, d.description[:60]) for d in errs
    ]

    # Two genuinely distinct sites (parameter and return) still report twice.
    two_sites = """
type Pos = { @Int | @Int.0 > 0 };
type Tiny = { @Pos | @Pos.0 < 10 };
public fn f(@Tiny -> @Tiny)
  requires(true)
  ensures(true)
  effects(pure)
{ @Tiny.0 }
"""
    sites = {(d.location.line, d.location.column)
             for d in _compile(two_sites).diagnostics
             if d.error_code == "E618"}
    assert len(sites) == 2, sites


def test_two_modules_at_one_coordinate_each_report() -> None:
    """The dedup key is a location, so the location must carry its own file.

    ``_error_once`` keys on the resolved ``(file, line, column)`` on the
    premise that a resolved location names the file it belongs to.  That premise held at
    three of the four places codegen works on an imported module's
    declarations; the mono-clone body pass entered the defining module's
    ALIAS scope without its SOURCE scope, so a clone of an IMPORTED generic
    stamped the importer's path onto module-local coordinates.  Two library
    modules of identical shape — ordinary, since a library template gets
    copied — then produced the same key from different declarations and the
    second was swallowed.

    Both halves are asserted, because the location was wrong in two ways at
    once and either alone under-specifies the fix: the COUNT (one diagnostic
    per declaration, not one for both) and the ATTRIBUTION (each names its own
    module's file and quotes its own module's line).  The two declarations are
    pinned to identical line/column first — that coincidence is what makes the
    file the only discriminator, so a fixture edit that de-aligned them would
    leave this test green for the wrong reason.
    """
    def lib(mod: str, fn: str) -> str:
        return f"""module {mod};

type Pos = {{ @Int | @Int.0 > 0 }};
type Tiny = {{ @Pos | @Pos.0 < 10 }};
public forall<T> fn {fn}(@T, @Tiny -> @Int)
  requires(true) ensures(true) effects(pure)
{{ 0 }}
"""

    main = """import alib(ga);
import blib(gb);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ ga(1, 5) + gb(1, 5) }
"""
    modules = [
        _resolved(("alib",), lib("alib", "ga")),
        _resolved(("blib",), lib("blib", "gb")),
    ]
    errs = [d for d in _compile_mod(main, modules).diagnostics
            if d.error_code == "E618"]

    assert len({(d.location.line, d.location.column) for d in errs}) <= 1, (
        "the two declarations must sit at ONE coordinate for this fixture to "
        f"discriminate on file: {[(d.location.line, d.location.column) for d in errs]}"
    )
    assert len(errs) == 2, [
        (d.location.file, d.location.line, d.location.column) for d in errs
    ]
    assert len({d.location.file for d in errs}) == 2, (
        "both diagnostics were attributed to one file: "
        f"{[d.location.file for d in errs]}"
    )

    # Attribution, not merely distinctness: each diagnostic must quote the
    # declaration it is about.  A location naming the importer pointed past
    # that file's last line, which renders an empty `source_line`.
    by_file = {d.location.file: d for d in errs}
    quoted = sorted(d.source_line.strip() for d in errs)
    assert all(q for q in quoted), f"empty source_line: {quoted!r}"
    assert [q.split("fn ")[1].split("(")[0] for q in quoted] == ["ga", "gb"], (
        f"a diagnostic quoted the wrong declaration: {quoted!r}"
    )
    assert {str(m.file_path) for m in modules} == set(by_file), (
        "diagnostics were not attributed to the defining modules' files: "
        f"{sorted(by_file)}"
    )


@pytest.mark.parametrize(
    ("alias", "base"),
    [("Nothing", "@Unit"), ("FNothing", "@Future<Unit>")],
)
def test_erased_base_emits_no_guard(alias: str, base: str) -> None:
    """Codegen's other layered decision: a base with no WASM local.

    ``@Unit`` erases, so there is nothing to load into a boundary check and
    codegen emits no guard — naming has no opinion, because whether a type
    has a runtime representation is not a naming question.

    ``Future<Unit>`` is the corner that has to be parametrized rather than
    assumed: it erases identically but is not spelled ``Unit``, and keying
    the skip on the NAME instead of on codegen's own erasure raised a raw
    ``ValueError`` out of ``_compile_fn`` (#943 review).  Codegen keys on
    ``_type_expr_to_wasm_type``; this is the test that would notice it going
    back to a name.
    """
    source = f"""
type {alias} = {{ {base} | true }};
public fn f(@{alias} -> @Int) requires(true) ensures(true) effects(pure) {{ 0 }}
"""
    gen = _generator(source)
    te = ast.NamedType(name=alias, type_args=None)
    assert naming.refinement_binder_parts(te, gen._alias_env) is not None
    assert gen._refinement_guard_parts(te) is None


def test_byte_range_still_conjoined_at_runtime() -> None:
    """The range conjunction is not merely structural — it traps.

    ``300`` satisfies ``> 5`` but not ``<= 255``; the guard rejects it, which
    is what proves the shared derivation's conjunction reaches the emitted
    check rather than only the returned AST.
    """
    from vera.codegen import execute

    source = """
type BigByte = { @Byte | @Byte.0 > 5 };
public fn f(@BigByte -> @Byte)
  requires(true) ensures(true) effects(pure)
{ @BigByte.0 }
"""
    result = _compile_ok(source)
    # The `match=` regex is the discrimination — it names the exact conjunct
    # that has to reach the emitted check — and `kind` is what rules out an
    # unrelated trap wearing the same words (PR #1224 review).  Both, not
    # either.
    with pytest.raises(WasmTrapError, match=r"@Byte\.0 <= 255") as exc:
        execute(result, fn_name="f", args=[300])
    assert exc.value.kind == "contract_violation", exc.value.kind
    assert _run(source, fn="f", args=[7]) == 7


def test_nat_range_still_conjoined_at_runtime() -> None:
    """The ``@Nat`` branch of the same conjunction, also at runtime.

    The parametrized differential covers ``Nat`` structurally, but structure
    is what a second copy of the walk could still reproduce — the ``@Byte``
    test exists because reaching the emitted check is a separate claim, and
    the ``@Nat`` branch is a separate branch.  The written predicate is chosen
    so a NEGATIVE argument satisfies it (``-1 < 100``): only the implicit
    ``>= 0`` conjunct rejects it, so dropping that conjunct is what this
    catches.
    """
    from vera.codegen import execute

    source = """
type SmallNat = { @Nat | @Nat.0 < 100 };
public fn f(@SmallNat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @SmallNat.0 }
"""
    result = _compile_ok(source)
    # Same pairing as the `@Byte` twin: the regex pins the implicit conjunct,
    # `kind` pins that it is the contract guard that rejected the value.
    with pytest.raises(WasmTrapError, match=r"@Nat\.0 >= 0") as exc:
        # An untrusted host's -1: `execute` refuses it by default.
        execute(result, fn_name="f", args=[-1], check_int_args=False)
    assert exc.value.kind == "contract_violation", exc.value.kind
    assert _run(source, fn="f", args=[7]) == 7


def test_codegen_really_consumes_the_shared_derivation() -> None:
    """Mutation validation: perturb naming, watch codegen's guard move.

    The parametrized differential above is green whether or not the two sides
    share an implementation — that is exactly what let a second copy drift
    unnoticed.  This is the assertion that distinguishes them: replace
    :func:`vera.naming.refinement_binder_parts` with one that renames the
    binder AND rewrites the predicate, and codegen's guard must report both.
    A codegen that still carries its own copy of the walk answers the old
    values and fails here.

    BOTH fields are perturbed because they travel by different routes:
    ``binder_name`` is the key the guard pushes under, ``predicate`` is what
    it checks — and the ``@Nat``/``@Byte`` conjunction lives on the predicate,
    so a codegen that took naming's NAME while rebuilding its own predicate
    would pass a name-only mutation (#1208 round 2).
    """
    source = _PRELUDE + """
public fn probe(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""
    gen = _generator(source)
    te = ast.NamedType(name="Pos", type_args=None)
    assert gen._refinement_guard_parts(te) == (
        naming.refinement_binder_parts(te, gen._alias_env).predicate,  # type: ignore[union-attr]
        "Int",
    )

    original = naming.refinement_binder_parts
    mutant_predicate = ast.BoolLit(value=False)

    def perturbed(
        te_: ast.TypeExpr, env: naming.AliasEnv,
    ) -> naming.RefinementBinder | None:
        parts = original(te_, env)
        if parts is None:
            return None
        return naming.RefinementBinder(
            predicate=mutant_predicate,
            binder_name=parts.binder_name + "$MUTANT",
            base=parts.base,
            base_is_refinement=parts.base_is_refinement,
        )

    naming.refinement_binder_parts = perturbed  # type: ignore[assignment]
    try:
        mutated = gen._refinement_guard_parts(te)
    finally:
        naming.refinement_binder_parts = original  # type: ignore[assignment]

    assert mutated is not None
    assert mutated[1] == "Int$MUTANT", (
        "codegen's refinement guard did not follow vera.naming — it is still "
        f"deriving the binder itself; got {mutated[1]!r}"
    )
    assert mutated[0] is mutant_predicate, (
        "codegen's refinement guard kept its own predicate — the shared "
        f"derivation's is not what it checks; got {mutated[0]!r}"
    )
