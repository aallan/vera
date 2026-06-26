"""Verifier<->codegen classification differential for #798 (Stage 3, RISK 6/7).

The soundness contract: the codegen integer-overflow guard must fire at
*exactly* the sites the verifier emits an ``int_overflow`` obligation for, and
classify each site's operand type (``@Int`` i64 vs ``@Nat`` u64) *identically*
— otherwise a Tier-1-clean program traps spuriously, or (worse) a wrapping op
slips through unguarded.

A green per-combo unit suite can hide a desync between the verifier's
``_overflow_int_type`` (which reads the checker's *resolved* type) and the
codegen ``_overflow_codegen_type`` (which the pre-fix design re-derived from the
AST, mis-classifying a literal-left ``@Int`` operand as ``@Nat``).  This is the
required differential (project cross-component-soundness rule): for a corpus
exercising all five combos *and* the literal-left ambiguity, assert the
verifier's per-site (gated) classification equals the codegen's, site for site.

Both sides are driven by the SAME ``ast.span_key`` so the comparison is exact.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from vera import ast
from vera.checker import typecheck_with_artifacts
from vera.parser import parse_to_ast
from vera.verifier import ContractVerifier
from vera.wasm import StringPool
from vera.wasm.context import WasmContext

REPO_ROOT = Path(__file__).parent.parent
EXAMPLES_DIR = REPO_ROOT / "examples"
CONFORMANCE_DIR = REPO_ROOT / "tests" / "conformance"


def _corpus_files() -> list[Path]:
    """Examples + every verify/run-level conformance program."""
    manifest = json.loads(
        (CONFORMANCE_DIR / "manifest.json").read_text(encoding="utf-8"),
    )
    conformance = [
        CONFORMANCE_DIR / entry["file"]
        for entry in manifest
        if entry["level"] in ("verify", "run")
    ]
    return sorted(EXAMPLES_DIR.glob("*.vera")) + sorted(conformance)


def _binary_sites(program: ast.Program) -> list[ast.BinaryExpr]:
    """Every ``+`` / ``-`` / ``*`` BinaryExpr node, in source order."""
    sites: list[ast.BinaryExpr] = []

    def walk(node: object) -> None:
        if isinstance(node, ast.BinaryExpr) and node.op in (
            ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
        ):
            sites.append(node)
        if isinstance(node, ast.Node):
            for v in vars(node).values():
                walk(v)
        elif isinstance(node, (list, tuple)):
            for item in node:
                walk(item)

    walk(program)
    return sites


def _verifier_gated_type(verifier: ContractVerifier, site: ast.BinaryExpr):
    """The type the verifier *obligates* this site at, mirroring the gate in
    ``_walk_for_primitive_op_obligations``: classification is on the operands'
    common (coerced) type (#798 — not one operand's self-type, which a literal
    skews, nor the narrowed result), and ``@Nat`` SUB is excluded (nat_sub)."""
    ovf = verifier._overflow_arith_type(site)
    if ovf is None:
        return None
    if site.op == ast.BinOp.SUB and ovf == "Nat":
        return None
    return ovf


def _codegen_gated_type(ctx: WasmContext, site: ast.BinaryExpr):
    """The type the codegen guard fires at, mirroring the gate in
    ``_translate_binary`` — the operands' common (coerced) type (#798)."""
    ovf = ctx._overflow_arith_codegen_type(site)
    if ovf is None:
        return None
    if site.op == ast.BinOp.SUB and ovf == "Nat":
        return None
    return ovf


def _assert_in_lockstep(source: str) -> None:
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source)
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"typecheck errors: {[d.description for d in errors]}"

    verifier = ContractVerifier(
        source=source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    ctx = WasmContext(StringPool())
    ctx.set_expr_semantic_types(arts.expr_semantic_types)

    sites = _binary_sites(program)
    assert sites, "corpus program has no +/-/* sites"
    mismatches = []
    for site in sites:
        v = _verifier_gated_type(verifier, site)
        c = _codegen_gated_type(ctx, site)
        if v != c:
            key = ast.span_key(site)
            mismatches.append((key, site.op.name, v, c))
    assert not mismatches, (
        "verifier<->codegen overflow classification desync "
        "(span, op, verifier_type, codegen_type): " + repr(mismatches)
    )


# Corpus: all five combos, plus the literal-left ambiguity (RISK 6) in both
# Int and Nat context, plus mixed slot/literal orderings and nested arithmetic.
_CORPUS = {
    "int_add_slots": """
public fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }
""",
    "int_sub_slots": """
public fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 - @Int.0 }
""",
    "int_mul_slots": """
public fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 * @Int.0 }
""",
    "nat_add_slots": """
public fn f(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.1 + @Nat.0 }
""",
    "nat_mul_slots": """
public fn f(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.1 * @Nat.0 }
""",
    "nat_sub_excluded": """
public fn f(@Nat, @Nat -> @Nat)
  requires(@Nat.1 >= @Nat.0) ensures(true) effects(pure)
{ @Nat.1 - @Nat.0 }
""",
    # RISK 6: a literal LEFT operand whose resolved type is Int.  The AST-only
    # classifier would call `5` (a non-negative IntLit) @Nat → wrong (u64)
    # range; the resolved-type lookup must keep it @Int in both sides.
    "int_literal_left_add": """
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 + @Int.0 }
""",
    "int_literal_left_sub": """
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 - @Int.0 }
""",
    "int_literal_left_mul": """
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 * @Int.0 }
""",
    # The same literal-left shape but in @Nat context — must stay @Nat.
    "nat_literal_left_add": """
public fn f(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 5 + @Nat.0 }
""",
    "nat_literal_left_mul": """
public fn f(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 5 * @Nat.0 }
""",
    # Nested arithmetic — every subexpression site must match.
    "int_nested": """
public fn f(@Int, @Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.2 * @Int.1 + @Int.0 - 7 }
""",
    "nat_nested": """
public fn f(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.1 * @Nat.0 + 3 }
""",
    # Float arithmetic must be classified None on both sides (not guarded).
    "float_not_guarded": """
public fn f(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ @Float64.1 + @Float64.0 }
""",
}


class TestVerifierCodegenOverflowDifferential798:
    @pytest.mark.parametrize("name", sorted(_CORPUS))
    def test_classification_in_lockstep(self, name: str) -> None:
        _assert_in_lockstep(_CORPUS[name])

    def test_literal_left_classified_identically_to_verifier(self) -> None:
        """The RISK-6 case: a positive-literal LEFT operand.

        The checker records a non-negative literal's own narrow type as ``@Nat``
        (``5`` alone is ``@Nat``), but ``5 + @Int.0`` as a *whole* is ``@Int``.
        Both the verifier and codegen classify on the WHOLE expression's
        resolved type (#798), so both read ``@Int`` (i64) here — in lockstep and
        at the correct range.  Reading the operand's type instead would classify
        ``@Nat`` and mis-range the site to u64.
        """
        source = _CORPUS["int_literal_left_add"]
        program = parse_to_ast(source)
        diags, arts = typecheck_with_artifacts(program, source)
        assert not [d for d in diags if d.severity == "error"]
        verifier = ContractVerifier(
            source=source,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        ctx = WasmContext(StringPool())
        ctx.set_expr_semantic_types(arts.expr_semantic_types)
        site = _binary_sites(program)[0]
        assert isinstance(site.left, ast.IntLit) and site.left.value == 5
        v = verifier._overflow_arith_type(site)
        c = ctx._overflow_arith_codegen_type(site)
        assert v == c == "Int", (
            f"literal-left classification: verifier={v}, codegen={c} (want Int)"
        )

    def test_literal_left_int_overflow_is_caught(self) -> None:
        """A literal-LEFT ``@Int`` overflow is caught — the #798 fix.

        The checker synthesises a non-negative literal's type as ``@Nat``, so an
        *operand*-type read of ``5 + @Int.0`` would classify ``@Nat`` and
        obligate the site at u64 — silently dropping an ``@Int`` overflow at
        ``[I64_MAX+1, U64_MAX]``.  Classifying on the whole expression's resolved
        type (``@Int``) closes that gap: the site is obligated, and codegen
        guards it, at the i64 range.  (Lockstep is pinned by
        ``test_literal_left_classified_identically_to_verifier``;
        ``test_int_overflow_codegen.py::TestLiteralLeftIntOverflow798`` checks
        it end-to-end at runtime.)
        """
        source = _CORPUS["int_literal_left_add"]
        program = parse_to_ast(source)
        diags, arts = typecheck_with_artifacts(program, source)
        assert not [d for d in diags if d.severity == "error"]
        verifier = ContractVerifier(
            source=source,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        site = _binary_sites(program)[0]
        # The fix: classify on the operands' common type → @Int (i64), not the
        # literal left operand's @Nat self-type.
        assert verifier._overflow_arith_type(site) == "Int"

    def test_narrowed_result_classified_at_i64_not_result_type(self) -> None:
        """An @Int add narrowed into a @Nat slot is i64 arithmetic (#798).

        ``@Int.0 + 1`` stored as @Nat resolves the *expression* to @Nat, but the
        addition runs at i64 (both operands @Int) — classifying on the result
        would mis-range it to u64 and drop an i64 overflow.  The operands' common
        type (@Int) is the correct width.  This pins the shape a result-type
        classifier silently gets wrong.
        """
        source = """
public fn f(@Int -> @Nat)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ @Int.0 + 1 }
"""
        program = parse_to_ast(source)
        diags, arts = typecheck_with_artifacts(program, source)
        assert not [d for d in diags if d.severity == "error"]
        verifier = ContractVerifier(
            source=source,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        site = _binary_sites(program)[0]
        # Result resolves to @Nat (narrowed); the *arithmetic* width is @Int.
        assert verifier._overflow_int_type(site) == "Nat"     # the result type
        assert verifier._overflow_arith_type(site) == "Int"   # the i64 width


class TestCorpusOverflowDifferential798:
    """Corpus-wide RISK-7 sweep: across every example + verify/run conformance
    program, the verifier's gated ``int_overflow`` classification must equal
    the codegen guard's at every ``+`` / ``-`` / ``*`` site.

    The hand-written ``_CORPUS`` above pins the tricky shapes; this sweep is
    the broad safety net — a desync anywhere in real Vera code (a slot, a call
    return, a nested arithmetic tree, an aliased type) fails here.
    """

    @pytest.mark.parametrize(
        "path", _corpus_files(), ids=lambda p: p.name.removesuffix(".vera"),
    )
    def test_corpus_classification_in_lockstep(self, path: Path) -> None:
        source = path.read_text(encoding="utf-8")
        program = parse_to_ast(source)
        diags, arts = typecheck_with_artifacts(
            program, source, file=str(path),
        )
        if [d for d in diags if d.severity == "error"]:
            pytest.skip(f"{path.name}: not standalone-typecheckable")

        verifier = ContractVerifier(
            source=source,
            file=str(path),
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        ctx = WasmContext(StringPool())
        ctx.set_expr_semantic_types(arts.expr_semantic_types)

        mismatches = []
        for site in _binary_sites(program):
            v = _verifier_gated_type(verifier, site)
            c = _codegen_gated_type(ctx, site)
            if v != c:
                mismatches.append((ast.span_key(site), site.op.name, v, c))
        assert not mismatches, (
            f"{path.name}: verifier<->codegen overflow classification desync "
            f"(span, op, verifier, codegen): {mismatches}"
        )
