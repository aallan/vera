"""Synthetic-AST tests for the defensive `isinstance` branches
added by #597 to compiler walker functions.

These branches are unreachable via end-to-end programs today —
every flow is masked by an upstream guard (type checker
rejection, `[E602]` codegen-skip, etc.).  Without these tests,
a future refactor that breaks a defensive branch would land
silently (no production path exercises them).

Strategy: construct synthetic AST nodes directly and invoke the
walker, asserting the defensive branch produces the correct
result.  Pins each branch's behaviour against future regression.

The 11 defensive branches:

- ``_scan_io_ops`` (compilability.py): IndexExpr, ArrayLit,
  InterpolatedString, AnonFn → recurses into sub-exprs.  The walk
  registers no import (each emitter registers the ones it calls,
  #735), so these positions are pinned on compiled programs: a host
  call in each declares its import.
- ``_scan_expr_for_handlers`` (compilability.py): QualifiedCall,
  IndexExpr, ArrayLit, InterpolatedString, AnonFn → recurses
  into sub-exprs to find HandleExpr nodes.
- ``_infer_expr_wasm_type`` (inference.py): AnonFn → "i32",
  ModuleCall → None.
- ``_infer_vera_type`` (inference.py): Block / MatchExpr /
  HandleExpr / AssertExpr / AssumeExpr / AnonFn / QualifiedCall /
  ModuleCall.

The file also carries the FIELD-coverage gate for the two
``compilability.py`` pre-scans (``TestPreScanWalkerFieldCoverage``,
#1210 round 5).  ``scripts/check_walker_coverage.py`` already audits
every walker carrying a ``# WALKER_COVERAGE:`` marker, but its
canonical set is the ``Expr`` subclasses and its verdict is
"the class is NAMED" — a class named in the checklist with an
"intentionally ignored" disposition counts as covered whether or
not it carries live sub-expressions.  Both of round 5's holes slipped
through exactly there: ``LetDestruct`` is a ``Stmt``, invisible to
that canonical set, and ``ModuleCall`` was named with a disposition
that was true of the callee and false of its arguments.  The gate
below closes both, and is a test rather than an extension of the
script because the script's set would then force a ``Stmt``
disposition onto all thirteen marked walkers.
"""

from __future__ import annotations

import ast as pyast
import dataclasses
import importlib.util
import inspect
import re
import sys
import typing
from pathlib import Path

import pytest

from vera import ast
from vera.codegen import compilability
from vera.codegen.core import CodeGenerator
from vera.wasm.context import WasmContext
from vera.wasm.helpers import CellNames
from vera.wasm.helpers import StringPool


# =====================================================================
# Helpers
# =====================================================================


def _make_cg() -> CodeGenerator:
    """Build a fresh CodeGenerator for compilability scans."""
    return CodeGenerator()


def _make_ctx() -> WasmContext:
    """Build a fresh WasmContext for inference helpers."""
    return WasmContext(string_pool=StringPool())


# =====================================================================
# `_scan_io_ops` defensive branches (#597)
# =====================================================================


def _declared_imports(body: str, formals: str, ret: str, effect: str,
                      decls: str = "") -> set[str]:
    """The host imports a module declares whose `main` has *body*."""
    from tests import pipeline

    source = (f"{decls}public fn main({formals} -> @{ret})\n"
              f"  requires(true)\n  ensures(true)\n  {effect}\n{{\n  {body}\n}}\n")
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    assert "main" in compiled.exports
    return set(re.findall(r'^\s*\(import "vera" "([^"]+)" ', compiled.wat, re.MULTILINE))


class TestScanIoOpsDefensiveBranches:
    """A host call in each of these positions declares its import.  The
    pre-scan's branches walk them and register nothing: the emitter that
    lowers the call registers the import it calls (#735), so what pins each
    position is the compiled module's declaration."""

    def test_indexexpr_collection_recursion(self) -> None:
        # An IO call's array indexed directly is dropped (E602), so the
        # collection is a host built-in's.
        assert "map_keys$ks" in _declared_imports(
            "map_keys(@Map<String, Int>.0)[0]", "@Map<String, Int>", "String",
            "effects(pure)")

    def test_indexexpr_index_recursion(self) -> None:
        assert "time" in _declared_imports(
            "@Array<Int>.0[nat_to_int(IO.time(()))]", "@Array<Int>", "Int",
            "effects(<IO>)")

    def test_arraylit_elements_recursion(self) -> None:
        assert "read_line" in _declared_imports(
            "[IO.read_line(())]", "", "Array<String>", "effects(<IO>)")

    def test_interpolated_string_parts_recursion(self) -> None:
        # The literal fragments are bare `str`, the interpolated part an
        # expression.
        assert "read_line" in _declared_imports(
            'IO.print("prefix: \\(IO.read_line(())) suffix")', "", "Unit",
            "effects(<IO>)")

    def test_anonfn_body_recursion(self) -> None:
        # A lifted closure's body: its own context registers the import,
        # merged into the module's when the closure is lifted.
        decls = (
            "type Reader = fn(Unit -> String) effects(<IO>);\n\n"
            "private fn run(@Reader -> @String)\n  requires(true)\n"
            "  ensures(true)\n  effects(<IO>)\n{\n  apply_fn(@Reader.0, ())\n}\n\n")
        assert "read_line" in _declared_imports(
            "run(fn(@Unit -> @String) effects(<IO>) { IO.read_line(()) })", "", "String",
            "effects(<IO>)", decls)


# =====================================================================
# `_scan_expr_for_handlers` defensive branches (#597)
# =====================================================================


def _handle_expr() -> ast.HandleExpr:
    """Build a minimal HandleExpr for State<Int>."""
    return ast.HandleExpr(
        effect=ast.EffectRef(
            name="State",
            type_args=(ast.NamedType(name="Int", type_args=None),)),
        state=None,
        clauses=(),
        body=ast.Block(statements=(), expr=ast.UnitLit()),
    )


class TestScanExprForHandlersDefensiveBranches:
    """Each branch recurses into a sub-expression position so
    HandleExprs buried inside are still discovered for type
    registration."""

    def test_qualifiedcall_args_recursion(self) -> None:
        cg = _make_cg()
        node = ast.QualifiedCall(
            qualifier="IO", name="print", args=(_handle_expr(),))
        cg._scan_expr_for_handlers(node)
        # State<Int> registered
        assert (CellNames(family="Int", base="Int"), "i64") in cg._state_types

    def test_indexexpr_recursion(self) -> None:
        cg = _make_cg()
        node = ast.IndexExpr(
            collection=_handle_expr(), index=ast.IntLit(value=0))
        cg._scan_expr_for_handlers(node)
        assert (CellNames(family="Int", base="Int"), "i64") in cg._state_types

    def test_arraylit_recursion(self) -> None:
        cg = _make_cg()
        node = ast.ArrayLit(elements=(_handle_expr(),))
        cg._scan_expr_for_handlers(node)
        assert (CellNames(family="Int", base="Int"), "i64") in cg._state_types

    def test_interpolated_string_recursion(self) -> None:
        cg = _make_cg()
        node = ast.InterpolatedString(parts=("x: ", _handle_expr()))
        cg._scan_expr_for_handlers(node)
        assert (CellNames(family="Int", base="Int"), "i64") in cg._state_types

    def test_anonfn_body_recursion(self) -> None:
        cg = _make_cg()
        body = ast.Block(statements=(), expr=_handle_expr())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        cg._scan_expr_for_handlers(node)
        assert (CellNames(family="Int", base="Int"), "i64") in cg._state_types


# =====================================================================
# `_infer_expr_wasm_type` defensive branches (#597)
# =====================================================================


class TestInferExprWasmTypeDefensiveBranches:
    """AnonFn → "i32" (closure handle), ModuleCall → None (path
    field can't be threaded through bare-name FnCall dispatch)."""

    def test_anonfn_returns_i32(self) -> None:
        ctx = _make_ctx()
        body = ast.Block(statements=(), expr=ast.UnitLit())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        assert ctx._infer_expr_wasm_type(node) == "i32"

    def test_modulecall_returns_none(self) -> None:
        """ModuleCall carries `expr.path` that the bare-name FnCall
        dispatcher can't consume.  Returning None surfaces the
        unknown-type cleanly rather than masking with a wrong same-
        name lookup."""
        ctx = _make_ctx()
        node = ast.ModuleCall(
            path=("some_module",), name="some_fn", args=())
        assert ctx._infer_expr_wasm_type(node) is None


# =====================================================================
# `_infer_vera_type` defensive branches (#597)
# =====================================================================


class TestInferVeraTypeDefensiveBranches:
    """Block / MatchExpr / HandleExpr → trailing-expr type;
    AssertExpr / AssumeExpr → "Unit"; AnonFn / QualifiedCall /
    ModuleCall → None (path/qualifier fields can't be threaded
    through the bare-name FnCall dispatcher).

    Since #1286 the `MatchExpr` arm joins over the arms rather than
    reading `arms[0]` — it answers from the first arm that YIELDS a
    name, an arm that only throws naming none.  The single-arm cases
    below are unaffected by that distinction; the join itself is pinned
    in `test_infer_vera_type_join_1286.py`.
    """

    def test_block_returns_trailing_expr_type(self) -> None:
        ctx = _make_ctx()
        node = ast.Block(statements=(), expr=ast.IntLit(value=42))
        assert ctx._infer_vera_type(node) == "Int"

    def test_matchexpr_returns_first_arm_body_type(self) -> None:
        ctx = _make_ctx()
        arm = ast.MatchArm(
            pattern=ast.WildcardPattern(),
            body=ast.BoolLit(value=True),
        )
        node = ast.MatchExpr(
            scrutinee=ast.IntLit(value=0), arms=(arm,))
        assert ctx._infer_vera_type(node) == "Bool"

    def test_matchexpr_no_arms_returns_none(self) -> None:
        ctx = _make_ctx()
        node = ast.MatchExpr(
            scrutinee=ast.IntLit(value=0), arms=())
        assert ctx._infer_vera_type(node) is None

    def test_handleexpr_returns_body_expr_type(self) -> None:
        ctx = _make_ctx()
        node = ast.HandleExpr(
            effect=ast.EffectRef(name="State", type_args=()),
            state=None,
            clauses=(),
            body=ast.Block(statements=(), expr=ast.FloatLit(value=1.5)),
        )
        assert ctx._infer_vera_type(node) == "Float64"

    def test_assertexpr_returns_unit(self) -> None:
        ctx = _make_ctx()
        node = ast.AssertExpr(expr=ast.BoolLit(value=True))
        assert ctx._infer_vera_type(node) == "Unit"

    def test_assumeexpr_returns_unit(self) -> None:
        ctx = _make_ctx()
        node = ast.AssumeExpr(expr=ast.BoolLit(value=True))
        assert ctx._infer_vera_type(node) == "Unit"

    def test_anonfn_returns_none(self) -> None:
        """Closure handle has no simple Vera-type name suitable
        for call rewriting; None lets callers handle the unknown
        case explicitly (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        body = ast.Block(statements=(), expr=ast.UnitLit())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        assert ctx._infer_vera_type(node) is None

    def test_qualifiedcall_returns_none(self) -> None:
        """`qualifier` can't be threaded through bare-name FnCall
        dispatch (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        node = ast.QualifiedCall(
            qualifier="IO", name="read_line", args=(ast.UnitLit(),))
        assert ctx._infer_vera_type(node) is None

    def test_modulecall_returns_none(self) -> None:
        """`path` can't be threaded through bare-name FnCall
        dispatch (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        node = ast.ModuleCall(
            path=("some_module",), name="some_fn", args=())
        assert ctx._infer_vera_type(node) is None


# =====================================================================
# Pre-scan walker FIELD coverage (#1210 round 5)
# =====================================================================

_SCRIPT_PATH = (
    Path(__file__).resolve().parent.parent
    / "scripts" / "check_walker_coverage.py"
)

# A field is "descendable" when its declared type can carry an expression the
# walkers must reach.  Matched on the RESOLVED annotation text, so
# `tuple[Expr, ...]`, `Expr | None` and `tuple[TypeExpr, Expr] | None` all
# count while `tuple[str, ...]` and `Span | None` do not.
_DESCENDABLE = ("Expr", "Block", "AnonFn", "Stmt")

# The two pre-scans under audit.  Both are in `vera/codegen/compilability.py`
# and both carry a `# WALKER_COVERAGE:` checklist.
_PRE_SCANS = ("_scan_io_ops", "_scan_expr_for_handlers")

# Descendable fields that are deliberately NOT reached by the recursion.  One
# line each, saying where the field IS reached — an entry whose reason is "we
# do not need it" is the shape that produced both round-5 holes, so each of
# these names a concrete other route.
#
# Keyed EITHER by class name (one reason covering the class, permitted only
# while the class has a single descendable field — see
# `test_the_ignore_table_cannot_rot`) or by an exact `(class, field)` pair.
# A class-level entry on a multi-field class would exempt whatever field the
# class grows next, which is precisely the class-keyed obligation this gate
# replaced (round-9 review); `HandlerClause` is the class that has two, so it
# is written per pair, each naming its own read.
_JUSTIFIED_IGNORES: dict[str | tuple[str, str], str] = {
    "FnDecl":
        "`decl.body` IS the entry point — `emit_function` hands it to both "
        "pre-scans; the recursion never meets a FnDecl.",
    "Requires":
        "contract predicate — enumerated by `contract_exprs()` at the entry "
        "point (#1210 round 2), not by the recursion.",
    "Ensures":
        "contract predicate — enumerated by `contract_exprs()` at the entry "
        "point (#1210 round 2), not by the recursion.",
    "Decreases":
        "contract predicate — enumerated by `contract_exprs()` at the entry "
        "point; carries `exprs`, which is why that helper exists.",
    "Invariant":
        "contract predicate — enumerated by `contract_exprs()` at the entry "
        "point, same as the other three clause kinds.",
    "RefinementType":
        "signature refinement predicate — enumerated by "
        "`_signature_refinement_predicates()` (#1210 rounds 5 and 7), the "
        "ONE derivation of what the boundary-guard emitters lower, covering "
        "all four of their routes: a param's or a return's own refinement, "
        "a tuple component's (both consume `_tuple_component_guard_sites`), "
        "and a closure signature's (off the AnonFn branch, via "
        "`_scan_anon_fn_signature`).  Reached through the alias table, so no "
        "structural walk can find it.",
    "HandlerState":
        "reached through the HandleExpr branch, which walks "
        "`node.state.init_expr`.",
    ("HandlerClause", "body"):
        "reached through the HandleExpr branch, which walks `clause.body` "
        "for every clause.",
    ("HandlerClause", "state_update"):
        "reached through the HandleExpr branch, which walks "
        "`clause.state_update[1]` for every clause.",
    "MatchArm":
        "reached through the MatchExpr branch, which walks every "
        "`arm.body`.",
    "DataDecl":
        "a data-type `invariant(...)` is verifier-only — no code in "
        "`vera/codegen/` or `vera/wasm/` reads `DataDecl.invariant`, so "
        "nothing written in one is lowered.",
}


def _descendable_fields(cls: type) -> list[str]:
    """Field names of *cls* whose type can carry a walkable expression."""
    if not dataclasses.is_dataclass(cls):
        return []
    hints = typing.get_type_hints(cls, vars(ast))
    out = []
    for f in dataclasses.fields(cls):
        text = str(hints.get(f.name, f.type)).replace("vera.ast.", "")
        if any(re.search(rf"\b{d}\b", text) for d in _DESCENDABLE):
            out.append(f.name)
    return out


def _is_justified(cls: str, field: str) -> bool:
    """True when this exact obligation is exempted in `_JUSTIFIED_IGNORES`."""
    return cls in _JUSTIFIED_IGNORES or (cls, field) in _JUSTIFIED_IGNORES


def _pair_holes(
    canonical: dict[str, list[str]], dispatched: set[str], reads: set[str],
) -> list[str]:
    """The obligations a walker satisfies neither by route nor by exemption.

    The obligation is a `(class, field)` PAIR, and a pair is discharged only
    by the conjunction — the class has an `isinstance` branch AND the field
    name is read in that branch — or by an entry in `_JUSTIFIED_IGNORES`.
    ONE computation, called by the gate and by both can-go-red proofs, so the
    mutations exercise the check that runs rather than a restatement of it.
    """
    return sorted(
        f"{cls}.{field}"
        for cls, fields in canonical.items()
        for field in fields
        if not _is_justified(cls, field)
        and not (cls in dispatched and field in reads)
    )


def _canonical_classes() -> dict[str, list[str]]:
    """Every `vera.ast` node class carrying at least one descendable field.

    Derived from the dataclass schema, not from a hand-kept list, so a new
    AST class — or a new expression-carrying field on an existing one —
    enters the canonical set the moment it is declared.
    """
    out: dict[str, list[str]] = {}
    for name in sorted(dir(ast)):
        cls = getattr(ast, name)
        if not (inspect.isclass(cls) and issubclass(cls, ast.Node)):
            continue
        fields = _descendable_fields(cls)
        if fields:
            out[name] = fields
    return out


@pytest.fixture(scope="module")
def coverage_script() -> object:
    """`scripts/check_walker_coverage.py` imported as a module.

    Its extractors are reused rather than re-implemented so the two
    instruments cannot disagree about what a walker "names".
    """
    spec = importlib.util.spec_from_file_location(
        "check_walker_coverage_for_prescans", _SCRIPT_PATH)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    sys.modules["check_walker_coverage_for_prescans"] = mod
    spec.loader.exec_module(mod)
    return mod


def _attribute_reads(fn_node: pyast.AST) -> set[str]:
    """Every attribute NAME read anywhere in a walker function.

    `node.state.init_expr`, `clause.body`, `stmt.value` — the receivers are
    untyped locals, so this is a name set, not a per-class one.  That is the
    limit of the field gate below and is stated on it.
    """
    return {
        n.attr for n in pyast.walk(fn_node) if isinstance(n, pyast.Attribute)
    }


@pytest.fixture(scope="module")
def pre_scan_walkers(
    coverage_script: object,
) -> dict[str, tuple[set, set, set]]:
    """`{walker: (isinstance-dispatched, checklist-named, fields-read)}`."""
    path = Path(inspect.getfile(compilability))
    found = coverage_script.find_walker_functions(path)  # type: ignore[attr-defined]
    by_name = {node.name: (node, src) for node, src in found}
    missing = set(_PRE_SCANS) - set(by_name)
    assert not missing, (
        f"{sorted(missing)} no longer carry a `# WALKER_COVERAGE:` marker in "
        f"{path.name} — either the marker was dropped (restore it: "
        "scripts/check_walker_coverage.py audits by marker) or the walker "
        "was renamed and this gate must follow it"
    )
    return {
        name: (
            coverage_script.extract_isinstance_classes(by_name[name][0]),  # type: ignore[attr-defined]
            coverage_script.extract_checklist_classes(by_name[name][1]),  # type: ignore[attr-defined]
            _attribute_reads(by_name[name][0]),
        )
        for name in _PRE_SCANS
    }


class TestPreScanWalkerFieldCoverage:
    """Every expression-carrying AST FIELD is walked, or justified here.

    The corpus-anchored differential in
    `tests/test_state_exn_registration.py` can only see a hole a corpus
    program contains; round 5's two holes had no corpus instance, so they
    survived a green suite for as long as nobody wrote the shape.  This gate
    is schema-driven instead: it reads the dataclass fields of `vera/ast.py`,
    so a new class — or a new expression-carrying field on a class the
    walkers already dispatch on — is a loud failure at the commit that adds
    it, whether or not anyone writes a program using it.

    ONE obligation, at FIELD granularity: every `(class, field)` pair the
    schema yields must have a dispatch route — the class `isinstance`-branched
    AND the field name read inside that branch — or an entry in
    `_JUSTIFIED_IGNORES` naming the route its expressions ARE reached by.
    The two halves are a conjunction on one obligation rather than two checks
    over two obligation sets, because a class-keyed obligation set discharges
    the moment a class has ANY branch (round-9 review): adding
    `IfExpr.finally_branch` and not walking it left the class dispatched, the
    class obligation satisfied, and only a second, weaker screen standing
    between a live sub-expression and going unregistered.

    The dispatch route reads a field NAME, because a walker reads
    `node.body` / `clause.body` off untyped locals and cannot be attributed
    to a class without typing the receivers.  The OBLIGATION is per pair
    regardless, so a new field is only ever discharged by a name the walker
    genuinely reads; a new field reusing a name some other branch already
    reads (`body`, `expr`, `value`, `args`) is the residual, and narrowing
    that would mean type-inferring the walkers' locals.  The corpus
    differential covers the rest.

    Deliberately STRONGER than `scripts/check_walker_coverage.py`: a
    checklist disposition alone does not count as coverage here, only an
    actual `isinstance` branch or an entry in `_JUSTIFIED_IGNORES`.  That is
    the exact distinction `ModuleCall` was hiding behind — named in both
    checklists as "tracked by the imported module's own scan", which was true
    of the callee and false of the arguments the walkers never reached.
    """

    def test_every_expression_carrying_field_is_walked_or_justified(
        self, pre_scan_walkers: dict[str, tuple[set, set, set]],
    ) -> None:
        canonical = _canonical_classes()
        pairs = sum(len(fields) for fields in canonical.values())
        assert len(canonical) > 20 and pairs > len(canonical), (
            f"the schema scan yields {pairs} field obligations over "
            f"{len(canonical)} AST classes — it has stopped matching (or "
            "stopped distinguishing fields from classes), and this gate "
            "would pass vacuously"
        )
        for walker, (dispatched, _checklist, reads) in (
                pre_scan_walkers.items()):
            holes = _pair_holes(canonical, dispatched, reads)
            assert not holes, (
                f"`{walker}` never reaches " + ", ".join(holes)
                + " — walk the field in an `isinstance` branch for its class, "
                "or add the pair to `_JUSTIFIED_IGNORES` with the route it IS "
                "reached by.  A field carrying live sub-expressions that no "
                "pass walks is the #1210 bug: the registration pass misses "
                "it while the lowering emits its calls anyway."
            )

    def test_the_ignore_table_cannot_rot(self) -> None:
        """Every justified entry still names something that exists.

        Without this, a class removed from `vera/ast.py` (or one that loses
        the field an entry exempts) leaves a stale exemption behind that
        would silently cover a LATER class or field of the same name.

        It also holds the line between the two key shapes: a class-level
        entry exempts whatever fields its class GROWS, so it is permitted
        only while the class has exactly one — the moment a second appears,
        the entry must be split into per-field ones that each name a route.
        That is the same class-keyed-obligation hole the gate itself closed,
        one table down.
        """
        canonical = _canonical_classes()
        for key, reason in _JUSTIFIED_IGNORES.items():
            if isinstance(key, str):
                assert key in canonical, (
                    f"`{key}` is exempted in `_JUSTIFIED_IGNORES` but no "
                    "longer carries any expression-carrying field — delete "
                    "the entry"
                )
                assert len(canonical[key]) == 1, (
                    f"`{key}` now carries {canonical[key]} — a class-level "
                    "exemption would cover whichever field it grows next.  "
                    "Split it into one `(class, field)` entry per field, each "
                    "naming its own route."
                )
            else:
                cls, field = key
                assert cls in canonical and field in canonical[cls], (
                    f"`{cls}.{field}` is exempted in `_JUSTIFIED_IGNORES` but "
                    f"is not in the schema — delete the entry (`{cls}` "
                    f"carries {canonical.get(cls)})"
                )
                assert cls not in _JUSTIFIED_IGNORES, (
                    f"`{cls}` has both a class-level and a per-field "
                    "exemption — the class-level one already covers every "
                    "field, so the pair entry's reason is never read"
                )
            assert len(reason) > 30 and reason.rstrip().endswith("."), (
                f"the `{key}` exemption needs a reason naming where its "
                f"expressions ARE reached, got: {reason!r}"
            )

    def test_the_gate_can_go_red_on_an_unwalked_field(
        self, pre_scan_walkers: dict[str, tuple[set, set, set]],
    ) -> None:
        """A fabricated field on a DISPATCHED class must be reported.

        The mutation the field granularity exists to catch, run through
        `_pair_holes` — the gate's own computation, not a restatement of it.
        No walker reads `fake_extra`, so pretending `IfExpr` declares one
        must produce exactly that hole even though `IfExpr` keeps its branch.
        Under the class-keyed obligation this shape was invisible: the class
        was dispatched, so the obligation discharged.
        """
        canonical = dict(_canonical_classes())
        assert "IfExpr" in canonical, "the fixture class must still exist"
        canonical["IfExpr"] = [*canonical["IfExpr"], "fake_extra"]
        for walker, (dispatched, _checklist, reads) in (
                pre_scan_walkers.items()):
            assert "IfExpr" in dispatched, walker
            assert _pair_holes(canonical, dispatched, reads) == [
                "IfExpr.fake_extra"], walker

    def test_the_checklist_comments_stay_truthful(
        self, pre_scan_walkers: dict[str, tuple[set, set, set]],
    ) -> None:
        """Every dispatched class is documented in the walker's checklist.

        `scripts/check_walker_coverage.py` accepts EITHER the branch or the
        comment; this asserts the comment keeps up with the branches, so a
        reader of the checklist sees the walk that actually happens.  It is
        what would have caught `ModuleCall`'s stale "intentionally ignored"
        line the moment its branch landed.
        """
        canonical = _canonical_classes()
        for walker, (dispatched, checklist, _reads) in (
                pre_scan_walkers.items()):
            undocumented = sorted(
                (dispatched & set(canonical)) - checklist)
            assert not undocumented, (
                f"`{walker}` dispatches on {undocumented} but its "
                "`# WALKER_COVERAGE:` checklist does not mention them — the "
                "comment is the thing reviewers read"
            )

    def test_the_gate_can_go_red_on_an_undispatched_class(
        self, pre_scan_walkers: dict[str, tuple[set, set, set]],
    ) -> None:
        """Drop a real branch from the dispatched set and the gate must fire.

        Proves the comparison is doing work: `LetDestruct` and `ModuleCall` —
        the two classes round 5 added — must be reported the moment they are
        not among the dispatched classes, by their FIELDS, since that is what
        the obligation is keyed on now.  Without this, an extraction that
        silently returned every class name would leave the gate green
        forever.  Run through `_pair_holes` for the same reason the field
        mutation is.
        """
        canonical = _canonical_classes()
        dropped = {"LetDestruct", "ModuleCall"}
        assert dropped <= set(canonical), (
            "the two round-5 classes must still carry descendable fields"
        )
        expected = sorted(
            f"{cls}.{field}" for cls in dropped for field in canonical[cls])
        for walker, (dispatched, _checklist, reads) in (
                pre_scan_walkers.items()):
            assert dropped <= dispatched, walker
            assert _pair_holes(
                canonical, dispatched - dropped, reads) == expected, walker


# =====================================================================
# ONE boundary-guard derivation, consumed by both sides (#1210 round 7)
# =====================================================================


def _self_calls(path: Path, fn: str) -> set[str]:
    """Method names *fn* calls on `self`, anywhere in its body."""
    tree = pyast.parse(path.read_text(encoding="utf-8"))
    for node in pyast.walk(tree):
        if isinstance(node, pyast.FunctionDef) and node.name == fn:
            return {
                c.func.attr
                for c in pyast.walk(node)
                if isinstance(c, pyast.Call)
                and isinstance(c.func, pyast.Attribute)
                and isinstance(c.func.value, pyast.Name)
                and c.func.value.id == "self"
            }
    raise AssertionError(f"{fn} not found in {path.name} — has it moved?")


_CONTRACTS = Path(inspect.getfile(compilability)).parent / "contracts.py"
_COMPILABILITY = Path(inspect.getfile(compilability))


class TestBoundaryGuardDerivationIsShared:
    """The pre-scan reads the emitters' own decomposition, not a copy of it.

    Round 5 registered a named function's params and return by RE-DERIVING
    the emitter's two bails ("mirror `_refinement_guard_parts` exactly" was
    the comment).  It was a faithful copy of one route and unaware of three
    others — tuple components on the way in, tuple components on the way out,
    and closure signatures — each of which lowered predicates nothing
    registered, and each of which was a check-green program that died at
    whole-module WAT with `unknown func $vera.state_push_Nat`.

    A behavioural test can only pin the shapes someone thought to write; the
    reason round 5's fix was incomplete is that three shapes went unwritten.
    So this asserts the STRUCTURE that makes the classes converge: exactly
    one function classifies, and every consumer calls it.  Divergence now
    requires editing that function — or deleting an edge here.
    """

    def test_every_consumer_reads_the_one_decomposition(self) -> None:
        for consumer in (
            "_emit_component_refinement_guards",   # the emitter
            "_has_guardable_tuple_components",     # the epilogue gate
            "_component_guard_predicates",         # the pre-scan's enumeration
        ):
            calls = _self_calls(_CONTRACTS, consumer)
            assert "_tuple_component_guard_sites" in calls, (
                f"`{consumer}` no longer reads the shared tuple "
                "decomposition — it is classifying components itself again, "
                f"which is the round-5 shape.  Calls: {sorted(calls)}"
            )

    def test_no_consumer_reclassifies_behind_the_decomposition(self) -> None:
        """The negative half: a consumer that re-derives has diverged.

        `_refinement_guard_parts` / `_resolve_tuple_type` / `_resolve_type_
        alias` are how a component is classified.  Called from a consumer
        rather than from `_tuple_component_guard_sites`, they are a second
        opinion — and a second opinion is what the pre-scan and the emitter
        having was.
        """
        for consumer in (
            "_emit_component_refinement_guards",
            "_has_guardable_tuple_components",
            "_component_guard_predicates",
        ):
            calls = _self_calls(_CONTRACTS, consumer)
            reclassified = calls & {
                "_refinement_guard_parts",
                "_resolve_tuple_type",
                "_resolve_type_alias",
            }
            assert not reclassified, (
                f"`{consumer}` classifies components with "
                f"{sorted(reclassified)} instead of reading "
                "`_tuple_component_guard_sites` — put the decision in the "
                "decomposition, where all three consumers see it"
            )

    def test_the_pre_scan_walks_closure_signatures(self) -> None:
        """Both walkers reach the closure leg, and it reads the derivation."""
        assert "_signature_refinement_predicates" in _self_calls(
            _COMPILABILITY, "_scan_anon_fn_signature")
        for walker in _PRE_SCANS:
            assert "_scan_anon_fn_signature" in _self_calls(
                _COMPILABILITY, walker), (
                f"`{walker}` no longer walks an AnonFn's SIGNATURE — a "
                "refined closure formal / return is guarded in the lifted "
                "body, and nothing else registers what its predicate needs"
            )

    def test_the_named_entry_point_reads_the_same_derivation(self) -> None:
        """The handler walk's entry point enumerates a `FnDecl`'s signature."""
        assert "_signature_refinement_predicates" in _self_calls(
            _COMPILABILITY, "_scan_body_for_state_handlers")

    def test_the_callgraph_probe_can_go_red(self) -> None:
        """The extraction finds real edges, and misses ones that are absent."""
        calls = _self_calls(_CONTRACTS, "_signature_refinement_predicates")
        assert {"_refinement_guard_parts", "_component_guard_predicates"} <= (
            calls), sorted(calls)
        assert "_emit_refinement_check" not in calls, (
            "the derivation must not EMIT anything — it is read by the "
            "import pre-scan, which runs before any instruction is built"
        )
        with pytest.raises(AssertionError):
            _self_calls(_CONTRACTS, "_no_such_method_anywhere")


# =====================================================================
# `contract_exprs` dispatches explicitly (#1210 round 5)
# =====================================================================


class TestContractExprsDispatch:
    """Every contract kind is enumerated, a new one by construction.

    The helper started as `getattr(c, "expr", None)`, which treats an
    unrecognised contract kind as "carries no predicates" — the silent skip it
    was written to fix, since `Decreases` carries `exprs` and was dropped
    exactly that way.  It reads each clause's fields through `vera.fold`, so
    the next new `ast.Contract` subclass has its expressions enumerated
    whatever its fields are called.
    """

    @staticmethod
    def _lit(n: int) -> ast.IntLit:
        return ast.IntLit(value=n)

    def test_single_predicate_kinds_are_yielded(self) -> None:
        contracts = (
            ast.Requires(expr=self._lit(1)),
            ast.Ensures(expr=self._lit(2)),
            ast.Invariant(expr=self._lit(3)),
        )
        assert [e.value for e in compilability.contract_exprs(contracts)] == [
            1, 2, 3]

    def test_decreases_yields_every_measure_component(self) -> None:
        """A lexicographic measure is SEVERAL expressions, in `exprs`."""
        contracts = (ast.Decreases(exprs=(self._lit(7), self._lit(8))),)
        assert [e.value for e in compilability.contract_exprs(contracts)] == [
            7, 8]

    def test_a_new_contract_kind_is_enumerated_by_construction(self) -> None:
        """A new `ast.Contract` subclass yields its expressions, in field
        order, under field names no enumeration was told about.

        Constructed synthetically because every kind that exists today is
        handled — which is the point: this pins what happens to the NEXT one.
        """

        @dataclasses.dataclass(frozen=True)
        class _FutureContract(ast.Contract):
            measure: ast.Expr
            bounds: tuple[ast.Expr, ...]

        future = _FutureContract(
            measure=self._lit(4), bounds=(self._lit(5), self._lit(6)))
        assert [e.value for e in compilability.contract_exprs((future,))] == [
            4, 5, 6]
