"""One obligation table (#1695, ROADMAP Stage 27): every obligation record
and every emitted guard come from one table entry.

The class: every obligation kind at every position the typed program types.
Its mechanism is architectural, three rules deciding one fact, where a
runtime check stands: the verifier records an obligation wherever its walk
reaches and predicts the guard with `guarded=` claims and mirror
predicates, code generation decides each guard inside translation, and the
reconciliation pairs the two afterwards by span.  So a check is claimed
with no guard, guarded with no claim, missed on both sides, or named by a
span the other side does not use.

The pins below are the issue's open lines, the seven #1542 positions, the
#1598 rows, #1642, #1641, #1782, #1602, #1567, #1563, #1725's disclosure and
#1696's m04, each asserting the verdict the table gives; the regression
cells hold the nine lines that do not reproduce where they are.
"""

from __future__ import annotations

import ast as pyast
import inspect
import re
from pathlib import Path

import pytest

from tests import pipeline

ROOT = Path(__file__).resolve().parents[1]

pytestmark = pytest.mark.matrix(
    decides=[
        "vera/obligations/table.py",
        "vera/verifier.py",
        "vera/reconcile.py",
        "vera/wasm/operators.py",
        "vera/wasm/data.py",
        "vera/codegen/contracts.py",
    ],
)

_BUDGET_S = 300


# =====================================================================
# Helpers
# =====================================================================


def _verified(source: str, name: str = "p.vera") -> pipeline.Verified:
    """`vera verify` with the join, in process."""
    return pipeline.verify(source, file=name, budget_s=_BUDGET_S, reconcile=True)


def _records(verified: pipeline.Verified, kind: str) -> list[tuple[str, int, int]]:
    return sorted((o.status, o.line, o.column)
                  for o in verified.result.obligations if o.kind == kind)


def _codes(verified: pipeline.Verified) -> list[str]:
    return [d.error_code or "" for d in verified.diagnostics]


def _run(tmp_path: Path, source: str, fn: str, *args: str) -> pipeline.CliResult:
    p = tmp_path / "r.vera"
    p.write_text(source, encoding="utf-8")
    return pipeline.cli("run", str(p), "--fn", fn, "--", *args, budget_s=_BUDGET_S)


# =====================================================================
# The architectural cell: one table, read by both sides
# =====================================================================


_MIRRORS = (
    "_refined_boundary_codegen_guardable",
    "_refined_bind_site_guarded",
    "_construction_refined_guarded",
    "_call_arg_nat_guarded",
    "_element_guard_emitted",
    "_NAT_CONSTRUCTION_GUARDED_SITES",
)


def _guard_claims(path: Path) -> list[str]:
    """Every keyword argument ending in `guarded` in *path*, with its
    enclosing function (the planning lane's `guarded_claims.py` scan)."""
    tree = pyast.parse(path.read_text(encoding="utf-8"))
    out: list[str] = []
    for fn in pyast.walk(tree):
        if not isinstance(fn, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
            continue
        for node in pyast.walk(fn):
            if isinstance(node, pyast.Call):
                out.extend(f"{fn.name}:{kw.arg}" for kw in node.keywords
                           if kw.arg and kw.arg.endswith("guarded"))
    return out


def test_the_verifier_claims_no_guard() -> None:
    """No `*guarded=` argument in `vera/verifier.py`: the verifier reads
    whether a row is guarded from the row and never predicts it."""
    claims = _guard_claims(ROOT / "vera" / "verifier.py")
    assert claims == [], claims


def test_the_verifier_defines_no_mirror_of_code_generation() -> None:
    text = (ROOT / "vera" / "verifier.py").read_text(encoding="utf-8")
    defined = [name for name in _MIRRORS
               if re.search(rf"^\s*(def |){name}\b", text, re.MULTILINE)]
    assert defined == [], defined


#: What #1836 deleted: the walk that found its own sites and the anchors
#: that keyed its records to rows after the fact, the fallback for a row no
#: record reached, and code generation's roster beside the row.
_DELETED = {
    "vera/verifier.py": ("_walk_for_nat_binding_obligations",
                         "_walk_for_primitive_op_obligations", "_row_record",
                         "_anchored_rows", "_record_anchors", "_value_spanning",
                         "_return_narrows_into_nat", "_nat_return_narrows"),
    "vera/narrowing.py": ("REFINED_BIND_GUARDED_SITES",),
    "vera/wasm/data.py": ("REFINED_BIND_GUARDED_SITES",),
    "vera/wasm/calls_handlers.py": ("REFINED_BIND_GUARDED_SITES",),
}


@pytest.mark.parametrize("module", sorted(_DELETED))
def test_the_row_driven_discharge_keeps_no_walk_fallback_or_roster(
    module: str,
) -> None:
    """Every record is made at a row, by the traversal that reaches it
    (#1836): no name of the deleted machinery is defined or read."""
    text = (ROOT / module).read_text(encoding="utf-8")
    present = [n for n in _DELETED[module] if re.search(rf"\b{n}\b", text)]
    assert present == [], present


def test_a_check_is_recorded_by_its_row() -> None:
    """`WasmContext._record_check` takes the row the check is the runtime
    half of, so an `EmittedCheck` names it."""
    from vera.trap_registry import EmittedCheck
    from vera.wasm.context import WasmContext

    params = inspect.signature(WasmContext._record_check).parameters
    assert "row" in params, list(params)
    assert "row" in EmittedCheck.__dataclass_fields__


def test_the_table_lists_every_kind_of_a_program() -> None:
    """`vera.obligations.table.build` lists, for one program holding every
    kind, one row per site; no kind is listed by the verifier's walk."""
    from vera.obligations.table import build

    source = """\
type Pos = { @Int | @Int.0 > 0 };

private fn pos(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Pos.0
}

public fn f(@Int, @Array<Int>, @Float64, @Nat, @Nat -> @Nat)
  requires(@Int.0 != 0)
  ensures(@Nat.result >= 0)
  decreases(@Nat.1)
  effects(pure)
{
  assert(@Int.0 != 0);
  let @Nat = @Int.0 / 3 + @Array<Int>.0[0] * float_to_int(@Float64.0) - 1;
  pos(@Nat.0 + 1);
  if @Nat.2 == 0 then { @Nat.0 - @Nat.1 } else { f(@Int.0, @Array<Int>.0, @Float64.0, @Nat.2 - 1, @Nat.1) }
}
"""
    typed = pipeline.check(source, file="k.vera").typed
    kinds = {row.kind for row in build(typed).rows}
    assert kinds >= {"requires", "ensures", "decreases", "assert", "div_zero",
                     "int_overflow", "index_bounds", "float_to_int_domain",
                     "nat_bind", "nat_sub", "refine_bind", "call_pre"}, kinds


def test_the_gates_carry_no_known_mismatch() -> None:
    """`scripts/check_reconciliation.py`'s `KNOWN` and the generator's
    `KNOWN_CLASSES` are both empty: no mismatch is allowlisted."""
    import importlib.util

    import sys

    spec = importlib.util.spec_from_file_location(
        "_gate_1695", ROOT / "scripts" / "check_reconciliation.py")
    assert spec is not None and spec.loader is not None
    gate = importlib.util.module_from_spec(spec)
    # Registered first, so the script's dataclasses resolve their annotations.
    sys.modules["_gate_1695"] = gate
    spec.loader.exec_module(gate)
    from tests.test_program_generator import KNOWN_CLASSES

    assert gate.KNOWN == ()
    assert KNOWN_CLASSES == ()


# =====================================================================
# The pins: the issue's lines, at the verdict the table gives
# =====================================================================


_SAFE_DIVIDE = """\
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
"""


def test_repro_1598_the_int_min_division_is_a_row() -> None:
    """`INT_MIN / -1` is an `int_overflow` row of the division, `tier3` under
    `requires(@Int.1 != 0)`, and the module's check answers it."""
    v = _verified(_SAFE_DIVIDE)
    rows = _records(v, "int_overflow")
    assert [r for r in rows if r[1] == 6] == [("tier3", 6, 3)], rows
    assert not [c for c in _codes(v) if c in ("E541", "W004")], _codes(v)


def test_repro_1629_a_literal_divisor_is_a_verified_row() -> None:
    source = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 % 3
}
"""
    v = _verified(source)
    assert _records(v, "div_zero") == [("verified", 6, 3)], _records(v, "div_zero")
    assert "W004" not in _codes(v)


def test_repro_1629_a_refined_parameters_entry_check_is_a_row_of_the_callee() -> None:
    source = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn f(@PosInt -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @PosInt.0
}
"""
    v = _verified(source)
    entries = [o for o in v.result.obligations
               if o.kind == "refine_bind" and o.fn_name == "f" and o.line == 3]
    assert [o.status for o in entries] == ["verified"], _records(v, "refine_bind")
    assert "W004" not in _codes(v)


_EXN_DECREASES = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(<Exn<Int>>)
{
  if @Nat.0 > 5 then { 0 } else { f(@Nat.0 + 1) }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { 0 }
  } in {
    f(1)
  }
}
"""


def test_repro_1530_a_decreases_on_an_exn_row_is_disclosed_unguarded() -> None:
    v = _verified(_EXN_DECREASES)
    assert _records(v, "decreases") == [("tier3_unguarded", 4, 3)], _records(v, "decreases")
    assert "E541" not in _codes(v)


_QUANTIFIED_ENSURES = """\
private fn pos(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(forall(@Nat, array_length(@Array<Int>.result), fn(@Nat -> @Bool) effects(pure) { @Array<Int>.result[@Nat.0] > 0 }))
  effects(pure)
{
  @Array<Int>.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = pos([-5]);
  @Array<Int>.0[0]
}
"""


def test_repro_1607_an_ensures_over_an_array_result_is_disclosed_unguarded() -> None:
    v = _verified(_QUANTIFIED_ENSURES)
    rows = [r for r in _records(v, "ensures") if r[1] == 3]
    assert rows == [("tier3_unguarded", 3, 3)], _records(v, "ensures")
    assert "E541" not in _codes(v)


def test_repro_1607_an_ensures_over_a_string_result_is_disclosed_unguarded() -> None:
    source = """\
public fn f(@Int -> @String)
  requires(true)
  ensures(@String.result == show(@Int.0))
  effects(pure)
{
  "not the number"
}
"""
    v = _verified(source)
    assert _records(v, "ensures") == [("tier3_unguarded", 3, 3)], _records(v, "ensures")
    assert "E541" not in _codes(v)


_NESTED_PAYLOAD = """\
public fn g(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Option<Nat>, Int> = Tuple(Some(float_to_int(@Float64.0)), 3);
  7
}
"""


def test_repro_1613_a_payload_nested_in_a_container_literal_is_a_row(tmp_path: Path) -> None:
    v = _verified(_NESTED_PAYLOAD)
    assert _records(v, "nat_bind") == [("tier3", 6, 45)], _records(v, "nat_bind")
    assert not [c for c in _codes(v) if c in ("E541", "W004")], _codes(v)
    ran = _run(tmp_path, _NESTED_PAYLOAD, "g", "-5.0")
    assert ran.returncode != 0 and "Negative value bound into a @Nat slot" in (
        ran.stdout + ran.stderr), ran.stdout + ran.stderr[-300:]


_PARTIAL_COMPONENTS = """\
type Pos = { @Int | @Int.0 > 0 };

private forall<T> fn gid(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

private fn f(@Tuple<Pos, Pos> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

public fn g(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(gid(Tuple(@Int.1, @Int.0)))
}
"""


def test_repro_1642_one_row_per_guarded_component() -> None:
    """The opaque argument of a tuple-typed parameter: one `refine_bind` row
    per component, each answered by the callee's component guard."""
    v = _verified(_PARTIAL_COMPONENTS)
    rows = [r for r in _records(v, "refine_bind") if r[1] == 24]
    assert rows == [("tier3", 24, 5), ("tier3", 24, 5)], _records(v, "refine_bind")
    assert not [c for c in _codes(v) if c in ("E541", "W004")], _codes(v)


_CLAUSE_BINDER = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    throw(@Int.0)
  }
}
"""


def test_repro_1782_a_guarded_clause_binder_is_one_row() -> None:
    v = _verified(_CLAUSE_BINDER)
    assert _records(v, "nat_bind") == [("tier3", 5, 12)], _records(v, "nat_bind")
    assert not [c for c in _codes(v) if c in ("E504", "E541", "W004")], _codes(v)


_CALLEES_ENSURES = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures({ let @Int = apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }, @Int.result); need_pos(@Int.0) > 0 })
  effects(pure)
{
  @Int.0
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(5)
}
"""


def test_repro_1567_a_call_in_a_callees_ensures_is_the_callees() -> None:
    v = _verified(_CALLEES_ENSURES)
    e501 = [d for d in v.diagnostics if d.error_code == "E501"]
    assert not [d for d in e501 if "'main'" in d.description], [d.description[:120] for d in e501]
    assert [o.fn_name for o in v.result.obligations if o.kind == "call_pre"] == ["f"], (
        [(o.fn_name, o.status, o.line) for o in v.result.obligations if o.kind == "call_pre"])


_REFUSED_BINDER = """\
type Pos = { @Int | @Int.0 > 0 };

private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Pos = @Int.0 - 5;
  need_pos(@Pos.0)
}
"""


def test_repro_1563_a_refused_binder_draws_no_second_error() -> None:
    v = _verified(_REFUSED_BINDER)
    errors = [d.error_code for d in v.errors]
    assert errors == ["E505"], errors


_EFFECT_ROW = """\
type IoFn = fn(Int -> Int) effects(<IO>);
type PureFn = fn(Int -> Int) effects(pure);

private data Box { Box(IoFn) }

private fn call_pure(@Box -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Box.0 {
    Box(@PureFn) -> apply_fn(@PureFn.0, 1)
  }
}

public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  call_pure(Box(fn(@Int -> @Int) effects(<IO>) { IO.print("side effect\\n"); @Int.0 }))
}
"""


def test_repro_1725_an_arm_binder_narrowing_an_effect_row_is_disclosed() -> None:
    v = _verified(_EFFECT_ROW)
    assert _records(v, "effect_bind") == [("tier3_unguarded", 12, 9)], _records(v, "effect_bind")
    e542 = [d for d in v.warnings if d.error_code == "E542"]
    assert e542 and "effect row" in e542[0].rationale, [d.rationale[:200] for d in e542]


def test_repro_1582_nothing_inside_an_assume_is_a_row() -> None:
    source = """\
public fn f(@Array<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  assume({ let @Nat = array_length(@Array<Int>.0) - 1; @Nat.0 >= 0 });
  7
}
"""
    v = _verified(source)
    assert _records(v, "int_overflow") == [], _records(v, "int_overflow")
    assert _records(v, "nat_bind") == [], _records(v, "nat_bind")
    assert "E541" not in _codes(v)


_MAP_VALUE = """\
private fn h(@Map<String, Nat> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

public fn g(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  h(map_insert(map_new(), "k", float_to_int(@Float64.0)))
}
"""


def test_repro_1608_a_map_insert_value_outside_a_let_is_a_row() -> None:
    v = _verified(_MAP_VALUE)
    assert _records(v, "nat_bind") == [("tier3", 14, 32)], _records(v, "nat_bind")
    assert "W004" not in _codes(v)


_NESTED_REFINEMENT = """\
type Pos = { @Int | @Int.0 > 0 };
type Small = { @Pos | @Pos.0 < 10 };

public fn mk(@Float64 -> @Option<Small>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}
"""


def test_a_predicate_copy_shares_its_own_kinds_record_in_every_pass() -> None:
    """A guard's copy of a refinement predicate shares the declaration's
    record of its own kind: a division's `div_zero` and its quotient's
    `int_overflow` stand at one node, and each keeps its record.  `mk`'s
    disclosure makes the verifier run a second pass, whose records the
    copies share, not the discarded first pass's (no W004)."""
    v = _verified(
        "type NonNeg = { @Int | @Int.0 >= 0 };\n"
        "type Q = { @Int | @Int.0 / @Int.0 == 1 };\n\n"
        "private fn mk(@Float64 -> @Option<NonNeg>)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n"
        "  let @Option<Int> = Some(float_to_int(@Float64.0));\n"
        "  @Option<Int>.0\n}\n\n"
        "public fn f(@Int -> @Int)\n  requires(@Int.0 > 0)\n  ensures(true)\n"
        "  effects(pure)\n{\n  let @Q = @Int.0;\n  @Q.0\n}\n")
    at = sorted(o.kind for o in v.result.obligations
                if (o.line, o.column) == (2, 19))
    assert at == ["div_zero", "int_overflow"], at
    recon = v.envelope()["reconciliation"]
    assert recon["guarded_unrecorded"] == recon["recorded_unguarded"] == 0, recon
    assert "W004" not in [w["error_code"] for w in v.envelope()["warnings"]]


def test_an_unguarded_binder_holds_no_post_fact() -> None:
    """The post-fact rule's negative space: a binder whose row no check can
    guard (a refinement over a refinement) and whose value the solver
    cannot decide holds nothing for the rest of its scope, so a call that
    needs its predicate is not proved from it (a Tier 3, `E532`)."""
    v = _verified(
        "type Pos = { @Int | @Int.0 > 0 };\n"
        "type Small = { @Pos | @Pos.0 < 10 };\n\n"
        "private fn need(@Int -> @Int)\n  requires(@Int.0 < 10)\n"
        "  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n\n"
        "public fn f(@Float64 -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  let @Small = float_to_int(@Float64.0);\n"
        "  need(@Small.0)\n}\n")
    binds = [(o.status, o.error_code) for o in v.result.obligations
             if o.kind == "refine_bind"]
    assert binds == [("tier3_unguarded", "E506")], binds
    pre = [(o.status, o.error_code) for o in v.result.obligations
           if o.kind == "call_pre"]
    assert pre == [("tier3", "E532")], pre


def test_repro_1602_the_e506_rationale_names_the_rows_reason() -> None:
    v = _verified(_NESTED_REFINEMENT)
    e506 = [d for d in v.warnings if d.error_code == "E506"]
    assert e506, _codes(v)
    rationale = e506[0].rationale
    assert "refinement" in rationale and "constructor field" not in rationale, rationale


_INDEX_INTO_NAT = """\
public fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [1, 2];
  let @Nat = @Array<Int>.0[@Nat.0];
  nat_to_int(@Nat.0)
}
"""


def test_repro_1696_m04_the_index_rows_post_fact_bounds_the_element() -> None:
    """After the guarded `index_bounds` row the index is in range, so the
    element is one of the literal's and the narrowing is no E503."""
    v = _verified(_INDEX_INTO_NAT)
    assert "E503" not in _codes(v), _codes(v)


# =====================================================================
# Regression cells: the nine lines that do not reproduce stay where they are
# =====================================================================


_POS = """\
private fn pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

"""


@pytest.mark.parametrize("body", [
    "match Some(1) {\n    Some(@Int) -> pos(0),\n    None -> 0\n  }",
    "apply_fn(fn(@Int -> @Int) effects(pure) { pos(0) }, 1)",
    "handle[State<Int>](@Int = 0) {\n    get(@Unit) -> { resume(pos(0)) },\n    put(@Int) -> { resume(()) }\n  } in { get(()) }",
    'string_length("\\(pos(0))")',
], ids=["match arm", "closure", "handler clause", "interpolation"])
def test_regression_1570_a_call_precondition_is_obligated_in_every_position(body: str) -> None:
    source = _POS + f"""\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}
"""
    v = _verified(source)
    assert "E501" in _codes(v), _codes(v)


def test_regression_1557_a_nat_subtraction_over_a_nat_call_is_obligated() -> None:
    source = """\
private fn nat_id(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn f(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_id(@Nat.1) - @Nat.0
}
"""
    v = _verified(source)
    assert "E502" in _codes(v), _codes(v)


def test_regression_a_non_negative_literal_into_a_nat_slot_is_no_row() -> None:
    source = """\
private fn takes(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(@Nat.0)
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = 5;
  takes(7)
}
"""
    v = _verified(source)
    assert _records(v, "nat_bind") == [], _records(v, "nat_bind")
    assert "W004" not in _codes(v)


def test_regression_1756_an_int_nat_if_join_is_obligated() -> None:
    """The join the checker types `Nat` carries the narrowing of its `Int`
    arm (#1756): a `nat_bind` record, never a guard with no claim."""
    source = """\
public fn f(@Bool, @Int, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = if @Bool.0 then { @Int.0 } else { @Nat.0 };
  @Nat.0
}
"""
    v = _verified(source)
    assert _records(v, "nat_bind"), _codes(v)
    assert "W004" not in _codes(v), _codes(v)


def test_regression_1596_a_generic_operand_narrowing_is_tier3_and_matched() -> None:
    source = """\
private forall<T> fn id(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = id(0 - 3) + 1;
  nat_to_int(@Nat.0)
}
"""
    v = _verified(source)
    assert ("tier3", 14, 14) in _records(v, "nat_bind"), _records(v, "nat_bind")
    assert not [c for c in _codes(v) if c in ("E541", "W004")], _codes(v)


# =====================================================================
# 67a: code generation guards rows and decides no guard of its own
# =====================================================================


def test_a_check_without_a_row_is_refused() -> None:
    """`_record_check` takes the row the check is the runtime half of: a
    check with no row, or for a row the table holds unguardable, is a
    compiler invariant, never a guard decided at the site."""
    from vera.obligations.table import TRIVIAL, Row
    from vera.skip import CodegenInvariantError
    from vera.wasm.context import StringPool, WasmContext

    compiled = pipeline.compile(_SAFE_DIVIDE, file="s.vera")
    assert compiled.ok and compiled.generator is not None
    table = compiled.generator._obligations
    ctx = WasmContext(StringPool(), obligations=table)
    requires = next(row for row in table.rows if row.kind == "requires")
    with pytest.raises(CodegenInvariantError, match="lists no row"):
        ctx._record_check(None, emitter="wasm/operators.py:_translate_binary")
    trivial = Row(id=len(table.rows), node=requires.node, kind="requires",
                  fn=requires.fn, target=None, guard=TRIVIAL)
    with pytest.raises(CodegenInvariantError, match="unguardable"):
        ctx._record_check(trivial, emitter="codegen/contracts.py:_compile_preconditions")
    assert ctx._record_check(
        requires, emitter="codegen/contracts.py:_compile_preconditions").startswith(" (;vera-check:")


def test_every_emission_names_its_row() -> None:
    """No emitter call outside a row: every `_emit_trap` in the
    code-generation package passes `row=`, and every `_record_check` its
    row first, bar the emission path itself, which passes the caller's
    through."""
    offenders: list[str] = []
    for path in sorted((ROOT / "vera" / "wasm").glob("*.py")) + sorted(
            (ROOT / "vera" / "codegen").glob("*.py")):
        tree = pyast.parse(path.read_text(encoding="utf-8"))
        for node in pyast.walk(tree):
            if not isinstance(node, pyast.Call):
                continue
            func = node.func
            name = func.attr if isinstance(func, pyast.Attribute) else None
            where = f"{path.relative_to(ROOT).as_posix()}:{node.lineno}"
            if name == "_emit_trap":
                if not any(kw.arg == "row" for kw in node.keywords):
                    offenders.append(f"{where}: _emit_trap without row=")
            elif name == "_record_check" and not node.args:
                offenders.append(f"{where}: _record_check names no row")
    assert offenders == [], offenders


# ---------------------------------------------------------------------
# The identity differential, code generation's half: every check names a
# row, every guardable row with a check of its own, in a function the
# module holds, has exactly one.
# ---------------------------------------------------------------------

_WAT_FN = re.compile(r"^\s*\(func \$([^\s()]+)", re.MULTILINE)


def _identity(files: dict[str, str], entry: str, tmp_path: Path) -> None:
    from vera import ast as vera_ast
    from vera.binding import source_name

    entry_path = pipeline.write_tree(tmp_path, files, entry=entry)
    compiled = pipeline.compile(entry_path, file=entry, budget_s=_BUDGET_S)
    if compiled.checked.errors:
        pytest.skip("the program is refused before code generation: "
                    + "; ".join(d.error_code or "" for d in compiled.checked.errors[:3]))
    # Code generation's own refusals (an E6xx a program is written to meet)
    # skip; an internal error (E699, a check with no row among them) fails.
    codes = [d.error_code or "" for d in compiled.errors]
    assert "E699" not in codes, [d.description[:200] for d in compiled.errors]
    if codes:
        pytest.skip("code generation refuses the program: " + "; ".join(codes[:3]))
    assert compiled.generator is not None
    table = compiled.generator._obligations
    held = {source_name(m.group(1)) for m in _WAT_FN.finditer(compiled.wat)}
    prelude = {tld.decl.name for tld in compiled.checked.typed.linked.prelude
               if isinstance(tld.decl, vera_ast.FnDecl)}
    # A generic `where` helper's template has rows (it compiles where it is
    # called at no instance); a module that holds only its clones holds
    # none of the template's code, whatever its parent holds.
    templates: set[str] = set()

    def generic_helpers(decl: vera_ast.FnDecl) -> None:
        for h in decl.where_fns or ():
            if h.forall_vars:
                templates.add(h.name)
            generic_helpers(h)

    for tld in compiled.checked.typed.linked.program.declarations:
        if isinstance(tld.decl, vera_ast.FnDecl):
            generic_helpers(tld.decl)
    checks = [c for c in compiled.result.emitted_checks if not c.prelude]
    named: dict[int, int] = {}
    for check in checks:
        if check.row is None:
            # A generated helper shared by every rendering of its type
            # (`_record_shared_check`, #1482): no row, no span.
            assert (check.emitter.endswith(":_float_to_string_core")
                    and check.line == 0), (check.emitter, check.line, check.column)
            continue
        named[check.row] = named.get(check.row, 0) + 1
        row = table.rows[check.row]
        assert row.guard.check and row.answered_by is None, (
            check.emitter, check.line, check.column, row)
    problems: list[str] = []
    for row in table.rows:
        if (not row.guard.check or row.answered_by is not None
                or row.fn.split("$")[0] in prelude
                or (row.fn in templates and row.fn not in held)
                or not (row.fn in held or row.fn.split("$where$")[0] in held)):
            continue
        count = named.get(row.id, 0)
        # A rendering checks each `Float64` its inline lowering holds, one
        # truncation per component (`show(Tuple(1.5, @Float64.0))`).
        if count != 1 and not (row.kind == "float_to_int_domain" and count > 1):
            span = row.node.span
            problems.append(
                f"{row.kind} {row.path} at "
                f"{span.line if span else '?'}:{span.column if span else '?'} "
                f"{row.evaluation} in {row.fn}: {count} check(s)")
    assert problems == [], problems


#: A closure written inside a position lowered at several sites: a measure
#: re-evaluated at each self tail call it transfers to, a refinement
#: predicate lowered by each guard of its type.  The table lists the
#: closure's rows once, in the body's evaluation (`_closures_listed`);
#: code generation lifts one copy per lowering site, each with its check.
_CLOSURE_AT_SEVERAL_SITES = {
    "measure": """\
public fn count(@Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 < 1000)
  ensures(true)
  decreases(apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }, @Int.0))
  effects(pure)
{
  if @Int.0 == 0 then { 0 } else { count(@Int.0 - 1) }
}
""",
    "predicate": """\
type Small = { @Int | apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }, @Int.0) < 100 };

public fn put_twice(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Small>>)
{
  put(@Int.0);
  put(@Int.0);
  0
}
""",
}


def _closure_sources_at_several_sites() -> list[object]:
    """The two shapes above, and the #1480 matrix's closure-body cells (a
    closure in a measure at entry, in a refinement predicate, in a body)."""
    from tests import test_evaluated_position_obligations_1480 as m1480

    out: list[object] = [pytest.param(src, id=name)
                         for name, src in sorted(_CLOSURE_AT_SEVERAL_SITES.items())]
    for param in m1480._sub_position_cells():
        sub, op, position, status = param.values  # type: ignore[attr-defined]
        if sub.name == "closure body":
            out.append(pytest.param(
                m1480._sub_position_cell(sub, op, position, status).source,
                id=f"1480-{position}-{op.name}"))
    return out


@pytest.mark.parametrize("source", _closure_sources_at_several_sites())
def test_no_two_rows_share_a_node_and_an_evaluation(source: str) -> None:
    """A closure inside a position lowered at several sites is walked once
    per site; whatever rows its operations take, no two of the table's rows
    share a (node, kind, path, evaluation) key, the key code generation
    looks a check's row up by."""
    from vera.obligations.table import ObligationTable, build

    typed = pipeline.check(source, file="p.vera").typed
    keys = [(ObligationTable._key(r.node), r.kind, r.path, r.evaluation)
            for r in build(typed).rows]
    assert len(keys) == len(set(keys)), sorted(
        k for k in set(keys) if keys.count(k) > 1)


@pytest.mark.parametrize("site", sorted(_CLOSURE_AT_SEVERAL_SITES))
def test_a_closure_lowered_at_several_sites_has_one_check_per_row(
    site: str, tmp_path: Path,
) -> None:
    """A closure node is lifted once per function context, whatever the
    number of sites that lower it (amendment 2 to the design note): one
    copy, one check, one row."""
    source = _CLOSURE_AT_SEVERAL_SITES[site]
    _identity({"p.vera": source}, "p.vera", tmp_path)


_ANON_FN = re.compile(r"^\s*\(func \$anon_\d+", re.MULTILINE)


def _closure_sources_lowered_twice() -> list[object]:
    """The two shapes, and the #1480 matrix's closure-body cells in a measure
    (the cells whose measure lowers at entry and at a self tail call)."""
    from tests import test_evaluated_position_obligations_1480 as m1480

    out: list[object] = [pytest.param(src, id=name)
                         for name, src in sorted(_CLOSURE_AT_SEVERAL_SITES.items())]
    for param in m1480._sub_position_cells():
        sub, op, position, status = param.values  # type: ignore[attr-defined]
        if sub.name == "closure body" and position.startswith("measure"):
            out.append(pytest.param(
                m1480._sub_position_cell(sub, op, position, status).source,
                id=f"1480-{position}-{op.name}"))
    return out


@pytest.mark.parametrize("source", _closure_sources_lowered_twice())
def test_one_lifted_function_per_closure_node(source: str) -> None:
    """The module holds as many lifted `anon_` functions as the closure
    nodes the program writes, every site of one node reusing its copy (the
    memo's killer: a module that lifts per site holds two)."""
    from vera import ast as vera_ast

    written: set[object] = set()

    def visit(node: object) -> None:
        if isinstance(node, vera_ast.AnonFn):
            written.add(node.node_id)
        if isinstance(node, vera_ast.Node):
            for name in node.__dataclass_fields__:
                visit(getattr(node, name))
        elif isinstance(node, (tuple, list)):
            for item in node:
                visit(item)

    # Each shape lowers its closure in one function, so a node is one copy.
    visit(pipeline.check(source, file="p.vera").typed.program)
    compiled = pipeline.compile(source, file="p.vera")
    assert compiled.ok, compiled
    assert len(_ANON_FN.findall(compiled.wat)) == len(written), compiled.wat[:400]


def test_a_rolled_back_lifting_leaves_no_memo_entry() -> None:
    """A translation of a closure that rolls back (a capture with no local
    at the site) takes its registration back, so the node's next
    translation lifts it once, under the id the rollback returned."""
    from vera.wasm.closures import ClosuresMixin

    class _Env:
        def __init__(self, resolves: bool) -> None:
            self.resolves = resolves

        def resolve(self, name: str, index: int) -> int | None:
            return 3 if self.resolves else None

    class _Ctx(ClosuresMixin):
        def __init__(self) -> None:
            self._pending_closures: list[object] = []
            self._next_closure_id = 7
            self._lifted_closure_ids: dict[object, int] = {}
            self.needs_alloc = False

        def _collect_free_vars(self, anon: object) -> list[tuple[str, int, str]]:
            return [("Int", 0, "i64")]

        def alloc_local(self, wt: str) -> int:
            return 9

    from vera import ast as vera_ast

    anon = vera_ast.AnonFn(params=(), return_type=None, effect=None, body=None)  # type: ignore[arg-type]
    ctx = _Ctx()
    assert ctx._translate_anon_fn(anon, _Env(False)) is None  # type: ignore[arg-type]
    assert ctx._pending_closures == [] and ctx._next_closure_id == 7
    assert ctx._lifted_closure_ids == {}
    assert ctx._translate_anon_fn(anon, _Env(True)) is not None  # type: ignore[arg-type]
    assert ctx._translate_anon_fn(anon, _Env(True)) is not None  # type: ignore[arg-type]
    assert [cid for _, _, cid in ctx._pending_closures] == [7]  # type: ignore[misc]
    assert ctx._next_closure_id == 8


_CORPUS = sorted((ROOT / "examples").rglob("*.vera")) + sorted(
    (ROOT / "tests" / "conformance").rglob("*.vera"))
_CORPUS_FILES = _CORPUS


@pytest.mark.parametrize(
    "path", _CORPUS, ids=[p.relative_to(ROOT).as_posix() for p in _CORPUS])
def test_identity_over_the_corpus(path: Path, tmp_path: Path) -> None:
    files = {sib.relative_to(path.parent).as_posix(): sib.read_text(encoding="utf-8")
             for sib in path.parent.rglob("*.vera")}
    _identity(files, path.name, tmp_path)


def _doc_blocks() -> list[tuple[str, str]]:
    import sys

    sys.path.insert(0, str(ROOT / "scripts"))
    import check_doc_examples as cde
    from doc_annotations import strip_annotations

    out: list[tuple[str, str]] = []
    for pattern in cde.DOC_GATES:
        for path in sorted(ROOT.glob(pattern)):
            blocks, _problems = cde.scan_document(path)
            for block in blocks:
                if cde.selects(block):
                    out.append((f"{path.relative_to(ROOT).as_posix()}:{block.line}",
                                strip_annotations(block.content)))
    return out


_DOC_BLOCKS = _doc_blocks()


@pytest.mark.parametrize(
    "source", [b[1] for b in _DOC_BLOCKS], ids=[b[0] for b in _DOC_BLOCKS])
def test_identity_over_the_doc_blocks(source: str, tmp_path: Path) -> None:
    _identity({"doc.vera": source}, "doc.vera", tmp_path)


@pytest.mark.parametrize("seed", range(1000), ids=[f"seed{s}" for s in range(1000)])
def test_identity_over_the_generator(seed: int, tmp_path: Path) -> None:
    from tests import program_generator as gen

    _identity(gen.generate(seed).files(), gen.ENTRY, tmp_path)


# ---------------------------------------------------------------------
# The identity differential, the verifier's half: every row of a function
# the verifier discharged has exactly one record, which names it, and every
# record of a table kind names its rows.
# ---------------------------------------------------------------------


def _verifier_identity(files: dict[str, str], entry: str, tmp_path: Path) -> None:
    from collections import Counter

    from vera import ast as vera_ast
    from vera import verifier as vmod

    entry_path = pipeline.write_tree(tmp_path, files, entry=entry)
    # Every record of a table kind is keyed to its rows where it is made
    # (#1836), and a discharge runs only where a row is: no record reaches
    # `_settle_rows` without rows.
    unanchored: list[tuple[str, str, int, int]] = []
    real_settle = vmod.ContractVerifier._settle_rows

    def settle(self, decl, start, made_here, *, premise=None):  # type: ignore[no-untyped-def]
        if self._table.rows_of_function(decl) is not None:
            unanchored.extend(
                (rec.fn_name, rec.kind, rec.line, rec.column) for rec in made_here
                if rec.kind in vmod._TABLE_KINDS and not rec.rows)
        return real_settle(self, decl, start, made_here, premise=premise)

    vmod.ContractVerifier._settle_rows = settle  # type: ignore[method-assign]
    try:
        v = pipeline.verify(entry_path, file=entry, budget_s=_BUDGET_S,
                            reconcile=True)
    finally:
        vmod.ContractVerifier._settle_rows = real_settle  # type: ignore[method-assign]
    if not v.ran:
        pytest.skip("the program is refused before verification")
    assert unanchored == [], unanchored
    assert _envelope_inconsistencies(v) == [], _envelope_inconsistencies(v)
    assert _leaf_omissions(v) == [], _leaf_omissions(v)
    table = v.result.table
    assert table is not None
    named = Counter(r for o in v.result.obligations for r in o.rows)
    twice = [(table.rows[r].kind, table.rows[r].content_key[3:]) for r, n in named.items()
             if n != 1]
    assert twice == [], twice
    no_row = [(o.kind, o.line, o.column) for o in v.result.obligations
              if not o.rows and o.kind != "state_decl"]
    assert no_row == [], no_row
    prelude = {tld.decl.name for tld in v.checked.typed.linked.prelude
               if isinstance(tld.decl, vera_ast.FnDecl)}
    # A generic's template is verified through its clones, whose records
    # carry the clones' rows; the template's own rows (its helpers' too)
    # have none.
    template_rows: set[int] = set()

    def template(decl: vera_ast.FnDecl, generic: bool) -> None:
        generic = generic or bool(decl.forall_vars)
        if generic and decl.body is not None:
            template_rows.update(table.by_body.get(id(decl.body), ()))
        for helper in decl.where_fns or ():
            template(helper, generic)

    for tld in v.checked.typed.linked.program.declarations:
        if isinstance(tld.decl, vera_ast.FnDecl):
            template(tld.decl, False)
    verified = {table.rows[r].fn for r in named}
    unrecorded = [
        (row.kind, row.content_key[3:], row.evaluation[0], row.fn)
        for row in table.rows
        if row.fn in verified and row.id not in named
        and row.fn.split("$")[0] not in prelude and row.id not in template_rows]
    assert unrecorded == [], unrecorded
    assert not [c for c in _codes(v) if c in ("E541", "W004")], _codes(v)


#: The four classes a fallback discharged before #1836, each a program whose
#: row is now an ordinary discharge in its own context, and the status that
#: discharge gives it (the status the fallback gave): a literal divisor (the
#: `div_zero` discharge proves it), a refined formal's ENTRY row (the entry
#: step's assumption), a trivial clause (`requires(true)`), and a binder at
#: its value's own refined type (nothing to prove beyond the type the value
#: carries, which an opaque component's accessor does not hold: left to the
#: check code generation emits, `tier3`).
_FORMER_FALLBACK_CLASSES = {
    "literal divisor": ("""\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 / 5
}
""", "div_zero", "verified"),
    "refined formal entry": ("""\
type PosInt = { @Int | @Int.0 > 0 };

public fn f(@PosInt -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @PosInt.0
}
""", "refine_bind", "verified"),
    "trivial": ("""\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
""", "requires", "verified"),
    "binder at its own type": ("""\
type PosInt = { @Int | @Int.0 > 0 };
private data Box {
  Boxed(PosInt, Int)
}

public fn f(@Box -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Box.0 {
    Boxed(@PosInt, @Int) -> @PosInt.0 + @Int.0
  }
}
""", "refine_bind", "tier3"),
}


@pytest.mark.parametrize("cls", list(_FORMER_FALLBACK_CLASSES))
def test_a_former_fallback_class_is_an_ordinary_discharge(cls: str) -> None:
    """Every row of the class is recorded where the traversal reaches it
    (in the records made while the function is verified, never at the
    settling), with the status the fallback gave it."""
    from vera import verifier as vmod

    source, kind, status = _FORMER_FALLBACK_CLASSES[cls]
    made: list[tuple[str, str, tuple[int, ...]]] = []
    real = vmod.ContractVerifier._settle_rows

    def settle(self, decl, start, made_here, *, premise=None):  # type: ignore[no-untyped-def]
        made.extend((r.kind, r.status, r.rows) for r in made_here)
        return real(self, decl, start, made_here, premise=premise)

    vmod.ContractVerifier._settle_rows = settle  # type: ignore[method-assign]
    try:
        v = _verified(source)
    finally:
        vmod.ContractVerifier._settle_rows = real  # type: ignore[method-assign]
    table = v.result.table
    assert table is not None
    rows = [r for r in table.rows if r.kind == kind and r.fn == "f"]
    assert rows, (cls, kind)
    for row in rows:
        at = [st for k, st, ids in made if k == kind and row.id in ids]
        assert at == [status], (cls, row.content_key, at)
    assert not hasattr(vmod.ContractVerifier, "_row_record")


_TAIL_NAMED = re.compile(r"\(at the self tail call at (\d+):(\d+)\)")
#: Verification errors that stand at no record of their own: a premise
#: refusal, the reconciliation's E541, and the disclosures.
_NO_RECORD_CODES = {"E538", "E539", "E540", "E541", "E542", "E543"}


def _envelope_inconsistencies(v: pipeline.Verified) -> list[object]:
    """Every `violated` record has an error at its site (or at a self tail
    call one of its rows is evaluated at, which a measure's copy names);
    every verification error stands at such a site: no E50x beside a record
    that is not `violated`, none with no record at all, and no more errors
    at a site than `violated` records stand there (one diagnostic per
    record, whichever copies discharged it)."""
    from vera import ast as vera_ast
    from vera import fold

    res = v.result
    table = res.table
    calls: dict[object, tuple[int, int]] = {}
    for n in fold.walk(v.checked.typed.linked.program):
        if isinstance(n, vera_ast.FnCall) and n.node_id is not None and n.span:
            calls[n.node_id] = (n.span.line, n.span.column)
    sites: list[set[tuple[int, int]]] = []
    bad: list[object] = []
    for o in res.obligations:
        if o.status != "violated":
            continue
        at = {(o.line, o.column)}
        named = _TAIL_NAMED.search(o.expr_text)
        if named:
            at.add((int(named.group(1)), int(named.group(2))))
        for r in o.rows:
            ev = table.rows[r].evaluation
            if ev and ev[0] == "measure_call" and ev[1] in calls:
                at.add(calls[ev[1]])
        sites.append(at)
    listed = [((d.location.line, d.location.column), d.error_code)
              for d in res.diagnostics if d.severity == "error"
              and d.error_code.startswith("E5")
              and d.error_code not in _NO_RECORD_CODES]
    errors = dict(listed)
    for at in sites:
        if not at & errors.keys():
            bad.append(("violated record with no error", sorted(at)))
    every = set().union(*sites) if sites else set()
    bad += [("error with no violated record", code, at)
            for at, code in errors.items() if at not in every]
    for at in errors:
        n = sum(1 for where, _ in listed if where == at)
        held = sum(1 for s in sites if at in s)
        if n > held:
            bad.append(("more errors than violated records", at, n, held))
    return bad


def _leaf_omissions(v: pipeline.Verified) -> list[object]:
    """Every value leaf a function's body yields into a return type that
    writes a refinement the leaf's type does not equal has a row: in the
    leaf (a construction's field, the leaf itself) or at the return.  A
    narrowing leaf with no row is an omission, the direction the identity
    cells cannot see (a site the table does not list is a site nothing
    records)."""
    from vera import ast as vera_ast
    from vera import fold, narrowing
    from vera.obligations.table import ObligationTable
    from vera.types import NEVER, AdtType, RefinedType

    def refined(t: object, depth: int = 0) -> bool:
        if isinstance(t, RefinedType):
            return True
        return (depth < 6 and isinstance(t, AdtType)
                and any(refined(a, depth + 1) for a in t.type_args))

    typed = v.checked.typed
    table = v.result.table
    key = ObligationTable._key
    narrowing_rows = [r for r in table.rows if r.kind in ("refine_bind", "nat_bind")]
    out: list[object] = []
    for tld in typed.linked.program.declarations:
        decl = tld.decl
        if (not isinstance(decl, vera_ast.FnDecl) or decl.body is None
                or decl.forall_vars):
            continue
        req = typed.semantic_type(decl.return_type)
        if req is None or not refined(req):
            continue
        at_return = {key(n) for n in fold.walk(decl.return_type)} | {key(decl.body)}
        if any(key(r.node) in at_return for r in narrowing_rows):
            continue
        for leaf in narrowing.value_leaves(decl.body):
            sem = typed.semantic_type(leaf)
            if sem is None or sem == req or sem == NEVER:
                continue
            inside = {key(n) for n in fold.walk(leaf)}
            if not any(key(r.node) in inside for r in narrowing_rows):
                out.append((decl.name, leaf.span.line if leaf.span else 0,
                            str(sem), str(req)))
    return out


@pytest.mark.parametrize(
    "path", _CORPUS_FILES, ids=[p.relative_to(ROOT).as_posix() for p in _CORPUS_FILES])
def test_verifier_identity_over_the_corpus(path: Path, tmp_path: Path) -> None:
    files = {sib.relative_to(path.parent).as_posix(): sib.read_text(encoding="utf-8")
             for sib in path.parent.rglob("*.vera")}
    _verifier_identity(files, path.name, tmp_path)


@pytest.mark.parametrize(
    "source", [b[1] for b in _DOC_BLOCKS], ids=[b[0] for b in _DOC_BLOCKS])
def test_verifier_identity_over_the_doc_blocks(source: str, tmp_path: Path) -> None:
    _verifier_identity({"doc.vera": source}, "doc.vera", tmp_path)


@pytest.mark.parametrize("seed", range(1000), ids=[f"seed{s}" for s in range(1000)])
def test_verifier_identity_over_the_generator(seed: int, tmp_path: Path) -> None:
    from tests import program_generator as gen

    _verifier_identity(gen.generate(seed).files(), gen.ENTRY, tmp_path)


#: A measure whose operation proves at the function's entry (`@Nat.0 >= 1`)
#: and is left undecided at the self tail call, whose argument the verifier
#: cannot see into: the copies share one record, which takes the tail
#: call's status and names it (amendment 3 to the design note).
_MEASURE_DECIDED_AT_THE_TAIL_CALL = """\
public fn down(@Nat, @Bool -> @Nat)
  requires(@Nat.0 >= 1)
  ensures(true)
  decreases(@Nat.0 - 1)
  effects(pure)
{
  if @Nat.0 <= 2 then { 0 } else { down(apply_fn(fn(@Nat -> @Nat) effects(pure) { @Nat.0 }, @Nat.0 - 1), @Bool.0) }
}
"""


def test_a_measures_copies_share_one_record_with_the_worst_status() -> None:
    v = _verified(_MEASURE_DECIDED_AT_THE_TAIL_CALL)
    (record,) = [o for o in v.result.obligations
                 if o.kind == "int_overflow" and (o.line, o.column) == (4, 13)]
    assert record.status == "tier3", record
    assert "self tail call at 7:36" in record.expr_text, record.expr_text
    assert len(record.rows) == 2, record.rows


#: A measure whose `@Nat` subtraction proves at the entry (`requires` gives
#: `a >= b`) and is refuted at the self tail call, whose second argument is
#: `b + 5`: one record, violated, naming the tail call (E502 there).
_MEASURE_REFUTED_AT_THE_TAIL_CALL = """\
public fn down(@Nat, @Nat -> @Nat)
  requires(@Nat.1 >= @Nat.0)
  ensures(true)
  decreases(@Nat.1 - @Nat.0)
  effects(pure)
{
  if @Nat.1 == @Nat.0 then { 0 } else { down(@Nat.1, @Nat.0 + 5) }
}
"""


def test_a_measure_refuted_at_the_tail_call_is_one_violated_record() -> None:
    v = _verified(_MEASURE_REFUTED_AT_THE_TAIL_CALL)
    (record,) = [o for o in v.result.obligations if o.kind == "nat_sub"]
    assert (record.status, record.line, record.column) == ("violated", 4, 13), record
    assert "self tail call at 7:41" in record.expr_text, record.expr_text
    assert len(record.rows) == 2, record.rows
    assert "E502" in _codes(v), _codes(v)


# ---------------------------------------------------------------------
# The WAT movers: a guard that appears or goes because the table lists the
# row the old decision missed, or lists none where it emitted one
# ---------------------------------------------------------------------


_BARE_PUT = """\
type Pos = { @Int | @Int.0 > 0 };

private fn write(@Int -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Pos>>)
{
  put(@Int.0)
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Pos>](@Pos = 1) {
    get(@Unit) -> { resume(@Pos.0) },
    put(@Pos) -> { resume(()) }
  } in {
    write(@Int.0);
    nat_to_int(0) + get(())
  }
}
"""


def test_mover_a_bare_put_into_a_refined_cell_takes_the_predicate_guard(
    tmp_path: Path,
) -> None:
    """The find of report 1: on the intrinsic route the write took the sign
    guard alone; the `refine_bind` row at the argument is the predicate's,
    and the run traps where it printed -3."""
    compiled = pipeline.compile(_BARE_PUT, file="p.vera")
    assert compiled.ok
    guards = pipeline.checks(
        compiled.result, emitter="codegen/contracts.py:_emit_refinement_check")
    assert [(g.line, g.column) for g in guards if g.function == "write"] == [(8, 7)]
    ran = _run(tmp_path, _BARE_PUT, "main", "-3")
    assert ran.returncode != 0 and "Refinement violation" in (ran.stdout + ran.stderr), (
        ran.stdout + ran.stderr[-300:])


def test_mover_a_guard_on_a_value_already_of_the_refined_type_goes() -> None:
    """`examples/ephemeris.vera` stored a refined slot into a field of its
    own type (lines 269 and 292): two §2.6.5 checks whose predicate held by
    typing, since the slot's own binding is checked, with no record (the
    KNOWN entries removed with them).  The table lists no row where a value
    already carries the refinement.  A binder is the other case: the
    sub-pattern at its field's own refinement (line 340) is still checked,
    since a field's refinement is no fact unless its producer was checked,
    and a parameter's payload is not (#1706's cells)."""
    compiled = pipeline.compile(ROOT / "examples" / "ephemeris.vera", file="ephemeris.vera")
    assert compiled.ok
    sites = {(g.line, g.column) for g in pipeline.checks(
        compiled.result, emitter="codegen/contracts.py:_emit_refinement_check")}
    assert not sites & {(269, 50), (292, 50)}, sorted(sites)
    assert (211, 35) in sites and (223, 36) in sites  # the entry checks stay
    assert (340, 26) in sites  # the binder's check stays


#: The join forms whose value leaves the table reads (`narrowing.flow_arms`),
#: each with one arm the `Never` form *n* and one a `@Nat`.
_NEVER_JOINS = {
    "if": "if @Bool.0 then {{ {n} }} else {{ @Nat.0 }}",
    "match": "match @Option<Nat>.0 {{\n    Some(@Nat) -> @Nat.0,\n    None -> {n}\n  }}",
    "handle": ("handle[Exn<Nat>] {{\n    throw(@Nat) -> {{ @Nat.0 }}\n  }} in {{\n"
               "    if @Bool.0 then {{ {n} }} else {{ @Nat.0 }}\n  }}"),
}
#: The leaves the checker types `Never`: a `throw`, a call of a function
#: declared `@Never` (which code generation refuses, E601, and its caller
#: with it, E620, so only the table's row is asserted there), and a nested
#: join whose every leaf is `Never`.
_NEVER_LEAVES = {
    "throw": "throw(4)",
    "call": "bail(4)",
    "nested": "if @Bool.0 then { throw(4) } else { throw(5) }",
}
_BAIL = """\
private fn bail(@Int -> @Never)
  requires(true)
  ensures(true)
  effects(<Exn<Int>>)
{
  throw(@Int.0)
}

"""


def _never_join_program(value: str, *, bail: bool = False, let: str = "Nat") -> str:
    return ((_BAIL if bail else "")
            + f"private fn f(@{let}, @Nat, @Option<Nat>, @Bool -> @Nat)\n"
            "  requires(true)\n  ensures(true)\n  effects(<Exn<Int>>)\n{\n"
            f"  let @{let} = {value};\n  0\n}}\n\n"
            "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
            "  effects(<IO>)\n{\n  ()\n}\n")


def _let_value_rows(source: str, kind: str) -> list[tuple[int, int]]:
    """The *kind* rows the table lists at `f`'s `let` value."""
    from vera import ast
    from vera.obligations.table import build

    typed = pipeline.check(source, file="join.vera").typed
    (fn,) = [d for d in typed.program.declarations
             if isinstance(getattr(d, "decl", None), ast.FnDecl) and d.decl.name == "f"]
    (let,) = [st for st in fn.decl.body.statements if isinstance(st, ast.LetStmt)]
    return [(r.node.span.line, r.node.span.column) for r in build(typed).rows
            if r.kind == kind and r.node is let.value]


def _f_checks(source: str, emitter: str) -> list[tuple[int, int]]:
    """The *emitter* checks the compiled `f` holds; `f` must be compiled
    (`pipeline.checks` refuses an absence asked of a function the module
    does not define)."""
    compiled = pipeline.compile(source, file="join.vera")
    assert compiled.ok, compiled
    return [(g.line, g.column) for g in pipeline.checks(
        compiled.result, emitter=emitter, function="f")]


@pytest.mark.parametrize("leaf", sorted(_NEVER_LEAVES))
@pytest.mark.parametrize("join", sorted(_NEVER_JOINS))
def test_repro_a_never_leaf_of_a_join_is_no_narrowing_into_nat(join: str, leaf: str) -> None:
    """A join-leaf reader of the table counted a leaf of semantic type
    `Never` as a value: a `let @Nat` of a join whose other arms are `@Nat`
    took a sign row and a guard the verifier, reading the join at the
    checker's `Nat`, records nothing for (a W004; generator seed 15 and 15
    more of seeds 0 to 999, none at base 56ae0449).  A `Never` leaf gives the
    join no value: no row, and the checks base emits (none)."""
    source = _never_join_program(_NEVER_JOINS[join].format(n=_NEVER_LEAVES[leaf]),
                                 bail=leaf == "call")
    assert _let_value_rows(source, "nat_bind") == [], source
    if leaf == "call":
        # `bail` is refused (E601) and `f`, its caller, with it (E620): no
        # module function to ask, so the row is the cell's evidence.
        compiled = pipeline.compile(source, file="join.vera")
        codes = {d.error_code for d in compiled.warnings}
        assert {"E601", "E620"} <= codes, codes
        return
    assert _f_checks(source, "wasm/operators.py:_emit_nat_bind_guard") == [], source


@pytest.mark.parametrize("join", ["if", "match"])
def test_a_join_whose_every_leaf_is_never_is_no_row(join: str) -> None:
    """A join whose every leaf is `Never` yields no value: nothing to prove
    a fact of, nothing to guard, so the table lists no row at the `let`
    (amendment 1 to the design note: a `Never` leaf is no row), code
    generation emits no guard after the throws, and the verifier records
    nothing there."""
    value = {"if": "if @Bool.0 then { throw(4) } else { throw(5) }",
             "match": ("match @Option<Nat>.0 {\n    Some(@Nat) -> throw(4),\n"
                       "    None -> throw(5)\n  }")}[join]
    source = _never_join_program(value)
    assert _let_value_rows(source, "nat_bind") == [], source
    assert _f_checks(source, "wasm/operators.py:_emit_nat_bind_guard") == [], source
    verified = _verified(source)
    assert verified.ran and not verified.errors, verified
    assert _records(verified, "nat_bind") == [], _records(verified, "nat_bind")


def test_the_sibling_never_leaf_readers_list_no_row_at_a_throw() -> None:
    """The two other readers that list a guarded row from a join's leaves
    read a `throw` leaf as the fixed reader does, as no value (amendment 1):
    a `@Nat` return's per-leaf rows skip the `throw` arm, so no dead guard
    follows it, and a refined `let` of a join whose value leaf already has
    the refinement takes no head row and no sign row."""
    ret = """\
private fn h(@Nat, @Bool -> @Nat)
  requires(true)
  ensures(true)
  effects(<Exn<Int>>)
{
  match @Bool.0 { true -> throw(4), false -> @Nat.0 }
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  ()
}
"""
    compiled = pipeline.compile(ret, file="ret.vera")
    assert [(g.line, g.column) for g in pipeline.checks(
        compiled.result, emitter="wasm/operators.py:_emit_nat_bind_guard",
        function="h")] == []
    assert _records(_verified(ret), "nat_bind") == []
    refined = "type Cap = { @Nat | @Nat.0 <= 30 };\n\n" + _never_join_program(
        "if @Bool.0 then { throw(4) } else { @Cap.0 }", let="Cap")
    assert _let_value_rows(refined, "refine_bind") == [], refined
    assert _let_value_rows(refined, "nat_bind") == [], refined
    # The value leaf that narrows keeps its row: a `Never` beside an `@Int`
    # arm takes the `@Int` arm's sign row and check.
    keeps = _never_join_program("if @Bool.0 then { throw(4) } else { 0 - @Nat.0 }")
    assert _let_value_rows(keeps, "nat_bind") == [(6, 14)], keeps
    assert _f_checks(keeps, "wasm/operators.py:_emit_nat_bind_guard") == [(6, 14)], keeps


def test_mover_a_clause_binder_over_a_container_payload_is_walked(
    tmp_path: Path,
) -> None:
    """The one exclusion beside #1818's rule goes: a handler clause binder
    over an `Array` payload declared narrower than it is a `nat_bind` row
    with a tree, so the payload is walked and a negative element traps; the
    verifier records the row Tier 3 (no E506 disclosure, no W004: the
    designed W004 of the first half retires with the verifier's discharge)."""
    from tests.test_composite_coercion_guards import SHAPES, program

    source = program("clause binder", SHAPES["Array"], "opaque")
    compiled = pipeline.compile(source, file="c.vera")
    assert compiled.ok
    walks = pipeline.checks(
        compiled.result, emitter="wasm/coercion.py:_emit_component_coercion")
    assert len(walks) == 1, walks
    ran = _run(tmp_path, source, "f", "-5.0")
    assert ran.returncode != 0 and "Negative value bound into a @Nat slot" in (
        ran.stdout + ran.stderr), ran.stdout + ran.stderr[-300:]
    v = _verified(source, "c.vera")
    assert _records(v, "nat_bind") == [("tier3", 26, 12)], _records(v, "nat_bind")
    assert not [c for c in _codes(v) if c in ("E506", "W004", "E541")], _codes(v)


_LATER_ELEMENT = """\
public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = 3;
  [@Nat.0, @Int.0][1]
}
"""


def test_mover_a_later_array_element_is_guarded(tmp_path: Path) -> None:
    """`[@Nat.0, @Int.0]` is an `Array<Nat>` (spec §4.12.1 fixes the element
    type from the first element): the `@Int` element's row is the
    literal's own, where the store guard read only a requirement the
    literal's context handed it, so `f(-5)` printed -5 (#1695's line)."""
    compiled = pipeline.compile(_LATER_ELEMENT, file="l.vera")
    assert compiled.ok
    guards = pipeline.checks(compiled.result, kind="nat_guard")
    assert [(g.line, g.column) for g in guards] == [(7, 12)], guards
    ran = _run(tmp_path, _LATER_ELEMENT, "f", "-5")
    assert ran.returncode != 0 and "Negative value bound into a @Nat slot" in (
        ran.stdout + ran.stderr), ran.stdout + ran.stderr[-300:]


def test_mover_the_second_guard_on_a_clause_binders_use_goes() -> None:
    """#1782's program: the clause binder `@Nat` over a thrown `@Int` is one
    row, guarded at the clause; its use at `nat_to_int`'s `@Nat` formal is
    no row under the post-fact rule, so the second sign guard goes."""
    compiled = pipeline.compile(_CLAUSE_BINDER, file="b.vera")
    assert compiled.ok
    guards = pipeline.checks(compiled.result, kind="nat_guard")
    assert [(g.line, g.column) for g in guards] == [(5, 5)], guards


_PREFIX = """\
public fn count(@Nat, @Nat -> @Nat)
  requires(true)
  ensures({ENSURES})
  decreases(@Nat.1)
  effects(pure)
{
  if @Nat.1 == 0 then { @Nat.0 } else { count(@Nat.0 + 1, @Nat.1 - 1) }
}
"""


def test_mover_the_self_tail_prefix_is_rendered_only_where_it_splices() -> None:
    """A `decreases` function's self-tail prefix re-evaluates the measure
    before each `return_call`: the table lists its rows once per tail call
    the function transfers to, and none where a runtime postcondition
    reverts every `return_call` to `call` (the entry check then covers
    each hop).  The prefix rendered for rows that do not exist was dead
    lowering: its locals go."""
    spliced = pipeline.compile(_PREFIX.replace("{ENSURES}", "true"), file="s.vera")
    reverted = pipeline.compile(_PREFIX.replace("{ENSURES}", "@Nat.result >= 0"), file="r.vera")
    assert spliced.ok and reverted.ok
    for compiled, copies in ((spliced, 1), (reverted, 0)):
        assert compiled.generator is not None
        table = compiled.generator._obligations
        re_evaluations = [row for row in table.rows
                          if row.kind == "decreases" and row.evaluation[0] == "measure_call"]
        assert len(re_evaluations) == copies, [r.evaluation for r in re_evaluations]
        prefixes = pipeline.checks(
            compiled.result, emitter="codegen/contracts.py:_dec_self_tail_prefix")
        assert len(prefixes) == copies, prefixes
    assert "return_call" in spliced.wat and "return_call" not in reverted.wat


# A self-recursive tail call whose measure carries a check of its own
# (`@Nat.1 - @Nat.0`, a `nat_sub` row): the spliced prefix holds a marker,
# and re-keying it once per splice must terminate (examples/fizzbuzz.vera
# looped in the re-keying and grew without bound).
_CHECKED_MEASURE = """\
private fn loop(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  decreases(@Nat.1 - @Nat.0)
  effects(pure)
{
  if @Nat.0 < @Nat.1 then { loop(@Nat.1, @Nat.0 + 1) } else { @Nat.0 }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  loop(10, 1)
}
"""

_CHECKED_MEASURE_CHILD = """\
import json, sys
from tests import pipeline
compiled = pipeline.compile(sys.stdin.read(), file="m.vera")
assert compiled.ok and compiled.generator is not None
table = compiled.generator._obligations
spliced = [row.id for row in table.rows
           if row.fn == "loop" and isinstance(row.evaluation, tuple)
           and row.evaluation[0] == "measure_call"]
named = [check.row for check in compiled.result.emitted_checks]
print(json.dumps({"spliced": spliced, "named": named,
                  "rows": len(table.rows)}))
"""


def test_mover_a_measure_check_is_rekeyed_once_per_splice() -> None:
    """Each spliced copy of the self-tail prefix names its own call's
    measure rows exactly once, and compiling it terminates: a subprocess
    under a 30 s timeout, since the defect this pins was a loop."""
    import json
    import subprocess
    import sys

    root = Path(__file__).resolve().parent.parent
    done = subprocess.run(
        [sys.executable, "-c", _CHECKED_MEASURE_CHILD],
        input=_CHECKED_MEASURE, capture_output=True, text=True,
        encoding="utf-8", cwd=root, timeout=30, check=False)
    assert done.returncode == 0, done.stderr[-2000:]
    report = json.loads(done.stdout.strip().splitlines()[-1])
    assert report["spliced"], "no measure re-evaluation row at the tail call"
    for row_id in report["spliced"]:
        assert report["named"].count(row_id) == 1, (row_id, report)
    assert len(report["named"]) <= report["rows"], report


# A refinement over a function type: `naming.refinement_binder_parts` names a
# binder for an alias base (`{ @IF | P }`) and code generation guards it at
# every boundary, as at base; for a base written inline (`{ @fn(…) … | P }`)
# it names none, and the row is unguardable (`REASON_FUNCTION_BASE`).
_FN_ALIAS = """\
type IF = fn(Int -> Int) effects(pure);

type One = { @IF | apply_fn(@IF.0, 0) == 1 };

private fn mk(@Int -> @IF)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + 5 }
}

"""

_FN_ALIAS_POSITIONS = {
    "parameter": """\
private fn use(@One, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@One.0, @Int.0)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  use(mk(@Int.0), @Int.0)
}
""",
    "tuple component": """\
private fn take(@Tuple<One, Nat> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  take(Tuple(mk(@Int.0), 1))
}
""",
    "return": """\
private fn ret(@Int -> @One)
  requires(true)
  ensures(true)
  effects(pure)
{
  mk(@Int.0)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(ret(@Int.0), 0)
}
""",
    "let": """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @One = mk(@Int.0);
  apply_fn(@One.0, 0)
}
""",
}


@pytest.mark.parametrize("position", sorted(_FN_ALIAS_POSITIONS))
def test_a_refinement_over_a_function_type_alias_is_guarded(
    position: str, tmp_path: Path,
) -> None:
    """The alias form is a guarded row at every boundary, and the run traps
    on the closure the predicate refutes (`apply_fn(·, 0) == 5`)."""
    source = _FN_ALIAS + _FN_ALIAS_POSITIONS[position]
    compiled = pipeline.compile(source, file="a.vera")
    assert compiled.ok, [d.description[:120] for d in compiled.errors]
    ran = _run(tmp_path, source, "f", "3")
    assert ran.returncode != 0 and "Refinement violation" in (ran.stdout + ran.stderr), (
        ran.stdout + ran.stderr[-300:])


def test_a_refinement_over_an_inline_function_type_is_no_guard() -> None:
    """The neighbour: the base written inline names no binder, so the row is
    listed unguardable with its reason and the module compiles."""
    source = """\
type RF = { @fn(Int -> Int) effects(pure) | true };

private fn use(@RF, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@RF.0, @Int.0)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  use(fn(@Int -> @Int) effects(pure) { @Int.0 + 5 }, @Int.0)
}
"""
    compiled = pipeline.compile(source, file="i.vera")
    assert compiled.ok, [d.description[:120] for d in compiled.errors]
    from vera.obligations.table import REASON_FUNCTION_BASE
    reasons = [row.guard.reason for row in compiled.generator._obligations.rows
               if row.kind == "refine_bind" and row.fn == "use"]
    assert reasons and set(reasons) == {REASON_FUNCTION_BASE}, reasons


def test_a_closures_return_rows_are_no_epilogue_of_the_function() -> None:
    """A refined-return closure in a self-recursive `decreases` function
    guards its own return inside the closure: the function keeps its
    `return_call` and its measure re-evaluation at the tail call."""
    source = """\
type Pos = { @Int | @Int.0 > 0 };

public fn count(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  let @Int = apply_fn(fn(@Int -> @Pos) effects(pure) { @Int.0 + 1 }, 1);
  if @Nat.0 == 0 then { 0 } else { count(@Nat.0 - 1) }
}
"""
    compiled = pipeline.compile(source, file="c.vera")
    assert compiled.ok, [d.description[:120] for d in compiled.errors]
    assert "return_call" in compiled.wat


def test_a_generic_field_at_a_refinement_is_guarded_in_an_array_literal(
    tmp_path: Path,
) -> None:
    """`[MkBox(@Int.0)]` held to `Array<Box<Pos>>`: the field's row is
    guarded by its own target type where the declared field is a variable
    and the argument records none, and the run traps on a non-positive
    value (code generation refused the program before)."""
    source = """\
type Pos = { @Int | @Int.0 > 0 };

private data Box<T> { MkBox(T) }

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Box<Pos>> = [MkBox(@Int.0)];
  0
}
"""
    compiled = pipeline.compile(source, file="b.vera")
    assert compiled.ok, [d.description[:120] for d in compiled.errors]
    ran = _run(tmp_path, source, "f", "-3")
    assert ran.returncode != 0 and "Refinement violation" in (ran.stdout + ran.stderr), (
        ran.stdout + ran.stderr[-300:])
    assert _run(tmp_path, source, "f", "3").returncode == 0


# ---------------------------------------------------------------------
# The fourth join: a value produced inside a `handle` body (#1695).  The
# table hands the requirement there as it does through a block, an `if` and
# a `match`, and lists the rows the hand-down alone produces unguarded: code
# generation hands no requirement into a handle (its coercion walk stops at
# it), so no store check is emitted there, at base or head (the follow-up
# closes it).  The verdicts are base's: a disclosure where the solver cannot
# decide, a refutation where it can.
# ---------------------------------------------------------------------

_HANDLE_VALUE = """\
type PosInt = {{ @Int | @Int.0 > 0 }};

public fn f(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects({eff})
{{
  {handle}
}}
"""

#: form -> (the handle, the effects row, the leaf the row stands at).
_HANDLE_FORMS = {
    "body": ("handle[State<Int>](@Int = 1) {\n"
             "    get(@Unit) -> { resume(@Int.0) },\n"
             "    put(@Int) -> { resume(()) }\n"
             "  } in {\n    Some(VALUE)\n  }", "pure"),
    "clause": ("handle[Exn<Int>] {\n"
               "    throw(@Int) -> { Some(VALUE) }\n"
               "  } in {\n    throw(1)\n  }", "pure"),
}


def _handle_program(form: str, value: str) -> str:
    handle, eff = _HANDLE_FORMS[form]
    return _HANDLE_VALUE.format(eff=eff, handle=handle.replace("VALUE", value))


@pytest.mark.parametrize("form", list(_HANDLE_FORMS))
def test_a_value_inside_a_handle_is_disclosed_as_at_base(
    form: str, tmp_path: Path,
) -> None:
    """Undecided: `tier3_unguarded`/E506 with the row's reason and the fix
    the user applies today; the module holds no check, as at base, and the
    run lets the payload through (the follow-up's subject)."""
    from vera.obligations import table as obligation_table

    src = _handle_program(form, "float_to_int(@Float64.0)")
    v = _verified(src)
    binds = [(o.status, o.error_code) for o in v.result.obligations
             if o.kind == "refine_bind"]
    assert binds == [("tier3_unguarded", "E506")], binds
    e506 = [d for d in v.result.diagnostics if d.error_code == "E506"]
    assert len(e506) == 1, e506
    assert obligation_table.REASON_HANDLE_VALUE in e506[0].rationale
    assert "outside" in e506[0].fix
    module = pipeline.compile(src).result
    assert pipeline.checks(module, obligation="refine_bind", function="f") == ()


# A `@Nat` return's value leaves, each discharged in its own branch's
# context (R111's finding 1 on PR #1835): two and three leaves, an `if` and
# a `match`, the violating leaf at each position.  The statuses are the
# leaves' own, in source order.
_NAT_RETURN_LEAVES = {
    "if2-violating-last": (
        "if @Int.0 > 0 then { @Int.0 } else { @Int.0 - 1 }",
        ["verified", "violated"]),
    "if2-violating-first": (
        "if @Int.0 > 0 then { @Int.0 - 5 } else { 0 - @Int.0 }",
        ["violated", "verified"]),
    "if2-both-violating": (
        "if @Int.0 > 0 then { @Int.0 - 5 } else { @Int.0 - 1 }",
        ["violated", "violated"]),
    "if3-violating-first": (
        "if @Int.0 > 10 then { @Int.0 - 20 } else "
        "{ if @Int.0 > 0 then { @Int.0 } else { 0 - @Int.0 } }",
        ["violated", "verified", "verified"]),
    "if3-violating-middle": (
        "if @Int.0 > 10 then { @Int.0 } else "
        "{ if @Int.0 > 0 then { @Int.0 - 5 } else { 0 - @Int.0 } }",
        ["verified", "violated", "verified"]),
    "if3-violating-last": (
        "if @Int.0 > 10 then { @Int.0 } else "
        "{ if @Int.0 > 0 then { @Int.0 } else { @Int.0 - 1 } }",
        ["verified", "verified", "violated"]),
    "match2-violating-last": (
        "match @Int.0 > 0 { true -> @Int.0, false -> @Int.0 - 1 }",
        ["verified", "violated"]),
    "match2-violating-first": (
        "match @Int.0 > 0 { true -> @Int.0 - 5, false -> 0 - @Int.0 }",
        ["violated", "verified"]),
    "match3-violating-first": (
        "match @Int.0 { 0 -> @Int.0 - 1, 1 -> @Int.0, _ -> @Int.0 - @Int.0 }",
        ["violated", "verified", "verified"]),
    "match3-violating-middle": (
        "match @Int.0 { 0 -> @Int.0, 1 -> @Int.0 - 2, _ -> @Int.0 - @Int.0 }",
        ["verified", "violated", "verified"]),
    "match3-violating-last": (
        "match @Int.0 { 0 -> @Int.0, 1 -> @Int.0, _ -> @Int.0 - 1 }",
        ["verified", "verified", "violated"]),
    # A `handle` is one leaf, as the table lists it (CodeRabbit on
    # cfc78e6a): the leaf beside it is discharged on its own.
    "if2-handle-leaf": (
        "if @Int.0 > 0 then { @Int.0 } else { handle[State<Int>](@Int = 0) "
        "{ get(@Unit) -> { resume(@Int.0) }, put(@Int) -> { resume(()) } } "
        "in { @Int.0 - 1 } }",
        ["verified", "violated"]),
}


def _nat_return_program(body: str) -> str:
    return ("public fn pick(@Int -> @Nat)\n  requires(true)\n  ensures(true)\n"
            f"  effects(pure)\n{{\n  {body}\n}}\n")


@pytest.mark.parametrize("shape", list(_NAT_RETURN_LEAVES))
def test_a_nat_return_leaf_is_discharged_in_its_own_context(shape: str) -> None:
    """Each value leaf of a `@Nat` return is its own record, discharged
    under its branch's path condition: a leaf that holds is `verified`, a
    leaf that can be negative is `violated` with its own E503 at the leaf,
    and no status is copied from another leaf or from the body."""
    body, want = _NAT_RETURN_LEAVES[shape]
    v = _verified(_nat_return_program(body))
    recs = sorted((o.line, o.column, o.status) for o in v.result.obligations
                  if o.kind == "nat_bind")
    assert [s for _, _, s in recs] == want, recs
    e503 = sorted((d.location.line, d.location.column)
                  for d in v.result.diagnostics if d.error_code == "E503")
    assert e503 == [(ln, col) for ln, col, s in recs if s == "violated"], e503
    assert _envelope_inconsistencies(v) == [], _envelope_inconsistencies(v)


def test_repro_r111_a_holding_nat_return_leaf_carries_no_error() -> None:
    """R111's program: the leaf under `@Int.0 > 0` holds and the `else`
    leaf does not; the E503 stands at the `else` leaf (6:40), and the leaf
    at 6:24 is `verified`."""
    v = _verified(_nat_return_program(
        "if @Int.0 > 0 then { @Int.0 } else { @Int.0 - 1 }"))
    assert _envelope_inconsistencies(v) == []
    recs = {(o.line, o.column): o.status for o in v.result.obligations
            if o.kind == "nat_bind"}
    assert recs == {(6, 24): "verified", (6, 40): "violated"}, recs
    e503 = [(d.location.line, d.location.column)
            for d in v.result.diagnostics if d.error_code == "E503"]
    assert e503 == [(6, 40)], e503


_SPANNING_VALUES = {
    "two-slot-leaves": (
        "if @Int.0 > 0 then { @Option<Int>.0 } else { @Option<Int>.0 }",
        "violated"),
    "a-holding-and-a-violating-leaf": (
        "match @Option<Int>.0 { Some(@Int) -> if @Int.0 > 0 then "
        "{ @Option<Int>.0 } else { @Option<Int>.0 }, None -> None }",
        "violated"),
    "both-leaves-holding": (
        "match @Option<Int>.0 { Some(@Int) -> if @Int.0 > 0 then "
        "{ @Option<Int>.0 } else { None }, None -> @Option<Int>.0 }",
        "verified"),
}


@pytest.mark.parametrize("shape", list(_SPANNING_VALUES))
def test_a_value_discharged_once_is_one_record_naming_its_leaf_rows(
        shape: str) -> None:
    """A value's nested refinement, discharged once for the whole value,
    whose component rows stand at several leaves, is one record at the
    value naming every one of those rows, never a copy of its status at
    each leaf; its one diagnostic stands where the record does."""
    body, want = _SPANNING_VALUES[shape]
    v = _verified(
        "type PosInt = { @Int | @Int.0 > 0 };\n"
        "public fn f(@Int, @Option<Int> -> @Option<PosInt>)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
        f"  {body}\n}}\n")
    recs = [o for o in v.result.obligations if o.kind == "refine_bind"]
    assert [(o.status, len(o.rows)) for o in recs] == [(want, 2)], recs
    e505 = [(d.location.line, d.location.column)
            for d in v.result.diagnostics if d.error_code == "E505"]
    assert e505 == ([(recs[0].line, recs[0].column)] if want == "violated"
                    else []), e505
    assert _envelope_inconsistencies(v) == [], _envelope_inconsistencies(v)


_HELD_BY_FIELDS = {
    # A field the solver does not decide (`float_to_int`): its row is
    # guarded, which proves nothing about the return's component.
    "undecided-field": (
        "public fn f(@Float64 -> @Tuple<PosInt, Int>)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n"
        "  Tuple(float_to_int(@Float64.0), 1)\n}\n"),
    # A field written as a piped stage: its record stands at the stage.
    "piped-field": (
        "public fn f(@Int -> @Tuple<PosInt, Int>)\n  requires(@Int.0 > 0)\n"
        "  ensures(true)\n  effects(pure)\n{\n  Tuple(@Int.0 |> id(), 1)\n}\n"
        "private fn id(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  @Int.0\n}\n"),
    # A piped field that is proved: found at its stage, it proves the
    # component.
    "piped-proved-field": (
        "public fn f(@Int -> @Tuple<PosInt, Int>)\n  requires(@Int.0 > 0)\n"
        "  ensures(true)\n  effects(pure)\n{\n  Tuple(@Int.0 |> keep(), 1)\n}\n"
        "private fn keep(@Int -> @Int)\n  requires(@Int.0 > 0)\n"
        "  ensures(@Int.result > 0)\n  effects(pure)\n{\n  @Int.0\n}\n"),
}


@pytest.mark.parametrize("shape", list(_HELD_BY_FIELDS))
def test_a_constructed_returns_component_is_proved_only_by_proved_fields(
        shape: str) -> None:
    """The return type's component row of a constructed body is `verified`
    only where every field record of the construction is `verified`
    (CodeRabbit's finding on PR #1835 at `_check_nested_refinement_obligation`):
    a field left to its check or refuted proves nothing, and the component
    row is left to the return's check; a proved field written as a piped
    stage is found where its record stands, at the stage."""
    v = _verified("type PosInt = { @Int | @Int.0 > 0 };\n"
                  + _HELD_BY_FIELDS[shape])
    table = v.result.table
    assert table is not None
    ret = [o.status for o in v.result.obligations if o.kind == "refine_bind"
           and any(table.rows[r].evaluation == ("return",) for r in o.rows)]
    assert ret == (["verified"] if shape == "piped-proved-field"
                   else ["tier3"]), ret


def test_repro_a_guarded_field_proves_no_return_component() -> None:
    """The reported instance, unsampled: a field left to its check leaves
    the constructed return's component row `tier3`, not `verified`."""
    test_a_constructed_returns_component_is_proved_only_by_proved_fields(
        "undecided-field")


def test_repro_a_value_record_is_not_copied_to_its_leaves() -> None:
    """The reported shape, unsampled: one record at the value naming both
    leaf rows, with its one E505 where it stands."""
    test_a_value_discharged_once_is_one_record_naming_its_leaf_rows(
        "a-holding-and-a-violating-leaf")


_UNTAKEN_READS = {
    # A literal index out of range in a branch that never runs.
    "literal-dead-branch": "if false then { @Array<Int>.0[0 - 1] } else { 0 - 1 }",
    # An index in range only where its branch runs: read unguarded, its
    # fact would confine the parameter on the other branch too.
    "parameter-branch": (
        "if @Int.0 > 100 then { @Array<Int>.0[@Int.0 - 50] } else { @Int.0 }"),
    # A refined `let` (#1563's post-fact) whose bind is refused, in a branch
    # that never runs.
    "refused-let-dead-branch": (
        "if false then { let @Pos = 0 - 1; @Pos.0 } else { 0 - 1 }"),
    # A refined `let` of a value the solver does not translate (the
    # refinement guard's post-fact over a fresh value), in a branch that
    # never runs, whose refinement no value satisfies.
    "opaque-let-dead-branch": (
        "if false then { let @Empty = float_to_int(1.5); @Empty.0 } "
        "else { 0 - 1 }"),
    # A `match` arm binder at a refinement (the guarded fresh value) in a
    # branch that never runs.
    "arm-binder-dead-branch": (
        "if false then { match Some(0 - 1) { Some(@Pos) -> @Pos.0, "
        "None -> 1 } } else { 0 - 1 }"),
}


@pytest.mark.parametrize("shape", list(_UNTAKEN_READS))
def test_an_element_reads_fact_holds_only_on_its_branch(shape: str) -> None:
    """A post-fact (an element read's index in range, #1696 m04; a
    refined bind's predicate, guarded or refused, #1563; a guarded binder's
    fresh value) holds where its read or bind runs, under its branch's
    conditions, never on a path it is not on (CodeRabbit on 3332cdfd): the
    argument the other branch yields is refuted at the callee's
    `requires`."""
    v = _verified(
        "type Pos = { @Int | @Int.0 > 0 };\n"
        "type Empty = { @Int | @Int.0 > 0 && @Int.0 < 0 };\n"
        "private fn g(@Int -> @Int)\n  requires(@Int.0 >= 0)\n  ensures(true)\n"
        "  effects(pure)\n{\n  @Int.0\n}\n"
        "public fn f(@Array<Int>, @Int -> @Int)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n"
        f"  g({_UNTAKEN_READS[shape]})\n}}\n")
    pre = [o.status for o in v.result.obligations if o.kind == "call_pre"]
    assert pre == ["violated"], pre
    assert "E501" in _codes(v)


def test_repro_an_untaken_element_read_proves_no_precondition() -> None:
    """The reported instance, unsampled."""
    test_an_element_reads_fact_holds_only_on_its_branch("literal-dead-branch")


def test_repro_a_row_two_discharges_reach_reports_one_error() -> None:
    """A `map_insert` value is one row (#1608): the call-argument walk and
    the stored-value walk both refute `-3`, and the site's one record keeps
    one E503; the other discharge's error goes with its record."""
    v = _verified(
        "public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n"
        '  let @Map<String, Nat> = map_insert(map_new(), "k", -3);\n'
        '  match map_get(@Map<String, Nat>.0, "k") {\n'
        "    Some(@Int) -> @Int.0,\n    None -> 7\n  }\n}\n")
    recs = [o.status for o in v.result.obligations if o.kind == "nat_bind"]
    assert recs == ["violated"], recs
    e503 = [d for d in v.result.diagnostics if d.error_code == "E503"]
    assert len(e503) == 1, [d.description for d in e503]
    assert _envelope_inconsistencies(v) == []


@pytest.mark.parametrize("form", list(_HANDLE_FORMS))
def test_a_refuted_value_inside_a_handle_keeps_its_record(form: str) -> None:
    """Refutable: the E505 has its `violated` record, at the row.  An `Exn`
    clause's value is one the requirement reaches by the table's hand-down
    alone, with no refined target at the position, so there the row is
    left to its check, which it has none of: base's disclosure, at the row
    (#1836)."""
    v = _verified(_handle_program(form, "0 - 5"))
    viol = [(o.status, o.error_code, o.line) for o in v.result.obligations
            if o.kind == "refine_bind"]
    want = ("violated", "E505") if form == "body" else ("tier3_unguarded", "E506")
    assert [x[:2] for x in viol] == [want], viol
    assert _envelope_inconsistencies(v) == []


_HAND_DOWN_NAT = """\
private fn h(@Map<String, Tuple<Nat, Int>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

public fn g(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = h(map_insert(map_new(), "k", if @Int.0 > 0 then { Tuple(@Int.0, 2) } else { Tuple(@Int.0, 2) }));
  assert(@Int.1 >= 0);
  0
}
"""


def test_repro_a_hand_down_nat_value_is_left_to_its_check(tmp_path: Path) -> None:
    """A `Nat` component that only the table's hand-down reaches (a
    `map_insert` value at a call argument, through a join) is held to `Nat`
    by no position the walk reaches: its rows are left to the check that
    reads them, `tier3`, as at base, and never discharged later in a
    context that an `assert` after it has added to (CodeRabbit on PR
    #1843).  The check traps the negative payload."""
    v = _verified(_HAND_DOWN_NAT)
    nat = [(o.status, o.error_code) for o in v.result.obligations
           if o.kind == "nat_bind"]
    assert nat == [("tier3", ""), ("tier3", "")], nat
    assert "E503" not in _codes(v)
    out = _run(tmp_path, _HAND_DOWN_NAT, "g", "-5")
    assert "Negative value bound into a @Nat slot" in out.stdout + out.stderr


_HAND_DOWN_MAP_ARG = """\
type Pos = { @Int | @Int.0 > 0 };

private fn consume(@Map<String, Pos> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  map_size(@Map<String, Pos>.0)
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  consume(map_insert(map_new(), "a", @Int.0))
}
"""

_HAND_DOWN_SET_LET = """\
type Pos = { @Int | @Int.0 > 0 };

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Set<Pos> = set_add(set_new(), @Int.0);
  set_size(@Set<Pos>.0)
}
"""


def test_repro_a_hand_down_value_record_is_never_verified() -> None:
    """A value that only the table's hand-down holds to a refinement (a
    `map_insert` value at a call argument, a `set_add` element at a `let`)
    is left to its check, `tier3` at its site, and never proved: no position
    states the refinement for the solver, and `-5` is a value either
    program admits (R112 on PR #1843: a mutant that recorded these
    `verified` passed every matrix).  The `Set` element's record keeps base's
    E541, the claim with no check that answers it."""
    v = _verified(_HAND_DOWN_MAP_ARG)
    at = next(i for i, line in enumerate(_HAND_DOWN_MAP_ARG.splitlines(), 1)
              if "map_insert" in line)
    site = [(o.status, o.line) for o in v.result.obligations
            if o.kind == "refine_bind" and o.line == at]
    assert site == [("tier3", at)], site
    v = _verified(_HAND_DOWN_SET_LET)
    recs = [o.status for o in v.result.obligations if o.kind == "refine_bind"]
    assert recs == ["tier3"], recs
    assert "E541" in _codes(v)


_SUBPATTERN_AFTER_A_WILDCARD = """\
type Pos = { @Int | @Int.0 > 0 };

private data P {
  MkP(Int, Int, Int)
}

public fn f(@Option<P> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<P>.0 {
    Some(MkP(_, @Nat, @Pos)) -> nat_to_int(@Nat.0) + @Pos.0,
    None -> 0
  }
}
"""

_UNPROJECTED_SUBPATTERN_AFTER_A_WILDCARD = """\
type Pos = { @Int | @Int.0 > 0 };

private data P {
  MkP(Int, Int, Int)
}

private data Wrap {
  MkWrap(P)
}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match MkWrap(MkP(@Int.0, @Int.0, @Int.0)) {
    MkWrap(MkP(_, @Nat, @Pos)) -> nat_to_int(@Nat.0) + @Pos.0
  }
}
"""

_LITERAL_DESTRUCTURE_BINDER = """\
type R = { @Option<Int> | @Option<Int>.0 == Some(1) };

public fn f(@Unit -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @R> = Tuple(1, Some(1));
  @R.0
}
"""


def _narrowing_records(source: str) -> list[tuple[object, ...]]:
    """Each narrowing record whole (its function, kind, status, site, code
    and text), then each diagnostic's code and first line."""
    v = _verified(source)
    return [(o.fn_name, o.kind, o.status, o.line, o.column, o.error_code,
             o.expr_text)
            for o in v.result.obligations
            if o.kind in ("nat_bind", "refine_bind")] + [
        (d.error_code, d.description.splitlines()[0])
        for d in v.result.diagnostics]


def test_repro_lane_a_binder_after_a_wildcard_sub_pattern_is_discharged() -> None:
    """A nested constructor sub-pattern whose first field is a wildcard and
    whose later fields bind at `Nat` and at a refinement: each binder is
    discharged at its own row over its projected field, as at base (the
    Mutation (diff) lane's `_obligate_subpattern_term` survivors on PR
    #1843: no cell entered a binder after a non-binding sub-pattern)."""
    assert _narrowing_records(_SUBPATTERN_AFTER_A_WILDCARD) == [
        ("f", "nat_bind", "violated", 13, 17, "E503", "@Nat"),
        ("f", "refine_bind", "violated", 13, 23, "E505", "@Pos"),
        ("E503", "@Int value narrowing into a @Nat ADT sub-pattern bind in "
                 "'f' may be negative."),
        ("E505", "Value narrowing into a refined ADT sub-pattern bind in 'f' "
                 "may violate the refinement predicate `@Int.0 > 0`."),
    ]


def test_repro_lane_an_unprojected_binder_after_a_wildcard_is_left_to_its_check() -> None:
    """The same pattern nested under a literal construction, whose fields
    the walk does not project (`_record_nested_subpattern_fallbacks`): each
    binder's row is left to its check, the `Nat` one `tier3`, the refined
    one disclosed (E506), as at base (the lane's survivors in that function
    on PR #1843)."""
    records = _narrowing_records(_UNPROJECTED_SUBPATTERN_AFTER_A_WILDCARD)
    assert records[:2] == [
        ("go", "nat_bind", "tier3", 17, 19, "", "@Nat"),
        ("go", "refine_bind", "tier3", 17, 25, "E506", "@Pos"),
    ], records
    assert [r[0] for r in records[2:]] == ["E506"], records
    assert records[2][1].startswith(
        "Refinement predicate at a ADT sub-pattern bind in 'go'"), records


def test_repro_lane_a_literal_destructure_binder_is_left_to_its_check() -> None:
    """A literal `Tuple` destructure's refined binder: the component's
    record is the component's row (disclosed, E506), and the binder's row is
    left to the destructure's check, `tier3`, as at base (the lane's
    `_leave_binder_rows` survivors on PR #1843; the `_1466` cells that pin it
    run at `--matrix=full` only)."""
    records = _narrowing_records(_LITERAL_DESTRUCTURE_BINDER)
    assert records[:2] == [
        ("f", "refine_bind", "tier3_unguarded", 8, 34, "E506", "Some(1)"),
        ("f", "refine_bind", "tier3", 8, 20, "", "@R"),
    ], records


_OWN_TYPE_SUB_PATTERN_BINDERS = """\
type Fpos = { @Float64 | @Float64.0 >= 0.0 };

type Pos = { @Int | @Int.0 > 0 };

private data Q {
  MkQ(Int, Fpos, Pos, Tuple<Int, Int>, Nat, Int)
}

public fn f(@Option<Q> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Q>.0 {
    Some(MkQ(_, @Fpos, @Pos, @Tuple<Int, Nat>, @Nat, @Int)) -> @Pos.0 + nat_to_int(@Nat.0) + @Int.0,
    None -> 0
  }
}
"""

_UNPROJECTED_OWN_TYPE_SUB_PATTERN_BINDERS = """\
type Fpos = { @Float64 | @Float64.0 >= 0.0 };

type Pos = { @Int | @Int.0 > 0 };

private data Q {
  MkQ(Int, Fpos, Pos, Tuple<Int, Int>, Nat, Int)
}

private data W {
  MkW(Q)
}

public fn g(@Fpos, @Pos, @Nat, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match MkW(MkQ(@Int.0, @Fpos.0, @Pos.0, Tuple(@Int.0, @Int.0), @Nat.0, @Int.0)) {
    MkW(MkQ(_, @Fpos, @Pos, @Tuple<Int, Nat>, @Nat, @Int)) -> @Pos.0 + nat_to_int(@Nat.0) + @Int.0
  }
}
"""


def test_repro_lane_sub_pattern_binders_at_their_fields_own_types() -> None:
    """Sub-pattern binders after a wildcard at a refined field's own type
    (a `Float64` and an `Int` base), at a composite coercion (`Tuple<Int,
    Nat>` over `Tuple<Int, Int>`) and at `Nat` and `Int` fields: the own-type
    and composite binders' rows are left to their checks, `tier3`, the rest
    take no record, as at base, over a projected scrutinee (the lane's
    `_obligate_subpattern_term` survivors on PR #1843: no cell entered a
    binder that does not narrow)."""
    assert _narrowing_records(_OWN_TYPE_SUB_PATTERN_BINDERS) == [('f', 'refine_bind', 'tier3', 15, 17, '', '@Fpos'), ('f', 'refine_bind', 'tier3', 15, 24, '', '@Pos'), ('f', 'nat_bind', 'tier3', 15, 30, '', '@Tuple<Int, Nat> [Tuple.1]')]


def test_repro_lane_unprojected_binders_at_their_fields_own_types() -> None:
    """The same binders nested under a literal construction
    (`_record_nested_subpattern_fallbacks`), as at base."""
    assert _narrowing_records(_UNPROJECTED_OWN_TYPE_SUB_PATTERN_BINDERS) == [('g', 'refine_bind', 'verified', 13, 14, '', '@Fpos'), ('g', 'refine_bind', 'verified', 13, 21, '', '@Pos'), ('g', 'nat_bind', 'violated', 18, 56, 'E503', '@Int.0'), ('g', 'refine_bind', 'tier3', 19, 16, '', '@Fpos'), ('g', 'refine_bind', 'tier3', 19, 23, '', '@Pos'), ('g', 'nat_bind', 'tier3', 19, 29, '', '@Tuple<Int, Nat> [Tuple.1]'), ('E503', "@Int value narrowing into a @Nat tuple component in 'g' may be negative.")]


_SUB_PATTERN_OVER_A_REFINED_FIELD = """\
type Pos = { @Int | @Int.0 > 0 };

type NonNeg = { @Int | @Int.0 >= 0 };

private data R {
  MkR(Pos)
}

public fn f(@Option<R> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<R>.0 {
    Some(MkR(@NonNeg)) -> @NonNeg.0,
    None -> 0
  }
}

public fn g(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<R> = Some(MkR(@Int.0));
  match @Option<R>.0 {
    Some(MkR(@NonNeg)) -> @NonNeg.0,
    None -> 0
  }
}
"""


def test_repro_lane_a_sub_pattern_binder_reads_its_fields_refinement() -> None:
    """A `NonNeg` binder over a `Pos` field: over an opaque source (a
    parameter) the field's own refinement is the binder's premise and the
    bind proves; over a source the walk follows to its construction, the
    construction's argument is, and the construction's own row is refuted
    (E505), as at base (the lane's `source_ty` survivors in
    `_obligate_subpattern_term` on PR #1843)."""
    assert _narrowing_records(_SUB_PATTERN_OVER_A_REFINED_FIELD) == [('f', 'refine_bind', 'verified', 15, 14, '', '@NonNeg'), ('g', 'refine_bind', 'violated', 25, 29, 'E505', '@Int.0'), ('g', 'refine_bind', 'verified', 27, 14, '', '@NonNeg'), ('E505', "Value narrowing into a refined constructor field in 'g' may violate the refinement predicate `@Int.0 > 0`.")]




_CLOSURE_RETURN_WITH_A_REFINED_COMPONENT = """\
type Pos = { @Int | @Int.0 > 0 };

private fn mk(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Int.0, @Int.0)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Int -> @Pos) effects(pure) { @Int.0 }, @Int.0)
}

public fn b(@Int -> @Tuple<Pos, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Int -> @Tuple<Pos, Nat>) effects(pure) { mk(@Int.0) }, @Int.0)
}

public fn k(@Int -> @Tuple<Pos, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Int -> @Tuple<Pos, Nat>) effects(pure) { if @Int.0 > 0 then { mk(@Int.0) } else { mk(0 - @Int.0) } }, @Int.0)
}
"""


def test_repro_a_closure_return_s_refined_component_keeps_its_own_record() -> None:
    """A closure returning `Tuple<Pos, Nat>` from a `Tuple<Int, Int>` call,
    directly and through an `if`: each value leaf's components and the
    closure return type's components keep their own `tier3` records, with
    no disclosure at the closure return, record for record as at base.
    At 030734a9 the closure arm's refined branch fired on the component's
    row: the leaf's record took an `E506` and a closure-return warning, and
    the return type's `[Tuple.0]` row had no record (PR #1843)."""
    assert _narrowing_records(_CLOSURE_RETURN_WITH_A_REFINED_COMPONENT) == [
        ('f', 'refine_bind', 'tier3', 16, 45, 'E506', '{ @Int.0 }'),
        ('b', 'nat_bind', 'tier3', 24, 57, '', 'mk(@Int.0) [Tuple.1]'),
        ('b', 'refine_bind', 'tier3', 24, 57, '', 'mk(@Int.0) [Tuple.0]'),
        ('b', 'refine_bind', 'tier3', 24, 24, '', '@Tuple<Pos, Nat> [Tuple.0]'),
        ('b', 'refine_bind', 'tier3', 24, 24, '', '@Tuple<Pos, Nat> [Tuple.1]'),
        ('b', 'refine_bind', 'tier3', 19, 22, 'E506', '@Tuple<Pos, Nat> [Tuple.0]'),
        ('b', 'refine_bind', 'tier3', 19, 22, 'E506', '@Tuple<Pos, Nat> [Tuple.1]'),
        ('k', 'nat_bind', 'tier3', 32, 78, '', 'mk(@Int.0) [Tuple.1]'),
        ('k', 'refine_bind', 'tier3', 32, 78, '', 'mk(@Int.0) [Tuple.0]'),
        ('k', 'nat_bind', 'tier3', 32, 98, '', 'mk(0 - @Int.0) [Tuple.1]'),
        ('k', 'refine_bind', 'tier3', 32, 98, '', 'mk(0 - @Int.0) [Tuple.0]'),
        ('k', 'refine_bind', 'tier3', 32, 24, '', '@Tuple<Pos, Nat> [Tuple.0]'),
        ('k', 'refine_bind', 'tier3', 32, 24, '', '@Tuple<Pos, Nat> [Tuple.1]'),
        ('k', 'refine_bind', 'tier3', 27, 22, 'E506', '@Tuple<Pos, Nat> [Tuple.0]'),
        ('k', 'refine_bind', 'tier3', 27, 22, 'E506', '@Tuple<Pos, Nat> [Tuple.1]'),
        ('E506', "Refinement predicate at a closure return in 'f' could not be verified statically; it will be checked at run time. To prove it statically, add a `requires(...)` implying the predicate or guard the binding with an `if`."),
        ('E506', "Refinement predicate at a return type in 'b' could not be verified statically; it will be checked at run time. To prove it statically, add a `requires(...)` implying the predicate or guard the binding with an `if`."),
        ('E506', "Refinement predicate at a return type in 'k' could not be verified statically; it will be checked at run time. To prove it statically, add a `requires(...)` implying the predicate or guard the binding with an `if`."),
    ]

_REFINED_CLOSURE_RETURN_OVER_A_NAT_COMPONENT = """\
type PT = { @Tuple<Int, Nat> | true };

private fn mk(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Int.0, @Int.0)
}

public fn c(@Int -> @PT)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Int -> @PT) effects(pure) { mk(@Int.0) }, @Int.0)
}

public fn d(@Int -> @PT)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Int -> @PT) effects(pure) { if @Int.0 > 0 then { mk(@Int.0) } else { mk(0 - @Int.0) } }, @Int.0)
}
"""


def test_repro_lane_a_refined_closure_return_keeps_its_nat_components() -> None:
    """A closure whose return type is a refinement over `Tuple<Int, Nat>`,
    returning a `Tuple<Int, Int>` call, directly and through an `if`: the
    body's refined record is disclosed at the closure return (E506), and the
    `Nat` component of each value leaf and of the return type is left to the
    boundary's check, `tier3`, as at base (the Mutation (diff) lane's
    `_binding_closure` survivors on PR #1843: no cell held a closure's
    boundary components beside a refined return)."""
    assert _narrowing_records(_REFINED_CLOSURE_RETURN_OVER_A_NAT_COMPONENT) == [
        ("c", "nat_bind", "tier3", 16, 44, "", "mk(@Int.0) [Tuple.1]"),
        ("c", "refine_bind", "tier3", 16, 44, "E506", "{ mk(@Int.0) }"),
        ("c", "refine_bind", "tier3", 16, 24, "", "@PT [Tuple.1]"),
        ("c", "refine_bind", "tier3", 16, 3, "E506",
         "{ apply_fn(fn(@Int -> @PT) effects(pure) { mk(@Int.0) }, @Int.0) }"),
        ("c", "refine_bind", "tier3", 11, 22, "", "@PT [Tuple.1]"),
        ("d", "nat_bind", "tier3", 24, 65, "", "mk(@Int.0) [Tuple.1]"),
        ("d", "nat_bind", "tier3", 24, 85, "", "mk(0 - @Int.0) [Tuple.1]"),
        ("d", "refine_bind", "tier3", 24, 44, "E506",
         "{ if @Int.0 > 0 then { mk(@Int.0) } else { mk(0 - @Int.0) } }"),
        ("d", "refine_bind", "tier3", 24, 24, "", "@PT [Tuple.1]"),
        ("d", "refine_bind", "tier3", 24, 3, "E506",
         "{ apply_fn(fn(@Int -> @PT) effects(pure) { if @Int.0 > 0 then { mk(@Int.0) } else { mk(0 - @Int.0) } }, @Int.0) }"),
        ("d", "refine_bind", "tier3", 19, 22, "", "@PT [Tuple.1]"),
        ("E506", "Refinement predicate at a closure return in 'c' could not "
                 "be verified statically; it will be checked at run time. To "
                 "prove it statically, add a `requires(...)` implying the "
                 "predicate or guard the binding with an `if`."),
        ("E506", "Refinement predicate at a return type in 'c' could not be "
                 "verified statically; it will be checked at run time. To "
                 "prove it statically, add a `requires(...)` implying the "
                 "predicate or guard the binding with an `if`."),
        ("E506", "Refinement predicate at a closure return in 'd' could not "
                 "be verified statically; it will be checked at run time. To "
                 "prove it statically, add a `requires(...)` implying the "
                 "predicate or guard the binding with an `if`."),
        ("E506", "Refinement predicate at a return type in 'd' could not be "
                 "verified statically; it will be checked at run time. To "
                 "prove it statically, add a `requires(...)` implying the "
                 "predicate or guard the binding with an `if`."),
    ]


_DESTRUCTURE_OF_AN_OPAQUE_SOURCE = """\
type Pos = { @Int | @Int.0 > 0 };

type NonNeg = { @Int | @Int.0 >= 0 };

type MkPair = fn(Int -> Tuple<Pos, Int>) effects(pure);

public fn f(@MkPair, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@NonNeg, @Int> = apply_fn(@MkPair.0, @Int.0);
  @NonNeg.0 + @Int.0
}
"""


def test_repro_lane_a_destructure_binder_reads_an_opaque_sources_field_type() -> None:
    """A non-literal destructure of a closure application's `Tuple<Pos,
    Int>`: the source is opaque, so the component's declared `Pos` is the
    `NonNeg` binder's premise and the bind proves, as at base (the lane's
    `_obligate_destructure_narrowings` survivors on PR #1843: no cell
    destructured an opaque source whose term carries no fact)."""
    assert _narrowing_records(_DESTRUCTURE_OF_AN_OPAQUE_SOURCE) == [
        ("f", "refine_bind", "verified", 12, 14, "", "@NonNeg"),
    ]

def test_the_handle_values_fix_is_a_guarded_construction(tmp_path: Path) -> None:
    """The fix text applied: the payload bound outside the handle and the
    value constructed from it is a checked store (`tier3`, no disclosure),
    and the run is refused there."""
    src = _HANDLE_VALUE.format(eff="pure", handle=(
        "let @Int = handle[State<Int>](@Int = 1) {\n"
        "    get(@Unit) -> { resume(@Int.0) },\n"
        "    put(@Int) -> { resume(()) }\n"
        "  } in {\n    float_to_int(@Float64.0)\n  };\n  Some(@Int.0)"))
    v = _verified(src)
    assert [(o.status, o.error_code) for o in v.result.obligations
            if o.kind == "refine_bind"] == [("tier3", "E506")]
    assert "E506" not in [d.error_code for d in v.result.diagnostics
                          if "no runtime check" in d.description]
    out = _run(tmp_path, src, "f", "-5.0")
    assert "Refinement violation" in out.stdout + out.stderr


_SAME_TYPE_ARGUMENT = """\
type PosInt = { @Int | @Int.0 > 0 };

private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}

private fn consume(@Option<PosInt> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<PosInt>.0 {
    Some(@PosInt) -> @PosInt.0,
    None -> 1
  }
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  consume(mk(@Float64.0))
}
"""


def test_no_record_is_made_at_a_site_with_no_row() -> None:
    """The traversal discharges a node only where the table lists a row
    (#1836): at a site with none, here an argument of exactly its
    parameter's type, nothing is discharged, so no record is made there to
    be dropped, and no diagnostic stands there."""
    from vera import verifier as vmod

    rowless: list[tuple[int, int]] = []
    real = vmod.ContractVerifier._settle_rows

    def settle(self, decl, start, made, *, premise=None):  # type: ignore[no-untyped-def]
        rowless.extend((r.line, r.column) for r in made
                       if r.kind in vmod._TABLE_KINDS and not r.rows)
        return real(self, decl, start, made, premise=premise)

    vmod.ContractVerifier._settle_rows = settle  # type: ignore[method-assign]
    try:
        v = _verified(_SAME_TYPE_ARGUMENT)
    finally:
        vmod.ContractVerifier._settle_rows = real  # type: ignore[method-assign]
    site = (27, 11)
    assert rowless == [], rowless
    assert [o for o in v.result.obligations if (o.line, o.column) == site] == []
    assert [d for d in v.result.diagnostics
            if (d.location.line, d.location.column) == site] == []
