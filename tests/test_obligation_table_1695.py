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
cells hold the nine lines that do not reproduce where they are.  Every red
cell carries the non-strict `_RED` marker until the table lands, as the
composite-coercion instrument did before #1818 (PR #1818's first commit).
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

#: Red until the table lands; removed with the change (never strict: a cell
#: this marker carries is one the change turns green).
_RED = pytest.mark.xfail(strict=False, reason="red until the obligation table lands (#1695)")

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


@_RED
def test_the_verifier_claims_no_guard() -> None:
    """No `*guarded=` argument in `vera/verifier.py`: the verifier reads
    whether a row is guarded from the row and never predicts it."""
    claims = _guard_claims(ROOT / "vera" / "verifier.py")
    assert claims == [], claims


@_RED
def test_the_verifier_defines_no_mirror_of_code_generation() -> None:
    text = (ROOT / "vera" / "verifier.py").read_text(encoding="utf-8")
    defined = [name for name in _MIRRORS
               if re.search(rf"^\s*(def |){name}\b", text, re.MULTILINE)]
    assert defined == [], defined


@_RED
def test_a_check_is_recorded_by_its_row() -> None:
    """`WasmContext._record_check` takes the row the check is the runtime
    half of, so an `EmittedCheck` names it."""
    from vera.trap_registry import EmittedCheck
    from vera.wasm.context import WasmContext

    params = inspect.signature(WasmContext._record_check).parameters
    assert "row" in params, list(params)
    assert "row" in EmittedCheck.__dataclass_fields__


@_RED
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


@_RED
def test_the_gates_carry_no_known_mismatch() -> None:
    """`scripts/check_reconciliation.py`'s `KNOWN` and the generator's
    `KNOWN_CLASSES` are both empty: no mismatch is allowlisted."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "_gate_1695", ROOT / "scripts" / "check_reconciliation.py")
    assert spec is not None and spec.loader is not None
    gate = importlib.util.module_from_spec(spec)
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


@_RED
def test_repro_1598_the_int_min_division_is_a_row() -> None:
    """`INT_MIN / -1` is an `int_overflow` row of the division, `tier3` under
    `requires(@Int.1 != 0)`, and the module's check answers it."""
    v = _verified(_SAFE_DIVIDE)
    rows = _records(v, "int_overflow")
    assert [r for r in rows if r[1] == 7] == [("tier3", 7, 3)], rows
    assert not [c for c in _codes(v) if c in ("E541", "W004")], _codes(v)


@_RED
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


@_RED
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


@_RED
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


@_RED
def test_repro_1607_an_ensures_over_an_array_result_is_disclosed_unguarded() -> None:
    v = _verified(_QUANTIFIED_ENSURES)
    rows = [r for r in _records(v, "ensures") if r[1] == 3]
    assert rows == [("tier3_unguarded", 3, 3)], _records(v, "ensures")
    assert "E541" not in _codes(v)


@_RED
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


@_RED
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


@_RED
def test_repro_1642_one_row_per_guarded_component() -> None:
    """The opaque argument of a tuple-typed parameter: one `refine_bind` row
    per component, each answered by the callee's component guard."""
    v = _verified(_PARTIAL_COMPONENTS)
    rows = [r for r in _records(v, "refine_bind") if r[1] == 25]
    assert rows == [("tier3", 25, 5), ("tier3", 25, 5)], _records(v, "refine_bind")
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


@_RED
def test_repro_1782_a_guarded_clause_binder_is_one_row() -> None:
    v = _verified(_CLAUSE_BINDER)
    assert _records(v, "nat_bind") == [("tier3", 5, 11)], _records(v, "nat_bind")
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


@_RED
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


@_RED
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


@_RED
def test_repro_1725_an_arm_binder_narrowing_an_effect_row_is_disclosed() -> None:
    v = _verified(_EFFECT_ROW)
    assert _records(v, "refine_bind") == [("tier3_unguarded", 12, 9)], _records(v, "refine_bind")
    e506 = [d for d in v.warnings if d.error_code == "E506"]
    assert e506 and "effect row" in e506[0].rationale, [d.rationale[:200] for d in e506]


@_RED
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


@_RED
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


@_RED
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


@_RED
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
