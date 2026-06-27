"""#807 — Tier-1 Z3 modeling for the modelable Float64 builtins deferred from
#797: `float_clamp`, `int_to_float`, `float_to_int`.

Follow-up to the #392 `smt.py` soundness audit (#797 mapped `@Float64` to
`z3.FPSort(11, 53)`).  Three builtins stayed Tier-3 and are modeled here:

  - `float_clamp(v, lo, hi)` — pure Float64; modeled unconditionally with a
    *faithful* WASM `f64.min(f64.max(v, lo), hi)` semantics (NaN-propagating,
    ±0-correct).  Z3's own `fp.min`/`fp.max` DIVERGE from WASM on NaN (they
    return the non-NaN operand), so a naive `fpMin`/`fpMax` model would be
    UNSOUND — test_clamp_nan_propagation_not_dropped guards exactly that.

  - `int_to_float(n)` / `float_to_int(x)` — cross the Int↔Float boundary.  Z3's
    symbolic Int↔Real↔FP reasoning is unreliable (it returns spurious `sat`
    counterexamples that don't satisfy their own constraints, non-
    deterministically across timeouts).  So these are modeled at Tier 1 ONLY
    for a *concrete* (constant-foldable) argument, where Z3 is just constant-
    folding; a symbolic argument defers to Tier 3 (sound — `float_to_int`'s
    `i64.trunc_f64_s` traps natively on NaN/Inf/out-of-range).  This matches the
    audit principle: defer to Tier 3 what Z3 cannot SOUNDLY model.

  - `float_to_int` is partial (traps), so a concrete arg additionally gets a
    domain obligation (E529): NaN / Inf / out-of-i64-range is a compile error.

Written test-first: each FAILS on the pre-#807 verifier (where all three defer
to Tier 3, so the modeled obligations land as `tier3`, not `verified`/
`violated`).
"""

from __future__ import annotations

import math
import tempfile

import pytest
import z3

from vera.parser import parse_to_ast, parse_file
from vera.transform import transform
from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as compile_vera, execute
from vera.codegen.api import WasmTrapError
from vera.errors import Diagnostic
from vera.smt import _FLOAT64_SORT, _wasm_fp_max, _wasm_fp_min
from vera.verifier import VerifyResult, verify


def _verify(source: str) -> VerifyResult:
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast, source)
    return verify(
        ast, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


def _ok(result: VerifyResult) -> bool:
    return not any(d.severity == "error" for d in result.diagnostics)


def _ens(result: VerifyResult) -> list[object]:
    return [o for o in result.obligations if o.kind == "ensures"]


# --------------------------------------------------------------------------
# Verify-vs-run differential helpers (#807).  The codegen for these builtins is
# the authoritative runtime semantics; the differential confirms the Z3 model
# AGREES with wasmtime bit-for-bit (NaN, ±0, ±inf, ties).
# --------------------------------------------------------------------------

# (Vera source expression, Python float) for each interesting Float64 value.
_FLOAT_VALUES: dict[str, tuple[str, float]] = {
    "nan": ("nan()", math.nan),
    "+inf": ("infinity()", math.inf),
    "-inf": ("0.0 - infinity()", -math.inf),
    "+0": ("0.0", 0.0),
    "-0": ("(0.0 - 1.0) * 0.0", -0.0),  # IEEE: +0 * -1 = -0
    "2.5": ("2.5", 2.5),
    "-2.5": ("0.0 - 2.5", -2.5),
    "0.5": ("0.5", 0.5),
    "1.0": ("1.0", 1.0),
    "-1.0": ("0.0 - 1.0", -1.0),
}


def _run_float_expr(body: str) -> float:
    """Compile and run `{ <body> }` returning the raw f64 (NaN/sign preserved)."""
    src = (
        "public fn f(@Unit -> @Float64)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        f"{{ {body} }}\n"
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as fh:
        fh.write(src)
        fh.flush()
        path = fh.name
    result = compile_vera(transform(parse_file(path)), source=src, file=path)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"compile errors: {[d.description for d in errors]}"
    value = execute(result, fn_name="f").value
    assert isinstance(value, float), f"expected float, got {value!r}"
    return value


def _py_to_z3fp(x: float) -> z3.FPRef:
    if math.isnan(x):
        return z3.fpNaN(_FLOAT64_SORT)
    if math.isinf(x):
        return (z3.fpPlusInfinity(_FLOAT64_SORT) if x > 0
                else z3.fpMinusInfinity(_FLOAT64_SORT))
    if x == 0.0:
        return (z3.fpMinusZero(_FLOAT64_SORT) if math.copysign(1.0, x) < 0
                else z3.fpPlusZero(_FLOAT64_SORT))
    return z3.FPVal(x, _FLOAT64_SORT)


def _model_matches_runtime(model: z3.FPRef, runtime: float) -> bool:
    """True iff the simplified Z3 model term is BIT-IDENTICAL to the runtime
    float — NaN↔NaN, and otherwise equal value AND equal zero-sign (so +0 and
    -0 are distinguished, unlike bare fpEQ)."""
    m = z3.simplify(model)
    if math.isnan(runtime):
        return z3.is_true(z3.simplify(z3.fpIsNaN(m)))
    rt = _py_to_z3fp(runtime)
    same = z3.And(
        z3.fpEQ(m, rt),
        z3.fpIsNegative(m) == z3.fpIsNegative(rt),
    )
    return z3.is_true(z3.simplify(same))


class TestFloatClampTier1_807:
    def test_clamp_in_range_verifies(self) -> None:
        # Sound contract: for non-NaN x, float_clamp(x, 0.0, 1.0) ∈ [0,1] so
        # result >= 0.0.  Pre-#807 float_clamp deferred to Tier 3 → the ensures
        # could not be modeled (tier3).  With the faithful model it discharges.
        result = _verify("""
public fn cl(@Float64 -> @Float64)
  requires(!float_is_nan(@Float64.0))
  ensures(@Float64.result >= 0.0)
  effects(pure)
{ float_clamp(@Float64.0, 0.0, 1.0) }
""")
        ens = _ens(result)
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert _ok(result), [d.description for d in result.diagnostics]

    def test_clamp_nan_propagation_not_dropped(self) -> None:
        # SOUNDNESS GUARD distinguishing the faithful model from a naive
        # z3.fpMin/fpMax one.  Runtime f64.min/f64.max PROPAGATE NaN, so
        # float_clamp(NaN, 0, 1) = NaN and `!float_is_nan(result)` is FALSE at
        # runtime.  A naive SMT fp.min/fp.max model drops the NaN (returns the
        # other operand) and would UNSOUNDLY prove `!float_is_nan(result)`.  The
        # faithful model must NOT prove it — Z3 finds the NaN counterexample
        # (violated).  (Pre-#807: tier3, also not "verified" — so this still
        # guards against a future naive model.)
        result = _verify("""
public fn cl(@Float64 -> @Float64)
  requires(true)
  ensures(!float_is_nan(@Float64.result))
  effects(pure)
{ float_clamp(@Float64.0, 0.0, 1.0) }
""")
        ens = _ens(result)
        assert ens and all(o.status == "violated" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]


def _clamp_triples() -> list[tuple[str, str, str]]:
    keys = list(_FLOAT_VALUES)
    triples: list[tuple[str, str, str]] = []
    # every value clamped to the normal [0, 1] range
    for v in keys:
        triples.append((v, "+0", "1.0"))
    # tricky bound pairs, each with a representative set of values
    bound_pairs = [
        ("1.0", "+0"),     # lo > hi  → must clamp to hi (codegen order)
        ("-1.0", "1.0"),   # spans zero
        ("+0", "-0"),      # ±0 bounds
        ("-0", "+0"),
        ("nan", "1.0"),    # NaN low bound → NaN propagates
        ("+0", "nan"),     # NaN high bound
        ("-inf", "+inf"),  # infinite bounds
    ]
    for lo, hi in bound_pairs:
        for v in ("0.5", "-0", "nan", "+inf", "-2.5"):
            triples.append((v, lo, hi))
    return triples


class TestFloatClampDifferential807:
    """Verify-vs-run: the Z3 model of float_clamp must agree with wasmtime
    bit-for-bit on NaN / ±0 / ±inf / ties / lo>hi — the confirmation the issue
    requires before landing the model (the fp.rem-vs-fmod trap #797 caught)."""

    @pytest.mark.parametrize("v,lo,hi", _clamp_triples())
    def test_clamp_model_agrees_with_runtime(
        self, v: str, lo: str, hi: str
    ) -> None:
        v_src, v_f = _FLOAT_VALUES[v]
        lo_src, lo_f = _FLOAT_VALUES[lo]
        hi_src, hi_f = _FLOAT_VALUES[hi]
        runtime = _run_float_expr(
            f"float_clamp({v_src}, {lo_src}, {hi_src})"
        )
        model = _wasm_fp_min(
            _wasm_fp_max(_py_to_z3fp(v_f), _py_to_z3fp(lo_f)),
            _py_to_z3fp(hi_f),
        )
        assert _model_matches_runtime(model, runtime), (
            f"float_clamp({v}, {lo}, {hi}): runtime={runtime!r} "
            f"model={z3.simplify(model)}"
        )


class TestIntToFloatTier1_807:
    def test_concrete_positive_verifies(self) -> None:
        # int_to_float(42) is a concrete arg → modeled as the folded FP 42.0.
        # Pre-#807 it deferred to Tier 3 (ensures tier3).
        result = _verify("""
public fn f(@Unit -> @Float64)
  requires(true) ensures(@Float64.result == 42.0) effects(pure)
{ int_to_float(42) }
""")
        ens = _ens(result)
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert _ok(result), [d.description for d in result.diagnostics]

    def test_concrete_negative_verifies(self) -> None:
        result = _verify("""
public fn f(@Unit -> @Float64)
  requires(true) ensures(@Float64.result == 0.0 - 7.0) effects(pure)
{ int_to_float(0 - 7) }
""")
        ens = _ens(result)
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_symbolic_defers_to_tier3(self) -> None:
        # SOUNDNESS GUARD for the concrete-gating decision: a symbolic
        # int_to_float argument must stay Tier 3 — Z3's symbolic Int↔Real↔FP
        # reasoning returns spurious counterexamples, so a contract over
        # int_to_float(@Int.0) must NOT be discharged (verified) or refuted
        # (violated) at Tier 1.  It defers (tier3).  A regression to
        # unconditional modeling would flip this to verified/violated/timeout.
        result = _verify("""
public fn f(@Int -> @Float64)
  requires(true) ensures(@Float64.result >= 0.0) effects(pure)
{ int_to_float(@Int.0) }
""")
        ens = _ens(result)
        assert ens and all(o.status == "tier3" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]


_I64_MIN = -(2**63)


def _i2f_triples() -> list[int]:
    # i64 boundaries + the 2^53 rounding boundary (where i64→f64 loses precision
    # and convert_i64_s rounds nearest-ties-to-even) + small values.
    return [
        0, 1, -1, 42, -7, 1000000,
        9007199254740992,      # 2^53 (last exactly representable)
        9007199254740993,      # 2^53 + 1 (rounds to even → 2^53)
        9007199254740995,      # 2^53 + 3 (rounds to even → 2^53 + 4)
        9223372036854775807,   # i64.MAX
        _I64_MIN,              # i64.MIN — the asymmetric two's-complement edge
    ]


def _int_to_float_body(n: int) -> str:
    # The literal -2^63 (i64.MIN) cannot be written directly: |i64.MIN| = 2^63
    # is out of the positive i64 literal range, so build it as
    # `0 - i64.MAX - 1` (each step stays in range).
    if n == _I64_MIN:
        return "int_to_float(0 - 9223372036854775807 - 1)"
    return f"int_to_float({n})" if n >= 0 else f"int_to_float(0 - {-n})"


class TestIntToFloatDifferential807:
    """Verify-vs-run: int_to_float's Z3 model fpToFP(RNE, ToReal(n)) must agree
    with wasmtime f64.convert_i64_s(n) bit-for-bit, including the 2^53 rounding
    boundary and the i64 min/max."""

    @pytest.mark.parametrize("n", _i2f_triples())
    def test_model_agrees_with_runtime(self, n: int) -> None:
        body = _int_to_float_body(n)
        runtime = _run_float_expr(body)
        model = z3.simplify(
            z3.fpToFP(z3.RNE(), z3.ToReal(z3.IntVal(n)), _FLOAT64_SORT)
        )
        assert _model_matches_runtime(model, runtime), (
            f"int_to_float({n}): runtime={runtime!r} model={model}"
        )


def _run_int_expr(body: str, sig: str = "@Unit -> @Int") -> int:
    """Compile and run `{ <body> }` returning the i64 result."""
    src = (
        f"public fn f({sig})\n"
        "  requires(true) ensures(true) effects(pure)\n"
        f"{{ {body} }}\n"
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as fh:
        fh.write(src)
        fh.flush()
        path = fh.name
    result = compile_vera(transform(parse_file(path)), source=src, file=path)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"compile errors: {[d.description for d in errors]}"
    value = execute(result, fn_name="f").value
    assert isinstance(value, int), f"expected int, got {value!r}"
    return value


def _errs(result: VerifyResult, code: str) -> list[Diagnostic]:
    return [d for d in result.diagnostics
            if d.severity == "error" and d.error_code == code]


class TestFloatToIntTier1_807:
    def test_concrete_safe_verifies(self) -> None:
        # float_to_int(3.9) is a concrete, finite, in-range arg → value modeled
        # as the truncated int 3 and the domain obligation discharges.
        result = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == 3) effects(pure)
{ float_to_int(3.9) }
""")
        ens = _ens(result)
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert _ok(result), [d.description for d in result.diagnostics]

    def test_concrete_negative_truncates_toward_zero(self) -> None:
        # trunc(-3.9) = -3 (toward zero, not floor -4).
        result = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == 0 - 3) effects(pure)
{ float_to_int(0.0 - 3.9) }
""")
        ens = _ens(result)
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_nan_arg_is_E529(self) -> None:
        # float_to_int(nan()) traps at runtime (i64.trunc_f64_s) → a concrete
        # NaN arg is a provable domain violation → loud E529 compile error.  The
        # reason string must name NaN specifically (the report distinguishes
        # NaN / infinite / out-of-range — pin it so a swapped/collapsed label
        # can't pass silently).
        result = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ float_to_int(nan()) }
""")
        errs = _errs(result, "E529")
        assert errs, [(d.error_code, d.severity) for d in result.diagnostics]
        assert "argument is NaN" in errs[0].description, errs[0].description

    def test_infinity_arg_is_E529(self) -> None:
        result = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ float_to_int(infinity()) }
""")
        errs = _errs(result, "E529")
        assert errs, [(d.error_code, d.severity) for d in result.diagnostics]
        assert "argument is infinite" in errs[0].description, errs[0].description

    def test_negative_infinity_arg_is_E529(self) -> None:
        result = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ float_to_int(0.0 - infinity()) }
""")
        errs = _errs(result, "E529")
        assert errs, [(d.error_code, d.severity) for d in result.diagnostics]
        assert "argument is infinite" in errs[0].description, errs[0].description

    def test_out_of_range_is_E529(self) -> None:
        # ~1.8e19 > i64.MAX (9.22e18): finite but trunc out of i64 range → traps
        # at runtime → E529 (Vera has no e-notation, so build it by *).
        result = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ float_to_int(9000000000000000000.0 * 2.0) }
""")
        errs = _errs(result, "E529")
        assert errs, [(d.error_code, d.severity) for d in result.diagnostics]
        assert "out of i64 range" in errs[0].description, errs[0].description

    def test_negative_out_of_range_is_E529(self) -> None:
        # ~-1.8e19 < i64.MIN: the low-side (two's-complement) out-of-range edge.
        result = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ float_to_int(0.0 - 9000000000000000000.0 * 2.0) }
""")
        errs = _errs(result, "E529")
        assert errs, [(d.error_code, d.severity) for d in result.diagnostics]
        assert "out of i64 range" in errs[0].description, errs[0].description

    def test_symbolic_defers_to_tier3(self) -> None:
        # SOUNDNESS GUARD for concrete-gating: a symbolic float_to_int argument
        # must defer to Tier 3 (codegen i64.trunc_f64_s traps), NOT be modeled —
        # Z3's symbolic FP↔Real reasoning is unreliable.  The domain obligation
        # lands tier3 and no spurious E529 is raised.
        result = _verify("""
public fn f(@Float64 -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ float_to_int(@Float64.0) }
""")
        dom = [o for o in result.obligations
               if o.kind == "float_to_int_domain"]
        assert dom and all(o.status == "tier3" for o in dom), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert not _errs(result, "E529"), "no spurious E529 on symbolic arg"


class TestFloatToIntDifferential807:
    """Verify-vs-run: float_to_int's modeled value must equal the runtime
    i64.trunc_f64_s for in-range concrete args, and the runtime must TRAP
    exactly where the verifier raises E529 (NaN / Inf / out-of-range)."""

    @pytest.mark.parametrize("body,expected", [
        ("float_to_int(3.9)", 3),
        ("float_to_int(0.0 - 3.9)", -3),
        ("float_to_int(0.0)", 0),
        ("float_to_int(2.5)", 2),
        ("float_to_int(0.0 - 0.5)", 0),
        ("float_to_int(9007199254740992.0)", 9007199254740992),  # 2^53
        ("float_to_int(0.0 - 9007199254740992.0)", -9007199254740992),
    ])
    def test_value_model_agrees_with_runtime(
        self, body: str, expected: int
    ) -> None:
        runtime = _run_int_expr(body)
        assert runtime == expected, f"{body}: runtime={runtime}"
        # The verifier must model the SAME value (ensures discharges at Tier 1).
        lit = str(expected) if expected >= 0 else f"0 - {-expected}"
        result = _verify(f"""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == {lit}) effects(pure)
{{ {body} }}
""")
        ens = _ens(result)
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert _ok(result), [d.description for d in result.diagnostics]

    @pytest.mark.parametrize("body", [
        "float_to_int(nan())",
        "float_to_int(infinity())",
        "float_to_int(0.0 - infinity())",
        "float_to_int(9000000000000000000.0 * 2.0)",
    ])
    def test_domain_violations_trap_at_runtime(self, body: str) -> None:
        # The runtime MUST trap exactly where the verifier raises E529 — this is
        # the agreement the issue requires for the trap cases.
        with pytest.raises(WasmTrapError):
            _run_int_expr(body)
