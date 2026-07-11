"""Regression: bare nullary-constructor sort selection in ``==``/``!=`` (#994 F1).

PR #994 (the #979/#981 checker adoption) newly accepts programs whose result
value is a payload-less nested constructor (``Some(None) : Option<Option<Int>>``)
compared against ``None`` / ``Some(None)`` in a contract.  A bare ``None`` carries
no payload to drive the verifier's sort recovery, so ``_find_sort_for_ctor``'s
base-name scan picked whichever ``Option<...>`` instantiation cached first — with
both ``Option<Int>`` and ``Option<Option<Int>>`` live it returned the wrong sort,
and ``_datatype_value_eq``'s ``left == right`` raised an **uncaught**
``z3.z3types.Z3Exception: sort mismatch`` — a Python traceback out of
``vera verify`` (exit 1, no JSON) on a ``vera check``-green program.

The fix hints the nullary-ctor sort with the checker's recorded (instance-
substituted) semantic type for that expression (the #747 side-table), resolving
the exact instantiation; a residual sort mismatch in ``_datatype_value_eq``
degrades to an honest Tier-3 (``None``) rather than crashing.

Semantic oracle: the same postconditions written with ``match`` (M1/M2) —
which never route through the nullary-ctor sort path — pin the truth values,
so the ``==``/``!=`` forms must agree with them, not merely stop crashing.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import z3

from vera.smt import SmtContext

from tests.verifier_helpers import _verify_ok, _verify_err


# ---------------------------------------------------------------------------
# Finding 1 repro shapes.  Each is `vera check`-green; on base each crashes
# `vera verify` with an uncaught z3 `sort mismatch`.
# ---------------------------------------------------------------------------

# The filed repro: `Some(None) != None` — the TRUE postcondition.  Must PROVE
# (or, if the term genuinely can't be translated, demote to an honest Tier-3 —
# never crash).
_NEQ_NONE_TRUE = """
private fn f(@Unit -> @Option<Option<Int>>)
  requires(true)
  ensures(@Option<Option<Int>>.result != None)
  effects(pure)
{ Some(None) }
"""

# `Some(None) == None` — a FALSE postcondition (the result IS Some(None), which
# is not None).  Must be disproved (E500), never falsely proved.
_EQ_NONE_FALSE = """
private fn f(@Unit -> @Option<Option<Int>>)
  requires(true)
  ensures(@Option<Option<Int>>.result == None)
  effects(pure)
{ Some(None) }
"""

# `Some(None) == Some(None)` — a TRUE postcondition comparing the nested value
# against an equal nested literal.  Must PROVE.
_EQ_SOMENONE_TRUE = """
private fn f(@Unit -> @Option<Option<Int>>)
  requires(true)
  ensures(@Option<Option<Int>>.result == Some(None))
  effects(pure)
{ Some(None) }
"""

# Reversed operand order: `None != Some(None)`-style — the ctor on the LEFT.
_NEQ_NONE_TRUE_REV = """
private fn f(@Unit -> @Option<Option<Int>>)
  requires(true)
  ensures(None != @Option<Option<Int>>.result)
  effects(pure)
{ Some(None) }
"""

# `Some(None) == Some(None)` with the literal on the LEFT.
_EQ_SOMENONE_TRUE_REV = """
private fn f(@Unit -> @Option<Option<Int>>)
  requires(true)
  ensures(Some(None) == @Option<Option<Int>>.result)
  effects(pure)
{ Some(None) }
"""

# Forall form of the true `!= None` postcondition — verified via monomorphized
# clones, where the recorded type is instance-substituted (T := Int).
_NEQ_NONE_TRUE_FORALL = """
private forall<T> fn nest(@Unit -> @Option<Option<T>>)
  requires(true)
  ensures(@Option<Option<T>>.result != None)
  effects(pure)
{ Some(None) }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match nest(()) { Some(@Option<Int>) -> 1, None -> 0 } }
"""

# Forall form of the false `== None` postcondition — must be disproved even
# through the clone.
_EQ_NONE_FALSE_FORALL = """
private forall<T> fn nest(@Unit -> @Option<Option<T>>)
  requires(true)
  ensures(@Option<Option<T>>.result == None)
  effects(pure)
{ Some(None) }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match nest(()) { Some(@Option<Int>) -> 1, None -> 0 } }
"""

# Match-based semantic oracles: same truth values, but never touch the
# nullary-ctor sort path (so they hold on base and after the fix alike).
_M1_MATCH_INNER_NONE_TRUE = """
private fn f(@Unit -> @Option<Option<Int>>)
  requires(true)
  ensures(match @Option<Option<Int>>.result { Some(@Option<Int>) -> match @Option<Int>.0 { Some(@Int) -> false, None -> true }, None -> false })
  effects(pure)
{ Some(None) }
"""

_M2_MATCH_INNER_SOME_FALSE = """
private fn f(@Unit -> @Option<Option<Int>>)
  requires(true)
  ensures(match @Option<Option<Int>>.result { Some(@Option<Int>) -> match @Option<Int>.0 { Some(@Int) -> true, None -> false }, None -> false })
  effects(pure)
{ Some(None) }
"""


# ---------------------------------------------------------------------------
# Crash-free + correct verdicts.
# ---------------------------------------------------------------------------

def test_neq_none_true_proves_or_tier3() -> None:
    # `Some(None) != None` is TRUE — must not crash and must not be a false
    # E500.  (Proving is ideal; an honest Tier-3 that leaves no error is also
    # acceptable — the runtime check would then confirm it.)
    _verify_ok(_NEQ_NONE_TRUE)


def test_neq_none_true_reversed_proves_or_tier3() -> None:
    _verify_ok(_NEQ_NONE_TRUE_REV)


def test_eq_somenone_true_proves_or_tier3() -> None:
    _verify_ok(_EQ_SOMENONE_TRUE)


def test_eq_somenone_true_reversed_proves_or_tier3() -> None:
    _verify_ok(_EQ_SOMENONE_TRUE_REV)


def test_neq_none_true_forall_proves_or_tier3() -> None:
    _verify_ok(_NEQ_NONE_TRUE_FORALL)


def test_eq_none_false_is_disproved() -> None:
    # `Some(None) == None` is FALSE — must be an E500, matching the M2-style
    # oracle's falsity.  Never a false PROVE.
    _verify_err(_EQ_NONE_FALSE, "does not hold")


def test_eq_none_false_forall_is_disproved() -> None:
    _verify_err(_EQ_NONE_FALSE_FORALL, "does not hold")


# ---------------------------------------------------------------------------
# Match-based semantic oracles (never crash; pin the truth values).
# ---------------------------------------------------------------------------

def test_match_oracle_inner_none_true_proves() -> None:
    _verify_ok(_M1_MATCH_INNER_NONE_TRUE)


def test_match_oracle_inner_some_false_disproved() -> None:
    _verify_err(_M2_MATCH_INNER_SOME_FALSE, "does not hold")


# ---------------------------------------------------------------------------
# `verify --json` must ALWAYS emit JSON — never a Python traceback — for the
# crash shape.
# ---------------------------------------------------------------------------

def _option_sort(name: str, payload: z3.SortRef) -> z3.DatatypeSortRef:
    dt = z3.Datatype(name)
    dt.declare("Some", ("val", payload))
    dt.declare("None")
    return dt.create()


def test_datatype_value_eq_degrades_on_sort_mismatch() -> None:
    # Defence-in-depth backstop (#994 F1): if a bare nullary ctor ever again
    # resolves to the wrong same-ADT instantiation (the recorded-type hint
    # unavailable / stale), `_datatype_value_eq` must be handed two
    # differently-sorted terms.  It MUST degrade to an honest Tier-3 (None)
    # rather than let `left == right` raise `z3.z3types.Z3Exception: sort
    # mismatch` — the uncaught traceback the finding filed.  This is the exact
    # shape the crash produced: `Option<Option<Int>>` vs `Option<Int>`.
    opt_int = _option_sort("Option<Int>", z3.IntSort())
    opt_opt_int = _option_sort("Option<Option<Int>>", opt_int)
    left = opt_opt_int.constructor(1)()   # None : Option<Option<Int>>
    right = opt_int.constructor(1)()      # None : Option<Int>
    assert left.sort() != right.sort()    # precondition: genuinely mismatched
    smt = SmtContext()
    # Must return None (Tier-3 demotion), NOT raise.
    assert smt._datatype_value_eq(left, right) is None


def test_verify_json_always_emits_json(tmp_path: Path) -> None:
    src = tmp_path / "f1.vera"
    src.write_text(_NEQ_NONE_TRUE, encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "-m", "vera.cli", "verify", "--json", str(src)],
        capture_output=True, text=True, encoding="utf-8",
    )
    # Whatever the verdict, stdout must be parseable JSON (no traceback).
    assert "Traceback" not in proc.stderr, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["file"] == str(src)
    assert "diagnostics" in payload
