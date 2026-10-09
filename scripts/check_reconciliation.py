#!/usr/bin/env python
"""Reconcile every corpus program's runtime-check claims with the checks
its compiled module holds (the audit's T2a), for local and burndown use.

    python scripts/check_reconciliation.py

CI runs the same join through `tests/test_reconciliation.py`, one test per
corpus program and one strict xfail per `KNOWN` entry, on every test cell,
so this script is not a CI step of its own.

Each program of the corpus (every `.vera` file under `examples/` and
`tests/conformance/`, at any depth, as `check_corpus_canonical.py` reads it)
goes through check, verify, compile and the join of
:func:`vera.reconcile.join`, in process and with the calls
`vera verify --reconcile` makes.  The gate fails on:

* a mismatch :data:`KNOWN` does not list: a `tier3` record no emitted check
  answers, an emitted check no record accounts for, or a site the join
  cannot place;
* a :data:`KNOWN` entry the join no longer reports: the issue it names is
  fixed, so the entry comes out (`tests/test_reconciliation.py` pins every
  entry as a strict xfail, which flips at the same moment);
* a :data:`KNOWN` key two mismatches share, which the entry would absorb;
* a program that stops before the join for a reason the manifest does not
  give it: a refusal at check is the negative fixtures' alone, a refusal at
  compile is a negative fixture's or a program named in
  :data:`COMPILE_STOPS`, and a library module that does not check on its own
  is named in :data:`FRAGMENTS`.  A program named in either table that
  reaches the join is a problem too.

:data:`KNOWN` is keyed by issue number.  Each entry names the open issue
whose class the mismatch belongs to, the mismatch kind, the obligation kind
and the site.  A new mismatch is a bug: file it (or extend the open issue
of its class) and add the entry with that number.
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

CORPUS_DIRS = ("examples", "tests/conformance")
MANIFEST = ROOT / "tests" / "conformance" / "manifest.json"


@dataclass(frozen=True)
class Known:
    """One mismatch the join reports today, and the open issue it belongs
    to."""

    issue: int
    program: str
    """The corpus program, repository-relative."""

    kind: str
    """`recorded_unguarded`, `guarded_unrecorded` or `no_mapping`."""

    obligation: str
    """The obligation kind(s), as :class:`vera.reconcile.Mismatch` names
    them."""

    site: str
    """``<file>:<line>:<column>`` of the record or the check."""

    def key(self) -> tuple[str, str, str, str]:
        return (self.program, self.kind, self.obligation, self.site)


#: Every mismatch the corpus has today, by the issue whose class it is.
#:
#: * #1482 — `float_to_string` truncates its integer part with an
#:   `i64.trunc_f64_s` the trap registry lists as a known defect, not a
#:   check, while the verifier records that truncation as the runtime check
#:   of a `float_to_int_domain` obligation at the call.
#: * #1530 — a `decreases` whose termination guard code generation declines
#:   (`_compile_decreases_entry`: the function declares `Exn`, or a measure
#:   component it cannot translate or rank) is recorded `tier3` (E525).
#: * #1557 — code generation's static `@Nat` rule
#:   (`narrowing.is_static_nat_typed` over its own call-type oracle) has no
#:   reading for a value the checker types `@Nat` (a non-generic or built-in
#:   `@Nat` call, a `State<Nat>` operation, a `handle`, an alias of `@Nat`):
#:   a subtraction over one is claimed and unguarded, and a binding of one
#:   is guarded with no `nat_bind` record (the verifier sees no narrowing).
#: * #1598 — a signed division's `INT_MIN / -1` check
#:   (`_note_quotient_overflow`) has no `int_overflow` obligation.
#: * #1628 — a `@Nat` widened into a built-in's `@Int` argument is recorded
#:   `nat_to_int_coerce` `tier3`, and the built-in's translator emits no
#:   widening guard.
#: * #1629 — a site the verifier records no obligation for is still checked:
#:   a division by a non-zero literal, a `@Nat` destructure or pattern
#:   binder over a value that is already `@Nat`, a refinement guard on a
#:   value already of the refined type.
KNOWN: tuple[Known, ...] = (
    # #1482
    Known(1482, "examples/ephemeris.vera", "recorded_unguarded", "float_to_int_domain", "ephemeris.vera:477:256"),
    Known(1482, "examples/maximum_syntax.vera", "recorded_unguarded", "float_to_int_domain", "maximum_syntax.vera:392:36"),
    # #1530
    Known(1530, "tests/conformance/ch02_adt_tuple_recursive.vera", "recorded_unguarded", "decreases", "ch02_adt_tuple_recursive.vera:15:3"),
    # #1557
    Known(1557, "tests/conformance/ch02_adt_recursive.vera", "guarded_unrecorded", "nat_bind", "ch02_adt_recursive.vera:16:31"),
    Known(1557, "tests/conformance/ch02_adt_tuple_recursive.vera", "guarded_unrecorded", "nat_bind", "ch02_adt_tuple_recursive.vera:21:30"),
    Known(1557, "tests/conformance/ch02_adt_tuple_recursive.vera", "guarded_unrecorded", "nat_bind", "ch02_adt_tuple_recursive.vera:31:14"),
    Known(1557, "tests/conformance/ch04_string_interpolation.vera", "guarded_unrecorded", "nat_bind", "ch04_string_interpolation.vera:35:14"),
    Known(1557, "tests/conformance/ch05_decreases_guard.vera", "guarded_unrecorded", "nat_bind", "ch05_decreases_guard.vera:17:29"),
    Known(1557, "tests/conformance/ch05_decreases_guard.vera", "guarded_unrecorded", "nat_bind", "ch05_decreases_guard.vera:44:14"),
    Known(1557, "tests/conformance/ch06_decreases.vera", "guarded_unrecorded", "nat_bind", "ch06_decreases.vera:29:31"),
    Known(1557, "tests/conformance/ch07_diverge.vera", "guarded_unrecorded", "nat_bind", "ch07_diverge.vera:29:14"),
    Known(1557, "tests/conformance/ch07_io_time_stderr.vera", "guarded_unrecorded", "nat_bind", "ch07_io_time_stderr.vera:10:14"),
    Known(1557, "tests/conformance/ch07_state_op_generic_instantiation.vera", "guarded_unrecorded", "nat_bind", "ch07_state_op_generic_instantiation.vera:39:9"),
    Known(1557, "tests/conformance/ch07_state_op_generic_instantiation.vera", "guarded_unrecorded", "nat_bind", "ch07_state_op_generic_instantiation.vera:39:29"),
    Known(1557, "tests/conformance/ch07_state_op_generic_instantiation.vera", "guarded_unrecorded", "nat_bind", "ch07_state_op_generic_instantiation.vera:54:16"),
    Known(1557, "tests/conformance/ch07_state_op_generic_instantiation.vera", "guarded_unrecorded", "nat_bind", "ch07_state_op_generic_instantiation.vera:54:22"),
    Known(1557, "tests/conformance/ch07_state_op_generic_instantiation.vera", "guarded_unrecorded", "nat_bind", "ch07_state_op_generic_instantiation.vera:54:52"),
    Known(1557, "tests/conformance/ch07_state_op_generic_instantiation.vera", "guarded_unrecorded", "nat_bind", "ch07_state_op_generic_instantiation.vera:54:59"),
    Known(1557, "tests/conformance/ch07_state_op_generic_instantiation.vera", "guarded_unrecorded", "nat_bind", "ch07_state_op_generic_instantiation.vera:54:85"),
    Known(1557, "tests/conformance/ch07_clause_body_op_enclosing.vera", "guarded_unrecorded", "nat_bind", "ch07_clause_body_op_enclosing.vera:21:16"),
    Known(1557, "tests/conformance/ch07_clause_body_op_enclosing.vera", "guarded_unrecorded", "nat_bind", "ch07_clause_body_op_enclosing.vera:46:58"),
    Known(1557, "tests/conformance/ch07_clause_body_op_enclosing.vera", "guarded_unrecorded", "nat_bind", "ch07_clause_body_op_enclosing.vera:51:31"),
    Known(1557, "tests/conformance/ch07_clause_body_op_enclosing.vera", "guarded_unrecorded", "nat_bind", "ch07_clause_body_op_enclosing.vera:75:18"),
    Known(1557, "tests/conformance/ch07_clause_body_op_enclosing.vera", "guarded_unrecorded", "nat_bind", "ch07_clause_body_op_enclosing.vera:82:48"),
    Known(1557, "tests/conformance/ch07_op_name_user_shadow.vera", "guarded_unrecorded", "nat_bind", "ch07_op_name_user_shadow.vera:40:16"),
    Known(1557, "tests/conformance/ch07_op_name_user_shadow.vera", "guarded_unrecorded", "nat_bind", "ch07_op_name_user_shadow.vera:40:43"),
    Known(1557, "tests/conformance/ch07_op_name_user_shadow.vera", "guarded_unrecorded", "nat_bind", "ch07_op_name_user_shadow.vera:59:58"),
    Known(1557, "tests/conformance/ch07_op_name_user_shadow.vera", "guarded_unrecorded", "nat_bind", "ch07_op_name_user_shadow.vera:81:58"),
    Known(1557, "tests/conformance/ch07_op_name_user_shadow.vera", "guarded_unrecorded", "nat_bind", "ch07_op_name_user_shadow.vera:96:14"),
    Known(1557, "tests/conformance/ch07_handler_registration_positions.vera", "guarded_unrecorded", "nat_bind", "ch07_handler_registration_positions.vera:22:16"),
    Known(1557, "tests/conformance/ch07_handler_registration_positions.vera", "guarded_unrecorded", "nat_bind", "ch07_handler_registration_positions.vera:39:40"),
    Known(1557, "tests/conformance/ch07_handler_registration_positions.vera", "guarded_unrecorded", "nat_bind", "ch07_handler_registration_positions.vera:56:65"),
    Known(1557, "tests/conformance/ch07_state_alias.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias.vera:14:28"),
    Known(1557, "tests/conformance/ch07_state_alias.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias.vera:18:16"),
    Known(1557, "tests/conformance/ch09_map.vera", "guarded_unrecorded", "nat_bind", "ch09_map.vera:70:14"),
    Known(1557, "tests/conformance/ch09_map.vera", "guarded_unrecorded", "nat_bind", "ch09_map.vera:88:14"),
    Known(1557, "tests/conformance/ch02_refinement_base_param_alias.vera", "guarded_unrecorded", "nat_bind", "ch02_refinement_base_param_alias.vera:38:14"),
    Known(1557, "tests/conformance/ch02_refinement_base_param_alias.vera", "guarded_unrecorded", "nat_bind", "ch02_refinement_base_param_alias.vera:38:21"),
    Known(1557, "tests/conformance/ch07_state_scalar_alias_cross_spelling.vera", "guarded_unrecorded", "nat_bind", "ch07_state_scalar_alias_cross_spelling.vera:27:16"),
    Known(1557, "tests/conformance/ch07_state_alias_chain.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias_chain.vera:23:28"),
    Known(1557, "tests/conformance/ch07_state_alias_chain.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias_chain.vera:27:16"),
    Known(1557, "tests/conformance/ch07_state_alias_chain.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias_chain.vera:40:16"),
    Known(1557, "tests/conformance/ch07_state_alias_chain.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias_chain.vera:53:16"),
    Known(1557, "tests/conformance/ch07_state_nested_param_alias.vera", "guarded_unrecorded", "nat_bind", "ch07_state_nested_param_alias.vera:16:28"),
    Known(1557, "tests/conformance/ch07_state_nested_param_alias.vera", "guarded_unrecorded", "nat_bind", "ch07_state_nested_param_alias.vera:20:16"),
    Known(1557, "tests/conformance/ch07_state_nested_param_alias.vera", "guarded_unrecorded", "nat_bind", "ch07_state_nested_param_alias.vera:30:28"),
    Known(1557, "tests/conformance/ch07_state_nested_param_alias.vera", "guarded_unrecorded", "nat_bind", "ch07_state_nested_param_alias.vera:34:16"),
    Known(1557, "tests/conformance/ch07_state_alias_op_result_positions.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias_op_result_positions.vera:16:28"),
    Known(1557, "tests/conformance/ch07_state_alias_op_result_positions.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias_op_result_positions.vera:19:24"),
    Known(1557, "tests/conformance/ch07_state_alias_op_result_positions.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias_op_result_positions.vera:19:33"),
    Known(1557, "tests/conformance/ch07_state_alias_op_result_positions.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias_op_result_positions.vera:20:16"),
    Known(1557, "tests/conformance/ch07_state_alias_op_result_positions.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias_op_result_positions.vera:30:28"),
    Known(1557, "tests/conformance/ch07_state_alias_op_result_positions.vera", "guarded_unrecorded", "nat_bind", "ch07_state_alias_op_result_positions.vera:47:28"),
    Known(1557, "tests/conformance/ch07_exn_string_alias.vera", "recorded_unguarded", "nat_sub", "ch07_exn_string_alias.vera:59:3"),
    Known(1557, "tests/conformance/ch08_state_alias_per_module_lib.vera", "guarded_unrecorded", "nat_bind", "ch08_state_alias_per_module_lib.vera:15:28"),
    Known(1557, "tests/conformance/ch08_state_alias_per_module_lib.vera", "guarded_unrecorded", "nat_bind", "ch08_state_alias_per_module_lib.vera:19:16"),
    Known(1557, "tests/conformance/ch08_state_alias_module_table_lib.vera", "guarded_unrecorded", "nat_bind", "ch08_state_alias_module_table_lib.vera:17:16"),
    Known(1557, "examples/life.vera", "guarded_unrecorded", "nat_bind", "life.vera:118:179"),
    Known(1557, "examples/life.vera", "guarded_unrecorded", "nat_bind", "life.vera:291:51"),
    Known(1557, "examples/list_ops.vera", "guarded_unrecorded", "nat_bind", "list_ops.vera:15:31"),
    # #1598
    Known(1598, "tests/conformance/ch02_refinement_types.vera", "guarded_unrecorded", "int_overflow", "ch02_refinement_types.vera:17:3"),
    Known(1598, "tests/conformance/ch03_slot_noncommutative.vera", "guarded_unrecorded", "int_overflow", "ch03_slot_noncommutative.vera:18:26"),
    Known(1598, "tests/conformance/ch03_slot_noncommutative.vera", "guarded_unrecorded", "int_overflow", "ch03_slot_noncommutative.vera:21:3"),
    Known(1598, "tests/conformance/ch04_primitive_obligations.vera", "guarded_unrecorded", "int_overflow", "ch04_primitive_obligations.vera:15:3"),
    Known(1598, "tests/conformance/ch04_primitive_obligations.vera", "guarded_unrecorded", "int_overflow", "ch04_primitive_obligations.vera:40:3"),
    Known(1598, "tests/conformance/ch06_requires.vera", "guarded_unrecorded", "int_overflow", "ch06_requires.vera:5:26"),
    Known(1598, "tests/conformance/ch06_requires.vera", "guarded_unrecorded", "int_overflow", "ch06_requires.vera:8:3"),
    Known(1598, "tests/conformance/ch07_exn_handler.vera", "guarded_unrecorded", "int_overflow", "ch07_exn_handler.vera:11:5"),
    Known(1598, "examples/effect_handler.vera", "guarded_unrecorded", "int_overflow", "effect_handler.vera:81:5"),
    Known(1598, "examples/maximum_syntax.vera", "guarded_unrecorded", "int_overflow", "maximum_syntax.vera:276:5"),
    Known(1598, "examples/refinement_types.vera", "guarded_unrecorded", "int_overflow", "refinement_types.vera:30:3"),
    Known(1598, "examples/safe_divide.vera", "guarded_unrecorded", "int_overflow", "safe_divide.vera:4:26"),
    Known(1598, "examples/safe_divide.vera", "guarded_unrecorded", "int_overflow", "safe_divide.vera:7:3"),
    # #1628
    Known(1628, "examples/json.vera", "recorded_unguarded", "nat_to_int_coerce", "json.vera:60:60"),
    Known(1628, "examples/life.vera", "recorded_unguarded", "nat_to_int_coerce", "life.vera:195:36"),
    Known(1628, "examples/life.vera", "recorded_unguarded", "nat_to_int_coerce", "life.vera:196:109"),
    Known(1628, "examples/string_ops.vera", "recorded_unguarded", "nat_to_int_coerce", "string_ops.vera:40:58"),
    # #1629
    Known(1629, "tests/conformance/ch04_arithmetic.vera", "guarded_unrecorded", "div_zero", "ch04_arithmetic.vera:32:3"),
    Known(1629, "tests/conformance/ch04_arithmetic.vera", "guarded_unrecorded", "div_zero", "ch04_arithmetic.vera:40:3"),
    Known(1629, "tests/conformance/ch04_nat_binding.vera", "guarded_unrecorded", "nat_bind", "ch04_nat_binding.vera:62:20"),
    Known(1629, "tests/conformance/ch04_nat_binding.vera", "guarded_unrecorded", "nat_bind", "ch04_nat_binding.vera:85:10"),
    Known(1629, "tests/conformance/ch04_primitive_obligations.vera", "guarded_unrecorded", "refine_bind", "ch04_primitive_obligations.vera:35:29"),
    Known(1629, "tests/conformance/ch07_diverge.vera", "guarded_unrecorded", "div_zero", "ch07_diverge.vera:16:8"),
    Known(1629, "tests/conformance/ch07_diverge.vera", "guarded_unrecorded", "div_zero", "ch07_diverge.vera:17:21"),
    Known(1629, "tests/conformance/ch09_type_conversions.vera", "guarded_unrecorded", "nat_bind", "ch09_type_conversions.vera:49:10"),
    Known(1629, "tests/conformance/ch09_type_conversions.vera", "guarded_unrecorded", "nat_bind", "ch09_type_conversions.vera:60:10"),
    Known(1629, "tests/conformance/ch09_string_search.vera", "guarded_unrecorded", "nat_bind", "ch09_string_search.vera:34:10"),
    Known(1629, "examples/ephemeris.vera", "guarded_unrecorded", "refine_bind", "ephemeris.vera:211:35"),
    Known(1629, "examples/ephemeris.vera", "guarded_unrecorded", "refine_bind", "ephemeris.vera:223:36"),
    Known(1629, "examples/ephemeris.vera", "guarded_unrecorded", "refine_bind", "ephemeris.vera:269:50"),
    Known(1629, "examples/ephemeris.vera", "guarded_unrecorded", "refine_bind", "ephemeris.vera:292:50"),
    Known(1629, "examples/ephemeris.vera", "guarded_unrecorded", "refine_bind", "ephemeris.vera:340:26"),
    Known(1629, "examples/ephemeris.vera", "guarded_unrecorded", "div_zero", "ephemeris.vera:448:146"),
    Known(1629, "examples/ephemeris.vera", "guarded_unrecorded", "div_zero", "ephemeris.vera:448:205"),
    Known(1629, "examples/fizzbuzz.vera", "guarded_unrecorded", "div_zero", "fizzbuzz.vera:6:6"),
    Known(1629, "examples/fizzbuzz.vera", "guarded_unrecorded", "div_zero", "fizzbuzz.vera:9:8"),
    Known(1629, "examples/fizzbuzz.vera", "guarded_unrecorded", "div_zero", "fizzbuzz.vera:12:10"),
    Known(1629, "examples/life.vera", "guarded_unrecorded", "nat_bind", "life.vera:28:10"),
    Known(1629, "examples/life.vera", "guarded_unrecorded", "nat_bind", "life.vera:34:14"),
    Known(1629, "examples/string_ops.vera", "guarded_unrecorded", "nat_bind", "string_ops.vera:17:8"),
    Known(1629, "examples/string_ops.vera", "guarded_unrecorded", "nat_bind", "string_ops.vera:40:39"),
)

#: Library modules under the corpus that do not type-check on their own,
#: and why: they are halves of a program the manifest declares, not
#: programs.
FRAGMENTS: dict[str, str] = {
    "tests/conformance/vera/cycle_a.vera":
        "one half of the import cycle ch08_circular_import is refused for",
    "tests/conformance/vera/cycle_b.vera":
        "one half of the import cycle ch08_circular_import is refused for",
}


#: Corpus programs that type-check and verify but that code generation
#: refuses, and why: the join has no module to read for them.
COMPILE_STOPS: dict[str, str] = {
    "tests/conformance/ch03_typed_holes.vera":
        "a typed hole has no code to compile (E614)",
}


@dataclass(frozen=True)
class Program:
    """One corpus program, and what the manifest says it must reach."""

    path: Path
    rel: str
    negative: bool = False
    """A manifest negative fixture: refused before verification."""


def corpus() -> list[Program]:
    """Every corpus program, with its manifest expectations."""
    manifest = {
        entry["file"]: entry
        for entry in json.loads(MANIFEST.read_text(encoding="utf-8"))
    }
    out: list[Program] = []
    for directory in CORPUS_DIRS:
        for path in sorted((ROOT / directory).rglob("*.vera")):
            rel = path.relative_to(ROOT).as_posix()
            entry = (manifest.get(path.name)
                     if path.parent.name == "conformance" else None)
            out.append(Program(
                path=path, rel=rel,
                negative=bool(entry and entry.get("expected_error")),
            ))
    return out


def mismatch_key(program: Program, mismatch: object) -> tuple[str, str, str, str]:
    """The :class:`Known` key of a :class:`vera.reconcile.Mismatch`."""
    file = getattr(mismatch, "file", None)
    site = (f"{Path(file).name if file else '?'}:"
            f"{getattr(mismatch, 'line')}:{getattr(mismatch, 'column')}")
    return (program.rel, getattr(mismatch, "kind"),
            getattr(mismatch, "obligation"), site)


def stop_problem(program: Program, run: object) -> str | None:
    """Why a program that stopped before the join should not have, or None
    when the stop is one the manifest (or :data:`FRAGMENTS`) gives it."""
    check_errors = getattr(run, "check_errors")
    compile_errors = getattr(run, "compile_errors")
    if program.negative:
        if check_errors or compile_errors:
            return None
        return "a negative fixture reached the join"
    if check_errors:
        if program.rel in FRAGMENTS:
            return None
        return f"refused at check: {check_errors[0][:120]}"
    if program.rel in FRAGMENTS:
        return "listed in FRAGMENTS, but it type-checks on its own"
    if compile_errors:
        if program.rel in COMPILE_STOPS:
            return None
        return f"refused at compile: {compile_errors[0][:120]}"
    return None


def joined_problem(program: Program) -> str | None:
    """Why a program that reached the join should not have, or None."""
    if program.negative:
        return "a negative fixture reached the join"
    if program.rel in COMPILE_STOPS:
        return "listed in COMPILE_STOPS, but it compiles"
    if program.rel in FRAGMENTS:
        return "listed in FRAGMENTS, but it type-checks on its own"
    return None


def shared_keys(program: Program, mismatches: list[object]) -> list[str]:
    """Every key two or more of *mismatches* share: a :class:`Known` entry
    names one mismatch, so a second at its key would be absorbed."""
    counts: dict[tuple[str, str, str, str], int] = {}
    for mismatch in mismatches:
        key = mismatch_key(program, mismatch)
        counts[key] = counts.get(key, 0) + 1
    return [f"{key[3]}: {n} {key[1]} {key[2]} mismatches share one key"
            for key, n in counts.items() if n > 1]


def main() -> int:
    from vera.reconcile import reconcile_file

    known = {entry.key(): entry for entry in KNOWN}
    if len(known) != len(KNOWN):
        print("ERROR: KNOWN lists one mismatch twice", file=sys.stderr)
        return 1
    programs = corpus()
    if not programs:
        print("ERROR: no corpus programs found", file=sys.stderr)
        return 1
    problems: list[str] = []
    seen: set[tuple[str, str, str, str]] = set()
    reconciled = stopped = 0
    for program in programs:
        run = reconcile_file(program.path)
        if run.reconciliation is None:
            stopped += 1
            why = stop_problem(program, run)
            if why:
                problems.append(f"{program.rel}: {why}")
            continue
        reconciled += 1
        why = joined_problem(program)
        if why:
            problems.append(f"{program.rel}: {why}")
        problems.extend(f"{program.rel}: {line}"
                        for line in shared_keys(program, run.mismatches))
        for mismatch in run.mismatches:
            key = mismatch_key(program, mismatch)
            seen.add(key)
            if key not in known:
                problems.append(
                    f"{key[3]}: {mismatch.kind} {mismatch.obligation} in "
                    f"'{mismatch.function}': {mismatch.detail} "
                    f"(not in KNOWN; program {program.rel})")
    for key, entry in known.items():
        if key not in seen:
            problems.append(
                f"{entry.site}: KNOWN lists #{entry.issue} {entry.kind} "
                f"{entry.obligation}, which the join no longer reports — "
                "remove the entry")
    if problems:
        print(f"Reconciliation: {len(problems)} problem(s)", file=sys.stderr)
        for line in problems:
            print(f"  {line}", file=sys.stderr)
        return 1
    print(f"Reconciliation: {reconciled} programs joined, {stopped} stopped "
          f"before the join as the manifest declares, {len(KNOWN)} known "
          f"mismatches across {len({e.issue for e in KNOWN})} open issues.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
