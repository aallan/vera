"""Reconcile the verifier's runtime-guard claims with the checks code
generation emits (the audit's T2a), by the obligation table's rows (#1695).

A ``tier3`` obligation says its property is checked at run time, and
``vera verify`` counts it in ``tier3_runtime``.  Both halves read one
table (:mod:`vera.obligations.table`): the verifier discharges its rows,
each :class:`~vera.obligations.core.ProofObligation` naming the rows it is
the record of (``rows``), and code generation guards them, each
:class:`~vera.trap_registry.EmittedCheck` naming the row it is the check of
(``row``).  :func:`join` pairs the two by row identity, so nothing about
where either side stands is compared:

* ``recorded_unguarded`` — a record whose status claims a runtime check
  (``tier3``, ``timeout``) with a guardable row the module, holding the
  row's function, holds no check for.  The claim is false, so ``vera
  verify`` reports it as an error (E541).  A row whose check is another
  row's (``Row.answered_by``: a ``call_pre`` the callee's ``requires``
  check answers, a call argument the callee's entry check answers) is
  answered by that row's check; every copy of a site (a measure at each
  self tail call, a clause at each operation call, a predicate at each
  guard) is a row, and each must have its check.
* ``guarded_unrecorded`` — a check whose row, and every row it answers,
  no record of this run names, in a function this run verified.  It is a
  warning (W004).  Every check names a row, so this arises only where the
  verifier did not discharge a row it should have.
* ``no_mapping`` — a check that names no row outside a generated helper
  shared by every rendering of its type, or a record of a kind no emitter
  serves.  Reported under the code of its direction.

A record inside a function the module has no code for (a generic no
program instantiates, a function code generation dropped) is ``absent``;
a check in code this run did not verify (a prelude body, an imported
module's own function) is ``out_of_scope``.

``state_decl`` and ``effect_bind`` are excluded (:data:`EXCLUDED_KINDS`):
the first is violated-or-absent, the second a row no check can evaluate.
"""

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Literal, get_args

from vera import ast
from vera.errors import Diagnostic, SourceLocation, VeraError
from vera.obligations.core import ObligationKind, ProofObligation
from vera.trap_registry import TRAP_EMITTERS, EmittedCheck

if TYPE_CHECKING:
    from vera.obligations.table import Row
    from vera.typed import TypedProgram
    from vera.codegen.api import CompileResult
    from vera.resolver import ResolvedModule
    from vera.verifier import VerifyResult

MismatchKind = Literal["recorded_unguarded", "guarded_unrecorded", "no_mapping"]

#: The statuses that claim a runtime check: the ones ``tier3_runtime``
#: counts (CLAUDE.md's partition table, ``summarize``).
CLAIMS_GUARD: frozenset[str] = frozenset({"tier3", "timeout"})

#: The status that says the site has NO runtime check.  A check standing at
#: a site recorded this way contradicts its record.
DENIES_GUARD = "tier3_unguarded"

#: Obligation kinds with no guard concept, excluded from the join by name.
#: A ``state_decl`` record is violated-or-absent (``ObligationKind``'s own
#: comment): it is an E533 refusal, never a runtime check.  An
#: ``effect_bind`` row (#1725, the obligation table) is a binder bound at
#: a narrower effect row, which no runtime check can evaluate: it is
#: disclosed, never guarded.
EXCLUDED_KINDS: frozenset[str] = frozenset({"state_decl", "effect_bind"})


def _emitters_by_kind() -> dict[str, frozenset[str]]:
    """Every per-site emitter that answers each obligation kind, read off
    :data:`~vera.trap_registry.TRAP_EMITTERS`."""
    out: dict[str, set[str]] = {}
    for key, row in TRAP_EMITTERS.items():
        if not row.per_site:
            continue
        for kind in row.obligations:
            out.setdefault(kind, set()).add(key)
    return {kind: frozenset(keys) for kind, keys in out.items()}


#: Obligation kind -> the emitters whose checks are its runtime half.
EMITTERS_BY_KIND: dict[str, frozenset[str]] = _emitters_by_kind()

#: Every obligation kind the verifier records.
OBLIGATION_KINDS: frozenset[str] = frozenset(get_args(ObligationKind))


@dataclass(frozen=True)
class Mismatch:
    """One disagreement between the obligation records and the module."""

    kind: MismatchKind
    obligation: str
    """The record's kind, or the kinds the check is the runtime half of
    (comma-separated)."""

    file: str | None
    line: int
    column: int
    function: str
    """The record's function (``fn_name``), or the WASM function the check
    sits in."""

    status: str = ""
    """The record's status; empty for a check."""

    emitter: str = ""
    """The check's emitter (a :data:`TRAP_EMITTERS` key); empty for a
    record."""

    detail: str = ""
    """Why it is a mismatch, in words."""

    def to_dict(self) -> dict[str, object]:
        """A JSON-compatible form (field names as keys)."""
        return {
            "kind": self.kind,
            "obligation": self.obligation,
            "file": self.file,
            "line": self.line,
            "column": self.column,
            "function": self.function,
            "status": self.status,
            "emitter": self.emitter,
            "detail": self.detail,
        }


@dataclass(frozen=True, eq=False)
class EntryCall:
    """One call that reaches the function an entry check guards (a
    `requires` clause, a refined parameter's guard)."""

    callers: frozenset[str]
    """The module functions the call is written in: the function whose
    region of the source holds it, every clone of a generic one."""

    records: tuple[ProofObligation, ...]
    """The records at the call the check stands for: none where the
    verifier discharged the call's obligation and recorded nothing, as it
    does for the precondition of a call into a user function."""


@dataclass
class Reconciliation:
    """The join's whole result: the mismatches, and what agreed."""

    mismatches: list[Mismatch] = field(default_factory=list)
    pairs: list[tuple[ProofObligation, EmittedCheck]] = field(
        default_factory=list)
    """Every (record, check) the join paired, the check answering the
    record."""

    absent: list[ProofObligation] = field(default_factory=list)
    """Records claiming a guard inside a function the module has no code
    for."""

    out_of_scope: list[EmittedCheck] = field(default_factory=list)
    """Checks in code this run did not verify (prelude and imported
    bodies)."""

    answers: list[tuple[ProofObligation, EmittedCheck]] = field(
        default_factory=list)
    """Every (record, check) the join relates, whatever the record's status:
    the check stands for the record's site, or for one arm of the join the
    record stands at.  Wider than ``pairs`` in three ways: a record that
    claims no runtime check is related too; each of several records at one
    site is related to every check that site offers, before the one-to-one
    matching (:func:`_match_sites`) gives each its own; and an arm's check is
    related to the join's record whether or not every arm has one.  It is
    what ``vera test --distrust`` reads a trap against
    (``vera.tester._TrapIndex``)."""

    entry: list[EmittedCheck] = field(default_factory=list)
    """The checks a function makes on entry for the call that entered it:
    each `requires` clause and each refined parameter's guard.  Each stands
    for the records at the calls that reach the function, never for one of
    the function's own."""

    entry_calls: dict[EmittedCheck, list[EntryCall]] = field(
        default_factory=dict)
    """Each entry check's calls: every call in the programs the run covered
    that reaches the check's function, with the module functions it is
    written in and the records at it the check stands for (``answers``,
    narrowed to the call).  A run of a function makes only the calls written
    in the functions it reaches, so what a trapped check stands for in that
    run is those calls' records, and a reached call with no record is a
    proof no record names (``vera.tester._TrapIndex``)."""


_WAT_FN_DEF_RE = re.compile(r"^\s*\(func \$:?([^\s()]+)", re.MULTILINE)


def _function_regions(
    compile_result: CompileResult,
) -> dict[tuple[str, int, int], frozenset[str]]:
    """(file, first line, last line) of every function the module defines,
    from the trap source map code generation keeps for each of them, with
    the module functions compiled from it — a clone under its generic's
    entry, as the record of checks reads it."""
    out: dict[tuple[str, int, int], set[str]] = {}
    source = compile_result.fn_source_map
    for match in _WAT_FN_DEF_RE.finditer(compile_result.wat):
        name = match.group(1)
        entry = source.get(name) or source.get(name.rsplit("$", 1)[0])
        if entry is None:
            continue
        key = _file_key(entry[0])
        if key is not None:
            out.setdefault((key, entry[1], entry[2]), set()).add(name)
    return {region: frozenset(names) for region, names in out.items()}


# =====================================================================
# The join, by row identity
# =====================================================================


def _function_files(
    program: ast.Program, file: str | None,
    resolved_modules: Iterable[ResolvedModule],
) -> dict[int, str | None]:
    """The file each function body is written in, by the body's identity
    (every top-level function and ``where`` helper of the entry program and
    of each module)."""
    out: dict[int, str | None] = {}

    def add(decl: ast.FnDecl, where: str | None) -> None:
        if decl.body is not None:
            out[id(decl.body)] = where
        for helper in decl.where_fns or ():
            add(helper, where)

    for tld in program.declarations:
        if isinstance(tld.decl, ast.FnDecl):
            add(tld.decl, file)
    for module in resolved_modules:
        for tld in module.program.declarations:
            if isinstance(tld.decl, ast.FnDecl):
                add(tld.decl, str(module.file_path))
    return out


def _written_in(
    regions: dict[tuple[str, int, int], frozenset[str]],
    file: str | None, line: int,
) -> frozenset[str]:
    """The module functions the line *line* of *file* is written in: those
    of the innermost region that holds it (a closure's, inside its
    function's), or none when no region holds it."""
    key = _file_key(file)
    if key is None or not line:
        return frozenset()
    holding = [(end - start, names) for (rkey, start, end), names in regions.items()
               if rkey == key and start <= line <= end]
    if not holding:
        return frozenset()
    narrowest = min(extent for extent, _ in holding)
    return frozenset().union(
        *(names for extent, names in holding if extent == narrowest))


def _file_key(file: str | None) -> str | None:
    """*file* as the regions key it: its resolved path's POSIX spelling,
    or its own where it does not resolve (a symlink loop raises
    `RuntimeError` on Python 3.11 and 3.12, `OSError` from 3.13); an empty
    name keys nothing."""
    if not file:
        return None
    try:
        return Path(file).resolve().as_posix()
    except (OSError, RuntimeError):
        return Path(file).as_posix()


def join(
    verify_result: VerifyResult,
    compile_result: CompileResult,
    *,
    program: ast.Program,
    file: str | None,
    resolved_modules: Iterable[ResolvedModule] = (),
) -> Reconciliation:
    """Join *verify_result*'s records with *compile_result*'s checks by the
    obligation table's rows (see the module docstring).

    *program* and *file* are the entry program the two were produced from,
    *resolved_modules* the modules it imports: they say which file each
    function is written in, for the calls an entry check stands for."""
    from vera.binding import source_name
    from vera.obligations.table import ENTRY

    table = verify_result.table
    out = Reconciliation()
    if table is None:
        return out
    resolved_modules = list(resolved_modules)
    rows = table.rows
    records = list(verify_result.obligations)
    checks = list(compile_result.emitted_checks)
    regions = _function_regions(compile_result)
    held = {source_name(m.group(1))
            for m in _WAT_FN_DEF_RE.finditer(compile_result.wat)}

    def is_held(fn: str) -> bool:
        return fn in held or fn.split("$where$")[0] in held

    by_row: dict[int, list[EmittedCheck]] = {}
    for check in checks:
        if check.row is not None:
            if not 0 <= check.row < len(rows):
                raise AssertionError(
                    f"a check names row {check.row}, which the verifier's "
                    f"table of {len(rows)} rows does not hold")
            by_row.setdefault(check.row, []).append(check)

    def answering(row_id: int) -> int | None:
        found = table.answered(rows[row_id])
        return None if found is None else found.id

    recorded: dict[int, list[ProofObligation]] = {}
    for record in records:
        for rid in record.rows:
            recorded.setdefault(rid, []).append(record)
    #: The rows a row's check answers: itself, and every row answered by it.
    answers_of: dict[int, list[int]] = {}
    for row in rows:
        target = answering(row.id)
        if target is not None:
            answers_of.setdefault(target, []).append(row.id)
    verified_fns = {rows[rid].fn for rid in recorded}

    # The relation: each record with every check of each of its rows.
    for record in records:
        related: dict[int, EmittedCheck] = {}
        for rid in record.rows:
            target = answering(rid)
            for check in by_row.get(target if target is not None else -1, ()):
                related.setdefault(id(check), check)
        out.answers.extend((record, check) for check in related.values())

    # The record side.
    for record in records:
        if record.status not in CLAIMS_GUARD or record.kind in EXCLUDED_KINDS:
            continue
        if record.kind not in EMITTERS_BY_KIND:
            out.mismatches.append(_record_mismatch(
                "no_mapping", record,
                "no emitter in vera.trap_registry.TRAP_EMITTERS answers "
                "this obligation kind"))
            continue
        found: list[EmittedCheck] = []
        missing: Row | None = None
        any_held = False
        for rid in record.rows:
            row = rows[rid]
            if not row.guard.check:
                continue
            target = answering(rid)
            if target is None:
                continue
            got = by_row.get(target, [])
            if got:
                found.extend(got)
                continue
            if is_held(rows[target].fn):
                any_held = True
                missing = missing or row
        if missing is not None and any_held:
            span = missing.node.span
            where = f" at {span.line}:{span.column}" if span is not None else ""
            ev = (f" (evaluated at {missing.evaluation[0]})"
                  if missing.evaluation and missing.evaluation[0] != "body" else "")
            out.mismatches.append(_record_mismatch(
                "recorded_unguarded", record,
                f"the compiled module holds no check for its row{where}{ev}"))
        elif found:
            out.pairs.extend((record, check) for check in found)
        else:
            out.absent.append(record)

    # The check side.
    for check in checks:
        crow = rows[check.row] if check.row is not None else None
        if crow is not None and (
                crow.kind == "requires" or crow.evaluation == ENTRY):
            out.entry.append(check)
        if check.prelude:
            out.out_of_scope.append(check)
            continue
        if crow is None:
            if check.line == 0:
                # A generated helper shared by every rendering of its type
                # (`_record_shared_check`, #1482): no site, no row.
                out.out_of_scope.append(check)
            else:
                out.mismatches.append(_check_mismatch(
                    "no_mapping", check, "the check names no row"))
            continue
        if crow.fn not in verified_fns:
            out.out_of_scope.append(check)
            continue
        named = [rid for rid in (crow.id, *answers_of.get(crow.id, ()))
                 if rid in recorded]
        if named:
            continue
        out.mismatches.append(_check_mismatch(
            "guarded_unrecorded", check,
            "this run recorded no obligation for the check's row"))

    # Each entry check's calls: every row its check answers at a call, with
    # the module functions the call is written in and the records of it.
    files = _function_files(program, file, resolved_modules)
    body_of: dict[int, int] = {}
    for body, ids in table.by_body.items():
        for rid in ids:
            body_of[rid] = body
    for check in out.entry:
        assert check.row is not None  # noqa: S101 — entry checks name rows
        calls: list[EntryCall] = []
        for rid in answers_of.get(check.row, ()):
            if rid == check.row:
                continue
            row = rows[rid]
            recs = tuple(r for r in recorded.get(rid, ())
                         if r.kind not in EXCLUDED_KINDS)
            in_file: str | None = next((r.file for r in recs if r.file), None)
            if in_file is None:
                in_file = files.get(body_of.get(rid, -1), file)
            span = row.node.span
            calls.append(EntryCall(
                _written_in(regions, in_file, span.line if span else 0), recs))
        out.entry_calls[check] = calls

    seen: set[Mismatch] = set()
    kept: list[Mismatch] = []
    for m in out.mismatches:
        if not m.status and m in seen:
            continue
        seen.add(m)
        kept.append(m)
    out.mismatches = sorted(kept, key=_mismatch_order)
    return out


def _check_mismatch(
    kind: MismatchKind, check: EmittedCheck, detail: str,
) -> Mismatch:
    return Mismatch(
        kind=kind, obligation=",".join(check.obligations), file=check.file,
        line=check.line, column=check.column, function=check.function,
        emitter=check.emitter, detail=detail,
    )


def _record_mismatch(
    kind: MismatchKind, record: ProofObligation, detail: str,
) -> Mismatch:
    return Mismatch(
        kind=kind, obligation=record.kind, file=record.file,
        line=record.line, column=record.column,
        function=(f"{record.owner}.{record.fn_name}" if record.owner
                  else record.fn_name),
        status=record.status, detail=detail,
    )


def _mismatch_order(m: Mismatch) -> tuple[str, int, int, str, str]:
    return (m.file or "", m.line, m.column, m.kind, m.obligation)


def reconcile(
    verify_result: VerifyResult,
    compile_result: CompileResult,
    *,
    program: ast.Program,
    file: str | None,
    resolved_modules: Iterable[ResolvedModule] = (),
) -> list[Mismatch]:
    """Every mismatch between *verify_result*'s records and the checks
    *compile_result* holds (see :func:`join` for the arguments)."""
    return join(
        verify_result, compile_result, program=program, file=file,
        resolved_modules=resolved_modules,
    ).mismatches


# =====================================================================
# Diagnostics
# =====================================================================

def mismatch_diagnostics(
    mismatches: Iterable[Mismatch], sources: dict[str, str],
) -> list[Diagnostic]:
    """One diagnostic per mismatch: E541 (an error) for a record whose
    runtime-check claim the module does not answer, W004 (a warning) for a
    check no record accounts for.  A ``no_mapping`` takes the code of its
    direction — a record the join cannot place is a claim it could not
    confirm, a check it cannot place one it could not account for — and
    says so in its description.  *sources* maps each file to its text, for
    the source line."""
    texts = {_file_key(f): text.splitlines() for f, text in sources.items()}
    out: list[Diagnostic] = []
    for m in mismatches:
        lines = texts.get(_file_key(m.file), [])
        source_line = lines[m.line - 1] if 1 <= m.line <= len(lines) else ""
        location = SourceLocation(file=m.file, line=m.line, column=m.column)
        if m.status:
            what = (
                f"but {m.detail}" if m.kind == "recorded_unguarded" else
                f"and the reconciliation cannot place it: {m.detail}"
            )
            out.append(Diagnostic(
                description=(
                    f"The '{m.obligation}' obligation in '{m.function}' is "
                    f"recorded as checked at run time ({m.status}), {what}."
                ),
                location=location,
                source_line=source_line,
                rationale=(
                    "`vera verify` counts a `tier3` or `timeout` obligation as "
                    "runtime-guarded: code generation is meant to emit a check "
                    "that traps when the property fails.  The verifier and "
                    "code generation decide that separately, and this run "
                    "compiled the program and found no emitted check for "
                    "this obligation, so the claim is not true of the "
                    "compiled module."
                    if m.kind == "recorded_unguarded" else
                    "`vera verify` counts a `tier3` or `timeout` obligation as "
                    "runtime-guarded: code generation is meant to emit a check "
                    "that traps when the property fails.  This run "
                    "compiled the program but could not relate this record "
                    "to the program or to any emitter, so it cannot say "
                    "whether the module checks it: the claim is unconfirmed, "
                    "which the reconciliation reports rather than skips."
                ),
                fix=(
                    "This is a disagreement inside the compiler, not an error "
                    "in the program: report it with the program attached.  "
                    "Until it is fixed, do not rely on a runtime check here — "
                    "make the property provable instead, with a `requires` "
                    "clause or an `if` guard around the operation, so it is "
                    "discharged at Tier 1."
                ),
                spec_ref='Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
                severity="error",
                error_code="E541",
                tier=3,
            ))
            continue
        what = (
            m.detail if m.kind == "guarded_unrecorded" else
            f"the reconciliation cannot place the check: {m.detail}"
        )
        out.append(Diagnostic(
            description=(
                f"The compiled module checks this site in '{m.function}' "
                f"(the runtime half of '{m.obligation}'), but {what}."
            ),
            location=location,
            source_line=source_line,
            rationale=(
                "Every runtime check in the compiled module is meant to be "
                "the runtime half of an obligation `vera verify` recorded, so "
                "that the verification summary accounts for each check the "
                "program performs.  The module checks this site at run time "
                "and no record of this run answers the check, so the summary "
                "omits it.  The check still runs: it is a dead guard on a "
                "value the checker already typed, a check at a site that "
                "cannot fail, or a gap in the verifier's accounting."
                if m.kind == "guarded_unrecorded" else
                "Every runtime check in the compiled module is meant to be "
                "the runtime half of an obligation `vera verify` recorded.  "
                "This run could not relate this check to a site of the "
                "program it knows how to pair, so it cannot say which record "
                "accounts for it; the check still runs, and the "
                "reconciliation reports the gap rather than skips it."
            ),
            spec_ref='Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
            severity="warning",
            error_code="W004",
        ))
    return out


def report_dict(reconciliation: Reconciliation | None) -> dict[str, object]:
    """The ``reconciliation`` object of ``vera verify --json``: whether the
    module compiled, the counts, and every mismatch.  None stands for a
    compile that failed, which leaves nothing to join."""
    if reconciliation is None:
        return {"compiled": False, "matched": 0, "recorded_unguarded": 0,
                "guarded_unrecorded": 0, "no_mapping": 0, "absent": 0,
                "out_of_scope": 0, "mismatches": []}
    kinds = [m.kind for m in reconciliation.mismatches]
    return {
        "compiled": True,
        "matched": len({id(record) for record, _ in reconciliation.pairs}),
        "recorded_unguarded": kinds.count("recorded_unguarded"),
        "guarded_unrecorded": kinds.count("guarded_unrecorded"),
        "no_mapping": kinds.count("no_mapping"),
        "absent": len(reconciliation.absent),
        "out_of_scope": len(reconciliation.out_of_scope),
        "mismatches": [m.to_dict() for m in reconciliation.mismatches],
    }


def summary_line(reconciliation: Reconciliation) -> str | None:
    """The one-line reconciliation summary ``vera verify`` prints after the
    verification summary, or None when the program claims no runtime check
    (Tier 3), which leaves nothing to say."""
    matched = len({id(record) for record, _ in reconciliation.pairs})
    claims = matched + len(reconciliation.absent) + sum(
        1 for m in reconciliation.mismatches if m.status)
    if not claims:
        return None
    text = (
        f"Reconciliation: {matched} of {claims} runtime checks (Tier 3) "
        f"found in the compiled module"
    )
    if reconciliation.absent:
        text += (
            f", {len(reconciliation.absent)} in a function the module holds "
            f"no code for"
        )
    return text


# =====================================================================
# The pipeline, as `vera verify` runs it
# =====================================================================

#: The code generation refusal a join is skipped for rather than failed on:
#: a program holding typed holes (E614).  `vera check` accepts one with a
#: W001 per hole, and the verifier verifies the rest of it; code generation
#: compiles nothing until every hole is filled, so there is no module to
#: join, and refusing the verification would take the hole workflow's
#: feedback away (spec Section 4.17).
SKIPPED_FOR = "E614"


@dataclass
class Reconciled:
    """What ``vera verify`` adds to a verification unless
    ``--no-reconcile``: the program compiled as ``vera compile`` compiles
    it, the join, and the diagnostics the two give."""

    compile_result: CompileResult
    reconciliation: Reconciliation | None
    """None when code generation refused the program: nothing to join."""

    diagnostics: list[Diagnostic]
    """The compile's own diagnostics, then one per mismatch
    (:func:`mismatch_diagnostics`); for a program holding typed holes, the
    one W005 warning that says the join was skipped."""

    skipped: str = ""
    """Why the join did not run although ``--no-reconcile`` was not given:
    the program holds typed holes.  Empty when it ran, or the compile
    refused the program for another reason."""

    def report(self) -> dict[str, object]:
        """The ``reconciliation`` object of ``vera verify --json``."""
        if self.skipped:
            return {"skipped": self.skipped}
        return report_dict(self.reconciliation)


def compile_for_reconcile(
    typed: TypedProgram, source: str, file: str | None,
) -> CompileResult:
    """Compile the typed program exactly as ``vera compile`` does."""
    from vera.codegen import compile as codegen_compile

    return codegen_compile(typed, source=source, file=file)


def _holes_skip(holes: list[Diagnostic], source: str) -> Diagnostic:
    """The W005 warning for a join skipped because the program holds typed
    holes, located at the first."""
    first = holes[0]
    lines = source.splitlines()
    line = first.location.line
    count = (f"{len(holes)} typed holes" if len(holes) > 1
             else "a typed hole")
    return Diagnostic(
        description=(
            f"The runtime checks are not reconciled: the program holds "
            f"{count}, and code generation compiles a program only once every "
            f"hole is filled (E614), so there is no compiled module to hold "
            f"its Tier 3 claims to."
        ),
        location=SourceLocation(
            file=first.location.file, line=line, column=first.location.column),
        source_line=lines[line - 1] if 1 <= line <= len(lines) else "",
        rationale=(
            "`vera verify` compiles the program in process and joins each "
            "runtime-check claim (`tier3`, `timeout`) with the check the "
            "compiled module holds for it.  A typed hole has no runtime "
            "behaviour, so code generation refuses the program, and the "
            "verification of the rest of it stands on its own: every proof "
            "and every disclosure above is the verifier's, and no Tier 3 "
            "claim has been held to a compiled check."
        ),
        fix=(
            "Fill each hole with an expression of the type its W001 warning "
            "names; `vera verify` then compiles the program and reconciles "
            "its runtime checks."
        ),
        spec_ref='Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
        severity="warning",
        error_code="W005",
    )


def reconcile_verified(
    typed: TypedProgram,
    source: str,
    file: str | None,
    verify_result: VerifyResult,
) -> Reconciled:
    """Compile the typed program and join *verify_result*'s records with the
    checks the module holds, as ``vera verify`` does unless
    ``--no-reconcile``.

    A program code generation refuses leaves nothing to join: its refusal
    is the answer, with one exception, a program holding typed holes, for
    which the join is skipped with a W005 warning (:data:`SKIPPED_FOR`)."""
    program, resolved_modules = typed.program, typed.modules
    compiled = compile_for_reconcile(typed, source, file)
    holes = [d for d in compiled.diagnostics
             if d.severity == "error" and d.error_code == SKIPPED_FOR]
    if holes:
        return Reconciled(
            compiled, None, [_holes_skip(holes, source)],
            skipped="the program holds typed holes, which code generation "
                    "refuses (E614)")
    diagnostics = list(compiled.diagnostics)
    if not compiled.ok:
        return Reconciled(compiled, None, diagnostics)
    joined = join(verify_result, compiled, program=program, file=file,
                  resolved_modules=resolved_modules)
    sources = {str(module.file_path): module.source
               for module in resolved_modules}
    if file is not None:
        sources[file] = source
    diagnostics += mismatch_diagnostics(joined.mismatches, sources)
    return Reconciled(compiled, joined, diagnostics)


@dataclass
class ReconcileRun:
    """One program through check, verify, compile and the join."""

    path: Path
    check_errors: list[str] = field(default_factory=list)
    compile_errors: list[str] = field(default_factory=list)
    program: ast.Program | None = None
    resolved_modules: list[ResolvedModule] = field(default_factory=list)
    verify_result: VerifyResult | None = None
    compile_result: CompileResult | None = None
    reconciliation: Reconciliation | None = None

    @property
    def mismatches(self) -> list[Mismatch]:
        """The join's mismatches; empty when the pipeline stopped early."""
        return [] if self.reconciliation is None else (
            self.reconciliation.mismatches)


def reconcile_file(
    path: str | Path, timeout_ms: int | None = None,
) -> ReconcileRun:
    """Check, verify, compile and join the program at *path*, in process,
    with the same calls ``vera verify`` makes.  A compile refusal, a typed
    hole's included, stops the run before the join."""
    from vera.checker import typecheck_with_artifacts
    from vera.parser import parse, read_source
    from vera.resolver import ModuleResolver
    from vera.transform import transform
    from vera.typed import build
    from vera.verifier import verify

    p = Path(path)
    run = ReconcileRun(path=p)
    try:
        source = read_source(p)
        program = transform(parse(source, file=str(p)))  # pragma: no mutate — the label reaches only a refusal's location, and reconcile_file records its description
    except VeraError as exc:
        # A source that is not UTF-8 (E024), or a parse or transform
        # refusal, is the program's own: a stop before the join, as `vera
        # verify` reports it, never an exception.
        run.check_errors = [exc.diagnostic.description]
        return run
    resolver = ModuleResolver(_root=p.parent)
    resolved = resolver.resolve_imports(program, p)
    run.program, run.resolved_modules = program, resolved
    check_diags, artifacts = typecheck_with_artifacts(
        program, source, file=str(p), resolved_modules=resolved,
    )
    run.check_errors = [
        d.description for d in resolver.errors + check_diags
        if d.severity == "error"
    ]
    if run.check_errors:
        return run
    typed = build(program, resolved, artifacts)
    run.verify_result = verify(typed, source, file=str(p),
                               timeout_ms=timeout_ms)
    reconciled = reconcile_verified(typed, source, str(p), run.verify_result)
    run.compile_result = reconciled.compile_result
    run.compile_errors = [
        d.description for d in run.compile_result.diagnostics
        if d.severity == "error"
    ]
    run.reconciliation = reconciled.reconciliation
    return run
