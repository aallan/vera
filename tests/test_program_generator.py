"""The program generator's three differentials: what checks compiles and loads with every public function exported; every obligation record has its guard and every guard its record; a Tier 1 proof meets no runtime violation on generated inputs.

`tests/program_generator.py` writes a whole Vera program from a seed, typed
from its own binding environment, with contracts true of every input their
`requires` admits.  This file holds that program to the toolchain, in process
through `tests/pipeline.py`:

* **The generator's own contract**: the program passes `vera check` with no
  diagnostic, is in `vera fmt`'s canonical form, and `vera verify` answers
  every query inside its default budget with no error.
* **(1) Load**: it compiles with no E6xx diagnostic, its exports are its
  public functions, and each runs to completion on the arguments the
  generator chose for it.
* **(2) Reconcile**: `vera/reconcile.py`'s join over its verification and its
  module reports no mismatch outside :data:`KNOWN_CLASSES`, which reads
  `scripts/check_reconciliation.py`'s `KNOWN` as classes.  A mismatch inside
  one is counted under the issue its entry names and fails nothing.
* **(3) Distrust**: `vera test --distrust` reports no refuted proof (E703), no
  trap it cannot attribute, and no failing trial at all, since every contract
  is true by construction.

Every pull request runs the contract and the three differentials over the ten
pinned :data:`SEEDS`, and holds the instrument to its own contract: a seed
writes its program byte for byte in every process, a hundred seeds reach
every construct of version one, each differential reports a hand-written
program that breaks it and passes that program's nearest neighbour that does
not, the minimiser keeps the failure it shrinks, and each known class still
has its shape.  The nightly lane (`.github/workflows/nightly-generator.yml`)
runs the same cell over the night's seeds, which ``VERA_GENERATOR_SEEDS``
names (:func:`night_seeds`).  A find outside the known classes is minimised
and written with its seed, its minimal program and what the generator
expected of it under ``VERA_GENERATOR_OUT``, and fails the seed's cell.

The program a seed writes is ``python -m tests.program_generator SEED``.
"""

from __future__ import annotations

import datetime
import json
import os
import re
import subprocess
import sys
import time
from collections.abc import Callable, Sequence
from dataclasses import dataclass, replace
from pathlib import Path

import pytest

from tests import pipeline
from tests import program_generator as gen
from tests.test_distrust_corpus import _FALSE_PROOF
from vera import ast, narrowing
from vera.formatter import format_source
from vera.obligations.cache import walk_nodes
from vera.reconcile import Mismatch, join

ROOT = Path(__file__).resolve().parent.parent

#: The label every program is checked, verified, compiled and tested under:
#: the file name a report gives the program.
LABEL = "generated.vera"

#: The pull request lane's seeds.
SEEDS = tuple(range(10))

#: Trials per public function in the distrust differential.
TRIALS = int(os.environ.get("VERA_GENERATOR_TRIALS", "20"))

#: A night's seeds start at its day's offset times this stride, so no two
#: nights share a seed whatever their count (:func:`night_seeds`).
NIGHT_STRIDE = 100_000

#: The first night of the stride's day count.
NIGHT_EPOCH = datetime.date(2026, 10, 1)

#: The most candidates the minimiser tries for one find.
MINIMISE_BUDGET = 300

#: The most finds one test process minimises: a change that breaks every
#: program would otherwise spend the night minimising.  A find past it is
#: recorded with its whole program.
MINIMISE_LIMIT = 10

#: How many finds this process has minimised.
_minimised = [0]


# =====================================================================
# Finds
# =====================================================================

@dataclass(frozen=True)
class Find:
    """One thing a program did that a differential says it must not."""

    #: ``contract`` (the generator's own), ``load``, ``reconcile`` or
    #: ``distrust``.
    differential: str
    #: What the minimiser holds fixed while it shrinks the program.
    signature: tuple[str, ...]
    #: The diagnostic or the mismatch, in words.
    detail: str
    #: The open issue whose class it is (``"#1695 (#1629)"``), or empty.
    known: str = ""
    #: The function a failing call or trial ran, and its arguments, in
    #: parameter order.
    function: str = ""
    args: tuple[int | bool, ...] = ()
    #: What identifies the find when lines move: a verify error's code and
    #: description, without its location.
    key: str = ""
    #: Why it is known, or why a known class's test did not hold of it.
    evidence: str = ""

    def to_dict(self) -> dict[str, object]:
        return {"differential": self.differential,
                "signature": list(self.signature), "detail": self.detail,
                "known": self.known, "function": self.function,
                "args": list(self.args), "evidence": self.evidence}


@dataclass
class Stages:
    """One program's stages, each run once: the verification (with its
    check), the module, and the distrust test."""

    source: str
    verified: pipeline.Verified
    compiled: pipeline.Compiled
    tested: pipeline.Tested | None = None

    @classmethod
    def of(cls, source: str) -> Stages:
        return cls(source, pipeline.verify(source, file=LABEL),
                   pipeline.compile(source, file=LABEL))

    def distrust(self, trials: int) -> pipeline.Tested:
        if self.tested is None:
            self.tested = pipeline.contract_test(
                self.source, file=LABEL, trials=trials, distrust=True)
        return self.tested


# =====================================================================
# The generator's own contract
# =====================================================================

def contract_finds(source: str, stages: Stages | None = None) -> list[Find]:
    """What the generator promises of every program: `vera check` reports no
    diagnostic at all, the text is `vera fmt`'s canonical form, and `vera
    verify` answers every query inside its default budget with no error.

    A program that breaks it is the generator's bug or the toolchain's: every
    contract the generator writes holds of every input the function's
    `requires` admits, so a refutation is wrong arithmetic in the generator
    or a wrong model in the verifier, and the minimal program says which."""
    verified = stages.verified if stages is not None else pipeline.verify(
        source, file=LABEL)
    finds = [
        Find("contract", ("check", d.error_code or d.severity), d.format())
        for d in verified.checked.diagnostics
    ]
    canonical = format_source(source, file=LABEL)
    if canonical != source:
        finds.append(Find("contract", ("fmt",), _first_difference(
            source, canonical)))
    if finds or not verified.ran:
        return finds
    finds += [
        Find("contract", ("verify", d.error_code or "error"), d.format(),
             key=f"{d.error_code}: {d.description}")
        for d in verified.errors
    ]
    finds += [
        Find("contract", ("verify", "timeout", o.kind),
             f"the {o.kind} obligation in '{o.fn_name}' at {o.line}:"
             f"{o.column} exhausted the solver's default budget")
        for o in verified.obligations if o.status == "timeout"
    ]
    return finds


#: The class of a verify error that vanishes when each function first names,
#: in an unused `let`, every data type it constructs and does not name in its
#: signature: the verifier walks a function's signature and `let`s for a data
#: type's sort instead of reading the checker's types, so a construction it
#: finds no sort for does not translate, and a call taking it loses the
#: callee's postcondition (`program_generator.name_constructed_types`).
CONSTRUCTED_SORT_ISSUE = "#1525"


def classify_contract(
    prog: gen.Program, finds: list[Find], stages: Stages,
) -> tuple[list[Find], gen.Program | None]:
    """*finds* with each verify error that #1525's counterfactual removes
    marked known, and the counterfactual program when it removes every find
    of the contract: the program the three differentials then run over.

    Run only on a program whose contract failed.  A verify error that
    survives the counterfactual stays a find; so does every error when the
    counterfactual reports one the program did not, since it no longer
    isolates the class.  Each verify error's evidence names the outcome and
    every obligation whose status the counterfactual changed."""
    errors = [f for f in finds if f.signature[0] == "verify" and f.key]
    named = gen.name_constructed_types(prog) if errors else None
    if named is None:
        return finds, None
    after = Stages.of(named.render())
    after_finds = contract_finds(after.source, after)
    before_keys = {f.key for f in finds}
    new = [f for f in after_finds if f.key not in before_keys or not f.key]
    survived = {f.key for f in after_finds}
    changed = _status_changes(stages.verified, after.verified)
    out: list[Find] = []
    for f in finds:
        if f not in errors:
            out.append(f)
        elif new:
            out.append(replace(f, evidence=(
                "the counterfactual reported what the program did not: "
                + "; ".join(x.key or " ".join(x.signature) for x in new))))
        elif f.key in survived:
            out.append(replace(f, evidence=(
                "survived the counterfactual (an unused `let` of each data "
                "type a function constructs and does not name)")))
        else:
            out.append(replace(f, known=CONSTRUCTED_SORT_ISSUE, evidence=(
                "vanished under the counterfactual (an unused `let` of each "
                "data type a function constructs and does not name); "
                "statuses that changed: " + ("; ".join(changed) or "none"))))
    if all(f.known for f in out) and not after_finds:
        return out, named
    return out, None


def _statuses(verified: pipeline.Verified) -> dict[tuple[str, str, str, int], str]:
    """Each obligation's status, keyed by what does not move when lines
    do: its function, kind, text and place among its namesakes."""
    seen: dict[tuple[str, str, str], int] = {}
    out: dict[tuple[str, str, str, int], str] = {}
    if not verified.ran:
        return out
    for o in verified.obligations:
        k = (o.fn_name, o.kind, o.expr_text)
        out[(*k, seen.get(k, 0))] = o.status
        seen[k] = seen.get(k, 0) + 1
    return out


def _status_changes(before: pipeline.Verified, after: pipeline.Verified) -> list[str]:
    a, b = _statuses(before), _statuses(after)
    return [
        f"{kind} in '{fn}' (`{text}`): {a.get(key, 'absent')} -> "
        f"{b.get(key, 'absent')}"
        for key in sorted(set(a) | set(b))
        for fn, kind, text, _ in (key,)
        if a.get(key) != b.get(key)
    ]


def _first_difference(source: str, canonical: str) -> str:
    for n, (mine, theirs) in enumerate(
            zip(source.splitlines(), canonical.splitlines()), start=1):
        if mine != theirs:
            return (f"not in canonical form at line {n}: wrote {mine!r}, "
                    f"vera fmt writes {theirs!r}")
    return "not in canonical form: the two differ in length"


# =====================================================================
# Differential 1: what checks compiles and loads, every public function
# exported and callable
# =====================================================================

def public_functions(program: ast.Program) -> list[str]:
    return [tld.decl.name for tld in program.declarations
            if isinstance(tld.decl, ast.FnDecl)
            and tld.visibility == "public"]


def load_finds(
    source: str, calls: Sequence[tuple[str, Sequence[int] | None]],
    stages: Stages | None = None,
) -> list[Find]:
    """Compile *source* as `vera compile` does, and run each of *calls* in
    the module it builds.

    The module must compile with no E6xx diagnostic and no error, export
    exactly the program's public functions, and run each call to completion:
    *calls* names every public function with the arguments to call it on
    (``None`` for one that takes none), which satisfy its `requires`."""
    compiled = stages.compiled if stages is not None else pipeline.compile(
        source, file=LABEL)
    if compiled.checked is None or not compiled.checked.ok:
        return []  # the contract's find
    finds = [
        Find("load", ("compile", d.error_code or "error"), d.format())
        for d in compiled.diagnostics
        if (d.error_code or "").startswith("E6") or d.severity == "error"
    ]
    if compiled._result is None or compiled.errors:
        return finds
    public = public_functions(compiled.parsed.program)
    exports = list(compiled.exports)
    finds += [
        Find("load", ("export", "missing"),
             f"the public function '{name}' is not exported "
             f"(exports: {', '.join(exports) or 'none'})", function=name)
        for name in public if name not in exports
    ]
    finds += [
        Find("load", ("export", "unexpected"),
             f"'{name}' is exported but no public function declares it",
             function=name)
        for name in exports if name not in public
    ]
    called = {name for name, _ in calls}
    finds += [
        Find("load", ("call", "unnamed"),
             f"the public function '{name}' has no call to run it on",
             function=name)
        for name in public if name not in called
    ]
    for name, args in calls:
        if name not in exports:
            continue
        ran = pipeline.run(compiled, fn=name,
                           args=list(args) if args is not None else None)
        if not ran.ok:
            kind = ran.trap.kind if ran.trap is not None else "refused"
            finds.append(Find(
                "load", ("call", kind),
                f"'{name}' on {list(args or [])} did not return: "
                f"{ran.trap if ran.trap is not None else ran.diagnostics}",
                function=name, args=tuple(args or ())))
    return finds


# =====================================================================
# Differential 2: every obligation record has its guard and every guard
# its record
# =====================================================================

class Sites:
    """The checked program's nodes by where they start, its constructors'
    fields and its functions' returns, for the known-class predicates."""

    def __init__(self, checked: pipeline.Checked) -> None:
        self.program = checked.program
        self._at: dict[tuple[int, int], list[ast.Node]] = {}
        for node in walk_nodes(self.program):
            span = node.span
            if span is not None:
                self._at.setdefault((span.line, span.column), []).append(node)
        self.fields: dict[str, list[ast.TypeExpr]] = {}
        self.returns: dict[str, ast.TypeExpr] = {}
        for tld in self.program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.DataDecl):
                for ctor in decl.constructors:
                    self.fields[ctor.name] = list(ctor.fields or ())
            elif isinstance(decl, ast.FnDecl):
                self.returns[decl.name] = decl.return_type

    def at(self, mismatch: Mismatch) -> list[ast.Node]:
        return self._at.get((mismatch.line, mismatch.column), [])

    def call_returns_nat(self, call: ast.Expr) -> str | None:
        """The call-type oracle the static rule lacks (#1557): a call's
        declared return, read from the program's own declaration."""
        ret = self.returns.get(getattr(call, "name", ""))
        if isinstance(ret, ast.NamedType) and ret.name == "Nat":
            return "Nat"
        return None


def _is_name(te: ast.TypeExpr, name: str) -> bool:
    return isinstance(te, ast.NamedType) and te.name == name and not te.type_args


def _division_by(node: ast.Node, *, literal: bool) -> bool:
    if not (isinstance(node, ast.BinaryExpr)
            and node.op in (ast.BinOp.DIV, ast.BinOp.MOD)):
        return False
    divisor = node.right
    is_literal = isinstance(divisor, ast.IntLit) and divisor.value != 0
    return is_literal if literal else node.op == ast.BinOp.DIV


def _nat_field_binder(node: ast.Node, sites: Sites) -> bool:
    """A `@Nat` binder of a constructor pattern whose field is a `Nat`: the
    value it binds is a `@Nat` already (#1629, group 2)."""
    for parent in walk_nodes(sites.program):
        if not isinstance(parent, ast.ConstructorPattern):
            continue
        fields_ = sites.fields.get(parent.name, [])
        for sub, declared in zip(parent.sub_patterns, fields_):
            if (sub is node and isinstance(sub, ast.BindingPattern)
                    and _is_name(sub.type_expr, "Nat")
                    and _is_name(declared, "Nat")):
                return True
    return False


def _nat_through_a_call(node: ast.Node, sites: Sites) -> bool:
    """A value non-negative only through a call to a function returning
    `@Nat` (#1557): `narrowing.is_static_nat_typed` reads it as `@Nat` with
    an oracle that answers a call's declared return, and not with one that
    reads no call, which is code generation's for a non-generic function.
    So the verifier, which reads the call, sees no narrowing to record (a
    value the checker types `@Nat`, or a sum or join of one with a
    non-negative literal), and code generation guards the binding."""
    if not isinstance(node, ast.Expr):
        return False
    return (narrowing.is_static_nat_typed(node, sites.call_returns_nat)
            and not narrowing.is_static_nat_typed(node, lambda _call: None))


@dataclass(frozen=True)
class KnownClass:
    """A mismatch the join reports today, by the open issue whose class it
    is: `scripts/check_reconciliation.py`'s `KNOWN`, read as classes rather
    than corpus sites, since a generated program has no fixed site."""

    issue: str
    kind: str
    obligation: str
    emitter: str
    #: The site, in words; :meth:`holds` reads it from the program.
    shape: str
    #: A program whose join reports this class, and nothing else.
    repro: str

    def holds(self, mismatch: Mismatch, sites: Sites) -> bool:
        if (mismatch.kind, mismatch.obligation, mismatch.emitter) != (
                self.kind, self.obligation, self.emitter):
            return False
        test = _SHAPES[self.shape]
        return any(test(node, sites) for node in sites.at(mismatch))


_SHAPES: dict[str, Callable[[ast.Node, Sites], bool]] = {
    "an `@Int` division": lambda node, _s: _division_by(node, literal=False),
    "a division by a non-zero literal":
        lambda node, _s: _division_by(node, literal=True),
    "a `@Nat` binder of a `Nat` field": _nat_field_binder,
    "a `@Nat` value read through a call": _nat_through_a_call,
}


_REPRO_1598 = """\
public fn q(@Int, @Int -> @Int)
  requires(@Int.0 >= 1 && @Int.0 <= 10)
  requires(@Int.1 >= 0 && @Int.1 <= 100)
  ensures(@Int.result >= 0)
  effects(pure)
{
  @Int.1 / @Int.0
}
"""

_REPRO_1629_DIVISOR = """\
public fn r(@Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 <= 100)
  ensures(@Int.result >= 0 && @Int.result <= 2)
  effects(pure)
{
  @Int.0 % 3
}
"""

_REPRO_1629_BINDER = """\
private data Box {
  Wrap(Nat),
  Empty
}

public fn s(@Nat -> @Nat)
  requires(@Nat.0 <= 100)
  ensures(@Nat.result <= 100)
  effects(pure)
{
  match Wrap(@Nat.0) {
    Wrap(@Nat) -> @Nat.0,
    Empty -> 0
  }
}
"""

_REPRO_1557 = """\
private fn nat_id(@Nat -> @Nat)
  requires(@Nat.0 <= 100)
  ensures(@Nat.result == @Nat.0)
  effects(pure)
{
  @Nat.0
}

public fn t(@Nat -> @Nat)
  requires(@Nat.0 <= 100)
  ensures(@Nat.result <= 100)
  effects(pure)
{
  let @Nat = nat_id(@Nat.0);
  @Nat.0
}
"""

#: The mismatches the join reports today that a generated program can meet,
#: each a shape of a `scripts/check_reconciliation.py` `KNOWN` class.
KNOWN_CLASSES: tuple[KnownClass, ...] = (
    KnownClass(
        "#1598", "guarded_unrecorded", "int_overflow",
        "wasm/operators.py:_note_quotient_overflow", "an `@Int` division",
        _REPRO_1598),
    KnownClass(
        "#1695 (#1629)", "guarded_unrecorded", "div_zero",
        "wasm/operators.py:_translate_binary",
        "a division by a non-zero literal", _REPRO_1629_DIVISOR),
    KnownClass(
        "#1695 (#1629)", "guarded_unrecorded", "nat_bind",
        "wasm/operators.py:_emit_nat_bind_guard",
        "a `@Nat` binder of a `Nat` field", _REPRO_1629_BINDER),
    KnownClass(
        "#1695 (#1557)", "guarded_unrecorded", "nat_bind",
        "wasm/operators.py:_emit_nat_bind_guard",
        "a `@Nat` value read through a call", _REPRO_1557),
)


def reconcile_finds(
    source: str, known: Sequence[KnownClass] = KNOWN_CLASSES,
    stages: Stages | None = None,
) -> list[Find]:
    """Every mismatch the join reports between *source*'s verification and
    its compiled module, each carrying the issue of the *known* class it
    belongs to, or none."""
    stages = stages if stages is not None else Stages.of(source)
    verified, compiled = stages.verified, stages.compiled
    if not verified.ran or verified.errors or not compiled.ok:
        return []  # the contract's find, or the load differential's
    checked = verified.checked
    joined = join(verified.result, compiled.result, program=checked.program,
                  file=checked.file, resolved_modules=checked.resolved or ())
    sites = Sites(checked)
    finds = []
    for m in joined.mismatches:
        cls = next((k for k in known if k.holds(m, sites)), None)
        finds.append(Find(
            "reconcile", (m.kind, m.obligation, m.emitter or m.status),
            f"{m.kind} '{m.obligation}' at {m.line}:{m.column} in "
            f"'{m.function}' ({m.emitter or m.status}): {m.detail}",
            known=cls.issue if cls is not None else "", function=m.function))
    return finds


# =====================================================================
# Differential 3: a Tier 1 proof meets no runtime violation
# =====================================================================

def distrust_finds(
    source: str, trials: int = TRIALS, stages: Stages | None = None,
    stats: dict[str, int] | None = None,
) -> list[Find]:
    """What `vera test --distrust` reports against *source*: a refuted proof
    (E703), a trap it cannot attribute to an obligation, and any other
    failing trial, which on a generated program is a failing check of a
    contract the generator wrote true.  *stats* gains the counts of what
    the run served."""
    tested = (stages.distrust(trials) if stages is not None
              else pipeline.contract_test(
                  source, file=LABEL, trials=trials, distrust=True))
    if not tested.checked.ok:
        return []  # the contract's find
    result = tested.result
    if stats is not None:
        functions = result.functions
        stats["public_tested"] = sum(1 for f in functions if f.trials_run)
        stats["public_proved"] = sum(1 for f in functions if f.proved)
        stats["proofs_exercised"] = sum(
            1 for f in functions if f.proved and f.trials_run)
        stats["public_skipped"] = sum(
            1 for f in functions if f.category == "skipped")
        stats["public"] = len(functions)
        stats["trials"] = result.summary.total_trials
    finds: list[Find] = []
    for f in result.functions:
        for trial in f.failures:
            where = f"'{f.fn_name}' on {trial.args}"
            args = tuple(trial.args.values())
            values = tuple(v for v in args if isinstance(v, int | bool))
            if trial.status == "refuted":
                finds.append(Find("distrust", ("E703", trial.trap_kind),
                                  f"{where}: {trial.attribution}",
                                  function=f.fn_name, args=values))
            elif trial.status == "unattributed":
                finds.append(Find(
                    "distrust", ("unattributed", trial.trap_kind),
                    f"{where}: {trial.attribution}", function=f.fn_name,
                    args=values))
            else:
                finds.append(Find(
                    "distrust", ("violation", trial.trap_kind or trial.status),
                    f"{where}: {trial.message}", function=f.fn_name,
                    args=values))
    if not any(x.signature[0] == "E703" for x in finds):
        finds += [Find("distrust", ("E703",), d.format())
                  for d in result.diagnostics if d.error_code == "E703"]
    return finds


# =====================================================================
# One program through all of it
# =====================================================================

def differentials(
    prog: gen.Program, *, trials: int = TRIALS,
    known: Sequence[KnownClass] = KNOWN_CLASSES,
    stats: dict[str, int] | None = None,
) -> list[Find]:
    """The generator's contract, then the three differentials, over *prog*,
    each stage run once.  A program that breaks the contract goes no
    further.  *stats* gains what the stages counted."""
    source = prog.render()
    stages = Stages.of(source)
    finds = contract_finds(source, stages)
    if stats is not None and stages.verified.ran:
        for o in stages.verified.obligations:
            stats[f"obligation_{o.status}"] = stats.get(
                f"obligation_{o.status}", 0) + 1
    if finds:
        finds, counterfactual = classify_contract(prog, finds, stages)
        if counterfactual is None:
            return finds
        # Every contract find is #1525's: the differentials run over the
        # program with the counterfactual's `let`s, which verifies clean.
        prog = counterfactual
        source = prog.render()
        stages = Stages.of(source)
    finds += load_finds(source, prog.calls(), stages)
    finds += reconcile_finds(source, known, stages)
    finds += distrust_finds(source, trials, stages, stats)
    return finds


def still_fails(find: Find, *, trials: int = TRIALS) -> Callable[[gen.Program], bool]:
    """The minimiser's predicate for *find*: a candidate keeps the
    generator's contract and its differential still reports a find with
    *find*'s signature and class (a contract find keeps only its own)."""
    def holds(candidate: gen.Program) -> bool:
        return _same(find, candidate, trials) is not None
    return holds


def _same(find: Find, prog: gen.Program, trials: int) -> Find | None:
    """The find *prog* reports in *find*'s place, if it reports one."""
    source = prog.render()
    stages = Stages.of(source)
    contract = contract_finds(source, stages)
    if contract:
        contract, counterfactual = classify_contract(prog, contract, stages)
        if find.differential != "contract" and counterfactual is not None:
            prog, source = counterfactual, counterfactual.render()
            stages = Stages.of(source)
            contract = []
    if find.differential == "contract":
        found = contract
    elif contract:
        return None
    elif find.differential == "load":
        found = load_finds(source, prog.calls(), stages)
    elif find.differential == "reconcile":
        found = reconcile_finds(source, stages=stages)
    else:
        found = distrust_finds(source, trials, stages)
    return next((f for f in found if f.signature == find.signature
                 and f.known == find.known), None)


def hold(seed: int) -> None:
    """The contract and the three differentials over *seed*'s program: a
    find outside the known classes is minimised, recorded with what the
    generator expected of the minimal program, and fails the cell."""
    started = time.perf_counter()
    prog = gen.generate(seed)
    stats: dict[str, int] = {}
    finds = differentials(prog, stats=stats)
    found = [f for f in finds if not f.known]
    record: dict[str, object] = {
        "seed": seed, "shape": prog.shape(), "stats": stats,
        "finds": [f.to_dict() for f in finds],
    }
    if found:
        if _minimised[0] < MINIMISE_LIMIT:
            _minimised[0] += 1
            minimal = gen.minimize(prog, still_fails(found[0]),
                                   budget=MINIMISE_BUDGET)
            shrunk = _same(found[0], minimal, TRIALS) or found[0]
        else:
            minimal, shrunk = prog, found[0]
            record["unminimised"] = (
                f"this process had minimised {MINIMISE_LIMIT} finds already")
        args = list(shrunk.args) if shrunk.function else None
        record["find"] = {
            **shrunk.to_dict(),
            "expected": gen.expectations(minimal, shrunk.function, args),
            "minimal": minimal.render(),
        }
    record["seconds"] = round(time.perf_counter() - started, 3)
    _write(seed, prog, record)
    if found:
        find = record["find"]
        assert isinstance(find, dict)
        pytest.fail(
            f"seed {seed}: {find['differential']} "
            f"{' '.join(find['signature'])}\n{find['detail']}\n\n"
            f"What the generator expected:\n"
            f"{json.dumps(find['expected'], indent=1)}\n\n"
            f"Minimal program:\n{find['minimal']}", pytrace=False)


def _write(seed: int, prog: gen.Program, record: dict[str, object]) -> None:
    """The seed's record, and for a find both programs, where the workflow
    uploads them and `program_generator.summarize` reads them."""
    out = os.environ.get("VERA_GENERATOR_OUT", "")
    if not out:
        return
    directory = Path(out)
    (directory / "records").mkdir(parents=True, exist_ok=True)
    if "find" in record:
        (directory / "finds").mkdir(parents=True, exist_ok=True)
        (directory / "finds" / f"seed-{seed}.vera").write_text(
            prog.render(), encoding="utf-8")
        find = record["find"]
        assert isinstance(find, dict)
        (directory / "finds" / f"seed-{seed}.min.vera").write_text(
            str(find["minimal"]), encoding="utf-8")
    (directory / "records" / f"seed-{seed}.json").write_text(
        json.dumps(record, indent=1), encoding="utf-8")


# =====================================================================
# The pull request lane
# =====================================================================

@pytest.mark.parametrize("seed", SEEDS)
def test_the_program_checks_clean(seed: int) -> None:
    """Every program the generator writes passes `vera check` with no
    diagnostic, and is in `vera fmt`'s canonical form: a slot reference the
    generator computed wrong, or a layout the formatter would change, fails
    here on every pull request."""
    source = gen.program(seed)
    checked = pipeline.check(source, file=LABEL)
    assert not checked.diagnostics, "\n\n".join(
        d.format() for d in checked.diagnostics) + f"\n\n{source}"
    assert format_source(source, file=LABEL) == source, _first_difference(
        source, format_source(source, file=LABEL))


@pytest.mark.parametrize("seed", SEEDS)
def test_the_differentials_hold_over_the_pinned_seeds(seed: int) -> None:
    """The contract and the three differentials over the pinned seeds, as
    the nightly lane runs them over the night's: a change that breaks code
    generation, the join or the tester for these shapes fails here."""
    hold(seed)


def _programs_in_a_process(seeds: Sequence[int], hash_seed: str) -> list[str]:
    """The programs *seeds* write in a fresh interpreter whose string hashes
    are seeded with *hash_seed*: the process boundary is what this measures,
    since a set's order is one thing that differs between processes."""
    script = (
        "import json, sys\n"
        "from tests import program_generator as g\n"
        "print(json.dumps([g.program(s) for s in json.loads(sys.argv[1])]))\n"
    )
    env = {k: v for k, v in os.environ.items()
           if k not in ("GIT_DIR", "GIT_INDEX_FILE", "GIT_WORK_TREE")}
    env["PYTHONHASHSEED"] = hash_seed
    out = subprocess.run(
        [sys.executable, "-c", script, json.dumps(list(seeds))],
        cwd=ROOT, env=env, capture_output=True, text=True, encoding="utf-8",
        check=True, timeout=300)
    return list(json.loads(out.stdout))


def test_a_seed_determines_its_program() -> None:
    """A seed writes its program byte for byte: twice in this process, and in
    two processes whose string hashes differ, so a find's seed is its
    program on any machine."""
    here = [gen.program(seed) for seed in SEEDS]
    assert here == [gen.program(seed) for seed in SEEDS]
    assert len(set(here)) == len(here), "two seeds wrote one program"
    for hash_seed in ("0", "1"):
        assert _programs_in_a_process(SEEDS, hash_seed) == here, hash_seed


def test_every_program_keeps_the_generators_invariants() -> None:
    """What the minimiser holds a candidate to, the generator writes by:
    each of a hundred programs is well formed (`well_formed`)."""
    broken = [seed for seed in range(100)
              if not gen.well_formed(gen.generate(seed))]
    assert not broken, broken


def test_a_program_the_generator_would_not_write_is_not_well_formed() -> None:
    """Seed 463's slide: `-1 * -3` reduced to its left operand puts `-1` in
    a `@Nat` position, which the generator never writes, so the minimiser
    refuses the candidate rather than report a program whose contract is
    false."""
    flag = gen.Binding("Bool")
    n = gen.Binding("Nat", gen.Iv(0, 5), gen.Iv(0, 5))

    def program(then: gen.Expr) -> gen.Program:
        bound = gen.Binding("Nat", value=gen.If(
            gen.Ref(flag), gen.Block([], then), gen.Block([], gen.Ref(n))))
        fn = gen.Function("f0", True, [flag, n], "Int",
                          gen.Block([gen.Let(bound)], gen.Lit(0)),
                          example=[True, 3])
        return gen.Program(0, [], [fn], [fn])

    assert gen.well_formed(program(gen.Bin("*", gen.Lit(-1), gen.Lit(-3))))
    assert not gen.well_formed(program(gen.Lit(-1)))


def test_the_seeds_reach_every_construct_of_version_one() -> None:
    """The generator is not vacuous: over a hundred seeds it writes every
    construct its grammar names (:data:`program_generator.CONSTRUCTS`)."""
    reached: dict[str, int] = {}
    for seed in range(100):
        for name, count in gen.generate(seed).shape().items():
            reached[name] = reached.get(name, 0) + count
    missing = [name for name in gen.CONSTRUCTS if not reached.get(name)]
    assert not missing, (missing, reached)


# A public function the module does not export: code generation drops it
# (E602), which `vera check` and `vera verify` accept.
_DROPPED_EXPORT = """\
type Id<T> = T;

public fn kept(@Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 <= 9)
  ensures(@Int.result >= 0)
  effects(pure)
{
  @Int.0
}

public fn dropped(@Nat -> @Nat)
  requires(@Nat.0 <= 10)
  ensures(@Nat.result <= 10)
  effects(pure)
{
  let @Id<Nat> = @Nat.0;
  @Id<Nat>.0
}
"""

_DROPPED_EXPORT_CALLS = (("kept", (3,)), ("dropped", (4,)))

_KEPT_EXPORT = _DROPPED_EXPORT.replace("let @Id<Nat>", "let @Nat").replace(
    "@Id<Nat>.0", "@Nat.0")


def test_the_load_differential_reports_a_public_function_it_cannot_run() -> None:
    finds = load_finds(_DROPPED_EXPORT, _DROPPED_EXPORT_CALLS)
    assert [f.signature for f in finds] == [
        ("compile", "E602"), ("export", "missing")], finds
    assert "'dropped' is not exported" in finds[1].detail
    assert not contract_finds(_KEPT_EXPORT)
    assert load_finds(_KEPT_EXPORT, _DROPPED_EXPORT_CALLS) == []


def test_the_load_differential_reports_a_call_that_traps() -> None:
    """A call the generator made is run, and a trap in it is the find: here
    the arguments break the `requires` the hand-written program states."""
    finds = load_finds(_KEPT_EXPORT, (("kept", (30,)), ("dropped", (4,))))
    assert [(f.signature, f.function, f.args) for f in finds] == [
        (("call", "contract_violation"), "kept", (30,))], finds


def test_the_reconcile_differential_reports_a_mismatch_outside_its_classes(
) -> None:
    """The divisor mismatch of #1629 is a known class; with no class to
    hold it, the same mismatch is a find."""
    known = reconcile_finds(_REPRO_1629_DIVISOR)
    assert [(f.signature, f.known) for f in known] == [(
        ("guarded_unrecorded", "div_zero", "wasm/operators.py:_translate_binary"),
        "#1695 (#1629)")], known
    unknown = reconcile_finds(_REPRO_1629_DIVISOR, known=())
    assert [(f.signature, f.known) for f in unknown] == [(
        known[0].signature, "")], unknown
    assert "guarded_unrecorded 'div_zero' at 6:3 in 'r'" in unknown[0].detail
    neighbour = _REPRO_1629_DIVISOR.replace("@Int.0 % 3", "@Int.0 + 0 * 3")
    assert reconcile_finds(neighbour, known=()) == []


@pytest.mark.parametrize(
    "cls", KNOWN_CLASSES, ids=lambda c: f"{c.issue} {c.shape}")
def test_each_known_class_keeps_its_shape(cls: KnownClass) -> None:
    """Each class's repro reports exactly that class, once.  The day its
    issue is fixed the repro reports nothing, this fails, and the entry
    comes out, as `scripts/check_reconciliation.py`'s `KNOWN` entries do."""
    assert not contract_finds(cls.repro), contract_finds(cls.repro)
    finds = reconcile_finds(cls.repro)
    assert [(f.signature, f.known) for f in finds] == [
        ((cls.kind, cls.obligation, cls.emitter), cls.issue)], finds
    alone = reconcile_finds(cls.repro, known=(cls,))
    assert [f.known for f in alone] == [cls.issue], alone


def test_the_distrust_differential_reports_a_refuted_proof() -> None:
    """#1555's address comparison: proved, and refuted by its one run.  The
    neighbour binds each call before comparing, the documented workaround,
    and its proof holds."""
    finds = distrust_finds(_FALSE_PROOF)
    assert [f.signature[0] for f in finds] == ["E703"], finds
    neighbour = _FALSE_PROOF.replace(
        "  if mo(7) == mo(7) then { 0 - 1 } else { 1 }\n",
        "  let @Option<Int> = mo(7);\n"
        "  let @Option<Int> = mo(7);\n"
        "  if @Option<Int>.0 == @Option<Int>.1 then { 0 - 1 } else { 1 }\n")
    assert neighbour != _FALSE_PROOF
    assert distrust_finds(neighbour) == []


def _lost_postcondition(lowest: int) -> gen.Program:
    """`f2` binds `f0(Bravo(@Int.0))`, whose `ensures` says it is 4, and
    passes it to `f1`, which requires 1 to 9; `f2` names no `Gauge`, so the
    verifier loses `f0`'s postcondition and refuses the call (#1525's class,
    `finds/ctor_argument_loses_postcondition.vera`).  With *lowest* below 1,
    `f2` also calls `f1` on its own parameter, which may be 0: a refusal no
    counterfactual removes."""
    bravo = gen.Ctor("Bravo", "Gauge", ["Int"])
    gauge = gen.Data("Gauge", True, [bravo])
    f0 = gen.Function("f0", False, [gen.Binding("Gauge")], "Nat",
                      gen.Block([], gen.Lit(4)), ensure_style="exact")
    wanted = gen.Iv(1, 9)
    p1 = gen.Binding("Int", wanted, wanted)
    f1 = gen.Function("f1", False, [p1], "Int", gen.Block([], gen.Ref(p1)),
                      ensure_style="none")
    own = gen.Iv(lowest, 9)
    p2 = gen.Binding("Int", own, own)
    four = gen.Binding("Int", value=gen.Call(
        f0, [gen.Construct(bravo, [gen.Ref(p2)])]))
    result: gen.Expr = gen.Call(f1, [gen.Ref(four)])
    if lowest < 1:
        result = gen.Bin("+", result, gen.Call(f1, [gen.Ref(p2)]))
    f2 = gen.Function("f2", True, [p2], "Int",
                      gen.Block([gen.Let(four)], result), example=[3])
    return gen.Program(0, [gauge], [f0, f1, f2], [f2])


def test_the_counterfactual_keys_a_lost_postcondition_to_1525() -> None:
    """The refusal vanishes when `f2` first binds an unused `let @Gauge`, so
    it is #1525's, the record says why, and the differentials run over the
    counterfactual program, which verifies clean."""
    prog = _lost_postcondition(1)
    finds = contract_finds(prog.render())
    assert [f.signature for f in finds] == [("verify", "E501")], finds
    stats: dict[str, int] = {}
    classified = differentials(prog, stats=stats)
    contract = [f for f in classified if f.differential == "contract"]
    assert [(f.known, f.signature) for f in contract] == [
        (CONSTRUCTED_SORT_ISSUE, ("verify", "E501"))], classified
    assert "vanished under the counterfactual" in contract[0].evidence
    assert "call_pre in 'f2'" in contract[0].evidence, contract[0].evidence
    assert "violated -> " in contract[0].evidence, contract[0].evidence
    assert not [f for f in classified if not f.known], classified
    assert stats["public_tested"] == 1, stats
    named = gen.name_constructed_types(prog)
    assert named is not None
    assert "  let @Gauge = Bravo(0);\n  let @Int = f0(Bravo(@Int.0));" in (
        named.render())


def test_a_refusal_the_counterfactual_does_not_remove_stays_a_find() -> None:
    """`f2`'s own parameter may be 0, which `f1` refuses whatever `f2`
    names: the refusal survives the counterfactual, and is a find."""
    finds = differentials(_lost_postcondition(0))
    assert [(f.differential, f.signature, f.known) for f in finds] == [
        ("contract", ("verify", "E501"), CONSTRUCTED_SORT_ISSUE),
        ("contract", ("verify", "E501"), "")], finds
    assert "survived the counterfactual" in finds[1].evidence


def test_the_minimiser_keeps_the_failure_it_shrinks() -> None:
    """The smallest of the first hundred programs that divides by a literal
    is shrunk to the smallest program whose join still reports the divisor
    class, keeping the generator's contract: a reduction that lost the find
    or broke the program would have been refused."""
    candidates = sorted(
        (gen.size(p), p.seed) for p in map(gen.generate, range(100))
        if p.shape()["/lit"] + p.shape()["%lit"])
    assert candidates, "no seed below 100 divides by a literal"
    prog = gen.generate(candidates[0][1])
    finds = [f for f in reconcile_finds(prog.render())
             if f.known == "#1695 (#1629)" and f.signature[1] == "div_zero"]
    assert finds, prog.render()
    holds = still_fails(finds[0])
    minimal = gen.minimize(prog, holds, budget=MINIMISE_BUDGET)
    assert holds(minimal)
    assert gen.well_formed(minimal)
    assert gen.size(minimal) < gen.size(prog), minimal.render()
    assert len(minimal.functions) == 1, minimal.render()


def test_the_record_states_what_the_generator_expected() -> None:
    """A find's record carries each function's contract as written, its
    intervals, and the value an exact `ensures` states on the failing
    arguments, so a generator bug is told from a toolchain find by reading
    the record."""
    prog = next(p for p in map(gen.generate, range(100))
                if any(gen.ensure_style(f) == "exact" and f.params
                       and all(q.type == "Int" for q in f.params)
                       for f in p.functions))
    fn = next(f for f in prog.functions if gen.ensure_style(f) == "exact"
              and f.params and all(q.type == "Int" for q in f.params))
    args = [int(a) for a in fn.example]
    entry = next(e for e in gen.expectations(prog, fn.name, args)
                 if e["function"] == fn.name)
    ran = pipeline.run(prog.render(), fn=fn.name, args=args)
    assert ran.ok, ran.trap
    assert entry["expected"] == ran.value, (entry, prog.render())
    assert entry["style"] == "exact"
    assert entry["ensures"] and entry["requires"]


# =====================================================================
# The nightly lane
# =====================================================================

def night_seeds(spec: str | None = None,
                today: datetime.date | None = None) -> list[int]:
    """The seeds ``VERA_GENERATOR_SEEDS`` names: nothing when it is unset,
    ``night:N`` for N seeds the UTC day determines, or a list of seeds and
    ranges (``12,40-49``) to rerun."""
    spec = os.environ.get("VERA_GENERATOR_SEEDS", "") if spec is None else spec
    spec = spec.strip()
    if not spec:
        return []
    night = re.fullmatch(r"night:(\d+)", spec)
    if night:
        count = int(night.group(1))
        day = today or datetime.datetime.now(datetime.timezone.utc).date()
        start = (day - NIGHT_EPOCH).days * NIGHT_STRIDE
        return list(range(start, start + count))
    seeds: list[int] = []
    for part in spec.split(","):
        bounds = re.fullmatch(r"\s*(\d+)\s*(?:-\s*(\d+)\s*)?", part)
        if bounds is None:
            raise ValueError(f"VERA_GENERATOR_SEEDS: cannot read {part!r}")
        low = int(bounds.group(1))
        high = int(bounds.group(2) or low)
        seeds.extend(range(low, high + 1))
    return seeds


def test_the_night_is_read_as_the_workflow_writes_it() -> None:
    assert night_seeds("") == []
    assert night_seeds("3,7-9") == [3, 7, 8, 9]
    day = NIGHT_EPOCH + datetime.timedelta(days=2)
    assert night_seeds("night:3", today=day) == [200_000, 200_001, 200_002]
    assert night_seeds("night:3", today=day + datetime.timedelta(days=1))[0] == (
        300_000)
    with pytest.raises(ValueError):
        night_seeds("1;rm")


NIGHT_SEEDS = night_seeds()

if NIGHT_SEEDS:
    @pytest.mark.budget(900)
    @pytest.mark.parametrize("seed", NIGHT_SEEDS)
    def test_the_differentials_hold(seed: int) -> None:
        """The contract and the three differentials over one of the night's
        programs (:func:`hold`)."""
        hold(seed)
