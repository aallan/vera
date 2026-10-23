"""The program generator's four differentials: what checks compiles and loads with every public function exported; every obligation record has its guard and every guard its record; a Tier 1 proof meets no runtime violation on generated inputs; a warm verification session agrees with a fresh one edit by edit.

`tests/program_generator.py` writes a whole Vera program from a seed, typed
from its own binding environment, with contracts true of every input their
`requires` admits, and a module beside it when the program imports one.
This file holds that program to the toolchain, in process through
`tests/pipeline.py`, the entry and its module written to one directory and
handed over by the entry's path, as `vera` resolves them:

* **The generator's own contract**: each file passes `vera check` with no
  diagnostic, is in `vera fmt`'s canonical form, and `vera verify` answers
  every query of the entry and of the module inside its default budget with
  no error.
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
* **(4) Warm**: the program and the edits `program_generator.edits` writes
  for it go, in order, to one warm `VerificationSession` as the language
  server sends them, and each text alone to a fresh session; the two report
  the same obligations, with the same statuses at the same places, and the
  same diagnostics, edit by edit.  Two sessions that differ in a
  counterexample alone make a find of #1785's class.

A find of (1), (2) or (3) that vanishes once each value code generation
types by its own reading is bound in place by a `let` of the type the
checker gives it is counted under that class's issue (:data:`REDERIVED`);
one that does not vanish is a find.

Every pull request runs the contract and the four differentials over the
ten pinned :data:`SEEDS`, and holds the instrument to its own contract: a seed
writes its program byte for byte in every process, a hundred seeds reach
every construct of the grammar, each differential reports a hand-written
program that breaks it and passes that program's nearest neighbour that does
not, the minimiser keeps the failure it shrinks and drops a handler, a
recursive call and an import, each known class still has its shape, and each
counterfactual class still holds its repro and its members.  The
nightly lane (`.github/workflows/nightly-generator.yml`) runs the same cell
over the night's seeds, which ``VERA_GENERATOR_SEEDS`` names
(:func:`night_seeds`).  A find outside the known classes is minimised and
written with its seed, its minimal program and what the generator expected
of it under ``VERA_GENERATOR_OUT``, and fails the seed's cell.

The program a seed writes is ``python -m tests.program_generator SEED``.
"""

from __future__ import annotations

import copy
import datetime
import itertools
import json
import os
import re
import subprocess
import sys
import time
from collections import Counter
from collections.abc import Callable, Sequence
from dataclasses import dataclass, is_dataclass, replace
from dataclasses import fields as dataclass_fields
from pathlib import Path

import pytest
import wasmtime
import yaml

from tests import pipeline
from tests import program_generator as gen
from tests.test_distrust_corpus import _FALSE_PROOF
from vera import ast
from vera.errors import Diagnostic, SourceLocation
from vera.formatter import format_source
from vera.obligations.session import VerificationSession
from vera.reconcile import Mismatch, join

ROOT = Path(__file__).resolve().parent.parent

#: The label every program's entry is checked, verified, compiled and tested
#: under: the file name a report gives the program.
LABEL = gen.ENTRY

#: The pull request lane's seeds: the first eight, 173 and 737, which
#: between them write every construct of the grammar
#: (:func:`test_the_pinned_seeds_reach_every_construct`) and a find of each
#: counterfactual class, #1744's at 7 and #1525's at 737
#: (:data:`PINNED_CLASSES`).
SEEDS = (0, 1, 2, 3, 4, 5, 6, 7, 173, 737)

#: A pinned seed whose program makes a find of each counterfactual class.
PINNED_CLASSES = (("#1744", 7), ("#1525", 737))

#: Trials per public function in the distrust differential.
TRIALS = int(os.environ.get("VERA_GENERATOR_TRIALS", "20"))

#: Edits per program in the warm differential.
EDITS = int(os.environ.get("VERA_GENERATOR_EDITS", str(gen.EDITS)))

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

#: Distinct directories for the programs one process writes.
_directories = itertools.count()


# =====================================================================
# Finds
# =====================================================================

@dataclass(frozen=True)
class Find:
    """One thing a program did that a differential says it must not."""

    #: ``contract`` (the generator's own), ``load``, ``reconcile``,
    #: ``distrust`` or ``warm``.
    differential: str
    #: What the minimiser holds fixed while it shrinks the program.
    signature: tuple[str, ...]
    #: The diagnostic or the mismatch, in words.
    detail: str
    #: The open issue whose class it is (``"#1695"``), or empty.
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
    #: The known class it falls in, by its shape: what the night's report
    #: counts it under.
    cls: str = ""
    #: A join mismatch's file, line and column.
    site: tuple[str | None, int, int] | None = None

    def to_dict(self) -> dict[str, object]:
        return {"differential": self.differential,
                "signature": list(self.signature), "detail": self.detail,
                "known": self.known, "function": self.function,
                "args": list(self.args), "evidence": self.evidence,
                "cls": self.cls}


Source = str | dict[str, str] | gen.Program


def _files(program: Source) -> dict[str, str]:
    if isinstance(program, gen.Program):
        return program.files()
    if isinstance(program, str):
        return {LABEL: program}
    return dict(program)


@dataclass
class Stages:
    """One program's stages, each run once: the verification (with its
    check), the module, the distrust test, and the module's own
    verification.  A program of one file with no directory to write it to
    runs as source text; any other is written and run by its entry's
    path."""

    files: dict[str, str]
    entry: Path | None
    verified: pipeline.Verified
    compiled: pipeline.Compiled
    tested: pipeline.Tested | None = None

    @classmethod
    def of(cls, program: Source, directory: Path | None = None) -> Stages:
        files = _files(program)
        if directory is None:
            assert set(files) == {LABEL}, "a program with a module needs a directory"
            source = files[LABEL]
            return cls(files, None, pipeline.verify(source, file=LABEL),
                       pipeline.compile(source, file=LABEL))
        target = directory / f"p{next(_directories)}"
        entry = pipeline.write_tree(target, files, entry=LABEL)
        return cls(files, entry, pipeline.verify(entry, file=LABEL),
                   pipeline.compile(entry, file=LABEL))

    @property
    def source(self) -> str:
        return self.files[LABEL]

    @property
    def target(self) -> str | Path:
        return self.entry if self.entry is not None else self.source

    def module_verified(self) -> pipeline.Verified | None:
        if gen.MODULE_FILE not in self.files or self.entry is None:
            return None
        return pipeline.verify(self.entry.parent / gen.MODULE_FILE,
                               file=gen.MODULE_FILE)

    def distrust(self, trials: int) -> pipeline.Tested:
        if self.tested is None:
            self.tested = pipeline.contract_test(
                self.target, file=LABEL, trials=trials, distrust=True)
        return self.tested


# =====================================================================
# The generator's own contract
# =====================================================================

def contract_finds(program: Source, stages: Stages | None = None) -> list[Find]:
    """What the generator promises of every program: `vera check` reports no
    diagnostic at all, each file is `vera fmt`'s canonical form, and `vera
    verify` answers every query of the entry and of the module inside its
    default budget with no error.

    A program that breaks it is the generator's bug or the toolchain's: every
    contract the generator writes holds of every input the function's
    `requires` admits, so a refutation is wrong arithmetic in the generator
    or a wrong model in the verifier, and the minimal program says which."""
    stages = stages if stages is not None else Stages.of(program)
    verified = stages.verified
    finds = [
        Find("contract", ("check", d.error_code or d.severity), d.format())
        for d in verified.checked.diagnostics
    ]
    if finds:
        # The formatter parses what it formats, and raises on text that does
        # not parse, so it runs only on a program the check accepted.
        return finds
    for name, text in stages.files.items():
        canonical = format_source(text, file=name)
        if canonical != text:
            finds.append(Find("contract", ("fmt",), f"{name}: " + _first_difference(
                text, canonical)))
    if finds or not verified.ran:
        return finds
    for label, run in (("", verified), (gen.MODULE_FILE, stages.module_verified())):
        if run is None:
            continue
        where = f"{label}: " if label else ""
        finds += [
            Find("contract", ("verify", d.error_code or "error"), where + d.format(),
                 key=_verify_key(label, d))
            for d in run.errors
        ]
        if run.ran:
            finds += [
                Find("contract", ("verify", "timeout", o.kind),
                     f"{where}the {o.kind} obligation in '{o.fn_name}' at {o.line}:"
                     f"{o.column} exhausted the solver's default budget")
                for o in run.obligations if o.status == "timeout"
            ]
    return finds


def _verify_key(label: str, d: Diagnostic) -> str:
    """What identifies a verify error when the counterfactual's `let`s move
    lines: its file, code and description without the counterexample, whose
    values name the solver's fresh terms in the order it made them, and its
    source line's text and column, which a whole line inserted above leaves
    alone."""
    return (f"{label}{d.error_code}: {_without_model(d.description)} "
            f"| {d.source_line.strip()} | {d.location.column}")


#: The class of a verify error that vanishes when each function first names,
#: in an unused `let`, every data type it constructs and does not name in its
#: signature: the verifier walks a function's signature and `let`s for a data
#: type's sort instead of reading the checker's types, so a construction it
#: finds no sort for does not translate, and a call taking it loses the
#: callee's postcondition (`program_generator.name_constructed_types`).
CONSTRUCTED_SORT_ISSUE = "#1525"
CONSTRUCTED_SORT_SHAPE = ("a construction of a data type its function names "
                          "nowhere, for which the verifier finds no sort")


def classify_contract(
    prog: gen.Program, finds: list[Find], stages: Stages,
    directory: Path | None = None,
) -> tuple[list[Find], gen.Program | None]:
    """*finds* with each verify error that #1525's counterfactual removes
    marked known, and the counterfactual program when it removes every find
    of the contract: the program the differentials then run over.

    Run only on a program whose contract failed.  A verify error that
    survives the counterfactual stays a find; so does every error when the
    counterfactual reports one the program did not, since it no longer
    isolates the class.  Each verify error's evidence names the outcome and
    every obligation whose status the counterfactual changed."""
    errors = [f for f in finds if f.signature[0] == "verify" and f.key]
    named = gen.name_constructed_types(prog) if errors else None
    if named is None:
        return finds, None
    after = Stages.of(named, directory if named.module is not None else None)
    after_finds = contract_finds(named, after)
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
            out.append(replace(f, known=CONSTRUCTED_SORT_ISSUE, cls=CONSTRUCTED_SORT_SHAPE,
                               evidence=(
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
    program: Source, calls: Sequence[tuple[str, Sequence[int] | None]],
    stages: Stages | None = None,
) -> list[Find]:
    """Compile *program* as `vera compile` does, and run each of *calls* in
    the module it builds.

    The module must compile with no E6xx diagnostic and no error, export
    exactly the entry's public functions, and run each call to completion:
    *calls* names every public function with the arguments to call it on
    (``None`` for one that takes none), which satisfy its `requires`."""
    stages = stages if stages is not None else Stages.of(program)
    compiled = stages.compiled
    if compiled.checked is None or not compiled.checked.ok:
        return []  # the contract's find
    generic = {tld.decl.name for tld in compiled.parsed.program.declarations
               if isinstance(tld.decl, ast.FnDecl) and tld.decl.forall_vars}
    finds = [
        Find("load", ("compile", d.error_code or "error"), d.format(),
             function=_function_named(d.description))
        for d in compiled.diagnostics
        if ((d.error_code or "").startswith("E6") or d.severity == "error")
        # A generic's template is not compiled, its clones are: a template
        # no call instantiates is skipped by design.
        and not (d.error_code == "E600" and _names_one_of(d.description, generic))
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
        try:
            ran = pipeline.run(compiled, fn=name,
                               args=list(args) if args is not None else None)
        except wasmtime.WasmtimeError as exc:
            # The module wasmtime refuses to load: no call of it runs.
            return finds + [Find("load", ("module", "invalid"),
                                 "the module does not load: "
                                 + " ".join(str(exc).split())[:400])]
        if not ran.ok:
            kind = ran.trap.kind if ran.trap is not None else "refused"
            finds.append(Find(
                "load", ("call", kind),
                f"'{name}' on {list(args or [])} did not return: "
                f"{ran.trap if ran.trap is not None else ran.diagnostics}",
                function=name, args=tuple(args or ())))
    return finds


def _names_one_of(description: str, names: set[str]) -> bool:
    return _function_named(description) in names


def _function_named(description: str) -> str:
    """The function a code generation diagnostic names, or empty."""
    match = re.match(r"Function '([^']+)'", description)
    return match.group(1) if match is not None else ""


# =====================================================================
# Differential 2: every obligation record has its guard and every guard
# its record
# =====================================================================

class Sites:
    """The entry's nodes and the module's, by the file and the place they
    start, each node's parent, and what the declarations say: each alias's
    type, each constructor's fields, and each function's return, for the
    known-class predicates.  Everything here is read off the programs as
    written, never off the checker's tables."""

    def __init__(self, checked: pipeline.Checked) -> None:
        self.program = checked.program
        self._at: dict[tuple[str | None, int, int], list[ast.Node]] = {}
        self.parent: dict[int, ast.Node | None] = {}
        self.fields: dict[str, tuple[list[ast.TypeExpr], tuple[str, ...]]] = {}
        self.returns: dict[str, ast.FnDecl] = {}
        self.aliases: dict[str, ast.TypeExpr] = {}
        programs = [(checked.file, checked.program)] + [
            (str(m.file_path), m.program) for m in (checked.resolved or ())]
        self._calls: dict[str, list[ast.FnCall]] = {}
        for file, program in programs:
            self._index(program, None, file)
            for tld in program.declarations:
                decl = tld.decl
                if isinstance(decl, ast.DataDecl):
                    for ctor in decl.constructors:
                        self.fields[ctor.name] = (list(ctor.fields or ()),
                                                  tuple(decl.type_params or ()))
                elif isinstance(decl, ast.FnDecl):
                    for fn in [decl, *(decl.where_fns or ())]:
                        self.returns[fn.name] = fn
                elif isinstance(decl, ast.TypeAliasDecl) and not decl.type_params:
                    self.aliases[decl.name] = decl.type_expr

    def _index(self, node: object, parent: ast.Node | None, file: str | None) -> None:
        if isinstance(node, ast.Node):
            self.parent[id(node)] = parent
            if isinstance(node, ast.FnCall):
                self._calls.setdefault(node.name, []).append(node)
            span = node.span
            if span is not None:
                self._at.setdefault((file, span.line, span.column), []).append(node)
            parent = node
        if is_dataclass(node) and not isinstance(node, type):
            for f in dataclass_fields(node):
                self._index(getattr(node, f.name), parent, file)
        elif isinstance(node, tuple):
            for item in node:
                self._index(item, parent, file)

    def at(self, mismatch: Mismatch) -> list[ast.Node]:
        return self._at.get((mismatch.file, mismatch.line, mismatch.column), [])

    def resolve(self, te: ast.TypeExpr | None) -> ast.TypeExpr | None:
        """*te* through the aliases the program declares."""
        seen = 0
        while (isinstance(te, ast.NamedType) and not te.type_args
               and te.name in self.aliases and seen < 8):
            te, seen = self.aliases[te.name], seen + 1
        return te

    def is_nat(self, te: ast.TypeExpr | None) -> bool:
        """Whether *te* is `Nat`, or a refinement of it, through the aliases."""
        te = self.resolve(te)
        if isinstance(te, ast.RefinementType):
            return self.is_nat(te.base_type)
        return isinstance(te, ast.NamedType) and te.name == "Nat" and not te.type_args

    def slot_type(self, slot: ast.SlotRef) -> ast.TypeExpr:
        return ast.NamedType(slot.type_name, slot.type_args)

    def arguments(self, te: ast.TypeExpr | None) -> list[ast.TypeExpr]:
        te = self.resolve(te)
        if isinstance(te, ast.NamedType):
            return [self.resolve(a) or a for a in (te.type_args or ())]
        return []

    def type_of(self, e: ast.Node) -> ast.TypeExpr | None:
        """The type the declarations give *e*, where they give one: a slot's,
        an element's of a slot's array, `map_get`'s of a slot's map."""
        if isinstance(e, ast.SlotRef):
            return self.resolve(self.slot_type(e))
        if isinstance(e, ast.IndexExpr):
            args = self.arguments(self.type_of(e.collection))
            return args[0] if args else None
        if isinstance(e, ast.FnCall) and e.name == "map_get" and e.args:
            args = self.arguments(self.type_of(e.args[0]))
            if len(args) == 2:
                return ast.NamedType("Option", (args[1],))
        return None

    def enclosing(self, node: ast.Node) -> ast.FnDecl | None:
        parent = self.parent.get(id(node))
        while parent is not None and not isinstance(parent, ast.FnDecl):
            parent = self.parent.get(id(parent))
        return parent

    def type_variable(self, te: ast.TypeExpr | None, node: ast.Node) -> str | None:
        """*te*'s name when it is a type variable of the function around
        *node*."""
        fn = self.enclosing(node)
        if (fn is not None and isinstance(te, ast.NamedType) and not te.type_args
                and te.name in (fn.forall_vars or ())):
            return te.name
        return None

    def at_nat(self, node: ast.Node, tvar: str) -> bool:
        """Whether some call of the generic around *node* instantiates
        *tvar* at `Nat`: every argument at a parameter of that type is a
        `Nat` by the declarations."""
        fn = self.enclosing(node)
        if fn is None:
            return False
        positions = [n for n, p in enumerate(fn.params)
                     if isinstance(p, ast.NamedType) and p.name == tvar and not p.type_args]
        if not positions:
            return False
        for call in self._calls.get(fn.name, []):
            if all(n < len(call.args) and self.nat_by_declarations(call.args[n])
                   for n in positions):
                return True
        return False

    def cell(self, node: ast.Node) -> ast.TypeExpr | None:
        """The `State` cell a `get` reads: the nearest handler's, or the
        enclosing function's row."""
        parent = self.parent.get(id(node))
        while parent is not None:
            if isinstance(parent, ast.HandleExpr):
                eff = parent.effect
                if isinstance(eff, ast.EffectRef) and eff.name == "State" and eff.type_args:
                    return eff.type_args[0]
            if isinstance(parent, ast.FnDecl):
                row = parent.effect
                if isinstance(row, ast.EffectSet):
                    for ref in row.effects:
                        if isinstance(ref, ast.EffectRef) and ref.name == "State" and ref.type_args:
                            return ref.type_args[0]
                return None
            parent = self.parent.get(id(parent))
        return None

    def nat_by_declarations(self, e: ast.Node) -> bool:
        """Whether *e*'s value is non-negative by what the program declares:
        a slot of a `Nat` type or a refinement of one, an element of a
        `Nat` array, a call whose callee returns `Nat` (a generic one at a
        `Nat` argument in every position of its type variable), a fold
        from one, a `get` of a `Nat` cell, a handler or a branch whose value
        is one, a non-negative literal, and arithmetic over them."""
        if isinstance(e, ast.SlotRef):
            tvar = self.type_variable(self.slot_type(e), e)
            if tvar is not None:
                return self.at_nat(e, tvar)
            return self.is_nat(self.slot_type(e))
        if isinstance(e, ast.IntLit):
            return e.value >= 0
        if isinstance(e, ast.BinaryExpr):
            return (e.op in (ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
                             ast.BinOp.DIV, ast.BinOp.MOD)
                    and self.nat_by_declarations(e.left)
                    and self.nat_by_declarations(e.right))
        if isinstance(e, ast.Block):
            return self.nat_by_declarations(e.expr)
        if isinstance(e, (ast.IfExpr, ast.MatchExpr)):
            # A branch that throws gives the construct no value.
            branches = ([e.then_branch, e.else_branch] if isinstance(e, ast.IfExpr)
                        else [a.body for a in e.arms])
            valued = [b for b in branches if not _throws(b)]
            return bool(valued) and all(self.nat_by_declarations(b) for b in valued)
        if isinstance(e, ast.HandleExpr):
            # An `Exn` clause's value is the handler's when the body throws;
            # a `State` clause's goes back to the body.
            clauses = ([c.body for c in e.clauses]
                       if isinstance(e.effect, ast.EffectRef) and e.effect.name == "Exn"
                       else [])
            return (self.nat_by_declarations(e.body)
                    and all(self.nat_by_declarations(c) for c in clauses))
        if isinstance(e, ast.IndexExpr):
            return self.is_nat(self.type_of(e))
        if isinstance(e, ast.QualifiedCall) and e.name == "get":
            return self.is_nat(self.cell(e))
        if isinstance(e, (ast.FnCall, ast.ModuleCall)):
            fn = self.returns.get(e.name)
            if fn is None and e.name == "array_fold" and len(e.args) == 3:
                # The checker binds a fold's accumulator to its initial
                # value's type.
                return self.nat_by_declarations(e.args[1])
            if fn is None:
                return e.name == "get" and not e.args[1:] and self.is_nat(self.cell(e))
            ret = fn.return_type
            tvars = fn.forall_vars or ()
            if isinstance(ret, ast.NamedType) and ret.name in tvars and not ret.type_args:
                at = [a for p, a in zip(fn.params, e.args)
                      if isinstance(p, ast.NamedType) and p.name == ret.name]
                return bool(at) and all(self.nat_by_declarations(a) for a in at)
            return self.is_nat(ret)
        return False

    def binder_of_nat_field(self, node: ast.Node) -> bool:
        """Whether *node* is a `@Nat` binder of a field the declarations type
        `Nat`: declared so, or a type parameter the scrutinee's declared type
        instantiates at `Nat`."""
        if not isinstance(node, ast.BindingPattern):
            return False
        tvar = self.type_variable(node.type_expr, node)
        if tvar is not None:
            return self.at_nat(node, tvar)
        if not self.is_nat(node.type_expr):
            return False
        pattern = self.parent.get(id(node))
        if not isinstance(pattern, ast.ConstructorPattern):
            return False
        position = next(n for n, sub in enumerate(pattern.sub_patterns) if sub is node)
        if pattern.name in ("Some", "Tuple"):
            declared: ast.TypeExpr | None = ast.NamedType(
                "T" if pattern.name == "Some" else f"T{position}", None)
            params: tuple[str, ...] = (("T",) if pattern.name == "Some"
                                       else tuple(f"T{n}" for n in range(
                                           len(pattern.sub_patterns))))
        else:
            fields, params = self.fields.get(pattern.name, ([], ()))
            declared = fields[position] if position < len(fields) else None
        if self.is_nat(declared):
            return True
        if not (isinstance(declared, ast.NamedType) and declared.name in params):
            return False
        arm = self.parent.get(id(pattern))
        match = self.parent.get(id(arm)) if arm is not None else None
        if not isinstance(match, ast.MatchExpr):
            return False
        args = self.arguments(self.type_of(match.scrutinee))
        k = params.index(declared.name)
        return k < len(args) and self.is_nat(args[k])


def _throws(e: ast.Node) -> bool:
    """Whether *e* is a `throw`, which gives its branch no value."""
    if isinstance(e, ast.Block):
        return _throws(e.expr)
    return isinstance(e, (ast.FnCall, ast.QualifiedCall)) and e.name == "throw"


def _nat_by_declared_names(e: ast.Node) -> bool:
    """Code generation's static rule for a value bound into a `@Nat` slot,
    as it reads one: a slot whose declared type is spelled `Nat`, a
    non-negative literal, arithmetic over them and a branch whose every
    value is one; a call, an element, a handler and a binder it does not
    read as one."""
    if isinstance(e, ast.SlotRef):
        return e.type_name == "Nat" and not e.type_args
    if isinstance(e, ast.IntLit):
        return e.value >= 0
    if isinstance(e, ast.BinaryExpr):
        return (e.op in (ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
                         ast.BinOp.DIV, ast.BinOp.MOD)
                and _nat_by_declared_names(e.left) and _nat_by_declared_names(e.right))
    if isinstance(e, ast.Block):
        return _nat_by_declared_names(e.expr)
    if isinstance(e, ast.IfExpr):
        return (_nat_by_declared_names(e.then_branch)
                and _nat_by_declared_names(e.else_branch))
    if isinstance(e, ast.MatchExpr):
        return bool(e.arms) and all(_nat_by_declared_names(a.body) for a in e.arms)
    return False


def _nat_guard_on_a_declared_nat(node: ast.Node, sites: Sites) -> bool:
    """The class #1695 holds for a `nat_bind` guard: a value the program's
    declarations make non-negative, so the verifier, which reads the
    checker's types, records no narrowing, and which code generation's own
    static rule, reading declared names, does not read as a `@Nat`, so it
    plants the guard (`Sites.nat_by_declarations` against
    `_nat_by_declared_names`).  A branch the declarations type `Int`, a
    negated literal among them (#1756's shape), is outside it."""
    if isinstance(node, ast.BindingPattern):
        return sites.binder_of_nat_field(node)
    return sites.nat_by_declarations(node) and not _nat_by_declared_names(node)


def _refinement_already_held(node: ast.Node, sites: Sites) -> bool:
    """A refinement check where the value already has the refinement's
    type by the declarations: a refined parameter at entry, whose callers
    discharge its predicate and whose body assumes it, or a `let` of a
    refined type bound to a slot of that same type.  The verifier records
    nothing there, and code generation checks it."""
    parent = sites.parent.get(id(node))
    if isinstance(parent, ast.FnDecl) and any(p is node for p in parent.params):
        return isinstance(sites.resolve(node), ast.RefinementType)  # type: ignore[arg-type]
    if (isinstance(node, ast.LetStmt) and isinstance(node.type_expr, ast.NamedType)
            and isinstance(sites.resolve(node.type_expr), ast.RefinementType)):
        name = node.type_expr.name
        return all(isinstance(x, ast.SlotRef) and x.type_name == name and not x.type_args
                   for x in _leaves(node.value))
    return False


def _leaves(e: ast.Node) -> list[ast.Node]:
    """The values a branch can take: each arm's, through nested branches."""
    if isinstance(e, ast.Block):
        return _leaves(e.expr)
    if isinstance(e, ast.IfExpr):
        return _leaves(e.then_branch) + _leaves(e.else_branch)
    if isinstance(e, ast.MatchExpr):
        return [leaf for a in e.arms for leaf in _leaves(a.body)]
    return [e]


def _join_typed_as_the_refinement(node: ast.Node, sites: Sites) -> bool:
    """A `let` of a refined type bound to an `if` or `match` with an arm of
    that refinement and an arm of another type: the checker types the join
    as the refinement (`is_subtype`'s rule for a refinement over its base),
    so the verifier records nothing, and code generation checks the
    predicate (#1695's line from #1760's review).  Silent at `vera verify`
    where the other arm breaks the predicate; a generated program's arms
    each keep it."""
    if not (isinstance(node, ast.LetStmt) and isinstance(node.type_expr, ast.NamedType)
            and isinstance(sites.resolve(node.type_expr), ast.RefinementType)):
        return False
    name = node.type_expr.name
    leaves = _leaves(node.value)
    refined = [x for x in leaves if isinstance(x, ast.SlotRef) and x.type_name == name]
    return len(leaves) > 1 and bool(refined) and len(refined) < len(leaves)


def _narrowing_into_refined_nat(node: ast.Node, sites: Sites) -> bool:
    """A value narrowed into a refinement of `Nat`: a `let`'s value, or a
    call's argument at such a parameter.  The verifier records the
    narrowing as the refinement's (`refine_bind`, whose predicate holds the
    base's sign), and code generation checks the sign (`nat_bind`) and the
    predicate apart, so the sign's check has no record of its own kind."""
    parent = sites.parent.get(id(node))
    if isinstance(parent, ast.LetStmt) and parent.value is node:
        target: ast.TypeExpr | None = parent.type_expr
    elif isinstance(parent, (ast.FnCall, ast.ModuleCall)) and any(a is node for a in parent.args):
        fn = sites.returns.get(parent.name)
        position = next(n for n, a in enumerate(parent.args) if a is node)
        target = fn.params[position] if fn is not None and position < len(fn.params) else None
    else:
        return False
    resolved = sites.resolve(target)
    return isinstance(resolved, ast.RefinementType) and sites.is_nat(resolved.base_type)


def _division_by(node: ast.Node, *, literal: bool) -> bool:
    if not (isinstance(node, ast.BinaryExpr)
            and node.op in (ast.BinOp.DIV, ast.BinOp.MOD)):
        return False
    divisor = node.right
    is_literal = isinstance(divisor, ast.IntLit) and divisor.value != 0
    return is_literal if literal else node.op == ast.BinOp.DIV


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


_NAT_GUARD_SHAPE = ("a `@Nat` value the declarations make non-negative, which "
                    "code generation's declared-name rule does not read as one")
_REFINED_NAT_SHAPE = "a narrowing into a refinement of `Nat`, recorded as the refinement's"
_REFINEMENT_HELD_SHAPE = ("a refinement check on a value the declarations already give "
                          "the refinement: a refined parameter, a `let` of refined slots")
_JOIN_SHAPE = ("a join of a refined arm with an unrefined one, bound into the "
               "refinement, which the checker types as the refinement")

_SHAPES: dict[str, Callable[[ast.Node, Sites], bool]] = {
    "an `@Int` division": lambda node, _s: _division_by(node, literal=False),
    "a division by a non-zero literal":
        lambda node, _s: _division_by(node, literal=True),
    _NAT_GUARD_SHAPE: _nat_guard_on_a_declared_nat,
    _REFINED_NAT_SHAPE: _narrowing_into_refined_nat,
    _REFINEMENT_HELD_SHAPE: _refinement_already_held,
    _JOIN_SHAPE: _join_typed_as_the_refinement,
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

_REPRO_NAT_GUARD = """\
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

_REPRO_REFINED_NAT = """\
type Cap = { @Nat | @Nat.0 <= 5 };

public fn cap(@Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 <= 3)
  ensures(true)
  effects(pure)
{
  let @Cap = @Int.0;
  0
}
"""

_REPRO_REFINED_JOIN = """\
type Pos = { @Int | @Int.0 > 0 };

public fn join(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Pos = 5;
  let @Pos = if @Bool.0 then {
    3
  } else {
    @Pos.0
  };
  0
}
"""

_REPRO_REFINED_PARAMETER = """\
type Low = { @Int | @Int.0 >= 1 && @Int.0 <= 6 };

public fn bump(@Low -> @Int)
  requires(true)
  ensures(@Int.result >= 2 && @Int.result <= 7)
  effects(pure)
{
  @Low.0 + 1
}
"""

#: The mismatches the join reports today that a generated program can meet:
#: each a shape of a `scripts/check_reconciliation.py` `KNOWN` class, or of
#: an open issue the generator found.
KNOWN_CLASSES: tuple[KnownClass, ...] = (
    KnownClass(
        "#1598", "guarded_unrecorded", "int_overflow",
        "wasm/operators.py:_note_quotient_overflow", "an `@Int` division",
        _REPRO_1598),
    KnownClass(
        "#1695 (#1629)", "guarded_unrecorded", "div_zero",
        "wasm/operators.py:_translate_binary",
        "a division by a non-zero literal", _REPRO_1629_DIVISOR),
    # One mechanism, met at every value the checker types `Nat` by its
    # leaves where code generation's own rule reads declared names: a call
    # (#1557), a `Nat` field's binder, a generic one's at `Nat` and a
    # refined slot (#1629), a `State<Nat>` read and its handler, an element
    # of a `Nat` array, a fold from a `Nat` over its `Int` closure.  The typed program's second pull request, in which
    # code generation reads the checker's types, flips this pin: the repro
    # then reports nothing, the cell fails, and the entry comes out.
    KnownClass(
        "#1695", "guarded_unrecorded", "nat_bind",
        "wasm/operators.py:_emit_nat_bind_guard", _NAT_GUARD_SHAPE,
        _REPRO_NAT_GUARD),
    # A narrowing into a refinement of `Nat` is one record (`refine_bind`)
    # and two checks (the sign's and the predicate's): the join pairs the
    # sign's with nothing.  The typed program does not change it; one
    # obligation table (#1695, v0.2.7) flips this pin.
    KnownClass(
        "#1695", "guarded_unrecorded", "nat_bind",
        "wasm/operators.py:_emit_nat_bind_guard", _REFINED_NAT_SHAPE,
        _REPRO_REFINED_NAT),
    KnownClass(
        "#1695 (#1629)", "guarded_unrecorded", "refine_bind",
        "codegen/contracts.py:_emit_refinement_check", _REFINEMENT_HELD_SHAPE,
        _REPRO_REFINED_PARAMETER),
    KnownClass(
        "#1695", "guarded_unrecorded", "refine_bind",
        "codegen/contracts.py:_emit_refinement_check", _JOIN_SHAPE,
        _REPRO_REFINED_JOIN),
)


def reconcile_finds(
    program: Source, known: Sequence[KnownClass] = KNOWN_CLASSES,
    stages: Stages | None = None,
) -> list[Find]:
    """Every mismatch the join reports between *program*'s verification and
    its compiled module, each carrying the issue of the *known* class it
    belongs to, or none."""
    stages = stages if stages is not None else Stages.of(program)
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
            known=cls.issue if cls is not None else "", function=m.function,
            evidence=(f"{cls.shape}, at {m.line}:{m.column}"
                      if cls is not None else ""),
            cls=cls.shape if cls is not None else "",
            site=(m.file, m.line, m.column)))
    return finds


# =====================================================================
# Differential 3: a Tier 1 proof meets no runtime violation
# =====================================================================

def distrust_finds(
    program: Source, trials: int = TRIALS, stages: Stages | None = None,
    stats: dict[str, int] | None = None,
) -> list[Find]:
    """What `vera test --distrust` reports against *program*: a refuted proof
    (E703), a trap it cannot attribute to an obligation, and any other
    failing trial, which on a generated program is a failing check of a
    contract the generator wrote true.  *stats* gains the counts of what
    the run served."""
    stages = stages if stages is not None else Stages.of(program)
    tested = stages.distrust(trials)
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
# Differential 4: a warm session agrees with a fresh one, edit by edit
# =====================================================================

def _obligation_prints(result: object) -> list[tuple[str, str, str, int, int, str, str]]:
    return [(o.file or "", o.fn_name, o.kind, o.line, o.column, o.status, o.expr_text)
            for o in result.obligations]  # type: ignore[attr-defined]


#: The class of a warm differential's find in which the two sessions differ
#: in a counterexample alone (#1785): the model the solver returns is one of
#: many that refute a clause, and the differences seen came in a four-worker
#: run, after other programs, and not when the seed ran alone in a new
#: process.  The mechanism is not established, and no seed shows one in a
#: new process, so the class has no pin: it is counted, and fails nothing.
WARM_MODEL_ISSUE = "#1785"
WARM_MODEL_SHAPE = "a counterexample the warm session and a fresh one model apart"


def _diagnostic_prints(result: object) -> list[tuple[str, str, str, str, int, int]]:
    """Each diagnostic, its description without a counterexample's values:
    a counterexample is a model the solver chose, and two sessions that
    differ in it alone make a find of #1785's class, not a disagreement."""
    return [(d.severity, d.error_code or "", _without_model(d.description),
             d.location.file or "", d.location.line, d.location.column)
            for d in result.diagnostics]  # type: ignore[attr-defined]


def _without_model(description: str) -> str:
    return description.split("\n  Counterexample:", 1)[0]


def _by_place(prints: list[tuple[str, str, str, int, int, str, str]]
              ) -> dict[tuple[object, ...], str]:
    """Each obligation's status, keyed by its file, function, kind, place,
    text and rank among its namesakes."""
    seen: dict[tuple[object, ...], int] = {}
    out: dict[tuple[object, ...], str] = {}
    for p in prints:
        key = (*p[:5], p[6])
        out[(*key, seen.get(key, 0))] = p[5]
        seen[key] = seen.get(key, 0) + 1
    return out


def _disagreements(n: int, name: str, warm: object, fresh: object) -> list[Find]:
    """What the warm session's answer to edit *n* and a fresh session's
    disagree on: an obligation's status or presence, their order, and the
    diagnostics."""
    head = f"edit {n} ({name})"
    a, b = _obligation_prints(warm), _obligation_prints(fresh)
    finds: list[Find] = []
    ka, kb = _by_place(a), _by_place(b)
    for key in sorted(set(ka) | set(kb), key=repr):
        if ka.get(key) == kb.get(key):
            continue
        file, fn, kind, line, column, _text, _rank = key
        both = key in ka and key in kb
        finds.append(Find(
            "warm", ("obligations", "status" if both else "presence", str(kind)),
            f"{head}: the `{kind}` obligation in '{fn}' at {line}:{column} is "
            f"{ka.get(key, 'absent')} in the warm session and "
            f"{kb.get(key, 'absent')} in a fresh one", function=str(fn)))
    if not finds and a != b:
        finds.append(Find("warm", ("obligations", "order"),
                          f"{head}: the two sessions report the same obligations "
                          f"in a different order"))
    da, db = _diagnostic_prints(warm), _diagnostic_prints(fresh)
    if da != db:
        only_warm = [d for d in da if d not in db]
        only_fresh = [d for d in db if d not in da]
        finds.append(Find("warm", ("diagnostics",),
                          f"{head}: the warm session alone reports {only_warm}, "
                          f"a fresh one alone {only_fresh}"))
    return finds


def warm_finds(
    prog: gen.Program, directory: Path, *,
    warm: type[VerificationSession] = VerificationSession,
    fresh: type[VerificationSession] = VerificationSession,
    edits: Sequence[gen.Edit] | None = None,
    stats: dict[str, int] | None = None,
) -> list[Find]:
    """The program and its edits through one warm session, in order, as the
    language server sends a document's text, and each text through a fresh
    session alone: every disagreement between the two, named by its edit.
    The module is written beside the entry, which both sessions read it
    from.  *stats* gains how many edits ran and how many functions the warm
    session replayed: a comparison over a session that replayed nothing
    would hold of a cache that is never read."""
    edits = list(edits) if edits is not None else gen.edits(prog, EDITS)
    target = directory / f"w{next(_directories)}"
    target.mkdir(parents=True, exist_ok=True)
    if prog.module is not None:
        (target / gen.MODULE_FILE).write_text(gen.render_module(prog), encoding="utf-8")
    path = str(target / LABEL)
    session = warm()
    finds: list[Find] = []
    replayed = 0
    for n, edit in enumerate(edits):
        text = edit.program.render()
        answer = session.verify_source(text, file=path)
        replayed += session.last_run_stats.replayed_fns
        alone = fresh().verify_source(text, file=path)
        found = _disagreements(n, edit.name, answer, alone)
        if not any(f.signature == ("diagnostics",) for f in found) and [
                d.description for d in answer.diagnostics] != [
                d.description for d in alone.diagnostics]:
            found.append(Find(
                "warm", ("diagnostics", "counterexample"),
                f"edit {n} ({edit.name}): the two sessions report the same "
                f"diagnostics with different counterexamples",
                known=WARM_MODEL_ISSUE, cls=WARM_MODEL_SHAPE,
                evidence="the diagnostics agree without their counterexamples"))
        finds += found
    if stats is not None:
        stats["warm_edits"] = stats.get("warm_edits", 0) + len(edits) - 1
        stats["warm_replayed_fns"] = stats.get("warm_replayed_fns", 0) + replayed
    return finds


# =====================================================================
# Code generation's own reading of a value's type
# =====================================================================

@dataclass(frozen=True)
class Rederived:
    """A class of finds code generation makes by reading a value's type off
    the expression rather than the checker's types, by the open issue whose
    class it is: the program with each of its values bound in place by a
    `let` of the type the checker gives it
    (`program_generator.bind_in_place`), which code generation reads off
    the declaration, makes none of them, and no find of its own."""

    issue: str
    #: The values the counterfactual binds, in words.
    shape: str
    #: What `program_generator.bind_in_place` binds for it, on top of the
    #: classes before it.
    kinds: tuple[str, ...]
    #: A program whose every find of the load, reconcile and distrust
    #: differentials is this class's.
    repro: Callable[[], gen.Program]


#: The differentials whose finds code generation's reading of a type makes.
_CODEGEN = ("load", "reconcile", "distrust")


def _codegen_finds(prog: gen.Program, stages: Stages, trials: int,
                   stats: dict[str, int] | None = None) -> list[Find]:
    return (load_finds(prog, prog.calls(), stages)
            + reconcile_finds(prog, KNOWN_CLASSES, stages)
            + distrust_finds(prog, trials, stages, stats))


def _key(f: Find) -> tuple[str, tuple[str, ...], str]:
    return (f.differential, f.signature, f.function)


def _at_a_bound_value(f: Find, sites: Sites) -> bool:
    """Whether *f* is a mismatch at the value of a `let` the counterfactual
    wrote, `{ let @T = value; @T.0 }`: a `let @Nat` of a fold from a `Nat`
    makes the `nat_bind` class's guard there by construction."""
    if f.site is None:
        return False
    for node in sites._at.get(f.site, []):
        let = sites.parent.get(id(node))
        block = sites.parent.get(id(let)) if let is not None else None
        if (isinstance(let, ast.LetStmt) and let.value is node
                and isinstance(block, ast.Block) and len(block.statements) == 1
                and block.statements[0] is let
                and isinstance(block.expr, ast.SlotRef) and block.expr.index == 0):
            return True
    return False


def _alike(a: Find, b: Find) -> bool:
    """Whether two finds are the same find of two programs that differ in
    columns only: their differential, signature and function.  Two sites
    of one signature in one function are alike, so one of them vanishing
    while the other stays marks neither: the classification only ever
    keeps a find a find."""
    return (a.differential, a.signature, a.function) == (
        b.differential, b.signature, b.function)


def classify_rederived(
    prog: gen.Program, finds: list[Find], directory: Path | None,
    trials: int = TRIALS, stats: dict[str, int] | None = None,
) -> list[Find]:
    """*finds* with each load, reconcile and distrust find that vanishes once
    code generation reads a class's values off a declaration
    (:data:`REDERIVED`) marked with the class's issue.

    Each class's counterfactual binds its values on top of the classes
    before it, and a find is the first class's under which it vanishes:
    the counterfactual makes no find alike it outside the known classes,
    and no more alike it in all than the program made inside them, so one
    it makes again in a known class has not vanished.  A
    counterfactual that does not check and verify clean, or that makes a
    find outside the known classes the program does not, isolates nothing,
    and classifies nothing more.  A known find the counterfactual makes
    anew, as binding a fold from a `Nat` in a `let @Nat` makes the
    `nat_bind` class's guard, does not.  A find that vanishes under none
    stays a find.  Where every find
    vanishes, *stats* takes the counterfactual's distrust run, which ran
    the functions the program's module could not."""
    open_ = [f for f in finds if not f.known and f.differential in _CODEGEN]
    if not open_:
        return finds
    held = Counter(_key(f) for f in finds if f.known and f.differential in _CODEGEN)
    marked: dict[int, Rederived] = {}
    kinds: tuple[str, ...] = ()
    served: dict[str, int] = {}
    for cls in REDERIVED:
        kinds += cls.kinds
        bound = gen.bind_in_place(prog, kinds)
        if bound is None:
            continue
        stages = Stages.of(bound, directory if bound.module is not None else None)
        if [f for f in contract_finds(bound, stages) if f.signature != ("fmt",)]:
            break
        served = {}
        after = _codegen_finds(bound, stages, trials, served)
        if any(not any(_alike(f, g) for g in open_) for f in after if not f.known):
            break
        anew = Counter(_key(f) for f in after if not f.known)
        written = Sites(stages.verified.checked)
        again = Counter(_key(f) for f in after
                        if not f.known or not _at_a_bound_value(f, written))
        for f in open_:
            # The program's open finds of a signature vanish when the
            # counterfactual makes none of them outside the classes and no
            # more of them in all than the program made inside one, beside
            # the known ones its own `let`s make: a find it makes again in a
            # known class has not vanished.
            k = _key(f)
            if id(f) not in marked and not anew[k] and again[k] <= held[k]:
                marked[id(f)] = cls
        if len(marked) == len(open_):
            if stats is not None:
                stats.update(served)
            break
    return [replace(f, known=marked[id(f)].issue, cls=marked[id(f)].shape, evidence=(
                "vanished with each value of its class bound in place by a "
                "`let` of the type the checker gives it"))
            if id(f) in marked else f for f in finds]


def _items() -> gen.Binding:
    """`let @Array<Int> = [0, 1, 8];`"""
    return gen.Binding("Array<Int>", value=gen.ArrayLit(
        "Int", [gen.Lit(0), gen.Lit(1), gen.Lit(8)]))


def _sum(items: gen.Binding, init: gen.Expr | None = None) -> gen.Fold:
    """`array_fold` over *items* from *init* (0), adding each element."""
    acc, elem = gen.Binding("Int", gen.ANY, gen.Iv(0, 0)), gen.Binding(
        "Int", gen.ANY, gen.Iv(0, 0))
    return gen.Fold(gen.Ref(items), init if init is not None else gen.Lit(0), acc, elem,
                    gen.Bin("+", gen.Ref(acc), gen.Ref(elem)))


def _cell(put: int, init: int = 0) -> gen.Handle:
    """`handle[State<Int>](@Int = init)` over `put(put); get(())`."""
    return gen.Handle("State", "Int", gen.Lit(init), gen.Block(
        [gen.Do(gen.Put("Int", gen.Lit(put)))], gen.Get("Int")))


def _pick() -> gen.Function:
    """`f0(@Bool, @T, @T -> @T)`, the generator's `choose` generic."""
    flag, a, b = gen.Binding("Bool"), gen.Binding("T"), gen.Binding("T")
    return gen.Function("f0", False, [flag, a, b], "T", gen.Block([], gen.If(
        gen.Ref(flag), gen.Block([], gen.Ref(a)), gen.Block([], gen.Ref(b)))),
        kind="generic", forall=["T"], template="choose",
        contract=["requires(true)", "ensures(true)"])


def _one(body: gen.Expr, *, lets: Sequence[gen.Let] = (), ret: str = "Int",
         params: Sequence[gen.Binding] = (), example: Sequence[int | bool] = (),
         functions: Sequence[gen.Function] = (),
         datas: Sequence[gen.Data] = ()) -> gen.Program:
    """A program of one public function `f9` over *body*, after *functions*."""
    fn = gen.Function("f9", True, list(params), ret, gen.Block(list(lets), body),
                      ensure_style="none", example=list(example))
    return gen.Program(0, list(datas), [*functions, fn], [fn])


def _repro_fold_argument() -> gen.Program:
    """`Some(array_fold(...))`: code generation infers no type for a fold as
    a constructor's argument, and drops the function (E602; #1525's line
    from #1680).  The arm's `@Nat.0 * 2` gives the function a postcondition
    the verifier proves, so `vera test --distrust` runs the function the
    counterfactual compiles."""
    items = _items()
    x = gen.Binding("Int", gen.ANY, gen.Iv(9, 9))
    n = gen.Binding("Nat", gen.Iv(0, 5), gen.Iv(0, 5))
    opt = gen.Binding("Option<Int>", value=gen.Construct(
        gen.SOME, [_sum(items)], ty="Option<Int>"))
    match = gen.Match(gen.Ref(opt), [
        gen.Arm(gen.Pattern(ctor=gen.SOME, binders=[x]), gen.Bin("*", gen.Ref(n), gen.Lit(2))),
        gen.Arm(gen.Pattern(ctor=gen.NONE), gen.Lit(0))])
    return _one(match, lets=[gen.Let(items), gen.Let(opt)], params=[n], example=[1])


def _repro_handler_arms() -> gen.Program:
    """An `if` whose two arms are each a `handle[State<Int>]`: code
    generation lowers it with no result type, and the module does not load
    (#1744's handler block).  Its `ensures`, which the verifier leaves to
    Tier 3, gives `vera test` a check to run once the module loads."""
    flag = gen.Binding("Bool")
    prog = _one(gen.If(gen.Ref(flag), gen.Block([], _cell(3)),
                       gen.Block([], _cell(4, -2))), params=[flag], example=[True])
    prog.functions[-1].contract = ["requires(true)",
                                   "ensures(@Int.result >= 3 && @Int.result <= 4)"]
    return prog


#: The classes of code generation's own reading of a value's type, each
#: binding its values on top of the classes before it.
REDERIVED: tuple[Rederived, ...] = (
    Rederived("#1525", "a fold as a scrutinee, a constructor's argument or a "
              "branch's every arm, which code generation finds no type for",
              (gen.BIND_FOLD,), _repro_fold_argument),
    Rederived("#1744", "a handler a branch takes, which code generation "
              "lowers with no result type", (gen.BIND_HANDLER_ARM,),
              _repro_handler_arms),
)


# =====================================================================
# One program through all of it
# =====================================================================

def differentials(
    prog: gen.Program, directory: Path | None = None, *, trials: int = TRIALS,
    known: Sequence[KnownClass] = KNOWN_CLASSES,
    stats: dict[str, int] | None = None, warm: bool = True,
) -> list[Find]:
    """The generator's contract, then the four differentials, over *prog*,
    each stage run once.  A program that breaks the contract goes no
    further.  *stats* gains what the stages counted."""
    if directory is None:
        assert prog.module is None
    stages = Stages.of(prog, directory)
    finds = contract_finds(prog, stages)
    if stats is not None and stages.verified.ran:
        for o in stages.verified.obligations:
            stats[f"obligation_{o.status}"] = stats.get(
                f"obligation_{o.status}", 0) + 1
    if finds:
        finds, counterfactual = classify_contract(prog, finds, stages, directory)
        if counterfactual is None:
            return finds
        # Every contract find is #1525's: the differentials run over the
        # program with the counterfactual's `let`s, which verifies clean.
        prog = counterfactual
        stages = Stages.of(prog, directory)
    finds += load_finds(prog, prog.calls(), stages)
    finds += reconcile_finds(prog, known, stages)
    finds += distrust_finds(prog, trials, stages, stats)
    finds = classify_rederived(prog, finds, directory, trials, stats)
    if warm and directory is not None:
        finds += warm_finds(prog, directory, stats=stats)
    return finds


def still_fails(find: Find, directory: Path, *,
                trials: int = TRIALS) -> Callable[[gen.Program], bool]:
    """The minimiser's predicate for *find*: a candidate keeps the
    generator's contract and its differential still reports a find with
    *find*'s signature and class (a contract find keeps only its own)."""
    def holds(candidate: gen.Program) -> bool:
        return _same(find, candidate, directory, trials) is not None
    return holds


def _same(find: Find, prog: gen.Program, directory: Path, trials: int) -> Find | None:
    """The find *prog* reports in *find*'s place, if it reports one."""
    stages = Stages.of(prog, directory)
    contract = contract_finds(prog, stages)
    if contract:
        contract, counterfactual = classify_contract(prog, contract, stages, directory)
        if find.differential != "contract" and counterfactual is not None:
            prog = counterfactual
            stages = Stages.of(prog, directory)
            contract = []
    if find.differential == "contract":
        found = contract
    elif contract:
        return None
    elif find.differential == "warm":
        found = warm_finds(prog, directory)
    else:
        found = [f for f in classify_rederived(
                     prog, _codegen_finds(prog, stages, trials), directory, trials)
                 if f.differential == find.differential]
    return next((f for f in found if f.signature == find.signature
                 and f.known == find.known), None)


def hold(seed: int, directory: Path) -> None:
    """The contract and the four differentials over *seed*'s program: a
    find outside the known classes is minimised, recorded with what the
    generator expected of the minimal program, and fails the cell."""
    started = time.perf_counter()
    prog = gen.generate(seed)
    stats: dict[str, int] = {}
    finds = differentials(prog, directory, stats=stats)
    found = [f for f in finds if not f.known]
    record: dict[str, object] = {
        "seed": seed, "shape": prog.shape(), "stats": stats,
        "finds": [f.to_dict() for f in finds],
    }
    if found:
        if _minimised[0] < MINIMISE_LIMIT:
            _minimised[0] += 1
            minimal = gen.minimize(prog, still_fails(found[0], directory),
                                   budget=MINIMISE_BUDGET)
            shrunk = _same(found[0], minimal, directory, TRIALS) or found[0]
        else:
            minimal, shrunk = prog, found[0]
            record["unminimised"] = (
                f"this process had minimised {MINIMISE_LIMIT} finds already")
        args = list(shrunk.args) if shrunk.function else None
        record["find"] = {
            **shrunk.to_dict(),
            "expected": gen.expectations(minimal, shrunk.function, args),
            "minimal": _joined(minimal),
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


def _joined(prog: gen.Program) -> str:
    """Every file of *prog*, the module's after the entry's under its name."""
    files = prog.files()
    out = files[LABEL]
    if gen.MODULE_FILE in files:
        out += f"\n-- {gen.MODULE_FILE}\n{files[gen.MODULE_FILE]}"
    return out


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
            _joined(prog), encoding="utf-8")
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
def test_the_program_checks_clean(seed: int, tmp_path: Path) -> None:
    """Every program the generator writes passes `vera check` with no
    diagnostic, and each of its files is in `vera fmt`'s canonical form: a
    slot reference the generator computed wrong, or a layout the formatter
    would change, fails here on every pull request."""
    files = gen.generate(seed).files()
    entry = pipeline.write_tree(tmp_path, files, entry=LABEL)
    checked = pipeline.check(entry, file=LABEL)
    assert not checked.diagnostics, "\n\n".join(
        d.format() for d in checked.diagnostics) + f"\n\n{files[LABEL]}"
    for name, text in files.items():
        assert format_source(text, file=name) == text, _first_difference(
            text, format_source(text, file=name))


@pytest.mark.parametrize("seed", SEEDS)
def test_the_differentials_hold_over_the_pinned_seeds(seed: int, tmp_path: Path) -> None:
    """The contract and the four differentials over the pinned seeds, as
    the nightly lane runs them over the night's: a change that breaks code
    generation, the join, the tester or the warm session for these shapes
    fails here."""
    hold(seed, tmp_path)


def _programs_in_a_process(seeds: Sequence[int], hash_seed: str) -> list[dict[str, str]]:
    """The programs *seeds* write in a fresh interpreter whose string hashes
    are seeded with *hash_seed*: the process boundary is what this measures,
    since a set's order is one thing that differs between processes."""
    script = (
        "import json, sys\n"
        "from tests import program_generator as g\n"
        "print(json.dumps([g.generate(s).files() for s in json.loads(sys.argv[1])]))\n"
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
    """A seed writes its program byte for byte, module and all: twice in
    this process, and in two processes whose string hashes differ, so a
    find's seed is its program on any machine."""
    here = [gen.generate(seed).files() for seed in SEEDS]
    assert here == [gen.generate(seed).files() for seed in SEEDS]
    assert len({json.dumps(p) for p in here}) == len(here), "two seeds wrote one program"
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


@pytest.mark.parametrize("parent", gen.COMPARE)
def test_a_comparison_is_never_an_unparenthesised_operand_of_one(parent: str) -> None:
    """The night of 2026-10-22 (#1781): an exact `ensures` wrote a `let`'s
    comparison as an operand of another, `0 == -5 != true`, which the
    parser refuses (E005), since a comparison groups with nothing.  Every
    comparison at a comparison's level, on either side, is parenthesised,
    in a body and in a contract, and the program parses."""
    for child in gen.COMPARE:
        if gen.PREC[child] != gen.PREC[parent]:
            continue
        for side in ("left", "right"):
            inner = gen.Bin(child, gen.Lit(0), gen.Lit(-5))
            flag = gen.Binding("Bool", value=inner)
            pair = ((gen.Ref(flag), gen.Lit(True)) if side == "left"
                    else (gen.Lit(True), gen.Ref(flag)))
            fn = gen.Function("f0", False, [], "Bool",
                              gen.Block([gen.Let(flag)], gen.Bin(parent, *pair)),
                              ensure_style="exact")
            prog = gen.Program(0, [], [fn], [])
            text = prog.render()
            written = f"(0 {child} -5)"
            assert gen.ensure_style(fn) == "exact"
            assert written in text.split("ensures(", 1)[1].split("\n", 1)[0], text
            parsed = pipeline.parse(text, file=LABEL)
            assert parsed.ok, (parent, child, side, parsed.diagnostics)
            inlined = copy.deepcopy(prog)
            gen._replace_everywhere(inlined, inlined.functions[0].body.lets[0].binding, inner)
            inlined.functions[0].body.lets.clear()
            assert pipeline.parse(inlined.render(), file=LABEL).ok, inlined.render()


def _measured(step: gen.Expr | None) -> gen.Program:
    """`f0(@Nat -> @Int)` counting its measure down, its step calling itself
    on *step* (the measure less one when ``None``)."""
    m = gen.Binding("Nat", gen.Iv(0, 4), gen.Iv(0, 4))
    view = gen.Binding("Nat", gen.Iv(1, 4), gen.Iv(1, 4), view_of=m)
    fn = gen.Function("f0", True, [m], "Int", gen.Block([], gen.Lit(0)),
                      kind="recursive", measure=m, example=[3])
    fn.group = [fn]
    arg = step if step is not None else gen.Bin("-", gen.Ref(view), gen.Lit(1))
    fn.body = gen.Block([], gen.If(
        gen.Bin("==", gen.Ref(m), gen.Lit(0)), gen.Block([], gen.Lit(1)),
        gen.Block([], gen.Call(fn, [arg]))))
    return gen.Program(0, [], [fn], [fn])


def _fold_less_its_init() -> gen.Program:
    """`array_fold` from a `@Nat` init over `fn(@Int, @Int -> @Int)`, less
    the same `@Nat`: the checker types the fold `@Nat`, so the subtraction
    is a `@Nat` one, whose check fails on every run of the generated
    input."""
    n = gen.Binding("Nat", gen.Iv(20, 35), gen.Iv(20, 35))
    items = gen.Binding("Array<Int>", value=gen.ArrayLit("Int", [gen.Lit(20), gen.Lit(-1)]))
    acc, elem = gen.Binding("Int", gen.ANY, gen.Iv(0, 0)), gen.Binding(
        "Int", gen.ANY, gen.Iv(0, 0))
    fold = gen.Fold(gen.Ref(items), gen.Ref(n), acc, elem, gen.Lit(0))
    return _one(gen.Bin("-", fold, gen.Ref(n)), lets=[gen.Let(items)], params=[n],
                example=[28])


def _member_fold_scrutinee() -> gen.Program:
    """A `match` on `array_fold(...)`: code generation infers no type for
    the scrutinee, and drops the function (E602; #1525's line from
    #1679)."""
    items = _items()
    match = gen.Match(_sum(items), [gen.Arm(gen.Pattern(literal=9), gen.Lit(1)),
                                    gen.Arm(gen.Pattern(), gen.Lit(2))])
    flag = gen.Binding("Bool")
    return _one(match, lets=[gen.Let(items)], params=[flag], example=[True])


def _member_fold_arms() -> gen.Program:
    """An `if` of two folds: code generation types neither arm, lowers the
    `if` with no result type, and the module does not load."""
    items = _items()
    flag = gen.Binding("Bool")
    return _one(gen.If(gen.Ref(flag), gen.Block([], _sum(items)),
                       gen.Block([], _sum(items, gen.Lit(1)))),
                lets=[gen.Let(items)], params=[flag], example=[True])


def _member_throw_and_fold() -> gen.Program:
    """Under `handle[Exn<Int>]`, an `if` of a `throw` and a fold: neither
    arm typed, and the module does not load."""
    items = _items()
    flag = gen.Binding("Bool")
    payload = gen.Binding("Int", gen.ANY, gen.Iv(1, 1))
    branch = gen.If(gen.Ref(flag), gen.Block([], gen.Throw("Int", gen.Lit(1))),
                    gen.Block([], _sum(items)))
    return _one(gen.Handle("Exn", "Int", None, gen.Block([], branch), payload, gen.Lit(2)),
                lets=[gen.Let(items)], params=[flag], example=[False])


def _member_handler_match() -> gen.Program:
    """A `match` on a `Bool` whose two arms are each a handler: the module
    does not load (#1744's handler block, at a `match`)."""
    flag = gen.Binding("Bool")
    return _one(gen.Match(gen.Ref(flag), [gen.Arm(gen.Pattern(literal=True), _cell(3)),
                                          gen.Arm(gen.Pattern(literal=False), _cell(4, -2))]),
                params=[flag], example=[True])


#: Each shape code generation reads a type of its own at, by the issue its
#: finds are counted under.
_REDERIVED_MEMBERS: dict[str, tuple[str, Callable[[], gen.Program]]] = {
    "fold_argument": ("#1525", _repro_fold_argument),
    "fold_scrutinee": ("#1525", _member_fold_scrutinee),
    "fold_arms": ("#1525", _member_fold_arms),
    "throw_and_fold": ("#1525", _member_throw_and_fold),
    "handler_arms": ("#1744", _repro_handler_arms),
    "handler_match": ("#1744", _member_handler_match),
}


@pytest.mark.parametrize("member", sorted(_REDERIVED_MEMBERS))
def test_each_rederived_class_reads_its_members(member: str) -> None:
    """Each shape the generator writes where code generation reads a type
    of its own makes a find of the load, reconcile or distrust differential
    that `vera check` and `vera verify` do not, and each such find vanishes
    with the shape's values bound in place: it is its class's, and the
    program fails nothing."""
    issue, build = _REDERIVED_MEMBERS[member]
    prog = build()
    stages = Stages.of(prog)
    assert contract_finds(prog, stages) == []
    plain = [f for f in _codegen_finds(prog, stages, TRIALS) if not f.known]
    assert plain, f"{member} makes no find: has {issue}'s fix landed?"
    shape = next(c.shape for c in REDERIVED if c.issue == issue)
    classified = classify_rederived(prog, plain, None)
    assert {(f.known, f.cls) for f in classified} == {(issue, shape)}, classified


@pytest.mark.parametrize("cls", REDERIVED, ids=[c.issue for c in REDERIVED])
def test_each_rederived_class_keeps_its_repro(cls: Rederived) -> None:
    """The class's pin: its repro makes a find of the load, reconcile or
    distrust differential, every such find is the class's, the program
    fails nothing, and the distrust run counted is the counterfactual's,
    which ran the function.  The day the issue is fixed the repro makes no
    find, this fails, and the class comes out."""
    stats: dict[str, int] = {}
    finds = differentials(cls.repro(), stats=stats, warm=False)
    assert [f for f in finds if not f.known] == [], finds
    assert [f for f in finds if f.known == cls.issue and f.cls == cls.shape], finds
    assert stats["public_tested"] >= 1, stats
    bound = gen.bind_in_place(cls.repro(), cls.kinds)
    assert bound is not None
    assert [n for f in gen.all_functions(bound) for n in gen._walk(f.body)
            if isinstance(n, gen.Bound)], bound.render()
    assert pipeline.check(bound.render(), file=LABEL).ok, bound.render()


def _clauses(text: str) -> list[str]:
    """Every contract clause of a program's text, in order."""
    return [line.strip() for line in text.splitlines()
            if line.strip().startswith(("requires(", "ensures(", "decreases("))]


def test_the_counterfactual_writes_every_contract_as_the_program_does() -> None:
    """The counterfactual changes bodies alone: over a hundred programs,
    each binding every value of every class, the contracts of the entry and
    of the module are the program's, clause for clause, a caller's `ensures`
    that reads its callee's included (seed 429's: a contract fixed before
    its caller's was read made the caller's `ensures(true)`)."""
    kinds = [k for c in REDERIVED for k in c.kinds]
    bound_some = 0
    for seed in range(100):
        prog = gen.generate(seed)
        bound = gen.bind_in_place(prog, kinds)
        if bound is None:
            continue
        bound_some += 1
        for name, text in prog.files().items():
            assert _clauses(bound.files()[name]) == _clauses(text), (seed, name)
    assert bound_some, "no program of a hundred holds a value to bind"


def test_a_find_the_counterfactual_does_not_remove_stays_a_find(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """The class's boundary: in a program of #1525's class, a find that the
    counterfactual makes too is a find, beside the class's counted ones,
    though its detail moves with the counterfactual's columns, as a
    mismatch's site does."""
    real = load_finds

    def with_another(program: Source, calls: Sequence[tuple[str, Sequence[int] | None]],
                     stages: Stages | None = None) -> list[Find]:
        column = 9 if isinstance(program, gen.Program) and "{ let @" in program.render() else 5
        return real(program, calls, stages) + [
            Find("load", ("call", "elsewhere"), f"a find no `let` explains, at 1:{column}",
                 function="f9")]

    monkeypatch.setattr(sys.modules[__name__], "load_finds", with_another)
    finds = differentials(_repro_fold_argument(), warm=False)
    assert [f.signature for f in finds if not f.known] == [("call", "elsewhere")], finds
    assert [f for f in finds if f.known == "#1525"], finds


def test_a_counterfactual_that_makes_a_find_of_its_own_classifies_nothing(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """A counterfactual that makes a find the program does not no longer
    isolates the class: the program's finds stay finds."""
    real = load_finds

    def in_the_counterfactual(program: Source,
                              calls: Sequence[tuple[str, Sequence[int] | None]],
                              stages: Stages | None = None) -> list[Find]:
        out = real(program, calls, stages)
        if isinstance(program, gen.Program) and "{ let @" in program.render():
            out.append(Find("load", ("call", "new"), "a find the counterfactual alone makes",
                            function="f9"))
        return out

    monkeypatch.setattr(sys.modules[__name__], "load_finds", in_the_counterfactual)
    finds = differentials(_repro_fold_argument(), warm=False)
    codegen = [f for f in finds if f.differential in _CODEGEN]
    assert codegen and not [f for f in codegen if f.known], finds


def test_a_fold_takes_its_initial_values_type() -> None:
    """The checker binds a fold's accumulator to its initial value's type:
    a fold from a `@Nat` is a `@Nat`, so `fold - @Nat.0` is a `@Nat`
    subtraction, which `vera verify` records (`nat_sub`, Tier 3) and the
    generator writes only where it is provable, so never here; and the
    counterfactual binds the fold at `Nat`, the checker's type, so the
    subtraction stays the `@Nat` one it is."""
    prog = _fold_less_its_init()
    value = prog.functions[-1].body.result
    assert isinstance(value, gen.Bin) and isinstance(value.left, gen.Fold)
    assert gen.static_type(value.left) == "Nat"
    assert gen.static_type(_sum(_items())) == "Int"
    statuses = {(o.kind, o.status) for o in Stages.of(prog).verified.obligations}
    assert ("nat_sub", "tier3") in statuses, statuses
    assert not gen.well_formed(copy.deepcopy(prog))
    bound = gen.bind_in_place(prog, [gen.BIND_FOLD])
    assert bound is not None
    assert "{ let @Nat = array_fold(" in bound.render(), bound.render()


def test_a_fold_from_a_nat_keeps_its_run_non_negative() -> None:
    """A fold from a `@Nat` is a `@Nat`, so a run of it that goes negative
    breaks its type at the first binding (the module's guard traps): the
    generator writes it only where its run stays non-negative, and the
    minimiser keeps to that."""
    n = gen.Binding("Nat", gen.Iv(0, 3), gen.Iv(0, 3))
    items = gen.Binding("Array<Int>", value=gen.ArrayLit("Int", [gen.Lit(1), gen.Lit(2)]))

    def program(step: int) -> gen.Program:
        acc, elem = gen.Binding("Int", gen.ANY, gen.Iv(0, 0)), gen.Binding(
            "Int", gen.ANY, gen.Iv(0, 0))
        fold = gen.Fold(gen.Ref(items), gen.Ref(n), acc, elem,
                        gen.Bin("+", gen.Ref(acc), gen.Lit(step)))
        bound = gen.Binding("Nat", value=fold)
        return _one(gen.Ref(bound), lets=[gen.Let(items), gen.Let(bound)], ret="Nat",
                    params=[n], example=[1])

    assert gen.well_formed(program(1))
    assert not gen.well_formed(program(-5))


def test_a_member_beside_a_known_find_of_its_signature_is_counted(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """A class's find in a function that also holds a known find of its
    signature: the counterfactual makes the known one again and not the
    member, so the member has vanished and is counted (seed 429's shape, a
    `nat_bind` guard of #1525's beside one of #1695's, until #1791 closed
    that member's line: here the program's `E602` beside a known one)."""
    real = load_finds
    prog = _repro_fold_argument()
    member = [f for f in real(prog, prog.calls()) if f.signature == ("compile", "E602")]
    assert [f.function for f in member] == ["f9"], member

    def beside(program: Source, calls: Sequence[tuple[str, Sequence[int] | None]],
               stages: Stages | None = None) -> list[Find]:
        return real(program, calls, stages) + [
            replace(member[0], detail="held", known="#1695")]

    monkeypatch.setattr(sys.modules[__name__], "load_finds", beside)
    finds = differentials(prog, warm=False)
    assert [f for f in finds if not f.known] == [], finds
    assert sorted(f.known for f in finds if _key(f) == _key(member[0])) == [
        "#1525", "#1695"], finds


def test_a_find_that_stays_beside_a_known_one_that_goes_stays_a_find(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """A program's open find beside a known find of its signature, of which
    the counterfactual makes the open one again and not the known one: as
    many of the signature as the program made in the classes, but one
    outside them, so the open one has not vanished."""
    real = load_finds

    def pair(program: Source, calls: Sequence[tuple[str, Sequence[int] | None]],
             stages: Stages | None = None) -> list[Find]:
        bound = isinstance(program, gen.Program) and "{ let @" in program.render()
        out = real(program, calls, stages) + [
            Find("load", ("call", "pair"), "open", function="f9")]
        if not bound:
            out.append(Find("load", ("call", "pair"), "known", function="f9", known="#1695"))
        return out

    monkeypatch.setattr(sys.modules[__name__], "load_finds", pair)
    finds = differentials(_repro_fold_argument(), warm=False)
    assert [f.known for f in finds if f.signature == ("call", "pair")
            and f.detail == "open"] == [""], finds


def test_a_member_beside_a_guard_the_counterfactual_writes_is_counted(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """A class's find in a function holding a fold from a `@Nat`: the
    counterfactual binds the fold at `Nat`, the checker's type, in a
    `let @Nat`, whose guard is the `nat_bind` class's by construction; that
    guard is not the member made again, so the member is counted (seed
    2101717 of the replay of #1781's night, whose member #1791 closed: here
    a find of the guard's signature the program alone makes)."""
    n = gen.Binding("Nat", gen.Iv(0, 5), gen.Iv(0, 5))
    items = gen.Binding("Array<Int>", value=gen.ArrayLit("Int", [gen.Lit(4), gen.Lit(-3)]))
    acc, elem = gen.Binding("Int", gen.ANY, gen.Iv(0, 0)), gen.Binding(
        "Int", gen.ANY, gen.Iv(0, 0))
    fold = gen.Fold(gen.Ref(items), gen.Ref(n), acc, elem, gen.Lit(0))
    prog = _one(gen.Bin("+", gen.Ref(n), fold), lets=[gen.Let(items)], params=[n],
                example=[1])
    assert gen.static_type(fold) == "Nat"
    bound = gen.bind_in_place(prog, gen.BIND_KINDS)
    assert bound is not None
    own = [f for f in reconcile_finds(bound) if f.function == "f9"]
    assert [(f.signature[:2], f.known) for f in own] == [
        (("guarded_unrecorded", "nat_bind"), "#1695")], own
    real = reconcile_finds

    def alone(program: Source, known: Sequence[KnownClass] = KNOWN_CLASSES,
              stages: Stages | None = None) -> list[Find]:
        out = real(program, known, stages)
        if isinstance(program, gen.Program) and "{ let @" in program.render():
            return out
        return out + [replace(own[0], detail="the program's", known="", cls="",
                              evidence="", site=None)]

    monkeypatch.setattr(sys.modules[__name__], "reconcile_finds", alone)
    finds = differentials(prog, warm=False)
    assert [f for f in finds if not f.known] == [], finds
    assert [f.known for f in finds if _key(f) == _key(own[0])] == ["#1525"], finds


def test_two_sites_of_one_signature_where_one_vanishes_stay_finds(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """Two finds of one signature in one function, of which the
    counterfactual makes one again: their sites cannot be told apart across
    the counterfactual's columns, so neither is marked, and the one that
    stays is never counted under the class."""
    real = load_finds

    def two_sites(program: Source, calls: Sequence[tuple[str, Sequence[int] | None]],
                  stages: Stages | None = None) -> list[Find]:
        bound = isinstance(program, gen.Program) and "{ let @" in program.render()
        return real(program, calls, stages) + [
            Find("load", ("call", "twin"), f"site {n}", function="f9")
            for n in range(1 if bound else 2)]

    monkeypatch.setattr(sys.modules[__name__], "load_finds", two_sites)
    finds = differentials(_repro_fold_argument(), warm=False)
    twins = [f for f in finds if f.signature == ("call", "twin")]
    assert len(twins) == 2 and not [f for f in twins if f.known], finds
    assert [f for f in finds if f.known == "#1525"], finds


def test_a_find_the_counterfactual_makes_again_in_a_known_class_stays_a_find(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """A find the counterfactual makes again, now inside a known class, has
    not vanished: the class holds its site in the counterfactual, not in the
    program, so it stays a find."""
    real = load_finds

    def reclassified(program: Source, calls: Sequence[tuple[str, Sequence[int] | None]],
                     stages: Stages | None = None) -> list[Find]:
        bound = isinstance(program, gen.Program) and "{ let @" in program.render()
        return real(program, calls, stages) + [
            Find("load", ("call", "again"), "a find", function="f9",
                 known="#1695" if bound else "")]

    monkeypatch.setattr(sys.modules[__name__], "load_finds", reclassified)
    finds = differentials(_repro_fold_argument(), warm=False)
    again = [f for f in finds if f.signature == ("call", "again")]
    assert [f.known for f in again] == [""], finds
    assert [f for f in finds if f.known == "#1525"], finds


def test_a_counterfactual_that_does_not_check_classifies_nothing(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """A counterfactual `vera check` refuses makes no find of the load,
    reconcile or distrust differential at all, which is no evidence: the
    program's finds stay finds."""
    def refused(prog: gen.Program, kinds: object) -> gen.Program:
        out = copy.deepcopy(prog)
        out.functions[-1].contract = ["requires(true)", "ensures(@Bool.result)"]
        return out

    monkeypatch.setattr(gen, "bind_in_place", refused)
    finds = differentials(_repro_fold_argument(), warm=False)
    codegen = [f for f in finds if f.differential in _CODEGEN]
    assert codegen and not [f for f in codegen if f.known], finds


def _opaque_narrowing(how: str) -> gen.Program:
    """`let @Int = value; let @Nat = @Int.0;`, *value* a `match` taking 1 in
    each arm whose scrutinee is a constructor applied in place or
    `map_get`'s result, or a call whose `ensures` states 2 or 0 taking a
    generic's call at a data type, the module's constructor, or a data slot
    bound to a `match` on `map_get`.  The entry's own data type is `Shade`,
    not the module's `Tally`, so each case meets its own rule."""
    amber, basalt = gen.Ctor("Amber", "Shade", ["Bool"]), gen.Ctor("Basalt", "Shade", [])
    datas = [gen.Data("Shade", False, [amber, basalt])]
    functions: list[gen.Function] = []
    lets: list[gen.Let] = []
    module: gen.Module | None = None
    if how == "imported":
        amber = gen.Ctor("Amber", gen.TALLY, ["Nat"])
        module = gen.Module([gen.Data(gen.TALLY, True, [amber, gen.Ctor("Basalt", gen.TALLY, [])],
                                      module=True)], [])
        datas = []
        zero = gen.Function("f1", False, [gen.Binding(gen.TALLY)], "Nat",
                            gen.Block([], gen.Lit(0)), ensure_style="upper")
        functions = [zero]
        value: gen.Expr = gen.Call(zero, [gen.Construct(amber, [gen.Lit(0)])])
    elif how == "match":
        value = gen.Match(gen.Construct(basalt, []), [
            gen.Arm(gen.Pattern(ctor=amber, binders=[gen.Binding("Bool")]), gen.Lit(1)),
            gen.Arm(gen.Pattern(ctor=basalt), gen.Lit(1))])
    elif how == "data_let":
        table = gen.Binding("Map<String, Int>", value=gen.MapBuild([("a", gen.Lit(1))]))
        shade = gen.Binding("Shade", value=gen.Match(gen.MapGet(gen.Ref(table), "a"), [
            gen.Arm(gen.Pattern(ctor=gen.SOME, binders=[gen.Binding("Int", gen.ANY, gen.Iv(1, 1))]),
                    gen.Construct(basalt, [])),
            gen.Arm(gen.Pattern(ctor=gen.NONE), gen.Construct(amber, [gen.Lit(True)]))]))
        two = gen.Function("f1", False, [gen.Binding("Shade")], "Int",
                           gen.Block([], gen.Lit(2)), ensure_style="exact")
        functions, lets = [two], [gen.Let(table), gen.Let(shade)]
        value = gen.Call(two, [gen.Ref(shade)])
    elif how == "map_get":
        table = gen.Binding("Map<String, Int>", value=gen.MapBuild([("a", gen.Lit(1))]))
        lets = [gen.Let(table)]
        value = gen.Match(gen.MapGet(gen.Ref(table), "a"), [
            gen.Arm(gen.Pattern(ctor=gen.SOME, binders=[gen.Binding("Int", gen.ANY, gen.Iv(1, 1))]),
                    gen.Lit(1)),
            gen.Arm(gen.Pattern(ctor=gen.NONE), gen.Lit(1))])
    else:
        pick = _pick()
        two = gen.Function("f1", False, [gen.Binding("Shade")], "Int",
                           gen.Block([], gen.Lit(2)), ensure_style="exact")
        functions = [pick, two]
        value = gen.Call(two, [gen.Call(pick, [gen.Lit(True), gen.Construct(basalt, []),
                                               gen.Construct(basalt, [])], {"T": "Shade"})])
    i = gen.Binding("Int", value=value)
    n = gen.Binding("Nat", value=gen.Ref(i))
    prog = _one(gen.Ref(n), lets=[*lets, gen.Let(i), gen.Let(n)], ret="Nat",
                functions=functions, datas=datas)
    prog.module = module
    return prog


@pytest.mark.parametrize("how", ["match", "map_get", "call", "imported", "data_let"])
def test_the_model_reads_no_value_the_verifier_does_not_translate(
        how: str, tmp_path: Path) -> None:
    """A `match` on a constructor applied in place or on `map_get`'s
    result, a call taking a generic's call at a data type, a call taking a
    constructor of the module's data type, and a call taking a data slot
    bound to a `match` on `map_get` are values the verifier does not
    translate (#1696; #1525 for the module's constructor): a `let` of one
    is unconstrained, and narrowing it into a `@Nat` is refused (E503),
    though it is 0, 1 or 2 on every run.  The generator models
    each as unconstrained, so it writes no such narrowing: the program is
    not one it could have written."""
    prog = _opaque_narrowing(how)
    finds = contract_finds(prog, Stages.of(prog, tmp_path))
    assert [f.signature for f in finds] == [("verify", "E503")], finds
    assert not gen.well_formed(prog)
    let = prog.functions[-1].body.lets[-2].binding
    assert let.value is not None
    assert gen.iv(gen.Ref(let), "v") == gen.ANY
    assert gen.iv(let.value, "r").within(0, 2)


def test_a_verify_error_is_keyed_without_its_counterexample() -> None:
    """A counterfactual's `let`s renumber the solver's fresh values, so a
    verify error that survives it can come back with another model: its key
    drops the model, and keeps the error's source line and column, which
    two errors of one line differ in."""
    a = Diagnostic(description="E503 thing.\n  Counterexample:\n      _x_1 = 0",
                   location=SourceLocation(file=LABEL, line=4, column=14),
                   source_line="  let @Nat = @Int.0;", error_code="E503")
    moved = replace(a, description="E503 thing.\n  Counterexample:\n      _x_3 = -1",
                    location=SourceLocation(file=LABEL, line=6, column=14))
    beside = replace(a, location=SourceLocation(file=LABEL, line=4, column=20))
    assert _verify_key("", a) == _verify_key("", moved)
    assert _verify_key("", a) != _verify_key("", beside)
    assert "Counterexample" not in _verify_key("", a)


def test_a_measure_that_does_not_decrease_is_not_well_formed() -> None:
    """A recursive call that passes its measure unchanged is a program the
    generator never writes: the minimiser refuses it, and only the measure
    less one is a recursive call's argument."""
    good = _measured(None)
    assert gen.well_formed(good)
    m = good.functions[0].measure
    assert m is not None
    assert not gen.well_formed(_measured(gen.Ref(m)))


def test_an_instantiation_its_constraint_refuses_is_not_well_formed() -> None:
    """`least` under `Ord<T>` is called at an orderable type only, with
    arguments of that type exactly: at `Bool` (#1679's shape, refused by
    code generation alone) the minimiser refuses the candidate."""
    x, y = gen.Binding("T"), gen.Binding("T")
    least = gen.Function(
        "f0", False, [x, y], "T", gen.Block([], gen.Builtin(
            "compare", [gen.Ref(x), gen.Ref(y)], "Ordering")), kind="generic",
        forall=["T"], constraints=["Ord<T>"], template="least",
        contract=["requires(true)", "ensures(true)"])

    def caller(t: str) -> gen.Program:
        bounds = gen.Iv(0, 5) if t in gen.NUMERIC else None
        a, b = gen.Binding(t, bounds, bounds), gen.Binding(t, bounds, bounds)
        call = gen.Call(least, [gen.Ref(a), gen.Ref(b)], {"T": t})
        fn = gen.Function("f1", False, [a, b], "Bool", gen.Block(
            [gen.Let(gen.Binding(t, value=call))], gen.Lit(True)), ensure_style="none")
        return gen.Program(0, [], [least, fn], [])

    assert gen.well_formed(caller("Int"))
    assert not gen.well_formed(caller("Bool"))


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


_TWO_HANDLERS = """\
public fn one_cell(@Bool -> @Int)
  requires(true)
  ensures(@Int.result >= 3 && @Int.result <= 4)
  effects(pure)
{
  if @Bool.0 then {
    handle[State<Int>](@Int = 0) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      put(3);
      get(())
    }
  } else {
    handle[State<Int>](@Int = -2) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      put(4);
      get(())
    }
  }
}
"""


def test_the_load_differential_reports_a_module_that_does_not_load() -> None:
    """An `if` whose arms are each a handler compiles, with no diagnostic,
    to a module wasmtime refuses (#1744's handler block): the load
    differential reports it, once, rather than crash on it.  With the
    handler bound by a `let` in one arm, the module loads and runs."""
    calls = (("one_cell", (1,)),)
    finds = load_finds(_TWO_HANDLERS, calls)
    assert [f.signature for f in finds] == [("module", "invalid")], finds
    assert "values remaining on stack" in finds[0].detail, finds[0].detail
    neighbour = """\
public fn one_cell(@Bool -> @Int)
  requires(true)
  ensures(@Int.result >= 3 && @Int.result <= 4)
  effects(pure)
{
  let @Int = handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(3);
    get(())
  };
  if @Bool.0 then {
    @Int.0
  } else {
    handle[State<Int>](@Int = -2) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      put(4);
      get(())
    }
  }
}
"""
    assert neighbour != _TWO_HANDLERS
    assert not contract_finds(neighbour), contract_finds(neighbour)
    assert load_finds(neighbour, calls) == []


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
    # The neighbour keeps its contract, so the join runs over it and
    # reports nothing because nothing is there.
    neighbour = _REPRO_1629_DIVISOR.replace(
        "@Int.result <= 2", "@Int.result <= 100").replace("@Int.0 % 3", "@Int.0")
    assert not contract_finds(neighbour), contract_finds(neighbour)
    assert reconcile_finds(neighbour, known=()) == []


@pytest.mark.parametrize(
    "cls", KNOWN_CLASSES, ids=lambda c: f"{c.issue} {c.obligation}")
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


#: Members of the `nat_bind` class beside its repro, a call (#1557), each a
#: value the declarations make non-negative at a `@Nat` position: a refined
#: slot, a `Nat` field's binder and a generic one's at `Nat`, a `State<Nat>`
#: read and its handler, an element of a `Nat` array.  And outside it, #1756's shape:
#: a join of an `@Int` branch with a `@Nat` one, which the checker typed
#: `@Nat` and whose guard is the only check of the `@Int` branch.
_NAT_GUARD_MEMBERS = {
    "a refined slot": """\
type Low = { @Nat | @Nat.0 <= 6 };

public fn bump(@Low -> @Nat)
  requires(true)
  ensures(@Nat.result <= 7)
  effects(pure)
{
  @Low.0 + 1
}
""",
    "a field's binder": """\
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
""",
    "an element's binder": """\
public fn c(@Nat -> @Nat)
  requires(@Nat.0 <= 9)
  ensures(true)
  effects(pure)
{
  let @Array<Option<Nat>> = [Some(@Nat.0), None];
  if 0 < array_length(@Array<Option<Nat>>.0) then {
    match @Array<Option<Nat>>.0[0] {
      Some(@Nat) -> @Nat.0,
      None -> 0
    }
  } else {
    0
  }
}
""",
    "a cell's handler": """\
public fn h(@Nat -> @Nat)
  requires(@Nat.0 <= 5)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 1) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    put(@Nat.0 + 2);
    get(())
  }
}
""",
    "a fold from a Nat": """\
public fn folded(@Nat -> @Nat)
  requires(@Nat.0 <= 3)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [1, 2];
  let @Nat = array_fold(@Array<Int>.0, @Nat.0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + 1 });
  @Nat.0
}
""",
    "an element of a Nat array": """\
public fn elem(@Nat -> @Int)
  requires(@Nat.0 <= 5)
  ensures(true)
  effects(pure)
{
  let @Array<Nat> = [@Nat.0, 2];
  if 1 < array_length(@Array<Nat>.0) then {
    nat_to_int(@Array<Nat>.0[1])
  } else {
    0
  }
}
""",
}

@pytest.mark.parametrize("member", sorted(_NAT_GUARD_MEMBERS))
def test_the_nat_guard_class_reads_its_mechanism(member: str) -> None:
    """Each member reports one `nat_bind` mismatch, and the class holds it:
    the predicate reads the mechanism, a value the declarations make
    non-negative and code generation's declared-name rule does not, from
    the program as written."""
    source = _NAT_GUARD_MEMBERS[member]
    assert not contract_finds(source), contract_finds(source)
    finds = reconcile_finds(source)
    nat = [f for f in finds if f.signature[1] == "nat_bind"]
    assert [f.known for f in nat] == ["#1695"], finds
    assert all(f.known for f in finds), finds


#: Members of the class of a refinement check on a value the declarations
#: already give the refinement, beside its repro, a refined parameter.
_HELD_MEMBERS = {
    "a let of a refined slot": """\
type Span = { @Int | @Int.0 >= -10 && @Int.0 <= -7 };

public fn held(@Int -> @Int)
  requires(@Int.0 >= -9 && @Int.0 <= -8)
  ensures(true)
  effects(pure)
{
  let @Span = @Int.0;
  let @Span = @Span.0;
  0
}
""",
    "a join of refined slots": """\
type Span = { @Int | @Int.0 >= -10 && @Int.0 <= -7 };

public fn joined(@Bool, @Int -> @Int)
  requires(@Int.0 >= -9 && @Int.0 <= -8)
  ensures(true)
  effects(pure)
{
  let @Span = @Int.0;
  let @Span = if @Bool.0 then {
    @Span.0
  } else {
    @Span.0
  };
  0
}
""",
}


@pytest.mark.parametrize("member", sorted(_HELD_MEMBERS))
def test_the_held_refinement_class_reads_its_mechanism(member: str) -> None:
    """Each member reports one `refine_bind` mismatch, which the class holds:
    a `let` of a refined type whose value's every arm is a slot of that type
    is checked by code generation and recorded by no one."""
    source = _HELD_MEMBERS[member]
    assert not contract_finds(source), contract_finds(source)
    finds = reconcile_finds(source)
    refine = [f for f in finds if f.signature[1] == "refine_bind"]
    assert [f.known for f in refine] == ["#1695 (#1629)"], finds
    assert all(f.known for f in finds), finds


#: Values at `@Nat` positions the class must and must not hold: the
#: declarations make each of the first non-negative, and none of the second
#: (an `@Int` slot, a negated literal: #1756's shape, which the checker's
#: join now types `@Int`, so the join reports nothing there at base).
_NAT_GUARD_SITES = """\
type Low = { @Nat | @Nat.0 <= 6 };

public fn sites(@Low, @Int, @Nat -> @Int)
  requires(@Int.0 >= 1 && @Int.0 <= 5 && @Nat.0 <= 5)
  ensures(true)
  effects(pure)
{
  let @Int = @Low.0 + 1;
  let @Int = @Int.0 - 3;
  let @Int = -1 * -3;
  let @Int = @Nat.0 + 1;
  0
}
"""


def _site_of(source: str, text: str) -> tuple[int, int]:
    """Where *text* starts in *source*, one-based."""
    for n, line in enumerate(source.splitlines(), start=1):
        column = line.find(text)
        if column >= 0:
            return n, column + 1
    raise AssertionError(text)


@pytest.mark.parametrize("value,held", [
    ("@Low.0 + 1", True), ("@Int.0 - 3", False), ("-1 * -3", False),
    ("@Nat.0 + 1", False)])
def test_the_nat_guard_class_holds_no_other_nat_bind(value: str, held: bool) -> None:
    """The class's predicate over a `nat_bind` guard at each value: a refined
    slot's arithmetic is the declarations' `@Nat` that code generation's
    declared-name rule misses; an `@Int` slot and a negated literal are no
    `@Nat` by the declarations, so a guard there stays a find; and
    `@Nat.0 + 1` code generation's rule reads as a `@Nat` itself, so a guard
    there is not this mechanism either."""
    checked = pipeline.check(_NAT_GUARD_SITES, file=LABEL)
    assert not checked.diagnostics, checked.diagnostics
    line, column = _site_of(_NAT_GUARD_SITES, value)
    cls = next(k for k in KNOWN_CLASSES if k.shape == _NAT_GUARD_SHAPE)
    mismatch = Mismatch("guarded_unrecorded", "nat_bind", LABEL, line, column,
                        "sites", emitter=cls.emitter)
    assert cls.holds(mismatch, Sites(checked)) is held


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
    assert pipeline.verify(neighbour, file=LABEL).ok
    stats: dict[str, int] = {}
    assert distrust_finds(neighbour, stats=stats) == []
    assert stats["proofs_exercised"] == 1, stats


def _lost_postcondition(lowest: int) -> gen.Program:
    """`f2` binds `f0(Bravo(@Int.0))`, whose `ensures` says it is 4, and
    passes it to `f1`, which requires 1 to 9; `f2` names no `Gauge`, so the
    verifier loses `f0`'s postcondition and refuses the call (#1525's
    constructed-sort line).  With *lowest* below 1,
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


def test_the_counterfactual_keys_a_lost_postcondition_to_1525(tmp_path: Path) -> None:
    """The refusal vanishes when `f2` first binds an unused `let @Gauge`, so
    it is #1525's, the record says why, and the differentials run over the
    counterfactual program, which verifies clean."""
    prog = _lost_postcondition(1)
    finds = contract_finds(prog.render())
    assert [f.signature for f in finds] == [("verify", "E501")], finds
    stats: dict[str, int] = {}
    classified = differentials(prog, tmp_path, stats=stats)
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


def test_a_refusal_the_counterfactual_does_not_remove_stays_a_find(
        tmp_path: Path) -> None:
    """`f2`'s own parameter may be 0, which `f1` refuses whatever `f2`
    names: the refusal survives the counterfactual, and is a find."""
    finds = differentials(_lost_postcondition(0), tmp_path)
    assert [(f.differential, f.signature, f.known) for f in finds] == [
        ("contract", ("verify", "E501"), CONSTRUCTED_SORT_ISSUE),
        ("contract", ("verify", "E501"), "")], finds
    assert "survived the counterfactual" in finds[1].evidence


def test_a_refutation_names_its_function_and_arguments() -> None:
    """#1555's refuted proof over a parameter the precondition pins: the
    find names the function and the arguments it was refuted on, which the
    record hands `program_generator.expectations`.  The diagnostic alone
    names neither."""
    pinned = _FALSE_PROOF.replace(
        "public fn main(-> @Int)\n  requires(true)",
        "public fn main(@Nat -> @Int)\n  requires(@Nat.0 == 3)")
    assert pinned != _FALSE_PROOF
    finds = distrust_finds(pinned)
    assert [(f.signature[0], f.function, f.args) for f in finds] == [
        ("E703", "main", (3,))], finds
    assert finds[0].to_dict()["args"] == [3]


def test_the_minimiser_never_accepts_the_program_it_holds() -> None:
    """A candidate that renders as the program the minimiser holds is no
    step.  A nullary constructor, or a construction of a type's fewest-field
    constructor at its stand-in values, is its own stand-in; accepting it
    restarted the reductions, which tried again every candidate refused
    before it and reached none after it, until the budget was spent."""
    def constructs(prog: gen.Program) -> bool:
        return any(isinstance(node, gen.Construct)
                   for fn in gen.all_functions(prog) for node in gen.nodes(fn))

    prog = next(p for p in map(gen.generate, range(2000, 2100)) if constructs(p))
    replaced = [gen._text(prog)]
    steps: list[tuple[str, str]] = []

    def holds(candidate: gen.Program) -> bool:
        if not constructs(candidate):
            return False
        steps.append((replaced[0], gen._text(candidate)))
        replaced[0] = gen._text(candidate)
        return True

    minimal = gen.minimize(prog, holds, budget=MINIMISE_BUDGET)
    assert steps, "the minimiser accepted nothing"
    identical = [n for n, (before, after) in enumerate(steps) if before == after]
    assert not identical, f"{len(identical)} of {len(steps)} steps kept the program"
    assert constructs(minimal)


def test_the_minimiser_keeps_the_failure_it_shrinks(tmp_path: Path) -> None:
    """The smallest of the first hundred single-file programs that divides
    by a literal is shrunk to the smallest program whose join still reports
    the divisor class, keeping the generator's contract: a reduction that
    lost the find or broke the program would have been refused."""
    candidates = sorted(
        (gen.size(p), p.seed) for p in map(gen.generate, range(100))
        if p.module is None and p.shape()["/lit"] + p.shape()["%lit"])
    assert candidates, "no seed below 100 divides by a literal"
    prog = gen.generate(candidates[0][1])
    finds = [f for f in reconcile_finds(prog.render())
             if f.known == "#1695 (#1629)" and f.signature[1] == "div_zero"]
    assert finds, prog.render()
    holds = still_fails(finds[0], tmp_path)
    minimal = gen.minimize(prog, holds, budget=MINIMISE_BUDGET)
    assert holds(minimal)
    assert gen.well_formed(minimal)
    assert gen.size(minimal) < gen.size(prog), minimal.render()
    assert len(minimal.functions) == 1, minimal.render()


def _keeping(name: str) -> Callable[[gen.Program], bool]:
    """A predicate that holds while a function named *name* remains."""
    return lambda candidate: any(f.name == name for f in candidate.functions)


def _has(prog: gen.Program, name: str, test: Callable[[object], bool]) -> bool:
    fn = next(f for f in prog.functions if f.name == name)
    return any(test(node) for f in [fn, *fn.helpers] for node in gen.nodes(f))


@pytest.mark.parametrize("construct", ["handler", "recursive call", "import"])
def test_the_minimiser_drops_what_a_find_does_not_need(construct: str) -> None:
    """Under a predicate that holds while one function remains, the
    minimiser drops a handler from that function, its recursive call, or
    the module it imports from, each candidate one the generator could have
    written."""
    if construct == "handler":
        def test(node: object) -> bool:
            return isinstance(node, gen.Handle)
    elif construct == "recursive call":
        def test(node: object) -> bool:
            return isinstance(node, gen.Call) and node.fn.group is not None
    else:
        def test(node: object) -> bool:
            return isinstance(node, gen.Call) and node.fn.module
    prog, name = next(
        (p, f.name) for p in map(gen.generate, range(200)) for f in p.functions
        if _has(p, f.name, test) and (construct != "recursive call" or f.group))
    minimal = gen.minimize(prog, _keeping(name), budget=MINIMISE_BUDGET)
    assert gen.well_formed(minimal)
    assert not _has(minimal, name, test), gen._text(minimal)
    if construct == "import":
        assert minimal.module is None, gen._text(minimal)


def _difference() -> gen.Program:
    """`f0(@Int, @Int -> @Int)`, its first parameter minus its second, with
    that exact `ensures`: written with two slots of one type swapped, the
    run returns the negation, while `vera check` and the verifier read the
    body and the `ensures` swapped alike."""
    bounds = gen.Iv(0, 10)
    first = gen.Binding("Int", bounds, bounds)
    second = gen.Binding("Int", bounds, bounds)
    fn = gen.Function(
        "f0", True, [first, second], "Int",
        gen.Block([], gen.Bin("-", gen.Ref(first), gen.Ref(second))),
        ensure_style="exact", example=[7, 2])
    return gen.Program(0, [], [fn], [fn])


def test_the_record_states_what_the_generator_expected() -> None:
    """A find's record carries each function's contract as written, its
    intervals, and the value an exact `ensures` states on the failing
    arguments, so a generator bug is told from a toolchain find by reading
    the record.  The value is the generator's own evaluation, held to a run
    of the compiled function: over the first public straight-line function
    and the first public linear recursion of the first hundred single-file
    programs, and over `_difference`, whose value its parameters' order
    decides, the one place two swapped slots show."""
    def first(test: Callable[[gen.Function], bool]) -> tuple[gen.Program, gen.Function]:
        return next(
            (p, f) for p in map(gen.generate, range(100)) if p.module is None
            for f in p.functions if f.public and gen.ensure_style(f) == "exact"
            and f.params and test(f))

    straight = first(lambda f: f.template != "linear")
    linear = first(lambda f: f.template == "linear")
    difference = _difference()
    for prog, fn in (straight, linear, (difference, difference.functions[0])):
        args = [int(a) for a in fn.example]
        entry = next(e for e in gen.expectations(prog, fn.name, args)
                     if e["function"] == fn.name)
        ran = pipeline.run(prog.render(), fn=fn.name, args=args)
        assert ran.ok, ran.trap
        assert entry["expected"] == ran.value, (entry, prog.render())
        assert entry["style"] == "exact"
        assert entry["ensures"] and entry["requires"]
    assert gen.evaluate(difference.functions[0], [7, 2]) == 5


def test_the_report_counts_each_known_class_with_its_seeds(tmp_path: Path) -> None:
    """The night's report gives each known class a row, by its issue and
    its shape: how many finds it counted, in how many programs, and the
    first seeds, so an absorption is read from the report alone; two
    classes of one issue keep two rows."""
    def known(issue: str, cls: str) -> dict[str, object]:
        return Find("reconcile", ("x",), "d", known=issue, cls=cls).to_dict()

    (tmp_path / "records").mkdir()
    for seed, finds in ((7, [known("#1695", "a"), known("#1695", "a")]),
                        (9, [known("#1695", "b")]),
                        *((s, [known("#1525", "c")]) for s in range(20, 27))):
        record = {"seed": seed, "shape": {}, "stats": {}, "finds": finds, "seconds": 1.0}
        (tmp_path / "records" / f"seed-{seed}.json").write_text(
            json.dumps(record), encoding="utf-8")
    report = gen.summarize(tmp_path)
    assert "| #1695 | a | 2 | 1 | 7 |" in report, report
    assert "| #1695 | b | 1 | 1 | 9 |" in report, report
    assert "| #1525 | c | 7 | 7 | 20, 21, 22, 23, 24 and 2 more |" in report, report


# =====================================================================
# Version two: the grammar's new constructs
# =====================================================================

#: What version two adds to version one's grammar, as `shape` counts it.
VERSION_TWO = (
    "fn_recursive", "decreases_nat", "decreases_data", "mutual_where",
    "fn_generic", "forall_ord", "forall_eq", "data_generic", "data_recursive",
    "alias_head", "alias_argument", "alias_refined", "refined_param",
    "refined_let", "module", "import_fn", "import_data", "array_int",
    "array_option_nat", "array_data", "map_string_int", "set_nat", "tuple",
    "array_length", "index_guarded", "array_fold", "map_get_match",
    "handle_state_int", "handle_state_nat", "handle_exn", "throw",
    "state_helper", "exn_helper", "noncommutative",
)


def test_the_seeds_reach_every_construct_of_version_two() -> None:
    """Over a hundred seeds the generator writes every construct version two
    adds: recursion with its measures, generics and their constraints,
    aliases, a module and its imports, the containers and their readers, the
    `State` and `Exn` handlers, and the non-commutative forms."""
    reached: dict[str, int] = {}
    for seed in range(100):
        for name, count in gen.generate(seed).shape().items():
            reached[name] = reached.get(name, 0) + count
    missing = [name for name in VERSION_TWO if not reached.get(name)]
    assert not missing, (missing, reached)


def test_the_pinned_seeds_reach_every_construct() -> None:
    """The pull request's ten seeds write every construct of the grammar,
    version two's among them: a change that breaks one fails on a pull
    request, not only at night."""
    totals: dict[str, int] = {}
    for seed in SEEDS:
        for name, count in gen.generate(seed).shape().items():
            totals[name] = totals.get(name, 0) + count
    missing = [name for name in gen.CONSTRUCTS if not totals.get(name)]
    assert not missing, (missing, totals)


@pytest.mark.parametrize(("issue", "seed"), PINNED_CLASSES)
def test_the_pinned_seeds_meet_each_counterfactual_class(
        issue: str, seed: int, tmp_path: Path) -> None:
    """A pinned seed makes a find of each counterfactual class, so a pull
    request runs the classification over a program the generator wrote, not
    over the hand-written repros alone."""
    finds = differentials(gen.generate(seed), tmp_path)
    assert [f for f in finds if f.known == issue], finds
    assert [f for f in finds if not f.known] == [], finds


def test_every_effect_helper_is_called_under_a_handler() -> None:
    """A `State` or `Exn` helper is written only where a handler of its cell
    calls it, so a run puts or throws inside a callee under its caller's
    handler, and a generic only where a call instantiates it, over three
    hundred programs (seeds 223 and 224 once kept a helper only a dropped
    helper called); the census counts a helper by its call, so a program
    that declares one and calls none reaches no helper construct."""
    called = 0
    for seed in range(300):
        prog = gen.generate(seed)
        targets = {id(node.fn) for f in gen.all_functions(prog)
                   for node in gen._walk(f.body) if isinstance(node, gen.Call)}
        written = [f for f in prog.functions if f.kind in ("state", "exn") or f.forall]
        assert all(id(f) in targets for f in written), (seed, [f.name for f in written])
        called += sum(1 for f in written if f.kind in ("state", "exn"))
    assert called, "no helper in a hundred programs"
    cell = gen.Binding("Int", gen.Iv(0, 5), gen.Iv(0, 5))
    writer = gen.Function("f0", False, [cell], "Unit", gen.Block(
        [], gen.Put("Int", gen.Ref(cell))), kind="state", effects="<State<Int>>")
    alone = _one(gen.Lit(1), functions=[writer])
    assert alone.shape()["state_helper"] == 0
    under = _one(gen.Handle("State", "Int", gen.Lit(0), gen.Block(
        [gen.Do(gen.Call(writer, [gen.Lit(3)]))], gen.Get("Int"))), functions=[writer])
    assert under.shape()["state_helper"] == 1


def test_a_module_is_written_beside_its_entry_and_imported() -> None:
    """A program with a module is two files: the entry imports the module by
    a selective list, each name in the list is a public declaration of the
    module, and the entry uses each one."""
    with_module = [p for p in map(gen.generate, range(100))
                   if p.module is not None]
    assert with_module, "no seed below 100 writes a module"
    for prog in with_module:
        files = prog.files()
        assert set(files) == {gen.ENTRY, gen.MODULE_FILE}, prog.seed
        entry, module = files[gen.ENTRY], files[gen.MODULE_FILE]
        imports = [line for line in entry.splitlines()
                   if line.startswith("import ")]
        assert len(imports) == 1, (prog.seed, imports)
        listed = re.fullmatch(r"import gen_lib\((.+)\);", imports[0])
        assert listed is not None, imports[0]
        rest = entry.split(imports[0], 1)[1]
        assert prog.module is not None
        for name in listed.group(1).split(", "):
            assert re.search(rf"^public (fn|data) {name}\b", module,
                             re.MULTILINE), (prog.seed, name)
            # A data type is used by its name or by one of its constructors,
            # which importing the type brings in.
            spellings = [name] + [c.name for d in prog.module.datas
                                  if d.name == name for c in d.ctors]
            assert any(re.search(rf"\b{w}\b", rest) for w in spellings), (
                prog.seed, name)


def test_a_program_with_a_module_checks_clean(tmp_path: Path) -> None:
    """The entry and its module, written to one directory and checked by the
    entry's path as `vera check` resolves them, report no diagnostic, and
    each file is in `vera fmt`'s canonical form: the first of a hundred
    programs that imports the data type and two functions, so an import the
    writer leaves out is a name the entry cannot resolve."""
    def imports_enough(p: gen.Program) -> bool:
        names = gen.imports(p)
        return gen.TALLY in names and len(names) >= 3

    prog = next(p for p in map(gen.generate, range(100)) if imports_enough(p))
    entry = pipeline.write_tree(tmp_path, prog.files(), entry=gen.ENTRY)
    checked = pipeline.check(entry)
    assert not checked.diagnostics, "\n".join(
        d.format() for d in checked.diagnostics)
    for name, text in prog.files().items():
        assert format_source(text, file=name) == text, name


def test_the_contract_verifies_the_module_on_its_own(tmp_path: Path) -> None:
    """A module whose own function breaks its `ensures` fails the contract
    though the entry verifies: the module is a program of its own, which
    `vera verify` is run on.  Its neighbour, the same module with the
    contract true, passes."""
    module = (
        "module gen_lib;\n\n"
        "public fn m0(@Int -> @Int)\n"
        "  requires(@Int.0 >= 0 && @Int.0 <= 9)\n"
        "  ensures(@Int.result >= 0)\n"
        "  effects(pure)\n"
        "{\n"
        "  @Int.0 - 10\n"
        "}\n")
    entry = (
        "import gen_lib(m0);\n\n"
        "public fn f0(@Int -> @Int)\n"
        "  requires(@Int.0 >= 0 && @Int.0 <= 9)\n"
        "  ensures(@Int.result >= 0)\n"
        "  effects(pure)\n"
        "{\n"
        "  m0(@Int.0)\n"
        "}\n")
    finds = contract_finds({LABEL: entry, gen.MODULE_FILE: module},
                           Stages.of({LABEL: entry, gen.MODULE_FILE: module}, tmp_path))
    assert [(f.signature, f.detail.split(":")[0]) for f in finds] == [
        (("verify", "E500"), gen.MODULE_FILE)], finds
    kept = module.replace("@Int.0 - 10", "@Int.0 + 10")
    assert contract_finds({LABEL: entry, gen.MODULE_FILE: kept},
                          Stages.of({LABEL: entry, gen.MODULE_FILE: kept}, tmp_path)) == []


def _rewritten_status(result: object, nth: int) -> object:
    """*result* with its *nth* obligation's status turned: a warm session
    that replays a stale verdict, built by hand."""
    obligations = list(result.obligations)  # type: ignore[attr-defined]
    ob = obligations[nth]
    flipped = "tier3" if ob.status == "verified" else "verified"
    obligations[nth] = replace(ob, status=flipped)
    return replace(result, obligations=obligations)  # type: ignore[type-var]


def test_the_warm_differential_reports_a_status_disagreement(
        tmp_path: Path) -> None:
    """A warm session whose answer to one edit differs from a fresh session's
    in one obligation's status is the find, and it names the edit, the
    obligation and the two statuses; the real warm session over the same
    edits reports nothing, having replayed at least one function."""
    prog = gen.generate(SEEDS[0])
    edits = gen.edits(prog)
    assert len(edits) >= 3, edits

    class Stale(VerificationSession):
        calls = 0

        def verify_source(self, *args: object, **kwargs: object) -> object:
            out = super().verify_source(*args, **kwargs)  # type: ignore[arg-type]
            Stale.calls += 1
            return _rewritten_status(out, 0) if Stale.calls == 2 else out

    finds = [f for f in warm_finds(prog, tmp_path / "stale", warm=Stale, edits=edits)  # type: ignore[arg-type]
             if not f.known]
    assert [f.signature[:2] for f in finds] == [("obligations", "status")], finds
    assert f"edit 1 ({edits[1].name})" in finds[0].detail, finds[0].detail
    assert " in the warm session and " in finds[0].detail, finds[0].detail
    stats: dict[str, int] = {}
    real = warm_finds(prog, tmp_path / "real", edits=edits, stats=stats)
    assert [f for f in real if not f.known] == [], real
    assert stats["warm_replayed_fns"] >= 1, stats


def test_the_warm_differential_reports_a_diagnostic_disagreement(
        tmp_path: Path) -> None:
    """A warm session whose answer to an edit drops a diagnostic a fresh
    session reports is the find, named by the edit; the edit that breaks a
    contract makes one to drop."""
    prog = next(p for p in map(gen.generate, range(50))
                if any(e.name.startswith("break") for e in gen.edits(p)))
    edits = gen.edits(prog)
    broken = next(n for n, e in enumerate(edits) if e.name.startswith("break"))

    class Forgetful(VerificationSession):
        calls = 0

        def verify_source(self, *args: object, **kwargs: object) -> object:
            out = super().verify_source(*args, **kwargs)  # type: ignore[arg-type]
            Forgetful.calls += 1
            if Forgetful.calls == broken + 1:
                return replace(out, verify_diagnostics=[])  # type: ignore[type-var]
            return out

    finds = [f for f in warm_finds(prog, tmp_path / "forgetful", warm=Forgetful,  # type: ignore[arg-type]
                                   edits=edits) if not f.known]
    assert [f.signature for f in finds] == [("diagnostics",)], finds
    assert f"edit {broken} ({edits[broken].name})" in finds[0].detail


def test_a_counterexample_that_differs_alone_is_counted_under_1785(
        tmp_path: Path) -> None:
    """A warm session whose answer to the edit that breaks a contract
    differs from a fresh session's in a counterexample's values alone makes
    a find of #1785's class, counted and failing nothing; no disagreement.
    The class has no pin: no seed shows it in a new process."""
    prog = next(p for p in map(gen.generate, range(50))
                if any(e.name.startswith("break") for e in gen.edits(p)))
    edits = gen.edits(prog)
    broken = next(n for n, e in enumerate(edits) if e.name.startswith("break"))
    marker = "\n  Counterexample:"

    class Remodelled(VerificationSession):
        calls = 0

        def verify_source(self, *args: object, **kwargs: object) -> object:
            out = super().verify_source(*args, **kwargs)  # type: ignore[arg-type]
            Remodelled.calls += 1
            if Remodelled.calls == broken + 1:
                assert out.verify_diagnostics
                return replace(out, verify_diagnostics=[  # type: ignore[type-var]
                    replace(d, description=d.description.split(marker)[0]
                            + marker + "\n        @Remodelled.0 = 1")
                    for d in out.verify_diagnostics])
            return out

    finds = warm_finds(prog, tmp_path / "remodelled", warm=Remodelled, edits=edits)  # type: ignore[arg-type]
    model = [f for f in finds if f.signature == ("diagnostics", "counterexample")]
    assert [(f.known, f.cls) for f in model] == [(WARM_MODEL_ISSUE, WARM_MODEL_SHAPE)], finds
    assert f"edit {broken} ({edits[broken].name})" in model[0].detail
    assert [f for f in finds if not f.known] == [], finds


def test_the_edits_keep_the_program_well_formed() -> None:
    """Every edit of the pinned seeds' sequences is a program the generator
    could have written, but the one that breaks a contract on purpose, and
    the sequence restores the contract it breaks."""
    kinds: set[str] = set()
    for seed in SEEDS:
        edits = gen.edits(gen.generate(seed))
        assert edits[0].name == "the program as written"
        for n, edit in enumerate(edits):
            kinds.add(edit.name.split(" ")[0])
            assert edit.name.startswith("break") or gen.well_formed(edit.program), (
                seed, edit.name)
            if edit.name.startswith("break"):
                assert n + 1 == len(edits) or edits[n + 1].name.startswith("restore"), (
                    seed, [e.name for e in edits])
    assert {"move", "add", "tighten", "break", "restore"} <= kinds, kinds


@pytest.mark.parametrize("change", ["the step moved", "the call alone", "the literal alone",
                                    "the call made a literal"])
def test_a_change_to_a_linear_recursions_step_keeps_its_ensures(change: str) -> None:
    """A linear recursion's exact `ensures` is its closed form, `base + m *
    k`, with `k` read off the `rec + k` its step adds, so a change to the
    step leaves no stale claim: the literal edit moving `k` by one, or the
    minimiser taking one of the step's operands for it or a literal for its
    recursive call (`_smaller`), makes a program that is well formed and
    verifies clean."""
    prog, fn = next((p, f) for p in map(gen.generate, range(100)) if p.module is None
                    for f in p.functions if f.template == "linear")
    prog = copy.deepcopy(prog)
    fn = next(f for f in prog.functions if f.name == fn.name)
    assert isinstance(fn.body.result, gen.If)
    branch = fn.body.result.other
    step = branch.result
    assert isinstance(step, gen.Bin) and isinstance(step.right, gen.Lit), prog.render()
    if change == "the step moved":
        step.right.value = int(step.right.value) + 1
    elif change == "the call alone":
        branch.result = step.left
    elif change == "the literal alone":
        branch.result = step.right
    else:
        step.left = gen.Lit(0)
    assert gen.well_formed(prog), prog.render()
    assert contract_finds(prog, Stages.of(prog)) == [], prog.render()


# =====================================================================
# The nightly lane
# =====================================================================

def test_the_workflow_keeps_what_it_claims() -> None:
    """`nightly-generator.yml` read as data, for the five things its header
    and the description claim: the tracking issue is filed on a failed
    scheduled night alone; the job holds `contents: read` and
    `issues: write` and nothing more; no context value is interpolated into
    a `run:` or the script; a pull request runs it only for the generator,
    its instrument and the workflow; and nothing is `continue-on-error`."""
    workflow = yaml.safe_load(
        (ROOT / ".github" / "workflows" / "nightly-generator.yml").read_text(
            encoding="utf-8"))
    # YAML 1.1 reads the `on` key as true.
    triggers = workflow.get("on", workflow.get(True))
    assert workflow["permissions"] == {"contents": "read"}
    [job] = workflow["jobs"].values()
    assert job["permissions"] == {"contents": "read", "issues": "write"}
    steps = job["steps"]
    issue = [s for s in steps if str(s.get("uses", "")).startswith(
        "actions/github-script@")]
    assert len(issue) == 1, issue
    assert issue[0]["if"] == "failure() && github.event_name == 'schedule'"
    for step in steps:
        for text in (step.get("run", ""), (step.get("with") or {}).get(
                "script", "")):
            assert "${{" not in str(text), step.get("name")
        assert "continue-on-error" not in step, step.get("name")
    assert "continue-on-error" not in job
    assert sorted(triggers["pull_request"]["paths"]) == sorted([
        "tests/program_generator.py", "tests/test_program_generator.py",
        ".github/workflows/nightly-generator.yml"])


def night_seeds(spec: str | None = None,
                today: datetime.date | None = None) -> list[int]:
    """The seeds ``VERA_GENERATOR_SEEDS`` names: nothing when it is unset,
    ``night:N`` for N seeds the UTC day determines, or a list of seeds and
    ranges (``12,40-49``) to rerun.  Anything else, a range that runs
    backwards and ``night:0`` among it, is a ``ValueError``, which fails
    the collection: a dispatch naming no seed would otherwise pass."""
    spec = os.environ.get("VERA_GENERATOR_SEEDS", "") if spec is None else spec
    spec = spec.strip()
    if not spec:
        return []
    night = re.fullmatch(r"night:(\d+)", spec)
    if night:
        count = int(night.group(1))
        if count == 0:
            raise ValueError("VERA_GENERATOR_SEEDS: night:0 names no seed")
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
        if high < low:
            raise ValueError(
                f"VERA_GENERATOR_SEEDS: {part.strip()!r} runs backwards and "
                f"names no seed")
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
    # A dispatch that names no seed would run the pull request's cells
    # alone and pass: a reversed range and a night of none are refused.
    with pytest.raises(ValueError):
        night_seeds("49-40")
    with pytest.raises(ValueError):
        night_seeds("night:0")


NIGHT_SEEDS = night_seeds()

if NIGHT_SEEDS:
    @pytest.mark.budget(900)
    @pytest.mark.parametrize("seed", NIGHT_SEEDS)
    def test_the_differentials_hold(seed: int, tmp_path: Path) -> None:
        """The contract and the four differentials over one of the night's
        programs (:func:`hold`)."""
        hold(seed, tmp_path)
