"""One derivation of WHERE code generation plants a guard.

Two rosters are read as claims about the backend: `carriers.ELEMENT_GUARD_SITES`
says which boundaries carry an element loop (#1430), and the boundary-guard
roster in `test_boundary_guard_correctness_1466.py` says which carry the tuple
decomposition (#1466).  A roster is only worth what holds it to the emitter,
so each is compared against the emitter's actual call sites — and that scan is
here, once, rather than once per roster.

The scan ENUMERATES the code-generation layer (`vera/codegen/*.py` and
`vera/wasm/*.py`) instead of reading a list of files.  The #1430 scan named
four files, so an emitter wired in a fifth was its blind spot: the comparison
would have kept agreeing while a whole position went unheld (observed in the
PR #1447 review at 65d90c4e, an observation rather than a finding because no
fifth file wired one at the time).  :data:`KNOWN_EMITTER_FILES` is asserted to
be a SUBSET of the enumeration rather than being the enumeration, so the two
packages remain the claim and the four files are a fact about today.

A call site is reported as ``enclosing_function/role``, because neither half
separates the four boundaries on its own: file granularity puts the parameter
loop and the return loop in different files from the positions they serve, and
function granularity collapses a closure's two boundaries onto one lifted-body
compiler (PR #1447 review, F3).  The role is the emitter's own argument — the
word its trap message prints — so the key is data the call site already
carries.
"""
from __future__ import annotations

import ast
import os
import re
from pathlib import Path

import vera

#: The packages whose modules may wire a guard emitter: the `CodeGenerator`
#: mixins and the `WasmContext` mixins.  Everything that emits WAT is one of
#: the two, which is what makes this an enumeration rather than a list.
EMITTER_PACKAGES = ("codegen", "wasm")

#: The files known to wire one today.  A FACT, asserted to lie inside the
#: enumeration above — never the source of it.
KNOWN_EMITTER_FILES = (
    "codegen/functions.py",
    "codegen/closures.py",
    "codegen/contracts.py",
    "wasm/calls_handlers.py",
)

#: The roles a guard emitter is called under, as literals at its call sites.
ROLE_PATTERN = r'"(parameter|return value)"'

_DEF = re.compile(r"    def (\w+)\(")


def codegen_sources() -> list[Path]:
    """Every module of the code-generation layer, enumerated."""
    root = Path(vera.__file__).resolve().parent
    found: list[Path] = []
    for package in EMITTER_PACKAGES:
        found.extend(sorted((root / package).glob("*.py")))
    return found


#: The WAT type names a heap-field layout table is keyed by.  A table that
#: mentions any of them and maps every key to a byte count IS one, whatever
#: it is called and however it is written.
_WAT_TYPE_KEYS = frozenset({"i32", "i64", "f64", "i32_pair", "unit"})

#: The one module allowed to state the layout.
LAYOUT_OWNER = "wasm/helpers.py"


def _is_layout_table(node: ast.AST) -> bool:
    """Whether *node* builds a heap-field size or alignment table.

    Read from the AST rather than from the source text, because a source
    pattern recognises one SPELLING of a table and a hand copy need not use
    it: single-quoted keys, `"unit"` written first, or `dict(i32=4, …)` are
    the same table and were invisible to the regex this replaces (CodeRabbit
    on PR #1478).  The shape is what identifies it — WAT type names mapped to
    byte counts — so a table keyed by VERA type names (`{"Int": 8, …}`, the
    array-element stride, where a `Bool` is one byte rather than four) is a
    different fact and is not reported, and neither is a dict whose values
    are anything but integers.
    """
    if isinstance(node, ast.Dict):
        keys, values = node.keys, node.values
        names = {
            k.value for k in keys
            if isinstance(k, ast.Constant) and isinstance(k.value, str)
        }
    elif (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "dict" and not node.args):
        names = {kw.arg for kw in node.keywords if kw.arg is not None}
        values = [kw.value for kw in node.keywords]
    else:
        return False
    if not names & _WAT_TYPE_KEYS:
        return False
    return bool(values) and all(
        isinstance(v, ast.Constant) and isinstance(v.value, int)
        and not isinstance(v.value, bool)
        for v in values
    )


def local_layout_tables() -> dict[str, list[str]]:
    """Every module of the code-generation layer that declares a heap-field
    size or alignment table of its own, as ``{module: ["line N: …"]}``.

    The layout is construction's contract with every reader of a constructed
    object — the destructure, the match extraction, the nested tag walk, the
    structural-eq field walk, the closure env block, the registered
    `ConstructorLayout`, and the boundary guard's tuple decomposition — and
    it was five hand copies that happened to agree.  Unifying them is worth
    exactly as much as the property that they STAY unified, so this reads the
    modules rather than trusting a comment: a sixth copy, under whatever name
    and in whatever spelling, is a row here.

    A TRIPWIRE, not the proof.  What proves the walks agree is widening the
    one table and watching every round trip follow
    (`tests/test_field_layout_one_source_1466.py`); this says no second table
    exists to diverge from it.  :data:`LAYOUT_OWNER` is excluded, being the
    one module the tables belong to.
    """
    found: dict[str, list[str]] = {}
    for path in codegen_sources():
        rel = str(path).split(f"{os.sep}vera{os.sep}")[-1].replace(os.sep, "/")
        if rel == LAYOUT_OWNER:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        hits = [
            f"line {node.lineno}: {ast.unparse(node)[:70]}"
            for node in ast.walk(tree) if _is_layout_table(node)
        ]
        if hits:
            found[rel] = hits
    return found


#: The emitters that take a guarded value's LOCAL as their second positional
#: argument.  Each one binds `@<base>.0` to whatever local it is handed, so
#: every one of them is a place the representation question is asked — and
#: each takes it at its OWN position, `_emit_refinement_check` fourth after
#: the context, the predicate and the base name, so the position and the
#: keyword are data here rather than an assumption that they agree.
#: `test_the_slot_binding_roster_matches_the_emitters` holds every entry to
#: the signature it names.
SLOT_BINDING_EMITTERS: dict[str, tuple[int, str]] = {
    "_emit_bind_refine_guard": (1, "value_local"),
    "_emit_refinement_check": (3, "value_local"),
    "_emit_clause_binder_guard": (1, "value_local"),
    "_emit_boundary_refinement_guard": (2, "value_local"),
    # Not a slot binding of its own: its `value_local` is the TUPLE's
    # pointer, and the guarded component's locals are derived inside it
    # through `bind_slot_value_from_field`.  Rostered anyway, because the
    # cell that holds this roster reads every signature carrying a
    # `value_local` and an unexplained absence is what let
    # `_emit_boundary_refinement_guard` sit outside it.
    "_emit_component_refinement_guards": (3, "value_local"),
}

#: The attribute a BOUND emitter is taken from before being called under a
#: local name — `emitter = self._refinement_guard_emitter`, then
#: `emitter(te, local, head, env)` (#1268).  That call is an `ast.Name`, so a
#: scan matching attribute calls alone sees nothing at the one position whose
#: emitter is INSTALLED rather than called by name, and that position binds a
#: pair (PR #1478 review, F11).  The local's name is derived per function
#: from this assignment rather than guessed.
BOUND_EMITTER_ATTRIBUTE = "_refinement_guard_emitter"

#: Where a bound emitter takes its value local: the callable is
#: `_emit_boundary_refinement_guard` with `ctx` already bound, so its third
#: parameter arrives second.
BOUND_EMITTER_POSITION = (1, "value_local")

#: How a guarded value's local may legitimately come to be, as
#: :func:`slot_binding_provenance` classifies it.
FROM_HELPER = "helper"
FROM_PARAMETER = "parameter"
FROM_ONE_LOCAL = "alloc_local(one word)"
FROM_COMPUTED_WIDTH = "alloc_local(computed width)"
FROM_WASM_PARAM = "alloc_param (the WASM signature)"
FROM_ADJACENT_PAIR = "alloc_local x2 (adjacency)"
FROM_UNKNOWN = "unknown"

_ONE_WORD = frozenset({"i32", "i64", "f64"})


class _Unpack:
    """`x, y = <expr>` — element *index* of whatever *value* holds.

    Not an AST node: a note to the classifier that the provenance continues
    one level down, which is how a local appended to a list and unpacked
    from it by a later `for` is followed to its allocation.
    """

    def __init__(self, value: ast.AST, index: int) -> None:
        self.value = value
        self.index = index


def _alloc_wt(node: ast.AST) -> str | None:
    """The width an `alloc_local(...)` call asks for, if *node* is one."""
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "alloc_local" and len(node.args) == 1
            and isinstance(node.args[0], ast.Constant)):
        value = node.args[0].value
        return value if isinstance(value, str) else None
    return None


def _resolve(
    value: object, assigned: dict[str, list[object]], depth: int = 0,
) -> list[object]:
    """Follow a name or an unpack to the expressions that can produce it."""
    if depth > 4:                       # pragma: no cover — cycle guard
        return [value]
    if isinstance(value, _Unpack):
        out: list[object] = []
        for inner in _resolve(value.value, assigned, depth + 1):
            if (isinstance(inner, (ast.Tuple, ast.List))
                    and value.index < len(inner.elts)):
                out.extend(_resolve(inner.elts[value.index], assigned,
                                    depth + 1))
            else:
                out.append(inner)
        return out or [value]
    if isinstance(value, ast.Name) and value.id in assigned:
        out = []
        for inner in assigned[value.id]:
            out.extend(_resolve(inner, assigned, depth + 1))
        return out or [value]
    return [value]


def _adjacent_pair_names(fn: ast.AST) -> set[str]:
    """Names assigned by an ``alloc_local("i32")`` with another one beside
    it — two halves of a hand-bound pair.

    Read from the BLOCK rather than from the enclosing function: counting
    `alloc_local("i32")` calls anywhere in a function that also spills a
    pair calls every i32 local in it an adjacent pair, which reported a
    finding for a site that has none.

    "Beside it" means no OTHER allocation lands between them, not that the
    two lines touch: a `msg = head` written in the middle separates nothing,
    and a window of exactly one statement let that hide a pair (PR #1478
    review, F11).  Both names are reported, since either may be the one the
    guard is handed.
    """
    names: set[str] = set()
    for node in ast.walk(fn):
        for field in ("body", "orelse", "finalbody"):
            block = getattr(node, field, None)
            if not isinstance(block, list):
                continue
            pending: list[str] = []
            for stmt in block:
                allocated = [
                    n for n in ast.walk(stmt) if _alloc_wt(n) is not None
                ]
                if not allocated:
                    continue          # allocates nothing; separates nothing
                bound = _i32_names_bound_by(stmt, allocated)
                if bound is None:
                    # Some other allocation, or one whose name this walk
                    # cannot read: whatever came before it is no longer
                    # beside what comes after.
                    pending = []
                elif len(bound) > 1:
                    # Both halves in ONE statement — a tuple assignment is
                    # as adjacent as two lines can be.
                    names.update(bound)
                    pending = bound[-1:]
                else:
                    if pending:
                        names.update(pending)
                        names.update(bound)
                    pending = bound
    return names


def _i32_names_bound_by(
    stmt: ast.stmt, allocated: list[ast.AST],
) -> list[str] | None:
    """The names *stmt* binds to an ``alloc_local("i32")``, in source order,
    or None when it allocates anything else or binds an allocation to
    something this walk cannot name.

    Python binds a value to a name in more ways than one, and reading only
    `ast.Assign.targets` reads only one of them: `ast.AnnAssign` keeps its
    binding in `target` (SINGULAR, because the annotated form binds exactly
    one), a tuple assignment holds the two halves of a pair in a single
    statement, and a walrus binds inside an expression.  Each of the three
    fell through to "some other allocation" and CLEARED the adjacency
    window, so a hand-bound pair written any of those ways was a silence
    rather than a finding — the blindness that call-site reading had, one
    level down (CodeRabbit on PR #1478).

    Only simple statements are read: a compound statement's own blocks are
    visited in their own right by the caller's walk, so reading its
    bindings here would report the same pair twice and, worse, call two
    allocations in DIFFERENT branches adjacent.
    """
    if not isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.Expr)):
        return None
    bound: dict[int, str] = {}
    for node in ast.walk(stmt):
        pairs: list[tuple[ast.expr, ast.expr]] = []
        if isinstance(node, ast.Assign):
            if (len(node.targets) == 1
                    and isinstance(node.targets[0], ast.Tuple)
                    and isinstance(node.value, ast.Tuple)
                    and len(node.targets[0].elts) == len(node.value.elts)):
                pairs = list(zip(node.targets[0].elts, node.value.elts))
            else:
                pairs = [(t, node.value) for t in node.targets]
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            pairs = [(node.target, node.value)]
        elif isinstance(node, ast.NamedExpr):
            pairs = [(node.target, node.value)]
        for target, value in pairs:
            if isinstance(target, ast.Name) and _alloc_wt(value) is not None:
                bound[id(value)] = target.id
    if len(bound) != len(allocated):
        return None                   # an allocation this walk cannot name
    if any(_alloc_wt(a) != "i32" for a in allocated):
        return None                   # not the pair-half width
    ordered = [bound[id(a)] for a in allocated]
    return ordered or None


def _classify(value: object, adjacent: set[str]) -> str:
    """How the expression *value* produces a guarded value's local."""
    if isinstance(value, _Unpack):      # pragma: no cover — resolved first
        return FROM_UNKNOWN
    if (isinstance(value, ast.Attribute)
            and value.attr in ("slot_local", "locals")):
        return FROM_HELPER
    if isinstance(value, ast.Subscript):          # binding.locals[0]
        return FROM_HELPER
    if (isinstance(value, ast.Call)
            and isinstance(value.func, ast.Attribute)
            and value.func.attr == "alloc_param"):
        # The WASM SIGNATURE's own adjacency: a pair parameter is two
        # consecutive params because that is the calling convention, not
        # because two calls happen to sit side by side.  A different
        # mechanism from the spills this scan is about, and the matrix's
        # `call argument` rows are what hold it.
        return FROM_WASM_PARAM
    if (isinstance(value, ast.Call)
            and isinstance(value.func, ast.Attribute)
            and value.func.attr == "alloc_local"
            and _alloc_wt(value) is None):
        # A width computed rather than written: one local, necessarily.
        # `alloc_local("i32_pair")` would put the internal pseudo-type into
        # the locals declaration, which is not a WAT value type and fails to
        # assemble (`vera/wasm/data.py`, the #1305 note), so every pair
        # allocation is two calls with a literal "i32" and is classified
        # above.
        return FROM_COMPUTED_WIDTH
    if _alloc_wt(value) in _ONE_WORD:
        # One word is one local whatever the base, so the binding cannot be
        # wrong.  Only a PAIR needs two, and a pair allocated by hand — two
        # `alloc_local("i32")` calls in a row — is what this scan exists to
        # find; the caller has already resolved which names those are.
        return FROM_ONE_LOCAL
    return FROM_UNKNOWN


def slot_binding_provenance() -> dict[str, str]:
    """Where every guard emitter's bound local comes from, by call site.

    Checking the ARGUMENT at the call site is not enough and the difference
    is not academic: `_translate_handle_exn` allocates its pair eighteen
    lines above the emitter call, inside an `if is_pair:` branch, so the call
    site reads a plain name and the hand-bound pair is invisible (PR #1478
    review, F10 — found this way, after two rounds of call-site reading
    missed it).  So each module is parsed, every call to one of
    :data:`SLOT_BINDING_EMITTERS` is taken, and its second positional
    argument is traced back to the assignments that produce it WITHIN the
    enclosing function.

    Keyed by ``module:function:line``, valued by one of the ``FROM_*``
    constants.  `FROM_ADJACENT_PAIR` is the finding: a pair whose two locals
    are allocated side by side, correct only while nothing comes between
    them, which is the convention this PR replaces with
    `helpers.slot_value_locals`.
    """
    out: dict[str, str] = {}
    for path in codegen_sources():
        rel = str(path).split(f"{os.sep}vera{os.sep}")[-1].replace(os.sep, "/")
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        out.update(slot_binding_provenance_for_tree(tree, rel))
    return out


def slot_binding_provenance_for_tree(
    tree: ast.AST, rel: str,
) -> dict[str, str]:
    """:func:`slot_binding_provenance` for ONE parsed module.

    The seam a fixture can drive: a cell that reaches only
    :func:`_adjacent_pair_names` stays green if the emitter lookup or the
    reporting is deleted, so the classification has to be callable on a
    scratch module rather than only on the tree (CodeRabbit on PR #1478).
    """
    out: dict[str, str] = {}
    for fn in ast.walk(tree):
        if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        # Every assignment in this function, by target name.
        assigned: dict[str, list[ast.AST]] = {}

        def _record(target: ast.AST, value: ast.AST) -> None:
            if isinstance(target, ast.Name):
                assigned.setdefault(target.id, []).append(value)
            elif isinstance(target, (ast.Tuple, ast.List)):
                # `ptr, length = a, b` pairs element-wise; anything else
                # (a helper's `.locals`, a call) binds every name to the
                # one value, which is what the classification needs.
                if (isinstance(value, (ast.Tuple, ast.List))
                        and len(value.elts) == len(target.elts)):
                    for t, v in zip(target.elts, value.elts):
                        _record(t, v)
                else:
                    for position, t in enumerate(target.elts):
                        _record(t, _Unpack(value, position))

        for node in ast.walk(fn):
            if isinstance(node, (ast.ListComp, ast.SetComp,
                                 ast.GeneratorExp)):
                # A comprehension binds its own targets, and the list it
                # builds holds its element expression — the closure
                # prologue collects its refined formals that way.
                for gen in node.generators:
                    _record(gen.target, gen.iter)
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    value = node.value
                    if isinstance(value, (ast.ListComp, ast.SetComp)):
                        value = value.elt
                    _record(target, value)
            elif isinstance(node, ast.AnnAssign) and node.value is not None:
                value = node.value
                if isinstance(value, (ast.ListComp, ast.SetComp)):
                    value = value.elt
                _record(node.target, value)
            elif isinstance(node, (ast.For, ast.AsyncFor)):
                _record(node.target, node.iter)
            elif (isinstance(node, ast.Call)
                    and isinstance(node.func, ast.Attribute)
                    and node.func.attr == "append"
                    and isinstance(node.func.value, ast.Name)
                    and len(node.args) == 1):
                # A local collected into a list and unpacked from it by a
                # later `for` is the shape the two boundary prologues use
                # (`refined_param_checks.append((ptr_idx, param_te))`), so
                # the append IS the assignment as far as provenance goes.
                assigned.setdefault(node.func.value.id, []).append(
                    node.args[0])
        params = {a.arg for a in fn.args.args} | {
            a.arg for a in fn.args.kwonlyargs}
        adjacent = _adjacent_pair_names(fn)
        # The local a BOUND emitter is called under, derived from its
        # assignment in this function rather than guessed by name.
        bound_emitters = {
            name for name, values in assigned.items()
            if any(isinstance(v, ast.Attribute)
                   and v.attr == BOUND_EMITTER_ATTRIBUTE for v in values)
        }
        for node in ast.walk(fn):
            if not isinstance(node, ast.Call):
                continue
            if (isinstance(node.func, ast.Attribute)
                    and node.func.attr in SLOT_BINDING_EMITTERS):
                index, keyword = SLOT_BINDING_EMITTERS[node.func.attr]
            elif (isinstance(node.func, ast.Name)
                    and node.func.id in bound_emitters):
                index, keyword = BOUND_EMITTER_POSITION
            else:
                continue
            key = f"{rel}:{fn.name}:{node.lineno}"
            arg: object
            if len(node.args) > index:
                arg = node.args[index]
            else:
                by_keyword = [k.value for k in node.keywords
                              if k.arg == keyword]
                if not by_keyword:
                    # A call whose value argument this walk cannot read
                    # is a site nobody has classified, which is the
                    # shrug `FROM_UNKNOWN` exists to refuse; skipping it
                    # dropped a keyword call silently (PR #1478 review,
                    # F11).
                    out[key] = FROM_UNKNOWN
                    continue
                arg = by_keyword[0]
            if isinstance(arg, ast.Name) and arg.id in params:
                out[key] = FROM_PARAMETER
                continue
            if isinstance(arg, ast.Name) and arg.id in adjacent:
                out[key] = FROM_ADJACENT_PAIR
                continue
            kinds = {
                _classify(v, adjacent) for v in _resolve(arg, assigned)
            }
            out[key] = (FROM_ADJACENT_PAIR
                        if FROM_ADJACENT_PAIR in kinds
                        else sorted(kinds)[0])
    return out


def emitter_call_sites(
    emitter: str, *, role_pattern: str = ROLE_PATTERN, window: int = 6,
    drop_self: bool = True,
) -> set[str]:
    """``{enclosing_function}/{role}`` for every call to *emitter*.

    A call whose role is passed through a variable rather than written as a
    literal reports ``?`` — which a roster entry then has to name, rather than
    the scan inventing a role for it.  *drop_self* excludes calls made from
    inside the emitter itself: right for an emitter that does not recurse, and
    wrong for one that does, where the recursion is a route of its own (the
    tuple decomposition's nested level, which has its own matrix cells).

    An emitter INSTALLED as a bound callable rather than called by name — the
    #1268 `throw`-payload guard, handed to the translation context through
    `set_refinement_guard_emitter` — IS seen: the name is matched on a word
    boundary rather than on an opening paren, so `functools.partial(self.
    <emitter>, ctx)` is a wiring site like any other.  Its role is then `?`,
    which a roster entry has to name.
    """
    # `self.<emitter>` followed by a call OR by anything else: an emitter
    # handed to `functools.partial` is wired just as hard as one called by
    # name, and a paren-only pattern left that form invisible — live in the
    # tree at `functions.py:544` and `closures.py:424`, which wire the
    # boundary emitter exactly that way (PR #1478 review, F5).
    pattern = re.compile(rf"self\.{re.escape(emitter)}\b")
    role = re.compile(role_pattern)
    found: set[str] = set()
    for path in codegen_sources():
        enclosing = "?"
        lines = path.read_text(encoding="utf-8").splitlines()
        for n, line in enumerate(lines):
            match = _DEF.match(line)
            if match:
                enclosing = match.group(1)
                continue
            if not pattern.search(line):
                continue
            hit = role.search("\n".join(lines[n:n + window]))
            found.add(f"{enclosing}/{hit.group(1) if hit else '?'}")
    if drop_self:
        return {site for site in found if not site.startswith(f"{emitter}/")}
    return found
