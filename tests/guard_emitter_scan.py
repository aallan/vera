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
