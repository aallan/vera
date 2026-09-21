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


#: A literal heap-field size or alignment table, as a hand copy spells one: a
#: dict whose FIRST key is a WAT type string mapped to a byte count,
#: `{"i32": 4, "i64": 8, ...}`.  The SHAPE is what makes it recognisable,
#: never the variable name — the copies this repo carried used four spellings
#: — and keying on the shape is also what keeps the scan off tables that map
#: VERA type names to sizes (`{"Int": 8, …}`, the array-element stride, where
#: a `Bool` is one byte rather than four): a different fact that belongs to
#: its own reader.
_LAYOUT_TABLE = re.compile(
    r'\{\s*"(?:i32|i64|f64|i32_pair)"\s*:\s*\d+', re.S)

#: The one module allowed to state it.
LAYOUT_OWNER = "wasm/helpers.py"


def local_layout_tables() -> dict[str, list[str]]:
    """Every module of the code-generation layer that declares a heap-field
    size or alignment table of its own, as ``{module: [line, ...]}``.

    The layout is construction's contract with every reader of a constructed
    object — the destructure, the match extraction, the nested tag walk, the
    structural-eq field walk, the boundary guard's tuple decomposition — and
    it was five hand copies that happened to agree.  Unifying them is worth
    exactly as much as the property that they STAY unified, so this reads the
    modules rather than trusting a comment: a sixth copy, under whatever
    name, is a row here.

    Matched over the whole text rather than line by line, so a table written
    across several lines cannot slip through; the reported line is where the
    dict opens.  :data:`LAYOUT_OWNER` is excluded, being the one module the
    tables belong to.
    """
    found: dict[str, list[str]] = {}
    for path in codegen_sources():
        rel = str(path).split(f"{os.sep}vera{os.sep}")[-1].replace(os.sep, "/")
        if rel == LAYOUT_OWNER:
            continue
        text = path.read_text(encoding="utf-8")
        hits = [
            f"line {text.count(chr(10), 0, m.start()) + 1}: "
            f"{text[m.start():m.start() + 60].splitlines()[0]}"
            for m in _LAYOUT_TABLE.finditer(text)
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
