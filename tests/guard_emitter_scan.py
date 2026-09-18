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
    `set_refinement_guard_emitter` — is not a call site this scan can see; the
    matrix's own cell for that position is what holds it.
    """
    pattern = re.compile(rf"self\.{re.escape(emitter)}\(")
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
