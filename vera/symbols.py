"""Every composed internal symbol, built and read in one place (#1494).

Code generation emits ONE flat WebAssembly function namespace, and the
compiler's data layouts share one flat ADT namespace.  Several owners put
names there — the entry program, each module, the prelude, the compiler's
runtime, the host — and several constructs compose a name from parts: a
module's qualified declaration, a hoisted ``where`` helper, a monomorphized
clone.  This module is the ONE builder of every such composed name and the
ONE reader of it.  Each construct is spelled with a marker or separator that
no Vera identifier, type name or module path can spell, so the encoding is
injective by construction, and :func:`decode` recovers the parts of every
name the builders make.

The grammar::

    symbol    := runtime | host | qualified | chain
    runtime   := "rt." NAME                   -- the compiler's own functions
    host      := "vera." NAME                 -- host imports
    qualified := owner "::" chain             -- a module's, or the prelude's
    owner     := SEG ("." SEG)*               -- a module path, as in source
               | "<prelude>"                  -- the prelude (#1495)
    chain     := IDENT step*
    step      := "$where$" IDENT              -- a hoisted `where` helper
               | "$" MANGLED                  -- a monomorphized clone

``IDENT`` is a declaration's name, ``SEG`` a module path segment (both
``LOWER_IDENT``, and a data declaration's ``IDENT`` is ``UPPER_IDENT``), and
``MANGLED`` a type-argument vector escaped by
:func:`vera.monomorphize.mangle_type_name`, whose alphabet is
``[A-Za-z0-9_]``.  ``NAME`` is a runtime or host name, which is the
compiler's own and opaque here.

Why no two parts can be confused:

* ``::`` separates an owner from its declaration, and ``.`` separates path
  segments.  No identifier, path segment or escaped type contains ``:`` or
  ``.``, so the first ``::`` of a symbol is always its owner boundary, and a
  symbol with no ``::`` is never qualified.
* ``<prelude>`` is the prelude's owner.  ``<`` starts no path segment, so no
  module path spells it — a module may be called ``prelude``, and its
  symbols read ``prelude::…``.
* ``$`` occurs in no identifier and no escaped type, so it only ever starts a
  step.  A step spelled ``$where$`` is a helper: ``where`` is reserved, so no
  identifier is ``where`` (E153), and no escaped type argument is either —
  a type name starts with an upper-case letter, and an owner-qualified data
  name escapes its ``::``.
* ``rt.`` and ``vera.`` begin only runtime and host symbols: a qualified
  symbol whose path begins ``rt`` still contains ``::`` and is read as
  qualified first, and ``vera`` is a reserved path prefix.

The module path is spelled as in source (``a.b::f``, the syntax of a
qualified call), so a module declaration's symbol already reads as source.
:func:`display` renders any symbol as the spelling a person wrote, for every
surface that shows a name to a person (#1494, DESIGN.md principle 1).
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

#: Between an owner and its declaration: the source syntax of a qualified call.
QUALIFIER = "::"
#: Between module path segments, as in source.
PATH_SEP = "."
#: The prelude's owner token; no module path can spell it.
PRELUDE_OWNER = "<prelude>"
#: Before a hoisted ``where`` helper's name.
HELPER_STEP = "$where$"
#: Before a monomorphized clone's escaped type-argument vector.
CLONE_STEP = "$"
#: The compiler's runtime namespace, and the host's.
RUNTIME_PREFIX = "rt."
HOST_PREFIX = "vera."

#: The kinds :func:`decode` distinguishes.
LOCAL = "local"
MODULE = "module"
PRELUDE = "prelude"
RUNTIME = "runtime"
HOST = "host"


@dataclass(frozen=True)
class Step:
    """One step of a chain: a hoisted helper, or a clone's type arguments."""

    kind: str  # "helper" | "clone"
    text: str


@dataclass(frozen=True)
class Symbol:
    """A decoded symbol.

    ``owner`` is one of :data:`LOCAL`, :data:`MODULE`, :data:`PRELUDE`,
    :data:`RUNTIME` and :data:`HOST`.  ``path`` is the module path of a
    :data:`MODULE` symbol and empty otherwise.  ``base`` and ``steps`` are the
    chain, for every owner but the runtime and the host, whose ``base`` is
    the opaque name after the prefix.
    """

    owner: str
    path: tuple[str, ...]
    base: str
    steps: tuple[Step, ...] = ()


# ---------------------------------------------------------------------
# Builders
# ---------------------------------------------------------------------


def owner_prefix(path: Sequence[str]) -> str:
    """The qualifier every symbol owned by module *path* begins with.

    The prelude's namespace, ``(PRELUDE_OWNER,)``, gives the prelude's.
    """
    return PATH_SEP.join(path) + QUALIFIER


def module_symbol(path: Sequence[str], local: str) -> str:
    """Module *path*'s declaration *local* (a chain), owner-qualified."""
    return owner_prefix(path) + local


def prelude_symbol(local: str) -> str:
    """The prelude's declaration *local*, when the entry declares its own."""
    return module_symbol((PRELUDE_OWNER,), local)


def helper_symbol(parent: str, helper: str) -> str:
    """The hoisted ``where`` helper *helper* of the declaration *parent*."""
    return parent + HELPER_STEP + helper


def clone_symbol(base: str, mangled_args: str) -> str:
    """The clone of generic *base* at the escaped type-argument vector."""
    return base + CLONE_STEP + mangled_args


def runtime_symbol(name: str) -> str:
    """The compiler's own function or export *name*."""
    return RUNTIME_PREFIX + name


def host_symbol(name: str) -> str:
    """The host import *name*."""
    return HOST_PREFIX + name


# ---------------------------------------------------------------------
# Readers
# ---------------------------------------------------------------------


def split_chain(chain: str) -> tuple[str, tuple[Step, ...]]:
    """A chain's base name and its steps.

    ``chain.split("$")`` yields the base, then a token per step: a token that
    is exactly ``where`` introduces a helper and is followed by the helper's
    name, and any other token is a clone's escaped type-argument vector.
    """
    tokens = chain.split("$")
    base = tokens[0]
    steps: list[Step] = []
    i = 1
    while i < len(tokens):
        if tokens[i] == "where" and i + 1 < len(tokens):
            steps.append(Step("helper", tokens[i + 1]))
            i += 2
        else:
            steps.append(Step("clone", tokens[i]))
            i += 1
    return base, tuple(steps)


def join_chain(base: str, steps: Sequence[Step]) -> str:
    """The inverse of :func:`split_chain`."""
    out = base
    for step in steps:
        if step.kind == "helper":
            out = helper_symbol(out, step.text)
        else:
            out = clone_symbol(out, step.text)
    return out


def decode(symbol: str) -> Symbol:
    """The owner and parts of *symbol*; the left inverse of :func:`encode`."""
    if QUALIFIER in symbol:
        owner_text, chain = symbol.split(QUALIFIER, 1)
        base, steps = split_chain(chain)
        if owner_text == PRELUDE_OWNER:
            return Symbol(PRELUDE, (), base, steps)
        return Symbol(MODULE, tuple(owner_text.split(PATH_SEP)), base, steps)
    if symbol.startswith(RUNTIME_PREFIX):
        return Symbol(RUNTIME, (), symbol[len(RUNTIME_PREFIX):])
    if symbol.startswith(HOST_PREFIX):
        return Symbol(HOST, (), symbol[len(HOST_PREFIX):])
    base, steps = split_chain(symbol)
    return Symbol(LOCAL, (), base, steps)


def encode(sym: Symbol) -> str:
    """The symbol text of *sym*; :func:`decode` inverts it."""
    if sym.owner == RUNTIME:
        return runtime_symbol(sym.base)
    if sym.owner == HOST:
        return host_symbol(sym.base)
    chain = join_chain(sym.base, sym.steps)
    if sym.owner == PRELUDE:
        return prelude_symbol(chain)
    if sym.owner == MODULE:
        return module_symbol(sym.path, chain)
    return chain


def is_runtime(symbol: str) -> bool:
    """Whether *symbol* is the compiler's runtime's or the host's."""
    return decode(symbol).owner in (RUNTIME, HOST)


def is_prelude(symbol: str) -> bool:
    """Whether *symbol* is the prelude's own (overridden) declaration."""
    return decode(symbol).owner == PRELUDE


def unqualified(symbol: str) -> str:
    """*symbol* without its owner qualifier: the chain alone."""
    if QUALIFIER in symbol:
        return symbol.split(QUALIFIER, 1)[1]
    return symbol


def strip_clone(symbol: str) -> str:
    """*symbol* without a trailing clone step, if it has one."""
    sym = decode(symbol)
    if sym.steps and sym.steps[-1].kind == "clone":
        return encode(Symbol(sym.owner, sym.path, sym.base, sym.steps[:-1]))
    return symbol


def display(symbol: str) -> str:
    """The spelling a PERSON wrote for the declaration *symbol* names.

    A module's declaration reads as a qualified call does (``liba::h``), a
    hoisted helper by its own name, a clone by its generic's name, and the
    prelude's own declaration by the prelude function's name.  A lifted
    closure reads ``fn(...)``, the form it was written in, and the runtime's
    and the host's own functions read by their names.  No internal marker
    survives (DESIGN.md principle 1).
    """
    sym = decode(symbol)
    if sym.owner == RUNTIME:
        if sym.base.startswith("anon_"):
            return "fn(...)"
        return sym.base
    if sym.owner == HOST:
        return sym.base
    name = sym.base
    for step in sym.steps:
        if step.kind == "helper":
            name = step.text
    if sym.owner == MODULE:
        return owner_prefix(sym.path) + name
    return name


def display_data_name(symbol: str) -> str:
    """The spelling a person sees for an ADT or constructor name.

    An owner-qualified data declaration (#1317) reads by its own name: the
    qualifier exists only to keep two modules' same-named declarations apart
    in the flat registry, and no data name is written qualified in source.
    """
    return unqualified(symbol)
