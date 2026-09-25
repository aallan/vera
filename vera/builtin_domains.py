"""The declared domains of the built-ins whose translation can trap (#1480).

A built-in whose compiled translation checks its arguments and traps outside
some range has a precondition, whether or not its signature says so.  Before
#1480 none did: `string_char_code(s, i)` bounds-checks `i` against the byte
length of `s` and traps with `unreachable`, while spec §9 gave it
`requires(true)` and the verifier recorded nothing — so `vera verify` passed a
program that trapped on every out-of-range index.

Each entry here is that precondition, written as the Vera `requires` clause
the built-in would carry if it were declared in Vera, over its parameters
exactly as a user function's is.  The verifier obligates it at every call
site through the same call-site precondition machinery a user callee's
`requires` goes through (E501 when it may not hold, E532 when it cannot be
checked statically), with one difference: the check runs INLINE, at the call,
so a discharged domain is recorded too — the call site is where the runtime
check is, and so where its obligation is (`vera.smt.CallDischarge`).

The domain is substituted with the call's ACTUAL arguments before it is
translated, rather than read against a callee environment: the byte length of
a string is modelled only for a literal (#802), so `string_length(@String.0)`
over a bound term has no model, while `string_length("abc")` is exactly 3.

A built-in whose trap is a native instruction the verifier already obligates
under a kind of its own is NOT here: `float_to_int` (and `floor`, `ceil`,
`round`, the same `i64.trunc_f64_s` after a rounding step) carry the
`float_to_int_domain` obligation (#807), which decides a concrete argument
exactly and leaves a symbolic one to the trap, because the solver's reasoning
across the float/integer boundary is not reliable (spec §6.4.3).
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache

from vera import ast


@dataclass(frozen=True)
class BuiltinDomain:
    """One trapping built-in's declared domain."""

    name: str
    #: The parameter list, as it is written in a Vera signature.
    params: str
    #: The domain, as the body of a Vera ``requires`` over those parameters.
    requires: str
    #: What the compiled translation does outside the domain, and where.
    trap: str


#: Every built-in whose compiled translation checks its arguments and traps
#: outside a domain the verifier can state.  Enumerated from the translators
#: (see the module docstring for the one family deliberately left out), and
#: held to them by `tests/test_evaluated_position_obligations_1480.py`.
BUILTIN_DOMAINS: tuple[BuiltinDomain, ...] = (
    BuiltinDomain(
        name="string_char_code",
        params="@String, @Int",
        requires="@Int.0 >= 0 && @Int.0 < string_length(@String.0)",
        trap=(
            "the index is compared in i64 with the string's length in "
            "bytes, and the call traps when it is negative or not below "
            "that length (`_translate_char_code`)"
        ),
    ),
)

#: The names alone, for the translator's per-call test.
BUILTIN_DOMAIN_NAMES: frozenset[str] = frozenset(
    d.name for d in BUILTIN_DOMAINS)


@dataclass(frozen=True)
class DomainContract:
    """A built-in's domain, parsed: the pieces a call-site check needs."""

    domain: BuiltinDomain
    params: tuple[ast.TypeExpr, ...]
    requires: ast.Requires
    #: The Vera source the two were parsed from — the text a diagnostic
    #: quotes the precondition out of, since its span numbers lines there.
    source: str


def declaration_source(domain: BuiltinDomain) -> str:
    """The built-in written as a Vera declaration carrying its domain.

    Only the parameters and the `requires` are read back; the rest is there
    so the text parses as a function declaration.
    """
    return (
        f"private fn {domain.name}({domain.params} -> @Unit)\n"
        f"  requires({domain.requires})\n"
        f"  ensures(true)\n"
        f"  effects(pure)\n"
        f"{{\n  ()\n}}\n"
    )


@lru_cache(maxsize=None)
def domain_contract(name: str) -> DomainContract | None:
    """The parsed domain of built-in *name*, or None if it declares none."""
    domain = next((d for d in BUILTIN_DOMAINS if d.name == name), None)
    if domain is None:
        return None
    # Imported here, not at module level: the parser pulls in the grammar,
    # and a module the SMT layer imports should not load it until a call to
    # a trapping built-in actually needs its domain.
    from vera.parser import parse_to_ast

    source = declaration_source(domain)
    program = parse_to_ast(source)
    fn = program.declarations[0].decl
    if not isinstance(fn, ast.FnDecl):  # pragma: no cover — source is ours
        raise AssertionError(f"domain of {name} did not parse as a function")
    requires = next(
        c for c in fn.contracts if isinstance(c, ast.Requires))
    return DomainContract(domain, fn.params, requires, source)
