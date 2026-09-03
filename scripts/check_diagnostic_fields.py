#!/usr/bin/env python3
"""Diagnostic-field enforcement script (#682).

`spec/00-introduction.md` §0.5.1 ("Diagnostic Structure") says every
diagnostic MUST include an error code, a description, a rationale, a
fix, and a spec reference.  "Diagnostics as instructions" is a core
differentiator (DESIGN.md §"Checkability"), so this is a load-bearing
claim — yet the `Diagnostic` dataclass defaults `rationale`/`fix`/
`spec_ref`/`error_code` to `""`, so a partially-tagged diagnostic
compiles and ships silently.

This script makes "is every diagnostic fully tagged?" a mechanically
checkable contract, mirroring `scripts/check_walker_coverage.py`
(#597).  It AST-parses every `Diagnostic(...)` constructor and every
`self._error(...)` / `self._warning(...)` call under `vera/` and fails
if a required field is missing.  It also validates that every present
`spec_ref` resolves to a real spec section/chapter, that every literal
`error_code` is *registered* in `vera/errors.py` `ERROR_CODES`, and
(#828) that every literal `error_code` emitted from more than one
distinct (file, enclosing-function) site has that exact site set
declared in `KNOWN_MULTI_SITE_ERROR_CODES` — the deterministic half of
making each code unique per concept; enforcing `error_code` *presence*
is a tracked follow-up.

Design — explicit over implicit (DESIGN.md §"Explicitness over
convenience"; no silently-inferred exemptions):

- **Required by default:** ``rationale``, ``fix``, ``spec_ref`` on every
  site (the three content fields of spec §0.5.1, per #682's acceptance
  criteria; ``error_code`` enforcement is a tracked follow-up).  A field
  counts as present if its kwarg is a non-empty string literal, or any
  non-constant expression (a variable / f-string / concatenation
  threading the value through).
- **Severity rule:** a ``warning`` carries no corrected-code template,
  so ``fix`` is not required of warning-severity diagnostics.
- **Structural registry (`STRUCTURAL_EXEMPTIONS`):** the codegen
  ``_error`` / ``_warning`` helpers build internal-compiler (E699) and
  "function skipped" limitation diagnostics that have no user-facing
  fix or spec section.  These are exempt from ``fix`` / ``spec_ref`` —
  declared *once*, with a written reason, here.  A new helper or a new
  direct ``Diagnostic(...)`` defaults to fully-required until added.
- **Per-call opt-out:** ``# diag-fields-exempt: <reason>`` on the call
  (found anywhere across a multi-line call's span), the reason mandatory —
  for one-off defensive / internal branches (e.g. an "unknown expression
  type" fallback).  It waives missing fields and *unresolvable* non-literal
  severity/spec_ref, never a resolving-but-wrong spec_ref or an
  unregistered error_code (#955).  A marker without a reason is itself a
  violation.  (A dedicated token, not a ruff-style suppression comment —
  see ``OPT_OUT`` below for why.)
- **Plumbing skip:** the *single* ``Diagnostic(...)`` an ``_error`` /
  ``_warning`` helper *method* constructs is not an independent site — its
  fields are threaded from the helper's parameters, so its call sites plus
  the registry govern it.  All three passes below honour the skip.
  Narrowed for #827: keying on the helper's *name* alone let a stray second
  ctor in the same helper (or a non-helper coincidentally named ``_error``)
  escape every pass.  The skip now requires (a) a genuine helper *method* —
  a class member with a ``self`` receiver, since every real helper is one, so
  a module-level function merely named ``_error`` is inspected, not exempted —
  (b) that the ctor is the method's **sole own-scope** construction, and (c)
  that the ctor is actually *reachable as the helper's result* — return-ed,
  appended, or bound to a local that is later return-ed/appended (#956).  A
  helper holding two constructions is ambiguous: neither is skipped, and both
  are inspected.  Counting *every* own-scope construction (not just the one
  structurally ``return``ed or ``.append(...)``-ed) is what makes (b) sound —
  see ``_own_scope_diag_ctors``.  "Own scope" is the helper's **body**:
  decorators, parameter defaults and annotations evaluate in the *enclosing*
  scope, so a ``Diagnostic(...)`` there is inspected, never elected.  Without
  (c), a helper that builds its sole ctor and hands it to something other
  than a return/append (e.g. ``self.dispatch(d)``) was wrongly elected as
  plumbing — see ``_ctor_is_reachable_as_result``.

Usage:
    python scripts/check_diagnostic_fields.py   # exit 0 if all sites
                                                # fully tagged; 1 + a
                                                # report otherwise.

Wired into pre-commit and the CI lint job so a new under-tagged
diagnostic added to `vera/` is rejected at the door.
"""

from __future__ import annotations

import ast
import io
import re
import sys
import tokenize
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator

ROOT = Path(__file__).resolve().parent.parent

# Fields this gate enforces — items 3/4/5 of spec §0.5.1 (rationale, fix,
# spec_ref), matching issue #682's acceptance criteria.  Description (item 2)
# is a mandatory dataclass field, always structurally present.  error_code
# (item 1) is near-universal already; enforcing it — plus the handful of
# codeless sites and the error_code/registry-name mismatches — is a tracked
# follow-up, deliberately out of this gate's scope.
REQUIRED_FIELDS = ("rationale", "fix", "spec_ref")

# Per-call opt-out marker.  Deliberately a dedicated token rather than a
# ruff-style suppression comment (issue #682's first suggestion): ruff claims
# every "noqa"-prefixed comment as its own directive and warns on an unknown
# code there, and a near-miss spelling would read to it as a blanket
# suppression.  A distinct token sidesteps the linter collision entirely.
OPT_OUT = "# diag-fields-exempt"

# (file-family, helper-method) -> (exempt fields, reason).  The codegen
# helpers' Diagnostic construction omits these by design; the diagnostic
# class genuinely has no such content.  Declared here so the exemption
# surface is explicit and reviewable rather than inferred from helper
# signatures.  (Warning-severity `fix` exemption is handled generally by
# the severity rule, not per-entry.)
STRUCTURAL_EXEMPTIONS: dict[tuple[str, str], tuple[set[str], str]] = {
    ("codegen", "_error"): (
        {"fix", "spec_ref"},
        "E699 internal-compiler errors: the type checker should have "
        "rejected the input before codegen; no user-facing fix or spec "
        "section exists.",
    ),
    ("codegen", "_warning"): (
        {"fix", "spec_ref"},
        "codegen 'function skipped' limitation warnings: report an "
        "unsupported-feature limitation, not a user error; no single "
        "corrected-code fix or spec section applies.",
    ),
}


@dataclass
class Violation:
    file: str
    line: int
    target: str           # "_error" | "_warning" | "Diagnostic"
    missing: list[str]
    snippet: str | None


def family(filename: str) -> str:
    """Map a file path to its diagnostic-helper family."""
    s = filename.replace("\\", "/")
    if "/checker/" in s or s.endswith("/checker.py"):
        return "checker"
    if "verifier" in s:
        return "verifier"
    if "/codegen/" in s:
        return "codegen"
    return "other"


def _field_present(call: ast.Call, name: str) -> bool:
    """A field is present if its kwarg is a non-empty string literal, or
    any non-constant expression (variable / f-string / concatenation
    threading the value through)."""
    for kw in call.keywords:
        if kw.arg != name:
            continue
        v = kw.value
        if isinstance(v, ast.Constant):
            return isinstance(v.value, str) and v.value.strip() != ""
        return True  # Name / JoinedStr / Call / BinOp(concat) → threaded
    return False


def _is_diag_ctor(node: ast.AST | None) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "Diagnostic")


def _walk_own_scope(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> Iterator[ast.AST]:
    """Yield every node in ``fn``'s BODY without descending into nested
    function / lambda / class scopes.

    Two boundaries matter, and both are load-bearing:

    - **Downward:** ``ast.walk`` would cross into nested ``def`` / ``lambda`` /
      ``class`` bodies, so a ``Diagnostic(...)`` there would be wrongly
      attributed to the *outer* helper — either miscounting the helper as
      ambiguous (>1 ctor) or exempting a ctor that belongs to the inner scope.
    - **Sideways:** the seed is ``fn.body``, NOT ``ast.iter_child_nodes(fn)``.
      For a ``FunctionDef`` the latter also yields ``decorator_list``, the
      ``arguments`` node (carrying default-value expressions) and the ``returns``
      annotation — all of which are evaluated in the *enclosing* scope, not the
      helper's.  Sweeping them in let a ``Diagnostic(...)`` written as a
      decorator argument (``@memo(fallback=Diagnostic(...))``) or a parameter
      default be counted as the helper's own construction; where the helper had
      no body ctor it then became the *sole* candidate, was elected as the
      helper's plumbing, and was skipped by all three passes — an under-tagged
      diagnostic escaping the gate (PR #952 review).
    """
    stack: list[ast.AST] = list(fn.body)
    while stack:
        node = stack.pop()
        yield node
        # A nested def / async def / lambda / class opens a new scope — its
        # Diagnostic constructions are not the enclosing helper's plumbing.
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            continue
        stack.extend(ast.iter_child_nodes(node))


def _own_scope_diag_ctors(
    fn: ast.FunctionDef | ast.AsyncFunctionDef,
) -> list[ast.Call]:
    """Every ``Diagnostic(...)`` constructed in ``fn``'s OWN scope — its body,
    excluding nested ``def`` / ``lambda`` / ``class`` bodies (a ctor there is
    that scope's concern) and excluding decorators / parameter defaults /
    annotations (those evaluate in the enclosing scope; see ``_walk_own_scope``).

    Counts *every* construction, deliberately — not only the one structurally
    ``return``ed or ``.append(...)``-ed.  #827's fault class is a **stray** ctor
    living alongside the helper's real one, and a rule that recognised only the
    return/append shape would miss a helper whose real construction is bound to
    a local first (``d = Diagnostic(...)``, then ``self.errors.append(d)``):
    the stray would be the lone *recognised* construction, get elected as "the
    helper's own", and be skipped — re-opening the very hole this gate closes.
    Counting all constructions makes any stray push the count to two, so neither
    is skipped and both are inspected."""
    return [n for n in _walk_own_scope(fn) if _is_diag_ctor(n)]  # type: ignore[misc]


def _not_an_instance_method(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    """True if a decorator rebinds ``fn`` to something other than an instance
    method, so a first parameter named ``self`` would not be a receiver.

    Matches the bare name (``@staticmethod``) and the dotted form
    (``@builtins.staticmethod``).  An alias (``from builtins import staticmethod
    as sm``) is undetectable statically; it would leave the ctor *inspected*
    rather than exempted, which is the fail-closed direction."""
    for d in fn.decorator_list:
        name = (d.id if isinstance(d, ast.Name)
                else d.attr if isinstance(d, ast.Attribute) else None)
        if name in ("staticmethod", "classmethod"):
            return True
    return False


def _class_scoped_functions(tree: ast.AST) -> set[ast.AST]:
    """Every ``def`` that is a *direct* member of a ``class`` body and is bound as
    an instance method — a genuine helper's home.

    Three shapes are excluded, each of which could otherwise name its first
    parameter ``self`` without that parameter being a receiver: a module-level
    function, a function nested inside a method (a local, not a bound method —
    ``ast.walk`` over the class would wrongly claim it), and a
    ``@staticmethod`` / ``@classmethod``."""
    out: set[ast.AST] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            for item in node.body:
                if not isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    continue
                if _not_an_instance_method(item):
                    continue
                out.add(item)
    return out


def _is_helper_method(fn: ast.FunctionDef | ast.AsyncFunctionDef,
                      class_methods: set[ast.AST]) -> bool:
    """True if ``fn`` is a genuine instance *method*: a direct member of a class
    body whose first positional parameter is ``self``.  Every real ``_error`` /
    ``_warning`` diagnostic helper in the tree (``checker/core.py``,
    ``codegen/core.py``, ``verifier.py``) is one.  A module-level function merely
    *named* ``_error`` — even one that names its first parameter ``self`` — is
    not, so its ``Diagnostic(...)`` is inspected rather than exempted (#827:
    keying the skip on the name alone let such a non-helper silently exempt an
    incomplete ctor, re-opening the under-reporting path this gate closes)."""
    if fn not in class_methods:
        return False
    params = fn.args.posonlyargs + fn.args.args
    return bool(params) and params[0].arg == "self"


def _is_append_call(node: ast.AST) -> bool:
    """True for `self.<attr>.append(...)` only — every real diagnostic-list
    sink in vera/ (`self.errors`, `self.diagnostics`) has this exact shape.
    A bare "any `.append(...)` call" check would treat an append to an
    unrelated throwaway local (`tmp = []; tmp.append(d)`) as evidence the
    ctor reaches the helper's result, when `tmp` may never be used again."""
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "append"
            and isinstance(node.func.value, ast.Attribute)
            and isinstance(node.func.value.value, ast.Name)
            and node.func.value.value.id == "self")


def _bump_target(target: ast.expr, counts: dict[str, int]) -> None:
    """Record every plain name a (possibly-tuple/list) assignment target
    binds — recursing into nested unpacking so ``a, (b, c) = ...`` counts
    all three."""
    if isinstance(target, ast.Name):
        counts[target.id] = counts.get(target.id, 0) + 1
    elif isinstance(target, (ast.Tuple, ast.List)):
        for elt in target.elts:
            _bump_target(elt, counts)


def _rebound_names(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> dict[str, int]:
    """Count every name-binding site that can affect ``fn``'s own scope —
    generically, rather than by enumerating statement forms (the
    enumeration approach missed starred unpacks, ``import ... as``,
    ``match`` captures, parameters, and ``nonlocal`` — PR #964 review):

    - any ``ast.Name`` in Store/Del context in own scope (assignment
      targets of every shape, ``for``/``with`` targets, walrus) — except
      the target of a *bare* annotation (``d: object`` with no value),
      which does not assign at runtime;
    - the binding forms that carry plain strings rather than Name nodes:
      ``import ... as``, ``except ... as``, ``match`` capture patterns;
    - the helper's own parameters (a ctor assigned to a name shadowing a
      parameter has two binding sites);
    - a ``nonlocal`` declaration in ANY nested function — it licenses an
      invisible rebind of the helper's local that the own-scope walk
      cannot see, so the declaration itself breaks trust in the name.

    A name bound more than once cannot be trusted to still hold its first
    value later in the function — see ``_ctor_is_reachable_as_result``."""
    counts: dict[str, int] = {}

    def bump(name: str) -> None:
        counts[name] = counts.get(name, 0) + 1

    a = fn.args
    for arg in (*a.posonlyargs, *a.args, *a.kwonlyargs,
                *([a.vararg] if a.vararg else []),
                *([a.kwarg] if a.kwarg else [])):
        bump(arg.arg)

    bare_annotation_targets: set[int] = set()
    for node in _walk_own_scope(fn):
        if (isinstance(node, ast.AnnAssign) and node.value is None
                and isinstance(node.target, ast.Name)):
            bare_annotation_targets.add(id(node.target))

    for node in _walk_own_scope(fn):
        if (isinstance(node, ast.Name)
                and isinstance(node.ctx, (ast.Store, ast.Del))
                and id(node) not in bare_annotation_targets):
            bump(node.id)
        elif isinstance(node, ast.alias):
            bump(node.asname if node.asname else node.name.split(".")[0])
        elif isinstance(node, ast.ExceptHandler) and node.name:
            bump(node.name)
        elif isinstance(node, (ast.MatchAs, ast.MatchStar)) and node.name:
            bump(node.name)
        elif isinstance(node, ast.MatchMapping) and node.rest:
            bump(node.rest)

    # Full-tree scan (crossing nested-scope boundaries deliberately):
    # only `nonlocal` can rebind the helper's local from a nested scope.
    for node in ast.walk(fn):
        if isinstance(node, ast.Nonlocal):
            for name in node.names:
                bump(name)

    return counts


def _ctor_is_reachable_as_result(
    fn: ast.FunctionDef | ast.AsyncFunctionDef, ctor: ast.Call,
) -> bool:
    """True if the helper's sole own-scope ctor is return-ed, appended, or
    bound to a local that is later return-ed/appended (#956).  A ctor merely
    constructed and handed to something else (e.g. dispatched via a bound
    attribute) is not plumbing — nothing threads its literal fields through
    a call site, so it must be inspected.

    The second loop matches a return/append by NAME alone — it has no real
    data-flow, so it cannot tell whether that name still holds the ctor by
    the time it's returned.  A local rebound after the ctor-binding Assign —
    plain reassignment (``d = something_else``), a ``for``/``with`` target,
    a walrus, or any of the other binding forms ``_rebound_names`` counts —
    would otherwise still match on the name and be wrongly treated as
    reachable.  Conservative fix: if the bound name is rebound more than
    once anywhere in own scope (by any binding form), its later reads are
    unreliable — don't treat it as reachable at all (inspected, not
    exempted)."""
    local_name = None
    bind_line = 0
    for node in _walk_own_scope(fn):
        if isinstance(node, ast.Return) and node.value is ctor:
            return True
        if _is_append_call(node) and any(a is ctor for a in node.args):
            return True
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name) and node.value is ctor):
            local_name = node.targets[0].id
            bind_line = node.lineno
        if (isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name)
                and node.value is ctor):
            # ``d: Diagnostic = Diagnostic(...)`` is an initial binding too,
            # not a disqualifier (PR #964 review).
            local_name = node.target.id
            bind_line = node.lineno
    if local_name is None or _rebound_names(fn).get(local_name, 0) != 1:
        return False
    for node in _walk_own_scope(fn):
        # Order-sensitive: a `return d` textually BEFORE the binding is not
        # evidence the ctor reaches the result (PR #964 review).
        if getattr(node, "lineno", 0) < bind_line:
            continue
        if isinstance(node, ast.Return) and isinstance(node.value, ast.Name) \
                and node.value.id == local_name:
            return True
        if _is_append_call(node) and any(
                isinstance(a, ast.Name) and a.id == local_name for a in node.args):
            return True
    return False


def _plumbing_ctors(tree: ast.AST) -> set[ast.Call]:
    """The ``Diagnostic(...)`` node that each ``_error`` / ``_warning`` helper
    method constructs as its *own* plumbing — narrowed for #827, then again
    for #956.

    Previously the skip keyed on the enclosing function's NAME and dropped
    *every* ``Diagnostic(...)`` lexically inside a helper span, so a stray /
    second ctor (one in an ``else`` branch, say) or a non-helper coincidentally
    named ``_error`` escaped every pass.  A ctor is now skipped only when its
    enclosing function is BOTH a genuine helper *method* (a class member with a
    ``self`` receiver — see ``_is_helper_method``) AND that method's **sole**
    own-scope construction — the one whose fields are threaded from the helper's
    params and are governed by its call sites plus ``STRUCTURAL_EXEMPTIONS``.
    A helper containing two constructions is ambiguous, so neither is skipped
    and both are inspected.

    Neither of those checks confirms the sole ctor is actually the helper's
    *output* — #956: a helper that builds the ``Diagnostic`` and hands it to
    something else entirely (e.g. ``self.dispatch(d)``) rather than returning
    or appending it was still elected as plumbing.  ``_ctor_is_reachable_as_result``
    closes that gap, run after the ``len(ctors) == 1`` gate so it doesn't disturb
    the ambiguity handling above.

    Returns the ctor *nodes*; callers match by identity (AST nodes hash by
    identity), so the set is meaningful only for ``tree``."""
    class_methods = _class_scoped_functions(tree)
    out: set[ast.Call] = set()
    for fn in ast.walk(tree):
        if (isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef))
                and fn.name in ("_error", "_warning")
                and _is_helper_method(fn, class_methods)):
            ctors = _own_scope_diag_ctors(fn)
            if len(ctors) == 1 and _ctor_is_reachable_as_result(fn, ctors[0]):
                out.add(ctors[0])
    return out


def _optout_lines(source: str) -> dict[int, str]:
    """Map a line number to its opt-out reason, but ONLY where the marker
    appears in a real ``COMMENT`` token — never inside a string literal or
    other source text.  (A raw line scan would let a diagnostic whose
    *description* merely contains the marker text silently exempt itself.)
    The reason is "" when the marker carries none (itself a violation)."""
    out: dict[int, str] = {}
    try:
        for tok in tokenize.generate_tokens(io.StringIO(source).readline):
            if tok.type != tokenize.COMMENT:
                continue
            text = tok.string.strip()
            # Anchored directive only: the comment must BE the marker, or the
            # marker immediately followed by ':' or whitespace.  A comment that
            # merely mentions the marker mid-text, or a near-miss like
            # `# diag-fields-exempt-foo`, must NOT disable the gate.
            if text == OPT_OUT:
                out[tok.start[0]] = ""
            elif text.startswith(OPT_OUT) and (
                    text[len(OPT_OUT)] == ":" or text[len(OPT_OUT)].isspace()):
                # Boundary char is ':' or ANY whitespace (space, tab, …) — the
                # trailing .strip() then drops it whatever it was.
                out[tok.start[0]] = text[len(OPT_OUT):].lstrip(" :").strip()
    except (tokenize.TokenError, IndentationError):
        pass
    return out


def check_source(source: str, filename: str) -> list[Violation]:
    """Return every under-tagged diagnostic site in one source string."""
    tree = ast.parse(source, filename=filename)
    src_lines = source.splitlines()
    fam = family(filename)

    # The sole Diagnostic() construction inside an _error/_warning helper method
    # is plumbing, not an independent site (#827: was keyed on function name,
    # which swallowed a stray second ctor in the same helper).
    plumbing = _plumbing_ctors(tree)

    optout = _optout_lines(source)
    violations: list[Violation] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        f = node.func
        # A non-literal severity is itself unresolvable (like an unresolvable
        # spec_ref below) and so IS opt-out-able — but the opt-out lookup must
        # run before we decide to report it (#955: it used to be appended and
        # `continue`d immediately, so a marker on this exact call was never
        # consulted).  Held here and only appended once we know there's no
        # opt-out for this call.
        pending: Violation | None = None
        if isinstance(f, ast.Name) and f.id == "Diagnostic":
            if node in plumbing:
                continue  # plumbing
            target = "Diagnostic"
            method = None
            severity = "error"
            sev_kws = [kw for kw in node.keywords if kw.arg == "severity"]
            if sev_kws:
                sev_val = sev_kws[0].value
                if isinstance(sev_val, ast.Constant) and isinstance(sev_val.value, str):
                    severity = sev_val.value
                else:
                    # A non-literal severity (e.g. `severity=level`) can't be
                    # resolved statically — the gate can't tell error from
                    # warning and would silently fall back to "error" and
                    # demand a `fix`.  Flag it rather than guess.
                    snip = (src_lines[node.lineno - 1]
                            if node.lineno - 1 < len(src_lines) else None)
                    pending = Violation(
                        filename, node.lineno, "Diagnostic",
                        ["severity is not a string literal — the gate cannot "
                         "tell error from warning; make it a literal"], snip)
        elif isinstance(f, ast.Attribute) and f.attr in ("_error", "_warning"):
            target = method = f.attr
            severity = "error" if f.attr == "_error" else "warning"
        else:
            continue

        snippet = src_lines[node.lineno - 1] if node.lineno - 1 < len(src_lines) else None

        # Per-call opt-out: a `# diag-fields-exempt[: reason]` COMMENT on any of
        # the call's source lines suppresses it (a missing reason is itself a
        # violation).  Comment-only — a marker inside a string does not count.
        opt_reason = next(
            (optout[ln] for ln in range(node.lineno,
                                        (node.end_lineno or node.lineno) + 1)
             if ln in optout),
            None)
        if opt_reason is not None:
            if opt_reason == "":
                violations.append(Violation(
                    filename, node.lineno, target, ["<opt-out reason>"], snippet))
            continue  # opt-out with a reason suppresses the site, `pending` included

        if pending is not None:
            violations.append(pending)
            continue

        required = set(REQUIRED_FIELDS)
        if severity == "warning":
            required.discard("fix")
        if method is not None:
            exempt, _why = STRUCTURAL_EXEMPTIONS.get((fam, method), (set(), ""))
            required -= exempt

        missing = sorted(fld for fld in required if not _field_present(node, fld))
        if missing:
            violations.append(Violation(filename, node.lineno, target, missing, snippet))
    return violations


def iter_vera_files(root: Path) -> list[Path]:
    return sorted(root.rglob("*.py"))


def check_paths(paths: Iterable[Path]) -> list[Violation]:
    out: list[Violation] = []
    for p in paths:
        rel = p.relative_to(ROOT).as_posix() if p.is_absolute() else p.as_posix()
        out.extend(check_source(p.read_text(encoding="utf-8"), rel))
    return out


# ---------------------------------------------------------------------------
# spec_ref validity.  A *present* spec_ref must also cite a real spec section
# (or chapter) whose title matches — otherwise it is a misleading instruction,
# exactly the failure the diagnostics-as-instructions claim cannot afford.
# Title comparison is lenient (case, backticks, and parentheticals ignored) so
# a cosmetic spec re-title doesn't break the gate, while a wrong section (right
# number, wrong rule — e.g. citing §4.3 "Operators" when §4.3 is "Slot
# References") still fails.
# ---------------------------------------------------------------------------

_REF_SEC = re.compile(r'Chapter\s+(\d+),\s+Section\s+([\d.]+)\s+"([^"]+)"')
_REF_CH = re.compile(r'^Chapter\s+(\d+),\s+"([^"]+)"\s*$')
_HEAD = re.compile(r'^#{1,6}\s+(\d+(?:\.\d+)*)\.?\s+(.+?)\s*$')
_CH_PREFIX = re.compile(r'^Chapter\s+\d+\s*[:—.\-]\s*')
# Cache keyed by *resolved* spec directory — a later call with a different
# spec_dir (e.g. a test fixture) must not reuse another directory's map.
_spec_cache: dict[Path, tuple[dict[str, str], dict[str, str]]] = {}


def _load_spec(spec_dir: Path) -> tuple[dict[str, str], dict[str, str]]:
    """Return ({section-number: title}, {chapter-number: chapter-title})."""
    key = spec_dir.resolve()
    cached = _spec_cache.get(key)
    if cached is not None:
        return cached
    sections: dict[str, str] = {}
    chapters: dict[str, str] = {}
    for md in sorted(spec_dir.glob("*.md")):
        cm = re.match(r"^(\d+)-", md.name)
        cnum = (cm.group(1).lstrip("0") or "0") if cm else None
        first_h1: str | None = None
        for line in md.read_text(encoding="utf-8").splitlines():
            h1 = re.match(r"^#\s+(.+?)\s*$", line)
            if h1 and first_h1 is None:
                first_h1 = h1.group(1).strip()
            m = _HEAD.match(line)
            if m:
                sections[m.group(1)] = m.group(2).strip()
        if cnum is not None and first_h1 is not None:
            chapters[cnum] = _CH_PREFIX.sub("", first_h1).strip()
    _spec_cache[key] = (sections, chapters)
    return _spec_cache[key]


def _norm(s: str) -> str:
    s = s.lower().replace("`", "")
    s = re.sub(r"\([^)]*\)", "", s)
    return re.sub(r"\s+", " ", s).strip()


def _iter_spec_refs(
    source: str, filename: str,
) -> Iterator[tuple[int, str | None, str | None, int, int]]:
    """Yield (lineno, ref_text_or_None, snippet, call_start, call_end) for each
    spec_ref argument.  ``call_start``/``call_end`` are the enclosing call's
    line span, so the caller can look up an opt-out marker anywhere across a
    multi-line call (#955), not just on the spec_ref argument's own line.

    ``ref_text`` is the literal string for a constant spec_ref; ``None`` marks
    a *non-literal* spec_ref (a variable / f-string / concatenation) that the
    gate cannot resolve to a spec section and so flags — mirroring how a
    non-literal ``severity`` is rejected in ``check_source``.  Empty / blank /
    non-string constant spec_refs are skipped here: the presence check owns
    "missing".  Diagnostic() plumbing inside the _error/_warning helper defs is
    skipped — its call sites plus the registry govern it."""
    tree = ast.parse(source, filename=filename)
    src_lines = source.splitlines()
    plumbing = _plumbing_ctors(tree)

    for n in ast.walk(tree):
        if not isinstance(n, ast.Call):
            continue
        f = n.func
        is_ctor = isinstance(f, ast.Name) and f.id == "Diagnostic"
        is_helper = (isinstance(f, ast.Attribute)
                     and f.attr in ("_error", "_warning"))
        if not (is_ctor or is_helper):
            continue
        if is_ctor and n in plumbing:
            continue  # plumbing
        call_start, call_end = n.lineno, n.end_lineno or n.lineno
        for kw in n.keywords:
            if kw.arg != "spec_ref":
                continue
            v = kw.value
            ln = v.lineno
            snip = src_lines[ln - 1] if ln - 1 < len(src_lines) else None
            if isinstance(v, ast.Constant):
                if isinstance(v.value, str) and v.value.strip():
                    yield ln, v.value, snip, call_start, call_end
                # empty / None / non-str literal → presence check owns "missing"
            else:
                yield ln, None, snip, call_start, call_end  # non-literal: unresolvable, flag it


def spec_ref_violations_in_source(source: str, filename: str,
                                  spec_dir: Path | None = None) -> list[Violation]:
    """Flag every spec_ref in one source that does not resolve to a real spec
    section/chapter with a matching (normalized) title.

    A non-literal (unresolvable) spec_ref honours ``# diag-fields-exempt``
    (#955) — same as a non-literal severity in ``check_source``.  A spec_ref
    that DOES resolve but cites the wrong/nonexistent section is a content
    error and is never suppressed by the opt-out, marker or not."""
    sections, chapters = _load_spec(spec_dir or (ROOT / "spec"))
    optout = _optout_lines(source)
    out: list[Violation] = []
    for ln, ref, snip, call_start, call_end in _iter_spec_refs(source, filename):
        if ref is None:
            opt_reason = next(
                (optout[cl] for cl in range(call_start, call_end + 1) if cl in optout),
                None)
            if opt_reason is not None:
                continue  # unresolvable spec_ref, opted out
            out.append(Violation(
                filename, ln, "spec_ref",
                ["spec_ref is not a string literal — the gate cannot validate "
                 "it against the spec; make it a literal"], snip))
            continue
        why: str | None = None
        sec_matches = list(_REF_SEC.finditer(ref))
        if sec_matches:
            # A spec_ref may cite SEVERAL sections (e.g. `§4.7 "Let Bindings"
            # and §11.2.1 "Nat as i64"`).  Validate EVERY citation, not just the
            # first — a wrong/bogus later citation is just as misleading and
            # must not ship silently.
            for m in sec_matches:
                chap, sec, title = m.group(1), m.group(2), m.group(3)
                actual = sections.get(sec)
                if actual is None:
                    why = f"cites §{sec}, which does not exist in the spec"
                elif _norm(actual) != _norm(title):
                    why = f'cites §{sec} as "{title}" but it is "{actual}"'
                elif not (sec == chap or sec.startswith(chap + ".")):
                    why = f"§{sec} is not in Chapter {chap}"
                if why is not None:
                    break
            # Reject stray non-citation text (e.g. a `LIES ` prefix): once the
            # citations and their joiners (commas / "and" / whitespace) are
            # stripped, nothing should remain.  `.finditer` alone would tolerate
            # garbage around an otherwise-valid citation.
            if why is None:
                residue = re.sub(r"\band\b|[,\s]+", "", _REF_SEC.sub("", ref))
                if residue:
                    why = ("spec_ref has unrecognised text around its "
                           f"citation(s): {ref!r}")
        else:
            mc = _REF_CH.match(ref)
            if not mc:
                why = f"unrecognised spec_ref format: {ref!r}"
            else:
                chap, title = mc.group(1), mc.group(2)
                actual = chapters.get(chap)
                if actual is None or _norm(actual) != _norm(title):
                    why = f'Chapter {chap} is "{actual}", not "{title}"'
        if why is not None:
            out.append(Violation(filename, ln, "spec_ref", [why], snip))
    return out


def spec_ref_violations(paths: Iterable[Path],
                        spec_dir: Path | None = None) -> list[Violation]:
    out: list[Violation] = []
    for p in paths:
        rel = p.relative_to(ROOT).as_posix() if p.is_absolute() else p.as_posix()
        out.extend(spec_ref_violations_in_source(
            p.read_text(encoding="utf-8"), rel, spec_dir))
    return out


# ---------------------------------------------------------------------------
# error_code registration.  A cheap, deterministic *emission-side* check: every
# literal error_code on a diagnostic must exist in vera/errors.py ERROR_CODES.
# Catches typos and unregistered codes.  It does NOT detect collisions (one
# registered code reused for two unrelated concepts) — that needs the semantic /
# structural work tracked in #828.  error_code *presence* stays deferred (#828);
# this only validates a code that IS present as a literal.
# ---------------------------------------------------------------------------


def _load_error_codes(errors_py: Path) -> set[str]:
    """Extract the registered code keys from `vera/errors.py` ERROR_CODES."""
    tree = ast.parse(errors_py.read_text(encoding="utf-8"),
                     filename=str(errors_py))
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            targets: list[ast.expr] = list(node.targets)
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
        else:
            continue
        if (any(isinstance(t, ast.Name) and t.id == "ERROR_CODES"
                for t in targets)
                and isinstance(node.value, ast.Dict)):
            return {
                str(k.value) for k in node.value.keys
                if isinstance(k, ast.Constant) and isinstance(k.value, str)
            }
    return set()


def _diagnostic_call_sites(
    source: str, filename: str, tree: ast.AST | None = None,
) -> Iterator[ast.Call]:
    """Yield each Diagnostic() / ._error() / ._warning() Call node, skipping the
    plumbing Diagnostic() construction inside an _error/_warning helper def.

    Accepts an already-parsed `tree` so a caller that also needs its OWN
    walk over the same source (e.g. mapping each Call's enclosing
    function) can share one AST — `ast.parse` on the same text twice
    produces two unrelated node objects, so `id()`-keyed maps built from
    a second parse never match nodes yielded from a first one."""
    if tree is None:
        tree = ast.parse(source, filename=filename)
    plumbing = _plumbing_ctors(tree)

    for n in ast.walk(tree):
        if not isinstance(n, ast.Call):
            continue
        f = n.func
        is_ctor = isinstance(f, ast.Name) and f.id == "Diagnostic"
        is_helper = (isinstance(f, ast.Attribute)
                     and f.attr in ("_error", "_warning"))
        if not (is_ctor or is_helper):
            continue
        if is_ctor and n in plumbing:
            continue
        yield n


def error_code_registration_violations_in_source(
    source: str, filename: str, registry: set[str],
) -> list[Violation]:
    """Flag any *literal* error_code on a diagnostic that is not in ERROR_CODES.
    Non-literal (threaded) codes are skipped — they cannot be checked
    statically."""
    src_lines = source.splitlines()
    out: list[Violation] = []
    for call in _diagnostic_call_sites(source, filename):
        for kw in call.keywords:
            if kw.arg != "error_code":
                continue
            v = kw.value
            if (isinstance(v, ast.Constant) and isinstance(v.value, str)
                    and v.value and v.value not in registry):
                ln = v.lineno
                snip = src_lines[ln - 1] if ln - 1 < len(src_lines) else None
                out.append(Violation(
                    filename, ln, "error_code",
                    [f"emits unregistered error_code {v.value!r} — add it to "
                     f"ERROR_CODES in vera/errors.py"], snip))
    return out


def error_code_registration_violations(
    paths: Iterable[Path], registry: set[str],
) -> list[Violation]:
    out: list[Violation] = []
    for p in paths:
        rel = p.relative_to(ROOT).as_posix() if p.is_absolute() else p.as_posix()
        out.extend(error_code_registration_violations_in_source(
            p.read_text(encoding="utf-8"), rel, registry))
    return out


# ---------------------------------------------------------------------------
# error_code uniqueness (#828): `ERROR_CODES` is a naming authority (code ->
# title) but not an allocation authority — nothing stops two UNRELATED
# diagnostic concepts from independently choosing the same registered code.
# Four such collisions accreted across separate PRs before #682's manual
# audit caught them (E130, E210, E320, E600 each meant two different things
# at two different call sites).  This is the deterministic layer that would
# have caught all four: it does not try to judge whether two DESCRIPTIONS
# read as the same concept (a fuzzy, hard-to-calibrate heuristic that this
# repo's own multi-site codes show produces false positives even on
# genuinely-one-concept text — see KNOWN_MULTI_SITE_ERROR_CODES below); it
# instead requires every code emitted from more than one distinct (file,
# enclosing-function) SITE to have that exact site set pre-declared, with a
# reason, exactly like STRUCTURAL_EXEMPTIONS above.  A code gaining an
# additional site — including a THIRD site added to an already-declared
# multi-site code — changes the recorded set and must fail until a human
# re-verifies and updates the declaration, closing the loophole a
# count-only or code-only allowlist would leave open.
# ---------------------------------------------------------------------------


def _enclosing_qualified_names(tree: ast.AST) -> dict[int, str]:
    """Map ``id(node)`` to the dotted qualified name of its nearest
    enclosing function/method (``ClassName.method_name``, or just
    ``function_name`` at module scope, or ``<module>`` for top-level
    code) — a far more stable site identity than a line number, which
    shifts on any unrelated edit above it in the file."""
    result: dict[int, str] = {}
    defs = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)

    def label(child: ast.AST, stack: list[str]) -> None:
        result[id(child)] = ".".join(stack) if stack else "<module>"

    def visit(node: ast.AST, stack: list[str]) -> None:
        if isinstance(node, defs):
            # A definition's name scopes only its BODY.  Python evaluates
            # decorators, parameter defaults, annotations, base classes and
            # class keywords in the enclosing scope, so a diagnostic emitted
            # from one of those belongs to the enclosing site, not to the
            # definition it decorates.
            inner = stack + [node.name]
            for field, value in ast.iter_fields(node):
                scope = inner if field == "body" else stack
                for child in (value if isinstance(value, list) else [value]):
                    if isinstance(child, ast.AST):
                        label(child, scope)
                        visit(child, scope)
            return
        for child in ast.iter_child_nodes(node):
            label(child, stack)
            visit(child, stack)

    visit(tree, [])
    return result


# (error_code) -> frozenset of (relative-file, qualified-name) sites that
# are the CURRENT, human-verified site set for a code legitimately shared
# by one diagnostic concept applied at more than one call shape.  Each
# entry's reason is why the sites are the same concept, not different ones
# — verified against the actual description/rationale text at every site
# (2026-09-03 audit, alongside this gate's introduction).
KNOWN_MULTI_SITE_ERROR_CODES: dict[str, frozenset[tuple[str, str]]] = {
    # Uninferred generic type argument: codegen's own monomorphization
    # discovery pass and the verifier's independent mirror of the same
    # check both report it where they find it (#1368).
    "E622": frozenset({
        ("vera/codegen/monomorphize.py", "MonomorphizationMixin._report_uninferred_type_args"),
        ("vera/verifier.py", "ContractVerifier._report_one_uninferred"),
    }),
    # Call-site effect subeffecting: a named function call and an
    # apply_fn-applied closure value are two call SHAPES for one rule.
    "E125": frozenset({
        ("vera/checker/calls.py", "CallsMixin._check_apply_fn"),
        ("vera/checker/calls.py", "CallsMixin._check_fn_call_with_info"),
    }),
    # Call arity mismatch: named call vs. apply_fn, same rule.
    "E201": frozenset({
        ("vera/checker/calls.py", "CallsMixin._check_apply_fn"),
        ("vera/checker/calls.py", "CallsMixin._check_fn_call_with_info"),
    }),
    # Argument type mismatch: named call vs. apply_fn, same rule.
    "E202": frozenset({
        ("vera/checker/calls.py", "CallsMixin._check_apply_fn"),
        ("vera/checker/calls.py", "CallsMixin._check_fn_call_with_info"),
    }),
    # Zero-size element type has no WASM representation: the array-literal
    # inferred form and the written Array/Map/Set type-expression form.
    "E135": frozenset({
        ("vera/checker/expressions.py", "ExpressionsMixin._check_array_lit"),
        ("vera/checker/resolution.py", "ResolutionMixin._resolve_named_type"),
    }),
    # Integer-literal range: a generic helper forwarding a caller-supplied
    # description, and the negation special case coded the same way.
    "E149": frozenset({
        ("vera/checker/core.py", "TypeChecker._literal_range_error"),
        ("vera/checker/expressions.py", "ExpressionsMixin._check_unary"),
    }),
    # Reserved `Vera*` prelude namespace: declaration name, type parameter
    # name, and the reference-side hit — one rule, three trigger points.
    "E154": frozenset({
        ("vera/checker/registration.py",
         "RegistrationMixin._check_reserved_decl_name"),
        ("vera/checker/registration.py",
         "RegistrationMixin._check_reserved_type_params"),
        ("vera/checker/resolution.py", "ResolutionMixin._resolve_named_type"),
    }),
    # Tier-3 refinement demotion: a single dispatcher picks between the
    # runtime-checked and the unguarded phrasing of one classification.
    "E506": frozenset({
        ("vera/verifier.py", "ContractVerifier._report_refined_runtime"),
        ("vera/verifier.py", "ContractVerifier._report_refined_unguarded"),
    }),
    # Codegen cannot lower this function/closure — skipped, enclosing
    # function dropped.  Every site is this one family (unsupported WASM
    # type, CodegenSkip, recursion-depth cap, cyclic-refinement closure,
    # contract-predicate skip, and the parent-drop wrapper); their
    # comments already cross-reference each other as one concept.
    "E602": frozenset({
        ("vera/codegen/closures.py",
         "ClosureLiftingMixin._compile_lifted_closure"),
        ("vera/codegen/closures.py",
         "ClosureLiftingMixin._lift_pending_closures"),
        ("vera/codegen/functions.py", "FunctionCompilationMixin._compile_fn"),
        ("vera/codegen/functions.py",
         "FunctionCompilationMixin._emit_contract_predicate_skip"),
        ("vera/codegen/functions.py",
         "FunctionCompilationMixin._lift_closures_or_drop"),
    }),
    # Ability-not-satisfied: the Eq-derivability failure and the generic
    # constraint-checking failure both name "Type T does not satisfy
    # ability A", spec §9.8.
    "E613": frozenset({
        ("vera/codegen/functions.py",
         "FunctionCompilationMixin._emit_adt_eq_not_derivable"),
        ("vera/codegen/monomorphize.py",
         "MonomorphizationMixin._check_constraints"),
    }),
    # Internal-compiler-error envelope: by nature emitted from any
    # unexpected-exception site; the concept is "something crashed",
    # not tied to one spec section (some sites carry none at all, a
    # STRUCTURAL_EXEMPTIONS case above).
    "E699": frozenset({
        ("vera/cli.py", "_internal_error_envelope"),
        ("vera/codegen/functions.py", "FunctionCompilationMixin._compile_fn"),
        ("vera/codegen/functions.py",
         "FunctionCompilationMixin._lift_closures_or_drop"),
    }),
}


def error_code_collision_violations(paths: Iterable[Path]) -> list[Violation]:
    """Flag a literal error_code emitted from more than one distinct
    (file, enclosing-function) site unless that EXACT site set is
    declared in KNOWN_MULTI_SITE_ERROR_CODES — the collision shape
    that let E130/E210/E320/E600 each carry two unrelated concepts
    (#682) until a manual audit found them."""
    sites_by_code: dict[str, set[tuple[str, str, int]]] = {}
    for p in paths:
        rel = p.relative_to(ROOT).as_posix() if p.is_absolute() else p.as_posix()
        source = p.read_text(encoding="utf-8")
        tree = ast.parse(source, filename=rel)
        qualnames = _enclosing_qualified_names(tree)
        for call in _diagnostic_call_sites(source, rel, tree=tree):
            for kw in call.keywords:
                if kw.arg != "error_code":
                    continue
                v = kw.value
                if isinstance(v, ast.Constant) and isinstance(v.value, str) and v.value:
                    qualname = qualnames.get(id(call), "<module>")
                    sites_by_code.setdefault(v.value, set()).add(
                        (rel, qualname, call.lineno))

    out: list[Violation] = []
    for code, site_triples in sorted(sites_by_code.items()):
        distinct_sites = {(f, q) for f, q, _ in site_triples}
        if len(distinct_sites) < 2:
            continue
        declared = KNOWN_MULTI_SITE_ERROR_CODES.get(code)
        if declared == frozenset(distinct_sites):
            continue
        first_file = min(f for f, _, _ in site_triples)
        first_line = min(ln for f, _, ln in site_triples if f == first_file)
        site_list = ", ".join(
            f"{f}::{q}" for f, q in sorted(distinct_sites)
        )
        if declared is None:
            detail = (
                f"error_code {code!r} is emitted from {len(distinct_sites)} "
                f"distinct sites not declared in KNOWN_MULTI_SITE_ERROR_CODES: "
                f"{site_list} — if these are genuinely one diagnostic concept "
                f"applied at different call shapes, add an entry with a "
                f"one-line reason; if they are unrelated concepts that "
                f"happen to share a code, give one of them a new code "
                f"(the #682 collision shape)"
            )
        else:
            detail = (
                f"error_code {code!r}'s live site set no longer matches its "
                f"KNOWN_MULTI_SITE_ERROR_CODES declaration — live: {site_list}; "
                f"re-verify the new/changed site is still the same concept "
                f"and update the declaration"
            )
        out.append(Violation(first_file, first_line, "error_code_collision",
                              [detail], None))
    return out


def main() -> int:
    files = iter_vera_files(ROOT / "vera")
    presence = check_paths(files)
    validity = spec_ref_violations(files)
    registry = _load_error_codes(ROOT / "vera" / "errors.py")
    codes = error_code_registration_violations(files, registry)
    collisions = error_code_collision_violations(files)
    violations = presence + validity + codes + collisions
    if not violations:
        print("check_diagnostic_fields: OK — every diagnostic is fully tagged, "
              "every spec_ref resolves, every error_code is registered, and "
              "every multi-site error_code is a declared, verified reuse.")
        return 0
    by_file: dict[str, list[Violation]] = {}
    for v in violations:
        by_file.setdefault(v.file, []).append(v)
    print(f"check_diagnostic_fields: {len(violations)} problem(s) in "
          f"{len(by_file)} file(s).\n")
    print("Every diagnostic MUST carry rationale + spec_ref, and an error-"
          "severity one a fix too (warnings are fix-exempt) — spec §0.5.1; the "
          "spec_ref must also resolve to a real section/chapter, any "
          "error_code must be registered in vera/errors.py ERROR_CODES, and a "
          "code emitted from more than one (file, function) site must have "
          "that exact site set declared in KNOWN_MULTI_SITE_ERROR_CODES.")
    print("Populate the missing field(s) / fix the spec_ref / register the "
          "error_code / declare or fix the multi-site set.  "
          "`# diag-fields-exempt: <reason>` waives a missing field or an "
          "unresolvable (non-literal) severity/spec_ref for a genuinely "
          "fix-less internal/defensive site — it does NOT waive a spec_ref "
          "citing the wrong/nonexistent section, an unregistered error_code, "
          "or an undeclared error_code collision: those are content errors, "
          "not tagging gaps.\n")
    for fname in sorted(by_file):
        print(f"  {fname}")
        for v in sorted(by_file[fname], key=lambda x: x.line):
            if v.target in ("spec_ref", "error_code", "error_code_collision"):
                print(f"    line {v.line:<5} {v.target:<11} {v.missing[0]}")
            else:
                print(f"    line {v.line:<5} {v.target:<11} missing: "
                      f"{', '.join(v.missing)}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
