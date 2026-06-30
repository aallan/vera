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
if a required field is missing.

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
- **Per-call opt-out:** ``# diag-fields-exempt: <reason>`` on the call,
  the reason mandatory — for one-off defensive / internal branches
  (e.g. an "unknown expression type" fallback).  A marker without a
  reason is itself a violation.  (A dedicated token, not a ruff-style
  suppression comment — see ``OPT_OUT`` below for why.)
- **Plumbing skip:** the ``Diagnostic(...)`` construction *inside* an
  ``_error`` / ``_warning`` helper def is not an independent site — its
  call sites plus the registry govern it.

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
            elif text.startswith(OPT_OUT + ":") or text.startswith(OPT_OUT + " "):
                out[tok.start[0]] = text[len(OPT_OUT):].lstrip(" :").strip()
    except (tokenize.TokenError, IndentationError):
        pass
    return out


def check_source(source: str, filename: str) -> list[Violation]:
    """Return every under-tagged diagnostic site in one source string."""
    tree = ast.parse(source, filename=filename)
    src_lines = source.splitlines()
    fam = family(filename)

    # Spans of _error/_warning helper *definitions* — Diagnostic()
    # constructions inside them are plumbing, not independent sites.
    helper_spans: list[tuple[int, int]] = []
    for n in ast.walk(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and \
                n.name in ("_error", "_warning"):
            helper_spans.append((n.lineno, n.end_lineno or n.lineno))

    def inside_helper(lineno: int) -> bool:
        return any(a <= lineno <= b for a, b in helper_spans)

    optout = _optout_lines(source)
    violations: list[Violation] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        f = node.func
        if isinstance(f, ast.Name) and f.id == "Diagnostic":
            if inside_helper(node.lineno):
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
                    violations.append(Violation(
                        filename, node.lineno, "Diagnostic",
                        ["severity is not a string literal — the gate cannot "
                         "tell error from warning; make it a literal"], snip))
                    continue
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
            continue  # opt-out with a reason suppresses the site

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
_spec_cache: tuple[dict[str, str], dict[str, str]] | None = None


def _load_spec(spec_dir: Path) -> tuple[dict[str, str], dict[str, str]]:
    """Return ({section-number: title}, {chapter-number: chapter-title})."""
    global _spec_cache
    if _spec_cache is not None:
        return _spec_cache
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
    _spec_cache = (sections, chapters)
    return _spec_cache


def _norm(s: str) -> str:
    s = s.lower().replace("`", "")
    s = re.sub(r"\([^)]*\)", "", s)
    return re.sub(r"\s+", " ", s).strip()


def _iter_spec_refs(
    source: str, filename: str,
) -> Iterator[tuple[int, str, str | None]]:
    """Yield (lineno, ref_text, snippet) for each non-empty literal spec_ref."""
    tree = ast.parse(source, filename=filename)
    src_lines = source.splitlines()
    for n in ast.walk(tree):
        if not isinstance(n, ast.Call):
            continue
        f = n.func
        if not ((isinstance(f, ast.Name) and f.id == "Diagnostic")
                or (isinstance(f, ast.Attribute)
                    and f.attr in ("_error", "_warning"))):
            continue
        for kw in n.keywords:
            if kw.arg == "spec_ref" and isinstance(kw.value, ast.Constant) \
                    and isinstance(kw.value.value, str) and kw.value.value.strip():
                ln = kw.value.lineno
                snip = src_lines[ln - 1] if ln - 1 < len(src_lines) else None
                yield ln, kw.value.value, snip


def spec_ref_violations_in_source(source: str, filename: str,
                                  spec_dir: Path | None = None) -> list[Violation]:
    """Flag every spec_ref in one source that does not resolve to a real spec
    section/chapter with a matching (normalized) title."""
    sections, chapters = _load_spec(spec_dir or (ROOT / "spec"))
    out: list[Violation] = []
    for ln, ref, snip in _iter_spec_refs(source, filename):
        m = _REF_SEC.search(ref)
        if m:
            chap, sec, title = m.group(1), m.group(2), m.group(3)
            actual = sections.get(sec)
            if actual is None:
                why = f"cites §{sec}, which does not exist in the spec"
            elif _norm(actual) != _norm(title):
                why = f'cites §{sec} as "{title}" but it is "{actual}"'
            elif not (sec == chap or sec.startswith(chap + ".")):
                why = f"§{sec} is not in Chapter {chap}"
            else:
                continue
        else:
            mc = _REF_CH.match(ref)
            if not mc:
                why = f"unrecognised spec_ref format: {ref!r}"
            else:
                chap, title = mc.group(1), mc.group(2)
                actual = chapters.get(chap)
                if actual is None or _norm(actual) != _norm(title):
                    why = f'Chapter {chap} is "{actual}", not "{title}"'
                else:
                    continue
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


def main() -> int:
    files = iter_vera_files(ROOT / "vera")
    presence = check_paths(files)
    validity = spec_ref_violations(files)
    violations = presence + validity
    if not violations:
        print("check_diagnostic_fields: OK — every diagnostic is fully tagged "
              "and every spec_ref resolves.")
        return 0
    by_file: dict[str, list[Violation]] = {}
    for v in violations:
        by_file.setdefault(v.file, []).append(v)
    print(f"check_diagnostic_fields: {len(violations)} problem(s) in "
          f"{len(by_file)} file(s).\n")
    print("Every diagnostic MUST carry rationale + fix + spec_ref (spec "
          "§0.5.1), and the spec_ref must resolve to a real section/chapter.")
    print("Populate the missing field(s) / fix the spec_ref, or add "
          "`# diag-fields-exempt: <reason>` for a genuinely fix-less "
          "internal/defensive site.\n")
    for fname in sorted(by_file):
        print(f"  {fname}")
        for v in sorted(by_file[fname], key=lambda x: x.line):
            if v.target == "spec_ref":
                print(f"    line {v.line:<5} spec_ref    {v.missing[0]}")
            else:
                print(f"    line {v.line:<5} {v.target:<11} missing: "
                      f"{', '.join(v.missing)}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
